const $=s=>document.querySelector(s);
function applyTheme(theme,persist=false){document.documentElement.dataset.theme=theme;if(persist)localStorage.setItem('event-ruler-theme',theme);const light=theme==='light',button=$('#themeButton');if(button){button.textContent=light?'☾':'☀';button.setAttribute('aria-label',light?'ダークモードに切替':'ライトモードに切替');button.setAttribute('aria-pressed',String(light))}document.querySelector('meta[name="theme-color"]')?.setAttribute('content',light?'#f2f3ef':'#090b0d')}
function initTheme(){const theme=document.documentElement.dataset.theme||'dark';applyTheme(theme);$('#themeButton').onclick=()=>applyTheme(document.documentElement.dataset.theme==='light'?'dark':'light',true)}
const DB_NAME='event-ruler-db', STORE='events', DB_VERSION=1;
const colors=['#75f0c2','#62b5ff','#F06BFF'];
const scales=[{label:'1 min',px:4,tick:60000},{label:'5 min',px:1.4,tick:300000},{label:'15 min',px:.55,tick:900000,spanMinutes:180}];
const SPAN=14*86400000;
const AUDIO_OPERATION_TIMEOUT=1200;
const RECORD_SOUND_VOLUME=0.072;
const ORB_SOUND_VOLUME=0.072;
const RECORD_SOUND_WAIT_MS=250;
const AUDIO_ASSET_RETRY_MS=2000;
let recordDataPromise=null,recordDataRetryAt=0,recordSoundToken=0;
const recordAudioStates=new WeakMap();
let orbDataPromise=null,orbDataRetryAt=0,lastPlayheadMarkerId=null;
const orbAudioStates=new WeakMap();
const RATCHET_CLICK_OPTIONS=Object.freeze({decay:.005,frequencyDrop:.5,frequencyDropTime:.00425,stopTime:.01});
let db,events=[],selectedColor=localStorage.getItem('marker-color')||colors[0],scaleIndex=1,origin=Date.now()-SPAN/2,selectedId=null,renderQueued=false,scrollTimer,undoItem=null,undoTimer;
let viewCenterTime=Date.now(),dataBusy=false,eventsRevision=0,tickRenderKey='',markerRenderKey='';
const audioCloseTasks=new WeakMap(),audioResumeOperations=new WeakMap();
const audioPrimes=new WeakMap(),audioPlaybackLogs=new Set();
let audioGestureSeen=false;
let audioClosingContext=null,audioLifecycle=0;
const timeFormat=new Intl.DateTimeFormat('ja-JP',{hour:'2-digit',minute:'2-digit',hour12:false});
const secondFormat=new Intl.DateTimeFormat('ja-JP',{hour:'2-digit',minute:'2-digit',second:'2-digit',hour12:false});
let audioContext=null,audioResumeTask=null,audioResetPromise=null,audioEventsInstalled=false,audioMayBeStale=false,audioGeneration=0,lastAudioGestureAt=0,lastAudioGestureTarget=null,lastAudioGestureType='',lastAudioErrorLogAt=0,pendingRatchetToken=0,lastRatchetStep=null,lastRatchetAt=0;
const ruler=$('#ruler'),track=$('#rulerTrack'),ticks=$('#ticks'),markers=$('#markers'),nowLine=$('#nowLine');

function audioLog(event,details={}){console.info(`[Event Ruler audio] ${event}`,{atMs:Math.round(performance.now()),...details})}
function logAudioPlayback(sound,started){
  const key=`${sound}:${started?'scheduled':'skipped'}`;
  if(audioPlaybackLogs.has(key))return;
  audioPlaybackLogs.add(key);
  const state=audioContext?.state||'none',orbReady=!!orbAudioStates.get(audioContext)?.buffer,recordReady=!!recordAudioStates.get(audioContext)?.buffer;
  const reason=started?'source-started':!audioGestureSeen?'awaiting-gesture':audioResetPromise?'recovering':document.visibilityState==='hidden'?'hidden':state!=='running'?`context-${state}`:(sound==='orb'&&!orbReady)||(sound==='record'&&!recordReady)?'buffer-not-ready':'start-failed';
  audioLog('first-playback',{sound,result:started?'scheduled':'skipped',reason,state,orbReady,recordReady});
}
function prepareAudioAtStartup(){
  // Fetch/decode while suspended; only a gesture may resume or prime the context.
  void loadOrbData();void loadRecordData();
  if(!audioContext&&!audioResetPromise&&!audioClosingContext)createAudioContext('startup');
}
function createAudioContext(reason){const AudioCtx=window.AudioContext||window.webkitAudioContext;if(!AudioCtx){audioLog('unsupported');return null}try{const ctx=new AudioCtx(),generation=++audioGeneration;audioContext=ctx;audioLog('context-created',{reason,generation,state:ctx.state});ctx.onstatechange=()=>{if(ctx===audioContext)audioLog('state-change',{generation,state:ctx.state})};void prepareOrbAudio(ctx);void prepareRecordAudio(ctx);return ctx}catch(error){audioLog('context-create-failed',{reason,message:error?.message||String(error)});return null}}
function loadOrbData(){
  if(!orbDataPromise&&performance.now()<orbDataRetryAt)return Promise.resolve(null);
  if(!orbDataPromise)orbDataPromise=(async()=>{
    try{
      const response=await fetch('orb.ogg');
      if(!response.ok)throw Error('HTTP '+response.status);
      const bytes=await response.arrayBuffer();audioLog('orb-load-complete');return bytes;
    }catch(error){orbDataRetryAt=performance.now()+AUDIO_ASSET_RETRY_MS;audioLog('orb-load-failed',{message:String(error)});return null}
  })().then(bytes=>{
    if(!bytes)orbDataPromise=null;
    return bytes;
  });
  return orbDataPromise;
}
function prepareOrbAudio(ctx){
  if(!ctx||ctx!==audioContext||ctx.state==='closed')return Promise.resolve();
  const state=orbAudioStates.get(ctx)||{buffer:null,gain:null,ready:null,retryAt:0};
  if(state.buffer||state.ready)return state.ready||Promise.resolve();
  if(performance.now()<state.retryAt)return Promise.resolve();
  orbAudioStates.set(ctx,state);
  state.ready=(async()=>{
    try{
      const bytes=await loadOrbData();
      if(!bytes||ctx!==audioContext||ctx.state==='closed')return;
      // decodeAudioData may detach its input; retain the original for recovery.
      const buffer=await ctx.decodeAudioData(bytes.slice(0));
      if(ctx!==audioContext||ctx.state==='closed')return;
      const gain=ctx.createGain();gain.gain.value=ORB_SOUND_VOLUME;gain.connect(ctx.destination);
      state.buffer=buffer;state.gain=gain;
      audioLog('orb-decode-complete',{state:ctx.state});
    }catch(error){state.retryAt=performance.now()+AUDIO_ASSET_RETRY_MS;audioLog('orb-decode-failed',{message:String(error)})}
  })().finally(()=>{state.ready=null});
  return state.ready;
}
function playOrbSound(){
  const ctx=audioContext,state=ctx&&orbAudioStates.get(ctx);
  if(!ctx||audioResetPromise||!audioGestureSeen||ctx.state!=='running'||document.visibilityState==='hidden'||!state?.buffer){logAudioPlayback('orb',false);return false}
  let source;
  try{
    const pitch=(Math.random() - Math.random()) * 0.35 + 0.9;
    source=ctx.createBufferSource();
    source.buffer=state.buffer;
    source.playbackRate.value=pitch;
    source.connect(state.gain);
    source.onended=()=>source.disconnect();
    source.start();
    logAudioPlayback('orb',true);
    return true;
  }catch(error){source?.disconnect();audioLog('orb-play-failed',{message:String(error)});return false}
}
function waitForAudioOperation(operation){return new Promise(resolve=>{let settled=false;const finish=value=>{if(settled)return;settled=true;clearTimeout(timer);resolve(value)},timer=setTimeout(()=>finish(false),AUDIO_OPERATION_TIMEOUT);let result;try{result=operation()}catch{finish(false);return}Promise.resolve(result).then(()=>finish(true),()=>finish(false))})}
function resumeContext(ctx){
  let operation=audioResumeOperations.get(ctx);
  if(!operation){
    try{operation=Promise.resolve(ctx.resume()).then(()=>true,()=>false)}catch{operation=Promise.resolve(false)}
    audioResumeOperations.set(ctx,operation);
    void operation.then(()=>{if(audioResumeOperations.get(ctx)===operation)audioResumeOperations.delete(ctx)});
  }
  // A timeout must not discard an unresolved native resume promise.
  return waitForAudioOperation(async()=>{if(!await operation)throw Error('resume failed')});
}
async function closeAudioContext(ctx,reason){
  if(!ctx||ctx.state==='closed')return true;
  ctx.onstatechange=null;
  let closing=audioCloseTasks.get(ctx);
  if(!closing){
    try{closing=Promise.resolve(ctx.close()).then(()=>true,()=>false)}catch{closing=Promise.resolve(false)}
    audioCloseTasks.set(ctx,closing);
    void closing.then(ok=>{if(!ok)audioCloseTasks.delete(ctx)});
  }
  const closed=await waitForAudioOperation(async()=>{if(!await closing)throw Error('close failed')});
  if(!closed)audioLog('close-incomplete',{reason,state:ctx.state});
  return closed&&ctx.state==='closed';
}
function primeAudioContext(ctx,allowPending=false){
  if(!ctx||(ctx.state!=='running'&&!(allowPending&&(ctx.state==='suspended'||ctx.state==='interrupted'))))return false;
  // Do not stack pending unlock sources; later gestures can still try again.
  const previous=audioPrimes.get(ctx);
  if(previous?.pending)return true;
  let osc,gain;
  try{
    const at=ctx.currentTime,prime={pending:true};
    osc=ctx.createOscillator();gain=ctx.createGain();osc.type='sawtooth';
    gain.gain.setValueAtTime(.000001,at);osc.connect(gain).connect(ctx.destination);
    osc.onended=()=>{osc.disconnect();gain.disconnect();prime.pending=false};
    osc.start(at);osc.stop(at+.001);audioPrimes.set(ctx,prime);return true;
  }catch(error){osc?.disconnect();gain?.disconnect();audioLog('prime-failed',{message:error?.message||String(error)});return false}
}
function recreateAfterResume(ctx,reason){return ctx===audioContext?forceRecreateAudio(reason):Promise.resolve(false)}
async function resumeAudio(allowCreate=false,reason='automatic'){if(audioResetPromise)return audioResetPromise;if(audioClosingContext)return allowCreate?forceRecreateAudio(reason):false;let ctx=audioContext;if((!ctx||ctx.state==='closed')&&allowCreate)ctx=createAudioContext(reason);if(!ctx)return false;if(audioResumeTask&&audioResumeTask.ctx===ctx){if(allowCreate)audioResumeTask.allowRecreate=true;return audioResumeTask.promise}if(ctx.state==='running')return true;const task={ctx,allowRecreate:allowCreate,reason,promise:null};task.promise=(async()=>{audioLog('resume-start',{reason,state:ctx.state});const resumed=(ctx.state==='suspended'||ctx.state==='interrupted')?await resumeContext(ctx):false;if(ctx!==audioContext||audioResumeTask!==task)return false;if(resumed&&ctx.state==='running'){audioLog('resume-complete',{reason});return true}audioLog('resume-failed',{reason,state:ctx.state});if(task.allowRecreate)return recreateAfterResume(ctx,`${reason}:resume-failed`);return false})().finally(()=>{if(audioResumeTask===task)audioResumeTask=null});audioResumeTask=task;return task.promise}
function forceRecreateAudio(reason){
  if(audioResetPromise)return audioResetPromise;
  const old=audioClosingContext||audioContext,epoch=audioLifecycle;
  audioLog('context-recovery-start',{reason,state:old?.state||'none'});
  audioContext=null;audioResumeTask=null;audioClosingContext=old;pendingRatchetToken++;
  const pending=(async()=>{
    // A timed-out close remains tracked. Never create another context until it closes.
    if(!await closeAudioContext(old,reason))return false;
    audioClosingContext=null;
    if(document.visibilityState==='hidden')return false;
    const next=createAudioContext(reason);
    if(!next)return false;
    const resuming=resumeContext(next);
    primeAudioContext(next,true);
    const resumed=await resuming;
    if(!resumed||next!==audioContext||next.state!=='running'){
      audioLog('context-recovery-failed',{reason,state:next.state});return false;
    }
    if(epoch===audioLifecycle)audioMayBeStale=false;
    audioLog('context-recovery-complete',{reason});return true;
  })().catch(error=>{audioLog('context-recovery-failed',{reason,message:String(error)});return false});
  audioResetPromise=pending;
  void pending.finally(()=>{if(audioResetPromise===pending)audioResetPromise=null});
  return pending;
}
function markAudioStale(reason){audioLifecycle++;pendingRatchetToken++;if(!audioMayBeStale)audioLog('lifecycle-stale',{reason,state:audioContext?.state||'none'});audioMayBeStale=true}
function recoverAudioFromGesture(reason){
  if(!audioGestureSeen){audioGestureSeen=true;audioLog('first-gesture',{reason,state:audioContext?.state||'none',orbReady:!!orbAudioStates.get(audioContext)?.buffer,recordReady:!!recordAudioStates.get(audioContext)?.buffer})}
  if(audioResetPromise)return;
  const ctx=audioContext,epoch=audioLifecycle;
  // A native resume can change state before its Promise callbacks run.
  if(audioClosingContext||(audioMayBeStale&&ctx?.state==='running'&&audioResumeTask?.ctx!==ctx)){void forceRecreateAudio(reason);return}
  const recovery=resumeAudio(true,reason),active=audioContext;
  primeAudioContext(active,true);
  if(active){void prepareOrbAudio(active);void prepareRecordAudio(active)}
  void recovery.then(ok=>{if(ok&&active===audioContext&&epoch===audioLifecycle)audioMayBeStale=false});
}
function activateAudio(event){const target=event.currentTarget,now=performance.now(),duplicate=target===lastAudioGestureTarget&&event.type!==lastAudioGestureType&&now-lastAudioGestureAt<500;if(duplicate)return;lastAudioGestureTarget=target;lastAudioGestureAt=now;lastAudioGestureType=event.type;if(target===ruler)lastRatchetStep=Math.floor(timeForX(ruler.scrollLeft+ruler.clientWidth/2)/scales[scaleIndex].tick);recoverAudioFromGesture(target===ruler?'ruler-gesture':'record-gesture')}
function installAudioRecovery(){if(audioEventsInstalled)return;audioEventsInstalled=true;for(const target of [ruler,$('#recordButton')]){target.addEventListener('pointerdown',activateAudio,{passive:true,capture:true});target.addEventListener('touchstart',activateAudio,{passive:true,capture:true})}document.addEventListener('visibilitychange',()=>{if(document.visibilityState==='hidden')markAudioStale('visibility-hidden')});window.addEventListener('pagehide',()=>markAudioStale('pagehide'));window.addEventListener('pageshow',event=>{if(event.persisted)markAudioStale('pageshow-persisted')});window.addEventListener('focus',()=>{if(audioGestureSeen&&document.visibilityState==='visible'&&audioContext&&(audioContext.state==='suspended'||audioContext.state==='interrupted'))markAudioStale('focus-non-running')})}
function mechanicalClick(pitch=1050,volume=.032,delay=0,options={}){const ctx=audioContext;if(!ctx||ctx.state!=='running')return false;const {decay=.026,frequencyDrop=.48,frequencyDropTime=.022,stopTime=.03}=options;try{const at=ctx.currentTime+delay,osc=ctx.createOscillator(),gain=ctx.createGain();osc.type='sawtooth';osc.frequency.setValueAtTime(pitch,at);osc.frequency.exponentialRampToValueAtTime(Math.max(90,pitch*frequencyDrop),at+frequencyDropTime);gain.gain.setValueAtTime(.0001,at);gain.gain.exponentialRampToValueAtTime(volume,at+.002);gain.gain.exponentialRampToValueAtTime(.0001,at+decay);osc.connect(gain).connect(ctx.destination);osc.start(at);osc.stop(at+stopTime);audioMayBeStale=false;return true}catch(error){audioMayBeStale=true;const now=performance.now();if(now-lastAudioErrorLogAt>2000){audioLog('click-failed',{state:ctx.state,message:error?.message||String(error)});lastAudioErrorLogAt=now}return false}}
function loadRecordData(){
  if(!recordDataPromise&&performance.now()<recordDataRetryAt)return Promise.resolve(null);
  if(!recordDataPromise)recordDataPromise=(async()=>{
    try{
      const response=await fetch('record.ogg');
      if(!response.ok)throw Error('HTTP '+response.status);
      const bytes=await response.arrayBuffer();audioLog('record-load-complete');return bytes;
    }catch(error){recordDataRetryAt=performance.now()+AUDIO_ASSET_RETRY_MS;audioLog('record-load-failed',{message:String(error)});return null}
  })().then(bytes=>{
    if(!bytes)recordDataPromise=null;
    return bytes;
  });
  return recordDataPromise;
}
function prepareRecordAudio(ctx){
  if(!ctx||ctx!==audioContext||ctx.state==='closed')return Promise.resolve();
  const state=recordAudioStates.get(ctx)||{buffer:null,gain:null,source:null,ready:null,retryAt:0};
  if(state.buffer||state.ready)return state.ready||Promise.resolve();
  if(performance.now()<state.retryAt)return Promise.resolve();
  recordAudioStates.set(ctx,state);
  state.ready=(async()=>{
    try{
      const bytes=await loadRecordData();
      if(!bytes||ctx!==audioContext||ctx.state==='closed')return;
      const buffer=await ctx.decodeAudioData(bytes.slice(0));
      if(ctx!==audioContext||ctx.state==='closed')return;
      const gain=ctx.createGain();gain.gain.value=RECORD_SOUND_VOLUME;gain.connect(ctx.destination);
      state.buffer=buffer;state.gain=gain;
      audioLog('record-decode-complete',{state:ctx.state});
    }catch(error){state.retryAt=performance.now()+AUDIO_ASSET_RETRY_MS;audioLog('record-decode-failed',{message:String(error)})}
  })().finally(()=>{state.ready=null});
  return state.ready;
}
function startRecordSound(ctx=audioContext){
  const state=ctx&&recordAudioStates.get(ctx);
  if(!ctx||ctx!==audioContext||audioResetPromise||ctx.state!=='running'||document.visibilityState==='hidden'||!state?.buffer){logAudioPlayback('record',false);return false}
  let source;
  try{
    source=ctx.createBufferSource();
    source.buffer=state.buffer;
    source.connect(state.gain);
    // Preserve the former currentTime=0 behavior on repeated recordings.
    if(state.source){state.source.stop();state.source.disconnect()}
    source.onended=()=>{source.disconnect();if(state.source===source)state.source=null};
    source.start();
    state.source=source;
    logAudioPlayback('record',true);
    return true;
  }catch(error){source?.disconnect();audioLog('record-play-failed',{message:String(error)});return false}
}
function playRecordSound(){
  const token=++recordSoundToken,epoch=audioLifecycle,requestedAt=performance.now();
  if(startRecordSound())return;
  // Start resume within the click stack. Saving never waits for this promise.
  const recovery=resumeAudio(true,'record-sound');
  void (async()=>{
    if(!await recovery)return;
    const ctx=audioContext;
    if(!ctx)return;
    await prepareRecordAudio(ctx);
    if(token!==recordSoundToken||epoch!==audioLifecycle||performance.now()-requestedAt>RECORD_SOUND_WAIT_MS)return;
    startRecordSound(ctx);
  })().catch(error=>audioLog('record-recovery-failed',{message:String(error)}));
}
function playRatchetSound(pitch){if(!audioGestureSeen||document.visibilityState==='hidden'){logAudioPlayback('ratchet',false);return}const token=++pendingRatchetToken,requestedAt=performance.now();if(!audioResetPromise&&mechanicalClick(pitch,.072,0,RATCHET_CLICK_OPTIONS)){logAudioPlayback('ratchet',true);return}logAudioPlayback('ratchet',false);resumeAudio(false,'ratchet-retry').then(ok=>{if(ok&&token===pendingRatchetToken&&performance.now()-requestedAt<100&&document.visibilityState!=='hidden')logAudioPlayback('ratchet',mechanicalClick(pitch,.072,0,RATCHET_CLICK_OPTIONS))})}
function playRatchet(){const center=timeForX(ruler.scrollLeft+ruler.clientWidth/2),step=Math.floor(center/scales[scaleIndex].tick),now=performance.now();if(lastRatchetStep===null){lastRatchetStep=step;return}if(step!==lastRatchetStep&&now-lastRatchetAt>28){playRatchetSound(2160);lastRatchetAt=now}lastRatchetStep=step}

function openDB(){return new Promise((resolve,reject)=>{const req=indexedDB.open(DB_NAME,DB_VERSION);req.onupgradeneeded=()=>{const d=req.result;if(!d.objectStoreNames.contains(STORE)){const s=d.createObjectStore(STORE,{keyPath:'id'});s.createIndex('timestamp','timestamp')}};req.onsuccess=()=>resolve(req.result);req.onerror=()=>reject(req.error)})}
function tx(mode='readonly'){return db.transaction(STORE,mode).objectStore(STORE)}
function request(req){return new Promise((resolve,reject)=>{req.onsuccess=()=>resolve(req.result);req.onerror=()=>reject(req.error)})}
async function loadEvents(){events=await request(tx().getAll());events.sort((a,b)=>a.timestamp-b.timestamp);eventsChanged()}
async function putEvent(item){
  await writeTransaction(store=>store.put(item));
  const i=events.findIndex(e=>e.id===item.id);
  if(i>=0)events.splice(i,1);
  events.splice(eventIndex(item.timestamp),0,item);
  eventsChanged();
}
async function removeEvent(id){await writeTransaction(store=>store.delete(id));const i=events.findIndex(e=>e.id===id);if(i>=0)events.splice(i,1);eventsChanged()}

function writeTransaction(enqueue){
  return new Promise((resolve,reject)=>{
    let transaction,error;
    try{
      transaction=db.transaction(STORE,'readwrite');
      transaction.oncomplete=()=>resolve();
      transaction.onerror=event=>{error=event.target.error||transaction.error};
      transaction.onabort=()=>reject(error||transaction.error||new Error('書き込みが中断されました'));
      enqueue(transaction.objectStore(STORE));
    }catch(cause){
      error=cause;
      if(transaction){try{transaction.abort()}catch{reject(cause)}}else reject(cause);
    }
  });
}
function eventsChanged(){eventsRevision++;renderPlayheadHit(timeForX(ruler.scrollLeft+ruler.clientWidth/2));queueRender();renderCounts()}
function eventIndex(timestamp){let lo=0,hi=events.length;while(lo<hi){const mid=(lo+hi)>>>1;if(events[mid].timestamp<timestamp)lo=mid+1;else hi=mid}return lo}
function newEventId(){return crypto.randomUUID?.()||`${Date.now()}-${Math.random()}`}
async function dataAction(work,errorMessage){
  if(dataBusy){showToast('保存処理中です');return false}
  dataBusy=true;
  try{await work();return true}catch(error){console.error('[Event Ruler data]',error);showToast(errorMessage);return false}
  finally{dataBusy=false}
}
function clearUndo(){clearTimeout(undoTimer);undoItem=null;$('#undoBar').hidden=true}

function chooseColor(color){selectedColor=color;localStorage.setItem('marker-color',color);document.documentElement.style.setProperty('--accent',color);$('#customColor').value=color;renderCounts()}

function pxPerMs(){const scale=scales[scaleIndex],px=scale.spanMinutes&&ruler.clientWidth?ruler.clientWidth/scale.spanMinutes:scale.px;return px/60000}
function xFor(t){return (t-origin)*pxPerMs()}
function timeForX(x){return origin+x/pxPerMs()}
function formatTime(t,sec=false){return (sec?secondFormat:timeFormat).format(t)}
function formatDate(t){const d=new Date(t);return `${d.getFullYear()}-${String(d.getMonth()+1).padStart(2,'0')}-${String(d.getDate()).padStart(2,'0')}`}
function setTrackWidth(){track.style.width=`${SPAN*pxPerMs()}px`}
function centerOn(t,behavior='auto'){ruler.scrollTo({left:xFor(t)-ruler.clientWidth/2,behavior})}
function installRulerDoubleTap(){
  const pointers=new Set();
  let tap=null,lastTap=null,suppressClick=false;
  const reset=()=>{tap=null;lastTap=null};
  const isTapTarget=target=>target instanceof Element&&ruler.contains(target)&&!target.closest('button,a,input,select,textarea,[role="button"]');
  window.addEventListener('pointerdown',event=>{
    pointers.add(event.pointerId);
    suppressClick=false;
    if(pointers.size!==1||!event.isPrimary||event.button!==0||!isTapTarget(event.target)){reset();return}
    tap={id:event.pointerId,type:event.pointerType,x:event.clientX,y:event.clientY,time:event.timeStamp};
  },{passive:true,capture:true});
  window.addEventListener('pointermove',event=>{
    if(tap&&event.pointerId===tap.id&&Math.hypot(event.clientX-tap.x,event.clientY-tap.y)>24)reset();
  },{passive:true,capture:true});
  window.addEventListener('pointerup',event=>{
    pointers.delete(event.pointerId);
    if(!tap||event.pointerId!==tap.id)return;
    const current=tap;
    tap=null;
    if(pointers.size||event.timeStamp-current.time>300||Math.hypot(event.clientX-current.x,event.clientY-current.y)>24||!isTapTarget(document.elementFromPoint(event.clientX,event.clientY))){reset();return}
    if(lastTap&&current.type===lastTap.type&&event.timeStamp-lastTap.time<=300&&Math.hypot(current.x-lastTap.x,current.y-lastTap.y)<=24){
      lastTap=null;
      suppressClick=true;
      centerOn(Date.now(), 'smooth');
    }else lastTap={...current,time:event.timeStamp};
  },{passive:true,capture:true});
  window.addEventListener('pointercancel',event=>{pointers.delete(event.pointerId);reset()},{passive:true,capture:true});
  window.addEventListener('blur',()=>{pointers.clear();reset();suppressClick=false});
  ruler.addEventListener('scroll',reset,{passive:true});
  // The jump can put a marker or readout under the pointer before its click.
  window.addEventListener('click',event=>{if(suppressClick){suppressClick=false;event.preventDefault();event.stopImmediatePropagation()}},true);
}
function setScale(next){next=Math.max(0,Math.min(scales.length-1,next));if(next===scaleIndex)return;const center=timeForX(ruler.scrollLeft+ruler.clientWidth/2);scaleIndex=next;setTrackWidth();centerOn(center);queueRender()}
function recenterIfNeeded(){const center=timeForX(ruler.scrollLeft+ruler.clientWidth/2);if(center-origin<SPAN*.2||center-origin>SPAN*.8){origin=center-SPAN/2;setTrackWidth();centerOn(center);queueRender()}}
function queueRender(){if(!renderQueued){renderQueued=true;requestAnimationFrame(()=>{renderQueued=false;render()})}}
function scheduleRender(){playRatchet();renderPlayheadHit(timeForX(ruler.scrollLeft+ruler.clientWidth/2),true);queueRender();clearTimeout(scrollTimer);scrollTimer=setTimeout(recenterIfNeeded,180)}

function updateClock(){const now=Date.now();$('#recordClock').textContent=formatTime(now,true);updateNow(now)}
function updateNow(now=Date.now()){const nx=xFor(now);nowLine.style.left=`${nx}px`;nowLine.hidden=nx<0||nx>track.clientWidth}
function render(){if(!ruler.clientWidth)return;const start=timeForX(Math.max(0,ruler.scrollLeft-ruler.clientWidth));const end=timeForX(Math.min(track.clientWidth,ruler.scrollLeft+ruler.clientWidth*2));renderTicks(start,end);renderMarkers(start,end);const center=timeForX(ruler.scrollLeft+ruler.clientWidth/2);viewCenterTime=center;renderPlayheadHit(center);$('#viewDate').textContent=`${formatDate(center)}  ${formatTime(center)}`;updateNow()}
function resizeTimeline(){setTrackWidth();centerOn(viewCenterTime);queueRender()}
function renderCounts(){const counts=new Map();events.forEach(e=>{const color=e.color.toLowerCase();counts.set(color,(counts.get(color)||0)+1)});const ordered=[...colors.map(c=>c.toLowerCase()),selectedColor.toLowerCase(),...counts.keys()].filter((c,i,a)=>a.indexOf(c)===i);const fragment=document.createDocumentFragment();ordered.forEach(color=>{const b=document.createElement('button');b.type='button';b.className='color-count';if(color===selectedColor.toLowerCase())b.classList.add('is-selected');b.style.setProperty('--count-color',color);b.textContent=counts.get(color)||0;b.setAttribute('aria-label',`${color} の記録 ${counts.get(color)||0}件。記録色に選択`);b.onclick=()=>chooseColor(color);fragment.append(b)});$('#totalCount').textContent=events.length;$('#colorCounts').replaceChildren(fragment)}
function renderTicks(start,end){const key=[origin,scaleIndex,pxPerMs(),Math.floor(start/scales[scaleIndex].tick),Math.floor(end/scales[scaleIndex].tick)].join(':');if(key===tickRenderKey)return;tickRenderKey=key;const tick=scales[scaleIndex].tick;const fragment=document.createDocumentFragment();const first=Math.floor(start/tick)*tick;for(let t=first;t<=end;t+=tick){const d=new Date(t),major=d.getMinutes()===0,mid=!major&&d.getMinutes()%15===0;const line=document.createElement('i');line.className=`tick ${major?'':mid?'medium':'minor'}`;line.style.left=`${xFor(t)}px`;fragment.append(line);if(major||tick>=3600000){const l=document.createElement('span');l.className='tick-label';l.style.left=`${xFor(t)}px`;l.textContent=formatTime(t);fragment.append(l)}if(d.getHours()===0&&d.getMinutes()===0){const dl=document.createElement('i');dl.className='day-line';dl.style.left=`${xFor(t)}px`;fragment.append(dl);const date=document.createElement('span');date.className='tick-label tick-date';date.style.left=`${xFor(t)}px`;date.textContent=formatDate(t);fragment.append(date)}}ticks.replaceChildren(fragment)}
function renderMarkers(start,end){
  const first=eventIndex(start),last=eventIndex(end+1),key=[origin,scaleIndex,pxPerMs(),first,last,eventsRevision].join(':');
  if(key===markerRenderKey)return;
  markerRenderKey=key;
  const fragment=document.createDocumentFragment(),recent=[],laneCounts=[0,0,0],windowMs=Math.max(12/pxPerMs(),120000);
  let head=0;
  for(let i=first;i<last;i++){
    const e=events[i];
    while(head<recent.length&&e.timestamp-recent[head].timestamp>=windowMs)laneCounts[recent[head++].lane]--;
    let lane=laneCounts.findIndex(count=>count===0);
    if(lane<0)lane=(recent.length-head)%3;
    recent.push({timestamp:e.timestamp,lane});laneCounts[lane]++;
    const b=document.createElement('button');b.className=`marker lane-${lane}`;b.style.left=`${xFor(e.timestamp)}px`;b.style.setProperty('--marker',e.color);b.setAttribute('aria-label',`${e.text} ${formatTime(e.timestamp,true)}`);b.onclick=()=>openDetail(e.id);fragment.append(b);
  }
  markers.replaceChildren(fragment);
}
function renderPlayheadHit(center,allowSound=false){const tolerance=12/pxPerMs();let hit=null,distance=Infinity;const next=eventIndex(center),previous=next>0?eventIndex(events[next-1].timestamp):-1;for(const i of [previous,next]){const e=events[i];if(!e)continue;const d=Math.abs(e.timestamp-center);if(d<distance){distance=d;hit=e}}const readout=$('#playheadReadout');if(!hit||distance>tolerance){lastPlayheadMarkerId=null;readout.classList.remove('is-visible');readout.setAttribute('aria-hidden','true');delete readout.dataset.eventId;return}if(hit.id!==lastPlayheadMarkerId){lastPlayheadMarkerId=hit.id;if(allowSound)playOrbSound()}readout.dataset.eventId=hit.id;readout.classList.add('is-visible');readout.setAttribute('aria-hidden','false');$('#playheadSwatch').style.setProperty('--orb-color',hit.color);$('#playheadText').textContent=hit.text;$('#playheadTime').textContent=formatTime(hit.timestamp,true)}

async function record(){
  const b=$('#recordButton');
  if(b.disabled||dataBusy)return;
  recoverAudioFromGesture('record-click');
  const text=$('#eventText').value.trim();
  if(!text){$('#eventText').focus();showToast('内容を入力してください');return}
  const item={id:newEventId(),text,color:selectedColor,timestamp:Date.now()};
  b.disabled=true;b.classList.add('is-saving');
  try{
    // Start audio inside the user gesture, before awaiting IndexedDB.
    try{playRecordSound()}catch(error){console.warn('[Event Ruler audio] record playback failed',error)}
    await dataAction(async()=>{await putEvent(item);showToast('記録しました');try{navigator.vibrate?.(18)}catch{}},'保存に失敗しました。記録されていません');
  }finally{setTimeout(()=>{b.disabled=false;b.classList.remove('is-saving')},260)}
}
function openDetail(id){const e=events.find(x=>x.id===id);if(!e)return;selectedId=id;$('#detailText').value=e.text;$('#detailColor').value=e.color;$('#detailDate').textContent=formatDate(e.timestamp);$('#detailTime').textContent=formatTime(e.timestamp,true);$('#detailDialog').style.setProperty('--detail-color',e.color);$('#detailDialog').showModal()}
function installDetailBackdropClose(){
  const dialog=$('#detailDialog');
  let startedOutside=false;
  const outside=event=>{
    const rect=dialog.getBoundingClientRect();
    return event.target===dialog&&(event.clientX<rect.left||event.clientX>rect.right||event.clientY<rect.top||event.clientY>rect.bottom);
  };
  dialog.addEventListener('pointerdown',event=>{startedOutside=event.isPrimary&&event.button===0&&outside(event)},{passive:true});
  dialog.addEventListener('pointercancel',()=>{startedOutside=false},{passive:true});
  dialog.addEventListener('click',event=>{if(startedOutside&&outside(event))dialog.close();startedOutside=false});
  dialog.addEventListener('close',()=>{startedOutside=false});
}
async function saveDetail(){
  const e=events.find(x=>x.id===selectedId);if(!e)return;
  const item={...e,text:$('#detailText').value.trim()||e.text,color:$('#detailColor').value};
  await dataAction(async()=>{await putEvent(item);$('#detailDialog').close();showToast('変更を保存しました')},'変更を保存できませんでした');
}
async function deleteSelected(){
  const e=events.find(x=>x.id===selectedId);if(!e)return;
  await dataAction(async()=>{await removeEvent(e.id);undoItem={...e};$('#detailDialog').close();showUndo()},'削除できませんでした');
}
function showUndo(){clearTimeout(undoTimer);$('#undoBar').hidden=false;undoTimer=setTimeout(clearUndo,6000)}
async function undo(){
  if(!undoItem||dataBusy)return;
  const item=undoItem;clearTimeout(undoTimer);
  const ok=await dataAction(async()=>{await putEvent(item);if(undoItem===item)clearUndo();showToast('元に戻しました')},'復元できませんでした');
  if(!ok&&undoItem===item)showUndo();
}
function showToast(msg){const t=$('#toast');t.textContent=msg;t.classList.add('show');clearTimeout(t._timer);t._timer=setTimeout(()=>t.classList.remove('show'),1500)}

function download(name,type,data){const a=document.createElement('a');a.href=URL.createObjectURL(new Blob([data],{type}));a.download=name;a.click();setTimeout(()=>URL.revokeObjectURL(a.href),1000)}
function exportJSON(){download(`event-ruler-${formatDate(Date.now())}.json`,'application/json',JSON.stringify({version:1,exportedAt:new Date().toISOString(),events},null,2))}
function exportCSV(){const esc=v=>`"${String(v).replaceAll('"','""')}"`;const rows=[['id','text','color','timestamp','datetime'],...events.map(e=>[e.id,e.text,e.color,e.timestamp,new Date(e.timestamp).toISOString()])];download(`event-ruler-${formatDate(Date.now())}.csv`,'text/csv;charset=utf-8','\ufeff'+rows.map(r=>r.map(esc).join(',')).join('\n'))}
function validateImportedEvent(e,index){
  const invalid=()=>{throw new Error(`${index+1}件目のデータが不正です`)};
  if(!e||typeof e!=='object'||Array.isArray(e))invalid();
  if(typeof e.text!=='string'||!e.text.trim()||e.text.length>120)invalid();
  if(typeof e.timestamp!=='number'||!Number.isSafeInteger(e.timestamp)||Math.abs(e.timestamp)>8640000000000000)invalid();
  if(typeof e.color!=='string'||!/^#[0-9a-f]{6}$/i.test(e.color))invalid();
  if(e.id!==undefined&&(typeof e.id!=='string'||!e.id.trim()||e.id.length>200))invalid();
  return {id:e.id===undefined?newEventId():e.id,text:e.text,color:e.color,timestamp:e.timestamp};
}
async function importJSON(file){
  await dataAction(async()=>{
    let data;try{data=JSON.parse(await file.text())}catch{throw new Error('JSON形式が不正です')}
    const input=Array.isArray(data)?data:data?.events;
    if(!Array.isArray(input)||(!Array.isArray(data)&&data.version!==undefined&&data.version!==1))throw new Error('未対応のJSON形式です');
    const items=new Map();
    for(let i=0;i<input.length;i++){
      const item=validateImportedEvent(input[i],i);items.set(item.id,item);
      if(i&&i%1000===0)await new Promise(resolve=>setTimeout(resolve,0));
    }
    // Last entry wins for duplicate IDs; existing IDs are replaced atomically.
    await writeTransaction(store=>{for(const item of items.values())store.put(item)});
    const merged=new Map(events.map(e=>[e.id,e]));
    for(const item of items.values())merged.set(item.id,item);
    events=Array.from(merged.values()).sort((a,b)=>a.timestamp-b.timestamp);
    clearUndo();eventsChanged();showToast(`${items.size}件を読み込みました（同じIDは上書き）`);
  },'インポートに失敗しました。データは変更されていません');
}
async function deleteAll(){
  if(dataBusy||!events.length)return;
  if(!confirm(`${events.length}件の記録をすべて削除しますか？\nこの操作は取り消せません。`))return;
  await dataAction(async()=>{await writeTransaction(store=>store.clear());events=[];clearUndo();eventsChanged();showToast('すべて削除しました')},'全削除に失敗しました');
}

function bind(){installDetailBackdropClose();ruler.addEventListener('scroll',scheduleRender,{passive:true});installRulerDoubleTap();$('#recordButton').onclick=record;$('#eventText').addEventListener('keydown',e=>{if(e.key==='Enter'){e.preventDefault();record()}});$('#customColor').oninput=e=>chooseColor(e.target.value);$('#saveButton').onclick=saveDetail;$('#deleteButton').onclick=deleteSelected;$('#undoButton').onclick=undo;$('#detailText').addEventListener('keydown',e=>{if(e.key==='Enter')e.preventDefault()});$('#detailColor').oninput=e=>$('#detailDialog').style.setProperty('--detail-color',e.target.value);const menu=$('#dataMenu');$('#menuButton').onclick=()=>{menu.hidden=!menu.hidden;$('#menuButton').setAttribute('aria-expanded',!menu.hidden)};menu.onclick=e=>{const a=e.target.dataset.action;if(!a)return;menu.hidden=true;if(a==='export-json')exportJSON();if(a==='export-csv')exportCSV();if(a==='import-json')$('#importInput').click();if(a==='delete-all')deleteAll()};$('#importInput').onchange=e=>{if(e.target.files[0])importJSON(e.target.files[0]);e.target.value=''};let pinch=0;ruler.addEventListener('touchstart',e=>{if(e.touches.length===2)pinch=Math.abs(e.touches[0].clientX-e.touches[1].clientX)},{passive:true});ruler.addEventListener('touchend',e=>{if(pinch&&e.touches.length<2)pinch=0},{passive:true});ruler.addEventListener('touchmove',e=>{if(e.touches.length===2&&pinch){const d=Math.abs(e.touches[0].clientX-e.touches[1].clientX);if(Math.abs(d-pinch)>45){setScale(scaleIndex+(d>pinch?-1:1));pinch=d}}},{passive:true})}

async function init(){prepareAudioAtStartup();initTheme();chooseColor(selectedColor);installAudioRecovery();$('#playheadReadout').onclick=e=>{const id=e.currentTarget.dataset.eventId;if(id)openDetail(id)};bind();window.addEventListener('resize',resizeTimeline);setTrackWidth();db=await openDB();await loadEvents();requestAnimationFrame(()=>{centerOn(Date.now());queueRender()});updateClock();setInterval(updateClock,1000);if('serviceWorker'in navigator)navigator.serviceWorker.register('service-worker.js',{updateViaCache:'none'}).then(reg=>reg.update()).catch(error=>console.warn('[Event Ruler offline]',error))}
init().catch(()=>showToast('保存領域を開けませんでした'));
