const VEHICLES = ['APUC-01','APUC-02','APUC-03','APUC-04','APUC-05','APUC-06','APUC-07','APUC-08'];
const APUCARANA_CENTER = [-23.5505, -51.4603];
let selectedVehicle = 'APUC-01';
let selectedRouteId = '';
let showAllActivity = false;
let db, map, markersLayer, routeLineLayer, streetLayer, satelliteLayer;
let currentBaseMap = 'street';
let tempIncidentPhoto = null;
let manualPhotoDragMarker=null;
let manualPhotoDragId='';
let mapObjectUrls = [];
let galleryObjectUrls = [];
let photoModalUrl = null;
let ocrWorkerPromises = [];
const OCR_POOL_SIZE = Math.min(2, Math.max(1, (navigator.hardwareConcurrency||4) >= 4 ? 2 : 1));
const geocodeCache = new Map();
let surveyAddressLookupCache = null;
let googleMapsLoadPromise = null;
const APUCARANA_BOUNDS = {south:-23.78,north:-23.32,west:-51.78,east:-51.16};

// Google Drive cloud sync
const DRIVE_SCOPE='https://www.googleapis.com/auth/drive.file';
const DRIVE_FOLDER_NAME='APUC Rotas';
const DRIVE_BACKUP_NAME='apuc-rotas-dados.json';
let driveAccessToken='';
let driveTokenExpiresAt=0;
let driveTokenClient=null;
let driveFolderId='';
let driveDataFileId='';
let cloudAutoSync=false;
let cloudDirty=false;
let cloudSyncTimer=null;
let cloudSyncInFlight=false;
let cloudSyncSuspend=0;

const ALL_REPORT_SCOPE='__ALL__';
const INSPECTION_REQ_KEYS=['telha_ceramica','telha_fibrocimento','telha_metalica','muro','grade_portao','vidro_comum','vidro_temperado','padrao_energia'];
const INSPECTION_LABELS={telha_ceramica:'Telha cerâmica',telha_fibrocimento:'Telha de fibrocimento',telha_metalica:'Telha metálica',muro:'Muro',grade_portao:'Grade / portão',vidro_comum:'Vidro comum',vidro_temperado:'Vidro temperado',padrao_energia:'Padrão de energia'};
function inspectionUnitNeighborhood(u){return String(u?.neighborhood||u?.sourceNeighborhood||(u?.vehicle?`A identificar — ${u.vehicle}`:'A identificar')).trim()}
function inspectionIsAffected(u){return !!u?.affected||INSPECTION_REQ_KEYS.some(k=>Number(u?.requirements?.[k]||0)>0)}
function inspectionRequirementText(u){const c=window.APUC_BUDGET_CATALOG||{};const parts=[];for(const k of INSPECTION_REQ_KEYS){const q=Number(u?.requirements?.[k]||0);if(q>0){const unit=c[k]?.unit||'';parts.push(`${INSPECTION_LABELS[k]}: ${q.toLocaleString('pt-BR',{maximumFractionDigits:2})}${unit?' '+unit:''}`)}}return parts.join('; ')||'Sem quantitativos informados'}
function inspectionBudgetForUnits(units=[]){const cat=window.APUC_BUDGET_CATALOG||{};const items=[];let total=0;for(const k of INSPECTION_REQ_KEYS){const qty=units.reduce((s,u)=>s+Number(u?.requirements?.[k]||0),0);if(qty<=0)continue;const unitPrice=Number(cat[k]?.unitPrice||0);const subtotal=qty*unitPrice;total+=subtotal;items.push({key:k,label:cat[k]?.label||INSPECTION_LABELS[k],unit:cat[k]?.unit||'',qty,unitPrice,subtotal,code:cat[k]?.code||'',description:cat[k]?.description||'',source:cat[k]?.source||'',note:cat[k]?.note||''})}return {items,total}}
function inspectionByNeighborhood(units=[]){const m=new Map();for(const u of units.filter(inspectionIsAffected)){const n=inspectionUnitNeighborhood(u);const key=normalizeNeighborhood(n);if(!m.has(key))m.set(key,{name:n,units:[]});m.get(key).units.push(u)}return [...m.values()].map(g=>({...g,count:g.units.length,budget:inspectionBudgetForUnits(g.units)})).sort((a,b)=>a.name.localeCompare(b.name,'pt-BR'))}
function inspectionMoney(n){return Number(n||0).toLocaleString('pt-BR',{style:'currency',currency:'BRL'})}

const $ = (id) => document.getElementById(id);
const esc = (v='') => String(v).replace(/[&<>'"]/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;',"'":'&#39;','"':'&quot;'}[c]));
const fmtDate = (value) => value ? new Date(value + (value.length===10?'T12:00:00':'')).toLocaleString('pt-BR',{dateStyle:'short',timeStyle:value.length>10?'short':undefined}) : '—';
const uid = () => crypto.randomUUID ? crypto.randomUUID() : Date.now().toString(36)+Math.random().toString(36).slice(2);
const routeSorter = (a,b) => String(b.date||'').localeCompare(String(a.date||'')) || String(b.updatedAt||'').localeCompare(String(a.updatedAt||''));

function toast(msg){ const el=$('toast'); el.textContent=msg; el.classList.add('show'); setTimeout(()=>el.classList.remove('show'),2600); }
function revokeUrls(list){ while(list.length){ try{ URL.revokeObjectURL(list.pop()); }catch{} } }

function openDB(){
  return new Promise((resolve,reject)=>{
    const req=indexedDB.open('apucRotasDB',4);
    req.onupgradeneeded=()=>{
      const d=req.result;
      if(!d.objectStoreNames.contains('routes')) d.createObjectStore('routes',{keyPath:'id'});
      if(!d.objectStoreNames.contains('photos')) d.createObjectStore('photos',{keyPath:'id'});
      if(!d.objectStoreNames.contains('incidents')) d.createObjectStore('incidents',{keyPath:'id'});
      if(!d.objectStoreNames.contains('settings')) d.createObjectStore('settings',{keyPath:'key'});
      if(!d.objectStoreNames.contains('reports')) d.createObjectStore('reports',{keyPath:'id'});
      if(!d.objectStoreNames.contains('surveyUnits')) d.createObjectStore('surveyUnits',{keyPath:'id'});
    };
    req.onsuccess=()=>resolve(req.result); req.onerror=()=>reject(req.error);
  });
}
function store(name,mode='readonly'){return db.transaction(name,mode).objectStore(name)}
function getAll(name){return new Promise((res,rej)=>{const r=store(name).getAll();r.onsuccess=()=>res(r.result);r.onerror=()=>rej(r.error)})}
function put(name,val){return new Promise((res,rej)=>{const r=store(name,'readwrite').put(val);r.onsuccess=()=>{markCloudDirty();res(val)};r.onerror=()=>rej(r.error)})}
function del(name,key){return new Promise((res,rej)=>{const r=store(name,'readwrite').delete(key);r.onsuccess=()=>{markCloudDirty();res()};r.onerror=()=>rej(r.error)})}
function clearStore(name){return new Promise((res,rej)=>{const r=store(name,'readwrite').clear();r.onsuccess=()=>{markCloudDirty();res()};r.onerror=()=>rej(r.error)})}
function blobToDataURL(blob){return new Promise((resolve,reject)=>{if(!blob)return resolve(null);const r=new FileReader();r.onload=()=>resolve(r.result);r.onerror=reject;r.readAsDataURL(blob)})}
function dataURLToBlob(dataURL){if(!dataURL)return null;const [head,data]=dataURL.split(',');const mime=(head.match(/:(.*?);/)||[])[1]||'image/jpeg';const bytes=atob(data);const arr=new Uint8Array(bytes.length);for(let i=0;i<bytes.length;i++)arr[i]=bytes.charCodeAt(i);return new Blob([arr],{type:mime})}
function parseCoord(v){ if(v===null||v===undefined||String(v).trim()==='')return null;const n=Number(String(v).replace(',','.'));return Number.isFinite(n)?n:null }

function validCoords(lat,lng){return Number.isFinite(lat)&&Number.isFinite(lng)&&Math.abs(lat)<=90&&Math.abs(lng)<=180}
function signedHemisphere(value,hem){
  const h=String(hem||'').toUpperCase();
  const n=Math.abs(Number(value));
  return ['S','W','O'].includes(h)?-n:n;
}
function dmsToDecimal(d,m=0,s=0,hem=''){
  const v=Math.abs(Number(d))+(Number(m)||0)/60+(Number(s)||0)/3600;
  return signedHemisphere(v,hem);
}
function parseCoordinatesFromText(raw){
  if(!raw)return null;
  let text=String(raw)
    .replace(/[−–—]/g,'-').replace(/[º˚]/g,'°').replace(/[’`´]/g,"'").replace(/[“”]/g,'"')
    .replace(/\bL0N\b/gi,'LON').replace(/\bL0NG\b/gi,'LONG')
    .replace(/(?<=\d)[|](?=\d)/g,'1');

  // 1) Graus, minutos e segundos: 23°33'02.1"S 51°27'37.2"W/O
  const dms=[];
  const dmsRe=/(\d{1,3})\s*°\s*(\d{1,2})\s*['′]?\s*(\d{1,2}(?:[.,]\d+)?)\s*["″]?\s*([NSWEO])/gi;
  let m;
  while((m=dmsRe.exec(text))){dms.push({value:dmsToDecimal(m[1],m[2],String(m[3]).replace(',','.'),m[4]),hem:m[4].toUpperCase()})}
  if(dms.length>=2){
    const lat=dms.find(x=>['N','S'].includes(x.hem));
    const lng=dms.find(x=>['E','W','O'].includes(x.hem));
    if(lat&&lng&&validCoords(lat.value,lng.value))return {lat:lat.value,lng:lng.value,format:'DMS'};
  }

  // 2) Graus e minutos decimais: 23°33.1234'S 51°27.1234'W
  const ddm=[];
  const ddmRe=/(\d{1,3})\s*°\s*(\d{1,2}(?:[.,]\d+)?)\s*['′]?\s*([NSWEO])/gi;
  while((m=ddmRe.exec(text))){ddm.push({value:dmsToDecimal(m[1],String(m[2]).replace(',','.'),0,m[3]),hem:m[3].toUpperCase()})}
  if(ddm.length>=2){
    const lat=ddm.find(x=>['N','S'].includes(x.hem));
    const lng=ddm.find(x=>['E','W','O'].includes(x.hem));
    if(lat&&lng&&validCoords(lat.value,lng.value))return {lat:lat.value,lng:lng.value,format:'graus/minutos'};
  }

  // 3) Decimal com rótulos Latitude / Longitude.
  const latM=text.match(/(?:LAT(?:ITUDE)?|Y)\s*[:=]?\s*([+-]?\d{1,2}(?:[.,]\d{4,}))/i);
  const lngM=text.match(/(?:LON(?:G(?:ITUDE)?)?|LONG|X)\s*[:=]?\s*([+-]?\d{1,3}(?:[.,]\d{4,}))/i);
  if(latM&&lngM){
    let lat=Number(latM[1].replace(',','.')),lng=Number(lngM[1].replace(',','.'));
    if(/\bS\b/i.test(text)&&lat>0)lat=-lat;if(/\b(?:W|O)\b/i.test(text)&&lng>0)lng=-lng;
    if(validCoords(lat,lng))return {lat,lng,format:'decimal rotulado'};
  }

  // 4) Hemisfério antes/depois do decimal: S 23.550500 / 51.460300 W
  const hemi=[];
  const hemiRe=/(?:([NSWEO])\s*)?([+-]?\d{1,3}(?:[.,]\d{4,}))\s*°?\s*([NSWEO])?/gi;
  while((m=hemiRe.exec(text))){
    const hem=(m[1]||m[3]||'').toUpperCase(); if(!hem)continue;
    hemi.push({value:signedHemisphere(Number(m[2].replace(',','.')),hem),hem});
  }
  if(hemi.length>=2){
    const lat=hemi.find(x=>['N','S'].includes(x.hem));const lng=hemi.find(x=>['E','W','O'].includes(x.hem));
    if(lat&&lng&&validCoords(lat.value,lng.value))return {lat:lat.value,lng:lng.value,format:'decimal hemisfério'};
  }

  // 5) Dois decimais. Para Apucarana/PR, corrige sinal quando a sobreposição omite S/O.
  const vals=(text.match(/[+-]?\d{1,3}(?:[.,]\d{4,})/g)||[]).map(v=>Number(v.replace(',','.'))).filter(Number.isFinite);
  for(let a=0;a<vals.length;a++)for(let b=a+1;b<vals.length;b++){
    let x=vals[a],y=vals[b],lat=null,lng=null;
    if(Math.abs(x)>=20&&Math.abs(x)<=30&&Math.abs(y)>=45&&Math.abs(y)<=60){lat=x;lng=y}
    else if(Math.abs(y)>=20&&Math.abs(y)<=30&&Math.abs(x)>=45&&Math.abs(x)<=60){lat=y;lng=x}
    if(lat!==null){
      if(lat>0)lat=-lat;if(lng>0)lng=-lng;
      if(validCoords(lat,lng))return {lat,lng,format:'decimal'};
    }
  }
  return null;
}
function coordSourceLabel(p){
  if(p?.coordSource==='overlay-right')return 'OCR • coordenadas no canto inferior direito';
  if(p?.coordSource==='address-overlay-left')return p?.mapInsetProvider==='Base de vistoria local'?'OCR + BASE LOCAL • endereço no canto inferior esquerdo':'OCR + GOOGLE MAPS • endereço no canto inferior esquerdo';
  if(p?.coordSource==='google-inset-coordinates')return 'OCR • coordenadas no mini mapa';
  if(p?.coordSource==='google-inset')return 'GOOGLE MAPS • mini mapa';
  if(p?.coordSource==='manual-address')return 'AJUSTE MANUAL • endereço';
  if(p?.coordSource==='manual-pin')return 'AJUSTE MANUAL • pin no mapa';
  if(p?.coordSource==='exif')return 'GPS/EXIF';
  return 'coordenada salva';
}
async function getOcrWorker(slot=0){
  if(!window.Tesseract)throw new Error('Módulo OCR não carregado. Verifique a conexão com a internet.');
  const idx=Math.max(0,Math.min(OCR_POOL_SIZE-1,Number(slot)||0));
  if(!ocrWorkerPromises[idx])ocrWorkerPromises[idx]=(async()=>{
    // Sem logger por caractere/progresso: reduz atualizações de DOM e deixa o OCR sensivelmente mais rápido.
    const worker=await Tesseract.createWorker('eng',1);
    await worker.setParameters({tessedit_pageseg_mode:'6',preserve_interword_spaces:'1'});
    return worker;
  })();
  return ocrWorkerPromises[idx];
}
async function loadImageDrawable(blob){
  if(window.createImageBitmap)return await createImageBitmap(blob);
  return await new Promise((resolve,reject)=>{const url=URL.createObjectURL(blob),img=new Image();img.onload=()=>{img._objectUrl=url;resolve(img)};img.onerror=e=>{URL.revokeObjectURL(url);reject(e)};img.src=url});
}
function closeImageDrawable(drawable){try{drawable?.close?.()}catch{};if(drawable?._objectUrl)try{URL.revokeObjectURL(drawable._objectUrl)}catch{}}
function cropDrawable(drawable,spec,targetWidth=1700,mode='original',contrast=2,threshold=148,maxScale=3.2,minScale=1.6){
  const sx=Math.round(drawable.width*spec.x),sy=Math.round(drawable.height*spec.y),sw=Math.max(1,Math.round(drawable.width*spec.w)),sh=Math.max(1,Math.round(drawable.height*spec.h));
  const scale=Math.min(maxScale,Math.max(minScale,targetWidth/sw));
  const canvas=document.createElement('canvas');canvas.width=Math.max(1,Math.round(sw*scale));canvas.height=Math.max(1,Math.round(sh*scale));
  const ctx=canvas.getContext('2d',{willReadFrequently:true});ctx.drawImage(drawable,sx,sy,sw,sh,0,0,canvas.width,canvas.height);
  if(mode!=='original'){
    const img=ctx.getImageData(0,0,canvas.width,canvas.height),d=img.data;
    for(let i=0;i<d.length;i+=4){
      let g=.299*d[i]+.587*d[i+1]+.114*d[i+2];
      if(mode==='contrast')g=Math.max(0,Math.min(255,(g-128)*contrast+128));
      else if(mode==='threshold')g=g>threshold?255:0;
      else if(mode==='invert')g=g>threshold?0:255;
      d[i]=d[i+1]=d[i+2]=g;
    }
    ctx.putImageData(img,0,0);
  }
  return canvas;
}
function makeCoordinateOverlayCropFromDrawable(drawable,variant=0,mode='original'){
  const specs=[
    {x:.44,y:.70,w:.56,h:.30},
    {x:.30,y:.58,w:.70,h:.42},
    {x:0,y:.77,w:1,h:.23},
    {x:.52,y:.48,w:.48,h:.52}
  ];
  return cropDrawable(drawable,specs[Math.min(variant,specs.length-1)],1650,mode,1.9,145,3.2,1.7);
}
async function readCoordinateOverlay(blob,{worker=null,drawable=null}={}){
  const ownDrawable=!drawable; if(!drawable)drawable=await loadImageDrawable(blob);
  worker=worker||await getOcrWorker(0);
  // Duas leituras rápidas primeiro; só expande a área se necessário.
  const fast=[[0,'original','6'],[0,'contrast','6']];
  const fallback=[[1,'contrast','11'],[2,'threshold','6'],[3,'contrast','11']];
  let combined='',bestConfidence=0;
  const whitelist='0123456789.,;:+-°º˚\\\'"′″NSWEOXYZLATITUDEONGlatitudelongxyz /\\n';
  try{
    for(const [variant,mode,psm] of [...fast,...fallback]){
      const canvas=makeCoordinateOverlayCropFromDrawable(drawable,variant,mode);
      await worker.setParameters({tessedit_pageseg_mode:psm,tessedit_char_whitelist:whitelist,preserve_interword_spaces:'1'});
      const result=await worker.recognize(canvas);const txt=result?.data?.text||'';const conf=Number(result?.data?.confidence||0);
      if(conf>bestConfidence)bestConfidence=conf;combined+=(combined?'\n':'')+txt;
      const coords=parseCoordinatesFromText(txt);
      if(coords&&inApucaranaBounds(coords.lat,coords.lng)){
        await worker.setParameters({tessedit_pageseg_mode:'6',tessedit_char_whitelist:'',preserve_interword_spaces:'1'});
        return {...coords,overlayText:combined.trim(),confidence:conf,method:'overlay-right'};
      }
    }
    await worker.setParameters({tessedit_pageseg_mode:'6',tessedit_char_whitelist:'',preserve_interword_spaces:'1'});
    return {lat:null,lng:null,overlayText:combined.trim(),confidence:bestConfidence,method:'overlay-right',error:'Não foi possível confirmar coordenadas válidas no canto inferior direito.'};
  }finally{if(ownDrawable)closeImageDrawable(drawable)}
}

function cleanAddressOcrText(raw){
  return String(raw||'')
    .replace(/\r/g,'\n').replace(/[|]/g,'I').replace(/[“”]/g,'"').replace(/[’`´]/g,"'").replace(/[–—]/g,'-').replace(/\s+/g,' ').trim();
}
function addressLineScore(line){
  const low=line.toLowerCase();let score=0;
  if(/\b(?:rua|r\.?|avenida|av\.?|travessa|tv\.?|alameda|rodovia|estrada|pra[cç]a|largo|via)\b/i.test(line))score+=6;
  if(/\b\d{1,5}[a-z]?\b/i.test(line))score+=3;if(/apucarana|paran[aá]|\bpr\b/i.test(low))score+=2;if(/[A-Za-zÀ-ÿ]{4,}/.test(line))score+=1;
  if(/google|maps|street view|coordenad|latitude|longitude/i.test(low))score-=4;return score;
}
function normalizeStreetPrefix(text){return text.replace(/^\s*R\.?\s+/i,'Rua ').replace(/^\s*Av\.?\s+/i,'Avenida ').replace(/^\s*Tv\.?\s+/i,'Travessa ').replace(/^\s*Rod\.?\s+/i,'Rodovia ')}
function extractAddressQueries(raw){
  const originalLines=String(raw||'').replace(/\r/g,'\n').split(/\n+/).map(x=>x.replace(/[^\p{L}\p{N}\s.,º°ª#\-/]/gu,' ').replace(/\s+/g,' ').trim()).filter(Boolean);
  const lines=originalLines.filter(x=>x.length>=3&&!/google|maps|street view|imagery|copyright/i.test(x));
  const ranked=lines.map((line,i)=>({line:normalizeStreetPrefix(line),i,score:addressLineScore(line)})).sort((a,b)=>b.score-a.score);const out=[];
  const push=q=>{q=String(q||'').replace(/\s+/g,' ').replace(/\s+,/g,',').trim();if(q&&!out.includes(q))out.push(q)};
  const streetWords='(?:Rua|R\\.?|Avenida|Av\\.?|Travessa|Tv\\.?|Alameda|Rodovia|Estrada|Pra[cç]a|Largo|Via)';const fullText=lines.join(' | ');
  const fullRe=new RegExp(`(${streetWords}\\s+[\\p{L}0-9 .'-]{3,80}?)(?:[,\\s]+(?:n[º°o.]?\\s*)?(\\d{1,5}[A-Za-z]?))(?=\\s*(?:[,|]|$))`,'giu');let m;
  while((m=fullRe.exec(fullText)))push(`${normalizeStreetPrefix(m[1].replace(/\s+/g,' ').trim())}, ${m[2]}, Apucarana, PR, Brasil`);
  for(const item of ranked.slice(0,6)){
    const line=item.line;if(item.score<2)continue;
    const same=line.match(new RegExp(`^(${streetWords}\\s+.+?)(?:[,\\s]+(?:n[º°o.]?\\s*)?(\\d{1,5}[A-Za-z]?))$`,'iu'));if(same)push(`${normalizeStreetPrefix(same[1])}, ${same[2]}, Apucarana, PR, Brasil`);
    const next=lines[item.i+1]||'';const nextNum=next.match(/^(?:n[º°o.]?\s*)?(\d{1,5}[A-Za-z]?)$/i)?.[1];if(nextNum&&/\b(?:rua|r\.?|avenida|av\.?|travessa|tv\.?|alameda|rodovia|estrada|pra[cç]a|largo|via)\b/i.test(line))push(`${line}, ${nextNum}, Apucarana, PR, Brasil`);
    if(/\b(?:rua|r\.?|avenida|av\.?|travessa|tv\.?|alameda|rodovia|estrada|pra[cç]a|largo|via)\b/i.test(line))push(`${line}, Apucarana, PR, Brasil`);
  }
  for(const item of ranked.slice(0,4)){const line=item.line;if(/\b\d{1,5}[A-Za-z]?\b/.test(line)&&/[A-Za-zÀ-ÿ]{3,}/.test(line))push(`${line}, Apucarana, PR, Brasil`)}
  return out.slice(0,8);
}
function normalizeAddressMatch(s){return String(s||'').normalize('NFD').replace(/[\u0300-\u036f]/g,'').toLowerCase().replace(/\b(apucarana|parana|pr|brasil|cep|numero|nº|n°)\b/g,' ').replace(/\bavenida\b/g,'av').replace(/\bru(a)?\b/g,'r').replace(/[^a-z0-9 ]/g,' ').replace(/\s+/g,' ').trim()}
async function findSurveyAddressMatch(query){
  if(!surveyAddressLookupCache){const units=await getSurveyUnits();surveyAddressLookupCache=units.filter(u=>validCoords(Number(u.lat),Number(u.lng))&&(u.address||u.formattedAddress)).map(u=>({u,key:normalizeAddressMatch(`${u.address||''} ${u.formattedAddress||''}`)}));}
  const q=normalizeAddressMatch(query);if(!q)return null;const qNum=(q.match(/\b\d{1,5}\b/g)||[]).at(-1)||'';const qWords=q.split(' ').filter(x=>x.length>=3&&!/^\d+$/.test(x));
  let best=null,bestScore=0;
  for(const x of surveyAddressLookupCache){const u=x.u,k=x.key;if(!k)continue;const kNums=k.match(/\b\d{1,5}\b/g)||[];if(qNum&&kNums.length&&!kNums.includes(qNum))continue;const overlap=qWords.filter(w=>k.includes(w)).length;const score=qWords.length?overlap/qWords.length:0;if(score>bestScore){best=x;bestScore=score}}
  if(best&&bestScore>=.66)return {lat:Number(best.u.lat),lng:Number(best.u.lng),address:best.u.formattedAddress||best.u.address||query,neighborhood:inspectionUnitNeighborhood(best.u),provider:'Base de vistoria local',localMatch:true};
  return null;
}
function makeAddressOverlayCropFromDrawable(drawable,variant=0,mode='original'){
  const specs=[{x:0,y:.61,w:.62,h:.39},{x:0,y:.70,w:.72,h:.30},{x:0,y:.48,w:.72,h:.52},{x:0,y:.78,w:.88,h:.22}];
  return cropDrawable(drawable,specs[Math.min(variant,specs.length-1)],1650,mode,2.05,150,3.1,1.7);
}
async function geocodeAddressCandidates(queries){
  // Para fotografias, a regra operacional é explícita: Rua + número → Google Maps,
  // com consulta direcionada a Apucarana/PR. A base local não substitui essa etapa.
  for(const q of queries.slice(0,4)){
    try{
      const hit=await googleGeocodeQuery(q);
      if(hit&&inApucaranaBounds(Number(hit.lat),Number(hit.lng))&&/Apucarana/i.test(hit.address||q)){
        return {...hit,query:q,provider:'Google Maps'};
      }
    }catch(e){return {error:e.message}}
  }
  return null;
}
async function readAddressOverlay(blob,{worker=null,drawable=null}={}){
  const ownDrawable=!drawable;if(!drawable)drawable=await loadImageDrawable(blob);worker=worker||await getOcrWorker(0);
  const fast=[[0,'original','6'],[0,'contrast','6']];const fallback=[[1,'contrast','11'],[3,'threshold','6']];
  let combined='',bestConfidence=0;const candidateQueries=[];
  const addQueries=txt=>{for(const q of extractAddressQueries(txt))if(!candidateQueries.includes(q))candidateQueries.push(q)};
  await worker.setParameters({tessedit_char_whitelist:'',preserve_interword_spaces:'1'});
  try{
    for(const phase of [fast,fallback]){
      for(const [variant,mode,psm] of phase){const canvas=makeAddressOverlayCropFromDrawable(drawable,variant,mode);await worker.setParameters({tessedit_pageseg_mode:psm,tessedit_char_whitelist:'',preserve_interword_spaces:'1'});const result=await worker.recognize(canvas);const txt=result?.data?.text||'';const conf=Number(result?.data?.confidence||0);if(conf>bestConfidence)bestConfidence=conf;combined+=(combined?'\n':'')+txt;addQueries(txt)}
      addQueries(combined);const hit=await geocodeAddressCandidates(candidateQueries);if(hit?.lat!=null)return {...hit,addressText:cleanAddressOcrText(combined),queries:candidateQueries.slice(0,8),confidence:bestConfidence,method:'address-overlay-left'};if(hit?.error)return {lat:null,lng:null,addressText:cleanAddressOcrText(combined),queries:candidateQueries.slice(0,8),confidence:bestConfidence,method:'address-overlay-left',error:hit.error};
    }
    return {lat:null,lng:null,addressText:cleanAddressOcrText(combined),queries:candidateQueries.slice(0,8),confidence:bestConfidence,method:'address-overlay-left',error:candidateQueries.length?'O endereço foi lido, mas não foi confirmado em Apucarana.':'Não foi possível ler com segurança o nome da rua e o número no canto inferior esquerdo.'};
  }finally{if(ownDrawable)closeImageDrawable(drawable)}
}
function makeMapInsetCropFromDrawable(drawable,variant=0){
  const sizes=variant===0?[.48,.42]:variant===1?[.62,.52]:[.76,.60];const spec={x:0,y:1-sizes[1],w:sizes[0],h:sizes[1]};return cropDrawable(drawable,spec,1500,variant===2?'threshold':'original',2,155,2.8,1.5);
}
async function readMapInset(blob,{worker=null,drawable=null}={}){
  const ownDrawable=!drawable;if(!drawable)drawable=await loadImageDrawable(blob);worker=worker||await getOcrWorker(0);let combined='';
  await worker.setParameters({tessedit_pageseg_mode:'11',tessedit_char_whitelist:'',preserve_interword_spaces:'1'});
  try{
    for(let variant=0;variant<2;variant++){
      const canvas=makeMapInsetCropFromDrawable(drawable,variant);const result=await worker.recognize(canvas);const txt=result?.data?.text||'';combined+=(combined?'\n':'')+txt;const coords=parseCoordinatesFromText(txt);if(coords&&inApucaranaBounds(coords.lat,coords.lng))return {...coords,mapText:combined.trim(),method:'coordinates'};
      // Se a primeira leitura já gerou rótulos geocodificáveis, evita uma segunda passada OCR.
      if(variant===0&&extractMapQueries(txt).length)return {lat:null,lng:null,mapText:combined.trim(),method:'labels'};
    }
    return {lat:null,lng:null,mapText:combined.trim(),method:'labels'};
  }finally{if(ownDrawable)closeImageDrawable(drawable)}
}
async function locateFromGoogleMapInset(blob,{worker=null,drawable=null}={}){
  const inset=await readMapInset(blob,{worker,drawable});if(validCoords(inset.lat,inset.lng))return {...inset,provider:'Google Maps inset'};const geo=await geocodeInsetText(inset.mapText);return {...inset,...geo};
}
function setOcrStatus(text,show=true){const el=$('ocrStatus');if(!el)return;el.hidden=!show;el.textContent=text||'Lendo coordenadas…'}

function setProcessProgress(kind,current,total,detail=''){
  const prefix=kind==='upload'?'upload':'location';
  const panel=$('photoProgressPanel'),row=$(prefix+'ProgressRow'),bar=$(prefix+'Progress'),fill=$(prefix+'ProgressFill'),textEl=$(prefix+'ProgressText'),insideEl=$(prefix+'ProgressInside'),detailEl=$(prefix+'ProgressDetail');
  if(!panel||!row||!bar||!fill||!textEl||!insideEl||!detailEl)return;
  const safeTotal=Math.max(1,Number(total)||1),safeCurrent=Math.min(safeTotal,Math.max(0,Number(current)||0));
  const pct=Math.max(0,Math.min(100,Math.round((safeCurrent/safeTotal)*100)));
  panel.hidden=false;row.hidden=false;
  row.classList.toggle('is-idle',pct===0);
  row.classList.toggle('is-complete',pct===100);
  fill.style.width=pct+'%';
  bar.setAttribute('aria-valuenow',String(pct));
  textEl.textContent=pct+'%';
  insideEl.textContent=pct+'%';
  detailEl.textContent=detail||`${safeCurrent} de ${safeTotal}`;
  // Garante que o navegador pinte a atualização antes da próxima etapa pesada.
  void fill.offsetWidth;
}
function resetProcessProgress(kind,detail=''){
  const prefix=kind==='upload'?'upload':'location';
  const row=$(prefix+'ProgressRow'),bar=$(prefix+'Progress'),fill=$(prefix+'ProgressFill'),textEl=$(prefix+'ProgressText'),insideEl=$(prefix+'ProgressInside'),detailEl=$(prefix+'ProgressDetail');
  if(!row||!bar||!fill||!textEl||!insideEl||!detailEl)return;
  row.hidden=false;row.classList.add('is-idle');row.classList.remove('is-complete');
  fill.style.width='0%';bar.setAttribute('aria-valuenow','0');textEl.textContent='0%';insideEl.textContent='0%';
  detailEl.textContent=detail||(kind==='upload'?'Aguardando envio de fotografias.':'Aguardando análise das coordenadas.');
}
function hideProcessProgress(kind,delay=0){
  // As barras permanecem sempre visíveis. Chamadas sem atraso apenas retornam a etapa ao estado de espera.
  // Chamadas com atraso preservam o resultado final (normalmente 100%) para conferência pelo usuário.
  if(!delay)resetProcessProgress(kind);
}
function clearPhotoProgress(delay=2200){
  // Mantém 100% e o resumo final visíveis após a conclusão.
}
function formatMb(bytes){return (Number(bytes||0)/1048576).toLocaleString('pt-BR',{minimumFractionDigits:1,maximumFractionDigits:1})+' MB'}


async function seedSettings(){
  const all=await getAll('settings'); const have=new Set(all.map(x=>x.key));
  for(const v of VEHICLES) if(!have.has('vehicle:'+v)) await put('settings',{key:'vehicle:'+v,destination:'Destino não definido'});
}

async function seedSurveyUnits(){
  const existing=await getAll('surveyUnits');
  if(existing.length)return;
  const seed=Array.isArray(window.APUC_INSPECTION_SEED)?window.APUC_INSPECTION_SEED:[];
  for(const x of seed)await put('surveyUnits',{...x,seedVersion:14,updatedAt:new Date().toISOString()});
}
async function getSurveyUnits(){return await getAll('surveyUnits')}
async function locateSurveyUnits(){
  const key=(await getSetting('googleMapsApiKey','')).trim();
  if(!key){toast('Configure a chave do Google Maps antes de localizar as unidades.');return}
  const units=await getSurveyUnits();
  const targets=units.filter(u=>(u.address||validCoords(u.lat,u.lng))&&(!validCoords(u.lat,u.lng)||!u.neighborhood));
  const bar=$('surveyGeocodeBar'),pct=$('surveyGeocodePct'),txt=$('surveyGeocodeText');
  const setProg=(done,total,msg)=>{const p=total?Math.round(done/total*100):100;if(bar)bar.style.width=p+'%';if(pct)pct.textContent=p+'%';if(txt)txt.textContent=msg||`${done}/${total}`};
  if(!targets.length){setProg(1,1,'Todas as unidades com dados suficientes já foram processadas.');toast('Nenhuma unidade pendente de localização.');return}
  setProg(0,targets.length,`Preparando ${targets.length} unidade(s)…`);let located=0,failed=0;
  for(let i=0;i<targets.length;i++){
    const u=targets[i];setProg(i,targets.length,`${i+1}/${targets.length} • ${u.vehicle} • Unidade ${String(u.unitNumber).padStart(2,'0')}`);
    try{
      let hit=null;
      if(validCoords(u.lat,u.lng))hit=await googleReverseGeocode(u.lat,u.lng);
      else if(u.address)hit=await googleGeocodeQuery(`${u.address}, Apucarana, PR, Brasil`);
      if(hit){u.lat=Number(hit.lat);u.lng=Number(hit.lng);u.formattedAddress=hit.address||u.formattedAddress||'';if(hit.neighborhood)u.neighborhood=hit.neighborhood;u.geocodeStatus='localizado';u.geocodedAt=new Date().toISOString();located++;}
      else{u.geocodeStatus='não localizado';failed++;}
    }catch(e){console.warn('Geocodificação da unidade',u.id,e);u.geocodeStatus='erro: '+e.message;failed++;}
    u.updatedAt=new Date().toISOString();await put('surveyUnits',u);setProg(i+1,targets.length,`${i+1}/${targets.length} • ${located} localizada(s) • ${failed} pendente(s)`);
    await new Promise(r=>setTimeout(r,55));
  }
  surveyAddressLookupCache=null;toast(`Unidades processadas: ${located} localizadas, ${failed} pendentes.`);await render();await renderReportNeighborhoodOptions();setTimeout(fitMap,120);
}
async function getVehicleSettings(){ const a=await getAll('settings'); return Object.fromEntries(a.filter(x=>x.key.startsWith('vehicle:')).map(x=>[x.key.slice(8),x])); }
async function getSetting(key, fallback=''){ const x=(await getAll('settings')).find(i=>i.key===key); return x?.value ?? fallback; }
async function setSetting(key,value){ await put('settings',{key,value}); }

function markCloudDirty(){
  if(cloudSyncSuspend>0)return;
  cloudDirty=true;
  updateDriveStatusUi();
  if(cloudAutoSync&&driveAccessToken){
    if(cloudSyncTimer)clearTimeout(cloudSyncTimer);
    cloudSyncTimer=setTimeout(()=>syncToGoogleDrive({silent:true}).catch(()=>{}),3500);
  }
}
function driveTokenValid(){return !!driveAccessToken && Date.now() < driveTokenExpiresAt-60000}
function updateDriveProgress(percent,text='',visible=true){
  const panel=$('driveSyncProgress'),bar=$('driveSyncBar'),pct=$('driveSyncPct'),inside=$('driveSyncInside'),detail=$('driveSyncText');
  if(panel)panel.hidden=!visible;
  const p=Math.max(0,Math.min(100,Math.round(Number(percent)||0)));
  if(bar)bar.style.width=p+'%';if(pct)pct.textContent=p+'%';if(inside)inside.textContent=p+'%';if(detail&&text)detail.textContent=text;
}
function updateDriveStatusUi(message=''){
  const status=$('googleDriveStatus'),side=$('cloudSidebarStatus');
  const connected=driveTokenValid();
  let label=message;
  if(!label){
    if(cloudSyncInFlight)label='Sincronizando com Google Drive…';
    else if(connected&&cloudDirty)label='Google Drive conectado • alterações aguardando sincronização';
    else if(connected)label='Google Drive conectado • dados sincronizados';
    else label='Google Drive não conectado • dados salvos localmente neste navegador';
  }
  if(status){status.innerHTML='<strong>Status:</strong> '+esc(label);status.classList.toggle('is-ok',connected&&!cloudDirty);status.classList.toggle('is-warn',!connected||cloudDirty)}
  if(side){side.textContent=connected?(cloudDirty?'Drive • pendente':'Drive • sincronizado'):'Armazenamento local';side.classList.toggle('cloud-online',connected&&!cloudDirty);side.classList.toggle('cloud-dirty',connected&&cloudDirty)}
}
async function waitForGoogleIdentity(timeout=12000){
  const start=Date.now();
  while(!window.google?.accounts?.oauth2){if(Date.now()-start>timeout)throw new Error('O módulo de login do Google não carregou. Verifique a conexão com a internet.');await new Promise(r=>setTimeout(r,120));}
  return window.google.accounts.oauth2;
}
async function initDriveFromSettings(){
  cloudAutoSync=String(await getSetting('googleDriveAutoSync','true'))!=='false';
  driveFolderId=await getSetting('googleDriveFolderId','');
  driveDataFileId=await getSetting('googleDriveFileId','');
  const auto=$('googleDriveAutoSync');if(auto)auto.checked=cloudAutoSync;
  updateDriveStatusUi();
}
async function getDriveClientId(){return String(await getSetting('googleDriveClientId','')).trim()}
async function requestGoogleDriveToken({prompt='consent'}={}){
  const clientId=($('googleDriveClientId')?.value||await getDriveClientId()).trim();
  if(!clientId)throw new Error('Informe o Google OAuth Client ID em Configurações.');
  const oauth2=await waitForGoogleIdentity();
  return await new Promise((resolve,reject)=>{
    driveTokenClient=oauth2.initTokenClient({
      client_id:clientId,
      scope:DRIVE_SCOPE,
      callback:(resp)=>{
        if(resp?.error)return reject(new Error(resp.error_description||resp.error));
        driveAccessToken=resp.access_token||'';
        driveTokenExpiresAt=Date.now()+(Number(resp.expires_in||3600)*1000);
        updateDriveStatusUi();resolve(driveAccessToken);
      },
      error_callback:(e)=>reject(new Error(e?.message||e?.type||'Falha no login do Google.'))
    });
    try{driveTokenClient.requestAccessToken({prompt});}catch(e){reject(e)}
  });
}
async function ensureDriveToken(interactive=true){
  if(driveTokenValid())return driveAccessToken;
  return await requestGoogleDriveToken({prompt:interactive?'consent':''});
}
async function driveRequest(url,options={},interactive=true){
  await ensureDriveToken(interactive);
  const headers=new Headers(options.headers||{});headers.set('Authorization','Bearer '+driveAccessToken);
  const res=await fetch(url,{...options,headers});
  if(res.status===401&&interactive){driveAccessToken='';driveTokenExpiresAt=0;await ensureDriveToken(true);headers.set('Authorization','Bearer '+driveAccessToken);const retry=await fetch(url,{...options,headers});if(!retry.ok)throw new Error(await driveErrorText(retry));return retry}
  if(!res.ok)throw new Error(await driveErrorText(res));return res;
}
async function driveErrorText(res){try{const j=await res.json();return j?.error?.message||`Google Drive: HTTP ${res.status}`}catch{return `Google Drive: HTTP ${res.status}`}}
async function saveInternalSetting(key,value){
  cloudSyncSuspend++;try{return await new Promise((res,rej)=>{const r=store('settings','readwrite').put({key,value});r.onsuccess=()=>res(value);r.onerror=()=>rej(r.error)})}finally{cloudSyncSuspend--}
}
async function ensureDriveFolder(){
  if(driveFolderId)return driveFolderId;
  const q=`name='${DRIVE_FOLDER_NAME.replaceAll("'","\\'")}' and mimeType='application/vnd.google-apps.folder' and trashed=false`;
  const url='https://www.googleapis.com/drive/v3/files?spaces=drive&pageSize=20&fields=files(id,name,webViewLink)&q='+encodeURIComponent(q);
  const found=await (await driveRequest(url)).json();
  if(found.files?.length){driveFolderId=found.files[0].id;await saveInternalSetting('googleDriveFolderId',driveFolderId);return driveFolderId}
  const created=await (await driveRequest('https://www.googleapis.com/drive/v3/files?fields=id,name,webViewLink',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({name:DRIVE_FOLDER_NAME,mimeType:'application/vnd.google-apps.folder'})})).json();
  driveFolderId=created.id;await saveInternalSetting('googleDriveFolderId',driveFolderId);return driveFolderId;
}
async function findDriveBackupFile(){
  const folder=await ensureDriveFolder();
  if(driveDataFileId){
    try{const r=await driveRequest(`https://www.googleapis.com/drive/v3/files/${encodeURIComponent(driveDataFileId)}?fields=id,name,modifiedTime,webViewLink`);return await r.json()}catch(e){console.warn('Arquivo Drive salvo não encontrado; pesquisando novamente.',e);driveDataFileId='';}
  }
  const q=`name='${DRIVE_BACKUP_NAME}' and '${folder}' in parents and trashed=false`;
  const result=await (await driveRequest('https://www.googleapis.com/drive/v3/files?spaces=drive&pageSize=20&fields=files(id,name,modifiedTime,webViewLink)&q='+encodeURIComponent(q))).json();
  const f=(result.files||[]).sort((a,b)=>String(b.modifiedTime||'').localeCompare(String(a.modifiedTime||'')))[0]||null;
  if(f){driveDataFileId=f.id;await saveInternalSetting('googleDriveFileId',f.id)}return f;
}
async function buildBackupObject(){
  const [routes,photos,incidents,settings,reports,surveyUnits]=await Promise.all([getAll('routes'),getAll('photos'),getAll('incidents'),getAll('settings'),getAll('reports'),getAll('surveyUnits')]);
  const p2=[];for(const p of photos)p2.push({...p,blobData:await blobToDataURL(p.blob),blob:undefined});
  const i2=[];for(const i of incidents)i2.push({...i,blobData:await blobToDataURL(i.blob),blob:undefined});
  return {version:5,cloudSchema:'apuc-rotas-drive-v1',exportedAt:new Date().toISOString(),routes,photos:p2,incidents:i2,settings,reports,surveyUnits};
}
async function restoreBackupObject(data,{confirmReplace=true}={}){
  if(!data||!Array.isArray(data.routes))throw new Error('Formato de backup inválido.');
  if(confirmReplace&&!confirm('Restaurar o backup e substituir os dados locais atuais?'))return false;
  cloudSyncSuspend++;
  try{
    for(const s of ['routes','photos','incidents','settings','reports','surveyUnits'])await clearStore(s);
    for(const x of data.routes||[])await put('routes',x);
    for(const raw of data.photos||[]){const x={...raw};x.blob=dataURLToBlob(x.blobData);delete x.blobData;await put('photos',x)}
    for(const raw of data.incidents||[]){const x={...raw};x.blob=dataURLToBlob(x.blobData);delete x.blobData;await put('incidents',x)}
    for(const x of data.settings||[])await put('settings',x);
    for(const x of data.reports||[])await put('reports',x);
    for(const x of data.surveyUnits||[])await put('surveyUnits',x);
  }finally{cloudSyncSuspend--}
  surveyAddressLookupCache=null;geocodeCache.clear();await seedSettings();await seedSurveyUnits();selectedRouteId='';await initDriveFromSettings();await render();setTimeout(fitMap,120);return true;
}
async function createResumableDriveSession(blob,metadata,fileId=''){
  const base=fileId?`https://www.googleapis.com/upload/drive/v3/files/${encodeURIComponent(fileId)}?uploadType=resumable&fields=id,name,modifiedTime,webViewLink`:'https://www.googleapis.com/upload/drive/v3/files?uploadType=resumable&fields=id,name,modifiedTime,webViewLink';
  const method=fileId?'PATCH':'POST';
  const res=await driveRequest(base,{method,headers:{'Content-Type':'application/json; charset=UTF-8','X-Upload-Content-Type':'application/json','X-Upload-Content-Length':String(blob.size)},body:JSON.stringify(metadata)});
  const location=res.headers.get('Location');if(!location)throw new Error('O Google Drive não retornou uma sessão de upload.');return location;
}
async function uploadBlobWithProgress(sessionUrl,blob){
  await ensureDriveToken(true);
  return await new Promise((resolve,reject)=>{
    const xhr=new XMLHttpRequest();xhr.open('PUT',sessionUrl,true);xhr.setRequestHeader('Authorization','Bearer '+driveAccessToken);xhr.setRequestHeader('Content-Type','application/json');
    xhr.upload.onprogress=e=>{if(e.lengthComputable){const p=10+Math.round((e.loaded/e.total)*85);updateDriveProgress(p,`Enviando ${(e.loaded/1048576).toLocaleString('pt-BR',{maximumFractionDigits:1})} de ${(e.total/1048576).toLocaleString('pt-BR',{maximumFractionDigits:1})} MB…`)}};
    xhr.onload=()=>{if(xhr.status>=200&&xhr.status<300){try{resolve(JSON.parse(xhr.responseText||'{}'))}catch{resolve({})}}else reject(new Error(`Google Drive: HTTP ${xhr.status} ${xhr.responseText||''}`))};xhr.onerror=()=>reject(new Error('Falha de rede durante o upload para o Google Drive.'));xhr.send(blob);
  });
}
async function syncToGoogleDrive({silent=false}={}){
  if(cloudSyncInFlight)return false;
  cloudSyncInFlight=true;updateDriveStatusUi();updateDriveProgress(2,'Preparando os dados para salvamento…',true);
  try{
    const clientId=($('googleDriveClientId')?.value||await getDriveClientId()).trim();if(!clientId)throw new Error('Configure o Google OAuth Client ID antes de sincronizar.');
    await ensureDriveToken(!silent);
    updateDriveProgress(5,'Montando backup completo…');
    const data=await buildBackupObject();const blob=new Blob([JSON.stringify(data)],{type:'application/json'});
    const folder=await ensureDriveFolder();const existing=await findDriveBackupFile();
    updateDriveProgress(8,`Preparando upload de ${(blob.size/1048576).toLocaleString('pt-BR',{maximumFractionDigits:1})} MB…`);
    const metadata=existing?{name:DRIVE_BACKUP_NAME,mimeType:'application/json'}:{name:DRIVE_BACKUP_NAME,mimeType:'application/json',parents:[folder],appProperties:{app:'APUC Rotas',kind:'backup'}};
    const session=await createResumableDriveSession(blob,metadata,existing?.id||'');const result=await uploadBlobWithProgress(session,blob);
    if(result.id){driveDataFileId=result.id;await saveInternalSetting('googleDriveFileId',result.id)}
    await saveInternalSetting('googleDriveLastSync',new Date().toISOString());cloudDirty=false;updateDriveProgress(100,'Dados salvos no Google Drive.');updateDriveStatusUi('Google Drive conectado • última sincronização concluída agora');if(!silent)toast('Dados salvos no Google Drive.');return true;
  }catch(e){console.error('Google Drive sync',e);updateDriveProgress(0,'Falha: '+e.message,true);updateDriveStatusUi('Falha na sincronização • '+e.message);if(!silent)alert('Não foi possível salvar no Google Drive: '+e.message);return false}
  finally{cloudSyncInFlight=false;updateDriveStatusUi()}
}
async function restoreFromGoogleDrive(){
  try{
    updateDriveProgress(3,'Conectando ao Google Drive…',true);await ensureDriveToken(true);const f=await findDriveBackupFile();if(!f)throw new Error('Nenhum backup do APUC Rotas foi encontrado no Google Drive.');
    updateDriveProgress(20,'Baixando o backup do Google Drive…');const res=await driveRequest(`https://www.googleapis.com/drive/v3/files/${encodeURIComponent(f.id)}?alt=media`);const text=await res.text();updateDriveProgress(65,'Validando e restaurando os dados…');const data=JSON.parse(text);const ok=await restoreBackupObject(data,{confirmReplace:true});if(!ok){updateDriveProgress(0,'Restauração cancelada.');return}
    driveDataFileId=f.id;await saveInternalSetting('googleDriveFileId',f.id);cloudDirty=false;updateDriveProgress(100,'Backup restaurado com sucesso.');updateDriveStatusUi('Google Drive conectado • backup restaurado');toast('Backup restaurado do Google Drive.');
  }catch(e){console.error(e);updateDriveProgress(0,'Falha: '+e.message,true);alert('Não foi possível restaurar do Google Drive: '+e.message)}
}
async function connectGoogleDrive(){
  try{
    const clientId=$('googleDriveClientId')?.value.trim();if(!clientId)throw new Error('Informe primeiro o Google OAuth Client ID.');await saveInternalSetting('googleDriveClientId',clientId);await requestGoogleDriveToken({prompt:'consent'});await ensureDriveFolder();await findDriveBackupFile();updateDriveStatusUi();toast('Google Drive conectado.');
  }catch(e){console.error(e);updateDriveStatusUi('Não conectado • '+e.message);alert('Não foi possível conectar ao Google Drive: '+e.message)}
}
function disconnectGoogleDrive(){
  if(driveAccessToken&&window.google?.accounts?.oauth2?.revoke)try{google.accounts.oauth2.revoke(driveAccessToken,()=>{})}catch{}
  driveAccessToken='';driveTokenExpiresAt=0;driveTokenClient=null;updateDriveStatusUi();toast('Google Drive desconectado desta sessão.');
}
function inApucaranaBounds(lat,lng){return Number.isFinite(lat)&&Number.isFinite(lng)&&lat>=APUCARANA_BOUNDS.south&&lat<=APUCARANA_BOUNDS.north&&lng>=APUCARANA_BOUNDS.west&&lng<=APUCARANA_BOUNDS.east}

async function loadGoogleMapsApi(){
  if(window.google?.maps?.Geocoder)return window.google.maps;
  const key=(await getSetting('googleMapsApiKey','')).trim();
  if(!key)throw new Error('Configure a chave da API do Google Maps em Configurações.');
  if(!googleMapsLoadPromise) googleMapsLoadPromise=new Promise((resolve,reject)=>{
    const cb='__apucGoogleMapsReady_'+Date.now();
    window[cb]=()=>{delete window[cb];resolve(window.google.maps)};
    const script=document.createElement('script');
    script.src=`https://maps.googleapis.com/maps/api/js?key=${encodeURIComponent(key)}&callback=${cb}&loading=async`;
    script.async=true;script.defer=true;
    script.onerror=()=>{googleMapsLoadPromise=null;delete window[cb];reject(new Error('Não foi possível carregar a API do Google Maps. Verifique a chave e a conexão.'));};
    document.head.appendChild(script);
  });
  return googleMapsLoadPromise;
}
function normalizeMapText(raw){
  return String(raw||'').replace(/\r/g,'\n').split(/\n+/).map(x=>x.replace(/[^\p{L}\p{N}\s.\-–—'/+°]/gu,' ').replace(/\s+/g,' ').trim()).filter(Boolean);
}
function extractMapQueries(raw){
  const lines=normalizeMapText(raw).filter(line=>{
    const low=line.toLowerCase();
    if(line.length<3)return false;
    if(/google|maps|street view|imagery|copyright|202\d|\bkm\b|\bm\b/.test(low)&&line.length<24)return false;
    if(/^\d+[.,]?\d*$/.test(line))return false;
    return true;
  });
  const plus=String(raw||'').match(/[23456789CFGHJMPQRVWX]{4,8}\+[23456789CFGHJMPQRVWX]{2,3}/i)?.[0];
  const unique=[];
  if(plus)unique.push(`${plus} Apucarana PR Brasil`);
  const likely=lines.filter(x=>/[A-Za-zÀ-ÿ]/.test(x)).sort((a,b)=>b.length-a.length);
  if(likely.length) unique.push(`${likely.slice(0,3).join(', ')}, Apucarana, PR, Brasil`);
  for(const line of likely.slice(0,6)) unique.push(`${line}, Apucarana, PR, Brasil`);
  return [...new Set(unique)].slice(0,7);
}
async function googleGeocodeQuery(query){
  const cacheKey=normalizeAddressMatch(query);
  if(geocodeCache.has(cacheKey))return await geocodeCache.get(cacheKey);
  const promise=(async()=>{
  await loadGoogleMapsApi();
  const geocoder=new google.maps.Geocoder();
  const bounds=new google.maps.LatLngBounds(
    {lat:APUCARANA_BOUNDS.south,lng:APUCARANA_BOUNDS.west},
    {lat:APUCARANA_BOUNDS.north,lng:APUCARANA_BOUNDS.east}
  );
  return await new Promise((resolve)=>{
    geocoder.geocode({address:query,bounds,region:'BR',componentRestrictions:{country:'BR',locality:'Apucarana',administrativeArea:'PR'}},(results,status)=>{
      if(status!=='OK'||!results?.length)return resolve(null);
      const candidates=results.map(r=>{
        const loc=r.geometry?.location; const lat=loc?.lat?.(),lng=loc?.lng?.();
        const comps=r.address_components||[];const pick=(types)=>{for(const t of types){const c=comps.find(x=>(x.types||[]).includes(t));if(c?.long_name)return c.long_name}return ''};const neighborhood=pick(['neighborhood','sublocality_level_1','sublocality','administrative_area_level_4','administrative_area_level_3']);return {lat,lng,address:r.formatted_address||query,types:r.types||[],neighborhood,addressComponents:comps};
      }).filter(x=>validCoords(x.lat,x.lng));
      resolve(candidates.find(x=>inApucaranaBounds(x.lat,x.lng))||candidates.find(x=>/Apucarana/i.test(x.address))||null);
    });
  });
  })();
  geocodeCache.set(cacheKey,promise);
  try{return await promise}catch(e){geocodeCache.delete(cacheKey);throw e}
}

async function googleReverseGeocode(lat,lng){
  await loadGoogleMapsApi();
  const geocoder=new google.maps.Geocoder();
  return await new Promise((resolve)=>{
    geocoder.geocode({location:{lat:Number(lat),lng:Number(lng)}},(results,status)=>{
      if(status!=='OK'||!results?.length)return resolve(null);
      const r=results.find(x=>/Apucarana/i.test(x.formatted_address||''))||results[0];
      const loc=r.geometry?.location;const rlat=loc?.lat?.(),rlng=loc?.lng?.();
      const comps=r.address_components||[];const pick=(types)=>{for(const t of types){const c=comps.find(x=>(x.types||[]).includes(t));if(c?.long_name)return c.long_name}return ''};
      resolve({lat:rlat,lng:rlng,address:r.formatted_address||'',neighborhood:pick(['neighborhood','sublocality_level_1','sublocality','administrative_area_level_4','administrative_area_level_3']),types:r.types||[],addressComponents:comps});
    });
  });
}

async function geocodeInsetText(raw){
  const queries=extractMapQueries(raw);
  if(!queries.length)return {lat:null,lng:null,queries:[],error:'Nenhum nome de via ou local legível no mini mapa.'};
  let lastErr='';
  for(const q of queries){
    try{
      const hit=await googleGeocodeQuery(q);
      if(hit)return {...hit,query:q,queries,provider:'Google Maps'};
    }catch(e){lastErr=e.message;break}
  }
  return {lat:null,lng:null,queries,error:lastErr||'O Google Maps não encontrou uma localização compatível em Apucarana.'};
}


function initMap(){
  map=L.map('map',{zoomControl:true,preferCanvas:false}).setView(APUCARANA_CENTER,13);
  streetLayer=L.tileLayer('https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png',{maxZoom:20,attribution:'&copy; OpenStreetMap contributors'});
  satelliteLayer=L.tileLayer('https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}',{maxZoom:20,attribution:'Tiles &copy; Esri'});
  streetLayer.addTo(map);
  markersLayer=L.layerGroup().addTo(map);
  routeLineLayer=L.layerGroup().addTo(map);
}
function setBaseMap(mode){
  currentBaseMap=mode;
  if(mode==='satellite'){
    if(map.hasLayer(streetLayer)) map.removeLayer(streetLayer);
    if(!map.hasLayer(satelliteLayer)) satelliteLayer.addTo(map);
  }else{
    if(map.hasLayer(satelliteLayer)) map.removeLayer(satelliteLayer);
    if(!map.hasLayer(streetLayer)) streetLayer.addTo(map);
  }
  $('btnStreet').classList.toggle('active',mode==='street');
  $('btnSatellite').classList.toggle('active',mode==='satellite');
}

async function syncSelectedRoute(){
  const routes=(await getAll('routes')).filter(r=>r.vehicle===selectedVehicle).sort(routeSorter);
  if(!routes.some(r=>r.id===selectedRouteId)) selectedRouteId=routes[0]?.id||'';
  $('routeViewSelect').innerHTML=routes.length?routes.map(r=>`<option value="${r.id}" ${r.id===selectedRouteId?'selected':''}>${esc(r.date)} — ${esc(r.destination)}</option>`).join(''):'<option value="">Nenhuma rota cadastrada</option>';
  $('routeViewSelect').disabled=!routes.length;
  $('btnEditSelectedRoute').disabled=!selectedRouteId;
}

async function render(){
  await renderVehicles();
  await renderStats();
  await syncSelectedRoute();
  await updateHero();
  await renderRoutes();
  await renderPhotoGallery();
  await renderActivity();
  await renderReportsSummary();
  await renderMap();
  await fillIncidentRoutes();
}

async function renderVehicles(){
  const settings=await getVehicleSettings();
  $('vehicleList').innerHTML=VEHICLES.map(v=>`<button class="vehicle-btn ${v===selectedVehicle?'active':''}" data-v="${v}"><span><strong>${v}</strong><small>${esc(settings[v]?.destination||'Destino não definido')}</small></span><span>›</span></button>`).join('');
  document.querySelectorAll('.vehicle-btn').forEach(b=>b.onclick=async()=>{selectedVehicle=b.dataset.v;selectedRouteId='';await render();setTimeout(fitMap,80)});
}
async function updateHero(){
  const routes=await getAll('routes'); const route=routes.find(r=>r.id===selectedRouteId);
  $('selectedVehicleTitle').textContent=selectedVehicle;
  $('selectedVehicleMeta').textContent=route?`${fmtDate(route.date)} • ${route.destination}${route.driver?' • '+route.driver:''}`:'Nenhuma rota selecionada';
}
async function renderStats(){
  const [routes,photos,incidents]=await Promise.all([getAll('routes'),getAll('photos'),getAll('incidents')]);
  $('statRoutes').textContent=routes.length; $('statPhotos').textContent=photos.length; $('statIncidents').textContent=incidents.length; $('statGps').textContent=photos.filter(p=>Number.isFinite(p.lat)&&Number.isFinite(p.lng)).length;
}
async function renderRoutes(){
  const [routes,photos,incidents]=await Promise.all([getAll('routes'),getAll('photos'),getAll('incidents')]);
  const filtered=routes.filter(r=>r.vehicle===selectedVehicle).sort(routeSorter);
  if(!filtered.length){$('routesTable').innerHTML='<tr><td colspan="7"><div class="empty">Nenhuma rota cadastrada para este veículo.</div></td></tr>';return}
  $('routesTable').innerHTML=filtered.map(r=>{
    const pc=photos.filter(p=>p.routeId===r.id).length, ic=incidents.filter(i=>i.routeId===r.id).length;
    return `<tr class="${r.id===selectedRouteId?'selected':''}" data-select-route="${r.id}"><td>${fmtDate(r.date)}</td><td><strong>${esc(r.destination)}</strong>${r.neighborhood?`<small class="route-neighborhood">${esc(r.neighborhood)}</small>`:''}</td><td>${esc(r.driver||'—')}</td><td>${pc}</td><td>${ic}</td><td><span class="status">REGISTRADA</span></td><td><div class="row-actions"><button class="icon-action" data-edit-route="${r.id}" title="Editar rota">✎</button><button class="icon-action" data-del-route="${r.id}" title="Excluir rota">×</button></div></td></tr>`;
  }).join('');
  document.querySelectorAll('[data-select-route]').forEach(row=>row.onclick=async e=>{if(e.target.closest('button'))return;selectedRouteId=row.dataset.selectRoute;await render();setTimeout(fitMap,80)});
  document.querySelectorAll('[data-edit-route]').forEach(b=>b.onclick=e=>{e.stopPropagation();editRoute(b.dataset.editRoute)});
  document.querySelectorAll('[data-del-route]').forEach(b=>b.onclick=e=>{e.stopPropagation();deleteRoute(b.dataset.delRoute)});
}

async function renderPhotoGallery(){
  revokeUrls(galleryObjectUrls);
  const photos=(await getAll('photos')).filter(p=>p.vehicle===selectedVehicle && (!selectedRouteId || p.routeId===selectedRouteId)).sort((a,b)=>String(a.takenAt||a.createdAt).localeCompare(String(b.takenAt||b.createdAt)));
  $('photoCount').textContent=photos.length;
  const deleteAllBtn=$('btnDeleteAllPhotos');
  if(deleteAllBtn){
    deleteAllBtn.disabled=!selectedRouteId || photos.length===0;
    deleteAllBtn.title=!selectedRouteId?'Selecione uma rota para apagar suas fotos.':photos.length===0?'Esta rota não possui fotografias.':`Apagar as ${photos.length} foto(s) desta rota`;
  }
  if(!photos.length){$('photoGallery').innerHTML='<div class="empty">Nenhuma imagem vinculada a esta rota.<br>Use “Enviar fotos” para adicionar registros de campo.</div>';return}
  $('photoGallery').innerHTML=photos.map(p=>{
    const url=p.blob?URL.createObjectURL(p.blob):''; if(url)galleryObjectUrls.push(url);
    const hasGps=Number.isFinite(p.lat)&&Number.isFinite(p.lng);
    return `<article class="photo-card" data-photo-card="${p.id}">
      ${url?`<img class="photo-thumb" data-open-photo="${p.id}" src="${url}" alt="${esc(p.fileName||'Foto')}">`:'<div class="photo-thumb"></div>'}
      <div class="photo-card-body"><div class="photo-card-title">${esc(p.fileName||'Fotografia')}</div><div class="photo-card-meta">${fmtDate(p.takenAt||p.createdAt)}</div><div class="${hasGps?'photo-gps':'photo-no-gps'}">${hasGps?'● LOCALIZADA '+p.lat.toFixed(5)+', '+p.lng.toFixed(5):'○ SEM LOCALIZAÇÃO'}</div>${hasGps?`<span class="coord-source">${esc(coordSourceLabel(p))}</span>`:''}${p.mapInsetAddress?`<div class="photo-card-address">${esc(p.mapInsetAddress)}</div>`:''}<div class="photo-actions">${hasGps?`<button class="mini-link" data-locate-photo="${p.id}">VER NO MAPA</button>`:''}<button class="mini-link" data-read-inset="${p.id}">LOCALIZAR</button><button class="mini-link" data-edit-photo="${p.id}">EDITAR</button><button class="mini-link" data-open-photo="${p.id}">AMPLIAR</button><button class="mini-link danger-link" data-delete-photo="${p.id}">EXCLUIR</button></div></div>
    </article>`;
  }).join('');
  document.querySelectorAll('[data-open-photo]').forEach(el=>el.onclick=e=>{e.stopPropagation();openPhoto(el.dataset.openPhoto)});
  document.querySelectorAll('[data-locate-photo]').forEach(el=>el.onclick=async e=>{e.stopPropagation();const p=(await getAll('photos')).find(x=>x.id===el.dataset.locatePhoto);if(p&&Number.isFinite(p.lat)&&Number.isFinite(p.lng)){map.flyTo([p.lat,p.lng],18,{duration:.6});}});
  document.querySelectorAll('[data-read-inset]').forEach(el=>el.onclick=e=>{e.stopPropagation();locateOnePhotoFromInset(el.dataset.readInset)});
  document.querySelectorAll('[data-edit-photo]').forEach(el=>el.onclick=e=>{e.stopPropagation();openPhotoEdit(el.dataset.editPhoto)});
  document.querySelectorAll('[data-delete-photo]').forEach(el=>el.onclick=e=>{e.stopPropagation();deletePhoto(el.dataset.deletePhoto)});
}
async function deletePhoto(id){ if(!confirm('Excluir esta fotografia?'))return;await del('photos',id);toast('Fotografia excluída.');await render(); }

async function openPhotoEdit(id){
  const p=(await getAll('photos')).find(x=>x.id===id);if(!p)return;
  $('photoEditId').value=p.id;$('photoEditName').value=p.fileName||'fotografia.jpg';$('photoEditAddress').value=p.mapInsetAddress||'';$('photoEditLat').value=Number.isFinite(p.lat)?p.lat:'';$('photoEditLng').value=Number.isFinite(p.lng)?p.lng:'';$('photoEditGeocodeStatus').textContent='';$('photoEditDialog').showModal();
}
async function geocodePhotoEditAddress(){
  const q=$('photoEditAddress').value.trim();if(!q){toast('Digite Rua e número.');return}
  $('photoEditGeocodeStatus').textContent='Localizando…';
  try{const hit=await googleGeocodeQuery(/Apucarana/i.test(q)?q:`${q}, Apucarana, PR, Brasil`);if(!hit)throw new Error('Endereço não localizado em Apucarana.');$('photoEditLat').value=Number(hit.lat).toFixed(7);$('photoEditLng').value=Number(hit.lng).toFixed(7);$('photoEditAddress').value=hit.address||q;$('photoEditGeocodeStatus').textContent='Endereço localizado.';}catch(e){$('photoEditGeocodeStatus').textContent='Falha: '+e.message}
}
async function savePhotoEdit(ev){
  ev.preventDefault();const id=$('photoEditId').value;const p=(await getAll('photos')).find(x=>x.id===id);if(!p)return;
  const lat=parseCoord($('photoEditLat').value),lng=parseCoord($('photoEditLng').value);p.fileName=$('photoEditName').value.trim()||p.fileName;p.mapInsetAddress=$('photoEditAddress').value.trim()||p.mapInsetAddress||'';
  if(validCoords(lat,lng)){p.lat=lat;p.lng=lng;p.coordSource='manual-address';p.coordConfidence=100;p.manualLocation=true;p.locatedAt=new Date().toISOString();}
  p.updatedAt=new Date().toISOString();await put('photos',p);$('photoEditDialog').close();toast('Fotografia atualizada.');await render();setTimeout(fitMap,100);
}
async function startPhotoPinDrag(){
  const id=$('photoEditId').value;const p=(await getAll('photos')).find(x=>x.id===id);if(!p)return;
  $('photoEditDialog').close();if(manualPhotoDragMarker){try{map.removeLayer(manualPhotoDragMarker)}catch{}}
  manualPhotoDragId=id;const start=validCoords(Number(p.lat),Number(p.lng))?[Number(p.lat),Number(p.lng)]:map.getCenter();
  manualPhotoDragMarker=L.marker(start,{draggable:true,zIndexOffset:2000}).addTo(map).bindTooltip('Arraste até a posição correta e solte.',{permanent:true,direction:'top'}).openTooltip();map.flyTo(start,Math.max(map.getZoom(),17),{duration:.5});
  manualPhotoDragMarker.on('dragend',async e=>{const ll=e.target.getLatLng();const current=(await getAll('photos')).find(x=>x.id===manualPhotoDragId);if(current){current.lat=ll.lat;current.lng=ll.lng;current.coordSource='manual-pin';current.coordConfidence=100;current.manualLocation=true;current.updatedAt=new Date().toISOString();try{const rev=await googleReverseGeocode(ll.lat,ll.lng);if(rev?.address)current.mapInsetAddress=rev.address}catch{}await put('photos',current)}try{map.removeLayer(manualPhotoDragMarker)}catch{}manualPhotoDragMarker=null;manualPhotoDragId='';toast('Posição manual salva.');await render();map.flyTo([ll.lat,ll.lng],18,{duration:.4})});
}

async function deleteAllPhotosFromSelectedRoute(){
  if(!selectedRouteId){toast('Selecione uma rota antes de apagar as fotografias.');return}
  const [routes,allPhotos]=await Promise.all([getAll('routes'),getAll('photos')]);
  const route=routes.find(r=>r.id===selectedRouteId);
  const photos=allPhotos.filter(p=>p.routeId===selectedRouteId);
  if(!photos.length){toast('Esta rota não possui fotografias para apagar.');return}
  const routeLabel=route?`${route.vehicle} • ${fmtDate(route.date)} • ${route.destination}`:selectedRouteId;
  const ok=confirm(`ATENÇÃO: apagar todas as ${photos.length} fotografia(s) da rota:\n\n${routeLabel}\n\nEsta ação não pode ser desfeita. Os sinistros e os dados da rota serão mantidos.`);
  if(!ok)return;
  if($('photoDialog')?.open)$('photoDialog').close();
  if(photoModalUrl){URL.revokeObjectURL(photoModalUrl);photoModalUrl=null}
  for(const p of photos)await del('photos',p.id);
  toast(`${photos.length} fotografia(s) apagada(s) desta rota.`);
  await render();
  setTimeout(fitMap,80);
}

async function renderActivity(){
  const [photos,incidents]=await Promise.all([getAll('photos'),getAll('incidents')]);
  let items=[
    ...photos.map(p=>({kind:'photo',date:p.takenAt||p.createdAt,vehicle:p.vehicle,routeId:p.routeId,title:'Foto georreferenciada',text:(p.fileName||'Imagem')+(Number.isFinite(p.lat)?` • ${p.lat.toFixed(5)}, ${p.lng.toFixed(5)}`:' • sem GPS'),id:p.id})),
    ...incidents.map(i=>({kind:'incident',date:i.date,vehicle:i.vehicle,routeId:i.routeId,title:i.code+' • '+i.type,text:i.address||i.description||'Sinistro registrado',id:i.id}))
  ].filter(x=>showAllActivity||(x.vehicle===selectedVehicle&&(!selectedRouteId||x.routeId===selectedRouteId))).sort((a,b)=>String(b.date).localeCompare(String(a.date))).slice(0,30);
  if(!items.length){$('activityList').innerHTML='<div class="empty">Sem atividades para exibir.</div>';return}
  $('activityList').innerHTML=items.map(x=>`<div class="activity-item" data-kind="${x.kind}" data-id="${x.id}"><div class="activity-icon ${x.kind==='incident'?'incident':''}">${x.kind==='incident'?'!':'▧'}</div><div><strong>${esc(x.title)}</strong><p>${esc(x.vehicle)} • ${fmtDate(x.date)}</p><p>${esc(x.text)}</p></div></div>`).join('');
  document.querySelectorAll('.activity-item[data-kind="photo"]').forEach(el=>el.onclick=()=>openPhoto(el.dataset.id));
  document.querySelectorAll('.activity-item[data-kind="incident"]').forEach(el=>el.onclick=()=>editIncident(el.dataset.id));
}

async function renderMap(){
  revokeUrls(mapObjectUrls); markersLayer.clearLayers(); routeLineLayer.clearLayers();
  const [photos,incidents,routes,surveyUnits]=await Promise.all([getAll('photos'),getAll('incidents'),getAll('routes'),getAll('surveyUnits')]);
  const ps=photos.filter(p=>p.vehicle===selectedVehicle&&(!selectedRouteId||p.routeId===selectedRouteId)&&Number.isFinite(p.lat)&&Number.isFinite(p.lng)).sort((a,b)=>String(a.takenAt||a.createdAt).localeCompare(String(b.takenAt||b.createdAt)));
  const is=incidents.filter(i=>i.vehicle===selectedVehicle&&(!selectedRouteId||i.routeId===selectedRouteId)&&Number.isFinite(i.lat)&&Number.isFinite(i.lng));
  const rs=routes.filter(r=>r.vehicle===selectedVehicle&&(!selectedRouteId||r.id===selectedRouteId)&&Number.isFinite(r.lat)&&Number.isFinite(r.lng));
  const us=surveyUnits.filter(u=>u.vehicle===selectedVehicle&&inspectionIsAffected(u)&&validCoords(Number(u.lat),Number(u.lng)));

  for(const p of ps){
    const url=p.blob?URL.createObjectURL(p.blob):''; if(url)mapObjectUrls.push(url);
    const icon=L.divIcon({className:'photo-marker-wrap',html:`<div class="photo-map-marker">${url?`<img src="${url}" alt="">`:''}</div>`,iconSize:[48,48],iconAnchor:[24,24]});
    const popup=`<strong>${esc(p.fileName||'Fotografia')}</strong>${url?`<img class="popup-photo" src="${url}" alt="">`:''}<div class="popup-caption">${fmtDate(p.takenAt||p.createdAt)}<br>${p.lat.toFixed(6)}, ${p.lng.toFixed(6)}<br>${esc(coordSourceLabel(p))}</div>`;
    const m=L.marker([p.lat,p.lng],{icon,zIndexOffset:200}).bindPopup(popup).addTo(markersLayer);
    m.on('dblclick',()=>openPhoto(p.id));
  }
  for(const i of is){
    const icon=L.divIcon({className:'incident-map-icon',html:'!',iconSize:[28,28],iconAnchor:[14,14]});
    const photoUrl=i.blob?URL.createObjectURL(i.blob):''; if(photoUrl)mapObjectUrls.push(photoUrl);
    L.marker([i.lat,i.lng],{icon,zIndexOffset:500}).bindPopup(`<strong>${esc(i.code)} • ${esc(i.type)}</strong>${photoUrl?`<img class="popup-photo" src="${photoUrl}" alt="">`:''}<div class="popup-caption">${esc(i.address)}<br>${fmtDate(i.date)}<br>${i.lat.toFixed(6)}, ${i.lng.toFixed(6)}</div>`).addTo(markersLayer);
  }
  for(const r of rs){
    const icon=L.divIcon({className:'destination-map-icon',html:'D',iconSize:[26,26],iconAnchor:[13,13]});
    L.marker([r.lat,r.lng],{icon}).bindPopup(`<strong>Destino da rota</strong><br>${esc(r.destination)}<br><span class="popup-caption">${fmtDate(r.date)}</span>`).addTo(routeLineLayer);
  }
  for(const u of us){
    const icon=L.divIcon({className:'survey-unit-icon',html:`<div class="survey-unit-marker">${String(u.unitNumber||'').padStart(2,'0')}</div>`,iconSize:[30,30],iconAnchor:[15,15]});
    const div=(u.divergences||[]).length?`<div class="source-note"><strong>Atenção:</strong> ${(u.divergences||[]).length} divergência(s) entre resumo e ficha detalhada.</div>`:'';
    const popup=`<div class="survey-popup"><strong>${esc(u.vehicle)} • Unidade ${esc(String(u.unitNumber).padStart(2,'0'))}</strong><div>${esc(u.formattedAddress||u.address||'Endereço não informado')}</div><div class="popup-caption">${esc(inspectionUnitNeighborhood(u))}<br>${Number(u.lat).toFixed(6)}, ${Number(u.lng).toFixed(6)}</div><div class="req">${esc(inspectionRequirementText(u))}</div>${div}</div>`;
    L.marker([Number(u.lat),Number(u.lng)],{icon,zIndexOffset:120}).bindPopup(popup).addTo(markersLayer);
  }
  if(ps.length>1)L.polyline(ps.map(p=>[p.lat,p.lng]),{weight:3,color:'#ed1c24',dashArray:'7 7',opacity:.8}).addTo(routeLineLayer);
}
async function fitMap(){
  const layers=[]; markersLayer.eachLayer(l=>layers.push(l)); routeLineLayer.eachLayer(l=>{if(l.getBounds||l.getLatLng)layers.push(l)});
  if(!layers.length){map.setView(APUCARANA_CENTER,13);return}
  try{map.fitBounds(L.featureGroup(layers).getBounds().pad(.18),{maxZoom:18})}catch{map.setView(APUCARANA_CENTER,13)}
}

function fillVehicleSelects(){ const opts=VEHICLES.map(v=>`<option>${v}</option>`).join(''); $('routeVehicle').innerHTML=opts; $('incidentVehicle').innerHTML=opts; }
async function fillIncidentRoutes(){
  const vehicle=$('incidentVehicle').value||selectedVehicle;
  const routes=(await getAll('routes')).filter(r=>r.vehicle===vehicle).sort(routeSorter);
  const cur=$('incidentRoute').value;
  $('incidentRoute').innerHTML='<option value="">Sem rota vinculada</option>'+routes.map(r=>`<option value="${r.id}">${esc(r.date)} — ${esc(r.destination)}</option>`).join('');
  if([...$('incidentRoute').options].some(o=>o.value===cur)) $('incidentRoute').value=cur;
  else if(vehicle===selectedVehicle && selectedRouteId) $('incidentRoute').value=selectedRouteId;
}

function openNewRoute(){
  $('routeForm').reset(); $('routeId').value=''; $('routeDialogTitle').textContent='Nova rota'; $('routeVehicle').value=selectedVehicle; $('routeDate').value=new Date().toISOString().slice(0,10); $('routeDialog').showModal();
}
async function editRoute(id){
  const r=(await getAll('routes')).find(x=>x.id===id);if(!r)return;
  $('routeDialogTitle').textContent='Editar rota'; $('routeId').value=r.id;$('routeVehicle').value=r.vehicle;$('routeDate').value=r.date;$('routeDriver').value=r.driver||'';$('routeDestination').value=r.destination||'';$('routeNeighborhood').value=r.neighborhood||'';$('routeLat').value=r.lat??'';$('routeLng').value=r.lng??'';$('routeNotes').value=r.notes||'';$('routeDialog').showModal();
}
async function deleteRoute(id){
  if(!confirm('Excluir esta rota? Fotos e sinistros permanecerão salvos, mas perderão o vínculo com a rota.'))return;
  await del('routes',id);
  const photos=await getAll('photos');for(const p of photos.filter(x=>x.routeId===id)){p.routeId='';await put('photos',p)}
  const incidents=await getAll('incidents');for(const i of incidents.filter(x=>x.routeId===id)){i.routeId='';await put('incidents',i)}
  if(selectedRouteId===id)selectedRouteId='';toast('Rota excluída.');await render();
}
async function saveRoute(ev){
  ev.preventDefault();
  const existingId=$('routeId').value; const old=existingId?(await getAll('routes')).find(x=>x.id===existingId):null;
  const lat=parseCoord($('routeLat').value),lng=parseCoord($('routeLng').value);
  const r={id:existingId||uid(),vehicle:$('routeVehicle').value,date:$('routeDate').value,driver:$('routeDriver').value.trim(),destination:$('routeDestination').value.trim(),neighborhood:$('routeNeighborhood').value.trim(),lat,lng,notes:$('routeNotes').value.trim(),updatedAt:new Date().toISOString()};
  await put('routes',r);
  if(old && old.vehicle!==r.vehicle){
    const photos=await getAll('photos'); for(const p of photos.filter(x=>x.routeId===r.id)){p.vehicle=r.vehicle;await put('photos',p)}
    const incidents=await getAll('incidents'); for(const i of incidents.filter(x=>x.routeId===r.id)){i.vehicle=r.vehicle;await put('incidents',i)}
  }
  await put('settings',{key:'vehicle:'+r.vehicle,destination:r.destination});
  selectedVehicle=r.vehicle; selectedRouteId=r.id; $('routeDialog').close();toast(existingId?'Rota atualizada.':'Rota cadastrada.');await render();setTimeout(fitMap,100);
}

async function nextIncidentCode(){ const list=await getAll('incidents');const nums=list.map(i=>Number(String(i.code||'').match(/\d+/)?.[0]||0));const n=(nums.length?Math.max(...nums):0)+1;return 'Sinistro '+String(n).padStart(2,'0') }
async function openNewIncident(){
  $('incidentForm').reset(); $('incidentId').value=''; $('incidentVehicle').value=selectedVehicle;$('incidentDate').value=new Date(Date.now()-new Date().getTimezoneOffset()*60000).toISOString().slice(0,16);tempIncidentPhoto=null;$('incidentPhotoPreview').innerHTML='';$('incidentTitle').textContent=await nextIncidentCode();await fillIncidentRoutes();if(selectedRouteId)$('incidentRoute').value=selectedRouteId;$('incidentDialog').showModal();
}
async function editIncident(id){
  const i=(await getAll('incidents')).find(x=>x.id===id);if(!i)return;$('incidentId').value=i.id;$('incidentVehicle').value=i.vehicle;await fillIncidentRoutes();$('incidentRoute').value=i.routeId||'';$('incidentDate').value=i.date?.slice(0,16)||'';$('incidentType').value=i.type||'Sinistro';$('incidentLat').value=i.lat??'';$('incidentLng').value=i.lng??'';$('incidentAddress').value=i.address||'';$('incidentDescription').value=i.description||'';$('incidentTitle').textContent=i.code;tempIncidentPhoto=i.blob||null;$('incidentPhotoPreview').innerHTML=i.blob?`<img src="${URL.createObjectURL(i.blob)}" alt="Foto do sinistro">`:'';$('incidentDialog').showModal();
}
async function saveIncident(ev){
  ev.preventDefault(); const id=$('incidentId').value; const old=id?(await getAll('incidents')).find(x=>x.id===id):null; const lat=parseCoord($('incidentLat').value),lng=parseCoord($('incidentLng').value); if(lat===null||lng===null){toast('Informe coordenadas válidas.');return}
  const inc={id:id||uid(),code:old?.code||await nextIncidentCode(),vehicle:$('incidentVehicle').value,routeId:$('incidentRoute').value,date:$('incidentDate').value,type:$('incidentType').value,lat,lng,address:$('incidentAddress').value.trim(),description:$('incidentDescription').value.trim(),blob:tempIncidentPhoto||old?.blob||null,updatedAt:new Date().toISOString()};
  await put('incidents',inc);selectedVehicle=inc.vehicle;if(inc.routeId)selectedRouteId=inc.routeId;$('incidentDialog').close();toast(id?'Sinistro atualizado.':'Sinistro cadastrado.');await render();setTimeout(fitMap,100);
}

async function analyzePhotoRecord(p,forceInset=true,{workerSlot=0,reprocess=false}={}){
  if(!p?.blob)return p;
  // Em processamento automático, fotos já confirmadas podem ser preservadas. O botão
  // "Localizar coordenadas" força reavaliação quando a origem atual tem prioridade menor.
  if(!reprocess&&validCoords(Number(p.lat),Number(p.lng)))return p;

  let meta=null,overlay=null,addressOverlay=null,inset=null,gps=null;

  // Metadados de data/câmera não participam da decisão de localização e podem ser lidos
  // sem antecipar o GPS/EXIF na ordem operacional.
  try{meta=await exifr.parse(p.blob,['DateTimeOriginal','CreateDate','Make','Model'])}catch(e){console.warn('Metadados EXIF:',e)}
  const dt=meta?.DateTimeOriginal||meta?.CreateDate;if(!p.takenAt&&dt instanceof Date)p.takenAt=dt.toISOString();
  if(!p.camera)p.camera=[meta?.Make,meta?.Model].filter(Boolean).join(' ');
  if(!forceInset)return p;

  const worker=await getOcrWorker(workerSlot);
  const drawable=await loadImageDrawable(p.blob); // uma única decodificação para todas as etapas OCR
  try{
    // 1) PRIORIDADE MÁXIMA: coordenadas geográficas escritas no canto inferior direito.
    try{overlay=await readCoordinateOverlay(p.blob,{worker,drawable})}catch(e){console.warn('Coordenadas impressas:',e);p.overlayCoordError=e.message}

    // 2) Se não houver coordenadas legíveis: Rua + número no canto inferior esquerdo
    //    e geocodificação obrigatoriamente pelo Google Maps em Apucarana/PR.
    if(!validCoords(overlay?.lat,overlay?.lng)){
      try{addressOverlay=await readAddressOverlay(p.blob,{worker,drawable})}catch(e){console.warn('Endereço impresso:',e);p.addressOverlayError=e.message}
    }

    // 3) Se ainda não localizar: analisar o mini mapa presente na fotografia.
    if(!validCoords(overlay?.lat,overlay?.lng)&&!validCoords(addressOverlay?.lat,addressOverlay?.lng)){
      try{inset=await locateFromGoogleMapInset(p.blob,{worker,drawable})}catch(e){console.warn('Mini mapa:',e);p.mapInsetError=e.message}
    }
  }finally{closeImageDrawable(drawable)}

  // 4) ÚLTIMA ALTERNATIVA: somente depois das três tentativas visuais, ler GPS/EXIF.
  if(!validCoords(overlay?.lat,overlay?.lng)&&!validCoords(addressOverlay?.lat,addressOverlay?.lng)&&!validCoords(inset?.lat,inset?.lng)){
    try{gps=await exifr.gps(p.blob)}catch(e){console.warn('GPS/EXIF:',e)}
  }

  if(validCoords(overlay?.lat,overlay?.lng)){
    p.lat=overlay.lat;p.lng=overlay.lng;p.coordSource='overlay-right';p.coordFormat=overlay.format||'coordenada OCR';
    p.overlayCoordText=overlay.overlayText||'';p.overlayCoordConfidence=overlay.confidence||0;p.overlayCoordError='';p.mapInsetError='';p.addressOverlayError='';p.locationError='';
  } else if(validCoords(addressOverlay?.lat,addressOverlay?.lng)){
    p.lat=addressOverlay.lat;p.lng=addressOverlay.lng;p.coordSource='address-overlay-left';p.coordFormat='logradouro + número geocodificados';
    p.addressOverlayText=addressOverlay.addressText||'';p.addressOverlayQuery=addressOverlay.query||'';p.addressOverlayConfidence=addressOverlay.confidence||0;p.addressOverlayError='';
    p.mapInsetAddress=addressOverlay.address||'';p.mapInsetProvider='Google Maps';
    p.overlayCoordText=overlay?.overlayText||p.overlayCoordText||'';p.overlayCoordError=overlay?.error||p.overlayCoordError||'';p.mapInsetError='';p.locationError='';
  } else if(validCoords(inset?.lat,inset?.lng)){
    p.lat=inset.lat;p.lng=inset.lng;p.coordSource=inset.method==='coordinates'?'google-inset-coordinates':'google-inset';
    p.coordFormat=inset.method==='coordinates'?'coordenada lida no mini mapa':'rótulos geocodificados';
    p.mapInsetText=inset.mapText||'';p.mapInsetQuery=inset.query||'';p.mapInsetAddress=inset.address||'';p.mapInsetProvider=inset.provider||'Google Maps';
    p.overlayCoordText=overlay?.overlayText||p.overlayCoordText||'';p.overlayCoordError=overlay?.error||p.overlayCoordError||'';
    p.addressOverlayText=addressOverlay?.addressText||p.addressOverlayText||'';p.addressOverlayError=addressOverlay?.error||p.addressOverlayError||'';p.locationError='';
  } else if(Number.isFinite(gps?.latitude)&&Number.isFinite(gps?.longitude)&&inApucaranaBounds(gps.latitude,gps.longitude)){
    p.lat=gps.latitude;p.lng=gps.longitude;p.coordSource='exif';p.coordFormat='GPS/EXIF';
    p.overlayCoordText=overlay?.overlayText||p.overlayCoordText||'';p.overlayCoordError=overlay?.error||p.overlayCoordError||'';
    p.addressOverlayText=addressOverlay?.addressText||p.addressOverlayText||'';p.addressOverlayError=addressOverlay?.error||p.addressOverlayError||'';
    p.mapInsetText=inset?.mapText||p.mapInsetText||'';p.mapInsetError=inset?.error||p.mapInsetError||'';p.locationError='';
  } else {
    p.lat=null;p.lng=null;p.coordSource='none';
    p.overlayCoordText=overlay?.overlayText||p.overlayCoordText||'';p.overlayCoordError=overlay?.error||p.overlayCoordError||'';
    p.addressOverlayText=addressOverlay?.addressText||p.addressOverlayText||'';p.addressOverlayError=addressOverlay?.error||p.addressOverlayError||'';
    p.mapInsetText=inset?.mapText||p.mapInsetText||'';p.mapInsetError=inset?.error||p.mapInsetError||'';
    p.locationError='Nenhuma das quatro etapas confirmou a localização.';
  }
  return p;
}
function newLocationStats(){return {located:0,withoutGps:0,exif:0,overlay:0,address:0,map:0,skipped:0,done:0}}
function tallyLocation(stats,p,skipped=false){
  stats.done++;if(validCoords(Number(p.lat),Number(p.lng))){stats.located++;if(skipped)stats.skipped++;else if(p.coordSource==='exif')stats.exif++;else if(p.coordSource==='overlay-right')stats.overlay++;else if(p.coordSource==='address-overlay-left')stats.address++;else if(String(p.coordSource||'').startsWith('google-inset'))stats.map++;}else stats.withoutGps++;return stats;
}
async function processPhotoLocationBatch(photos,{reprocess=false,onProgress=null}={}){
  const list=Array.from(photos||[]),stats=newLocationStats();if(!list.length)return stats;
  let cursor=0;const concurrency=Math.min(OCR_POOL_SIZE,list.length);
  const runners=Array.from({length:concurrency},(_,slot)=>(async()=>{
    while(true){
      const idx=cursor++;if(idx>=list.length)break;const original=list[idx];let updated=original;
      const skip=!reprocess&&validCoords(Number(original.lat),Number(original.lng));
      if(!skip){try{updated=await analyzePhotoRecord(original,true,{workerSlot:slot,reprocess})}catch(e){console.warn('Localização da foto:',original.fileName,e);updated.locationError=e?.message||String(e)}await put('photos',updated)}
      tallyLocation(stats,updated,skip);if(onProgress)onProgress({...stats,total:list.length,last:updated,index:idx,concurrency});
    }
  })());
  await Promise.all(runners);return stats;
}
async function locateOnePhotoFromInset(id){
  const p=(await getAll('photos')).find(x=>x.id===id);if(!p?.blob)return;
  setProcessProgress('location',0,1,`Analisando ${p.fileName||'fotografia'}…`);setOcrStatus('Coordenadas impressas → Rua + número/Google Maps → mini mapa → GPS/EXIF…');
  try{
    const updated=await analyzePhotoRecord(p,true,{workerSlot:0,reprocess:true});await put('photos',updated);
    setProcessProgress('location',1,1,validCoords(updated.lat,updated.lng)?`Localizada • ${updated.lat.toFixed(6)}, ${updated.lng.toFixed(6)} • ${coordSourceLabel(updated)}`:'Análise concluída • coordenadas não confirmadas');
    if(validCoords(updated.lat,updated.lng)){toast(`Foto localizada: ${updated.lat.toFixed(6)}, ${updated.lng.toFixed(6)}`);await render();setTimeout(()=>map.flyTo([updated.lat,updated.lng],18,{duration:.6}),100)}
    else {toast(updated.overlayCoordError||updated.addressOverlayError||updated.mapInsetError||'Não foi possível localizar esta foto automaticamente.');await render()}
  }catch(e){console.error(e);setProcessProgress('location',1,1,'Falha durante a localização');toast('Falha ao localizar a fotografia.');}
  finally{setOcrStatus('',false);hideProcessProgress('location',2600)}
}
async function handlePhotoUpload(files){
  if(!files?.length)return;
  if(!selectedRouteId){toast('Cadastre ou selecione uma rota antes de enviar fotos.');$('photoUpload').value='';return}
  const route=(await getAll('routes')).find(r=>r.id===selectedRouteId);if(!route){toast('Rota selecionada não encontrada.');return}
  const list=Array.from(files),totalBytes=list.reduce((sum,f)=>sum+(f.size||0),0);let uploadedBytes=0;const saved=[];
  setProcessProgress('upload',0,Math.max(totalBytes,1),`Preparando ${list.length} foto(s) • ${formatMb(totalBytes)}`);hideProcessProgress('location');
  try{
    for(let i=0;i<list.length;i++){
      const file=list[i],photo={id:uid(),vehicle:selectedVehicle,routeId:selectedRouteId,fileName:file.name,mime:file.type,blob:file,lat:null,lng:null,takenAt:null,createdAt:new Date().toISOString(),camera:'',coordSource:'none'};
      await put('photos',photo);saved.push(photo);uploadedBytes+=file.size||0;setProcessProgress('upload',uploadedBytes,Math.max(totalBytes,1),`${i+1}/${list.length} • ${file.name} • ${formatMb(uploadedBytes)} de ${formatMb(totalBytes)}`);
    }
    setProcessProgress('upload',Math.max(totalBytes,1),Math.max(totalBytes,1),`Upload concluído • ${list.length} foto(s) • ${formatMb(totalBytes)}`);
    setProcessProgress('location',0,saved.length,`Até ${Math.min(OCR_POOL_SIZE,saved.length)} foto(s) em paralelo • coordenadas impressas primeiro`);setOcrStatus('Coordenadas impressas → endereço/Google Maps → mini mapa → GPS/EXIF…');
    const stats=await processPhotoLocationBatch(saved,{onProgress:s=>{setProcessProgress('location',s.done,s.total,`${s.done}/${s.total} • ${s.located} localizada(s) • ${s.withoutGps} pendente(s) • ${s.concurrency} processo(s)`);setOcrStatus(`Localização ${Math.round(s.done/s.total*100)}% • ${s.last?.fileName||''}`)}});
    setProcessProgress('location',saved.length,saved.length,`Concluído • ${stats.located} de ${saved.length} foto(s) localizadas`);
    toast(`${list.length} foto(s): ${stats.located} localizadas${stats.exif?` • ${stats.exif} por GPS/EXIF`:''}${stats.overlay?` • ${stats.overlay} pelas coordenadas escritas`:''}${stats.address?` • ${stats.address} por rua e número`:''}${stats.map?` • ${stats.map} pelo mini mapa`:''}${stats.withoutGps?` • ${stats.withoutGps} sem localização`:''}.`);
  }finally{setOcrStatus('',false);$('photoUpload').value='';clearPhotoProgress(3000)}
  await render();setTimeout(fitMap,120);
}
async function analyzeExistingPhotos(){
  if(!selectedRouteId){toast('Selecione uma rota para analisar as fotografias.');return}
  const photos=(await getAll('photos')).filter(p=>p.routeId===selectedRouteId&&p.blob);if(!photos.length){toast('Esta rota não possui fotografias.');return}

  // Coordenadas OCR (1º) e endereço Google Maps (2º) já estão em fontes de prioridade máxima.
  // Fotos localizadas por mini mapa, GPS/EXIF ou ainda sem posição são reavaliadas para tentar
  // promovê-las a uma fonte mais prioritária, exatamente na ordem definida pelo usuário.
  const best=photos.filter(p=>validCoords(Number(p.lat),Number(p.lng))&&['overlay-right','address-overlay-left'].includes(p.coordSource));
  const candidates=photos.filter(p=>!best.some(b=>b.id===p.id));
  hideProcessProgress('upload');
  if(!candidates.length){setProcessProgress('location',1,1,`100% • ${photos.length} foto(s) já confirmadas pelas fontes prioritárias`);toast('Todas as fotografias já estão confirmadas por coordenadas impressas ou endereço/Google Maps.');return}

  setProcessProgress('location',0,candidates.length,`${best.length} já confirmada(s) • ${candidates.length} para localizar/reavaliar`);
  setOcrStatus('Coordenadas impressas → Rua + número/Google Maps → mini mapa → GPS/EXIF…');
  try{
    const stats=await processPhotoLocationBatch(candidates,{reprocess:true,onProgress:s=>{
      setProcessProgress('location',s.done,s.total,`${s.done}/${s.total} processada(s) • ${s.located} localizada(s) • ${s.withoutGps} não localizada(s)`);
      setOcrStatus(`Localização ${Math.round(s.done/s.total*100)}% • ${s.last?.fileName||''}`);
    }});
    const refreshed=(await getAll('photos')).filter(p=>p.routeId===selectedRouteId&&p.blob);
    const totalLocated=refreshed.filter(p=>validCoords(Number(p.lat),Number(p.lng))).length;
    setProcessProgress('location',candidates.length,candidates.length,`Concluído • ${totalLocated} de ${photos.length} foto(s) posicionadas no mapa`);
    toast(`Análise concluída: ${totalLocated} de ${photos.length} foto(s) localizadas. Ordem aplicada: coordenadas → endereço/Google Maps → mini mapa → GPS/EXIF.`);
  }finally{setOcrStatus('',false);hideProcessProgress('location',3000)}
  await render();setTimeout(fitMap,120);
}
async function openPhoto(id){
  const p=(await getAll('photos')).find(x=>x.id===id);if(!p?.blob)return;
  if(photoModalUrl)URL.revokeObjectURL(photoModalUrl); photoModalUrl=URL.createObjectURL(p.blob);
  $('photoLarge').src=photoModalUrl;$('photoMeta').textContent=`${p.vehicle} • ${p.fileName} • ${p.takenAt?fmtDate(p.takenAt):'data não disponível'} • ${Number.isFinite(p.lat)?`${p.lat.toFixed(6)}, ${p.lng.toFixed(6)} • ${coordSourceLabel(p)}`:'sem coordenadas'}${p.mapInsetAddress?' • '+p.mapInsetAddress:''}${p.camera?' • '+p.camera:''}`;$('photoDialog').showModal();
}

async function openSettings(){
  $('googleMapsApiKey').value=await getSetting('googleMapsApiKey','');
  if($('googleDriveClientId'))$('googleDriveClientId').value=await getSetting('googleDriveClientId','');
  if($('googleDriveAutoSync'))$('googleDriveAutoSync').checked=String(await getSetting('googleDriveAutoSync','true'))!=='false';
  updateDriveStatusUi();
  $('settingsDialog').showModal();
}
async function saveSettings(ev){
  ev.preventDefault();
  const old=await getSetting('googleMapsApiKey','');
  const key=$('googleMapsApiKey').value.trim();
  const driveClientId=$('googleDriveClientId')?.value.trim()||'';
  cloudAutoSync=!!$('googleDriveAutoSync')?.checked;
  cloudSyncSuspend++;
  try{
    await setSetting('googleMapsApiKey',key);
    await setSetting('googleDriveClientId',driveClientId);
    await setSetting('googleDriveAutoSync',String(cloudAutoSync));
  }finally{cloudSyncSuspend--}
  if(key!==old)googleMapsLoadPromise=null;
  $('settingsDialog').close();updateDriveStatusUi();toast('Configurações salvas.');markCloudDirty();
}

async function exportJson(){
  const data=await buildBackupObject();
  download(new Blob([JSON.stringify(data,null,2)],{type:'application/json'}),`APUC_Rotas_backup_${new Date().toISOString().slice(0,10)}.json`)
}
async function importJson(file){
  try{const data=JSON.parse(await file.text());const ok=await restoreBackupObject(data,{confirmReplace:true});if(ok){cloudDirty=true;updateDriveStatusUi();toast('Backup importado.')}}catch(e){alert('Não foi possível importar o backup: '+e.message)}finally{$('inputImportJson').value=''}
}
async function exportCsv(){
  const [routes,photos,incidents]=await Promise.all([getAll('routes'),getAll('photos'),getAll('incidents')]);const rows=[['veiculo','data_rota','destino','bairro_localidade','responsavel','latitude_destino','longitude_destino','qtd_fotos','qtd_sinistros','observacoes']];for(const r of routes.filter(x=>x.vehicle===selectedVehicle)){rows.push([r.vehicle,r.date,r.destination,r.neighborhood||'',r.driver||'',r.lat??'',r.lng??'',photos.filter(p=>p.routeId===r.id).length,incidents.filter(i=>i.routeId===r.id).length,r.notes||''])}const csv='\uFEFF'+rows.map(row=>row.map(v=>'"'+String(v).replaceAll('"','""')+'"').join(';')).join('\r\n');download(new Blob([csv],{type:'text/csv;charset=utf-8'}),`${selectedVehicle}_rotas.csv`)
}
function download(blob,name){const a=document.createElement('a');a.href=URL.createObjectURL(blob);a.download=name;a.click();setTimeout(()=>URL.revokeObjectURL(a.href),1000)}
async function resetAll(){
  const photos=await getAll('photos');
  if(!photos.length){toast('Não há fotografias de rotas para apagar.');return}
  if(!confirm(`ATENÇÃO: apagar TODAS as ${photos.length} fotografia(s) vinculada(s) às rotas?\n\nAs rotas, sinistros, laudos e configurações serão preservados.`))return;
  await clearStore('photos');
  toast(`${photos.length} fotografia(s) apagada(s). As rotas foram preservadas.`);
  await render();
  setTimeout(fitMap,120);
}

function normalizeNeighborhood(v=''){return String(v||'').trim().replace(/\s+/g,' ').toLocaleLowerCase('pt-BR')}
function routeNeighborhood(r){return String(r?.neighborhood||r?.destination||'').trim()}
function reportScopeLabel(scope){return scope===ALL_REPORT_SCOPE?'Todos os bairros — consolidado':String(scope||'').trim()}
function reportIdForNeighborhood(scope){return scope===ALL_REPORT_SCOPE?'laudo:unificado':'bairro:'+normalizeNeighborhood(scope)}
function reportSafeName(v=''){return String(v||'laudo').normalize('NFD').replace(/[\u0300-\u036f]/g,'').replace(/[^a-zA-Z0-9_-]+/g,'_').replace(/^_+|_+$/g,'').slice(0,80)||'laudo'}
function fmtMoneyInput(v){
  const raw=String(v??'').trim();if(!raw)return '0,00';
  const normalized=raw.replace(/\./g,'').replace(',','.').replace(/[^0-9.-]/g,'');const n=Number(normalized);
  return Number.isFinite(n)?n.toLocaleString('pt-BR',{minimumFractionDigits:2,maximumFractionDigits:2}):raw;
}
function reportDatePt(value){if(!value)return '____/____/________';const d=new Date(value+'T12:00:00');return Number.isNaN(d.getTime())?value:d.toLocaleDateString('pt-BR')}
function reportLongDate(value=new Date()){
  const d=value instanceof Date?value:new Date(value);const months=['JANEIRO','FEVEREIRO','MARÇO','ABRIL','MAIO','JUNHO','JULHO','AGOSTO','SETEMBRO','OUTUBRO','NOVEMBRO','DEZEMBRO'];
  return `${String(d.getDate()).padStart(2,'0')} DE ${months[d.getMonth()]} DE ${d.getFullYear()}`;
}
async function renderReportsSummary(){
  const [routes,photos,units]=await Promise.all([getAll('routes'),getAll('photos'),getAll('surveyUnits')]);
  const nbs=new Map();for(const r of routes){const n=routeNeighborhood(r);if(n)nbs.set(normalizeNeighborhood(n),n)}for(const u of units.filter(inspectionIsAffected)){const n=inspectionUnitNeighborhood(u);if(n)nbs.set(normalizeNeighborhood(n),n)}
  if($('reportNeighborhoodCount'))$('reportNeighborhoodCount').textContent=nbs.size;
  if($('reportEligiblePhotos'))$('reportEligiblePhotos').textContent=photos.filter(p=>p.routeId&&p.blob).length;
  const affected=units.filter(inspectionIsAffected);if($('inspectionUnitCount'))$('inspectionUnitCount').textContent=affected.length;if($('inspectionLocatedCount'))$('inspectionLocatedCount').textContent=affected.filter(u=>validCoords(Number(u.lat),Number(u.lng))).length;if($('inspectionBudgetTotal'))$('inspectionBudgetTotal').textContent=inspectionMoney(inspectionBudgetForUnits(affected).total);
}
async function reportNeighborhoods(){
  const [routes,units]=await Promise.all([getAll('routes'),getAll('surveyUnits')]);const map=new Map();
  for(const r of routes){const n=routeNeighborhood(r);if(n&&!map.has(normalizeNeighborhood(n)))map.set(normalizeNeighborhood(n),n)}
  for(const u of units.filter(inspectionIsAffected)){const n=inspectionUnitNeighborhood(u);if(n&&!map.has(normalizeNeighborhood(n)))map.set(normalizeNeighborhood(n),n)}
  return [...map.values()].sort((a,b)=>a.localeCompare(b,'pt-BR'));
}
async function renderReportNeighborhoodOptions(){
  const list=await reportNeighborhoods();const select=$('reportNeighborhood');if(!select)return;
  const previous=select.value;const routes=await getAll('routes');const selected=routes.find(r=>r.id===selectedRouteId);const preferred=routeNeighborhood(selected);
  select.innerHTML=`<option value="${ALL_REPORT_SCOPE}">TODOS OS BAIRROS — LAUDO UNIFICADO</option>`+list.map(n=>`<option value="${esc(n)}">${esc(n)}</option>`).join('');
  if(previous&&[...select.options].some(o=>o.value===previous))select.value=previous;else if(preferred&&list.some(n=>normalizeNeighborhood(n)===normalizeNeighborhood(preferred)))select.value=list.find(n=>normalizeNeighborhood(n)===normalizeNeighborhood(preferred));else select.value=ALL_REPORT_SCOPE;
  select.disabled=false;if(!$('reportEventDate').value)$('reportEventDate').value=new Date().toISOString().slice(0,10);await loadReportDraftForNeighborhood();
}
async function reportStatsForNeighborhood(scope){
  const [routes,photos,incidents,units]=await Promise.all([getAll('routes'),getAll('photos'),getAll('incidents'),getAll('surveyUnits')]);const all=scope===ALL_REPORT_SCOPE;const key=normalizeNeighborhood(scope);
  const rs=all?routes:routes.filter(r=>normalizeNeighborhood(routeNeighborhood(r))===key);const ids=new Set(rs.map(r=>r.id));
  const ps=all?photos:photos.filter(p=>ids.has(p.routeId));const ins=all?incidents:incidents.filter(i=>ids.has(i.routeId));
  const us=(all?units:units.filter(u=>normalizeNeighborhood(inspectionUnitNeighborhood(u))===key)).filter(inspectionIsAffected);
  return {routes:rs,photos:ps,incidents:ins,units:us};
}
function reportAutoDamageText(units=[]){const b=inspectionBudgetForUnits(units);return b.items.map(x=>`${x.label}: ${x.qty.toLocaleString('pt-BR',{maximumFractionDigits:2})} ${x.unit}`).join('; ')}
function reportAutoNotes(units=[],scope=''){
  if(!units.length)return '';
  const notLocated=units.filter(u=>!validCoords(Number(u.lat),Number(u.lng))).length;const noAddress=units.filter(u=>!u.address&&!validCoords(Number(u.lat),Number(u.lng))).length;const divergences=units.reduce((s,u)=>s+(u.divergences?.length||0),0);
  const bits=[`Dados consolidados a partir das planilhas de vistoria: ${units.length} unidade(s) com necessidade registrada.`];if(notLocated)bits.push(`${notLocated} unidade(s) ainda sem coordenadas confirmadas; utilize “Localizar unidades das planilhas” para geocodificação quando houver endereço.`);if(noAddress)bits.push(`${noAddress} unidade(s) não possuem endereço nem coordenadas no bloco estruturado da planilha.`);if(divergences)bits.push(`Foram identificadas ${divergences} divergência(s) entre quadros-resumo e fichas detalhadas; o sistema preserva a ficha detalhada como referência unitária e sinaliza a inconsistência para conferência.`);bits.push('Os valores são referenciais, cruzados com o Modelo orçamento.xlsx. Grade/portão e padrão de energia utilizam itens correlatos do banco de insumos e exigem confirmação do escopo técnico antes da contratação.');return bits.join(' ')
}
async function renderInspectionReportSummary(scope){
  const el=$('reportInspectionSummary');if(!el)return;const ctx=await reportStatsForNeighborhood(scope);const b=inspectionBudgetForUnits(ctx.units);const located=ctx.units.filter(u=>validCoords(Number(u.lat),Number(u.lng))).length;const divs=ctx.units.reduce((s,u)=>s+(u.divergences?.length||0),0);
  if(!ctx.units.length){el.innerHTML='<div class="inspection-source-alert">Não há unidades das planilhas vinculadas a este bairro/localidade. O laudo continuará usando os registros de rotas, fotos e sinistros.</div>';return}
  const rows=b.items.map(x=>`<tr><td>${esc(x.label)}</td><td>${x.qty.toLocaleString('pt-BR',{maximumFractionDigits:2})} ${esc(x.unit)}</td><td>${inspectionMoney(x.unitPrice)}</td><td>${inspectionMoney(x.subtotal)}</td></tr>`).join('');
  el.innerHTML=`<div class="inspection-title"><strong>PLANILHAS DE VISTORIA + MODELO ORÇAMENTÁRIO</strong><span>${inspectionMoney(b.total)}</span></div><div class="inspection-kpis"><div class="inspection-kpi"><b>${ctx.units.length}</b><small>unidades afetadas</small></div><div class="inspection-kpi"><b>${located}</b><small>com coordenadas</small></div><div class="inspection-kpi"><b>${ctx.units.filter(u=>u.address).length}</b><small>com endereço</small></div><div class="inspection-kpi"><b>${divs}</b><small>divergências de origem</small></div></div><table class="inspection-budget-mini"><thead><tr><th>Serviço</th><th>Quantidade</th><th>Unitário</th><th>Subtotal</th></tr></thead><tbody>${rows}<tr class="total"><td colspan="3">TOTAL REFERENCIAL</td><td>${inspectionMoney(b.total)}</td></tr></tbody></table>${divs?`<div class="inspection-source-alert">Há ${divs} divergência(s) entre resumos e fichas detalhadas. Elas serão indicadas no laudo para conferência.</div>`:''}`;
}
async function updateReportDataSummary(){
  const scope=$('reportNeighborhood').value;const ctx=await reportStatsForNeighborhood(scope);const gps=ctx.photos.filter(p=>Number.isFinite(p.lat)&&Number.isFinite(p.lng)).length;const budget=inspectionBudgetForUnits(ctx.units);
  $('reportDataSummary').innerHTML=`<div class="report-summary-item"><strong>${ctx.routes.length}</strong><span>rotas</span></div><div class="report-summary-item"><strong>${ctx.photos.length}</strong><span>fotografias</span></div><div class="report-summary-item"><strong>${gps}</strong><span>fotos georreferenciadas</span></div><div class="report-summary-item"><strong>${ctx.incidents.length}</strong><span>sinistros</span></div><div class="report-summary-item"><strong>${ctx.units.length}</strong><span>unidades planilhas</span></div><div class="report-summary-item"><strong>${inspectionMoney(budget.total)}</strong><span>orçamento referencial</span></div>`;await renderInspectionReportSummary(scope);
}
async function loadReportDraftForNeighborhood(){
  const scope=$('reportNeighborhood').value;if(!scope){$('reportDataSummary').innerHTML='<div class="empty">Nenhum bairro/localidade disponível.</div>';return}
  const d=(await getAll('reports')).find(x=>x.id===reportIdForNeighborhood(scope));const stats=await reportStatsForNeighborhood(scope);const budget=inspectionBudgetForUnits(stats.units);
  $('reportEventType').value=d?.eventType||'';$('reportEventDate').value=d?.eventDate||$('reportEventDate').value||new Date().toISOString().slice(0,10);
  $('reportDamagedQty').value=d?.damagedQty??stats.units.length;$('reportDamagedValue').value=d?.damagedValue|| (budget.total?budget.total.toLocaleString('pt-BR',{minimumFractionDigits:2,maximumFractionDigits:2}):'');$('reportDamagedDamage').value=d?.damagedDamage||reportAutoDamageText(stats.units);$('reportDamagedImpact').value=d?.damagedImpact||'';
  $('reportDestroyedQty').value=d?.destroyedQty??0;$('reportDestroyedValue').value=d?.destroyedValue||'';$('reportDestroyedDamage').value=d?.destroyedDamage||'';$('reportDestroyedImpact').value=d?.destroyedImpact||'';
  $('reportTechnicalNotes').value=d?.technicalNotes||reportAutoNotes(stats.units,scope);$('reportIncludePhotos').checked=true;$('reportIncludeIncidents').checked=d?.includeIncidents??true;$('reportIncludeInspection').checked=d?.includeInspection??true;$('reportIncludeBudget').checked=d?.includeBudget??true;$('reportPhotoLimit').value=d?.photoLimit||12;await updateReportDataSummary();
}
function collectReportFormData(){
  const scope=$('reportNeighborhood').value.trim();const neighborhood=reportScopeLabel(scope);return {id:reportIdForNeighborhood(scope),scope,neighborhood,eventType:$('reportEventType').value.trim(),eventDate:$('reportEventDate').value,damagedQty:Math.max(0,Number($('reportDamagedQty').value||0)),damagedValue:$('reportDamagedValue').value.trim(),damagedDamage:$('reportDamagedDamage').value.trim(),damagedImpact:$('reportDamagedImpact').value.trim(),destroyedQty:Math.max(0,Number($('reportDestroyedQty').value||0)),destroyedValue:$('reportDestroyedValue').value.trim(),destroyedDamage:$('reportDestroyedDamage').value.trim(),destroyedImpact:$('reportDestroyedImpact').value.trim(),technicalNotes:$('reportTechnicalNotes').value.trim(),includePhotos:$('reportIncludePhotos').checked,includeIncidents:$('reportIncludeIncidents').checked,includeInspection:$('reportIncludeInspection').checked,includeBudget:$('reportIncludeBudget').checked,photoLimit:Math.min(60,Math.max(1,Number($('reportPhotoLimit').value||12))),updatedAt:new Date().toISOString()};
}
async function saveReportDraft(showToast=true){const d=collectReportFormData();if(!d.scope){toast('Selecione um bairro/localidade.');return null}await put('reports',d);if(showToast)toast('Dados do laudo salvos para '+d.neighborhood+'.');return d}
async function collectReportContext(){
  const data=collectReportFormData();if(!data.scope)throw new Error('Selecione um bairro/localidade.');if(!data.eventType)throw new Error('Informe a tipificação do evento / FIDE.');if(!data.eventDate)throw new Error('Informe a data do evento.');
  data.includePhotos=true;
  await put('reports',data);const linked=await reportStatsForNeighborhood(data.scope);linked.photos.sort(reportPhotoSort);const budget=inspectionBudgetForUnits(linked.units);const byNeighborhood=inspectionByNeighborhood(linked.units);
  const reportPhotos=data.includePhotos?linked.photos:[];const unitPhotoAssignments=reportAssignUnitPhotos(linked.units,reportPhotos,linked.routes);const matchedPhotoIds=new Set(unitPhotoAssignments.filter(x=>x.photo).map(x=>x.photo.id));
  return {...data,...linked,unified:data.scope===ALL_REPORT_SCOPE,surveyUnits:data.includeInspection?linked.units:[],budget:data.includeBudget?budget:{items:[],total:0},inspectionByNeighborhood:byNeighborhood,photos:reportPhotos,allPhotoCount:linked.photos.length,incidents:data.includeIncidents?linked.incidents:[],unitPhotoAssignments,matchedUnitPhotoCount:unitPhotoAssignments.filter(x=>x.photo).length,unmatchedUnitPhotoCount:unitPhotoAssignments.filter(x=>!x.photo).length,unmatchedPhotoCount:reportPhotos.filter(p=>!matchedPhotoIds.has(p.id)).length};
}
function setReportBusy(busy,label='Gerando…'){
  const f=$('reportForm');if(busy)f.classList.add('report-generating');else f.classList.remove('report-generating');for(const id of ['btnSaveReportDraft','btnGenerateDocx','btnGeneratePdf'])$(id).disabled=busy;if(busy)toast(label);
}
async function fetchBytes(url){const r=await fetch(url);if(!r.ok)throw new Error('Não foi possível carregar '+url);return new Uint8Array(await r.arrayBuffer())}
async function fetchDataUrl(url){const r=await fetch(url);if(!r.ok)throw new Error('Não foi possível carregar '+url);return await blobToDataURL(await r.blob())}
async function imageBlobToJpegAsset(blob,maxW=1500,maxH=1100,quality=.88){
  const bmp=await loadImageDrawable(blob);try{const ratio=Math.min(1,maxW/bmp.width,maxH/bmp.height);const w=Math.max(1,Math.round(bmp.width*ratio)),h=Math.max(1,Math.round(bmp.height*ratio));const c=document.createElement('canvas');c.width=w;c.height=h;const x=c.getContext('2d');x.fillStyle='#ffffff';x.fillRect(0,0,w,h);x.drawImage(bmp,0,0,w,h);const out=await new Promise((res,rej)=>c.toBlob(b=>b?res(b):rej(new Error('Falha ao preparar imagem')),'image/jpeg',quality));return {blob:out,dataUrl:await blobToDataURL(out),bytes:new Uint8Array(await out.arrayBuffer()),width:w,height:h}}finally{bmp.close?.();if(bmp._objectUrl)URL.revokeObjectURL(bmp._objectUrl)}}
function reportPhotoCaption(p,idx){const bits=[`Foto ${String(idx+1).padStart(2,'0')}`,p.vehicle||'',p.mapInsetAddress||'',Number.isFinite(p.lat)&&Number.isFinite(p.lng)?`${p.lat.toFixed(6)}, ${p.lng.toFixed(6)}`:'sem coordenadas',coordSourceLabel(p),fmtDate(p.takenAt||p.createdAt)];return bits.filter(Boolean).join(' • ')}
function reportIncidentLines(ctx){return ctx.incidents.map(i=>`${i.code||'Sinistro'} - ${i.type||'Ocorrência'} - ${i.address||'endereço não informado'} - ${i.description||'sem descrição complementar'}`)}
function reportMatchNorm(v=''){return String(v||'').normalize('NFD').replace(/[\u0300-\u036f]/g,'').toLowerCase().replace(/\b(rua|r\.?|avenida|av\.?|travessa|tv\.?|alameda|rodovia|br|apucarana|parana|pr|brasil|cep)\b/g,' ').replace(/[^a-z0-9]+/g,' ').replace(/\s+/g,' ').trim()}
function reportPhotoAddress(p){return [p?.mapInsetAddress,p?.addressOverlayText,p?.mapInsetText,p?.addressOverlayQuery,p?.fileName].filter(Boolean).join(' ')}
function reportAddressSimilarity(a,b){const A=reportMatchNorm(a),B=reportMatchNorm(b);if(!A||!B)return 0;if(A===B||A.includes(B)||B.includes(A))return 1;const as=new Set(A.split(' ').filter(x=>x.length>1)),bs=new Set(B.split(' ').filter(x=>x.length>1));if(!as.size||!bs.size)return 0;let hit=0;for(const x of as)if(bs.has(x))hit++;return hit/Math.max(as.size,bs.size)}
function reportDistanceMeters(a,b){if(!validCoords(Number(a?.lat),Number(a?.lng))||!validCoords(Number(b?.lat),Number(b?.lng)))return Infinity;const R=6371000,toRad=x=>x*Math.PI/180;const p1=toRad(Number(a.lat)),p2=toRad(Number(b.lat)),dp=toRad(Number(b.lat)-Number(a.lat)),dl=toRad(Number(b.lng)-Number(a.lng));const q=Math.sin(dp/2)**2+Math.cos(p1)*Math.cos(p2)*Math.sin(dl/2)**2;return 2*R*Math.atan2(Math.sqrt(q),Math.sqrt(1-q))}
function reportUnitSort(a,b){return inspectionUnitNeighborhood(a).localeCompare(inspectionUnitNeighborhood(b),'pt-BR')||String(a.vehicle||'').localeCompare(String(b.vehicle||''),'pt-BR')||Number(a.unitNumber||0)-Number(b.unitNumber||0)}
function reportPhotoSort(a,b){return String(a.takenAt||a.createdAt||'').localeCompare(String(b.takenAt||b.createdAt||''))}
function reportAssignUnitPhotos(units=[],photos=[],routes=[]){
  const routeMap=new Map(routes.map(r=>[r.id,r]));
  const ps=photos.filter(p=>p?.blob).map((p,i)=>({...p,_ri:i,_routeNeighborhood:routeNeighborhood(routeMap.get(p.routeId)||{})}));
  const us=[...units].sort(reportUnitSort);const used=new Set(),assigned=new Map();const pairs=[];
  for(const u of us){for(const p of ps){if(String(p.vehicle||'')!==String(u.vehicle||''))continue;const un=normalizeNeighborhood(inspectionUnitNeighborhood(u)),pn=normalizeNeighborhood(p._routeNeighborhood);const sameNb=!!(un&&pn&&un===pn);const sim=reportAddressSimilarity(u.formattedAddress||u.address||'',reportPhotoAddress(p));const dist=reportDistanceMeters(u,p);let score=sameNb?180:0;if(sim>=.28)score+=sim*1250;if(Number.isFinite(dist)){if(dist<=25)score+=1650;else if(dist<=60)score+=1350;else if(dist<=120)score+=1050;else if(dist<=250)score+=700;else if(dist<=500)score+=300;}if(un&&pn&&un!==pn)score-=220;if(score>=650)pairs.push({u,p,score,sim,dist,sameNb});}}
  pairs.sort((a,b)=>b.score-a.score||a.dist-b.dist);
  for(const x of pairs){if(assigned.has(x.u.id)||used.has(x.p.id))continue;let method='correspondência automática';if(Number.isFinite(x.dist)&&x.dist<=250)method=`proximidade geográfica (${Math.round(x.dist)} m)`;else if(x.sim>=.45)method='endereço reconhecido na fotografia';else if(x.sameNb)method='bairro e veículo';assigned.set(x.u.id,{photo:x.p,matchMethod:method,distanceMeters:Number.isFinite(x.dist)?x.dist:null,confidence:Math.min(1,x.score/1800)});used.add(x.p.id);}
  const groupKeys=new Set(us.map(u=>`${u.vehicle}|${normalizeNeighborhood(inspectionUnitNeighborhood(u))}`));
  for(const key of groupKeys){const [vehicle,nb]=key.split('|');const ru=us.filter(u=>!assigned.has(u.id)&&u.vehicle===vehicle&&normalizeNeighborhood(inspectionUnitNeighborhood(u))===nb).sort((a,b)=>Number(a.unitNumber||0)-Number(b.unitNumber||0));const rp=ps.filter(p=>!used.has(p.id)&&p.vehicle===vehicle&&(!nb||normalizeNeighborhood(p._routeNeighborhood)===nb)).sort(reportPhotoSort);for(let i=0;i<Math.min(ru.length,rp.length);i++){assigned.set(ru[i].id,{photo:rp[i],matchMethod:'ordem da rota no mesmo bairro',distanceMeters:reportDistanceMeters(ru[i],rp[i]),confidence:.45});used.add(rp[i].id);}}
  for(const vehicle of [...new Set(us.map(u=>u.vehicle))]){const ru=us.filter(u=>!assigned.has(u.id)&&u.vehicle===vehicle).sort((a,b)=>Number(a.unitNumber||0)-Number(b.unitNumber||0));const rp=ps.filter(p=>!used.has(p.id)&&p.vehicle===vehicle).sort(reportPhotoSort);for(let i=0;i<Math.min(ru.length,rp.length);i++){assigned.set(ru[i].id,{photo:rp[i],matchMethod:'ordem cronológica do veículo',distanceMeters:reportDistanceMeters(ru[i],rp[i]),confidence:.3});used.add(rp[i].id);}}
  return us.map(u=>({unit:u,...(assigned.get(u.id)||{photo:null,matchMethod:'foto não localizada',distanceMeters:null,confidence:0})}));
}
function reportUnitBudgetRows(u){return inspectionBudgetForUnits([u]).items}

async function generateTechnicalReportDocx(){
  try{
    if(!window.docx)throw new Error('Biblioteca de geração Word não carregada. Verifique a conexão com a internet.');
    setReportBusy(true,'Montando laudo Word A4 retrato…');
    const ctx=await collectReportContext();const D=window.docx;
    const {Document,Packer,Paragraph,TextRun,Table,TableRow,TableCell,WidthType,AlignmentType,VerticalAlign,BorderStyle,ImageRun,PageOrientation,PageBreak,SectionType}=D;
    const BLUE='4463A9',YELLOW='F2CB18',DARK='1B1B1B',GRAY='667085',LIGHT='F4F6F9',WHITE='FFFFFF',RED='9A1B1B';
    const A4={width:11906,height:16838,orientation:PageOrientation.PORTRAIT};
    const PAGE={page:{size:A4,margin:{top:520,bottom:560,left:620,right:620}}};
    const border=(color='C7CED8',size=4)=>({style:BorderStyle.SINGLE,size,color});
    const borders=(color='C7CED8')=>({top:border(color),bottom:border(color),left:border(color),right:border(color)});
    const txt=(text,opt={})=>new TextRun({text:String(text??''),bold:!!opt.bold,color:opt.color||DARK,size:opt.size||16,font:opt.font||'Aptos',italics:!!opt.italics});
    const para=(text='',opt={})=>new Paragraph({alignment:opt.align||AlignmentType.LEFT,spacing:{before:opt.before||0,after:opt.after??70,line:opt.line||230},keepNext:!!opt.keepNext,children:Array.isArray(text)?text:[txt(text,opt)]});
    const cell=(children,w,opt={})=>new TableCell({width:{size:w,type:WidthType.PERCENTAGE},verticalAlign:VerticalAlign.CENTER,shading:opt.fill?{fill:opt.fill}:undefined,borders:opt.noBorder?{top:border(WHITE,0),bottom:border(WHITE,0),left:border(WHITE,0),right:border(WHITE,0)}:borders(opt.border||'C7CED8'),margins:{top:80,bottom:80,left:90,right:90},children:Array.isArray(children)?children:[children]});
    const spanCell=(children,span,opt={})=>new TableCell({columnSpan:span,verticalAlign:VerticalAlign.CENTER,shading:opt.fill?{fill:opt.fill}:undefined,borders:borders(opt.border||'C7CED8'),margins:{top:80,bottom:80,left:90,right:90},children:Array.isArray(children)?children:[children]});
    const strip=(color,height=55)=>new Table({width:{size:100,type:WidthType.PERCENTAGE},rows:[new TableRow({height:{value:height,rule:'exact'},children:[cell(para('',{after:0}),100,{fill:color,border:color})]})]});
    const logoBytes=await fetchBytes('assets/prefeitura-apucarana-vertical.png');
    const brandHeader=(title='LAUDO TÉCNICO',subtitle='DANOS EM UNIDADES HABITACIONAIS')=>[
      new Table({width:{size:100,type:WidthType.PERCENTAGE},rows:[new TableRow({children:[cell(new Paragraph({children:[new ImageRun({data:logoBytes,transformation:{width:82,height:74}})]}),24,{noBorder:true}),cell([para(title,{bold:true,color:BLUE,size:29,align:AlignmentType.RIGHT,after:16,font:'Aptos Display'}),para(subtitle,{bold:true,size:15,align:AlignmentType.RIGHT,after:16}),para('PREFEITURA DE APUCARANA • GESTÃO DE CAMPO',{color:GRAY,size:11,align:AlignmentType.RIGHT,after:0})],76,{noBorder:true})]})]}),strip(YELLOW,28),strip(BLUE,58)
    ];
    const labelCell=(label,value,w)=>cell([para(label,{bold:true,color:BLUE,size:11,after:15}),para(value||'—',{bold:true,size:13,after:0})],w,{fill:LIGHT,border:'D9DFE8'});
    const metaTable=new Table({width:{size:100,type:WidthType.PERCENTAGE},rows:[new TableRow({children:[labelCell('BAIRRO / LOCALIDADE',ctx.neighborhood,50),labelCell('EVENTO / FIDE',ctx.eventType,50)]}),new TableRow({children:[labelCell('DATA DO EVENTO',reportDatePt(ctx.eventDate),50),labelCell('REGISTROS',`${ctx.allPhotoCount} fotos • ${ctx.matchedUnitPhotoCount} associadas`,50)]})]});
    const damageTable=(qty,damage,value,impact)=>new Table({width:{size:100,type:WidthType.PERCENTAGE},rows:[
      new TableRow({children:[cell(para('Quantidade',{bold:true,color:WHITE,size:11,align:AlignmentType.CENTER,after:0}),20,{fill:BLUE,border:'FFFFFF'}),cell(para('Localidade / Bairro',{bold:true,color:WHITE,size:11,align:AlignmentType.CENTER,after:0}),45,{fill:BLUE,border:'FFFFFF'}),cell(para('Valor Estimado R$',{bold:true,color:WHITE,size:11,align:AlignmentType.CENTER,after:0}),35,{fill:BLUE,border:'FFFFFF'})]}),
      new TableRow({children:[cell(para(String(qty),{bold:true,align:AlignmentType.CENTER,after:0}),20),cell(para(ctx.neighborhood,{align:AlignmentType.CENTER,after:0}),45),cell(para('R$ '+fmtMoneyInput(value),{bold:true,align:AlignmentType.CENTER,after:0}),35)]}),
      new TableRow({children:[spanCell(para('DANOS NAS EDIFICAÇÕES',{bold:true,color:BLUE,size:11,after:0}),3,{fill:LIGHT})]}),new TableRow({children:[spanCell(para(damage||'—',{size:12,after:0}),3)]}),
      new TableRow({children:[spanCell(para('IMPACTO AOS MORADORES',{bold:true,color:BLUE,size:11,after:0}),3,{fill:LIGHT})]}),new TableRow({children:[spanCell(para(impact||'—',{size:12,after:0}),3)]})
    ]});
    const genericHeader=(labels,widths)=>new TableRow({children:labels.map((x,i)=>cell(para(x,{bold:true,color:WHITE,size:10,align:AlignmentType.CENTER,after:0}),widths[i],{fill:BLUE,border:'FFFFFF'}))});
    const neighborhoodTableDocx=()=>{const widths=[42,15,18,25];const rows=[genericHeader(['Bairro / Localidade','Unidades','Com coordenadas','Orçamento ref.'],widths)];for(const g of ctx.inspectionByNeighborhood){const located=g.units.filter(u=>validCoords(Number(u.lat),Number(u.lng))).length;rows.push(new TableRow({children:[cell(para(g.name,{bold:true,size:10,after:0}),widths[0]),cell(para(String(g.count),{align:AlignmentType.CENTER,size:10,after:0}),widths[1]),cell(para(String(located),{align:AlignmentType.CENTER,size:10,after:0}),widths[2]),cell(para(inspectionMoney(g.budget.total),{align:AlignmentType.CENTER,size:10,after:0}),widths[3])]}));}return new Table({width:{size:100,type:WidthType.PERCENTAGE},rows})};
    const budgetTableDocx=()=>{const widths=[31,11,15,17,17,9];const rows=[genericHeader(['Serviço','Código','Quantidade','Unitário','Subtotal','Obs.'],widths)];for(const x of ctx.budget.items)rows.push(new TableRow({children:[cell(para(x.label,{size:9,after:0}),widths[0]),cell(para(x.code||'—',{size:8,align:AlignmentType.CENTER,after:0}),widths[1]),cell(para(`${x.qty.toLocaleString('pt-BR',{maximumFractionDigits:2})} ${x.unit}`,{size:8,align:AlignmentType.CENTER,after:0}),widths[2]),cell(para(inspectionMoney(x.unitPrice),{size:8,align:AlignmentType.CENTER,after:0}),widths[3]),cell(para(inspectionMoney(x.subtotal),{bold:true,size:8,align:AlignmentType.CENTER,after:0}),widths[4]),cell(para(x.note?'*':'',{size:8,align:AlignmentType.CENTER,after:0}),widths[5])]}));rows.push(new TableRow({children:[new TableCell({columnSpan:4,width:{size:74,type:WidthType.PERCENTAGE},verticalAlign:VerticalAlign.CENTER,borders:borders(),margins:{top:80,bottom:80,left:90,right:90},children:[para('TOTAL REFERENCIAL',{bold:true,color:BLUE,align:AlignmentType.RIGHT,after:0})]}),cell(para(inspectionMoney(ctx.budget.total),{bold:true,color:BLUE,align:AlignmentType.CENTER,after:0}),17),cell(para('',{after:0}),9)]}));return new Table({width:{size:100,type:WidthType.PERCENTAGE},rows})};
    const unitRequirementsTable=(u)=>{const b=inspectionBudgetForUnits([u]),widths=[38,17,13,17,15];const rows=[genericHeader(['Serviço / dano','Quantidade','Un.','Unitário','Subtotal'],widths)];if(!b.items.length)rows.push(new TableRow({children:[spanCell(para('Sem quantitativos informados.',{size:10,after:0}),5)]}));for(const x of b.items)rows.push(new TableRow({children:[cell(para(x.label,{size:10,after:0}),widths[0]),cell(para(x.qty.toLocaleString('pt-BR',{maximumFractionDigits:2}),{size:10,align:AlignmentType.CENTER,after:0}),widths[1]),cell(para(x.unit||'—',{size:9,align:AlignmentType.CENTER,after:0}),widths[2]),cell(para(inspectionMoney(x.unitPrice),{size:9,align:AlignmentType.CENTER,after:0}),widths[3]),cell(para(inspectionMoney(x.subtotal),{bold:true,size:9,align:AlignmentType.CENTER,after:0}),widths[4])]}));rows.push(new TableRow({children:[new TableCell({columnSpan:4,verticalAlign:VerticalAlign.CENTER,borders:borders(),margins:{top:80,bottom:80,left:90,right:90},children:[para('Subtotal referencial da unidade',{bold:true,color:BLUE,align:AlignmentType.RIGHT,after:0})]}),cell(para(inspectionMoney(b.total),{bold:true,color:BLUE,align:AlignmentType.CENTER,after:0}),widths[4])]}));return new Table({width:{size:100,type:WidthType.PERCENTAGE},rows})};
    const intro=para([txt('Após avaliações de danos realizadas devido a ',{size:13}),txt(ctx.eventType,{bold:true,size:13}),txt(', ocorrido em ',{size:13}),txt(reportDatePt(ctx.eventDate),{bold:true,size:13}),txt(', foram verificados os seguintes danos em unidades habitacionais no âmbito de ',{size:13}),txt(ctx.neighborhood,{bold:true,size:13}),txt('. As fichas individuais a seguir integram fotografia, localização, quantitativos e estimativa referencial de cada unidade.',{size:13})],{after:90});
    const summaryChildren=[...brandHeader(),metaTable,para('DESCRIÇÃO INICIAL',{bold:true,color:BLUE,size:16,before:90,after:45}),intro,para('UNIDADES HABITACIONAIS - DANIFICADAS',{bold:true,color:BLUE,size:15,after:45}),damageTable(ctx.damagedQty,ctx.damagedDamage,ctx.damagedValue,ctx.damagedImpact),para('*Informar a quantidade de casas por bairro/distrito/localidade.',{italics:true,color:RED,size:10,after:55}),para('UNIDADES HABITACIONAIS - DESTRUÍDAS',{bold:true,color:BLUE,size:15,after:45}),damageTable(ctx.destroyedQty,ctx.destroyedDamage,ctx.destroyedValue,ctx.destroyedImpact),para('*Informar a quantidade de casas por bairro/distrito/localidade.',{italics:true,color:RED,size:10,after:55})];
    if(ctx.technicalNotes)summaryChildren.push(para('OBSERVAÇÕES TÉCNICAS',{bold:true,color:BLUE,size:14,after:30}),para(ctx.technicalNotes,{size:11,after:55}));
    summaryChildren.push(para(`ASSOCIAÇÃO FOTOGRÁFICA: ${ctx.matchedUnitPhotoCount} unidade(s) com foto associada automaticamente; ${ctx.unmatchedUnitPhotoCount} sem fotografia correspondente. O vínculo é feito por coordenadas, endereço e, quando necessário, ordem cronológica da rota.`,{color:GRAY,italics:true,size:10,after:30}));
    const sections=[{properties:PAGE,children:summaryChildren}];
    if((ctx.surveyUnits.length&&ctx.includeInspection)||(ctx.budget.items.length&&ctx.includeBudget)){
      const children=[...brandHeader(ctx.unified?'LAUDO TÉCNICO UNIFICADO':'QUANTITATIVOS E ORÇAMENTO','CONSOLIDAÇÃO TÉCNICA'),para(ctx.unified?'CONSOLIDADO DE TODOS OS BAIRROS':'QUANTITATIVOS E ORÇAMENTO REFERENCIAL',{bold:true,color:BLUE,size:20,after:75}),para(`Base analisada: ${ctx.surveyUnits.length} unidade(s) com necessidade registrada.`,{size:11,after:65})];
      if(ctx.unified&&ctx.inspectionByNeighborhood.length){children.push(para('CONSOLIDAÇÃO POR BAIRRO / LOCALIDADE',{bold:true,color:BLUE,size:14,after:35}),neighborhoodTableDocx(),para('',{after:55}));}
      if(ctx.includeBudget&&ctx.budget.items.length){children.push(para('ORÇAMENTO REFERENCIAL - MODELO ORÇAMENTÁRIO',{bold:true,color:BLUE,size:14,after:35}),budgetTableDocx(),para('Itens marcados com * usam referência correlata e exigem confirmação do escopo técnico. Os preços foram cruzados com o Modelo orçamento.xlsx.',{italics:true,color:GRAY,size:9,after:55}));const muro=ctx.budget.items.find(x=>x.key==='muro');if(muro)children.push(para(`MEMÓRIA DO MURO: ${muro.qty.toLocaleString('pt-BR',{maximumFractionDigits:2})} m linear × ${inspectionMoney(muro.unitPrice)}/m = ${inspectionMoney(muro.subtotal)}.`,{size:10,after:50}));}
      sections.push({properties:{type:SectionType.NEXT_PAGE,...PAGE},children});
    }
    if(ctx.includeInspection&&ctx.unitPhotoAssignments.length){
      const unitChildren=[];
      for(let i=0;i<ctx.unitPhotoAssignments.length;i++){
        if(i>0)unitChildren.push(new Paragraph({children:[new PageBreak()]}));
        const a=ctx.unitPhotoAssignments[i],u=a.unit;
        unitChildren.push(...brandHeader(`FICHA TÉCNICA - UNIDADE ${String(u.unitNumber||'').padStart(2,'0')}`,`${u.vehicle||''} • ${inspectionUnitNeighborhood(u)}`));
        unitChildren.push(new Table({width:{size:100,type:WidthType.PERCENTAGE},rows:[new TableRow({children:[labelCell('APUC / UNIDADE',`${u.vehicle||'—'} • ${String(u.unitNumber||'').padStart(2,'0')}`,35),labelCell('BAIRRO / LOCALIDADE',inspectionUnitNeighborhood(u)||'—',65)]}),new TableRow({children:[labelCell('ENDEREÇO',u.formattedAddress||u.address||'Não informado',65),labelCell('COORDENADAS',validCoords(Number(u.lat),Number(u.lng))?`${Number(u.lat).toFixed(6)}, ${Number(u.lng).toFixed(6)}`:'Não localizada',35)]})]}));
        unitChildren.push(para('REGISTRO FOTOGRÁFICO DA UNIDADE',{bold:true,color:BLUE,size:13,before:65,after:35}));
        if(a.photo?.blob){const img=await imageBlobToJpegAsset(a.photo.blob,1500,1100,.86);const maxW=520,maxH=285,sc=Math.min(maxW/img.width,maxH/img.height,1);unitChildren.push(new Paragraph({alignment:AlignmentType.CENTER,spacing:{after:35},children:[new ImageRun({data:img.bytes,transformation:{width:Math.round(img.width*sc),height:Math.round(img.height*sc)}})]}));unitChildren.push(para(`${reportPhotoCaption(a.photo,i)} • Associação: ${a.matchMethod}${Number.isFinite(a.distanceMeters)?` • distância ${Math.round(a.distanceMeters)} m`:''}`,{size:9,color:GRAY,align:AlignmentType.CENTER,after:55}));}
        else unitChildren.push(new Table({width:{size:100,type:WidthType.PERCENTAGE},rows:[new TableRow({children:[cell(para('FOTOGRAFIA NÃO LOCALIZADA PARA ESTA UNIDADE',{bold:true,color:RED,size:12,align:AlignmentType.CENTER,after:0}),100,{fill:'FFF7E6',border:YELLOW})]})]}));
        unitChildren.push(para('DANOS / QUANTITATIVOS E CUSTO REFERENCIAL',{bold:true,color:BLUE,size:13,after:35}),unitRequirementsTable(u));
        if((u.divergences||[]).length)unitChildren.push(para(`ATENÇÃO: ${(u.divergences||[]).length} divergência(s) entre quadro-resumo e ficha detalhada. Preservada a ficha detalhada como referência unitária; requer conferência técnica.`,{bold:true,color:RED,size:9,before:35,after:30}));
        unitChildren.push(para(`Fonte: ${u.sourceWorkbook||'planilha de vistoria'} • ${u.sourceSheet||''} • modo ${u.sourceMode||'não informado'}.`,{italics:true,color:GRAY,size:8,before:25,after:20}));
      }
      sections.push({properties:{type:SectionType.NEXT_PAGE,...PAGE},children:unitChildren});
    }
    if(ctx.incidents.length){const inc=[...brandHeader('SÍNTESE TÉCNICA','SINISTROS VINCULADOS'),para(ctx.neighborhood,{bold:true,color:BLUE,size:18,after:55}),...reportIncidentLines(ctx).map(x=>para('• '+x,{size:11,after:30}))];sections.push({properties:{type:SectionType.NEXT_PAGE,...PAGE},children:inc});}
    const [mateusSigBytes,rodrigoSigBytes]=await Promise.all([fetchBytes('assets/mateus_signature.png'),fetchBytes('assets/rodrigo_signature.png')]);
    const sign=(sigBytes,sigW,sigH,name,role,reg='')=>[
      new Paragraph({alignment:AlignmentType.CENTER,spacing:{before:80,after:0},children:[new ImageRun({data:sigBytes,transformation:{width:sigW,height:sigH}})]}),
      para('________________________________________',{color:GRAY,size:11,align:AlignmentType.CENTER,after:30}),
      para(name,{bold:true,size:12,align:AlignmentType.CENTER,after:14}),
      para(role,{bold:true,size:10,align:AlignmentType.CENTER,after:10}),
      reg?para(reg,{bold:true,size:10,align:AlignmentType.CENTER,after:70}):para('',{after:70})
    ];
    const signatures=[...brandHeader('ASSINATURAS','VALIDAÇÃO DO LAUDO'),para('APUCARANA, '+reportLongDate()+'.',{bold:true,size:12,align:AlignmentType.RIGHT,after:70}),...sign(mateusSigBytes,110,85,'MATEUS FRANCISCON FERNANDES','SECRETÁRIO MUNICIPAL DE OBRAS','CREA-PR - 144.447/D'),...sign(rodrigoSigBytes,165,80,'SARGENTO RODRIGO GERALDO LEME','COORDENADOR MUNICIPAL DE PROTEÇÃO E DEFESA CIVIL')];
    sections.push({properties:{type:SectionType.NEXT_PAGE,...PAGE},children:signatures});
    const doc=new Document({creator:'Prefeitura de Apucarana - APUC Rotas',title:`Laudo Técnico - ${ctx.neighborhood}`,description:'Laudo técnico A4 retrato com ficha fotográfica individual por unidade.',sections});
    const blob=await Packer.toBlob(doc);download(blob,`Laudo_Tecnico_${reportSafeName(ctx.neighborhood)}_${ctx.eventDate}.docx`);toast('Laudo Word A4 retrato gerado com fotos distribuídas por unidade.');
  }catch(e){console.error(e);alert('Não foi possível gerar o DOCX: '+e.message)}finally{setReportBusy(false)}
}


function pdfTextLines(pdf,text,maxW){return pdf.splitTextToSize(String(text||''),maxW)}
function pdfPageBrand(pdf,logo,title,subtitle,portrait=false){const w=pdf.internal.pageSize.getWidth();pdf.setFillColor(242,203,24);pdf.rect(0,0,w,2.7,'F');pdf.setFillColor(68,99,169);pdf.rect(0,2.7,w,6.3,'F');if(logo)pdf.addImage(logo,'PNG',11,13,29,26,undefined,'FAST');pdf.setTextColor(68,99,169);pdf.setFont('helvetica','bold');pdf.setFontSize(portrait?17:20);pdf.text(title,w-11,20,{align:'right'});pdf.setTextColor(25,25,25);pdf.setFontSize(9);pdf.text(subtitle,w-11,26,{align:'right'});pdf.setTextColor(90,100,112);pdf.setFont('helvetica','normal');pdf.setFontSize(6.8);pdf.text('PREFEITURA DE APUCARANA • GESTÃO DE CAMPO',w-11,31,{align:'right'});}
function pdfFooter(pdf){const w=pdf.internal.pageSize.getWidth(),h=pdf.internal.pageSize.getHeight();pdf.setDrawColor(68,99,169);pdf.setLineWidth(.25);pdf.line(12,h-10,w-12,h-10);pdf.setTextColor(68,99,169);pdf.setFontSize(6.5);pdf.setFont('helvetica','normal');pdf.text('PREFEITURA DE APUCARANA  |  Secretaria Municipal de Obras  |  Defesa Civil',w/2,h-5,{align:'center'});}
async function generateTechnicalReportPdf(){
  try{
    if(!window.jspdf?.jsPDF)throw new Error('Biblioteca de geração PDF não carregada. Verifique a conexão com a internet.');
    setReportBusy(true,'Montando laudo PDF A4 retrato…');
    const ctx=await collectReportContext();const {jsPDF}=window.jspdf;
    const pdf=new jsPDF({orientation:'portrait',unit:'mm',format:'a4',compress:true});
    const logo=await fetchDataUrl('assets/prefeitura-apucarana-vertical.png');const BLUE=[68,99,169],YELLOW=[242,203,24],LIGHT=[244,246,249],DARK=[25,25,25],GRAY=[100,110,120],RED=[154,27,27];
    const page=()=>({W:pdf.internal.pageSize.getWidth(),H:pdf.internal.pageSize.getHeight()});
    const brand=(title,subtitle)=>{pdfPageBrand(pdf,logo,title,subtitle,true);pdfFooter(pdf)};
    const addPage=(title,subtitle)=>{pdf.addPage('a4','portrait');brand(title,subtitle)};
    brand('LAUDO TÉCNICO','DANOS EM UNIDADES HABITACIONAIS');
    let {W,H}=page();let y=43;
    const cardW=(W-22-4)/2,cardH=16;const meta=[['BAIRRO / LOCALIDADE',ctx.neighborhood],['EVENTO / FIDE',ctx.eventType],['DATA DO EVENTO',reportDatePt(ctx.eventDate)],['REGISTROS',`${ctx.allPhotoCount} fotos • ${ctx.matchedUnitPhotoCount} associadas`]];
    meta.forEach((m,i)=>{const col=i%2,row=Math.floor(i/2),x=11+col*(cardW+4),yy=y+row*(cardH+3);pdf.setFillColor(...LIGHT);pdf.setDrawColor(215,221,232);pdf.rect(x,yy,cardW,cardH,'FD');pdf.setTextColor(...BLUE);pdf.setFont('helvetica','bold');pdf.setFontSize(6.2);pdf.text(m[0],x+2,yy+4);pdf.setTextColor(...DARK);pdf.setFontSize(7.5);pdf.text(pdfTextLines(pdf,m[1],cardW-4),x+2,yy+9)});y+=39;
    pdf.setTextColor(...BLUE);pdf.setFont('helvetica','bold');pdf.setFontSize(9);pdf.text('DESCRIÇÃO INICIAL',11,y);y+=5;pdf.setTextColor(...DARK);pdf.setFont('helvetica','normal');pdf.setFontSize(7.3);const intro=`Após avaliações de danos realizadas devido a ${ctx.eventType}, ocorrido em ${reportDatePt(ctx.eventDate)}, foram verificados danos em unidades habitacionais no âmbito de ${ctx.neighborhood}. As fichas individuais integram fotografia, localização, quantitativos e estimativa referencial de cada unidade.`;const introLines=pdfTextLines(pdf,intro,W-22);pdf.text(introLines,11,y);y+=introLines.length*3.6+4;
    const damageBlock=(title,qty,damage,value,impact)=>{pdf.setTextColor(...BLUE);pdf.setFont('helvetica','bold');pdf.setFontSize(8.2);pdf.text(title,11,y);y+=2;pdf.autoTable({startY:y,margin:{left:11,right:11},theme:'grid',styles:{fontSize:6.5,cellPadding:1.6,lineColor:[190,198,210],lineWidth:.15,textColor:DARK,valign:'top'},headStyles:{fillColor:BLUE,textColor:[255,255,255],fontStyle:'bold'},columnStyles:{0:{cellWidth:46,fontStyle:'bold'},1:{cellWidth:142}},head:[['Campo','Informação']],body:[['Quantidade',String(qty)],['Localidade / Bairro',ctx.neighborhood],['Danos nas edificações',damage||'—'],['Valor estimado','R$ '+fmtMoneyInput(value)],['Impacto aos moradores',impact||'—']]});y=pdf.lastAutoTable.finalY+5;};
    damageBlock('UNIDADES HABITACIONAIS - DANIFICADAS',ctx.damagedQty,ctx.damagedDamage,ctx.damagedValue,ctx.damagedImpact);
    damageBlock('UNIDADES HABITACIONAIS - DESTRUÍDAS',ctx.destroyedQty,ctx.destroyedDamage,ctx.destroyedValue,ctx.destroyedImpact);
    if(ctx.technicalNotes){if(y>238){addPage('SÍNTESE TÉCNICA','OBSERVAÇÕES DO LAUDO');y=46;}pdf.setTextColor(...BLUE);pdf.setFont('helvetica','bold');pdf.setFontSize(8);pdf.text('OBSERVAÇÕES TÉCNICAS',11,y);y+=4;pdf.setTextColor(...DARK);pdf.setFont('helvetica','normal');pdf.setFontSize(6.7);const notes=pdfTextLines(pdf,ctx.technicalNotes,W-22);pdf.text(notes,11,y);y+=notes.length*3.2+4;}
    if(y>252){addPage('SÍNTESE TÉCNICA','ASSOCIAÇÃO FOTOGRÁFICA');y=46;}pdf.setTextColor(...GRAY);pdf.setFont('helvetica','italic');pdf.setFontSize(6.5);pdf.text(pdfTextLines(pdf,`Associação fotográfica automática: ${ctx.matchedUnitPhotoCount} unidade(s) com foto associada; ${ctx.unmatchedUnitPhotoCount} sem fotografia correspondente. Critérios: coordenadas, endereço e ordem cronológica da rota.`,W-22),11,y);

    if((ctx.surveyUnits.length&&ctx.includeInspection)||(ctx.budget.items.length&&ctx.includeBudget)){
      addPage(ctx.unified?'LAUDO TÉCNICO UNIFICADO':'QUANTITATIVOS E ORÇAMENTO','CONSOLIDAÇÃO TÉCNICA');let iy=46;
      if(ctx.unified&&ctx.inspectionByNeighborhood.length){pdf.setTextColor(...BLUE);pdf.setFont('helvetica','bold');pdf.setFontSize(9);pdf.text('CONSOLIDAÇÃO POR BAIRRO / LOCALIDADE',11,iy);iy+=4;pdf.autoTable({startY:iy,margin:{left:11,right:11,top:44,bottom:15},theme:'grid',styles:{fontSize:6.4,cellPadding:1.6,lineColor:[198,205,216],lineWidth:.15},headStyles:{fillColor:BLUE,textColor:[255,255,255],fontStyle:'bold'},head:[['Bairro / Localidade','Unidades','Com coordenadas','Orçamento ref.']],body:ctx.inspectionByNeighborhood.map(g=>[g.name,String(g.count),String(g.units.filter(u=>validCoords(Number(u.lat),Number(u.lng))).length),inspectionMoney(g.budget.total)]),didDrawPage:()=>pdfFooter(pdf)});iy=pdf.lastAutoTable.finalY+7;}
      if(ctx.includeBudget&&ctx.budget.items.length){if(iy>225){addPage('ORÇAMENTO REFERENCIAL','MODELO ORÇAMENTÁRIO');iy=46;}pdf.setTextColor(...BLUE);pdf.setFont('helvetica','bold');pdf.setFontSize(9);pdf.text('ORÇAMENTO REFERENCIAL',11,iy);iy+=4;pdf.autoTable({startY:iy,margin:{left:11,right:11,top:44,bottom:15},theme:'grid',styles:{fontSize:5.8,cellPadding:1.35,lineColor:[198,205,216],lineWidth:.15},headStyles:{fillColor:BLUE,textColor:[255,255,255],fontStyle:'bold'},columnStyles:{0:{cellWidth:49},1:{cellWidth:28},2:{cellWidth:33},3:{cellWidth:33},4:{cellWidth:45}},head:[['Item','Quantidade','Unitário','Subtotal','Referência']],body:[...ctx.budget.items.map(x=>[x.label,`${x.qty.toLocaleString('pt-BR',{maximumFractionDigits:2})} ${x.unit}`,inspectionMoney(x.unitPrice),inspectionMoney(x.subtotal),x.note||x.code||'']),[{content:'TOTAL REFERENCIAL',colSpan:3,styles:{fontStyle:'bold',halign:'right'}},{content:inspectionMoney(ctx.budget.total),styles:{fontStyle:'bold'}},'']],didDrawPage:()=>pdfFooter(pdf)});iy=pdf.lastAutoTable.finalY+5;const muro=ctx.budget.items.find(x=>x.key==='muro');if(muro&&iy<270){pdf.setTextColor(...GRAY);pdf.setFont('helvetica','italic');pdf.setFontSize(6.2);pdf.text(pdfTextLines(pdf,`Memória do muro: ${muro.qty.toLocaleString('pt-BR',{maximumFractionDigits:2})} m × ${inspectionMoney(muro.unitPrice)}/m = ${inspectionMoney(muro.subtotal)}.`,W-22),11,iy);}}
    }

    if(ctx.includeInspection&&ctx.unitPhotoAssignments.length){
      for(let i=0;i<ctx.unitPhotoAssignments.length;i++){
        const a=ctx.unitPhotoAssignments[i],u=a.unit;addPage(`FICHA TÉCNICA - UNIDADE ${String(u.unitNumber||'').padStart(2,'0')}`,`${u.vehicle||''} • ${inspectionUnitNeighborhood(u)}`);({W,H}=page());
        pdf.autoTable({startY:45,margin:{left:11,right:11},theme:'grid',styles:{fontSize:6.6,cellPadding:1.5,lineColor:[205,211,220],lineWidth:.15},headStyles:{fillColor:BLUE,textColor:[255,255,255],fontStyle:'bold'},columnStyles:{0:{cellWidth:41,fontStyle:'bold'},1:{cellWidth:147}},head:[['Identificação','Informação']],body:[['APUC / Unidade',`${u.vehicle||'—'} • Unidade ${String(u.unitNumber||'').padStart(2,'0')}`],['Bairro / Localidade',inspectionUnitNeighborhood(u)||'—'],['Endereço',u.formattedAddress||u.address||'Não informado'],['Coordenadas',validCoords(Number(u.lat),Number(u.lng))?`${Number(u.lat).toFixed(6)}, ${Number(u.lng).toFixed(6)}`:'Não localizada']]});
        let py=pdf.lastAutoTable.finalY+5;pdf.setTextColor(...BLUE);pdf.setFont('helvetica','bold');pdf.setFontSize(8);pdf.text('REGISTRO FOTOGRÁFICO DA UNIDADE',11,py);py+=4;
        if(a.photo?.blob){const img=await imageBlobToJpegAsset(a.photo.blob,1600,1200,.84);const maxW=184,maxH=82,scale=Math.min(maxW/img.width,maxH/img.height);const iw=img.width*scale,ih=img.height*scale;const x=(W-iw)/2;pdf.setDrawColor(180,188,198);pdf.rect(x-1,py-1,iw+2,ih+2);pdf.addImage(img.dataUrl,'JPEG',x,py,iw,ih,undefined,'FAST');py+=ih+5;pdf.setTextColor(...GRAY);pdf.setFont('helvetica','italic');pdf.setFontSize(6);const cap=`${reportPhotoCaption(a.photo,i)} • Associação: ${a.matchMethod}${Number.isFinite(a.distanceMeters)?` • distância ${Math.round(a.distanceMeters)} m`:''}`;const cl=pdfTextLines(pdf,cap,W-24);pdf.text(cl,12,py);py+=cl.length*3+4;}
        else {pdf.setFillColor(255,247,230);pdf.setDrawColor(...YELLOW);pdf.rect(11,py,W-22,48,'FD');pdf.setTextColor(...RED);pdf.setFont('helvetica','bold');pdf.setFontSize(9);pdf.text('FOTOGRAFIA NÃO LOCALIZADA PARA ESTA UNIDADE',W/2,py+25,{align:'center'});py+=53;}
        pdf.setTextColor(...BLUE);pdf.setFont('helvetica','bold');pdf.setFontSize(8);pdf.text('DANOS / QUANTITATIVOS E CUSTO REFERENCIAL',11,py);py+=3;const ub=inspectionBudgetForUnits([u]);pdf.autoTable({startY:py,margin:{left:11,right:11,bottom:15},theme:'grid',styles:{fontSize:6,cellPadding:1.25,lineColor:[198,205,216],lineWidth:.15},headStyles:{fillColor:BLUE,textColor:[255,255,255],fontStyle:'bold'},head:[['Serviço / dano','Qtd.','Un.','Unitário','Subtotal']],body:[...(ub.items.length?ub.items.map(x=>[x.label,x.qty.toLocaleString('pt-BR',{maximumFractionDigits:2}),x.unit||'—',inspectionMoney(x.unitPrice),inspectionMoney(x.subtotal)]):[['Sem quantitativos informados','','','','']]),[{content:'SUBTOTAL REFERENCIAL DA UNIDADE',colSpan:4,styles:{fontStyle:'bold',halign:'right'}},{content:inspectionMoney(ub.total),styles:{fontStyle:'bold'}}]]});
        let ny=pdf.lastAutoTable.finalY+4;if((u.divergences||[]).length&&ny<277){pdf.setTextColor(...RED);pdf.setFont('helvetica','bold');pdf.setFontSize(6);const dl=pdfTextLines(pdf,`ATENÇÃO: ${(u.divergences||[]).length} divergência(s) entre quadro-resumo e ficha detalhada. Requer conferência técnica.`,W-22);pdf.text(dl,11,ny);ny+=dl.length*3+2;}if(ny<281){pdf.setTextColor(...GRAY);pdf.setFont('helvetica','italic');pdf.setFontSize(5.5);pdf.text(pdfTextLines(pdf,`Fonte: ${u.sourceWorkbook||'planilha de vistoria'} • ${u.sourceSheet||''} • modo ${u.sourceMode||'não informado'}.`,W-22),11,ny);}pdfFooter(pdf);
      }
    }

    if(ctx.incidents.length){addPage('SÍNTESE TÉCNICA','SINISTROS VINCULADOS');pdf.setTextColor(...BLUE);pdf.setFont('helvetica','bold');pdf.setFontSize(11);pdf.text(ctx.neighborhood,12,47);pdf.autoTable({startY:52,margin:{left:12,right:12,top:44,bottom:15},theme:'grid',styles:{fontSize:6.5,cellPadding:1.6,lineColor:[205,211,220],lineWidth:.15},headStyles:{fillColor:BLUE,textColor:[255,255,255],fontStyle:'bold'},head:[['Registro','Tipo','Endereço','Data','Descrição']],body:ctx.incidents.map(i=>[i.code||'',i.type||'',i.address||'',fmtDate(i.date),i.description||'']),didDrawPage:()=>pdfFooter(pdf)});}

    addPage('ASSINATURAS','VALIDAÇÃO DO LAUDO');({W,H}=page());pdf.setTextColor(...DARK);pdf.setFont('helvetica','bold');pdf.setFontSize(8);pdf.text('APUCARANA, '+reportLongDate()+'.',W-12,49,{align:'right'});
    const [mateusSig,rodrigoSig]=await Promise.all([fetchDataUrl('assets/mateus_signature.png'),fetchDataUrl('assets/rodrigo_signature.png')]);
    const sig=(yy,img,imgW,imgH,name,role,reg='')=>{pdf.addImage(img,'PNG',(W-imgW)/2,yy-imgH-2,imgW,imgH,undefined,'FAST');pdf.setDrawColor(110,110,110);pdf.line(34,yy,W-34,yy);pdf.setTextColor(...DARK);pdf.setFont('helvetica','bold');pdf.setFontSize(8);pdf.text(name,W/2,yy+7,{align:'center'});pdf.setFontSize(6.8);pdf.text(role,W/2,yy+12,{align:'center'});if(reg)pdf.text(reg,W/2,yy+17,{align:'center'});};
    sig(104,mateusSig,32,25,'MATEUS FRANCISCON FERNANDES','SECRETÁRIO MUNICIPAL DE OBRAS','CREA-PR - 144.447/D');sig(184,rodrigoSig,54,26,'SARGENTO RODRIGO GERALDO LEME','COORDENADOR MUNICIPAL DE PROTEÇÃO E DEFESA CIVIL');pdfFooter(pdf);
    pdf.save(`Laudo_Tecnico_${reportSafeName(ctx.neighborhood)}_${ctx.eventDate}.pdf`);toast('Laudo PDF A4 retrato gerado com uma ficha fotográfica por unidade.');
  }catch(e){console.error(e);alert('Não foi possível gerar o PDF: '+e.message)}finally{setReportBusy(false)}
}


function sheetText(v){return String(v??'').trim()}
function sheetNumber(v){if(typeof v==='number'&&Number.isFinite(v))return v;const m=String(v??'').replace(',','.').match(/-?\d+(?:\.\d+)?/);return m?Number(m[0]):0}
function vehicleFromSheetText(t=''){const m=String(t).match(/APUC\D*0?([1-8])\b/i);return m?`APUC-${String(m[1]).padStart(2,'0')}`:''}
function neighborhoodFromSheet(sheetName,rows){let raw='';for(const row of rows.slice(0,10)){for(const v of row.slice(0,4)){const s=sheetText(v);if(/GRUPO/i.test(s)&&s.includes('-')){raw=s.split('-').slice(1).join('-').trim();break}}if(raw)break}if(!raw&&String(sheetName).includes('-'))raw=String(sheetName).split('-').slice(1).join('-').replace(/CARRO\s*\d+/ig,'').trim();return raw.replace(/^SEOB\s*/i,'').replace(/^CARRO\s*\d+/i,'').trim()}
function emptyReq(){return Object.fromEntries(INSPECTION_REQ_KEYS.map(k=>[k,0]))}
function reqKeyForLabel(label,section=''){const n=String(label||'').normalize('NFD').replace(/[\u0300-\u036f]/g,'').toLowerCase().replace(/\s+/g,' ').trim();if(n==='ceramica'||n.includes('telha ceram'))return 'telha_ceramica';if(n==='fibrocimento'||n.includes('fibrocimento'))return 'telha_fibrocimento';if(n==='metalica'||n.includes('telha metal'))return 'telha_metalica';if(n==='muro'||n.startsWith('muro '))return 'muro';if(n.includes('grade')&&n.includes('port'))return 'grade_portao';if(n.includes('padrao de energia'))return 'padrao_energia';if(section==='vidros'&&n==='comum')return 'vidro_comum';if(section==='vidros'&&n==='temperado')return 'vidro_temperado';return ''}
function parseInspectionSheet(sheetName,rows,workbookName){
  const vehicle=vehicleFromSheetText(sheetName+' '+(rows.slice(0,6).flat().join(' ')));if(!vehicle||/FATOR|CÁLCULO|CALCULO/i.test(sheetName))return [];
  const nb=neighborhoodFromSheet(sheetName,rows);const summary=new Map();let idRow=-1,ids=[];
  for(let r=0;r<Math.min(rows.length,40);r++){const row=rows[r]||[];const idx=row.findIndex(v=>/^ID\.?$/i.test(sheetText(v)));if(idx>=0){idRow=r;ids=row.slice(idx+1).map(v=>Number(v)).filter(Number.isFinite);break}}
  if(idRow>=0&&ids.length){let section='';for(let r=idRow+1;r<Math.min(rows.length,idRow+30);r++){const row=rows[r]||[];const first=sheetText(row.find(v=>sheetText(v)!==''));if(/^Unidade\s*\d+/i.test(first))break;if(/^Vidros$/i.test(first)){section='vidros';continue}if(/^Cobertura$/i.test(first)){section='cobertura';continue}const key=reqKeyForLabel(first,section);if(!key)continue;for(let j=0;j<ids.length;j++){const id=ids[j];if(!summary.has(id))summary.set(id,emptyReq());const val=sheetNumber(row[j+1]);if(val)summary.get(id)[key]=val}}
  }
  const detailed=[];for(let r=0;r<rows.length;r++){const row=rows[r]||[];const first=sheetText(row.find(v=>sheetText(v)!==''));const um=first.match(/^Unidade\s*0?(\d+)/i);if(!um)continue;const unitNumber=Number(um[1]);const req=emptyReq();let address='',lat=null,lng=null,section='';let end=Math.min(rows.length,r+36);for(let rr=r+1;rr<end;rr++){const rrrow=rows[rr]||[];const non=rrrow.map(sheetText).filter(Boolean);if(non.some(x=>/^Unidade\s*0?\d+/i.test(x)))break;for(const x of non){if(/^Endere[cç]o\s*:/i.test(x))address=x.replace(/^Endere[cç]o\s*:\s*/i,'').replace(/^Endere[cç]o\s*:\s*/i,'').trim();if(/Coordenadas geogr[aá]ficas/i.test(x)){const c=parseCoordinatesFromText(x);if(c){lat=c.lat;lng=c.lng}}}const label=non[0]||'';if(/^Vidros$/i.test(label)){section='vidros';continue}if(/^Cobertura$/i.test(label)){section='cobertura';continue}const key=reqKeyForLabel(label,section);if(key){const nums=rrrow.slice(1).map(sheetNumber).filter(n=>n!==0);if(nums.length)req[key]=nums[0]}}
    const sreq=summary.get(unitNumber)||emptyReq();const divergences=[];for(const k of INSPECTION_REQ_KEYS){if(Math.abs(Number(req[k]||0)-Number(sreq[k]||0))>.0001&&((req[k]||0)!==0||(sreq[k]||0)!==0))divergences.push({item:k,detalhe:Number(req[k]||0),resumo:Number(sreq[k]||0)})}const affected=INSPECTION_REQ_KEYS.some(k=>Number(req[k]||sreq[k]||0)>0);detailed.push({id:`upload:${vehicle}:${normalizeNeighborhood(nb)||'sem-bairro'}:${unitNumber}`,vehicle,unitNumber,unitLabel:`Unidade ${String(unitNumber).padStart(2,'0')}`,sourceNeighborhood:nb,neighborhood:nb,address,lat,lng,formattedAddress:'',sourceWorkbook:workbookName,sourceSheet:sheetName,sourceMode:'detalhe',requirements:req,summaryRequirements:sreq,divergences,affected,hasCoordinates:validCoords(lat,lng),needsGeocoding:!!address&&!validCoords(lat,lng),updatedAt:new Date().toISOString()})}
  const have=new Set(detailed.map(x=>x.unitNumber));for(const [unitNumber,sreq] of summary.entries()){if(have.has(unitNumber))continue;const affected=INSPECTION_REQ_KEYS.some(k=>Number(sreq[k]||0)>0);detailed.push({id:`upload:${vehicle}:${normalizeNeighborhood(nb)||'sem-bairro'}:${unitNumber}`,vehicle,unitNumber,unitLabel:`Unidade ${String(unitNumber).padStart(2,'0')}`,sourceNeighborhood:nb,neighborhood:nb,address:'',lat:null,lng:null,formattedAddress:'',sourceWorkbook:workbookName,sourceSheet:sheetName,sourceMode:'resumo',requirements:{...sreq},summaryRequirements:{...sreq},divergences:[],affected,hasCoordinates:false,needsGeocoding:false,updatedAt:new Date().toISOString()})}
  return detailed;
}
function scoreInspectionUnit(u){let s=u.sourceMode==='detalhe'?20:0;if(u.address)s+=8;if(validCoords(Number(u.lat),Number(u.lng)))s+=10;s+=INSPECTION_REQ_KEYS.filter(k=>Number(u.requirements?.[k]||0)>0).length;return s}
function parseBudgetWorkbook(workbook){const codeMap={94210:'telha_fibrocimento',94201:'telha_ceramica',94216:'telha_metalica',102169:'vidro_comum',102181:'vidro_temperado',4948:'grade_portao',101946:'padrao_energia'};const updates={};for(const sn of workbook.SheetNames){const rows=XLSX.utils.sheet_to_json(workbook.Sheets[sn],{header:1,defval:null,raw:true});let unitCol=-1;for(const row of rows.slice(0,20)){const idx=row.findIndex(v=>/UNIT[AÁ]RIO/i.test(sheetText(v)));if(idx>=0){unitCol=idx;break}}if(unitCol<0)continue;for(const row of rows){for(let c=0;c<row.length;c++){const code=Number(row[c]);if(!codeMap[code])continue;const price=Number(row[unitCol]);if(Number.isFinite(price)&&price>0)updates[codeMap[code]]={unitPrice:price,source:`Planilha atualizada • ${sn}`,code:String(code)}}}}return updates}
async function loadCustomBudgetCatalog(){const raw=await getSetting('customBudgetCatalog','');if(!raw)return;try{const obj=typeof raw==='string'?JSON.parse(raw):raw;for(const [k,v] of Object.entries(obj||{}))if(window.APUC_BUDGET_CATALOG?.[k])Object.assign(window.APUC_BUDGET_CATALOG[k],v)}catch(e){console.warn('Catálogo orçamentário salvo inválido',e)}}
async function importInspectionSheets(files){
  const arr=[...(files||[])];if(!arr.length)return;if(!window.XLSX){alert('Módulo de planilhas não carregado.');return}const status=$('inspectionImportStatus');if(status)status.textContent='Lendo planilhas…';const parsed=[];let budgetUpdates={};const names=[];
  try{for(const file of arr){names.push(file.name);const wb=XLSX.read(await file.arrayBuffer(),{type:'array',cellDates:true});if(/or[cç]amento/i.test(file.name)){Object.assign(budgetUpdates,parseBudgetWorkbook(wb));continue}for(const sn of wb.SheetNames){const rows=XLSX.utils.sheet_to_json(wb.Sheets[sn],{header:1,defval:null,raw:true});parsed.push(...parseInspectionSheet(sn,rows,file.name))}}
    if(parsed.length){const best=new Map();for(const u of parsed){const key=`${u.vehicle}|${normalizeNeighborhood(u.neighborhood)}|${u.unitNumber}`;if(!best.has(key)||scoreInspectionUnit(u)>scoreInspectionUnit(best.get(key)))best.set(key,u)}const units=[...best.values()];if(!confirm(`Foram reconhecidas ${units.length} unidade(s) nas planilhas enviadas. Substituir a base atual de unidades por esta versão?`)){if(status)status.textContent='Importação cancelada.';return}cloudSyncSuspend++;try{await clearStore('surveyUnits');for(const u of units)await put('surveyUnits',u)}finally{cloudSyncSuspend--}surveyAddressLookupCache=null;markCloudDirty();}
    if(Object.keys(budgetUpdates).length){for(const [k,v] of Object.entries(budgetUpdates)){if(window.APUC_BUDGET_CATALOG?.[k])Object.assign(window.APUC_BUDGET_CATALOG[k],v)}await saveInternalSetting('customBudgetCatalog',JSON.stringify(budgetUpdates));markCloudDirty()}
    if(status)status.textContent=`Atualizado: ${names.join(', ')}${parsed.length?` • ${parsed.length} registros lidos`:''}${Object.keys(budgetUpdates).length?` • ${Object.keys(budgetUpdates).length} preços atualizados`:''}.`;toast('Planilhas atualizadas incorporadas ao cruzamento.');await render();setTimeout(fitMap,120);
  }catch(e){console.error(e);if(status)status.textContent='Falha na importação: '+e.message;alert('Não foi possível importar as planilhas: '+e.message)}finally{if($('inputInspectionSheets'))$('inputInspectionSheets').value=''}
}


function spatialProgress(percent,text){const p=Math.max(0,Math.min(100,Math.round(percent||0)));if($('spatialProgress'))$('spatialProgress').hidden=false;if($('spatialProgressPct'))$('spatialProgressPct').textContent=p+'%';if($('spatialProgressBar'))$('spatialProgressBar').style.width=p+'%';if($('spatialProgressText'))$('spatialProgressText').textContent=text||''}
async function collectSpatialCases(){
  const scope=$('spatialScope')?.value||'all',includePhotos=$('spatialIncludePhotos')?.checked!==false,includeInc=$('spatialIncludeIncidents')?.checked!==false;
  const [photos,incidents]=await Promise.all([getAll('photos'),getAll('incidents')]);let ps=photos.filter(p=>validCoords(Number(p.lat),Number(p.lng))),is=incidents.filter(i=>validCoords(Number(i.lat),Number(i.lng)));
  if(scope==='vehicle'){ps=ps.filter(p=>p.vehicle===selectedVehicle);is=is.filter(i=>i.vehicle===selectedVehicle)}else if(scope==='route'){ps=ps.filter(p=>p.routeId===selectedRouteId);is=is.filter(i=>i.routeId===selectedRouteId)}
  const cases=[];if(includePhotos)for(const p of ps)cases.push({id:p.id,kind:'photo',label:p.fileName||'Fotografia',vehicle:p.vehicle,routeId:p.routeId,lat:Number(p.lat),lng:Number(p.lng),address:p.mapInsetAddress||'',date:p.takenAt||p.createdAt,blob:p.blob||null});if(includeInc)for(const i of is)cases.push({id:i.id,kind:'incident',label:`${i.code||'Sinistro'} • ${i.type||''}`,vehicle:i.vehicle,routeId:i.routeId,lat:Number(i.lat),lng:Number(i.lng),address:i.address||'',date:i.date,blob:i.blob||null});return cases;
}
async function updateSpatialSummary(){const cases=await collectSpatialCases();const photos=cases.filter(x=>x.kind==='photo').length,inc=cases.filter(x=>x.kind==='incident').length;const scope=$('spatialScope')?.value||'all';const label=scope==='all'?'Todos os veículos':scope==='vehicle'?selectedVehicle:(selectedRouteId?'Rota selecionada':'Nenhuma rota selecionada');if($('spatialSummary'))$('spatialSummary').innerHTML=`<strong>${esc(label)}</strong><br>${cases.length} local(is) espacializado(s) • ${photos} fotografia(s) • ${inc} sinistro(s)<br><small>As unidades importadas das planilhas não fazem parte deste relatório.</small>`;return cases}
async function openSpatialReport(){await updateSpatialSummary();if($('spatialProgress'))$('spatialProgress').hidden=true;$('spatialDialog').showModal()}
function mercatorWorld(lat,lng,z){const size=256*Math.pow(2,z);const sin=Math.max(-.9999,Math.min(.9999,Math.sin(lat*Math.PI/180)));return{x:(lng+180)/360*size,y:(0.5-Math.log((1+sin)/(1-sin))/(4*Math.PI))*size,size}}
function fitStaticZoom(points,width,height,pad=80){if(points.length<=1)return 17;let minLat=90,maxLat=-90,minLng=180,maxLng=-180;for(const p of points){minLat=Math.min(minLat,p.lat);maxLat=Math.max(maxLat,p.lat);minLng=Math.min(minLng,p.lng);maxLng=Math.max(maxLng,p.lng)}for(let z=18;z>=9;z--){const a=mercatorWorld(maxLat,minLng,z),b=mercatorWorld(minLat,maxLng,z);if(Math.abs(b.x-a.x)<=width-pad*2&&Math.abs(b.y-a.y)<=height-pad*2)return z}return 9}
function loadCorsImage(url){return new Promise((resolve,reject)=>{const img=new Image();img.crossOrigin='anonymous';img.onload=()=>resolve(img);img.onerror=reject;img.src=url})}
async function renderStaticMapCanvas(points,{width=1200,height=800,satellite=true,showMarkers=true,zoom=null}={}){
  if(!points.length)throw new Error('Não há locais com coordenadas para gerar o mapa.');const z=zoom||fitStaticZoom(points,width,height);let cx=0,cy=0;for(const p of points){const w=mercatorWorld(p.lat,p.lng,z);cx+=w.x;cy+=w.y}cx/=points.length;cy/=points.length;
  const canvas=document.createElement('canvas');canvas.width=width;canvas.height=height;const ctx=canvas.getContext('2d');ctx.fillStyle=satellite?'#1b2730':'#eef2f5';ctx.fillRect(0,0,width,height);
  const left=cx-width/2,top=cy-height/2;const tx0=Math.floor(left/256),ty0=Math.floor(top/256),tx1=Math.floor((left+width)/256),ty1=Math.floor((top+height)/256);const n=Math.pow(2,z);const jobs=[];
  for(let ty=ty0;ty<=ty1;ty++)for(let tx=tx0;tx<=tx1;tx++){const xx=((tx%n)+n)%n,yy=ty;if(yy<0||yy>=n)continue;const url=satellite?`https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/${z}/${yy}/${xx}`:`https://tile.openstreetmap.org/${z}/${xx}/${yy}.png`;jobs.push((async()=>{try{const img=await loadCorsImage(url);ctx.drawImage(img,tx*256-left,ty*256-top,256,256)}catch{}})())}
  await Promise.all(jobs);if(!jobs.length){ctx.strokeStyle='rgba(255,255,255,.2)';for(let x=0;x<width;x+=100){ctx.beginPath();ctx.moveTo(x,0);ctx.lineTo(x,height);ctx.stroke()}for(let y=0;y<height;y+=100){ctx.beginPath();ctx.moveTo(0,y);ctx.lineTo(width,y);ctx.stroke()}}
  canvas._mapProject=(lat,lng)=>{const w=mercatorWorld(lat,lng,z);return{x:w.x-left,y:w.y-top}};canvas._zoom=z;
  if(showMarkers){for(let i=0;i<points.length;i++){const p=points[i],q=canvas._mapProject(p.lat,p.lng);ctx.beginPath();ctx.arc(q.x,q.y,p.kind==='incident'?12:9,0,Math.PI*2);ctx.fillStyle=p.kind==='incident'?'#f2cb18':'#4463a9';ctx.fill();ctx.lineWidth=3;ctx.strokeStyle='#fff';ctx.stroke();ctx.fillStyle='#111';ctx.font='700 13px Arial';ctx.fillText(String(i+1),q.x+14,q.y+4)}}
  ctx.fillStyle='rgba(255,255,255,.92)';ctx.fillRect(12,height-42,330,30);ctx.fillStyle='#1f2937';ctx.font='600 15px Arial';ctx.fillText(`APUC Rotas • ${points.length} local(is) • zoom ${z}`,22,height-22);return canvas;
}
function canvasDownload(canvas,name){canvas.toBlob(blob=>blob&&download(blob,name),'image/png',.95)}
async function generateSpatialGeneralPng(){try{const cases=await updateSpatialSummary();if(!cases.length)throw new Error('Nenhum local georreferenciado no escopo selecionado.');spatialProgress(15,'Carregando imagem de satélite…');const canvas=await renderStaticMapCanvas(cases,{satellite:true});spatialProgress(100,'Mapa geral gerado.');canvasDownload(canvas,`APUC_Rotas_Espacializacao_${new Date().toISOString().slice(0,10)}.png`)}catch(e){alert('Não foi possível gerar o mapa: '+e.message)}}
async function generateHeatmap(){
  try{const [photos,incidents]=await Promise.all([getAll('photos'),getAll('incidents')]);const cases=[...photos.filter(p=>validCoords(Number(p.lat),Number(p.lng))).map(p=>({kind:'photo',lat:Number(p.lat),lng:Number(p.lng)})),...incidents.filter(i=>validCoords(Number(i.lat),Number(i.lng))).map(i=>({kind:'incident',lat:Number(i.lat),lng:Number(i.lng)}))];if(!cases.length)throw new Error('Não há casos georreferenciados.');toast('Gerando mapa de calor…');const canvas=await renderStaticMapCanvas(cases,{width:1500,height:1050,satellite:true,showMarkers:false});const ctx=canvas.getContext('2d');ctx.save();ctx.globalCompositeOperation='screen';for(const p of cases){const q=canvas._mapProject(p.lat,p.lng),r=65;const g=ctx.createRadialGradient(q.x,q.y,0,q.x,q.y,r);g.addColorStop(0,'rgba(255,0,0,.78)');g.addColorStop(.35,'rgba(255,179,0,.55)');g.addColorStop(.7,'rgba(242,203,24,.28)');g.addColorStop(1,'rgba(255,255,0,0)');ctx.fillStyle=g;ctx.fillRect(q.x-r,q.y-r,r*2,r*2)}ctx.restore();ctx.fillStyle='rgba(255,255,255,.94)';ctx.fillRect(18,18,540,70);ctx.fillStyle='#4463a9';ctx.font='800 28px Arial';ctx.fillText('MAPA DE CALOR — APUC ROTAS',34,49);ctx.fillStyle='#20242b';ctx.font='600 16px Arial';ctx.fillText(`${cases.length} casos georreferenciados • base de satélite`,34,75);canvasDownload(canvas,`APUC_Rotas_Mapa_de_Calor_${new Date().toISOString().slice(0,10)}.png`);toast('Mapa de calor gerado.');
  }catch(e){alert('Não foi possível gerar o mapa de calor: '+e.message)}
}
async function generateSpatialPdf(){
  try{const cases=await updateSpatialSummary();if(!cases.length)throw new Error('Nenhum local georreferenciado no escopo selecionado.');const {jsPDF}=window.jspdf||{};if(!jsPDF)throw new Error('Módulo PDF não carregado.');spatialProgress(5,'Preparando mapa geral…');const pdf=new jsPDF({orientation:'landscape',unit:'mm',format:'a4'});const W=297,H=210;const addHeader=(title,subtitle='')=>{pdf.setFillColor(68,99,169);pdf.rect(0,0,W,28,'F');pdf.setFillColor(242,203,24);pdf.rect(0,28,W,5,'F');pdf.setTextColor(255,255,255);pdf.setFont('helvetica','bold');pdf.setFontSize(16);pdf.text(title,12,13);pdf.setFontSize(8);pdf.text(subtitle,12,21)};addHeader('RELATÓRIO DE ESPACIALIZAÇÃO','APUC ROTAS • Prefeitura de Apucarana');const general=await renderStaticMapCanvas(cases,{width:1500,height:960,satellite:true});pdf.addImage(general.toDataURL('image/jpeg',.9),'JPEG',12,40,273,150,undefined,'FAST');pdf.setTextColor(45,52,60);pdf.setFontSize(8);pdf.text(`${cases.length} locais georreferenciados. Unidades das planilhas não incluídas neste produto.`,12,198);if($('spatialIncludeIndividual')?.checked){for(let i=0;i<cases.length;i++){const c=cases[i];spatialProgress(10+Math.round((i/cases.length)*85),`Mapa individual ${i+1}/${cases.length}…`);pdf.addPage('a4','landscape');addHeader(`CASO ${String(i+1).padStart(3,'0')} — ${c.kind==='incident'?'SINISTRO':'FOTOGRAFIA'}`,`${c.vehicle||''} • ${c.label||''}`);const cv=await renderStaticMapCanvas([c],{width:1400,height:850,satellite:true,zoom:18});pdf.addImage(cv.toDataURL('image/jpeg',.9),'JPEG',12,40,185,112,undefined,'FAST');pdf.setTextColor(30,36,44);pdf.setFont('helvetica','bold');pdf.setFontSize(10);pdf.text(c.label||'Registro',207,48);pdf.setFont('helvetica','normal');pdf.setFontSize(8);const lines=[`Veículo: ${c.vehicle||'—'}`,`Data: ${fmtDate(c.date)}`,`Coordenadas: ${c.lat.toFixed(6)}, ${c.lng.toFixed(6)}`,`Endereço: ${c.address||'não informado'}`];pdf.text(lines,207,58,{maxWidth:78});if(c.blob){try{const img=await imageBlobToJpegAsset(c.blob,1000,750,.82);const scale=Math.min(76/img.width,54/img.height);pdf.addImage(img.dataUrl,'JPEG',207,92,img.width*scale,img.height*scale,undefined,'FAST')}catch{}}}}
  spatialProgress(100,'Relatório concluído.');pdf.save(`APUC_Rotas_Relatorio_Espacializacao_${new Date().toISOString().slice(0,10)}.pdf`);toast('Relatório de espacialização gerado.');
  }catch(e){console.error(e);alert('Não foi possível gerar o relatório de espacialização: '+e.message)}
}


function bindEvents(){
  $('btnNewRoute').onclick=openNewRoute;
  $('btnEditSelectedRoute').onclick=()=>selectedRouteId?editRoute(selectedRouteId):toast('Selecione uma rota.');
  $('btnNewIncident').onclick=openNewIncident;
  $('btnAnalyzePhotos').onclick=analyzeExistingPhotos;
  $('btnDeleteAllPhotos').onclick=deleteAllPhotosFromSelectedRoute;
  $('routeForm').addEventListener('submit',saveRoute);
  $('incidentForm').addEventListener('submit',saveIncident);
  $('photoUpload').onchange=e=>handlePhotoUpload(e.target.files);
  if($('inputInspectionSheets'))$('inputInspectionSheets').onchange=e=>e.target.files?.length&&importInspectionSheets(e.target.files);
  $('routeViewSelect').onchange=async e=>{selectedRouteId=e.target.value;await render();setTimeout(fitMap,80)};
  $('incidentVehicle').onchange=fillIncidentRoutes;
  $('incidentPhoto').onchange=e=>{tempIncidentPhoto=e.target.files?.[0]||null;$('incidentPhotoPreview').innerHTML=tempIncidentPhoto?`<img src="${URL.createObjectURL(tempIncidentPhoto)}" alt="Preview">`:''};
  $('btnFitMap').onclick=fitMap;
  $('btnStreet').onclick=()=>setBaseMap('street');
  $('btnSatellite').onclick=()=>setBaseMap('satellite');
  $('btnShowAll').onclick=()=>{showAllActivity=!showAllActivity;$('btnShowAll').textContent=showAllActivity?'FILTRAR ROTA':'VER TODOS';renderActivity()};
  $('photoClose').onclick=()=>{$('photoDialog').close();if(photoModalUrl){URL.revokeObjectURL(photoModalUrl);photoModalUrl=null}};
  if($('photoEditForm'))$('photoEditForm').addEventListener('submit',savePhotoEdit);
  if($('btnPhotoGeocodeAddress'))$('btnPhotoGeocodeAddress').onclick=geocodePhotoEditAddress;
  if($('btnStartPhotoDrag'))$('btnStartPhotoDrag').onclick=startPhotoPinDrag;
  $('btnExportJson').onclick=exportJson;
  $('inputImportJson').onchange=e=>e.target.files?.[0]&&importJson(e.target.files[0]);
  $('btnExportCsv').onclick=exportCsv;
  $('btnReset').onclick=resetAll;
  $('navReports').onclick=()=>{renderReportNeighborhoodOptions().then(()=>$('reportDialog').showModal())};
  $('btnOpenReport').onclick=()=>{renderReportNeighborhoodOptions().then(()=>$('reportDialog').showModal())};
  if($('btnSpatialReport'))$('btnSpatialReport').onclick=openSpatialReport;
  if($('navSpatial'))$('navSpatial').onclick=openSpatialReport;
  if($('btnHeatmap'))$('btnHeatmap').onclick=generateHeatmap;
  if($('spatialScope'))$('spatialScope').onchange=updateSpatialSummary;
  if($('spatialIncludePhotos'))$('spatialIncludePhotos').onchange=updateSpatialSummary;
  if($('spatialIncludeIncidents'))$('spatialIncludeIncidents').onchange=updateSpatialSummary;
  if($('btnSpatialGeneralPng'))$('btnSpatialGeneralPng').onclick=generateSpatialGeneralPng;
  if($('btnGenerateSpatialPdf'))$('btnGenerateSpatialPdf').onclick=generateSpatialPdf;
  $('btnLocateSurveyUnits').onclick=async()=>{await renderReportNeighborhoodOptions();if(!$('reportDialog').open)$('reportDialog').showModal();await locateSurveyUnits()};
  if($('btnLocateSurveyUnitsDialog'))$('btnLocateSurveyUnitsDialog').onclick=locateSurveyUnits;
  $('reportNeighborhood').onchange=loadReportDraftForNeighborhood;
  $('btnSaveReportDraft').onclick=saveReportDraft;
  $('btnGenerateDocx').onclick=generateTechnicalReportDocx;
  $('btnGeneratePdf').onclick=generateTechnicalReportPdf;
  $('navSettings').onclick=openSettings;
  $('settingsForm').addEventListener('submit',saveSettings);
  if($('btnDriveConnect'))$('btnDriveConnect').onclick=connectGoogleDrive;
  if($('btnDriveSync'))$('btnDriveSync').onclick=()=>syncToGoogleDrive({silent:false});
  if($('btnDriveRestore'))$('btnDriveRestore').onclick=restoreFromGoogleDrive;
  if($('btnDriveDisconnect'))$('btnDriveDisconnect').onclick=disconnectGoogleDrive;
  if($('googleDriveAutoSync'))$('googleDriveAutoSync').onchange=async e=>{cloudAutoSync=!!e.target.checked;await saveInternalSetting('googleDriveAutoSync',String(cloudAutoSync));if(cloudAutoSync&&cloudDirty&&driveTokenValid())syncToGoogleDrive({silent:true});};
  $('navRotas').onclick=()=>$('routesSection').scrollIntoView({behavior:'smooth'});
  $('navSinistros').onclick=()=>$('incidentsSection').scrollIntoView({behavior:'smooth'});
}

(async function(){
  try{db=await openDB();cloudSyncSuspend++;try{await seedSettings();await seedSurveyUnits();await loadCustomBudgetCatalog()}finally{cloudSyncSuspend--}fillVehicleSelects();initMap();bindEvents();await initDriveFromSettings();await render();updateDriveStatusUi();setTimeout(()=>map.invalidateSize(),100)}catch(e){console.error(e);document.body.innerHTML='<div style="padding:40px;font-family:sans-serif"><h2>Não foi possível iniciar o aplicativo.</h2><p>'+esc(e.message)+'</p></div>'}
})();
