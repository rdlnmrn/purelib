#!/usr/bin/env python3
"""Durable private Core epoch: exact ledger, observed contexts, incremental receipts.
No original-source baseline reruns; no installed or project artifact writes.
"""
from pathlib import Path
import argparse,json,hashlib,os,subprocess,time,concurrent.futures,fcntl,threading,signal
EXT=['.olean','.olean.server','.olean.private','.ir'];SIX=EXT+['.ilean','.c']
HASH_CACHE={}
def sha(p):
 p=Path(p);st=p.stat();key=(st.st_dev,st.st_ino,st.st_size,st.st_mtime_ns,st.st_ctime_ns)
 if str(p) in HASH_CACHE and HASH_CACHE[str(p)][0]==key:return HASH_CACHE[str(p)][1]
 with p.open('rb') as f:h=hashlib.file_digest(f,'sha256').hexdigest()
 assert key==(lambda q:(q.st_dev,q.st_ino,q.st_size,q.st_mtime_ns,q.st_ctime_ns))(p.stat())
 HASH_CACHE[str(p)]=(key,h);return h
def bind(p):return {'path':str(p),'sha256':sha(p)}
def check(v):assert sha(v['path'])==v['sha256'],v['path'];return Path(v['path'])
def read(p):return json.loads(Path(p).read_text())
def enc(v):return json.dumps(v,sort_keys=True,separators=(',',':')).encode()
def digest(v):return hashlib.sha256(enc(v)).hexdigest()
def put(p,v):p.parent.mkdir(parents=True,exist_ok=True);q=Path(str(p)+'.partial');q.write_bytes(enc(v)+b'\n');q.replace(p)
def owned(pg):
 total=0
 for p in Path('/proc').iterdir():
  if not p.name.isdigit():continue
  try:
   if os.getpgid(int(p.name))==pg:total+=next((int(x.split()[1]) for x in (p/'status').read_text().splitlines() if x.startswith('VmRSS:')),0)
  except (FileNotFoundError,ProcessLookupError,PermissionError):pass
 return total
ap=argparse.ArgumentParser();ap.add_argument('--request',required=True);ap.add_argument('--out',required=True);ap.add_argument('--jobs',type=int,default=4);args=ap.parse_args();assert 1<=args.jobs<=4;request=read(args.request);assert request['root_private_compilation_authorized'] is True
out=Path(args.out).resolve();assert '/.lake/' in str(out);out.mkdir(parents=True,exist_ok=True);pins=[bind(__file__),bind(args.request),request['host'],request['recovery'],request['contexts'],request['full_import_graph']]+request.get('inputs',[])
for v in pins:check(v)
recovery=read(request['recovery']['path']);contexts=read(request['contexts']['path']);ctx={r['module']:r for r in contexts['rows']};ctx.update({r['module']:r for r in request.get('extra_contexts',[])})
ledger={};
for r in recovery['rows']:ledger.setdefault(r['module'],{})[r['part']]=r['immutable']
for r in request.get('extra_parts',[]):ledger.setdefault(r['module'],{})[r['part']]=r['immutable']
source={r['module']:r['immutable'] for r in recovery['original_sources']};source.update(request.get('candidate_sources',{}));order=request['topological_order'];assert order and len(order)==len(set(order));assert set(order)<=ctx.keys();graph={m:set(v) for m,v in read(request['full_import_graph']['path']).items()};resolver=out/'resolver';resolver.mkdir(exist_ok=True)
lock=out/'WRITER.lock';lf=lock.open('a+b');fcntl.flock(lf,fcntl.LOCK_EX|fcntl.LOCK_NB)
def install(m,ps):
 for e in EXT:
  v=ps[e];check(v);p=resolver/Path(m.replace('.','/')+e);p.parent.mkdir(parents=True,exist_ok=True)
  if p.is_symlink():p.unlink()
  else:assert not p.exists(),p
  p.symlink_to(v['path'])
for m,ps in ledger.items():assert set(ps)==set(EXT);install(m,ps)
pending=set(order);running={};done={};results=[];start=time.monotonic();wholepeak=0;active_pgids=set();pgid_lock=threading.Lock()

stop_event=threading.Event()
def interrupted(signum,frame):stop_event.set()
signal.signal(signal.SIGTERM,interrupted);signal.signal(signal.SIGINT,interrupted)
def process_identity(pid):
 try:
  z=Path('/proc')/str(pid);st=(z/'stat').read_text().rsplit(')',1)[1].split()
  return {'pid':pid,'start_ticks':st[19],'namespace':os.stat('/proc/self/ns/pid').st_ino,'pgid':os.getpgid(pid)}
 except (FileNotFoundError,ProcessLookupError):return None
def check_previous_group(marker, job):
 if marker['namespace']!=os.stat('/proc/self/ns/pid').st_ino:
  raise RuntimeError('Cannot rule out worker in another process namespace: '+str(job))
 members=[]
 for entry in Path('/proc').iterdir():
  if not entry.name.isdigit():continue
  try:
   if os.getpgid(int(entry.name))==marker['pgid']:
    members.append(process_identity(int(entry.name)))
  except (FileNotFoundError,ProcessLookupError):pass
 if members:raise RuntimeError('Previous owned process-group members are still alive: '+str(job)+' '+str(members))
closure_cache={}
def closure(m):
 if m in closure_cache:return closure_cache[m]
 seen=set();q=list(graph.get(m,[]))
 while q:
  n=q.pop()
  if n in seen:continue
  seen.add(n);q.extend(graph.get(n,[]))
 assert seen<=ledger.keys(),(m,seen-ledger.keys());closure_cache[m]=seen;return seen

def emit(m):
 if stop_event.is_set():raise RuntimeError('Supervisor interrupted; no further jobs launched')
 deps=closure(m);ps={n:dict(ledger[n]) for n in deps};inputs=[{'module':n,'part':e,**ps[n][e]} for n in sorted(ps) for e in EXT];s=source[m];check(s);c=ctx[m];setup={'name':m,'package':c['package'],'isModule':c['isModule'],'imports':None,'importArts':{n:[ps[n][e]['path'] for e in ['.olean','.ir','.olean.server','.olean.private']] for n in sorted(ps)},'options':{},'dynlibs':[],'plugins':[]};key={'source':s,'module':m,'host':request['host'],'setup':setup,'all_import_parts':inputs,'context':c};job=out/'jobs'/Path(m.replace('.','/'))/digest(key);rp=job/'COMPILE.json'
 if (job/'STATE.json').exists():
  previous=read(job/'STATE.json')
  if previous.get('worker'):check_previous_group(previous['worker'],job)
 if rp.exists():
  r=read(rp);assert r['key']==key
  if r['exit_code']==0:
   for v in r['parts'].values():check(v)
   print('REUSE',m,flush=True);return m,bind(rp),r
  if not (job/'STATE.json').exists() or read(job/'STATE.json')['status']!='STOPPED':
   raise RuntimeError('Preserved prior semantic failure; revise inputs before retry: '+str(rp))
 state=job/'STATE.json'
 if job.exists():
  if not state.exists():raise RuntimeError('Unrecorded pending directory requires owned-process review: '+str(job))
  old=read(state);assert old['key']==key
  if old.get('worker'):check_previous_group(old['worker'],job)
  job.rename(Path(str(job)+'.interrupted.'+str(time.time_ns())))
 job.mkdir(parents=True,exist_ok=False)
 put(state,{'key':key,'status':'PREPARING','supervisor':process_identity(os.getpid()),'worker':None})
 src=check(s) if request.get('source_in_place',False) else job/'source'/Path(m.replace('.','/')+'.lean')
 if not request.get('source_in_place',False):
  src.parent.mkdir(parents=True);src.write_bytes(check(s).read_bytes())
 sp=job/'setup.json';put(sp,setup)
 base=job/'parts'/Path(m.replace('.','/'));base.parent.mkdir(parents=True)
 for v in inputs:check(v)
 cmd=[request['host']['path'],'-R',str(job/'source'),'--setup',str(sp),'-DwarningAsError=true',str(src),'-o',str(base)+'.olean','-i',str(base)+'.ilean','-c',str(base)+'.c'];env=os.environ.copy();env.update(LEAN_PATH=str(resolver),LEAN_NUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1');begin=time.monotonic();peak=0;log=job/'compile.log'
 with log.open('xb') as f:
  proc=subprocess.Popen(['/usr/bin/time','-v','-o',str(job/'compile.time'),*cmd],stdout=f,stderr=subprocess.STDOUT,env=env,start_new_session=True)
  identity=process_identity(proc.pid);assert identity and identity['pgid']==proc.pid
  put(state,{'key':key,'status':'RUNNING','supervisor':process_identity(os.getpid()),'worker':identity})
  with pgid_lock:active_pgids.add(proc.pid)
  stopped=False
  while proc.poll() is None:
   peak=max(peak,owned(proc.pid))
   if stop_event.is_set() and not stopped:
    live=process_identity(proc.pid)
    if live and live['start_ticks']==identity['start_ticks'] and live['pgid']==proc.pid:os.killpg(proc.pid,signal.SIGTERM)
    stopped=True
   time.sleep(.15)
  with pgid_lock:active_pgids.discard(proc.pid)
  code=proc.wait()
 put(state,{'key':key,'status':'STOPPED' if stop_event.is_set() else 'TERMINAL','supervisor':process_identity(os.getpid()),'worker':identity,'exit_code':code})
 for v in inputs:check(v)
 r={'status':'PASS_PRIVATE_COMPLETE_EMISSION_PENDING_DOWNSTREAM_KERNEL_AUDIT' if code==0 else 'FAIL_PRIVATE_EMISSION','key':key,'source':bind(src),'setup':bind(sp),'parts':{e:bind(Path(str(base)+e)) for e in SIX} if code==0 else {},'command':cmd,'exit_code':code,'seconds':time.monotonic()-begin,'whole_owned_PGID_peak_rss_kib':peak,'log':bind(log),'time':bind(job/'compile.time'),'live_handles':[]};put(rp,r);print('EMITTED',m,code,round(r['seconds'],2),peak,flush=True)
 if code:raise RuntimeError(str(rp))
 if r['seconds']>60:raise RuntimeError('Diagnose completed >60s module before scheduling more: '+str(rp))
 return m,bind(rp),r
try:
 with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
  while pending or running:
   ready=[m for m in order if m in pending and not (closure(m)&(pending|set(running.values()))) ]
   for m in ([] if stop_event.is_set() else ready[:args.jobs-len(running)]):pending.remove(m);running[pool.submit(emit,m)]=m
   assert running,('cyclic/pending graph',pending)
   completed,_=concurrent.futures.wait(running,timeout=.15,return_when=concurrent.futures.FIRST_COMPLETED)
   for fut in completed:
    m,rp,r=fut.result();running.pop(fut);done[m]=rp;ledger[m]={e:r['parts'][e] for e in EXT};install(m,ledger[m]);results.append({'module':m,'receipt':rp,'source':r['source'],'setup':r['setup'],'parts':r['parts']})
   with pgid_lock:pgids=list(active_pgids)
   wholepeak=max(wholepeak,sum(owned(pid) for pid in pgids))
 for v in pins:check(v)
 put(out/'EPOCH.json',{'status':'PASS_COMPLETE_COHERENT_PRIVATE_CORE_EMISSIONS_PENDING_FINAL_ROOT_ACCEPTANCE','request':bind(args.request),'rows':[{'module':m,'part':e,'immutable':z} for m,ps in sorted(ledger.items()) for e,z in ps.items()],'compiled_rows':results,'seconds':time.monotonic()-start,'measured_aggregate_owned_worker_rss_kib':wholepeak,'measured_max_whole_worker_rss_kib':max(read(r['receipt']['path'])['whole_owned_PGID_peak_rss_kib'] for r in results),'live_handles':[]});print('EPOCH_PASS',len(results),bind(out/'EPOCH.json'),flush=True)
finally:stop_event.set();lf.close()
