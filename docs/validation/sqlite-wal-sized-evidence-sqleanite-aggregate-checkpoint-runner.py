import argparse,concurrent.futures,hashlib,json,subprocess,time
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('plan',type=Path);a=p.parse_args();plan=json.loads(a.plan.read_text());root=Path.cwd();logs=Path('/dev/shm/sqleanite-tools-20261024/logs')
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def digest():
 h=hashlib.sha256()
 for f in sorted((root/'SQLeanite').rglob('*.lean'))+[root/'Main.lean']:h.update(str(f.relative_to(root)).encode()+b'\0'+f.read_bytes())
 return h.hexdigest()
source=digest();executable=sha(root/'.lake/build/bin/sqleanite');native=sha(root/'native/sqleanite_vfs.c')
def run(job):
 name=job['name'];cmd=job['argv'];log=logs/(plan['prefix']+'-'+name+'.log');before=digest();start=time.time()
 with log.open('w') as f:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
 after=digest();receipt=dict(name=name,argv=cmd,exit_code=r.returncode,seconds=time.time()-start,
  before_source_sha256=before,after_source_sha256=after,executable_sha256=sha(root/'.lake/build/bin/sqleanite'),log=str(log),log_sha256=sha(log))
 if '--output' in cmd:
  report=Path(cmd[cmd.index('--output')+1])
  if report.exists():
   d=json.loads(report.read_text());receipt.update(cases=(len(d['cases']) if isinstance(d['cases'],list) else d['cases']) if 'cases' in d else d.get('queries',sum(p['queries'] for p in d.get('phases',[]))),failures=d['failures'] if isinstance(d['failures'],int) else len(d['failures']),report_sha256=sha(report))
 if len(cmd)>1 and Path(cmd[1]).is_file():receipt['harness_sha256']=sha(Path(cmd[1]))
 assert before==source==after and sha(root/'.lake/build/bin/sqleanite')==executable and sha(root/'native/sqleanite_vfs.c')==native,'Source/executable changed during evaluation'
 print(json.dumps(receipt),flush=True);return receipt
with concurrent.futures.ThreadPoolExecutor(max_workers=plan.get('workers',1)) as pool:records=list(pool.map(run,plan['jobs']))
for job in plan.get('checks',[]):records.append(run(job))
out=dict(evaluation=plan.get('evaluation',''),source_sha256=source,executable_sha256=executable,native_sha256=native,receipts=records)
Path(plan['output']).write_text(json.dumps(out,indent=2)+'\n')
raise SystemExit(any(r['exit_code'] for r in records))
