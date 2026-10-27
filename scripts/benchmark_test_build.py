#!/usr/bin/env python3
"""Compare native test-driver build modes while retaining optimized library objects."""
import argparse
import hashlib
import json
from pathlib import Path
import shlex
import statistics
import subprocess
import time

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);p.add_argument('--repeats',type=int,default=2);a=p.parse_args()
 root=Path.cwd();folder=a.output.parent;folder.mkdir(parents=True,exist_ok=True)
 source=root/'.lake/build/ir/Tests.c';source_hash=sha(source);cli_hash=sha(root/'.lake/build/bin/sqleanite')
 trace=json.loads((root/'.lake/build/ir/Tests.c.o.export.trace').read_text());original=shlex.split(trace['log'][0]['message'].removeprefix('.> '))
 old_object=original[original.index('-o')+1];response=(root/'.lake/build/bin/sqleanite_tests.rsp').read_text();assert old_object in response
 records=[];expected=None
 # Alternate order to expose warm-cache/order effects instead of measuring
 # all reference builds first. The same generated source and library objects
 # are used in every variant; only the test-driver optimization flag changes.
 for repeat in range(a.repeats):
  for optimization in (['O3','O0'] if repeat%2==0 else ['O0','O3']):
   tag=f'{optimization}-{repeat}';obj=folder/(tag+'.o');binary=folder/(tag+'-tests');rsp=folder/(tag+'.rsp')
   cmd=list(original);cmd[cmd.index('-o')+1]=str(obj);cmd=[x for x in cmd if x not in ['-O0','-O1','-O2','-O3','-Os','-Oz']];cmd.append('-'+optimization)
   start=time.monotonic();compiled=subprocess.run(cmd,capture_output=True,text=True);build_time=time.monotonic()-start
   (folder/(tag+'-build.log')).write_text(compiled.stdout+compiled.stderr);assert compiled.returncode==0,compiled.stderr
   rsp.write_text(response.replace(old_object,str(obj)));start=time.monotonic()
   linked=subprocess.run([cmd[0],'-o',str(binary),'@'+str(rsp)],capture_output=True,text=True);link_time=time.monotonic()-start
   assert linked.returncode==0,linked.stderr
   start=time.monotonic()
   with (folder/(tag+'-run.log')).open('w') as log:run=subprocess.run([str(binary)],stdout=log,stderr=subprocess.STDOUT)
   run_time=time.monotonic()-start;output=(folder/(tag+'-run.log')).read_text();assert run.returncode==0,output[-2000:]
   observed=[line for line in output.splitlines() if line.startswith('ok - ') or line.endswith('SQLeanite tests passed')]
   assert observed and observed[-1].endswith('SQLeanite tests passed')
   if expected is None:expected=observed
   else:assert observed==expected,'test groups or output changed between variants'
   assert sha(source)==source_hash and sha(root/'.lake/build/bin/sqleanite')==cli_hash,'source or production executable changed'
   row={'optimization':optimization,'repeat':repeat,'compile_seconds':build_time,'link_seconds':link_time,'run_seconds':run_time,'returncode':run.returncode,'test_groups':len(observed)-1,'test_output_sha256':hashlib.sha256('\n'.join(observed).encode()).hexdigest(),'binary_sha256':sha(binary),'command':cmd}
   records.append(row);print(json.dumps({k:v for k,v in row.items() if k!='command'}),flush=True)
 summary={opt:{key:statistics.median(row[key] for row in records if row['optimization']==opt) for key in ['compile_seconds','link_seconds','run_seconds']} for opt in ['O3','O0']}
 report={'scope':'Paired native compilation and execution of the generated Lean test driver on this host. Lean elaboration and production-library optimization are unchanged; this is not an SQL performance benchmark.','source_sha256':source_hash,'production_executable_sha256':cli_hash,'records':records,'medians':summary,'compile_speedup':summary['O3']['compile_seconds']/summary['O0']['compile_seconds'],'run_ratio_O0_over_O3':summary['O0']['run_seconds']/summary['O3']['run_seconds']}
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(summary),flush=True)
if __name__=='__main__':main()
