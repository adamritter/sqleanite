from pathlib import Path
import argparse,hashlib,importlib.util,json,os,shutil,subprocess,tempfile,time
p=argparse.ArgumentParser(description='Static upstream SQLite date SQL extraction, not the full Tcl test suite.');p.add_argument('--source',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
root=Path(__file__).resolve().parents[1];spec=importlib.util.spec_from_file_location('helpers',root/'scripts/run-json-position-differential.py');helpers=importlib.util.module_from_spec(spec);spec.loader.exec_module(helpers)
source=helpers.digest();binary=root/'.lake/build/bin/sqleanite';exe=hashlib.sha256(binary.read_bytes()).hexdigest();sqlite=os.environ.get('SQLITE3_BIN','sqlite3')
inputs=[];excluded=[]
extraction=subprocess.check_output(['tclsh',str(root/'scripts/extract-sqlite-date.tcl'),str(a.source)],text=True)
for line in extraction.splitlines():
 fields=line.split('\t')
 if fields[0]=='case':inputs.append(dict(name=bytes.fromhex(fields[1]).decode(),sql=bytes.fromhex(fields[2]).decode()))
 else:excluded.append(dict(kind=fields[0],line=int(fields[1]),detail=bytes.fromhex(fields[2]).decode()))
def run(command,sql):
 try:
  r=subprocess.run(command,input=sql.encode(),capture_output=True,timeout=15);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 except subprocess.TimeoutExpired:return dict(code=124,stdout='',stderr='timeout')
def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
reference=csql(':memory:','SELECT sqlite_version(),sqlite_source_id();')
assert reference['stdout']=='3.53.4|2026-07-24 19:02:57 bf7c7f30031888f4e796e429ab3978879485813aaca6f641c7b33e4e09459bcc\n',reference
cases=[];start=time.time()
with tempfile.TemporaryDirectory(prefix='sqleanite-upstream-date-') as tmp:
 folder=Path(tmp);base=folder/'base.db';assert csql(base,'CREATE TABLE dummy(id INTEGER PRIMARY KEY);')['code']==0
 for i,entry in enumerate(inputs):
  for mode in ['--verified-file','--verified-wal-file']:
   left=folder/(str(i)+mode+'-lean.db');right=folder/(str(i)+mode+'-sqlite.db');shutil.copyfile(base,left);shutil.copyfile(base,right)
   l,c=run([str(binary),mode,str(left)],entry['sql']),csql(right,entry['sql'])
   observe='PRAGMA integrity_check;SELECT type,hex(name),hex(tbl_name),hex(sql) FROM sqlite_schema ORDER BY type,name;'
   lo,co=csql(left,observe),csql(right,observe)
   cases.append(dict(input=i,mode=mode,lean=l,sqlite=c,observation_lean=lo,observation_sqlite=co,matched=l['code']!=124 and c['code']!=124 and helpers.same(l,c) and lo==co))
assert source==helpers.digest() and exe==hashlib.sha256(binary.read_bytes()).hexdigest()
assert inputs, 'No standalone SQL extracted'
report=dict(sqlite_identity=reference['stdout'].strip(),evaluation='Static top-level datetest/do_execsql_test SQL extracted with a safe Tcl interpreter from pinned date.test; compared to live pinned C on an independent database. Original Tcl assertions, loops, mocked time and setup are not replayed. All unextracted commands and extraction errors are listed. Not the full upstream suite.',upstream_file='test/date.test',upstream_sha256=hashlib.sha256(a.source.read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),extractor_sha256=hashlib.sha256((root/'scripts/extract-sqlite-date.tcl').read_bytes()).hexdigest(),source_sha256=source,executable_sha256=exe,seconds=time.time()-start,inputs=inputs,unextracted=excluded,cases=cases,failures=sum(not c['matched'] for c in cases))
a.output.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(dict(cases=len(cases),failures=report['failures'],seconds=report['seconds'])))
for case in [c for c in cases if not c['matched'] and c['mode']=='--verified-file']:
 print(json.dumps(dict(name=inputs[case['input']]['name'],sql=inputs[case['input']]['sql'],lean=case['lean'],sqlite=case['sqlite'])))

raise SystemExit(bool(report["failures"] or not cases))
