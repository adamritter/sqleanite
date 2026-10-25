#!/usr/bin/env python3
"""Reproduce saved read-only join failures on their original C-created fixtures.

This is a regression replay, not a fresh evaluation. Re-run both executables;
do not treat saved output as the current oracle. Check complete output/error
status and unchanged main/WAL bytes, plus pinned-C integrity checks. The
--compare-error-output option also compares rows emitted before an error.
"""
import argparse,hashlib,json,os,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path);p.add_argument('--output',type=Path,required=True);p.add_argument('--compare-error-output',action='store_true');a=p.parse_args()
 original=json.loads(a.input.read_text());sqlite=os.environ.get('SQLITE3_BIN','sqlite3');binary=ROOT/'.lake/build/bin/sqleanite';cases=[]
 def run(args,sql):
  r=subprocess.run(args,input=sql.encode(),capture_output=True,timeout=120)
  return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 def snapshot(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['', '-wal'] if Path(str(path)+s).exists()}
 with tempfile.TemporaryDirectory(prefix='sqleanite-saved-join-') as tmp:
  for old in original['cases']:
   if old['matched']:continue
   folder=Path(tmp)/str(len(cases));folder.mkdir();left=folder/'lean.db';right=folder/'sqlite.db'
   fixture=(next(f for f in original['fixtures'] if f['fixture']==old['fixture'] and f['mode']==old['mode'])
    if isinstance(original['fixtures'],list) else dict(setup=old['schema_sql']))
   prepared=csql(right,fixture['setup']);assert prepared['code']==0,prepared;shutil.copyfile(right,left)
   bl=snapshot(left);br=snapshot(right);l=run([str(binary),old['mode'],str(left)],old['sql']);r=csql(right,old['sql'])
   unchanged=bl==snapshot(left) and br==snapshot(right);li=csql(left,'PRAGMA integrity_check;');ri=csql(right,'PRAGMA integrity_check;')
   matched=((l['code']==r['code']==0 and l['stdout']==r['stdout']) or(l['code']>0 and r['code']>0)) and unchanged and li['code']==ri['code']==0 and li['stdout']==ri['stdout']=='ok\n'
   if a.compare_error_output:matched &= l['stdout']==r['stdout']
   cases.append(dict(fixture=old['fixture'],mode=old['mode'],setup=fixture['setup'],sql=old['sql'],lean=l,sqlite=r,unchanged=unchanged,integrity_lean=li,integrity_sqlite=ri,matched=matched))
 h=hashlib.sha256()
 for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:h.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
 report=dict(evaluation='regression replay of saved failures',compare_error_output=a.compare_error_output,input_file=str(a.input),input_sha256=hashlib.sha256(a.input.read_bytes()).hexdigest(),cases=cases,failures=sum(not c['matched'] for c in cases),implementation_sha256=h.hexdigest(),executable_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip())
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=report['failures'])));return bool(report['failures'])
if __name__=='__main__':raise SystemExit(main())
