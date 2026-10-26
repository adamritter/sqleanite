from pathlib import Path
import json,subprocess,time,hashlib
root=Path('/dev/shm/sqleanite-catalog-20261026');parent=json.loads((root/'docs/validation/sqlite-datetime-parent-20261026.json').read_text())
sqls=[x['sql'] for x in parent['inputs'][:276]]
code='''import SQLeanite.Parser
import SQLeanite.SQLite.Scalar
open SQLeanite
def run (sql : String) : Except String String := do
  let statements ← parse sql
  let some (.select query) := statements[0]? | throw "not SELECT"
  let values ← query.columns.toList.mapM (fun column => SQLite.Scalar.eval column.expr)
  pure (String.intercalate "|" (values.map toString))
def main : IO Unit := do
  let queries : List String := [
'''+',\n'.join(json.dumps(s,ensure_ascii=False) for s in sqls)+''']
  for query in queries do
    match run query with
    | .ok output => IO.println ("OK:" ++ output)
    | .error message => IO.println ("ERROR:" ++ message)
'''
Path('/tmp/DateTimeComponent.lean').write_text(code)
start=time.time();r=subprocess.run(['lake','env','lean','--run','/tmp/DateTimeComponent.lean'],cwd=root,capture_output=True,text=True)
Path('/tmp/sqleanite-datetime-component2.stdout').write_text(r.stdout);Path('/tmp/sqleanite-datetime-component2.stderr').write_text(r.stderr)
actual=r.stdout.splitlines();cases=[]
if r.returncode==0:
 assert len(actual)==len(sqls)
 for i,(sql,result) in enumerate(zip(sqls,actual)):
  expected='OK:'+parent['cases'][2*i]['sqlite']['stdout'].rstrip('\n')
  cases.append(dict(sql=sql,actual=result,expected=expected,matched=result==expected))
report=dict(evaluation='Component expression evaluation of fixed development inputs; not public or final-checkpoint coverage.',exit_code=r.returncode,seconds=time.time()-start,cases=cases,failures=sum(not c['matched'] for c in cases),stdout_sha256=hashlib.sha256(r.stdout.encode()).hexdigest())
Path('/tmp/sqleanite-datetime-component2.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='cases'}));print(json.dumps([c for c in cases if not c['matched']][:10]))
