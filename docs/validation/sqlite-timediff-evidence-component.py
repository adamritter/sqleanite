from pathlib import Path
import json,random,subprocess,time,hashlib,sys
root=Path('/dev/shm/sqleanite-catalog-20261026');seed=int(sys.argv[1]);tag=sys.argv[2];rng=random.Random(seed)
fixed=['2023-02-15','2023-03-15','2023-04-15','2024-01-31','2024-02-29','2023-02-31','0000-01-01','-0001-12-31','-4713-11-24 12:00:00','9999-12-31 23:59:59.999','2000-01-01 24:05','2001-02-03 04:05:06.789+01:30',2451544.5,0,5373484.49999,None,'invalid']
pairs=[(a,b) for a in fixed for b in fixed]
def stamp():
 y=rng.randrange(-4712,10000);year=('-'+str(-y).zfill(4)) if y<0 else str(y).zfill(4)
 return year+'-%02d-%02d %02d:%02d:%02d.%03d'%(rng.randrange(1,13),rng.randrange(1,32),rng.randrange(25),rng.randrange(60),rng.randrange(60),rng.randrange(1000))
pairs.extend((stamp(),stamp()) for _ in range(512))
def sqlvalue(x):return 'NULL' if x is None else "'"+x.replace("'","''")+"'" if isinstance(x,str) else str(x)
def leanvalue(x):return 'Value.null' if x is None else '(Value.text '+json.dumps(x,ensure_ascii=False)+')' if isinstance(x,str) else '(Value.real '+str(x)+')' if isinstance(x,float) else '(Value.integer '+str(x)+')'
sqls=[]
for a,b in pairs:
 a,b=sqlvalue(a),sqlvalue(b);d='timediff('+a+','+b+')';sqls.append("SELECT 'OK:'||ifnull("+d+",''),datetime("+b+','+d+'),datetime('+a+');')
c=subprocess.run(['sqlite3','-batch','-bail',':memory:'],input='\n'.join(sqls),text=True,capture_output=True);assert c.returncode==0,c.stderr
expected=c.stdout.splitlines();assert len(expected)==len(pairs)
code='''import SQLeanite.SQLite.DateDifference
open SQLeanite
def main : IO Unit := do
  let pairs : List (Value × Value) := [
'''+',\n'.join('('+leanvalue(a)+', '+leanvalue(b)+')' for a,b in pairs)+''']
  for (left, right) in pairs do
    match SQLite.DateDifference.evaluate left right with
    | .error message => IO.println ("ERROR:" ++ message)
    | .ok delta =>
        IO.println ("OK:" ++ toString delta ++ "|" ++
          toString (SQLite.DateTime.render "datetime" [right, delta]) ++ "|" ++
          toString (SQLite.DateTime.render "datetime" [left]))
'''
path=Path('/tmp/TimeDifferenceComponent.lean');path.write_text(code)
start=time.time();r=subprocess.run(['lake','env','lean','--run',str(path)],cwd=root,capture_output=True,text=True)
Path('/tmp/sqleanite-timediff-'+tag+'.stdout').write_text(r.stdout);Path('/tmp/sqleanite-timediff-'+tag+'.stderr').write_text(r.stderr)
cases=[]
if r.returncode==0:
 actual=r.stdout.splitlines();assert len(actual)==len(pairs),(len(actual),len(pairs),r.stdout[:500])
 for pair,sql,want,got in zip(pairs,sqls,expected,actual):cases.append(dict(pair=pair,sql=sql,expected=want,actual=got,matched=want==got))
report=dict(seed=seed,evaluation='Component timediff and independent modifier round trip; fixed edge pairs plus seeded dates. Not final public coverage.',exit_code=r.returncode,seconds=time.time()-start,cases=cases,failures=sum(not c['matched'] for c in cases),component_source_sha256=hashlib.sha256(code.encode()).hexdigest(),implementation_sha256=hashlib.sha256((root/'SQLeanite/SQLite/DateDifference.lean').read_bytes()).hexdigest())
Path('/tmp/sqleanite-timediff-'+tag+'.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='cases'}));print(json.dumps([c for c in cases if not c['matched']][:8]))
