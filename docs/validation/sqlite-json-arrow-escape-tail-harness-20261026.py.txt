#!/usr/bin/env python3
"""Public fixed and seeded JSON escape-tail regression with complete raw values.

Malformed E2 escapes, valid line continuations, ordinary unknown escapes and
escaped object-key comparisons are all evaluated without outcome filtering.
Each input independently exercises ->>, jsonb_extract, json_type,
json_array_length, json_valid(...,8), and json_error_position. Exact output,
status and first diagnostics are compared, and file bytes must stay unchanged.
"""
import argparse, concurrent.futures, hashlib, importlib.util, json, os, random, shutil, subprocess, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('position_corpus', ROOT / 'scripts/run-json-position-differential.py')
helpers = importlib.util.module_from_spec(spec); spec.loader.exec_module(helpers)

def inputs(rng, count):
    out = []
    def add(kind, payload, path, group, key=False, width=None):
        value = helpers.node(kind, payload) if width is None else bytes([{1:12,2:13,4:14,8:15}[width]*16+kind]) + len(payload).to_bytes(width,'big') + payload
        if key: value = helpers.node(12, value + helpers.node(11, helpers.node(3, b'41')))
        out.append(dict(group=group, expression=helpers.blob(value), path=helpers.literal(path)))
    payloads = [b'\\\xe2', b'\\\xe2abc', b'prefix\\\xe2\x80', b'\\\xe2\x80aTAIL', b'\\\xe2\x80\xaaTAIL',
        b'\\\xe2\x80\xa8TAIL', b'\\\xe2\x80\xa9TAIL', b'\\\n\\\xe2suffix', b'\\\r\n\\\xe2\x80zEND',
        b'\\\xe2\x80\xa8\\\xe2suffix', b'\\\xe2\x80\xa8\\qEND', b'\\qEND', b'\\\xe1END',
        b'a\\u0000b\\\xe2remaining', b'\\\xe2\x00remainder', b'\\\xe2\\u0041\\nEND']
    for kind in [7,8,9,10]:
        for payload in payloads: add(kind,payload,b'$','fixed-escape-tail')
    for kind in [7,8,9,10]:
        for key, path in [(b'\\\xe2abc',b'\\\xe2xyz'), (b'pre\\\xe2abc',b'pre\\\xe2xyz'),
            (b'\\\xe2abc',b'\\\xe2abc'), (b'\\\xe2abc',b'\\qabc'), (b'\\qabc',b'\\qxyz'),
            (b'\\\xe2\x80\xa8tail',b'tail'), (b'\\\n\\\xe2abc',b'\\\r\\\xe2xyz'),
            (b'a\\u0000b',b'a\\u0000c'), (b'\\\xe2abc',b'\\\xe2\x80\xa8xyz')]:
            add(kind,key,b'$."'+path+b'"','fixed-key-escape-tail',key=True)
    out.append(dict(group='candidate1-regression',expression="X'c82431335c745c22613232335c745c75346532645c756433645c75646530307d5ce234653264'",path="'$'"))
    for i in range(count):
        prefix = rng.choice([b'', b'pre', b'\\\n', b'\\\r\n', b'a\\u0000b', b'\\\xe2\x80\xa8'])
        escape = rng.choice([b'\\\xe2',b'\\\xe2\x80',b'\\\xe2\x80\xa8',b'\\\xe2\x80\xa9',b'\\q',b'\\\xe1'])
        tail = rng.randbytes(rng.randrange(0,30))
        payload = prefix + escape + tail
        kind = rng.choice([7,8,9,10]); width = rng.choice([None,1,2,4,8])
        add(kind,payload,b'$','seeded-escape-tail',width=width)
        keypath = prefix + escape + rng.randbytes(rng.randrange(0,30))
        add(kind,payload,b'$."'+keypath+b'"','seeded-key-escape-tail',key=True,width=width)
    return out

def calls(value='v', path='p'):
    return [f'({value} ->> {path})',f'jsonb_extract({value},{path})',f'json_type({value},{path})',
        f'json_array_length({value},{path})',f'json_valid({value},8)',f'json_error_position({value})']

def observe(call): return f'SELECT typeof({call}),hex({call}),hex(quote({call}));'

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,required=True);p.add_argument('--random-cases',type=int,default=64);p.add_argument('--fixtures',type=int,default=8);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    rng=random.Random(a.seed);sqlite=os.environ.get('SQLITE3_BIN','sqlite3');binary=ROOT/'.lake/build/bin/sqleanite';source=helpers.digest();exe=hashlib.sha256(binary.read_bytes()).hexdigest()
    def run(cmd,sql):
        x=subprocess.run(cmd,input=sql.encode(),capture_output=True,timeout=180)
        return dict(code=x.returncode,stdout=x.stdout.decode('latin1'),stderr=x.stderr.decode('latin1'))
    def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
    def snapshot(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['','-wal'] if Path(str(path)+s).exists()}
    def fixture_run(fixture,page,folder,base,values):
        cases=[];runs=[]
        for mode in ['--verified-file','--verified-wal-file']:
            left=folder/(mode+'-lean.db');right=folder/(mode+'-c.db');shutil.copyfile(base,left);shutil.copyfile(base,right);bl,br=snapshot(left),snapshot(right)
            for i,value in enumerate(values):
                for call in calls():
                    sql=observe(call)[:-1]+f' FROM t WHERE id={i};';l=run([str(binary),mode,str(left)],sql);c=csql(right,sql)
                    cases.append(dict(fixture=fixture,page_size=page,mode=mode,input=i,group=value['group'],sql=sql,lean=l,sqlite=c,matched=helpers.same(l,c)))
            sql='PRAGMA integrity_check;SELECT id,typeof(v),hex(v),typeof(p),hex(p) FROM t ORDER BY id;';l,c=csql(left,sql),csql(right,sql)
            runs.append(dict(fixture=fixture,page_size=page,mode=mode,lean=l,sqlite=c,lean_unchanged=bl==snapshot(left),sqlite_unchanged=br==snapshot(right),matched=l['code']==c['code']==0 and l['stdout']==c['stdout'] and l['stdout'].startswith('ok\n') and bl==snapshot(left) and br==snapshot(right)))
        return cases,runs
    fixtures=[];cases=[];runs=[]
    with tempfile.TemporaryDirectory(prefix='sqleanite-json-escape-tail-') as tmp, concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
        futures=[]
        for fixture in range(a.fixtures):
            values=inputs(rng,a.random_cases);page=512<<(fixture%8);folder=Path(tmp)/str(fixture);folder.mkdir();base=folder/'base.db'
            setup=f'PRAGMA page_size={page};CREATE TABLE t(id INTEGER PRIMARY KEY,v,p);BEGIN;'+''.join(f'INSERT INTO t VALUES({i},'+v['expression']+','+v['path']+');' for i,v in enumerate(values))+'COMMIT;'
            made=csql(base,setup);assert made['code']==0,made;fixtures.append(dict(fixture=fixture,page_size=page,values=values));futures.append(pool.submit(fixture_run,fixture,page,folder,base,values))
        for future in futures:
            part,observations=future.result();cases.extend(part);runs.extend(observations)
    assert source==helpers.digest() and exe==hashlib.sha256(binary.read_bytes()).hexdigest(),'Implementation changed during evaluation'
    failures=sum(not x['matched'] for x in cases+runs)
    report=dict(seed=a.seed,random_cases=a.random_cases,fixtures=fixtures,cases=cases,runs=runs,failures=failures,fixture_workers=2,comparison=__doc__.strip(),implementation_sha256=source,executable_sha256=exe,harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),helper_sha256=hashlib.sha256((ROOT/'scripts/run-json-position-differential.py').read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip())
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=failures)));return bool(failures)
if __name__=='__main__':raise SystemExit(main())
