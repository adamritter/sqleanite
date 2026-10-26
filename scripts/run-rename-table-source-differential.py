#!/usr/bin/env python3
"""ALTER RENAME TABLE: catalog spelling, rows, errors and cross-engine reuse.

Preselected ordinary rowid tables include source comments, quote styles,
Unicode, hidden/explicit rowids, AUTOINCREMENT and table-level primary keys.
Seeded new names/data exercise reused templates; no outcome is filtered.
Named-index spelling and referring foreign keys/views/triggers remain separate
known gaps and are outside this corpus. Both public file modes are checked.
"""
import argparse, hashlib, importlib.util, json, os, random, shutil, subprocess, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('helpers', ROOT/'scripts/run-json-position-differential.py')
helpers = importlib.util.module_from_spec(spec); spec.loader.exec_module(helpers)

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--seed', type=int, required=True)
    p.add_argument('--count', type=int, default=128)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args(); rng = random.Random(a.seed)
    sqlite = os.environ.get('SQLITE3_BIN', 'sqlite3'); binary = ROOT/'.lake/build/bin/sqleanite'
    source = helpers.digest(); executable = hashlib.sha256(binary.read_bytes()).hexdigest()
    def run(cmd, sql):
        r = subprocess.run(cmd, input=sql.encode(), capture_output=True, timeout=30)
        return dict(code=r.returncode, stdout=r.stdout.decode('latin1'), stderr=r.stderr.decode('latin1'))
    def csql(path, sql): return run([sqlite, '-batch', '-bail', str(path)], sql)
    def quote(s, style='"'):
        return '['+s+']' if style=='[' else style+s.replace(style, style+style)+style
    def name(): return ''.join(rng.choice('aAZ09_ é中";\'') for _ in range(rng.randrange(1, 28)))
    inputs=[]; cases=[]
    bodies=['(id INTEGER PRIMARY KEY,v TEXT)', '(id INTEGER, v TEXT, PRIMARY KEY(id DESC))',
            '(id INTEGER PRIMARY KEY AUTOINCREMENT,v)', '(id INTEGER,v TEXT)',
            "(id INTEGER PRIMARY KEY,v DEFAULT ('a;''b') /* keep */ )"]
    for i in range(a.count):
        old='old_'+name(); new='new_'+name(); ot=quote(old); nt=quote(new)
        create='CREATE TABLE '+quote(old,rng.choice(['"',"'",'`','[']))+' /* retain '+str(rng.randrange(10000000))+' */ '+bodies[i%len(bodies)]+';'
        populate=''.join('INSERT INTO '+ot+' VALUES('+str(j)+",'value "+str(rng.randrange(1000000))+"');" for j in range(1,1+i%5))
        alter='ALTER TABLE '+quote(old,rng.choice(['"',"'",'`','[']))+' RENAME TO '+quote(new,rng.choice(['"',"'",'`','[']))+';'
        scenario=i%6
        if scenario==0: sql=alter
        elif scenario==1: sql='BEGIN;'+alter+'COMMIT;'
        elif scenario==2: sql='BEGIN;'+alter+'ROLLBACK;'+alter
        elif scenario==3: sql='SAVEPOINT s;'+alter+'ROLLBACK TO s;RELEASE s;'+alter
        elif scenario==4: sql=alter+'ALTER TABLE '+nt+' RENAME TO '+ot+';'+alter
        else: sql=alter+'UPDATE '+nt+" SET v='changed' WHERE id=1;"
        sql+='SELECT * FROM '+nt+' ORDER BY id;'
        read='PRAGMA table_info('+nt+');SELECT * FROM '+nt+' ORDER BY id;'
        observe='PRAGMA integrity_check;SELECT type,hex(name),hex(tbl_name),hex(sql) FROM sqlite_schema ORDER BY type,name;'+read
        follow='INSERT INTO '+nt+"(v) VALUES('follow');PRAGMA integrity_check;"+read
        inputs.append(dict(create=create,populate=populate,sql=sql,read=read,observe=observe,follow=follow,page_size=512<<(i%8),scenario=scenario))
    with tempfile.TemporaryDirectory(prefix='sqleanite-rename-source-') as tmp:
        folder=Path(tmp)
        for i,entry in enumerate(inputs):
            base=folder/(str(i)+'-base.db')
            made=csql(base,'PRAGMA page_size='+str(entry['page_size'])+';'+entry['create']+entry['populate'])
            assert made['code']==0,made
            for mode in ['--verified-file','--verified-wal-file']:
                left=folder/(str(i)+mode+'-lean.db');right=folder/(str(i)+mode+'-sqlite.db')
                shutil.copyfile(base,left);shutil.copyfile(base,right)
                l,c=run([str(binary),mode,str(left)],entry['sql']),csql(right,entry['sql'])
                lo,co=csql(left,entry['observe']),csql(right,entry['observe'])
                lr,cr=run([str(binary),mode,str(left)],entry['read']),csql(right,entry['read'])
                lw,cw=csql(left,entry['follow']),csql(right,entry['follow'])
                matched=helpers.same(l,c) and lo==co and lo['code']==0 and lo['stdout'].startswith('ok\n') and helpers.same(lr,cr) and lw==cw and lw['code']==0
                cases.append(dict(input=i,mode=mode,lean=l,sqlite=c,observation_lean=lo,observation_sqlite=co,reopen_lean=lr,reopen_sqlite=cr,follow_lean=lw,follow_sqlite=cw,matched=matched))
    assert source==helpers.digest() and executable==hashlib.sha256(binary.read_bytes()).hexdigest()
    report=dict(seed=a.seed,comparison=__doc__.strip(),inputs=inputs,cases=cases,failures=sum(not c['matched'] for c in cases),implementation_sha256=source,executable_sha256=executable,harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),helper_sha256=hashlib.sha256((ROOT/'scripts/run-json-position-differential.py').read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip())
    a.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(cases=len(cases),failures=report['failures'])))
    return bool(report['failures'])
if __name__=='__main__': raise SystemExit(main())
