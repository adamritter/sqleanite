"""Independent native differential observations for maintained gap regressions."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

from test_check_add_column import statement_lines
from remaining_gap_cases_schema import cases as schema_cases
from remaining_gap_cases_queries import cases as query_cases
from remaining_gap_cases_storage import cases as storage_cases
from remaining_gap_cases_effects import cases as effects_cases
from remaining_gap_cases_extended import cases as extended_cases

ROOT=Path(__file__).resolve().parents[1]
SQLITE=os.environ.get('SQLITE3_BIN','sqlite3')
BINARY=ROOT/'.lake/build/bin/sqleanite'
MODES={'rollback':'--verified-file','wal':'--verified-wal-file'}


def cases(seed):
    result=schema_cases(seed)+query_cases(seed)+storage_cases(seed)+effects_cases(seed)+extended_cases(seed)
    names=[c['name'] for c in result]
    assert len(names)==len(set(names)), 'duplicate probe names'
    return result


def run(argv,sql,timeout=15):
    try:
        p=subprocess.run([str(x) for x in argv],input=sql.encode(),capture_output=True,timeout=timeout)
        return dict(code=p.returncode,stdout_hex=p.stdout.hex(),stderr=p.stderr.decode('utf-8','backslashreplace'),timed_out=False)
    except subprocess.TimeoutExpired as e:
        return dict(code=124,stdout_hex=(e.stdout or b'').hex(),stderr=(e.stderr or b'').decode('utf-8','backslashreplace'),timed_out=True)


def native(path,sql):
    return run([SQLITE,'-batch','-bail',path],statement_lines(sql))


def error(result):
    lines=result['stderr'].splitlines()
    return re.sub(r'^(?:Parse error|Runtime error|Error)(?: near line [0-9]+)?: ?', '',lines[0] if lines else '')


def text(result):return bytes.fromhex(result['stdout_hex']).decode('utf-8')
def ident(name):return '"'+name.replace('"','""')+'"'
def literal(name):return "'"+name.replace("'","''")+"'"


def snapshot(path):
    catalog=native(path,'SELECT type,hex(name),hex(tbl_name),hex(sql) FROM sqlite_schema ORDER BY type,name;')
    headers=native(path,'PRAGMA encoding;PRAGMA page_size;PRAGMA auto_vacuum;PRAGMA user_version;PRAGMA application_id;')
    integrity=native(path,'PRAGMA integrity_check;')
    names=native(path,"SELECT json_quote(name) FROM sqlite_schema WHERE type='table' ORDER BY name;")
    tables=[]
    if names['code']==0:
        for raw in text(names).splitlines():
            name=json.loads(raw)
            info=native(path,'PRAGMA table_xinfo('+ident(name)+');')
            columns=native(path,'SELECT json_quote(name) FROM pragma_table_xinfo('+literal(name)+') WHERE hidden<>1 ORDER BY cid;')
            if columns['code']:
                tables.append(dict(name=name,info=info,columns=columns));continue
            cols=[json.loads(x) for x in text(columns).splitlines()]
            wr=native(path,'SELECT wr FROM pragma_table_list WHERE schema=\'main\' AND name='+literal(name)+';')
            # Include the observable hidden rowid where it has an unshadowed name.
            aliases=[a for a in ('rowid','_rowid_','oid') if a not in [c.lower() for c in cols]]
            if wr['code']==0 and text(wr).strip()=='0' and aliases:cols=[aliases[0]]+cols
            fields=','.join('typeof('+ident(c)+'),hex('+ident(c)+'),quote('+ident(c)+')' for c in cols)
            data=native(path,'SELECT json_array('+fields+') FROM '+ident(name)+';') if fields else columns
            # Snapshot is a multiset, not a planner-order assertion. SQL result
            # stdout above is ALWAYS compared verbatim with its original order.
            if data['code']==0:
                data=dict(data,stdout_hex=('\n'.join(sorted(text(data).splitlines()))+'\n').encode().hex())
            tables.append(dict(name=name,info=info,columns=columns,rows=data))
    return dict(catalog=catalog,headers=headers,integrity=integrity,names=names,tables=tables,
                reserved_bytes=(path.read_bytes()[20] if path.exists() and path.stat().st_size>=100 else None))


def evaluate_api(case):
    sql=statement_lines(case['setup']+case['sql'])
    lean=run([ROOT/'.lake/build/bin/sqleanite_tests','--error-effects-script'],sql)
    ref=run([SQLITE,'-batch',':memory:'],sql)
    def errors(result):
        return [re.sub(r'^(?:Parse error|Runtime error|Error)(?: near line [0-9]+)?: ?', '',line)
                for line in result['stderr'].splitlines()
                if re.match(r'^(?:Parse error|Runtime error|Error)(?: near line [0-9]+)?:',line)]
    differences=[]
    if lean['timed_out'] or ref['timed_out']:differences.append('timeout')
    if lean['code']!=ref['code']:differences.append('exit_status')
    if lean['stdout_hex']!=ref['stdout_hex']:differences.append('sql_output')
    if errors(lean)!=errors(ref):differences.append('sql_errors')
    valid=bool(ref['code'])==case.get('reference_error',False) and not ref['timed_out']
    return dict(**case,mode='api',status=('fail' if differences else 'pass') if valid else 'invalid_reference_sql',
                differences=differences,lean=lean,sqlite=ref)


def wal_fixture(case,base,left,right):
    # Keep a native connection alive until the committed main/WAL pair has been
    # copied. The oracle's last-close checkpoint must not erase the test input.
    run_setup=native(base,"PRAGMA encoding="+literal(case['encoding'])+";CREATE TABLE anchor(x);")
    if run_setup['code']:raise RuntimeError(str(run_setup))
    with tempfile.NamedTemporaryFile() as log:
        proc=subprocess.Popen([SQLITE,'-batch','-bail',str(base)],stdin=subprocess.PIPE,
                              stdout=log,stderr=log,text=True)
        try:
            sql='PRAGMA journal_mode=WAL;PRAGMA wal_autocheckpoint=0;'+case['setup']
            proc.stdin.write(statement_lines(sql)+'\n.print SQLEANITE_WAL_READY\n');proc.stdin.flush()
            import time
            deadline=time.monotonic()+15
            while True:
                out=Path(log.name).read_bytes()
                if b'SQLEANITE_WAL_READY' in out:break
                if proc.poll() is not None or time.monotonic()>deadline:
                    raise RuntimeError('native WAL fixture failed: '+repr(out))
                time.sleep(.01)
            wal=Path(str(base)+'-wal')
            if not wal.exists() or wal.stat().st_size<=32:raise RuntimeError('missing committed WAL')
            for target in (left,right):
                shutil.copyfile(base,target);shutil.copyfile(wal,str(target)+'-wal')
            return dict(main_sha256=sha(base),wal_sha256=sha(wal),wal_bytes=wal.stat().st_size)
        finally:
            proc.stdin.close()
            try:proc.wait(timeout=5)
            except subprocess.TimeoutExpired:proc.kill();proc.wait()


def evaluate(case,mode):
    if mode=='api':return evaluate_api(case)
    with tempfile.TemporaryDirectory(prefix='sqleanite-remaining-') as folder:
        base=Path(folder)/'base.db';left=Path(folder)/'lean.db';right=Path(folder)/'sqlite.db'
        fixture=None
        if case.get('wal_fixture'):
            fixture=wal_fixture(case,base,left,right)
        else:
            setup=native(base,case['setup'])
            if setup['code'] or setup['timed_out']:
                return dict(**case,mode=mode,status='invalid_reference_setup',setup_result=setup)
            if not base.exists():base.touch()
            shutil.copyfile(base,left);shutil.copyfile(base,right)
        sql=statement_lines(case['sql'])
        ref=native(right,sql)
        lean=run([BINARY,MODES[mode],left],sql)
        lo,ro=snapshot(left),snapshot(right)
        differences=[]
        if lean['timed_out'] or ref['timed_out']:differences.append('timeout')
        if lean['code']!=ref['code']:differences.append('exit_status')
        if lean['stdout_hex']!=ref['stdout_hex']:differences.append('sql_output')
        if error(lean)!=error(ref):differences.append('sql_error')
        for key in lo:
            if lo[key]!=ro[key]:differences.append('persisted_'+key)
        if ro['integrity']['code'] or text(ro['integrity'])!='ok\n':differences.append('reference_integrity')
        if lo['integrity']['code'] or text(lo['integrity'])!='ok\n':differences.append('lean_integrity')
        status='invalid_reference_sql' if ref['code'] or ref['timed_out'] else ('fail' if differences else 'pass')
        return dict(**case,mode=mode,status=status,fixture=fixture,differences=differences,lean=lean,sqlite=ref,observation_lean=lo,observation_sqlite=ro)


def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def provenance():
    h=hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:
        h.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    return dict(source_sha256=h.hexdigest(),executable_sha256=sha(BINARY),api_executable_sha256=sha(ROOT/'.lake/build/bin/sqleanite_tests'),
                sqlite_version=subprocess.check_output([SQLITE,'--version'],text=True).strip(),
                harness_sha256={p.name:sha(p) for p in sorted((ROOT/'scripts').glob('*remaining*gap*.py'))})
