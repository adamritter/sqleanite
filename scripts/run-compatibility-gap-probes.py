#!/usr/bin/env python3
"""Recheck retained SQL counterexamples without treating them as coverage.

This is a diagnostic inventory, not a whole-SQLite compatibility percentage.
Use --require-compatible to fail on any remaining rejection or difference.
"""
import argparse
import hashlib
import json
import os
import pathlib
import subprocess
import tempfile

ROOT=pathlib.Path(__file__).resolve().parents[1]


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean',type=pathlib.Path,default=ROOT/'.lake/build/bin/sqleanite')
    p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','/usr/bin/sqlite3'))
    p.add_argument('--output',type=pathlib.Path)
    p.add_argument('--require-compatible',action='store_true')
    args=p.parse_args()
    old=json.loads((ROOT/'docs/validation/sqlite-remaining-gaps-20261024.json').read_text())
    probes=[dict(name=x['name'],sql=x['sql'],historical_status=x['status']) for x in old['probes']]
    setup='CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,1.5),(2,2.5),(3,NULL);'
    probes += [dict(name=name,sql=setup+sql) for name,sql in [
        ('row_expression_delete','DELETE FROM t WHERE v+1>2;SELECT id FROM t ORDER BY id;'),
        ('real_sum','SELECT sum(v) FROM t;'),
        ('avg','SELECT avg(v) FROM t;'),
        ('count_distinct','SELECT count(DISTINCT v) FROM t;'),
        ('window','SELECT row_number() OVER (ORDER BY id) FROM t;'),
        ('limit_offset','SELECT id FROM t ORDER BY id LIMIT 1 OFFSET 1;'),
        ('in_list','SELECT id FROM t WHERE id IN (1,3);'),
        ('aggregate_row_where','SELECT count(*) FROM t WHERE v+1>2;'),
        ('pragma','PRAGMA integrity_check;'),
        ('round','SELECT round(v,1) FROM t ORDER BY id;'),
        ('update_primary_key','UPDATE t SET id=id+10;SELECT id FROM t ORDER BY id;')]]
    probes += [dict(name='unique_index',sql=setup+'CREATE UNIQUE INDEX tv ON t(v);'),
               dict(name='without_rowid',sql="CREATE TABLE w(k TEXT PRIMARY KEY,v) WITHOUT ROWID;INSERT INTO w VALUES('x',1);SELECT * FROM w;"),
               dict(name='nocase',sql="CREATE TABLE n(id INTEGER PRIMARY KEY,v TEXT COLLATE NOCASE);INSERT INTO n VALUES(1,'a');SELECT id FROM n WHERE v='A';")]
    probes += [dict(name='in_fixed_column_rhs',sql='CREATE TABLE t(id INTEGER PRIMARY KEY,n);INSERT INTO t VALUES(1,1),(2,2);SELECT id FROM t WHERE id=1 AND id IN (1,abs(-9223372036854775808),id) ORDER BY id LIMIT 1;')]
    results=[]
    with tempfile.TemporaryDirectory(prefix='sqleanite-gaps-') as tmp:
        for i,probe in enumerate(probes):
            d=pathlib.Path(tmp)/str(i);d.mkdir();q=d/'query.sql';q.write_text(probe['sql'])
            a=subprocess.run([str(args.lean),'--verified-file',str(d/'lean.db'),str(q)],text=True,capture_output=True,timeout=120)
            b=subprocess.run([args.sqlite,'-batch','-bail',str(d/'sqlite.db')],input=probe['sql'],text=True,capture_output=True,timeout=120)
            if a.returncode==0 and b.returncode==0:
                status='matches' if a.stdout==b.stdout else 'output_difference'
            elif a.returncode!=0 and b.returncode==0: status='explicit_rejection'
            elif a.returncode==0 and b.returncode!=0: status='unexpected_acceptance'
            else: status='both_reject'
            results.append(dict(**probe,status=status,lean=dict(exit_code=a.returncode,stdout=a.stdout,stderr=a.stderr),
                sqlite=dict(exit_code=b.returncode,stdout=b.stdout,stderr=b.stderr)))
    counts={status:sum(r['status']==status for r in results) for status in sorted({r['status'] for r in results})}
    digest=hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:
        digest.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    report=dict(purpose=__doc__.strip(),counts=counts,probes=results,implementation_sha256=digest.hexdigest(),
        executable_sha256=hashlib.sha256(args.lean.read_bytes()).hexdigest(),
        harness_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
        sqlite_version=subprocess.check_output([args.sqlite,'--version'],text=True).strip())
    if args.output: args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
    return args.require_compatible and any(x['status'] not in ['matches','both_reject'] for x in results)


if __name__=='__main__':
    raise SystemExit(main())
