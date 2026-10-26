#!/usr/bin/env python3
"""Fixed public read controls against pinned C SQLite; not fresh evaluation.

Read every setup/sql pair from a JSON cases list and rerun both programs. Both
public file modes are used unless an input case already records its mode.
Compare complete stdout including error prefixes, status, immutable main/WAL
bytes, and C integrity checks. Stored oracle output never supplies the result.
"""
import argparse, hashlib, json, os, shutil, subprocess, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
def digest(root):
    value = hashlib.sha256()
    for path in sorted((root/'SQLeanite').rglob('*.lean'))+[root/'Main.lean']:
        value.update(str(path.relative_to(root)).encode()+b'\0'+path.read_bytes())
    return value.hexdigest()
def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('--implementation-root', type=Path, default=ROOT)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args(); root = args.implementation_root.resolve()
    sqlite = os.environ.get('SQLITE3_BIN', 'sqlite3'); binary = root/'.lake/build/bin/sqleanite'
    source = digest(root); executable = hashlib.sha256(binary.read_bytes()).hexdigest()
    data = json.loads(args.input.read_text()); cases = []
    def run(command, sql):
        result = subprocess.run(command, input=sql.encode(), capture_output=True, timeout=120)
        return dict(code=result.returncode, stdout=result.stdout.decode('latin1'), stderr=result.stderr.decode('latin1'))
    def csql(path, sql):return run([sqlite, '-batch', '-bail', str(path)], sql)
    def snapshot(path):
        return {suffix:hashlib.sha256(Path(str(path)+suffix).read_bytes()).hexdigest()
                for suffix in ['', '-wal'] if Path(str(path)+suffix).exists()}
    with tempfile.TemporaryDirectory(prefix='sqleanite-read-controls-') as tmp:
        for index, case in enumerate(data['cases']):
            for mode in ([case['mode']] if 'mode' in case else ['--verified-file','--verified-wal-file']):
                folder = Path(tmp)/str(len(cases)); folder.mkdir()
                left, right = folder/'lean.db', folder/'sqlite.db'
                created = csql(right, case['setup']); assert created['code']==0, created
                shutil.copyfile(right, left); bl, br = snapshot(left), snapshot(right)
                lean = run([str(binary), mode, str(left)], case['sql']); reference = csql(right, case['sql'])
                unchanged = bl==snapshot(left) and br==snapshot(right)
                li, ri = csql(left, 'PRAGMA integrity_check;'), csql(right, 'PRAGMA integrity_check;')
                matched = (bool(lean['code'])==bool(reference['code']) and lean['stdout']==reference['stdout']
                           and unchanged and li['code']==ri['code']==0 and li['stdout']==ri['stdout']=='ok\n')
                cases.append(dict(input_case=index, mode=mode, setup=case['setup'], sql=case['sql'], lean=lean,
                    sqlite=reference, unchanged=unchanged, integrity_lean=li, integrity_sqlite=ri, matched=matched))
    assert source==digest(root), 'Source changed during control evaluation'
    assert executable==hashlib.sha256(binary.read_bytes()).hexdigest(), 'Executable changed during control evaluation'
    failures = sum(not case['matched'] for case in cases)
    report = dict(evaluation=__doc__.strip(), input_file=str(args.input),
        input_sha256=hashlib.sha256(args.input.read_bytes()).hexdigest(), cases=cases, failures=failures,
        implementation_sha256=source, executable_sha256=executable,
        harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        sqlite_version=subprocess.check_output([sqlite, '--version'], text=True).strip())
    args.output.write_text(json.dumps(report, indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=failures)))
    return bool(failures)
if __name__ == '__main__':raise SystemExit(main())
