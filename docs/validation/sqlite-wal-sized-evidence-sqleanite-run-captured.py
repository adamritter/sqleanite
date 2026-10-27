from pathlib import Path
import argparse, hashlib, json, subprocess, time

p = argparse.ArgumentParser()
p.add_argument('label')
p.add_argument('mode', choices=['build', 'plan'])
p.add_argument('plan', nargs='?')
p.add_argument('--target', action='append', default=[])
a = p.parse_args()
root = Path.cwd()
logs = Path('/dev/shm/sqleanite-tools-20261024/logs')

def digest():
    h = hashlib.sha256()
    for f in sorted((root / 'SQLeanite').rglob('*.lean')) + [root / 'Main.lean']:
        h.update(str(f.relative_to(root)).encode() + b'\0' + f.read_bytes())
    return h.hexdigest()

source = digest()
start = time.time()
if a.mode == 'build':
    log = logs / (a.label + '.log')
    with log.open('w') as output:
        result = subprocess.run(['lake', 'build'] + a.target, stdout=output, stderr=subprocess.STDOUT)
else:
    if not a.plan:
        p.error('plan mode requires a plan path')
    result = subprocess.run(['python3', '/tmp/sqleanite-aggregate-checkpoint-runner.py', a.plan])
record = dict(exit_code=result.returncode, seconds=time.time() - start,
              source_sha256=source, after_source_sha256=digest(), capture='subprocess returncode')
if a.mode == 'build':
    record.update(log=str(log), log_sha256=hashlib.sha256(log.read_bytes()).hexdigest())
Path('/tmp/sqleanite-' + a.label + '-process.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record), flush=True)
if record['after_source_sha256'] != source:
    raise RuntimeError('Source changed during captured execution')
raise SystemExit(result.returncode)
