#!/usr/bin/env python3
"""Finite gap discovery report, NOT a global SQLite compatibility percentage."""
import argparse
import concurrent.futures
from collections import Counter
import json
from pathlib import Path
import time
from remaining_gap_harness import cases,evaluate,provenance


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--seed',type=int,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--feature',action='append')
    p.add_argument('--workers',type=int,default=4)
    args=p.parse_args()
    selected=cases(args.seed)
    if args.feature:
        unknown=set(args.feature)-{c['name'] for c in selected}
        if unknown:p.error('unknown features: '+str(sorted(unknown)))
        selected=[c for c in selected if c['name'] in args.feature]
    before=provenance();start=time.monotonic()
    jobs=[(case,mode) for case in selected for mode in (('api',) if case.get('api') else ('rollback','wal'))]
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        records=list(pool.map(lambda job:evaluate(*job),jobs))
    after=provenance()
    assert before==after,'source, binary, oracle or harness changed during evaluation'
    counts=dict(Counter(c['status'] for c in records))
    report=dict(complete=True,seed=args.seed,seconds=time.monotonic()-start,
                provenance=before,counts=counts,cases=records,
                scope='Named finite SQL/file hypotheses; pass is not feature completeness. Native setup/query errors are invalid probes, never compatibility failures.')
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2,ensure_ascii=True)+'\n')
    print(json.dumps(dict(features=len(selected),cases=len(records),counts=counts,seconds=report['seconds'])))
    return 2 if any(c.startswith('invalid') for c in counts) else int(bool(counts.get('fail')))

if __name__=='__main__':raise SystemExit(main())
