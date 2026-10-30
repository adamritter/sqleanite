#!/usr/bin/env python3
"""Every named hypothesis is an independently runnable real failing test.

python scripts/test_remaining_compatibility_gaps.py RemainingGaps.test_upsert_compound_wal
No skip/expectedFailure, no baseline-dependent acceptance, no production edits.
SQLEANITE_REMAINING_SEED varies fixture values without changing SQL semantics.
"""
import os
import unittest
from remaining_gap_harness import cases,evaluate

class RemainingGaps(unittest.TestCase):
    pass

def regression(case,mode):
    def test(self):
        result=evaluate(case,mode)
        self.assertEqual(result['status'],'pass',
            case['name']+' '+mode+': '+str(result.get('differences',[]))+'\n'+
            str(result.get('lean',result.get('setup_result')))+'\nreference: '+str(result.get('sqlite')))
    return test

for case in cases(int(os.environ.get('SQLEANITE_REMAINING_SEED','2026103001'))):
    for mode in (('api',) if case.get('api') else ('rollback','wal')):
        setattr(RemainingGaps,'test_'+case['name']+'_'+mode,regression(case,mode))

if __name__=='__main__':unittest.main()
