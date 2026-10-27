#!/usr/bin/env python3
"""Individually runnable, deliberately failing SQLite compatibility regressions.

Run all: python -m unittest discover -s scripts -p test_compatibility_gaps.py
Run one: python scripts/test_compatibility_gaps.py CompatibilityGaps.test_cte_wal
Known gaps are failures, never skips or expected failures. Each test compares
SQL output/errors AND persisted catalog/rows/integrity with reference SQLite.
Set SQLEANITE_GAP_SEED for fresh final-checkpoint data; default reproduces the
56 differences recorded on 2026-10-27. Requires a built public executable.
"""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / 'scripts/run-compatibility-gap-survey.py'
spec = importlib.util.spec_from_file_location('gap_survey', SCRIPT)
survey = importlib.util.module_from_spec(spec)
spec.loader.exec_module(survey)

class CompatibilityGaps(unittest.TestCase):
    """88 separately selectable checks, including all 56 recorded failures."""

    @classmethod
    def setUpClass(cls):
        # One execution still creates isolated databases for every feature/mode.
        # Keep each comparison as a separate unittest, including known failures.
        with tempfile.TemporaryDirectory(prefix='sqleanite-gap-unit-') as directory:
            report = Path(directory) / 'result.json'
            result = subprocess.run(
                [sys.executable, str(SCRIPT), '--seed', os.environ.get('SQLEANITE_GAP_SEED', '356317'),
                 '--output', str(report)],
                capture_output=True, text=True, timeout=1800)
            if not report.exists():
                raise AssertionError('Survey did not produce a report: ' + result.stderr)
            data = json.loads(report.read_text())
            if not data['complete']:
                raise AssertionError('Survey stopped before completing: ' + result.stderr)
            expected = {(feature, mode) for feature, _ in survey.PROBES
                        for mode in ('--verified-file', '--verified-wal-file')}
            cls.cases = {(case['feature'], case['mode']): case for case in data['cases']}
            if set(cls.cases) != expected or len(data['cases']) != len(expected):
                raise AssertionError('Missing, duplicate or unexpected survey cases')
            failures = sum(not case['matched'] for case in data['cases'])
            if data['failures'] != failures or result.returncode != int(bool(failures)):
                raise AssertionError('Survey failure count/exit status is inconsistent: ' + result.stderr)


def regression(feature, mode):
    def test(self):
        case = self.cases[(feature, mode)]
        differences = []
        if not survey.helpers.same(case['lean'], case['sqlite']):
            differences.append('SQL result/error: ' + repr(case['lean']) + ' != ' + repr(case['sqlite']))
        if case['observation_lean'] != case['observation_sqlite']:
            differences.append('persisted catalog/rows/integrity differ')
        self.assertTrue(case['matched'], feature + ' ' + mode + ': ' + '; '.join(differences))
    return test

for feature, _ in survey.PROBES:
    for suffix, mode in [('rollback', '--verified-file'), ('wal', '--verified-wal-file')]:
        setattr(CompatibilityGaps, 'test_' + feature.replace('-', '_') + '_' + suffix,
                regression(feature, mode))

if __name__ == '__main__':
    unittest.main()
