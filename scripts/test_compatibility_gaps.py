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

def regression(feature, mode):
    def test(self):
        with tempfile.TemporaryDirectory(prefix='sqleanite-gap-unit-') as directory:
            report = Path(directory) / 'result.json'
            result = subprocess.run(
                [sys.executable, str(SCRIPT), '--seed', os.environ.get('SQLEANITE_GAP_SEED', '356317'),
                 '--feature', feature, '--mode=' + mode, '--output', str(report)],
                capture_output=True, text=True, timeout=90)
            self.assertTrue(report.exists(), result.stderr)
            data = json.loads(report.read_text())
            self.assertTrue(data['complete'], result.stderr)
            self.assertEqual(len(data['cases']), 1)
            case = data['cases'][0]
            differences = []
            if not survey.helpers.same(case['lean'], case['sqlite']):
                differences.append('SQL result/error: ' + repr(case['lean']) + ' != ' + repr(case['sqlite']))
            if case['observation_lean'] != case['observation_sqlite']:
                differences.append('persisted catalog/rows/integrity differ')
            self.assertTrue(case['matched'], feature + ' ' + mode + ': ' + '; '.join(differences))
            self.assertEqual(result.returncode, 0, result.stderr)
    return test

for feature, _ in survey.PROBES:
    for suffix, mode in [('rollback', '--verified-file'), ('wal', '--verified-wal-file')]:
        setattr(CompatibilityGaps, 'test_' + feature.replace('-', '_') + '_' + suffix,
                regression(feature, mode))

if __name__ == '__main__':
    unittest.main()
