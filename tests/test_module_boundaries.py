"""Regression checks for the structural guarantees of the module refactor."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent


def script(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / f'{name}.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class ModuleBoundaries(unittest.TestCase):
    def test_repository_boundaries(self):
        self.assertEqual(script('check_module_boundaries').violations(), [])

    def test_audit_reads_only_explicitly_imported_parts(self):
        reader = script('lean_sources')
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            folder = root / 'SQLeanite' / 'Feature'
            folder.mkdir(parents=True)
            facade = root / 'SQLeanite' / 'Feature.lean'
            facade.write_text('import SQLeanite.Feature.Live\n/-! ' + reader.FACADE_MARKER + ' -/\n')
            (folder / 'Live.lean').write_text('import Init\ndef live := 1\n')
            (folder / 'Detached.lean').write_text('def detachedProof := 2\n')
            text = reader.source_text(root, 'SQLeanite/Feature.lean')
            self.assertIn('def live := 1', text)
            self.assertNotIn('detachedProof', text)
            facade.write_text('import SQLeanite.Feature.Missing\n/-! ' + reader.FACADE_MARKER + ' -/\n')
            with self.assertRaises(FileNotFoundError):
                reader.source_text(root, 'SQLeanite/Feature.lean')

    def test_indirect_execution_dependency_is_detected(self):
        checker = script('check_module_boundaries')
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            folder = root / 'SQLeanite'
            folder.mkdir()
            (folder / 'CoreDecode.lean').write_text('import SQLeanite.Bridge\n')
            (folder / 'Bridge.lean').write_text('import SQLeanite.CoreSQL\n')
            (folder / 'CoreSQL.lean').write_text('import Init\n')
            self.assertTrue(any('reaches execution module SQLeanite.CoreSQL' in error
                                for error in checker.violations(root)))

    def test_line_limit_is_strictly_below_600(self):
        checker = script('check_module_boundaries')
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / 'Example.lean'
            source.write_text('-- example\n' * 599)
            self.assertEqual(checker.violations(root), [])
            source.write_text('-- example\n' * 600)
            self.assertTrue(any('600 lines' in error for error in checker.violations(root)))

    def test_test_entry_keeps_dispatch_and_only_its_imported_cases(self):
        reader = script('lean_sources')
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            cases = root / 'SQLeaniteTests'
            cases.mkdir()
            (cases / 'Live.lean').write_text('def liveCase := 1\n')
            (cases / 'Detached.lean').write_text('def detachedCase := 2\n')
            (root / 'Tests.lean').write_text('import SQLeaniteTests.Live\ndef main := liveCase\n')
            text = reader.source_text(root, 'Tests.lean')
            self.assertIn('def liveCase', text)
            self.assertIn('def main', text)
            self.assertNotIn('detachedCase', text)


if __name__ == '__main__':
    unittest.main()
