"""Enforce small source files and the physical-decoder dependency boundary."""
from pathlib import Path
import argparse
import re

ROOT = Path(__file__).resolve().parent.parent
SOURCE_SUFFIXES = {'.lean', '.py', '.sh', '.c', '.h'}


def sources(root=ROOT):
    files = list(root.glob('*.lean'))
    for folder in ['SQLeanite', 'TestData', 'SQLeaniteTests', 'scripts', 'tests', 'native']:
        files.extend(p for p in (root / folder).rglob('*')
                     if p.is_file() and p.suffix in SOURCE_SUFFIXES)
    return files


def import_graph(root=ROOT):
    return {str(path.relative_to(root)).removesuffix('.lean').replace('/', '.'):
            set(re.findall(r'^import (\S+)', path.read_text(), re.MULTILINE))
            for path in sources(root) if path.suffix == '.lean'}


def dependencies(graph, module):
    seen, pending = set(), list(graph.get(module, []))
    while pending:
        dependency = pending.pop()
        if dependency not in seen:
            seen.add(dependency)
            pending.extend(graph.get(dependency, []))
    return seen


def violations(root=ROOT):
    errors = []
    for path in sources(root):
        count = len(path.read_text().splitlines())
        if count >= 600:
            errors.append(f'{path.relative_to(root)}: {count} lines (maximum 599)')
    graph = import_graph(root)
    for module in graph:
        if module == 'SQLeanite.CoreDecode' or module.startswith('SQLeanite.CoreDecode.'):
            for dependency in dependencies(graph, module):
                if dependency == 'SQLeanite.Engine' or dependency.startswith('SQLeanite.Engine.') or \
                        dependency == 'SQLeanite.CoreSQL' or dependency.startswith('SQLeanite.CoreSQL.'):
                    errors.append(f'{module} reaches execution module {dependency}')
        if module in {'Main', 'SQLeanite.CoreRuntime'}:
            for dependency in dependencies(graph, module):
                if dependency == 'SQLeanite.Engine' or dependency.startswith('SQLeanite.Engine.'):
                    errors.append(f'{module} reaches the legacy interpreter {dependency}')
    return sorted(set(errors))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reaches', nargs=2, metavar=('MODULE', 'DEPENDENCY'))
    args = parser.parse_args()
    if args.reaches:
        module, dependency = args.reaches
        raise SystemExit(0 if dependency in dependencies(import_graph(), module) else 1)
    errors = violations()
    if errors:
        raise SystemExit('\n'.join(errors))
    print(f'Module boundaries: {len(sources())} source files below 600 lines; decoder independent of SQL execution')
