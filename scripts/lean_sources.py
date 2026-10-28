"""Read a logical Lean source through its explicit compatibility imports.

Audits must follow the facade's actual imports, rather than globbing sibling
files: an unimported proof or implementation must not satisfy a wiring check.
The expanded text is for source inspection. ProofAxioms also uses it to run
all its print directives, which imports alone deliberately do not replay.
"""
from pathlib import Path
import argparse
import re

FACADE_MARKER = 'Compatibility import for the responsibility modules above.'


def source_files(root: Path, relative: str) -> list[Path]:
    path = root / relative
    text = path.read_text()
    test_entry = relative == 'Tests.lean'
    if FACADE_MARKER not in text and not test_entry:
        return [path]
    module = 'SQLeaniteTests' if test_entry else relative.removesuffix('.lean').replace('/', '.')
    children = re.findall(r'^import (\S+)', text, re.MULTILINE)
    if not children or any(not name.startswith(module + '.') for name in children):
        raise ValueError(f'{relative}: invalid compatibility import')
    result = []
    for name in children:
        child = name.replace('.', '/') + '.lean'
        result.extend(source_files(root, child))
    if test_entry:
        result.append(path)
    return list(dict.fromkeys(result))


def source_text(root: Path, relative: str) -> str:
    imports, bodies = [], []
    for path in source_files(root, relative):
        text = path.read_text()
        imports.extend(re.findall(r'^import (\S+)', text, re.MULTILINE))
        bodies.append(re.sub(r'^import \S+\n', '', text, flags=re.MULTILINE))
    header = ''.join(f'import {name}\n' for name in dict.fromkeys(imports))
    return header + '\n' + '\n'.join(bodies)


def materialize(root: Path, destination: Path) -> None:
    if (root / 'Tests.lean').exists():
        destination.mkdir(parents=True, exist_ok=True)
        (destination / 'Tests.lean').write_text(source_text(root, 'Tests.lean'))
    for folder in ['SQLeanite', 'TestData']:
        for path in (root / folder).rglob('*.lean'):
            if FACADE_MARKER in path.read_text():
                relative = str(path.relative_to(root))
                target = destination / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text(source_text(root, relative))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument('--materialize', type=Path)
    parser.add_argument('source', nargs='?')
    args = parser.parse_args()
    if args.materialize:
        materialize(args.root, args.materialize)
    elif args.source:
        print(source_text(args.root, args.source), end='')
    else:
        parser.error('supply a source or --materialize')


if __name__ == '__main__':
    main()
