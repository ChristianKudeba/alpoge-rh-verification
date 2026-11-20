#!/usr/bin/env python3
"""Read-only source metrics and import audit; this does not compile Lean.

Run from any directory, with a report path outside the source tree:
  python verification/aggressive/audit_snapshot.py --out /tmp/compaction.json
"""
from __future__ import annotations

import argparse
from collections import deque
import hashlib
import json
from pathlib import Path

from analyze_imports import capture, closure, git, totals

BASE = 'a6f8e4806fc188e1b5053df51f440df74d6fd2cb'


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--base', default=BASE)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    repo = args.repo.resolve()
    base = git(repo, 'rev-parse', args.base).decode().strip()
    before, after, changes = capture(repo, base)
    reachable, external = closure(after, 'Main')
    _, old_external = closure(before, 'Main')
    dangling = [(name, dep) for name, data in after.items()
                for dep in data['imports'] if dep in before and dep not in after]
    assert not dangling, f'Retained imports of removed modules: {dangling[:10]}'
    assert external == old_external, 'Main external dependencies changed'
    assert {'Main', 'Statements'} <= reachable
    assert reachable == set(after), 'Source contains modules outside Main closure'

    # A topological traversal checks the complete retained graph without Python
    # recursion limits. Only external library imports are leaves.
    degree = {name: sum(dep in after for dep in data['imports'])
              for name, data in after.items()}
    consumers = {name: [] for name in after}
    for name, data in after.items():
        for dep in data['imports']:
            if dep in after:
                consumers[dep].append(name)
    ready = deque(name for name, count in degree.items() if count == 0)
    visited = 0
    while ready:
        visited += 1
        for consumer in consumers[ready.popleft()]:
            degree[consumer] -= 1
            if degree[consumer] == 0:
                ready.append(consumer)
    assert visited == len(after), 'Retained import graph contains a cycle'

    preserved = {}
    for name in ('Challenge.lean', 'Solution.lean', 'comparator.json', 'src/Main.lean',
                 'src/Statements.lean', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json'):
        data = (repo / name).read_bytes()
        assert data == git(repo, 'show', f'{base}:{name}'), f'Changed protected input: {name}'
        preserved[name] = hashlib.sha256(data).hexdigest()

    old_totals, new_totals = totals(before, set(before)), totals(after, set(after))
    modified = []
    for path in changes['changed'] + changes['added']:
        module = path.removeprefix('src/').removesuffix('.lean').replace('/', '.')
        modified.append({'path': path,
                         'before': {k: before[module][k] for k in
                                    ('physical_lines', 'nonblank_lines', 'bytes', 'sha256')}
                                   if module in before else None,
                         'after': {k: after[module][k] for k in
                                   ('physical_lines', 'nonblank_lines', 'bytes', 'sha256')}})
    deleted_modules = set(before) - set(after)
    report = {
        'base_commit': base,
        'scope': 'All src/**/*.lean; excludes Mathlib and verification fixtures. Comments count as lines.',
        'before': old_totals, 'after': new_totals,
        'removed': {k: old_totals[k] - new_totals[k] for k in
                    ('modules', 'physical_lines', 'nonblank_lines', 'bytes')},
        'deleted_source_totals': totals(before, deleted_modules),
        'modified_source_files': modified,
        'deleted_source_paths': changes['deleted'],
        'protected_inputs_sha256': preserved,
        'external_imports': sorted(external),
        'all_retained_modules_reachable_from_Main': True,
        'retained_imports_into_deleted_set': 0,
        'retained_graph_acyclic': True,
        'validation_limit': 'Static audit only. Full candidate Comparator remains required.',
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: report[k] for k in
                     ('before', 'after', 'removed', 'deleted_source_totals', 'validation_limit')}, indent=2))


if __name__ == '__main__':
    main()
