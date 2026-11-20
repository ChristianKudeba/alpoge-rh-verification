#!/usr/bin/env python3
"""Compare Lean source import closures at a Git ref and in the working tree.

Only the Python standard library and Git are needed. No Lean compilation occurs.
The working-tree files are read once; their Git blob IDs identify unchanged comparison-ref
files. Original contents are fetched with git cat-file only for changed/deleted
files. The captured working tree is an observed snapshot (not an atomic checkout).
Import lexing removes nested Lean comments and quoted strings before reading
line-start import commands. Unexpected multiline import commands abort the run.
All source files, not just target closures, are scanned and recorded.

Example:
  python analyze_imports.py --repo /workspace/alpoge-compaction \
    --ref 7cbf7a0c32fca1badf05931879a37c3f8a2b03b4 --out ./graph-analysis
"""
from __future__ import annotations

import argparse
import datetime as dt
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

TOKEN = re.compile(r'/\-|--[^\n]*|"(?:\\.|[^"\\])*"', re.S)
COMMENT_TOKEN = re.compile(r'/\-|\-/')
IMPORT = re.compile(r'^[ \t]*(?:(?:public|meta)[ \t]+)*import[ \t]+([^\n]+)$', re.M)
EMPTY_IMPORT = re.compile(r'^[ \t]*(?:(?:public|meta)[ \t]+)*import[ \t]*$', re.M)
MODULE = re.compile(r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*\Z")
TARGETS = [
    'Main',
    'Formalism.GammaFactorNonvanishing.CritLine',
    'Formalism.GammaFactorNonvanishing.RhOfRight',
    'Supplements.Kernels.MainTheorems',
    'Supplements.Kernels.MainTheoremsCritical',
    'Supplements.Kernels.MainTheoremsAll',
    'Development.AutomorphicArithmetic.CharacterBoxes.EveryCharacter',
    'Development.AutomorphicArithmetic.CharacterBoxes.EveryCharacterStatement',
]


def git(repo: Path, *args: str) -> bytes:
    return subprocess.check_output(['git', '-C', str(repo), *args])


def mask_comments_and_strings(source: str) -> str:
    """Preserve newlines and characters outside comments/string literals."""
    parts: list[str] = []
    cursor = 0
    while match := TOKEN.search(source, cursor):
        parts.append(source[cursor:match.start()])
        end = match.end()
        if match.group() == '/-':
            depth = 1
            while depth:
                nested = COMMENT_TOKEN.search(source, end)
                if nested is None:
                    raise ValueError('unterminated Lean block comment')
                depth += 1 if nested.group() == '/-' else -1
                end = nested.end()
        removed = source[match.start():end]
        parts.append(''.join('\n' if char == '\n' else ' ' for char in removed))
        cursor = end
    parts.append(source[cursor:])
    return ''.join(parts)


def analyze(path: str, data: bytes) -> dict:
    source = data.decode('utf-8-sig')
    masked = mask_comments_and_strings(source)
    if EMPTY_IMPORT.search(masked):
        raise ValueError(f'{path}: multiline/empty import command needs parser support')
    imports = []
    locations = []
    for match in IMPORT.finditer(masked):
        words = match.group(1).split()
        if not words or any(not MODULE.fullmatch(word) for word in words):
            raise ValueError(f'{path}: unsupported import syntax: {match.group(0)!r}')
        for word in words:
            imports.append(word)
            locations.append({'module': word, 'line': masked.count('\n', 0, match.start()) + 1})
    rest = IMPORT.sub('', masked)
    rest = re.sub(r'^\s*prelude\s*$', '', rest, flags=re.M)
    lines = source.splitlines()
    return {
        'path': path,
        'imports': list(dict.fromkeys(imports)),
        'import_locations': locations,
        'physical_lines': len(lines),
        'nonblank_lines': sum(bool(line.strip()) for line in lines),
        'bytes': len(data),
        'sha256': hashlib.sha256(data).hexdigest(),
        'import_only': bool(imports) and not rest.strip(),
    }


def module_name(path: str) -> str:
    return path.removeprefix('src/').removesuffix('.lean').replace('/', '.')


def fetch_blobs(repo: Path, requests: list[tuple[str, str]]) -> dict[str, bytes]:
    if not requests:
        return {}
    proc = subprocess.Popen(['git', '-C', str(repo), 'cat-file', '--batch'],
                            stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    result = {}
    assert proc.stdin and proc.stdout
    for path, oid in requests:
        proc.stdin.write((oid + '\n').encode())
        proc.stdin.flush()
        fields = proc.stdout.readline().decode().split()
        if len(fields) != 3 or fields[1] != 'blob':
            raise RuntimeError(f'Unexpected cat-file header: {fields}')
        size = int(fields[2])
        content = proc.stdout.read(size)
        if len(content) != size or proc.stdout.read(1) != b'\n':
            raise RuntimeError('Truncated Git blob')
        result[path] = content
    proc.stdin.close()
    if proc.wait() != 0:
        raise RuntimeError('git cat-file failed')
    return result


def capture(repo: Path, ref: str) -> tuple[dict, dict, dict]:
    entries = git(repo, 'ls-tree', '-rz', ref, '--', 'src').split(b'\0')
    head_oids = {}
    for entry in entries:
        if not entry:
            continue
        meta, path_bytes = entry.split(b'\t', 1)
        path = path_bytes.decode()
        mode, kind, oid = meta.decode().split()
        if path.endswith('.lean'):
            if kind != 'blob' or mode not in ('100644', '100755'):
                raise ValueError(f'Unsupported Lean source entry: {entry!r}')
            head_oids[path] = oid
    del entries
    original, current = {}, {}
    changed, added = [], []
    seen = set()
    start = time.monotonic()
    count = 0
    for directory, dirs, files in os.walk(repo / 'src'):
        dirs.sort()
        for filename in sorted(files):
            if not filename.endswith('.lean'):
                continue
            full_path = Path(directory) / filename
            path = full_path.relative_to(repo).as_posix()
            data = full_path.read_bytes()
            info = analyze(path, data)
            module = module_name(path)
            current[module] = info
            seen.add(path)
            oid = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
            if head_oids.get(path) == oid:
                original[module] = info
            elif path in head_oids:
                changed.append(path)
            else:
                added.append(path)
            count += 1
            if count % 25000 == 0:
                print(f'Scanned {count:,} Lean files in {time.monotonic()-start:.1f}s',
                      file=sys.stderr, flush=True)
    deleted = sorted(set(head_oids) - seen)
    requests = [(path, head_oids[path]) for path in changed + deleted]
    for path, data in fetch_blobs(repo, requests).items():
        original[module_name(path)] = analyze(path, data)
    capture_info = {'changed': sorted(changed), 'added': sorted(added), 'deleted': deleted,
                    'head_source_files': len(head_oids), 'observed_source_files': len(current)}
    return original, current, capture_info


def closure(graph: dict, root: str, overrides: dict | None = None) -> tuple[set, set]:
    internal, external = set(), set()
    todo = [root]
    while todo:
        module = todo.pop()
        if module in internal or module in external:
            continue
        if module not in graph:
            external.add(module)
            continue
        internal.add(module)
        imports = overrides.get(module, graph[module]['imports']) if overrides else graph[module]['imports']
        todo.extend(imports)
    return internal, external


def totals(graph: dict, modules: set) -> dict:
    return {'modules': len(modules),
            **{key: sum(graph[module][key] for module in modules)
               for key in ('physical_lines', 'nonblank_lines', 'bytes')},
            'import_only_modules': sum(graph[module]['import_only'] for module in modules)}


def metrics(graph: dict, root: str, overrides: dict | None = None) -> dict:
    reached, external = closure(graph, root, overrides)
    return {**totals(graph, reached), 'root': root, 'includes_root': True,
            'direct_imports': (overrides.get(root, graph[root]['imports']) if overrides
                               else graph[root]['imports']),
            'external_imports': sorted(external)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--ref', default='7cbf7a0c32fca1badf05931879a37c3f8a2b03b4')
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    repo, output = args.repo.resolve(), args.out.resolve()
    output.mkdir(parents=True, exist_ok=True)
    started = dt.datetime.now(dt.timezone.utc).isoformat()
    commit = git(repo, 'rev-parse', args.ref).decode().strip()
    original, current, capture_info = capture(repo, commit)
    report = {
        'repository': str(repo), 'original_commit': commit,
        'capture_started_utc': started,
        'capture_finished_utc': dt.datetime.now(dt.timezone.utc).isoformat(),
        'scope': 'Repository src/*.lean only. Mathlib and other external imports are leaves.',
        'line_metrics': 'Physical source lines and nonblank source lines; comments included.',
        'capture': capture_info, 'versions': {}, 'main_import_simulations': {},
    }
    old_import = 'Supplements.Kernels.MainTheoremsAll'
    new_import = 'Supplements.Kernels.MainTheorems'
    for version, graph in [('original', original), ('working_tree', current)]:
        report['versions'][version] = {
            'whole_source': totals(graph, set(graph)),
            'targets': {root: metrics(graph, root) for root in TARGETS if root in graph},
        }
        imports = graph['Main']['imports']
        revised = [new_import if dep == old_import else dep for dep in imports]
        overrides = {'Main': list(dict.fromkeys(revised))}
        before, _ = closure(graph, 'Main')
        after, _ = closure(graph, 'Main', overrides)
        removed = before - after
        report['main_import_simulations'][version] = {
            'applies': old_import in imports,
            'before': metrics(graph, 'Main'), 'after': metrics(graph, 'Main', overrides),
            'removed_totals': totals(graph, removed),
            'removed_modules': [dict(module=mod, **graph[mod]) for mod in sorted(removed)],
        }
        with gzip.open(output / f'{version}-import-graph.json.gz', 'wt', encoding='utf-8') as stream:
            json.dump(graph, stream, ensure_ascii=False, sort_keys=True)
        (output / f'{version}-main-removed.txt').write_text('\n'.join(sorted(removed)) + '\n')
    (output / 'report.json').write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n')
    # Emit a compact human-readable summary; the full evidence is in report.json.
    print(json.dumps({
        'original_commit': commit, 'capture': capture_info,
        'targets': {version: {root: {k: values[k] for k in
                     ('modules', 'physical_lines', 'nonblank_lines', 'import_only_modules')}
                   for root, values in data['targets'].items()}
                   for version, data in report['versions'].items()},
        'main_import_removed': {version: data['removed_totals']
                                for version, data in report['main_import_simulations'].items()},
        'report': str(output / 'report.json'),
    }, indent=2))


if __name__ == '__main__':
    main()
