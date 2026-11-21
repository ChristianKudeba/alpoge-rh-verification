#!/usr/bin/env python3
"""Reproduce the hosted-check bundle from exact archive and research sources."""
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2] / 'src'
order, seen = [], set()


def visit(module):
    if module in seen or module == 'Mathlib' or module.startswith('Mathlib.'):
        return
    seen.add(module)
    path = ROOT / (module.replace('.', '/') + '.lean')
    if not path.is_file():
        raise FileNotFoundError(f'Missing internal dependency {module}: {path}')
    for imported in re.findall(r'^import (\S+)\s*$', path.read_text(), re.M):
        visit(imported)
    order.append(module)


def block(path, text):
    text = re.sub(r'^import .*\n', '', text, flags=re.M)
    depth = len(re.findall(r'^(?:noncomputable )?section\b|^namespace\b', text, re.M))
    depth -= len(re.findall(r'^end\b', text, re.M))
    assert depth >= 0, (path, depth)
    return '\nsection\n-- Source: ' + path + '\n' + text.rstrip() + '\n' + 'end\n' * depth + 'end\n'


visit('Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN')
sources = [(module.replace('.', '/') + '.lean', ROOT / (module.replace('.', '/') + '.lean'))
           for module in order]
sources += [(name, HERE / name) for name in ['Joint/LengthBudget.lean',
            'Compaction/LengthCertificates.lean', 'Compaction/WindowCertificates.lean']]
header = '''set_option linter.all false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 4000000
'''
snippet = header + '\n'.join(block(name, path.read_text()) for name, path in sources)
assert len(snippet) <= 200000
manifest = {'archive_commit': 'c72f6d62e557ff255d079647554c7ba7fabdaa98',
            'sources': [{'path': name, 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
                        for name, path in sources],
            'snippet_sha256': hashlib.sha256(snippet.encode()).hexdigest(),
            'characters': len(snippet)}
expected = json.loads((HERE / 'bundle-manifest.json').read_text())
if manifest != expected:
    raise RuntimeError('Sources differ from the checked manifest; rerun Lean before updating evidence.')
bundle = 'import Mathlib\n' + snippet
if (HERE / 'checked-bundle.lean').read_text() != bundle:
    raise RuntimeError('Stored bundle differs from its exact source reconstruction.')
print(json.dumps({'reproduced': True, 'archive_modules': len(order),
                  'snippet_sha256': manifest['snippet_sha256']}))
