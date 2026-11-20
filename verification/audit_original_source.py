#!/usr/bin/env python3
"""Read pinned Git archive; lexical audit, not Lean verification."""
import collections
import hashlib
import json
import pathlib
import re
import subprocess
import tarfile
import time

REPO = pathlib.Path('/workspace/alpoge-compaction')
OUT = pathlib.Path('/workspace/principia-harness/a0564e7e/integration/source-audit.json')
PIN = '7cbf7a0c32fca1badf05931879a37c3f8a2b03b4'
START = re.compile(r'--|/-|"')
BLOCK = re.compile(r'/-|-/')
STRING = re.compile(r'"(?:[^"\\]|\\.)*"', re.S)
TOKENS = re.compile(r'\b(?:axiom|sorry|admit|unsafe|native_decide|implemented_by|extern|sorryAx|mkSorry|mkSyntheticSorry|ofReduceBool|trustCompiler|run_tac|run_cmd|run_elab|run_meta|elab|elab_rules|macro|macro_rules|syntax|initialize|builtin_initialize|skipKernelTC|skipKernelCheck|addDecl|addAndCompile|setEnv|modifyEnv|unchecked|trustLevel|axiomDecl)\b|\bKernel\.isDefEq\b|\bEnvironment\.add\b|#(?:eval|reduce|print)\b')
OPTIONS = re.compile(r'\bset_option\s+([^\s]+)\s+([^\s]+)')

def blank_noncode(text):
    """Blank comments and quoted strings while retaining positions/newlines."""
    chunks, pos = [], 0
    while m := START.search(text, pos):
        start = m.start()
        chunks.append(text[pos:start])
        if m.group() == '--':
            end = text.find('\n', m.end())
            end = len(text) if end < 0 else end
        elif m.group() == '/-':
            depth, end = 1, m.end()
            while depth:
                close = BLOCK.search(text, end)
                if close is None:
                    end = len(text)
                    break
                depth += 1 if close.group() == '/-' else -1
                end = close.end()
        else:
            close = STRING.match(text, start)
            end = close.end() if close else len(text)
        chunks.append(re.sub(r'[^\n]', ' ', text[start:end]))
        pos = end
    chunks.append(text[pos:])
    return ''.join(chunks)

sample = '/- axiom /- sorry -/ unsafe -/ theorem x := "admit" -- native_decide\naxiom y'
assert TOKENS.findall(blank_noncode(sample)) == ['axiom']
started = time.time()
proc = subprocess.Popen(['git', 'archive', '--format=tar', PIN], cwd=REPO, stdout=subprocess.PIPE)
counts, option_counts, hits, source_count, total_bytes = collections.Counter(), collections.Counter(), [], 0, 0
digest = hashlib.sha256()
special = {}
with tarfile.open(fileobj=proc.stdout, mode='r|') as archive:
    for member in archive:
        if not member.isfile():
            continue
        if member.name in ('src/Main.lean', 'README.md', 'lean-toolchain', 'lakefile.toml'):
            data = archive.extractfile(member).read()
            special[member.name] = data.decode('utf-8')
        elif member.name.startswith('src/') and member.name.endswith('.lean'):
            data = archive.extractfile(member).read()
        else:
            continue
        if not (member.name.startswith('src/') and member.name.endswith('.lean')):
            continue
        source_count += 1
        total_bytes += len(data)
        digest.update(member.name.encode() + b'\0' + hashlib.sha256(data).digest())
        text = data.decode('utf-8')
        code = blank_noncode(text)
        for match in TOKENS.finditer(code):
            line_no = code.count('\n', 0, match.start()) + 1
            line = text.splitlines()[line_no - 1]
            counts[match.group()] += 1
            hits.append({'path': member.name, 'line': line_no, 'token': match.group(), 'source_line': line})
        for match in OPTIONS.finditer(code):
            option_counts[' '.join(match.groups())] += 1
        if source_count % 25000 == 0:
            print(f'Audited {source_count} source files', flush=True)
if proc.wait() != 0:
    raise SystemExit('git archive failed')
result = {
    'schema': 1,
    'repository': 'https://github.com/CocoSgt/riemann-hypothesis-lean',
    'source_commit': PIN,
    'method': 'Read every original src/*.lean member directly from git archive at the pinned commit. Blank nested /- -/ comments, -- comments, and ordinary quoted strings, then scan fixed token patterns. No checkout files modified.',
    'scope': {'lean_files': source_count, 'bytes': total_bytes, 'ordered_path_and_sha256_digest': digest.hexdigest()},
    'scanned_pattern': TOKENS.pattern,
    'token_counts': dict(sorted(counts.items())),
    'set_options': dict(sorted(option_counts.items())),
    'findings': hits,
    'main_original': special.get('src/Main.lean'),
    'lean_toolchain_original': special.get('lean-toolchain'),
    'lakefile_original': special.get('lakefile.toml'),
    'limitations': [
        'This is lexical source inspection, not elaboration, a successful Lean build, an axiom dependency audit, or independent proof verification.',
        'Custom syntax, imported dependencies, toolchain/compiler trust, generated expressions, and parser edge cases require separate review.',
        'Quoted strings are omitted, including interpolated strings; custom elaborator and metaprogramming tokens remain separately reported.',
        'The scan is limited to the original repository src/*.lean files. It does not inspect the implementations of external Lean/Mathlib dependencies.',
        'Absence of a listed token is not evidence that the formal theorem has the intended mathematical meaning.'
    ],
    'elapsed_seconds': round(time.time() - started, 2),
}
OUT.write_text(json.dumps(result, indent=2, ensure_ascii=False) + '\n')
print(json.dumps({'output': str(OUT), 'scope': result['scope'], 'tokens': result['token_counts'], 'set_options': result['set_options'], 'seconds': result['elapsed_seconds']}, indent=2), flush=True)
