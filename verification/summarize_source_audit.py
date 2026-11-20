#!/usr/bin/env python3
"""Add manually reviewed interpretations and exact pinned-source provenance."""
import json
import pathlib
import re
import subprocess

ROOT = pathlib.Path('/workspace/principia-harness/a0564e7e/integration')
REPO = '/workspace/alpoge-compaction'
PIN = '7cbf7a0c32fca1badf05931879a37c3f8a2b03b4'
audit = json.loads((ROOT / 'source-audit.json').read_text())
def original(path):
    return subprocess.check_output(['git', 'show', f'{PIN}:{path}'], cwd=REPO).decode()

audit['zero_observed_tokens'] = [token for token in (
    'axiom', 'sorry', 'admit', 'unsafe', 'native_decide', 'implemented_by', 'extern',
    'sorryAx', 'mkSorry', 'mkSyntheticSorry', 'ofReduceBool', 'trustCompiler',
    'skipKernelTC', 'skipKernelCheck', 'axiomDecl', 'trustLevel', 'setEnv',
    'run_elab', 'run_meta', 'initialize', 'builtin_initialize'
) if audit['token_counts'].get(token, 0) == 0]
audit['reviewed_findings'] = [
    {
        'category': 'custom elaborators',
        'paths': [
            'src/Formalism/LocalToGlobal/IndefiniteReal/HeckeNonvanishing/Imports.lean',
            'src/Formalism/LocalToGlobal/NumberFieldFamilies/OwnStruct.lean',
            'src/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutCptCopy.lean'
        ],
        'assessment': 'kexactB elaborates a term and assigns it to a goal. kcopy recursively builds terms by projections/constructors and assigns them; its probe calls Kernel.isDefEq. cpt_copy_thms substitutes names in existing definition/theorem types and values, then calls addDecl for defnDecl/thmDecl. These are material metaprogramming audit points; their presence alone is not evidence of an unchecked axiom. Successful kernel checking was not established.'
    },
    {
        'category': 'environment mutation',
        'paths': [f'src/BuildAid/D{i}.lean' for i in range(1, 6)],
        'assessment': 'The five run_cmd/modifyEnv occurrences add namespace strings to Lean.LibrarySuggestions.nameDenyListExt. They do not visibly add theorem or axiom declarations.'
    },
    {
        'category': 'tactic metaprograms',
        'assessment': 'Of 32 run_tac occurrences, 30 use liftMetaTactic/revertAll followed by exact an existing declaration. FramesTildeGammaValues.lean constructs a Subsingleton.elim proof and notes it. ExistsGIs.lean assigns the local hypothesis h to the goal. This source inspection does not establish kernel acceptance of the resulting terms.'
    },
    {
        'category': 'syntax macros',
        'assessment': '87 macro keyword occurrences are recorded. Inspected declarations expand quoted Lean term/tactic syntax, including wrappers around kexactB. This is a lexical inventory, not a proof that every macro is semantically faithful.'
    },
    {
        'category': 'reducibility and elaboration options',
        'assessment': '37 allowUnsafeReducibility true occurrences are present. Other audit-relevant options include hygiene false (31), quotPrecheck false (7), and backward.isDefEq.respectTransparency false (1877). These are not the debug.skipKernelTC option; this audit does not infer successful kernel verification from that distinction.'
    }
]
audit['main_exported_theorems'] = [
    {'name': name, 'type': ty.strip(), 'proof': proof.strip()}
    for name, ty, proof in re.findall(r'^theorem (\S+) : (.*?) := (.*)$', audit['main_original'], re.M)
]
assert len(audit['main_exported_theorems']) == 5
audit['statements_original'] = original('src/Statements.lean')
audit['main_theorems_original'] = original('src/Supplements/Kernels/MainTheorems.lean')
readme = original('README.md').splitlines()
tree = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', PIN], cwd=REPO).decode().splitlines()
licenses = [p for p in tree if re.search(r'(^|/)(LICENSE|COPYING|COPYRIGHT)([.-].*)?$', p, re.I)]
audit['provenance'] = {
    'readme_excerpt': [{'line': i+1, 'text': line} for i, line in enumerate(readme) if i+1 in (1,3,4,5,9,10,11,13,101,170,172)],
    'license_named_files': licenses,
    'assessment': 'The README attributes the mathematics and Lean code to Levent Alpöge working with Claude. It says no independent build/review had been published as of mirroring, asserts byte-for-byte correspondence to the original archive, and states the original archive had no stated license and this mirror adds none. This audit has not independently compared the original web archive. A permissive redistribution license is not established; preserve the attribution/no-license notice and do not relicense the source as Apache/MIT without a separate grant.'
}
problem_path = 'src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ComplexFormsBaseLevelLeSpanIntegral.lean'
audit['syntax_candidate_for_compiler_check'] = {
    'path': problem_path,
    'line': 11,
    'source_line': original(problem_path).splitlines()[10],
    'assessment': 'The exact numeral/open token adjacency was accepted by the hosted scratch check 890bbe89daf06855732d4923dfb2c327. The probe defined Foo.x, used set_option maxHeartbeats 1600000open Foo, and #check x resolved Foo.x. This is not a syntax defect. The full source file and imports were not compiled.',
    'hosted_check_id': '890bbe89daf06855732d4923dfb2c327',
    'hosted_check_result': 'closed',
    'hosted_check_sorries': 0,
    'hosted_check_axioms': [],
    'probe_file': 'source-lexical-probe.lean',
    'probe_result_file': 'source-lexical-probe-result.json'
}
audit['conclusion'] = 'No direct occurrence of the listed axiom/sorry/admit/unsafe/native_decide/kernel-skip tokens was found in the scanned original source after masking comments/strings. Custom metaprogramming and unsafe-reducibility options are present and documented. This does not establish a complete proof, intended semantics, absence of unlisted trust mechanisms, or an independently verified build. The five public theorem signatures and source provenance were checked textually.'
(ROOT / 'source-audit.json').write_text(json.dumps(audit, indent=2, ensure_ascii=False) + '\n')
print(json.dumps({'report': str(ROOT/'source-audit.json'), 'findings': len(audit['findings']), 'main_theorems': len(audit['main_exported_theorems']), 'source_files': audit['scope']['lean_files']}, indent=2))
