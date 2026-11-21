#!/usr/bin/env python3
"""Native check, exact original type comparison, and empty-kernel replay.
The pinned original archives must first be restored with restore-fixpi-cache.py.
This is a targeted theorem check, not a full Main/Comparator verdict.
"""
from pathlib import Path
import hashlib, json, os, subprocess, time
HERE=Path(__file__).resolve().parent
REPO=HERE.parents[3]
CACHE=Path('/workspace/principia-harness/certificate-hour/matrix/project-cache/.lake/build/lib/lean')
BIN=Path('/workspace/principia-harness/a0564e7e/integration/.elan/toolchains/leanprover--lean4---v4.33.1/bin')
TARGET='UpperTheory.Reformulated.B.Gr34.mem_UC'
MODULE='FixPiIffCandidateChecked'
OUTPUT=HERE/'build'; OUTPUT.mkdir(exist_ok=True)
source=HERE/'FixPiIffCandidate.lean'
checked=HERE/(MODULE+'.lean')
checked.write_text(source.read_text()+'\n#print axioms '+TARGET+'\n')
paths=[OUTPUT,CACHE]+sorted((REPO/'.lake/packages').glob('*/.lake/build/lib/lean'))
env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,paths));env['PATH']=str(BIN)+os.pathsep+env['PATH']
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def run(label,cmd):
 start=time.monotonic();r=subprocess.run(list(map(str,cmd)),cwd=HERE,env=env,capture_output=True,text=True)
 log=r.stdout+r.stderr;(HERE/(label+'.log')).write_text(log)
 record={'exit_code':r.returncode,'seconds':time.monotonic()-start,'command':list(map(str,cmd)),'log_sha256':sha(HERE/(label+'.log'))}
 (HERE/(label+'.json')).write_text(json.dumps(record,indent=2)+'\n')
 print(label,record['exit_code'],f"{record['seconds']:.2f}s",flush=True)
 if r.returncode:print(log);raise SystemExit(r.returncode)
 return record
native=run('fixpi-native',[BIN/'lean','-j1','-s400000','-R',HERE,'-DautoImplicit=false','-DrelaxedAutoImplicit=false','-DmaxSynthPendingDepth=3','-DmaxHeartbeats=4000000','-o',OUTPUT/(MODULE+'.olean'),checked])
original=CACHE/'Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/FixPiIff.olean'
ast=HERE/'fixpi-original-type.ast'
types=run('fixpi-type-compare',[BIN/'lean','--run',HERE/'CompareFixPiTypes.lean',original,OUTPUT/(MODULE+'.olean'),ast])
replay=run('fixpi-kernel-replay',[BIN/'lean','-j1','-s400000','--run',HERE/'ReplayFixPiCertificate.lean',MODULE,TARGET])
record={'target':TARGET,'candidate_source_sha256':sha(source),'checked_source_sha256':sha(checked),'candidate_olean_sha256':sha(OUTPUT/(MODULE+'.olean')),'original_olean_sha256':sha(original),'exact_type_ast_sha256':sha(ast),'verifier_sha256':sha(HERE/'ReplayFixPiCertificate.lean'),'checks':{'native':native,'exact_type':types,'kernel_replay':replay},'scope':'targeted statement/import cleanup; no full Main/Comparator verdict and no mathematical argument reduction claim'}
(HERE/'fixpi-validation-summary.json').write_text(json.dumps(record,indent=2)+'\n')
print('ALL TARGETED CHECKS PASSED')
