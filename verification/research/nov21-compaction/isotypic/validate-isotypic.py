#!/usr/bin/env python3
"""Check a snapshot of the final isotypic representation proof.
Expects the generic helper to have been compiled in fixed-vectors/output.
Compares the public theorem to the original proof's complete compiled type,
then replays the new theorem's proof/type closure into an empty kernel.
"""
from pathlib import Path
import hashlib,json,os,subprocess,time
HERE=Path(__file__).resolve().parent
REPO=HERE.parents[3]
BIN=Path('/workspace/principia-harness/a0564e7e/integration/.elan/toolchains/leanprover--lean4---v4.33.1/bin')
OUTPUT=HERE/'output';OUTPUT.mkdir(exist_ok=True)
SOURCE=REPO/'src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntertwiningMapNeZeroOfIsotypicIrreducible.lean'
HELPER=REPO/'src/Lemmata/IsotypicGeneration.lean'
helper_receipt=json.loads((HERE.parent/'fixed-vectors/IsotypicGeneration.json').read_text())
if helper_receipt['source_sha256']!=hashlib.sha256(HELPER.read_bytes()).hexdigest():raise RuntimeError('Generic helper source does not match compiled helper receipt')
SNAPSHOT=HERE/'IsoSepActual.lean';SNAPSHOT.write_bytes(SOURCE.read_bytes())
(HERE/'IsotypicGeneration.snapshot.lean').write_bytes(HELPER.read_bytes())
CHECKED=HERE/'IsoSepActualChecked.lean';CHECKED.write_text(SNAPSHOT.read_text()+'\n#print axioms GlobalTheory.IsoSep.main\n')
TARGET='GlobalTheory.IsoSep.main';MODULE='IsoSepActualChecked'
PREFIX=HERE.parent/'fixed-vectors/output'
CACHE=Path('/workspace/principia-harness/certificate-hour/matrix/project-cache/.lake/build/lib/lean')
paths=[OUTPUT,PREFIX,CACHE]+sorted((REPO/'.lake/packages').glob('*/.lake/build/lib/lean'))
env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,paths));env['PATH']=str(BIN)+os.pathsep+env['PATH']
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def run(label,command):
 start=time.monotonic();r=subprocess.run(list(map(str,command)),cwd=HERE,env=env,capture_output=True,text=True);log=r.stdout+r.stderr;(HERE/(label+'.log')).write_text(log)
 record={'exit_code':r.returncode,'seconds':time.monotonic()-start,'command':list(map(str,command)),'log_sha256':sha(HERE/(label+'.log'))};(HERE/(label+'.json')).write_text(json.dumps(record,indent=2)+'\n');print(label,record['exit_code'],f"{record['seconds']:.2f}s",flush=True)
 if r.returncode:print(log);raise SystemExit(r.returncode)
 return record
native=run('actual-native',[BIN/'lean','-j1','-s400000','-R',HERE,'-DautoImplicit=false','-DrelaxedAutoImplicit=false','-DmaxSynthPendingDepth=3','-DmaxHeartbeats=4000000','-o',OUTPUT/(MODULE+'.olean'),CHECKED])
ast=HERE/'original-type.ast';original=OUTPUT/'IsoSepOriginalChecked.olean';candidate=OUTPUT/(MODULE+'.olean')
types=run('actual-type-compare',[BIN/'lean','--run',HERE/'CompareIsotypicTypes.lean',original,candidate,ast])
replay=run('actual-kernel-replay',[BIN/'lean','-j1','-s400000','--run',HERE/'ReplayIsotypicCertificate.lean',MODULE,TARGET])
if SOURCE.read_bytes()!=SNAPSHOT.read_bytes():raise RuntimeError('Consumer source changed during validation')
if HELPER.read_bytes()!=(HERE/'IsotypicGeneration.snapshot.lean').read_bytes():raise RuntimeError('Helper source changed during validation')
record={'target':TARGET,'actual_source_path':str(SOURCE),'actual_source_sha256':sha(SNAPSHOT),'helper_source_sha256':sha(HELPER),'source_matches_snapshot_after_checks':True,'checked_source_sha256':sha(CHECKED),'candidate_olean_sha256':sha(candidate),'original_olean_sha256':sha(original),'exact_type_ast_sha256':sha(ast),'verifier_sha256':sha(HERE/'ReplayIsotypicCertificate.lean'),'helper_olean_sha256':sha(PREFIX/'Lemmata/IsotypicGeneration.olean'),'checks':{'native':native,'exact_type':types,'kernel_replay':replay},'scope':'targeted theorem compaction with unchanged compiled public type; no full Main/Comparator verdict'}
(HERE/'validation-summary.json').write_text(json.dumps(record,indent=2)+'\n');print('ALL TARGETED CHECKS PASSED')
