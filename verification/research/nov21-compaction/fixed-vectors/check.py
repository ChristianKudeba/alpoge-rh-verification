import os, subprocess, json, time, hashlib, sys
from pathlib import Path
repo=Path('/workspace/alpoge-compaction')
base=repo/'verification/research/nov21-compaction/fixed-vectors'
output=base/'output'
modules=['Lemmata.IsotypicGeneration','Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HasFixedVector','Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SubgroupFixed','Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrreducibleProjectionExists','Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedVectorsNeBotOfMemSumIntertwiningRanges']
env=os.environ.copy()
env['LEAN_PATH']=':'.join(map(str,[output,Path('/workspace/principia-harness/certificate-hour/matrix/project-cache/.lake/build/lib/lean')]+sorted((repo/'.lake/packages').glob('*/.lake/build/lib/lean'))))
bin=Path('/workspace/principia-harness/a0564e7e/integration/.elan/toolchains/leanprover--lean4---v4.33.1/bin')
archive=Path('/workspace/principia-harness/certificate-hour/matrix/project-cache/.lake/build/lib/lean')
selected={Path(*m.split('.')).with_suffix(ext) for m in modules for ext in ['.olean','.olean.private','.olean.server','.ilean']}
def mirror(src,dst):
    dst.mkdir(parents=True,exist_ok=True)
    for item in src.iterdir():
        relative=item.relative_to(archive);target=dst/item.name
        if relative in selected: continue
        if target.is_symlink() and any(relative in p.parents for p in selected): target.unlink()
        if target.is_symlink() or target.is_file(): continue
        if target.is_dir(): mirror(item,target)
        elif any(relative in p.parents for p in selected): mirror(item,target)
        else: target.symlink_to(item,target_is_directory=item.is_dir())
mirror(archive,output)
for module in (sys.argv[1:] or modules):
    name=module.split('.')[-1]
    relative=Path(*module.split('.'))
    src=repo/'src'/relative.with_suffix('.lean');out=output/relative.with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
    cmd=[str(bin/'lean'),'-j1','-s400000','-R',str(repo/'src'),'-DautoImplicit=false','-DrelaxedAutoImplicit=false','-DmaxSynthPendingDepth=3','-DmaxHeartbeats=4000000','-o',str(out),str(src)]
    start=time.monotonic();p=subprocess.run(cmd,cwd=repo,env=env,text=True,capture_output=True)
    log=p.stdout+p.stderr;(base/(name+'.log')).write_text(log)
    record={'module':module,'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'command':cmd,'exit_code':p.returncode,'seconds':time.monotonic()-start}
    (base/(name+'.json')).write_text(json.dumps(record,indent=2)+'\n');print(name,'exit',p.returncode,'seconds',record['seconds'],flush=True);print(log,flush=True)
    if p.returncode:raise SystemExit(p.returncode)
