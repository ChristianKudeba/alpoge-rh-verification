from pathlib import Path
import os,subprocess,json,hashlib,time,sys
repo=Path('/workspace/alpoge-compaction');path=Path(sys.argv[1]).resolve();label=sys.argv[2] if len(sys.argv)>2 else path.stem
bin=Path('/workspace/principia-harness/a0564e7e/integration/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean')
paths=[Path('/workspace/principia-harness/certificate-hour/matrix/project-cache/.lake/build/lib/lean')]+sorted((repo/'.lake/packages').glob('*/.lake/build/lib/lean'))
env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,paths));out=path.parent/(label+'.olean')
cmd=[str(bin),'-j1','-s400000','-DautoImplicit=false','-DrelaxedAutoImplicit=false','-DmaxSynthPendingDepth=3','-DmaxHeartbeats=4000000','-R',str(path.parent),'-o',str(out),str(path)]
data=path.read_bytes();t=time.monotonic();r=subprocess.run(cmd,env=env,cwd=repo,capture_output=True,text=True)
(path.parent/(label+'.log')).write_text(r.stdout+r.stderr)
record={'source':str(path),'source_sha256':hashlib.sha256(data).hexdigest(),'command':cmd,'lean_path':paths and str(env['LEAN_PATH']),'exit_code':r.returncode,'seconds':time.monotonic()-t,'compiler':subprocess.check_output([str(bin),'--version'],text=True).strip()};(path.parent/(label+'.json')).write_text(json.dumps(record,indent=2)+'\n');print(r.stdout+r.stderr);print(json.dumps(record,indent=2));assert path.read_bytes()==data;sys.exit(r.returncode)
