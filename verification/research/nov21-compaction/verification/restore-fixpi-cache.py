#!/usr/bin/env python3
"""Restore missing immutable original imports for the PR44 FixPiIff check.
This verifies archive identities, not their proof terms. Kernel replay is separate.
"""
from pathlib import Path
import concurrent.futures, hashlib, json, os, subprocess, time
HERE=Path(__file__).resolve().parent
CACHE=Path('/workspace/principia-harness/certificate-hour/matrix/project-cache')
DATA=json.load(open('/workspace/principia-harness/certificate-hour/matrix/cache-tools/module-artifacts.json'))
MODULES=json.loads((HERE/'fixpi-original-import-closure.json').read_text())['missing']
BIN=Path('/workspace/principia-harness/a0564e7e/integration/.elan/toolchains/leanprover--lean4---v4.33.1/bin')
def fetch(name):
 h,archive,expected=DATA[name]; out=CACHE/'archives'/archive
 if not out.exists() or hashlib.sha256(out.read_bytes()).hexdigest()!=expected:
  tmp=out.with_name(out.name+f'.fixpi-{os.getpid()}.tmp')
  subprocess.run(['curl','-fsS','--retry','2','-A','RiemannHypothesisCache/1.0','-o',str(tmp),'https://rh-cache.taucetiproject.org/artifacts/leanprover-community/riemann-hypothesis/'+archive.replace('.ltar','.art')],check=True)
  actual=hashlib.sha256(tmp.read_bytes()).hexdigest()
  if actual!=expected: raise RuntimeError(f'Archive digest mismatch for {name}: {actual}')
  tmp.replace(out)
 rel=Path(*name.split('.')); bases=[str(CACHE/'.lake/build'/kind/rel.parent) for kind in ['lib/lean','ir']]
 for b in bases:Path(b).mkdir(parents=True,exist_ok=True)
 return {'name':name,'sha256':expected,'bytes':out.stat().st_size,'file':str(out),'hash':h,'base':bases}
start=time.monotonic()
with concurrent.futures.ThreadPoolExecutor(max_workers=12) as pool: records=list(pool.map(fetch,MODULES))
jobs=[{k:r[k] for k in ['file','hash','base']} for r in records]
env=os.environ.copy();env['RUST_MIN_STACK']=str(64*1024*1024)
subprocess.run([str(BIN/'leantar'),'--jobs','4','-f','-x','-j','-'],input=json.dumps(jobs),text=True,cwd=CACHE,env=env,check=True)
(HERE/'fixpi-cache-restoration.json').write_text(json.dumps({'seconds':time.monotonic()-start,'total_archive_bytes':sum(r['bytes'] for r in records),'records':records},indent=2)+'\n')
print(json.dumps({'restored':len(records),'total_archive_bytes':sum(r['bytes'] for r in records),'seconds':time.monotonic()-start}))
