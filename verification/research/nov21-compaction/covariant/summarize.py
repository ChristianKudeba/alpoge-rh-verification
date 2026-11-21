from pathlib import Path
import re,json,hashlib,subprocess,difflib
root=Path(__file__).parent;repo=Path('/workspace/alpoge-compaction')
entries=[
 ('basis-surjection','src/Formalism/SharpRestriction/LevelLetterCocycles/LevelKernelDetection/ExistsBasisOfSurjective.lean',['exists_linear_rightInverse_of_surjective','exists_basis_of_surjective'],'Projectivity supplies the section; a coproduct bijection supplies the kernel decomposition, replacing coordinate lifting and an explicit inverse pair.'),
 ('subspace-transport','src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsLinearEquivMapEqOfFinrankEq.lean',['exists_linearEquiv_map_eq_of_finrank_eq'],'Extend an isomorphism between equal-dimensional subspaces to the ambient space instead of choosing and identifying two complements.'),
 ('trans-tuple','src/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/NcSGLP.lean',['surj_equiv','pi_surj','trans_tuple','dual_apply_eq_sum_mul_single'],'Use ambient extension and duality to replace complement constructions, kernel rank/projection machinery, and an annihilator argument.'),
 ('trans-tuple/ncx','src/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/NcXGLP.lean',['surj_equiv','pi_surj','trans_tuple'],'Use the same ambient-extension and duality abstractions in the parallel proof.')]
def declarations(s):
 ms=list(re.finditer(r'^(private )?theorem ([^\s:({]+)',s,re.M));out={}
 for i,m in enumerate(ms):
  t=s[m.start():ms[i+1].start() if i+1<len(ms) else len(s)]
  t=re.split(r'^end\b',t,flags=re.M)[0].rstrip();cut=t.find(':= by')
  if cut<0: cut=t.find(':=')
  body=t[cut+len(':= by'):] if t[cut:].startswith(':= by') else t[cut+2:]
  out[m[2]]={'private':bool(m[1]),'statement':t[:cut],'proof_lines':sum(bool(x.strip()) for x in body.splitlines())}
 return out
out={'base_commit':'6186b8d5c272c08c90f6f5cce1a25d22232ed78d','compiler':'Lean 4.33.1 (819816b2e0a3bf405af45ae5c7af2491d8f5bee6)','mathlib_pin':'0df444a360eaa60ab8c11dca51a86af692955474','axioms':['propext','Classical.choice','Quot.sound'],'files':[]}
for folder,rel,names,mechanism in entries:
 p=root/folder;a=(p/'original.lean').read_bytes();b=(p/'candidate.lean').read_bytes();assert (repo/rel).read_bytes()==b
 sa,sb=declarations(a.decode()),declarations(b.decode());assert all(n in sb and sa[n]['statement']==sb[n]['statement'] for n in sa if not sa[n]['private'])
 assert re.findall(r'^import .*$',a.decode(),re.M)==re.findall(r'^import .*$',b.decode(),re.M)
 changed=[]
 for n in names:
  old=sa[n];new=sb.get(n)
  if new: assert old['statement']==new['statement']
  changed.append({'name':n,'private':old['private'],'old_proof_lines':old['proof_lines'],'new_proof_lines':new['proof_lines'] if new else 0,'status':'replaced' if new else 'unused_private_helper_removed'})
 f={'source':rel,'evidence':folder,'mechanism':mechanism,'old_lines':len(a.splitlines()),'new_lines':len(b.splitlines()),'old_bytes':len(a),'new_bytes':len(b),'original_sha256':hashlib.sha256(a).hexdigest(),'candidate_sha256':hashlib.sha256(b).hexdigest(),'public_statements_byte_identical':True,'imports_identical':True,'changed_declarations':changed}
 out['files'].append(f);(p/'final.diff').write_text(''.join(difflib.unified_diff(a.decode().splitlines(True),b.decode().splitlines(True),fromfile='a/'+rel,tofile='b/'+rel)))
out['total_old_lines']=sum(f['old_lines'] for f in out['files']);out['total_new_lines']=sum(f['new_lines'] for f in out['files']);out['total_lines_saved']=out['total_old_lines']-out['total_new_lines'];out['total_bytes_saved']=sum(f['old_bytes']-f['new_bytes'] for f in out['files']);out['changed_proof_lines_before']=sum(d['old_proof_lines'] for f in out['files'] for d in f['changed_declarations']);out['changed_proof_lines_after']=sum(d['new_proof_lines'] for f in out['files'] for d in f['changed_declarations']);out['proof_lines_saved']=out['changed_proof_lines_before']-out['changed_proof_lines_after'];out['verbose_statement_compression_lines']=0
out['verification_scope']='Native recompilation of all four complete modules, plus two-copy rfl equality checks for all changed public statements. Pinned cached dependencies are loaded; this is not a fresh full-project Comparator run.'
(root/'manifest.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
