from pathlib import Path
import json,re
ROOT=Path(__file__).resolve().parents[2]
LEAN=ROOT/'lean'
CAT=[]

def declaration(path,name,namespace):
 text=(LEAN/path).read_text()
 start=re.search(r'^theorem '+re.escape(name)+r'\b',text,re.M).start()
 end=re.search(r'\s:=\s',text[start:]).start()+start
 header=text[start:end]
 # Binder arguments preceding the top-level result colon.
 tail=header[len('theorem '+name):]
 args=[]
 while tail.lstrip().startswith(('(','{','[')):
  tail=tail.lstrip(); opener=tail[0]; closer={'(':')','{':'}','[':']'}[opener]
  stack=[closer]; i=1
  while stack:
   c=tail[i]
   if c in '({[':stack.append({'(':')','{':'}','[':']'}[c])
   elif c==stack[-1]:stack.pop()
   i+=1
  binding=tail[1:i-1];tail=tail[i:]
  if opener!='[':
   names=binding.split(':',1)[0].strip().split()
   if opener=='{':args += ['('+n+' := '+n+')' for n in names]
   else:args += names
 return header+' := by\n  exact '+namespace+'.'+name+(' '+' '.join(args) if args else '')+'\n'

def write_entry(id,title,status,imports,opens,custom,decls,summary,qualifications,origextra=[]):
 body='\n'.join('import '+m for m in imports)+'\n\n/-!\nSeparate typed proof interface for OEIS '+id+'.\nThe complete implementation is in the imported, preserved libraries.\nAI disclosure: ChatGPT (OpenAI) generated this presentation for Dev Goyal.\nIndependent human review of this consolidated presentation is pending.\n-/\n\nnamespace FinalCollection.'+id+'\n\nopen '+opens+'\n\n'+custom+'\n'
 for path,name,ns in decls:body+=declaration(path,name,ns)+'\n'
 body+='end FinalCollection.'+id+'\n'
 body=body.replace('open PowerSeries Hanna.Series Consecutive', 'open PowerSeries Consecutive\nopen Hanna.Series (Normalized compose compose_X_right)')
 (LEAN/'Entries'/f'{id}.lean').write_text(body)
 names=re.findall(r'^theorem ([A-Za-z_0-9]+)',body,re.M)
 CAT.append({'oeis_id':id,'title':title,'status':status,'source_url':'https://oeis.org/'+id,'manuscript_tex':f'manuscripts/{id}.tex','manuscript_pdf':f'manuscripts/{id}.pdf','lean_file':f'lean/Entries/{id}.lean','imported_modules':imports,'original_endpoints':list(dict.fromkeys(origextra+[ns+'.'+name for _,name,ns in decls])),'new_endpoints':['FinalCollection.'+id+'.'+n for n in names],'summary':summary,'qualifications':qualifications})

# Preserve all sixteen original theorem statements, under a separate entry namespace.
a=(LEAN/'Hanna/Acceptance.lean').read_text()
a=a.replace('namespace Hanna.Acceptance','namespace FinalCollection.A396843').replace('end Hanna.Acceptance','end FinalCollection.A396843').replace('open PowerSeries','open PowerSeries Hanna')
a=a.replace('namespace FinalCollection.A396843','/-! Separate typed interface for A396843 and its proved parameter family.\nThe original proof terms and complete library dependencies are retained.\nAI-generated consolidation for Dev Goyal; human review of this presentation is pending. -/\n\nnamespace FinalCollection.A396843')
a=a.replace('end FinalCollection.A396843','theorem a396843_parity (n : ℕ) (hn : 1 ≤ n) : Odd (a 3 n) := by\n  exact Hanna.Acceptance.parity_odd 3 (by decide) n hn\n\nend FinalCollection.A396843')
a='import Hanna.Acceptance\n'+a
(LEAN/'Entries/A396843.lean').write_text(a)
ns=re.findall(r'^theorem (\w+)',a,re.M)
CAT.append({'oeis_id':'A396843','title':'Parity and binary divisibility for A396843','status':'Original proof and generalizations; corrected modulo-nine classification','source_url':'https://oeis.org/A396843','manuscript_tex':'manuscripts/A396843.tex','manuscript_pdf':'manuscripts/A396843.pdf','lean_file':'lean/Entries/A396843.lean','imported_modules':['Hanna.Acceptance','Hanna.Corollaries','Hanna.Parity'],'original_endpoints':['Hanna.Acceptance.'+n for n in ns if n!='a396843_parity'],'new_endpoints':['FinalCollection.A396843.'+n for n in ns],'summary':'Oddness for m=3, parity for all integer parameters, exact residues modulo m squared, binary-digit divisibility for the series and its inverse, and the exact minimum prime-exponent criterion.','qualifications':'Original repository retained; new consolidation is AI-generated and awaits human review. Danial Asaria is credited for the prior counterexample to the false earlier modulo-nine claim. No new-priority claim.'})

h_custom='''theorem source_existence_uniqueness (R : Type*) [CommRing R] :
    ∃! U : PowerSeries R, Series.Normalized U ∧ Series.Psi (4 : R) U = X^2 := by
  exact Hanna.Acceptance.existence_uniqueness R 4

theorem even_positive_tail :
    a 4 1 = 1 ∧ ∀ n ≥ 2, (2 : ℤ) ∣ a 4 n := by
  exact Hanna.Acceptance.parity_even 4 (by decide)

theorem binary_divisibility (n : ℕ) (hn : 1 ≤ n) :
    (4 : ℤ)^binaryWeight (n-1) ∣ a 4 n := by
  exact Hanna.Acceptance.binary_divisibility_integer 4 (by decide) n hn
'''
write_entry('A396844','A corrected modulo-sixteen classification for A396844','Corrected all-index classification already contained in the original proof package',['Hanna.Acceptance'],'PowerSeries Hanna',h_custom,[('Hanna/Acceptance.lean','residues_parameter_four','Hanna.Acceptance')],'For n at least two, residue four at n=4^k+1, residue twelve at n=2*4^k+1, and zero otherwise modulo sixteen; includes parity and binary divisibility.','The original source claim omitted the first exceptional class. This is a corrected theorem, not a proof of that false clause.',['Hanna.Acceptance.existence_uniqueness','Hanna.Acceptance.parity_even','Hanna.Acceptance.binary_divisibility_integer','Hanna.Acceptance.inverse_binary_divisibility_integer','Hanna.Acceptance.minimum_prime_exponent_iff'])

for id,r,title in [('A396099',2,'Four congruence proofs for A396099'),('A396798',4,'Iterate congruences and a phase correction for A396798'),('A396807',5,'Every integer iterate of A396807 modulo ten'),('A396797',3,'A formalized known congruence theorem for A396797')]:
 custom=f'''theorem source_existence_uniqueness (R : Type*) [CommRing R] :
    ∃! F : PowerSeries R, Normalized F ∧ F = X + iter F {r} * iter F {r+1} := by
  exact Consecutive.existence_uniqueness {r}

theorem source_normalized : Normalized (solution (R:=ℤ) {r}) := by
  exact Consecutive.solution_normalized {r}

theorem source_equation :
    solution (R:=ℤ) {r} = X + iter (solution (R:=ℤ) {r}) {r} *
      iter (solution (R:=ℤ) {r}) {r+1} := by
  exact Consecutive.solution_equation {r}
'''
 if r==2:
  decls=[('Consecutive/Acceptance.lean','a396099_all_four','Consecutive')]+[('Consecutive/Coefficients.lean','a396099_'+s,'Consecutive') for s in ['odd','residue','period','second_iterate_series','second_iterate','difference_series','difference']]
  summary='All four source assertions: positive coefficients odd; residue cycle 1,3,3,1 from degree three modulo four; second-iterate coefficients vanish above degree two; the stated difference has residue two above degree two.'
  status='Four proved source conjectures'
 elif r==4:
  decls=[('Consecutive/Related.lean','a396798_'+s,'Consecutive') for s in ['iterate_residue','corrected_residue','corrected_period','counterexample','literal_period_false','second_iterate','fourth_iterate','sixth_iterate','eighth_iterate','third_iterate_period','fifth_iterate_period','seventh_iterate_period']]
  summary='Seven iterate assertions modulo eight, complete natural-iterate coefficient formula, and corrected coefficient block 1,1,5,5 beginning at degree two; false starting-at-one phase refuted.'
  status='Seven proved iterate assertions and a refutation/correction'
 else:
  if r==5:
   decls=[('Consecutive/Related.lean','a396807_residue','Consecutive'),('Consecutive/Related.lean','a396807_iterate_residue','Consecutive'),('Consecutive/IntegerIterates.lean','a396807_integer_iterate_congruence','Consecutive')]
   summary='Every positive-index coefficient is one modulo ten, and the degree-n coefficient of every integer compositional iterate k is k^(n-1) modulo ten.'
   status='Two proved source assertions, including negative iterates'
  else:
   decls=[]
   custom+='''
theorem integer_iterate_congruence (k : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    (integerIterateCoeff 3 k n : ZMod 6) = (k : ZMod 6)^(n-1) := by
  exact Consecutive.integerIterateCoeff_mod_odd 3 (by decide) k n hn

theorem positive_coefficients (n : ℕ) (hn : 1 ≤ n) :
    (a 3 n : ZMod 6) = 1 := by
  have h := Consecutive.integerIterateCoeff_mod_odd 3 (by decide) 1 n hn
  simpa [integerIterateCoeff, ziter, a, iter_succ, iter_zero, compose_X_right] using h
'''
   summary='The credited known r=3 case: positive coefficients are one modulo six and all integer iterates have coefficients k^(n-1) modulo six.'
   status='Formalization of a known result credited to Shiva Priyan Shanmuga Sundaram'
 custom+=f'''
theorem exact_composition_order (k : ℤ) :
    ziter (solution (R:=ZMod {2*r}) {r}) (solution_normalized {r}) k = X ↔
      ({2*r} : ℤ) ∣ k := by
  exact Consecutive.ziter_solution_mod_eq_X_iff {r} (by decide) k
'''
 extra=['Consecutive.existence_uniqueness','Consecutive.solution_normalized','Consecutive.solution_equation','Consecutive.ziter_solution_mod_eq_X_iff']
 if r==3:extra+=['Consecutive.integerIterateCoeff_mod','Consecutive.ziter_solution_mod']
 write_entry(id,title,status,['Consecutive'],'PowerSeries Hanna.Series Consecutive',custom,decls,summary,'All series are constructed from the source equation. General odd-parameter proof credits Sundaram\'s earlier r=3 result; no global novelty claim. Negative iterates use the genuine compositional inverse.',extra)

for id,q,word in [('A393856',4,'five'),('A393857',5,'six'),('A393858',6,'seven'),('A393859',7,'eight')]:
 custom=f'''theorem source_existence_uniqueness (R : Type*) [CommRing R] :
    ∃! F : PowerSeries R, Normalized F ∧
      compose F (X - X * scaleTail ({q} : R) F) = X := by
  exact Hanna.Related.ScaledInverse.existence_uniqueness ({q} : R)

theorem source_normalized : Normalized (scaledSolution ({q} : ℤ)) := by
  exact scaledSolution_normalized {q}

theorem source_equation :
    compose (scaledSolution ({q} : ℤ))
      (X - X * scaleTail ({q} : ℤ) (scaledSolution ({q} : ℤ))) = X := by
  exact scaledSolution_equation {q}
'''
 decls=[('Hanna/Related/ScaledInverse.lean',id.lower()+'_mod_'+word,'Hanna.Related.ScaledInverse')]
 if q%2==0:decls+=[('Hanna/Related/ScaledParity.lean',id.lower()+'_parity','Hanna.Related.ScaledInverse')]
 summary=f'Every positive-index coefficient is one modulo {q+1}.'+(' A coefficient is odd exactly when its index is a power of two.' if q%2==0 else '')
 write_entry(id,'Congruences for the scaled inverse series '+id,'Two proved source assertions' if q%2==0 else 'One proved source assertion',['Related'],'PowerSeries Hanna.Series Hanna.Related.ScaledInverse',custom,decls,summary,'The apparent division by the parameter is defined coefficientwise; no division in a residue ring is assumed. Source normalization and uniqueness are part of the checked interface.',['Hanna.Related.ScaledInverse.existence_uniqueness','Hanna.Related.ScaledInverse.scaledSolution_normalized','Hanna.Related.ScaledInverse.scaledSolution_equation','Hanna.Related.ScaledInverse.integer_mod_parameter_add_one']+(['Hanna.Related.ScaledInverse.integer_coeff_odd_iff'] if q%2==0 else []))
(ROOT/'catalogue/original_entries.json').write_text(json.dumps(CAT,indent=2)+'\n')
print('Created',len(CAT),'interfaces;',sum(len(c['new_endpoints']) for c in CAT),'named endpoints')
