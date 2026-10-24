import Hanna.Series.Triangular
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# The three congruences for OEIS A355872

The bilateral theta source is defined coefficientwise as a locally finite sum.
Its unique integral solution is constructed before any residue calculation.

AI-generated proofs and formalization by ChatGPT (OpenAI) for Dev D. Goyal.
Sequence and conjectures: Paul D. Hanna, OEIS A355872, 9 August 2022.
-/

namespace Families.BilateralTheta

set_option maxRecDepth 4096

open PowerSeries Hanna.Series

noncomputable section

attribute [local instance] Classical.propDecidable

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The literal summand for the integer index m. Natural absolute values only
express the nonnegative integer exponents m² and (m−1)². -/
def term (A : PowerSeries R) (m : ℤ) : PowerSeries R :=
  (-X)^(m.natAbs^2)*A^((m-1).natAbs^2)

@[simp] theorem term_zero (A : PowerSeries R) : term A 0=A := by simp [term]
@[simp] theorem term_one (A : PowerSeries R) : term A 1=-X := by simp [term]
@[simp] theorem term_two (A : PowerSeries R) : term A 2=X^4*A := by
  norm_num [term, neg_pow]

def window (n : ℕ) : Finset ℤ := Finset.Icc (-(n+1 : ℕ) : ℤ) (n+1)

theorem term_vanish (A : PowerSeries R) (m : ℤ) (n : ℕ)
    (hn : n<m.natAbs^2) : coeff R n (term A m)=0 := by
  have hd : (X : PowerSeries R)^(m.natAbs^2) ∣ term A m := by
    rw [term, neg_pow]
    exact dvd_mul_of_dvd_left (dvd_mul_left ((X : PowerSeries R)^(m.natAbs^2)) _) _
  exact X_pow_dvd_iff.mp hd n hn

theorem outside_window_vanish (A : PowerSeries R) (m : ℤ) (n : ℕ)
    (hm : m∉window n) : coeff R n (term A m)=0 := by
  apply term_vanish
  have habs : n+1<m.natAbs := by
    simp only [window, Finset.mem_Icc, not_and_or] at hm
    have hp := Int.natCast_natAbs m
    omega
  nlinarith

/-- The literal bilateral sum, evaluated by a provably sufficient finite window. -/
def bilateral (A : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => ∑ m ∈ window n, coeff R n (term A m)

@[simp] theorem bilateral_coeff (A : PowerSeries R) (n : ℕ) :
    coeff R n (bilateral A)=∑ m ∈ window n, coeff R n (term A m) := by
  simp [bilateral]

theorem bilateral_coeff_finsum (A : PowerSeries R) (n : ℕ) :
    coeff R n (bilateral A)=∑ᶠ m : ℤ, coeff R n (term A m) := by
  rw [bilateral_coeff]
  symm
  apply finsum_eq_sum_of_support_subset
  intro m hm
  by_contra hn
  exact hm (outside_window_vanish A m n hn)

def step (A : PowerSeries R) : PowerSeries R := X-(bilateral A-A)

theorem source_iff_fixed (A : PowerSeries R) : bilateral A=X ↔ A=step A := by
  unfold step
  constructor <;> intro h <;> linear_combination h

theorem term_dvd_sub (n : ℕ) (m : ℤ) (hm : m≠0)
    (A B : PowerSeries R) (hd : (X : PowerSeries R)^n ∣ A-B) :
    X^(n+1) ∣ term A m-term B m := by
  have hp := hd.trans (sub_dvd_pow_sub_pow A B ((m-1).natAbs^2))
  have he : (X : PowerSeries R)^1 ∣ (-X)^(m.natAbs^2) := by
    have hpos : 0<m.natAbs := Int.natAbs_pos.mpr hm
    have hh : (X : PowerSeries R)^1 ∣ X^(m.natAbs^2) :=
      pow_dvd_pow X (by nlinarith)
    rw [neg_pow]
    exact dvd_mul_of_dvd_right hh ((-1 : PowerSeries R)^(m.natAbs^2))
  have hh := mul_dvd_mul he hp
  rw [← pow_add] at hh
  simpa only [term, ← mul_sub, Nat.add_comm] using hh

theorem step_contraction (n : ℕ) (A B : PowerSeries R)
    (hd : (X : PowerSeries R)^n ∣ A-B) : X^(n+1) ∣ step A-step B := by
  apply X_pow_dvd_iff.mpr
  intro k hk
  have hs : coeff R k (bilateral A)-coeff R k (bilateral B)=coeff R k A-coeff R k B := by
    simp only [bilateral_coeff, ← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro m _ hm
      have hv := X_pow_dvd_iff.mp (term_dvd_sub n m hm A B hd) k hk
      simpa only [map_sub] using hv
    · intro hm
      exact False.elim (hm (by simp only [window, Finset.mem_Icc]; constructor <;> omega))
  simp only [step, map_sub]
  linear_combination -hs

theorem recursion_triangular :
    Triangular (fun a n => coeff R n (PowerSeries.mk a-step (PowerSeries.mk a))) := by
  intro n a b hab
  have hd : (X : PowerSeries R)^n ∣ PowerSeries.mk a-PowerSeries.mk b := by
    apply X_pow_dvd_iff.mpr
    intro k hk
    simp only [map_sub,coeff_mk]
    exact sub_eq_zero.mpr (hab k hk)
  have hp := X_pow_dvd_iff.mp (step_contraction n _ _ hd) n (by omega)
  simp only [map_sub, coeff_mk] at hp ⊢
  linear_combination -hp

theorem existence_uniqueness : ∃! A : PowerSeries R, bilateral A=X := by
  let op := fun a n => coeff R n (PowerSeries.mk a-step (PowerSeries.mk a))
  obtain ⟨a,ha,hu⟩ := triangular_existsUnique op recursion_triangular (fun _ => 0)
  have he : PowerSeries.mk a=step (PowerSeries.mk a) := by
    ext n
    have h := congrFun ha n
    change coeff R n (PowerSeries.mk a-step (PowerSeries.mk a))=0 at h
    simpa only [map_sub, sub_eq_zero] using h
  refine ⟨PowerSeries.mk a,(source_iff_fixed _).mpr he,?_⟩
  intro B hB
  have hb : (fun n => coeff R n B)=a := by
    apply hu
    funext n
    change coeff R n (PowerSeries.mk (fun n => coeff R n B)-
      step (PowerSeries.mk (fun n => coeff R n B)))=0
    have hm : PowerSeries.mk (fun n => coeff R n B)=B := by ext; simp
    rw [hm, ← (source_iff_fixed B).mp hB, sub_self, map_zero]
  ext n
  simpa only [coeff_mk] using congrFun hb n

def solution : PowerSeries R := existence_uniqueness.exists.choose

theorem solution_source : bilateral (solution : PowerSeries R)=X :=
  existence_uniqueness.exists.choose_spec

theorem solution_unique {A : PowerSeries R} (he : bilateral A=X) : A=solution :=
  existence_uniqueness.unique he solution_source

theorem map_term (f : R →+* S) (A : PowerSeries R) (m : ℤ) :
    PowerSeries.map f (term A m)=term (PowerSeries.map f A) m := by
  simp only [term, map_mul, map_pow, map_neg, PowerSeries.map_X]

theorem map_bilateral (f : R →+* S) (A : PowerSeries R) :
    PowerSeries.map f (bilateral A)=bilateral (PowerSeries.map f A) := by
  ext n
  simp only [coeff_map, bilateral_coeff, map_sum]
  apply Finset.sum_congr rfl
  intro m _
  exact (coeff_map f n (term A m)).symm.trans
    (congrArg (coeff S n) (map_term f A m))

theorem map_solution (f : R →+* S) :
    PowerSeries.map f (solution : PowerSeries R)=(solution : PowerSeries S) := by
  apply solution_unique
  rw [← map_bilateral, solution_source, PowerSeries.map_X]

/-- All nonzero coefficients lie in one residue class of degrees modulo four. -/
def Supported (r : ℕ) (A : PowerSeries R) : Prop :=
  ∀ n : ℕ, n%4≠r%4 → coeff R n A=0

theorem supported_X : Supported 1 (X : PowerSeries R) := by
  intro n hn
  rw [coeff_X,if_neg]
  intro he
  subst n
  exact hn rfl

theorem Supported.add {r : ℕ} {A B : PowerSeries R}
    (hA : Supported r A) (hB : Supported r B) : Supported r (A+B) := by
  intro n hn
  simp only [map_add,hA n hn,hB n hn,add_zero]

theorem Supported.neg {r : ℕ} {A : PowerSeries R}
    (hA : Supported r A) : Supported r (-A) := by
  intro n hn
  simp only [map_neg,hA n hn,neg_zero]

theorem Supported.sub {r : ℕ} {A B : PowerSeries R}
    (hA : Supported r A) (hB : Supported r B) : Supported r (A-B) := by
  simpa only [sub_eq_add_neg] using hA.add hB.neg

theorem Supported.mul {r s : ℕ} {A B : PowerSeries R}
    (hA : Supported r A) (hB : Supported s B) : Supported (r+s) (A*B) := by
  intro n hn
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨i,j⟩ hij
  have he : i+j=n := Finset.mem_antidiagonal.mp hij
  by_cases hi : i%4=r%4
  · have hj : j%4≠s%4 := by
      intro hj
      apply hn
      rw [←he,Nat.add_mod,hi,hj,←Nat.add_mod]
    rw [hB j hj,mul_zero]
  · rw [hA i hi,zero_mul]

theorem Supported.pow {r : ℕ} {A : PowerSeries R}
    (hA : Supported r A) (k : ℕ) : Supported (r*k) (A^k) := by
  induction k with
  | zero =>
    intro n hn
    rw [pow_zero,coeff_one,if_neg]
    intro he
    subst n
    exact hn rfl
  | succ k ih =>
    simpa only [pow_succ,Nat.mul_succ] using ih.mul hA

theorem square_index_mod_four (m : ℤ) :
    (m.natAbs^2+(m-1).natAbs^2)%4=1 := by
  have hs (z : ℤ) : ((z.natAbs : ZMod 4)^2)=(z : ZMod 4)^2 := by
    have h := congrArg (Int.castRingHom (ZMod 4)) (Int.natAbs_sq z)
    simpa only [map_pow,map_natCast,map_intCast] using h
  have h : ((m.natAbs^2+(m-1).natAbs^2 : ℕ) : ZMod 4)=1 := by
    simp only [Nat.cast_add,Nat.cast_pow,hs,Int.cast_sub,Int.cast_one]
    exact (by decide : ∀ t : ZMod 4, t^2+(t-1)^2=1) (m : ZMod 4)
  have hv := congrArg ZMod.val h
  simpa only [ZMod.val_natCast,show (1 : ZMod 4).val=1 by decide] using hv

theorem term_supported {A : PowerSeries R} (hA : Supported 1 A) (m : ℤ) :
    Supported 1 (term A m) := by
  have h := ((supported_X (R:=R)).neg.pow (m.natAbs^2)).mul
    (hA.pow ((m-1).natAbs^2))
  simp only [Nat.one_mul] at h
  intro n hn
  exact h n (by simpa only [square_index_mod_four] using hn)

theorem bilateral_supported {A : PowerSeries R} (hA : Supported 1 A) :
    Supported 1 (bilateral A) := by
  intro n hn
  rw [bilateral_coeff]
  apply Finset.sum_eq_zero
  intro m _
  exact term_supported hA m n hn

theorem step_supported {A : PowerSeries R} (hA : Supported 1 A) :
    Supported 1 (step A) :=
  supported_X.sub ((bilateral_supported hA).sub hA)

def approximation : ℕ → PowerSeries R
  | 0 => 0
  | k+1 => step (approximation k)

theorem approximation_supported (k : ℕ) : Supported 1 (approximation k : PowerSeries R) := by
  induction k with
  | zero => intro n _; simp [approximation]
  | succ k ih => exact step_supported ih

theorem approximation_agrees (k : ℕ) :
    (X : PowerSeries R)^k ∣ solution-approximation k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs : (solution : PowerSeries R)=step solution := (source_iff_fixed _).mp solution_source
    simpa only [approximation,←hs,Nat.succ_eq_add_one] using
      step_contraction k solution (approximation k) ih

theorem solution_supported : Supported 1 (solution : PowerSeries R) := by
  intro n hn
  have h := X_pow_dvd_iff.mp (approximation_agrees (R:=R) (n+1)) n (by omega)
  simpa only [map_sub,approximation_supported (n+1) n hn,sub_zero] using h

theorem solution_constant : constantCoeff R (solution : PowerSeries R)=0 := by
  simpa only [coeff_zero_eq_constantCoeff_apply] using solution_supported (R:=R) 0 (by decide)

/-- A sparse integral rational series X/(1+X⁴). -/
def alternating : PowerSeries R :=
  PowerSeries.mk fun n => if n%4=1 then (-1)^(n/4) else 0

@[simp] theorem alternating_coeff (n : ℕ) :
    coeff R n (alternating : PowerSeries R)=if n%4=1 then (-1)^(n/4) else 0 := by
  simp [alternating]

theorem alternating_coeff_shift (n : ℕ) :
    coeff R (n+4) (alternating : PowerSeries R)=-coeff R n alternating := by
  have hm : (n+4)%4=n%4 := by omega
  have hd : (n+4)/4=n/4+1 := by omega
  simp only [alternating_coeff,hm,hd,pow_succ]
  split_ifs <;> ring

theorem alternating_equation :
    (alternating : PowerSeries R)+X^4*alternating=X := by
  ext n
  by_cases hn : n<4
  · interval_cases n <;> norm_num [alternating, coeff_X_pow_mul',coeff_X]
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (by omega : 4≤n)
    rw [Nat.add_comm 4 k, map_add, coeff_X_pow_mul, alternating_coeff_shift]
    simp [coeff_X,show k+4≠1 by omega]

/-- The comparison series 2X/(1+X⁴), defined independently of the source. -/
def comparison : PowerSeries R := 2*alternating

theorem comparison_equation :
    (comparison : PowerSeries R)+X^4*comparison=2*X := by
  have h := congrArg (fun U : PowerSeries R => 2*U) alternating_equation
  simpa only [comparison, mul_add, mul_assoc, mul_left_comm] using h

theorem comparison_fourth_zero : (comparison : PowerSeries (ZMod 8))^4=0 := by
  have hn : (16 : PowerSeries (ZMod 8))=0 := by
    simpa only [map_ofNat,map_zero] using congrArg (C (ZMod 8)) (by decide : (16 : ZMod 8)=0)
  rw [comparison,mul_pow,show (2 : PowerSeries (ZMod 8))^4=16 by ring,hn,zero_mul]

theorem comparison_fourth_zero_sixteen : (comparison : PowerSeries (ZMod 16))^4=0 := by
  have hn : (16 : PowerSeries (ZMod 16))=0 := by
    simpa only [map_ofNat,map_zero] using congrArg (C (ZMod 16)) (by decide : (16 : ZMod 16)=0)
  rw [comparison,mul_pow,show (2 : PowerSeries (ZMod 16))^4=16 by ring,hn,zero_mul]

theorem term_nilpotent (A : PowerSeries R) (hA : A^4=0) (m : ℤ)
    (h0 : m≠0) (h1 : m≠1) (h2 : m≠2) : term A m=0 := by
  have hp : 2≤(m-1).natAbs := by
    have ha := Int.natCast_natAbs (m-1)
    omega
  have he : 4≤(m-1).natAbs^2 := by nlinarith
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le he
  simp only [term,hk,pow_add,hA,zero_mul,mul_zero]

theorem bilateral_of_fourth_zero (A : PowerSeries R) (hA : A^4=0) :
    bilateral A=A-X+X^4*A := by
  ext n
  rw [bilateral_coeff_finsum]
  have he : (∑ᶠ m : ℤ, coeff R n (term A m))=
      ∑ m ∈ ({0,1,2} : Finset ℤ), coeff R n (term A m) := by
    apply finsum_eq_sum_of_support_subset
    intro m hm
    by_contra h
    simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton,not_or] at h
    exact hm (by
      change coeff R n (term A m)=0
      rw [term_nilpotent A hA m h.1 h.2.1 h.2.2,map_zero])
  rw [he]
  simp [sub_eq_add_neg, add_assoc]

theorem solution_mod_eight : (solution : PowerSeries (ZMod 8))=comparison := by
  symm
  apply solution_unique
  rw [bilateral_of_fourth_zero comparison comparison_fourth_zero]
  have h := comparison_equation (R:=ZMod 8)
  linear_combination h

theorem solution_mod_sixteen : (solution : PowerSeries (ZMod 16))=comparison := by
  symm
  apply solution_unique
  rw [bilateral_of_fourth_zero comparison comparison_fourth_zero_sixteen]
  have h := comparison_equation (R:=ZMod 16)
  linear_combination h

/-- Coefficients of the actual unique integer source series. -/
def a (n : ℕ) : ℤ := coeff ℤ (4*n-3) solution

theorem source_coefficient_expansion (n : ℕ) :
    coeff ℤ n solution=∑ᶠ k : ℕ, coeff ℤ n (C ℤ (a (k+1))*X^(4*k+1)) := by
  by_cases hn : n%4=1
  · have he : n=4*(n/4)+1 := by omega
    have hf : (∑ᶠ k : ℕ, coeff ℤ n (C ℤ (a (k+1))*X^(4*k+1)))=
        ∑ k ∈ ({n/4} : Finset ℕ), coeff ℤ n (C ℤ (a (k+1))*X^(4*k+1)) := by
      apply finsum_eq_sum_of_support_subset
      intro k hk
      by_contra h
      have hneq : n≠4*k+1 := by
        simp only [Finset.mem_coe,Finset.mem_singleton] at h
        omega
      apply hk
      change coeff ℤ n (C ℤ (a (k+1))*X^(4*k+1))=0
      rw [coeff_C_mul,coeff_X_pow,if_neg hneq,mul_zero]
    rw [hf]
    have hidx : 4*(n/4+1)-3=n := by omega
    simp only [Finset.sum_singleton,coeff_C_mul,coeff_X_pow,if_pos he,mul_one,a,hidx]
  · rw [solution_supported n (by simpa using hn)]
    symm
    apply finsum_eq_zero_of_forall_eq_zero
    intro k
    have hneq : n≠4*k+1 := by omega
    rw [coeff_C_mul,coeff_X_pow,if_neg hneq,mul_zero]

theorem solution_coeff_mod_eight (n : ℕ) :
    ((coeff ℤ n solution : ℤ) : ZMod 8)=
      if n%4=1 then 2*(-1)^(n/4) else 0 := by
  have h := congrArg (coeff (ZMod 8) n) (map_solution (Int.castRingHom (ZMod 8)))
  rw [coeff_map,solution_mod_eight,comparison,two_mul,map_add,alternating_coeff] at h
  change ((coeff ℤ n solution : ℤ) : ZMod 8)=_ at h
  split_ifs with hn
  · rw [if_pos hn] at h
    simpa only [two_mul] using h
  · rw [if_neg hn] at h
    simpa using h

theorem a_shift_mod_eight (n : ℕ) : (a (n+1) : ZMod 8)=2*(-1)^n := by
  have h : 4*(n+1)-3=4*n+1 := by omega
  have hd : (4*n+1)/4=n := by omega
  simp only [a,h,solution_coeff_mod_eight]
  simp [hd]

theorem solution_coeff_mod_sixteen (n : ℕ) :
    ((coeff ℤ n solution : ℤ) : ZMod 16)=
      if n%4=1 then 2*(-1)^(n/4) else 0 := by
  have h := congrArg (coeff (ZMod 16) n) (map_solution (Int.castRingHom (ZMod 16)))
  rw [coeff_map,solution_mod_sixteen,comparison,two_mul,map_add,alternating_coeff] at h
  change ((coeff ℤ n solution : ℤ) : ZMod 16)=_ at h
  split_ifs with hn
  · rw [if_pos hn] at h
    simpa only [two_mul] using h
  · rw [if_neg hn] at h
    simpa using h

theorem a_shift_mod_sixteen (n : ℕ) : (a (n+1) : ZMod 16)=2*(-1)^n := by
  have h : 4*(n+1)-3=4*n+1 := by omega
  have hd : (4*n+1)/4=n := by omega
  simp only [a,h,solution_coeff_mod_sixteen]
  simp [hd]

theorem a_mod_sixteen (n : ℕ) (hn : 1≤n) : (a n : ZMod 16)=2*(-1)^(n-1) := by
  simpa only [Nat.sub_add_cancel hn] using a_shift_mod_sixteen (n-1)

theorem a_odd_index_mod_eight (n : ℕ) (hn : 1≤n) : (a (2*n-1) : ZMod 8)=2 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  have he : 2*(1+k)-1=2*k+1 := by omega
  rw [he,a_shift_mod_eight]
  simp [pow_mul]

theorem a_even_index_mod_eight (n : ℕ) (hn : 1≤n) : (a (2*n) : ZMod 8)=6 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  have he : 2*(1+k)=(2*k+1)+1 := by omega
  rw [he,a_shift_mod_eight,pow_add,pow_mul]
  norm_num
  decide

theorem a_mod_four (n : ℕ) (hn : 1≤n) : (a n : ZMod 4)=2 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  let f : ZMod 8 →+* ZMod 4 := ZMod.castHom (by decide : 4∣8) (ZMod 4)
  have h := congrArg f (a_shift_mod_eight k)
  change f (Int.cast (a (k+1)))=f (2*(-1)^k) at h
  have hf : ∀ z : ℤ, f (z : ZMod 8)=(z : ZMod 4) := by intro z; exact map_intCast f z
  rw [hf] at h
  simp only [map_mul,map_ofNat,map_pow,map_neg,map_one] at h
  have hp : ∀ j : ℕ, (2 : ZMod 4)*(-1)^j=2 := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih => rw [pow_succ,← mul_assoc,ih]; norm_num; decide
  simpa only [Nat.add_comm,hp k] using h

end
end Families.BilateralTheta
