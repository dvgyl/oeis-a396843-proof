import Families.CubicFrobenius

/-!
AI-generated formalization by ChatGPT (OpenAI) for Dev D. Goyal.

# Four conjectures in A389474 and A389475

The integer solution is constructed before its congruences are proved.
Its coefficient recursion divides an always-even residual by two.
-/

namespace Families.CubicReversion

open PowerSeries Hanna.Series

noncomputable section

variable {R : Type*} [CommRing R]

def residual (s : R) (A : PowerSeries R) : PowerSeries R :=
  A^2+2*C R s*A^3-compose A (3*X^2)+2*X^2

def Equation (s : R) (A : PowerSeries R) : Prop :=
  compose A (3*X^2)=2*X^2+A^2+2*C R s*A^3

theorem equation_iff_residual (s : R) (A : PowerSeries R) :
    Equation s A ↔ residual s A=0 := by
  unfold Equation residual
  constructor <;> intro h <;> linear_combination -h

theorem residual_perturbation (s : R) (A B : PowerSeries R) (r : ℕ) (hr : 2≤r)
    (hA : Normalized A) (hB : Normalized B) (hab : X^r∣B-A) :
    X^(r+2)∣residual s B-residual s A-2*X*(B-A) := by
  have hsum : (X : PowerSeries R)^2∣B+A-2*X := by
    have h1 := (normalized_iff_X_sq_dvd B).mp hB
    have h2 := (normalized_iff_X_sq_dvd A).mp hA
    convert dvd_add h1 h2 using 1; ring
  have hquad : (X : PowerSeries R)^2∣B^2+B*A+A^2 := by
    have ha : (X : PowerSeries R)^1∣A := by simpa using hA.X_dvd
    have hb : (X : PowerSeries R)^1∣B := by simpa using hB.X_dvd
    simpa [pow_two] using dvd_add
      (dvd_add (X_pow_dvd_product hb hb) (X_pow_dvd_product hb ha))
      (X_pow_dvd_product ha ha)
  have hsquare := X_pow_dvd_product hab hsum
  have hcube := dvd_mul_of_dvd_left (X_pow_dvd_product hab hquad) (2*C R s)
  have hcomp : (X : PowerSeries R)^(r+2)∣compose (B-A) (3*X^2) := by
    have h := compose_outer_vanish (B-A) (3*X^2) r 2 (by simp) hab
      (dvd_mul_left (X^2) 3)
    exact (pow_dvd_pow X (by omega : r+2≤2*r)).trans h
  have h := dvd_sub (dvd_add hsquare hcube) hcomp
  rw [compose_sub _ _ _ (by simp)] at h
  convert h using 1; unfold residual; ring

theorem residual_X (s : R) : residual s (X : PowerSeries R)=2*C R s*X^3 := by
  have hz : constantCoeff R (3*X^2 : PowerSeries R)=0 := by simp
  rw [residual, compose_X_left _ hz]
  ring

theorem residual_vanish_initial (s : R) (A : PowerSeries R) (hA : Normalized A) :
    (X : PowerSeries R)^3∣residual s A := by
  have hd := (normalized_iff_X_sq_dvd A).mp hA
  have hp := residual_perturbation s X A 2 (by omega) normalized_X hA hd
  have hp3 : (X : PowerSeries R)^3∣residual s A-residual s X-2*X*(A-X) :=
    (pow_dvd_pow X (by omega : 3≤2+2)).trans hp
  have hx3 : (X : PowerSeries R)^3∣2*X*(A-X) := by
    have h := X_pow_dvd_product (dvd_refl ((X : PowerSeries R)^1)) hd
    convert dvd_mul_of_dvd_left h (2 : PowerSeries R) using 1; ring
  have hX : (X : PowerSeries R)^3∣residual s X := by
    rw [residual_X]
    exact dvd_mul_left _ _
  convert dvd_add (dvd_add hp3 hX) hx3 using 1; ring

theorem map_residual {S : Type*} [CommRing S] (f : R →+* S) (s : R) (A : PowerSeries R) :
    PowerSeries.map f (residual s A)=residual (f s) (PowerSeries.map f A) := by
  have hz : constantCoeff R (3*X^2 : PowerSeries R)=0 := by simp
  simp only [residual, map_add, map_sub, map_mul, map_pow, PowerSeries.map_C,
    PowerSeries.map_X, map_ofNat, map_compose f A (3*X^2) hz]

theorem residual_even (s : ℤ) (A : PowerSeries ℤ) (n : ℕ) :
    (2:ℤ)∣coeff ℤ n (residual s A) := by
  have hm : PowerSeries.map (Int.castRingHom (ZMod 2)) (residual s A)=0 := by
    rw [map_residual]
    have htwo : (2 : PowerSeries (ZMod 2))=0 := by
      have h : (2 : ZMod 2)=0 := by decide
      simpa only [map_ofNat, map_zero] using congrArg (C (ZMod 2)) h
    have hthree : (3 : PowerSeries (ZMod 2))=1 := by
      have h : (3 : ZMod 2)=1 := by decide
      simpa only [map_ofNat, map_one] using congrArg (C (ZMod 2)) h
    simp only [residual, htwo, hthree, zero_mul, one_mul, add_zero]
    rw [square_substitution (PowerSeries.map (Int.castRingHom (ZMod 2)) A), sub_self]
  have hc := congrArg (coeff (ZMod 2) n) hm
  simp only [coeff_map, Int.coe_castRingHom, map_zero] at hc
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hc

def recursionOperator (s : ℤ) (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  coeff ℤ (n+3) (residual s (ofTail a))/2

theorem recursion_triangular (s : ℤ) : Triangular (recursionOperator s) := by
  intro n a b hab
  have hd := (agree_iff_X_pow_dvd_sub (n+2) (ofTail a) (ofTail b)).mp
    (ofTail_agree a b n hab)
  have hp := residual_perturbation s (ofTail b) (ofTail a) (n+2) (by omega)
    (normalized_ofTail b) (normalized_ofTail a) hd
  have hc := X_pow_dvd_iff.mp hp (n+3) (by omega)
  have hx (F : PowerSeries ℤ) : coeff ℤ (n+3) (2*X*F)=2*coeff ℤ (n+2) F := by
    simp [two_mul, add_mul, show n+3=(n+2)+1 by omega]
  simp only [map_sub, hx, coeff_ofTail] at hc
  unfold recursionOperator
  omega

theorem solution_exists (s : ℤ) :
    ∃ A : PowerSeries ℤ, Normalized A ∧ Equation s A := by
  let a := triangularCoeffs (recursionOperator s) (fun _ => 0)
  have ha := triangularCoeffs_spec (recursionOperator s) (recursion_triangular s) (fun _ => 0)
  refine ⟨ofTail a, normalized_ofTail a, (equation_iff_residual _ _).mpr ?_⟩
  ext n
  by_cases hn : n<3
  · exact X_pow_dvd_iff.mp (residual_vanish_initial s (ofTail a) (normalized_ofTail a)) n hn
  · have he := congrFun ha (n-3)
    change coeff ℤ (n-3+3) (residual s (ofTail a))/2=0 at he
    rw [Nat.sub_add_cancel (by omega)] at he
    obtain ⟨k,hk⟩ := residual_even s (ofTail a) n
    simp only [map_zero]
    omega

theorem solution_unique (s : ℤ) {A B : PowerSeries ℤ} (hA : Normalized A)
    (hB : Normalized B) (heA : Equation s A) (heB : Equation s B) : A=B := by
  have hzA := (equation_iff_residual _ _).mp heA
  have hzB := (equation_iff_residual _ _).mp heB
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n<2
    · rcases (by omega : n=0 ∨ n=1) with rfl | rfl
      · exact hA.1.trans hB.1.symm
      · exact hA.2.trans hB.2.symm
    · have hd := (agree_iff_X_pow_dvd_sub n A B).mp ih
      have hp := residual_perturbation s B A n (by omega) hB hA hd
      have hc := X_pow_dvd_iff.mp hp (n+1) (by omega)
      rw [hzA, hzB] at hc
      have hx : coeff ℤ (n+1) (2*X*(A-B))=2*(coeff ℤ n A-coeff ℤ n B) := by
        simp [two_mul, add_mul]
      simp only [zero_sub, sub_zero, map_neg, hx] at hc
      omega

theorem existence_uniqueness (s : ℤ) :
    ∃! A : PowerSeries ℤ, Normalized A ∧ Equation s A := by
  obtain ⟨A,hA,heA⟩ := solution_exists s
  exact ⟨A,⟨hA,heA⟩,fun B hB => solution_unique s hB.1 hA hB.2 heA⟩

def cubicSolution (s : ℤ) : PowerSeries ℤ := (existence_uniqueness s).exists.choose

theorem cubicSolution_normalized (s : ℤ) : Normalized (cubicSolution s) :=
  (existence_uniqueness s).exists.choose_spec.1

theorem cubicSolution_equation (s : ℤ) : Equation s (cubicSolution s) :=
  (existence_uniqueness s).exists.choose_spec.2

end
end Families.CubicReversion
