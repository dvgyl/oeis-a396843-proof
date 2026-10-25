module

public import Hanna.Related.ScaledParity
public import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# OEIS A397588: parity of a differential fixed point

The actual normalized integral solution of `A = X + (X*A^2)'` is
constructed and proved unique before its parity is determined.

AI disclosure: OpenAI ChatGPT generated these proofs for Dev D. Goyal.
-/

@[expose] public section

namespace Families.DifferentialParity

open PowerSeries Hanna.Series

noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S]

theorem derivative_vanish (G : PowerSeries R) (n : ℕ)
    (hG : (X : PowerSeries R)^(n+1) ∣ G) : X^n ∣ derivative G := by
  apply X_pow_dvd_iff.mpr
  intro k hk
  rw [coeff_derivative, X_pow_dvd_iff.mp hG (k+1) (by omega), zero_mul]

def step (G : PowerSeries R) : PowerSeries R := X + derivative (X*G^2)

theorem step_normalized {G : PowerSeries R} (hG : Normalized G) :
    Normalized (step G) := by
  have hg : (X : PowerSeries R)^1 ∣ G := by simpa using hG.X_dvd
  have hsq : (X : PowerSeries R)^2 ∣ G^2 := by
    simpa [pow_two] using X_pow_dvd_product hg hg
  have hx : (X : PowerSeries R)^3 ∣ X*G^2 := by
    simpa using X_pow_dvd_product (dvd_refl ((X : PowerSeries R)^1)) hsq
  have hd := derivative_vanish (X*G^2) 2 hx
  apply (normalized_iff_X_sq_dvd (step G)).mpr
  simpa [step] using hd

theorem step_contraction (n : ℕ) {G H : PowerSeries R}
    (hG : Normalized G) (hH : Normalized H)
    (hGH : (X : PowerSeries R)^n ∣ G-H) :
    (X : PowerSeries R)^(n+1) ∣ step G-step H := by
  have hsum : (X : PowerSeries R)^1 ∣ G+H := by
    simpa using dvd_add hG.X_dvd hH.X_dvd
  have hsq : (X : PowerSeries R)^(n+1) ∣ G^2-H^2 := by
    convert X_pow_dvd_product hGH hsum using 1
    ring
  have hx : (X : PowerSeries R)^(n+1+1) ∣ X*(G^2-H^2) := by
    simpa only [pow_one, show 1+(n+1)=n+1+1 by omega] using
      X_pow_dvd_product (dvd_refl ((X : PowerSeries R)^1)) hsq
  have hd := derivative_vanish (X*(G^2-H^2)) (n+1) hx
  have he : step G-step H = derivative (X*(G^2-H^2)) := by
    rw [mul_sub, map_sub]
    dsimp [step]
    ring
  rw [he]
  exact hd

theorem equation_triangular :
    Triangular (fun (a : ℕ → R) n => coeff (n+2) (ofTail a-step (ofTail a))) := by
  intro n a b hab
  have hd := (agree_iff_X_pow_dvd_sub (n+2) (ofTail a) (ofTail b)).mp
    (ofTail_agree a b n hab)
  have hp := step_contraction (n+2) (normalized_ofTail a) (normalized_ofTail b) hd
  have hc := X_pow_dvd_iff.mp hp (n+2) (by omega)
  simp only [map_sub, coeff_ofTail] at hc ⊢
  linear_combination -hc

theorem solution_exists : ∃ G : PowerSeries R, Normalized G ∧ G=step G := by
  let op := fun (a : ℕ → R) n => coeff (n+2) (ofTail a-step (ofTail a))
  let a := triangularCoeffs op (fun _ => 0)
  have ha := triangularCoeffs_spec op equation_triangular (fun _ => 0)
  refine ⟨ofTail a, normalized_ofTail a, ?_⟩
  have hs := step_normalized (normalized_ofTail a)
  ext n
  rcases n with _ | (_ | n)
  · exact (normalized_ofTail a).1.trans hs.1.symm
  · exact (normalized_ofTail a).2.trans hs.2.symm
  · have hc := congrFun ha n
    change coeff (n+2) (ofTail a-step (ofTail a))=0 at hc
    simpa only [map_sub, sub_eq_zero, Nat.succ_eq_add_one, Nat.add_assoc] using hc

theorem solution_unique {G H : PowerSeries R} (hG : Normalized G)
    (hH : Normalized H) (heG : G=step G) (heH : H=step H) : G=H := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hd := (agree_iff_X_pow_dvd_sub n G H).mp ih
    have hp := step_contraction n hG hH hd
    have hc := X_pow_dvd_iff.mp hp n (by omega)
    rw [← heG, ← heH, map_sub, sub_eq_zero] at hc
    exact hc

theorem existence_uniqueness :
    ∃! G : PowerSeries R, Normalized G ∧ G=X+derivative (X*G^2) := by
  obtain ⟨G,hG,heG⟩ := solution_exists (R:=R)
  exact ⟨G,⟨hG,heG⟩,fun H hH => solution_unique hH.1 hG hH.2 heG⟩

def A : PowerSeries R := (existence_uniqueness (R:=R)).exists.choose

theorem A_normalized : Normalized (A : PowerSeries R) :=
  (existence_uniqueness (R:=R)).exists.choose_spec.1

theorem A_equation : (A : PowerSeries R)=X+derivative (X*A^2) :=
  (existence_uniqueness (R:=R)).exists.choose_spec.2

theorem map_derivative (f : R →+* S) (G : PowerSeries R) :
    PowerSeries.map f (derivative G)=derivative (PowerSeries.map f G) := by
  ext n
  simp only [coeff_map, coeff_derivative, map_mul, map_add, map_natCast, map_one]

theorem map_A (f : R →+* S) :
    PowerSeries.map f (A : PowerSeries R)=(A : PowerSeries S) := by
  apply solution_unique (A_normalized.map f) A_normalized _ A_equation
  have he := congrArg (PowerSeries.map f) (A_equation (R:=R))
  simpa only [step, map_add, map_derivative, map_mul, map_pow, PowerSeries.map_X] using he

theorem A_mod_two_quadratic : (A : PowerSeries (ZMod 2))-A^2=X := by
  have htwo : (2 : PowerSeries (ZMod 2))=0 := by
    have h : (2 : ZMod 2)=0 := by decide
    simpa only [map_ofNat, map_zero] using congrArg (C (R := (ZMod 2))) h
  have hsquare : derivative (R := (ZMod 2)) ((A : PowerSeries (ZMod 2))^2)=0 := by
    rw [pow_two, Derivation.leibniz]
    simp only [smul_eq_mul, ← two_mul, htwo, zero_mul]
  have he := A_equation (R:=ZMod 2)
  rw [Derivation.leibniz, hsquare, derivative_X] at he
  simp only [smul_zero, zero_add, smul_eq_mul, mul_one] at he
  linear_combination he

/-- The source's separately stated divisibility by three follows from a
stronger complete series reduction. -/
theorem A_mod_three : (A : PowerSeries (ZMod 3))=X := by
  apply solution_unique A_normalized normalized_X A_equation
  have hd : derivative (R := (ZMod 3)) ((X : PowerSeries (ZMod 3))^3)=0 := by
    ext n
    rw [coeff_derivative, coeff_X_pow, map_zero]
    by_cases hn : n+1=3
    · rw [if_pos hn]
      have hn' : n=2 := by omega
      subst n
      decide
    · rw [if_neg hn, zero_mul]
  change X=X+derivative (R := (ZMod 3)) (X*X^2)
  rw [show (X : PowerSeries (ZMod 3))*X^2=X^3 by ring, hd, add_zero]

/-- A397588, with its zero constant coefficient included. -/
def a (n : ℕ) : ℤ := coeff (R := ℤ) n A

/-- The exact OEIS conjecture, strengthened to include the zero index. -/
theorem a397588_parity (n : ℕ) : Odd (a n) ↔ ∃ k : ℕ, n=2^k := by
  have hm := congrArg (coeff (R := (ZMod 2)) n) (map_A (Int.castRingHom (ZMod 2)))
  rw [coeff_map] at hm
  change (a n : ZMod 2)=coeff (R := (ZMod 2)) n A at hm
  have hc : ((a n : ZMod 2)=1) ↔ Odd (a n) := by
    simpa [Int.odd_iff] using ZMod.intCast_eq_intCast_iff' (a n) 1 2
  rw [← hc, hm]
  exact Hanna.Related.ScaledInverse.quadratic_coeff_one_iff_power_two A
    A_normalized A_mod_two_quadratic n

/-- This is an additional assertion in the entry, not another conjecture claim. -/
theorem a397588_divisible_by_three (n : ℕ) (hn : 1<n) : (3 : ℤ) ∣ a n := by
  have hm := congrArg (coeff (R := (ZMod 3)) n) (map_A (Int.castRingHom (ZMod 3)))
  rw [coeff_map, A_mod_three, coeff_X, if_neg (by omega : n≠1)] at hm
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a n) 3).mp hm

end
end Families.DifferentialParity
