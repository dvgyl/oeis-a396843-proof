import Hanna.Related.ScaledInverse
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Ring.Int.Parity

/-!
# The parity conjectures for A393856 and A393858

Reduction of the exact scaled inverse equation at an even parameter gives
`A - A^2 = X` over `ZMod 2`.  Its coefficients are nonzero precisely at the
powers of two.  The proof below covers every index.
-/

namespace Hanna.Related.ScaledInverse

open PowerSeries Hanna.Series

variable {R : Type*} [CommRing R]

theorem scaleTail_zero {A : PowerSeries R} (hA : Normalized A) :
    scaleTail (0 : R) A = X := by
  ext n
  rcases n with _ | (_ | n)
  · simp [hA.1]
  · simp [hA.2]
  · simp [coeff_X, show n+1+1 ≠ 1 by omega]

theorem scaledSolution_zero_quadratic :
    scaledSolution (0 : R) - scaledSolution (0 : R)^2 = X := by
  have hn := scaledSolution_normalized (0 : R)
  have h := (source_iff_core (0 : R) hn).mp (scaledSolution_equation (0 : R))
  simpa only [core, scaleTail_zero hn, compose_X_left _ hn.constantCoeff, pow_two] using h

private abbrev F := ZMod 2

/-- Squaring a series in characteristic two doubles its support indices. -/
theorem coeff_square_mod_two (A : PowerSeries F) (n : ℕ) :
    coeff F n (A^2) = if 2 ∣ n then coeff F (n/2) A else 0 := by
  rw [pow_two, coeff_mul_eq_coeff_trunc_mul_trunc A A (Nat.lt_succ_self n)]
  rw [← Polynomial.coe_mul, ← pow_two]
  rw [← Polynomial.expand_char (p := 2), Polynomial.coeff_coe, Polynomial.coeff_map,
    frobenius_def, Polynomial.coeff_expand (by decide : 0 < 2)]
  split_ifs with h
  · rw [ZMod.pow_card, coeff_trunc, if_pos (by omega)]
  · simp

theorem quadratic_coeff_one_iff_power_two (A : PowerSeries F)
    (hA : Normalized A) (hquad : A-A^2=X) (n : ℕ) :
    coeff F n A = 1 ↔ ∃ k : ℕ, n = 2^k := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n = 0
    · subst n
      rw [hA.1]
      simp only [zero_ne_one, false_iff]
      rintro ⟨k, hk⟩
      exact (Nat.two_pow_pos k).ne' hk.symm
    by_cases ho : n = 1
    · subst n
      rw [hA.2]
      simp only [true_iff]
      exact ⟨0, by simp⟩
    have hn : 2 ≤ n := by omega
    have hc := congrArg (coeff F n) hquad
    rw [map_sub, coeff_square_mod_two, coeff_X, if_neg ho] at hc
    by_cases hd : 2 ∣ n
    · rw [if_pos hd, sub_eq_zero] at hc
      rw [hc, ih (n/2) (by omega)]
      constructor
      · rintro ⟨k, hk⟩
        refine ⟨k+1, ?_⟩
        have he := Nat.mul_div_cancel' hd
        rw [pow_succ]
        omega
      · rintro ⟨k, hk⟩
        cases k with
        | zero => simp at hk; omega
        | succ k =>
          refine ⟨k, ?_⟩
          rw [hk, pow_succ, Nat.mul_div_left _ (by decide : 0 < 2)]
    · rw [if_neg hd, sub_zero] at hc
      rw [hc]
      simp only [zero_ne_one, false_iff]
      rintro ⟨k, hk⟩
      cases k with
      | zero => simp at hk; omega
      | succ k =>
        apply hd
        rw [hk, pow_succ]
        exact dvd_mul_left _ _

theorem scaledSolution_zero_coeff_one_iff (n : ℕ) :
    coeff F n (scaledSolution (0 : F)) = 1 ↔ ∃ k : ℕ, n = 2^k :=
  quadratic_coeff_one_iff_power_two _ (scaledSolution_normalized 0)
    scaledSolution_zero_quadratic n

theorem integer_coeff_odd_iff (q : ℤ) (hq : (q : F) = 0) (n : ℕ) :
    Odd (coeff ℤ n (scaledSolution q)) ↔ ∃ k : ℕ, n = 2^k := by
  have hmap := congrArg (coeff F n) (map_scaledSolution (Int.castRingHom F) q)
  rw [PowerSeries.coeff_map] at hmap
  change ((coeff ℤ n (scaledSolution q) : ℤ) : F) =
    coeff F n (scaledSolution (q : F)) at hmap
  rw [hq] at hmap
  have hcast : (((coeff ℤ n (scaledSolution q) : ℤ) : F) = 1) ↔
      Odd (coeff ℤ n (scaledSolution q)) := by
    simpa [Int.odd_iff] using
      ZMod.intCast_eq_intCast_iff' (coeff ℤ n (scaledSolution q)) 1 2
  rw [← hcast, hmap]
  exact scaledSolution_zero_coeff_one_iff n

/-- The second A393856 conjecture, with no bound on the index. -/
theorem a393856_parity (n : ℕ) :
    Odd (coeff ℤ n (scaledSolution (4 : ℤ))) ↔ ∃ k : ℕ, n = 2^k :=
  integer_coeff_odd_iff 4 (by decide) n

/-- The second A393858 conjecture, with no bound on the index. -/
theorem a393858_parity (n : ℕ) :
    Odd (coeff ℤ n (scaledSolution (6 : ℤ))) ↔ ∃ k : ℕ, n = 2^k :=
  integer_coeff_odd_iff 6 (by decide) n

end Hanna.Related.ScaledInverse
