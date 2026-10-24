import Hanna.Series.Inverse
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# Frobenius substitution for actual formal power series over prime fields

AI-generated formalization by ChatGPT (OpenAI) for Dev D. Goyal.
Review status: see AUTHORSHIP.md.
-/

namespace More.CubicReversion

open PowerSeries Hanna.Series

variable {R : Type*} [CommRing R]

theorem coeff_compose_X_power (A : PowerSeries R) (p n : ℕ) (hp : 0<p) :
    coeff R n (compose A (X^p)) = if p∣n then coeff R (n/p) A else 0 := by
  rw [coeff_compose A (X^p) (by simp [hp.ne'])]
  simp only [← pow_mul, coeff_X_pow]
  by_cases hd : p∣n
  · rw [if_pos hd]
    have hm : n/p ∈ Finset.range (n+1) := by
      apply Finset.mem_range.mpr
      exact Nat.lt_succ_of_le (Nat.div_le_self n p)
    rw [Finset.sum_eq_single_of_mem (n/p) hm]
    · rw [if_pos (Nat.mul_div_cancel' hd).symm]
      simp
    · intro k hk hne
      rw [if_neg, mul_zero]
      intro he
      apply hne
      have heq : p*k=p*(n/p) := he.symm.trans (Nat.mul_div_cancel' hd).symm
      exact Nat.eq_of_mul_eq_mul_left hp heq
  · rw [if_neg hd]
    apply Finset.sum_eq_zero
    intro k hk
    rw [if_neg, mul_zero]
    intro he
    exact hd ⟨k, he⟩

theorem coeff_power_trunc (A : PowerSeries R) (n p : ℕ) :
    coeff R n (A^p)=coeff R n ((PowerSeries.trunc (n+1) A : PowerSeries R)^p) := by
  have hd : (X : PowerSeries R)^(n+1)∣A-(PowerSeries.trunc (n+1) A : PowerSeries R) := by
    apply X_pow_dvd_iff.mpr
    intro k hk
    simp [Polynomial.coeff_coe, coeff_trunc, hk]
  have hp := hd.trans (sub_dvd_pow_sub_pow A (PowerSeries.trunc (n+1) A : PowerSeries R) p)
  have he := X_pow_dvd_iff.mp hp n (by omega)
  simpa only [map_sub, sub_eq_zero] using he

theorem coeff_frobenius (p : ℕ) [Fact p.Prime] (A : PowerSeries (ZMod p)) (n : ℕ) :
    coeff (ZMod p) n (A^p)=if p∣n then coeff (ZMod p) (n/p) A else 0 := by
  have hp : 0<p := (Fact.out : p.Prime).pos
  rw [coeff_power_trunc A n p, ← Polynomial.coe_pow]
  rw [← Polynomial.expand_char (p:=p), Polynomial.coeff_coe, Polynomial.coeff_map,
    frobenius_def, Polynomial.coeff_expand hp]
  split_ifs with hd
  · rw [ZMod.pow_card, coeff_trunc, if_pos (Nat.lt_succ_of_le (Nat.div_le_self n p))]
  · simp

theorem frobenius_substitution (p : ℕ) [Fact p.Prime] (A : PowerSeries (ZMod p)) :
    A^p=compose A (X^p) := by
  ext n
  rw [coeff_frobenius, coeff_compose_X_power _ _ _ (Fact.out : p.Prime).pos]

theorem cube_substitution (A : PowerSeries (ZMod 3)) : A^3=compose A (X^3) :=
  frobenius_substitution 3 A

theorem square_substitution (A : PowerSeries (ZMod 2)) : A^2=compose A (X^2) :=
  frobenius_substitution 2 A

end More.CubicReversion
