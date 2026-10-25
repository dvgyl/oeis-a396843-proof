module

public import Solutions.Common
public import Hanna
public import Mathlib.Data.Nat.Digits.Defs

/-!
# Solution for the family `A(x·A - m·x·A²) = x²`

Each statement of `Challenges.HannaFamily` is derived from the library `Hanna`. There the
equation is written `Series.Psi m U = X^2`, which unfolds to the substitution used in the
Challenge, and `a m n` is the coefficient of `x^n` in the unique normalized solution.
-/

public section

namespace OEISProofs.HannaFamily

open PowerSeries Hanna

theorem eq_A (m : ℤ) (U : PowerSeries ℤ) (h0 : coeff 0 U = 0) (h1 : coeff 1 U = 1)
    (hU : U.subst (X * U - C m * X * U ^ 2) = X ^ 2) : U = A m :=
  (Series.existence_uniqueness m).unique ⟨⟨h0, h1⟩, hU⟩
    ⟨Series.solution_normalized m, Series.solution_equation m⟩

theorem binaryWeight_eq_digits_sum (n : ℕ) : binaryWeight n = (Nat.digits 2 n).sum := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [binaryWeight_step, Nat.digits_def' (by norm_num) hn, List.sum_cons,
        ih (n / 2) (Nat.div_lt_self hn (by norm_num))]

theorem existsUnique (m : ℤ) :
    ∃! U : PowerSeries ℤ, coeff 0 U = 0 ∧ coeff 1 U = 1 ∧
      U.subst (X * U - C m * X * U ^ 2) = X ^ 2 := by
  obtain ⟨U, ⟨⟨h0, h1⟩, hU⟩, huniq⟩ := Series.existence_uniqueness m
  exact ⟨U, ⟨h0, h1, hU⟩, fun V ⟨g0, g1, gV⟩ => huniq V ⟨⟨g0, g1⟩, gV⟩⟩

theorem odd_coeff (m : ℤ) (hm : Odd m) (U : PowerSeries ℤ) (h0 : coeff 0 U = 0)
    (h1 : coeff 1 U = 1) (hU : U.subst (X * U - C m * X * U ^ 2) = X ^ 2)
    (n : ℕ) (hn : 1 ≤ n) :
    Odd (coeff n U) := by
  rw [eq_A m U h0 h1 hU]
  exact Statements.parity_odd m hm n hn

theorem even_coeff (m : ℤ) (hm : Even m) (U : PowerSeries ℤ) (h0 : coeff 0 U = 0)
    (h1 : coeff 1 U = 1) (hU : U.subst (X * U - C m * X * U ^ 2) = X ^ 2)
    (n : ℕ) (hn : 2 ≤ n) :
    Even (coeff n U) := by
  rw [eq_A m U h0 h1 hU]
  exact even_iff_two_dvd.2 ((Statements.parity_even m hm).2 n hn)

theorem modEq_sq (m : ℤ) (hm : 2 ≤ m) (U : PowerSeries ℤ) (h0 : coeff 0 U = 0)
    (h1 : coeff 1 U = 1) (hU : U.subst (X * U - C m * X * U ^ 2) = X ^ 2) :
    (∀ j : ℕ, coeff (2 ^ j + 1) U ≡ m * (-1) ^ j [ZMOD m ^ 2]) ∧
      (∀ n : ℕ, 2 ≤ n → (¬∃ j : ℕ, n = 2 ^ j + 1) → m ^ 2 ∣ coeff n U) := by
  rw [eq_A m U h0 h1 hU]
  obtain ⟨hpow, hrest⟩ := Statements.mod_parameter_squared m hm
  exact ⟨fun j => (Int.modEq_iff_dvd.2 (hpow j)).symm, hrest⟩

theorem pow_digitSum_dvd (m : ℤ) (hm : 2 ≤ m) (U : PowerSeries ℤ) (h0 : coeff 0 U = 0)
    (h1 : coeff 1 U = 1) (hU : U.subst (X * U - C m * X * U ^ 2) = X ^ 2)
    (n : ℕ) (hn : 1 ≤ n) :
    m ^ (Nat.digits 2 (n - 1)).sum ∣ coeff n U := by
  rw [eq_A m U h0 h1 hU, ← binaryWeight_eq_digits_sum]
  exact Statements.binary_divisibility_integer m hm n hn

theorem prime_pow_dvd (m : ℤ) (hm : 2 ≤ m) (p : ℕ) (hp : p.Prime) (hpm : (p : ℤ) ∣ m)
    (e : ℕ) (he : (p : ℤ) ^ e ∣ m ∧ ¬(p : ℤ) ^ (e + 1) ∣ m)
    (U : PowerSeries ℤ) (h0 : coeff 0 U = 0)
    (h1 : coeff 1 U = 1) (hU : U.subst (X * U - C m * X * U ^ 2) = X ^ 2)
    (n : ℕ) (hn : 2 ≤ n) :
    (p : ℤ) ^ (e * (Nat.digits 2 (n - 1)).sum) ∣ coeff n U ∧
      (((p : ℤ) ^ e ∣ coeff n U ∧ ¬(p : ℤ) ^ (e + 1) ∣ coeff n U) ↔
        ∃ j : ℕ, n = 2 ^ j + 1) := by
  rw [eq_A m U h0 h1 hU, ← binaryWeight_eq_digits_sum]
  exact ⟨Statements.prime_divisibility_lower_bound m hm p hp hpm e he n (by omega),
    Statements.minimum_prime_exponent_iff m hm p hp hpm e he n hn⟩

theorem residues_mod_nine (U : PowerSeries ℤ) (h0 : coeff 0 U = 0)
    (h1 : coeff 1 U = 1) (hU : U.subst (X * U - C 3 * X * U ^ 2) = X ^ 2) :
    (∀ k : ℕ, coeff (4 ^ k + 1) U ≡ 3 [ZMOD 9]) ∧
      (∀ k : ℕ, coeff (2 * 4 ^ k + 1) U ≡ 6 [ZMOD 9]) ∧
      (∀ n : ℕ, 2 ≤ n → (¬∃ k : ℕ, n = 4 ^ k + 1) → (¬∃ k : ℕ, n = 2 * 4 ^ k + 1) →
        (9 : ℤ) ∣ coeff n U) := by
  rw [eq_A 3 U h0 h1 hU]
  obtain ⟨h₁, h₂, h₃⟩ := Statements.residues_parameter_three
  exact ⟨fun k => (Int.modEq_iff_dvd.2 (h₁ k)).symm,
    fun k => (Int.modEq_iff_dvd.2 (h₂ k)).symm, h₃⟩

theorem residues_mod_sixteen (U : PowerSeries ℤ) (h0 : coeff 0 U = 0)
    (h1 : coeff 1 U = 1) (hU : U.subst (X * U - C 4 * X * U ^ 2) = X ^ 2) :
    (∀ k : ℕ, coeff (4 ^ k + 1) U ≡ 4 [ZMOD 16]) ∧
      (∀ k : ℕ, coeff (2 * 4 ^ k + 1) U ≡ 12 [ZMOD 16]) ∧
      (∀ n : ℕ, 2 ≤ n → (¬∃ k : ℕ, n = 4 ^ k + 1) → (¬∃ k : ℕ, n = 2 * 4 ^ k + 1) →
        (16 : ℤ) ∣ coeff n U) := by
  rw [eq_A 4 U h0 h1 hU]
  obtain ⟨h₁, h₂, h₃⟩ := Statements.residues_parameter_four
  exact ⟨fun k => (Int.modEq_iff_dvd.2 (h₁ k)).symm,
    fun k => (Int.modEq_iff_dvd.2 (h₂ k)).symm, h₃⟩

end OEISProofs.HannaFamily
