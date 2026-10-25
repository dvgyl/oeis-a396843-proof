module

public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Data.Int.ModEq

/-!
# Equations with an exact halving step (OEIS A389537, A389542, A389474, A389475)

All series have integer coefficients; a series is *normalized* if it has the form
`x + a(2)x² + ⋯`. `A.subst B` is Mathlib's substitution `A(B(x))` of a series `B` with zero
constant term.

In each of these equations, computing the coefficients one at a time involves a division
by `2`, or the analysis passes through the series `(A - x - x²)/2`; the existence of a
solution with integer coefficients is part of the results.

* **A389537.** `A(A(x) - x) = A(x)²`. Conjectured: for `n > 2`, `a(n) ≡ 2 (mod 4)` if
  `n = 3·2^k`, and `4 ∣ a(n)` otherwise.
* **A389542.** `A(A(x)² - x²) = 4A(x)³`. Conjectured: for `n > 1`, `a(n) ≡ 2 (mod 4)` if
  `n = 2^k + 1`, and `4 ∣ a(n)` otherwise.
* **A389474.** `A(x² + 2x³ + 2A(x)²) = 3A(x)²`. Conjectured: every coefficient of `A(x)²`
  beyond `x³` is divisible by `9`, and every coefficient of `A(x)^(3k) - A(x³)^k` is divisible
  by `3`. The first is proved in the stronger form `A(x)² ≡ x² + 2x³ (mod 9)`.
* **A389475.** `A(3x²) = 2x² + A(x)² - 2A(x)³`. Conjectured: `A(x)³ ≡ A(x³)` and
  `A(x)² ≡ x² + 2A(x³)` modulo `3`, coefficientwise.
-/

public section

namespace OEISProofs.Halving

open PowerSeries

/-- A389537: the equation `A(A(x) - x) = A(x)²` has exactly one normalized solution. -/
theorem a389537_existsUnique :
    ∃! A : PowerSeries ℤ, coeff 0 A = 0 ∧ coeff 1 A = 1 ∧ A.subst (A - X) = A ^ 2 := by
  sorry

/-- A389537: for `n > 2`, `a(n) ≡ 2 (mod 4)` exactly when `n = 3·2^k`, and `4 ∣ a(n)` exactly
when it is not. -/
theorem a389537_coeff (A : PowerSeries ℤ) (h0 : coeff 0 A = 0) (h1 : coeff 1 A = 1)
    (hA : A.subst (A - X) = A ^ 2) (n : ℕ) (hn : 2 < n) :
    (coeff n A ≡ 2 [ZMOD 4] ↔ ∃ k : ℕ, n = 3 * 2 ^ k) ∧
      ((4 : ℤ) ∣ coeff n A ↔ ¬∃ k : ℕ, n = 3 * 2 ^ k) := by
  sorry

/-- A389542: the equation `A(A(x)² - x²) = 4A(x)³` has exactly one normalized solution. -/
theorem a389542_existsUnique :
    ∃! A : PowerSeries ℤ, coeff 0 A = 0 ∧ coeff 1 A = 1 ∧
      A.subst (A ^ 2 - X ^ 2) = 4 * A ^ 3 := by
  sorry

/-- A389542: for `n > 1`, `a(n) ≡ 2 (mod 4)` exactly when `n = 2^k + 1`, and `4 ∣ a(n)` exactly
when it is not. -/
theorem a389542_coeff (A : PowerSeries ℤ) (h0 : coeff 0 A = 0) (h1 : coeff 1 A = 1)
    (hA : A.subst (A ^ 2 - X ^ 2) = 4 * A ^ 3) (n : ℕ) (hn : 1 < n) :
    (coeff n A ≡ 2 [ZMOD 4] ↔ ∃ k : ℕ, n = 2 ^ k + 1) ∧
      ((4 : ℤ) ∣ coeff n A ↔ ¬∃ k : ℕ, n = 2 ^ k + 1) := by
  sorry

/-- A389474: the equation `A(x² + 2x³ + 2A²) = 3A²` has exactly one normalized solution. -/
theorem a389474_existsUnique :
    ∃! A : PowerSeries ℤ, coeff 0 A = 0 ∧ coeff 1 A = 1 ∧
      A.subst (X ^ 2 + 2 * X ^ 3 + 2 * A ^ 2) = 3 * A ^ 2 := by
  sorry

/-- A389474: `A(x)² ≡ x² + 2x³ (mod 9)` coefficientwise (so every coefficient of `A(x)²`
beyond `x³` is divisible by `9`), and every coefficient of `A(x)^(3k) - A(x³)^k` is divisible
by `3`. -/
theorem a389474_coeff (A : PowerSeries ℤ) (h0 : coeff 0 A = 0) (h1 : coeff 1 A = 1)
    (hA : A.subst (X ^ 2 + 2 * X ^ 3 + 2 * A ^ 2) = 3 * A ^ 2) :
    (∀ n : ℕ, coeff n (A ^ 2) ≡ coeff n (X ^ 2 + 2 * X ^ 3 : PowerSeries ℤ) [ZMOD 9]) ∧
      (∀ n k : ℕ, (3 : ℤ) ∣ coeff n (A ^ (3 * k) - (A.subst (X ^ 3 : PowerSeries ℤ)) ^ k)) := by
  sorry

/-- A389475: the equation `A(3x²) = 2x² + A² - 2A³` has exactly one normalized solution. -/
theorem a389475_existsUnique :
    ∃! A : PowerSeries ℤ, coeff 0 A = 0 ∧ coeff 1 A = 1 ∧
      A.subst (3 * X ^ 2 : PowerSeries ℤ) = 2 * X ^ 2 + A ^ 2 - 2 * A ^ 3 := by
  sorry

/-- A389475: every coefficient of `A(x)³ - A(x³)` and of `A(x)² - x² - 2A(x³)` is divisible
by `3`. -/
theorem a389475_coeff (A : PowerSeries ℤ) (h0 : coeff 0 A = 0) (h1 : coeff 1 A = 1)
    (hA : A.subst (3 * X ^ 2 : PowerSeries ℤ) = 2 * X ^ 2 + A ^ 2 - 2 * A ^ 3) :
    (∀ n : ℕ, (3 : ℤ) ∣ coeff n (A ^ 3 - A.subst (X ^ 3 : PowerSeries ℤ))) ∧
      (∀ n : ℕ, (3 : ℤ) ∣ coeff n (A ^ 2 - X ^ 2 - 2 * A.subst (X ^ 3 : PowerSeries ℤ))) := by
  sorry

end OEISProofs.Halving
