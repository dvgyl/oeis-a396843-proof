module

public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Int.ModEq

/-!
# Theta series and theta-type equations (OEIS A378580, A378581, A380060, A380680, A355872)

All series have integer coefficients. `A.subst B` is Mathlib's substitution `A(B(x))` of a
series `B` with zero constant term, and `invOfUnit B 1` is the multiplicative inverse `1/B` of
a series `B` with constant term `1`.

* **Theta substitutions (A378580, A378581).** Let `T` be Jacobi's theta series
  `θ₃(x) = 1 + 2x + 2x⁴ + 2x⁹ + ⋯ = 1 + 2∑_{k≥1} x^(k²)`, described in the hypotheses below by
  its coefficients. A378580 is the unique `A` with `A(0) = 1` and `A(x/A(x)) = θ₃(x)`; A378581
  is the unique `A` with `A(0) = 1` and `A(x·A(x)) = θ₃(x)`. Both entries conjecture that for
  `n > 0`, `a(n) ≡ 2 (mod 4)` if `n` is a perfect square and `4 ∣ a(n)` otherwise.
* **The implicit theta-type sum (A380060).** `A = 1 + 2∑_{k≥1} x^(k²)·((A - x^k)/(1 - x^k·A))^k`,
  with the same conjectured square pattern. The OEIS defines it by the two-sided sum over all
  integers `k`; the accompanying paper proves that this equals the one-sided form used here,
  and that step is not formalized.
* **The explicit theta-type sum (A380680).** `A = 1 + 2∑_{k≥1} x^(k²)·((2 - x^k)/(1 - 2x^k))^k`,
  again written in the OEIS as a two-sided sum. The entry conjectures the same square pattern,
  which is false (`a(1) = 4`, `a(2) = 6`); the correct pattern uses `n = 2j²` instead of `n = j²`.
  Both entries themselves record that the summand is invariant under `k ↦ -k`.
* **The bilateral equation (A355872).** `x = ∑_{m∈ℤ} (-x)^(m²)·A(x)^((m-1)²)`, written below
  coefficientwise with `finsum` (each coefficient involves only finitely many `m`). The entry
  records three congruences for `a(n)`, the coefficient of `x^(4n-3)` (the only nonzero ones);
  all three follow from `a(n) ≡ 2·(-1)^(n-1) (mod 16)`.

In each infinite sum over `k ≥ 1` below, the coefficient of `x^n` is the finite sum over
`k = 1, …, n + 1` (written with `k + 1` in place of `k`), since `x^(k²)` has no terms below
degree `k²`.

Context: these are congruences for the coefficients of power series defined by functional
equations. Results of this kind are known, for example, for the Catalan and Motzkin numbers
(Deutsch and Sagan, J. Number Theory 117 (2006); Eu, Liu and Yeh, European J. Combin. 29
(2008)), and Kauers, Krattenthaler and Müller (Electron. J. Combin. 18(2) (2012), P37) give a
method for the behaviour modulo powers of `2` of recursively defined sequences.
-/

public section

namespace OEISProofs.Theta

open PowerSeries

/-- A378580: for the theta series `T`, the equation `A(x/A(x)) = T` has exactly one solution
with constant term `1`. -/
theorem quotient_existsUnique (T : PowerSeries ℤ) (hT0 : coeff 0 T = 1)
    (hTsq : ∀ n : ℕ, 0 < n → (∃ k : ℕ, n = k ^ 2) → coeff n T = 2)
    (hTns : ∀ n : ℕ, 0 < n → (¬∃ k : ℕ, n = k ^ 2) → coeff n T = 0) :
    ∃! A : PowerSeries ℤ, constantCoeff A = 1 ∧ A.subst (X * invOfUnit A 1) = T := by
  sorry

/-- A378580: the solution of `A(x/A(x)) = θ₃(x)` satisfies `a(n) ≡ 2 (mod 4)` when `n > 0` is
a perfect square, and `4 ∣ a(n)` for every other `n > 0`. -/
theorem quotient_coeff (T : PowerSeries ℤ) (hT0 : coeff 0 T = 1)
    (hTsq : ∀ n : ℕ, 0 < n → (∃ k : ℕ, n = k ^ 2) → coeff n T = 2)
    (hTns : ∀ n : ℕ, 0 < n → (¬∃ k : ℕ, n = k ^ 2) → coeff n T = 0)
    (A : PowerSeries ℤ) (hA0 : constantCoeff A = 1) (hA : A.subst (X * invOfUnit A 1) = T) :
    (∀ n : ℕ, 0 < n → (∃ k : ℕ, n = k ^ 2) → coeff n A ≡ 2 [ZMOD 4]) ∧
      (∀ n : ℕ, 0 < n → (¬∃ k : ℕ, n = k ^ 2) → (4 : ℤ) ∣ coeff n A) := by
  sorry

/-- A378581: for the theta series `T`, the equation `A(x·A(x)) = T` has exactly one solution
with constant term `1`. -/
theorem product_existsUnique (T : PowerSeries ℤ) (hT0 : coeff 0 T = 1)
    (hTsq : ∀ n : ℕ, 0 < n → (∃ k : ℕ, n = k ^ 2) → coeff n T = 2)
    (hTns : ∀ n : ℕ, 0 < n → (¬∃ k : ℕ, n = k ^ 2) → coeff n T = 0) :
    ∃! A : PowerSeries ℤ, constantCoeff A = 1 ∧ A.subst (X * A) = T := by
  sorry

/-- A378581: the solution of `A(x·A(x)) = θ₃(x)` satisfies `a(n) ≡ 2 (mod 4)` when `n > 0` is
a perfect square, and `4 ∣ a(n)` for every other `n > 0`. -/
theorem product_coeff (T : PowerSeries ℤ) (hT0 : coeff 0 T = 1)
    (hTsq : ∀ n : ℕ, 0 < n → (∃ k : ℕ, n = k ^ 2) → coeff n T = 2)
    (hTns : ∀ n : ℕ, 0 < n → (¬∃ k : ℕ, n = k ^ 2) → coeff n T = 0)
    (A : PowerSeries ℤ) (hA0 : constantCoeff A = 1) (hA : A.subst (X * A) = T) :
    (∀ n : ℕ, 0 < n → (∃ k : ℕ, n = k ^ 2) → coeff n A ≡ 2 [ZMOD 4]) ∧
      (∀ n : ℕ, 0 < n → (¬∃ k : ℕ, n = k ^ 2) → (4 : ℤ) ∣ coeff n A) := by
  sorry

/-- A380060: the equation `A = 1 + 2∑_{k≥1} x^(k²)·((A - x^k)/(1 - x^k·A))^k` has exactly one
solution. -/
theorem implicit_existsUnique :
    ∃! A : PowerSeries ℤ, A = 1 + 2 * PowerSeries.mk (fun n =>
      ∑ k ∈ Finset.range (n + 1), coeff n
        (X ^ ((k + 1) ^ 2) * ((A - X ^ (k + 1)) * invOfUnit (1 - X ^ (k + 1) * A) 1) ^ (k + 1))) := by
  sorry

/-- A380060: for `n > 0`, `a(n) ≡ 2 (mod 4)` exactly when `n` is a perfect square, and
`4 ∣ a(n)` exactly when it is not. -/
theorem implicit_coeff (A : PowerSeries ℤ)
    (hA : A = 1 + 2 * PowerSeries.mk (fun n =>
      ∑ k ∈ Finset.range (n + 1), coeff n
        (X ^ ((k + 1) ^ 2) * ((A - X ^ (k + 1)) * invOfUnit (1 - X ^ (k + 1) * A) 1) ^ (k + 1))))
    (n : ℕ) (hn : 0 < n) :
    (coeff n A ≡ 2 [ZMOD 4] ↔ ∃ j : ℕ, n = j ^ 2) ∧
      ((4 : ℤ) ∣ coeff n A ↔ ¬∃ j : ℕ, n = j ^ 2) := by
  sorry

/-- A380680: for the explicit series `A = 1 + 2∑_{k≥1} x^(k²)·((2 - x^k)/(1 - 2x^k))^k`
and `n > 0`, `a(n) ≡ 2 (mod 4)` exactly when `n = 2j²`, and `4 ∣ a(n)` exactly when `n` is not
of this form. In particular the conjectured square pattern fails: `a(1) = 4` and `a(2) = 6`. -/
theorem explicit_coeff (A : PowerSeries ℤ)
    (hA : A = 1 + 2 * PowerSeries.mk (fun n =>
      ∑ k ∈ Finset.range (n + 1), coeff n
        (X ^ ((k + 1) ^ 2) * ((2 - X ^ (k + 1)) * invOfUnit (1 - X ^ (k + 1) * 2) 1) ^ (k + 1)))) :
    (∀ n : ℕ, 0 < n →
      ((coeff n A ≡ 2 [ZMOD 4] ↔ ∃ j : ℕ, n = 2 * j ^ 2) ∧
        ((4 : ℤ) ∣ coeff n A ↔ ¬∃ j : ℕ, n = 2 * j ^ 2))) ∧
      coeff 1 A = 4 ∧ coeff 2 A = 6 := by
  sorry

/-- A355872: the equation `x = ∑_{m∈ℤ} (-x)^(m²)·A(x)^((m-1)²)`, read coefficientwise, has
exactly one solution. -/
theorem bilateral_existsUnique :
    ∃! A : PowerSeries ℤ, ∀ n : ℕ,
      (∑ᶠ m : ℤ, coeff n ((-X) ^ (m.natAbs ^ 2) * A ^ ((m - 1).natAbs ^ 2))) = coeff n X := by
  sorry

/-- A355872: the solution has nonzero coefficients only at the exponents `4n - 3`, and the
coefficient `a(n)` of `x^(4n-3)` satisfies `a(n) ≡ 2·(-1)^(n-1) (mod 16)` for `n ≥ 1`. -/
theorem bilateral_coeff (A : PowerSeries ℤ)
    (hA : ∀ n : ℕ,
      (∑ᶠ m : ℤ, coeff n ((-X) ^ (m.natAbs ^ 2) * A ^ ((m - 1).natAbs ^ 2))) = coeff n X) :
    (∀ n : ℕ, n % 4 ≠ 1 → coeff n A = 0) ∧
      (∀ n : ℕ, 1 ≤ n → coeff (4 * n - 3) A ≡ 2 * (-1) ^ (n - 1) [ZMOD 16]) := by
  sorry

end OEISProofs.Theta
