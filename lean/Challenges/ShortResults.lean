module

public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.Data.Int.ModEq
public import Mathlib.Algebra.Group.Nat.Even

/-!
# Results with short proofs (OEIS A396093, A392210, A380056)

All series are formal power series. `F.subst B` is Mathlib's substitution `F(B(x))` of a
series `B` with zero constant term. A series is *normalized* if it has the form
`x + a(2)x² + ⋯`.

* **A396093.** `A = B(B(B(x)))` with `B(x) = x/(1-x)²`. Conjectured: `a(2n)` is even for
  `n ≥ 1`, and `a(2n-1)` is even exactly when `n = 5k - 2`; both follow from the complete
  rule: `a(n)` is odd exactly when `n ≡ 1, 3, 7, 9 (mod 10)`.
* **A392210.** The infinitely nested square `x + sq(x/(1-x) + sq(x/(1-2x) + sq(x/(1-3x) + ⋯)))`
  with `sq(y) = y²`; the entry observes that `a(2n-1)` is even for `n > 1`. It is formalized
  through formula (1) of the entry, `F(x) = x + F(x/(1-x))²`, as the unique normalized solution
  (`x/(1-x)` is written `X * PowerSeries.mk 1`). The accompanying paper proves that the nested
  expression defines the same series; that step is not formalized.
* **A380056.** `a(n) = n!·[x^n] (e^x - 1)/cos(2x)`. Conjectured: `a(n) ≡ 1 (mod 4)` for `n ≥ 1`,
  and `5 ∣ a(4n)`. Proved: in addition `a(n) ≡ 2·2^n + 3·4^n (mod 5)`, so `5 ∣ a(n)` exactly
  when `4 ∣ n`. The series `A` is characterized by `A(x)·cos(2x) = e^x - 1` over `ℚ`.

Context: these are congruences for the coefficients of power series, given explicitly or by a
functional equation. Results of this kind are known, for example, for the Catalan and Motzkin
numbers (Deutsch and Sagan, J. Number Theory 117 (2006); Eu, Liu and Yeh, European J. Combin. 29
(2008)), and Kauers, Krattenthaler and Müller (Electron. J. Combin. 18(2) (2012), P37) give a
method for the behaviour modulo powers of `2` of recursively defined sequences.
-/

public section

namespace OEISProofs.ShortResults

open PowerSeries

/-- A396093: if `B(x)·(1-x)² = x` (so `B = x/(1-x)²`), the coefficient `a(n)` of `x^n` in
`B(B(B(x)))` is odd exactly when `n ≡ 1, 3, 7, 9 (mod 10)`; in particular `a(2n)` is even, and
for `n ≥ 1`, `a(2n-1)` is even exactly when `n = 5k - 2` with `k ≥ 1`. -/
theorem a396093_coeff (B : PowerSeries ℤ) (hB : B * (1 - X) ^ 2 = X) :
    (∀ n : ℕ, Even (coeff n (B.subst (B.subst B))) ↔
        ¬(n % 10 = 1 ∨ n % 10 = 3 ∨ n % 10 = 7 ∨ n % 10 = 9)) ∧
      (∀ n : ℕ, Even (coeff (2 * n) (B.subst (B.subst B)))) ∧
      (∀ n : ℕ, 1 ≤ n → (Even (coeff (2 * n - 1) (B.subst (B.subst B))) ↔
        ∃ k : ℕ, 1 ≤ k ∧ n = 5 * k - 2)) := by
  sorry

/-- A392210: the equation `F(x) = x + F(x/(1-x))²` has exactly one normalized solution. -/
theorem a392210_existsUnique :
    ∃! F : PowerSeries ℤ, coeff 0 F = 0 ∧ coeff 1 F = 1 ∧
      F = X + (F.subst (X * PowerSeries.mk (1 : ℕ → ℤ))) ^ 2 := by
  sorry

/-- A392210: for `n > 1`, the coefficient `a(2n-1)` of the solution is even. -/
theorem a392210_coeff (F : PowerSeries ℤ) (h0 : coeff 0 F = 0) (h1 : coeff 1 F = 1)
    (hF : F = X + (F.subst (X * PowerSeries.mk (1 : ℕ → ℤ))) ^ 2) (n : ℕ) (hn : 1 < n) :
    Even (coeff (2 * n - 1) F) := by
  sorry

/-- A380056: there is exactly one series `A` over `ℚ` with `A(x)·cos(2x) = e^x - 1`. -/
theorem a380056_existsUnique :
    ∃! A : PowerSeries ℚ, A * rescale (2 : ℚ) (cos ℚ) = exp ℚ - 1 := by
  sorry

/-- A380056: the numbers `a(n) = n!·[x^n] A` are integers. -/
theorem a380056_integral (A : PowerSeries ℚ) (hA : A * rescale (2 : ℚ) (cos ℚ) = exp ℚ - 1)
    (n : ℕ) :
    ∃ z : ℤ, (z : ℚ) = (n.factorial : ℚ) * coeff n A := by
  sorry

/-- A380056: `a(n) ≡ 1 (mod 4)` for `n ≥ 1`, `a(n) ≡ 2·2^n + 3·4^n (mod 5)`, and `5 ∣ a(n)`
exactly when `4 ∣ n`. -/
theorem a380056_coeff (A : PowerSeries ℚ) (hA : A * rescale (2 : ℚ) (cos ℚ) = exp ℚ - 1)
    (a : ℕ → ℤ) (ha : ∀ n, (a n : ℚ) = (n.factorial : ℚ) * coeff n A) :
    (∀ n : ℕ, 1 ≤ n → a n ≡ 1 [ZMOD 4]) ∧
      (∀ n : ℕ, a n ≡ 2 * 2 ^ n + 3 * 4 ^ n [ZMOD 5]) ∧
      (∀ n : ℕ, (5 : ℤ) ∣ a n ↔ 4 ∣ n) := by
  sorry

end OEISProofs.ShortResults
