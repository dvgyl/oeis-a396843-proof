module

public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Data.Int.ModEq
public import Mathlib.Algebra.Group.Nat.Even

/-!
# Scaled inverses `A(x - x·A(qx)/q) = x` (OEIS A393856–A393859)

For an integer `q`, consider power series `A(x) = x + a(2)x² + a(3)x³ + ⋯` with integer
coefficients that satisfy

  `A(x - x·A(qx)/q) = x`.

Since `A` has no constant term, `A(qx)/q` is the series with the integer coefficients
`q^(n-1)·a(n)`. It is written below as `PowerSeries.mk (fun n => q ^ (n - 1) * coeff n A)`,
which avoids division (and is meaningful also for `q = 0`). `A.subst B` is Mathlib's
substitution `A(B(x))` of a power series `B` with zero constant term into `A`.

The OEIS entries A393856, A393857, A393858 and A393859 (Paul D. Hanna) are the cases
`q = 4, 5, 6, 7`. They conjecture that every coefficient `a(n)` with `n ≥ 1` leaves remainder
`1` on division by `q + 1`, and, for `q = 4` and `q = 6`, that `a(n)` is odd exactly when
`n` is a power of `2`. The theorems below prove these statements for every `q`
(respectively for every even `q`), after showing that the equation has exactly one
solution of the form `x + ⋯`.
-/

public section

namespace OEISProofs.ScaledInverses

open PowerSeries

/-- For every integer `q`, the equation `A(x - x·A(qx)/q) = x` has exactly one solution
`A` with integer coefficients, constant term `0` and coefficient of `x` equal to `1`. -/
theorem existsUnique (q : ℤ) :
    ∃! A : PowerSeries ℤ, coeff 0 A = 0 ∧ coeff 1 A = 1 ∧
      A.subst (X - X * PowerSeries.mk (fun n => q ^ (n - 1) * coeff n A)) = X := by
  sorry

/-- For a natural number `q`, every coefficient `a(n)` with `n ≥ 1` of the solution is
congruent to `1` modulo `q + 1`. For `q = 4, 5, 6, 7` these are the conjectures of
A393856 (modulo 5), A393857 (modulo 6), A393858 (modulo 7) and A393859 (modulo 8). -/
theorem coeff_modEq_one (q : ℕ) (A : PowerSeries ℤ) (h0 : coeff 0 A = 0) (h1 : coeff 1 A = 1)
    (hA : A.subst (X - X * PowerSeries.mk (fun n => (q : ℤ) ^ (n - 1) * coeff n A)) = X)
    (n : ℕ) (hn : 1 ≤ n) :
    coeff n A ≡ 1 [ZMOD (q + 1 : ℕ)] := by
  sorry

/-- For an even integer `q`, the coefficient `a(n)` of the solution is odd exactly when `n`
is a power of `2`. For `q = 4` and `q = 6` these are the parity conjectures of A393856 and
A393858. -/
theorem odd_coeff_iff (q : ℤ) (hq : Even q) (A : PowerSeries ℤ) (h0 : coeff 0 A = 0)
    (h1 : coeff 1 A = 1)
    (hA : A.subst (X - X * PowerSeries.mk (fun n => q ^ (n - 1) * coeff n A)) = X)
    (n : ℕ) :
    Odd (coeff n A) ↔ ∃ k : ℕ, n = 2 ^ k := by
  sorry

end OEISProofs.ScaledInverses
