module

public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Data.Int.ModEq
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Consecutive iterates `F = x + F^{∘r}·F^{∘(r+1)}` (OEIS A396099, A396798, A396807)

For a natural number `r`, consider power series `F(x) = x + a(2)x² + a(3)x³ + ⋯` with integer
coefficients that satisfy

  `F(x) = x + F^{∘r}(x)·F^{∘(r+1)}(x)`,

where `F^{∘k}` is the `k`-th compositional iterate: `F^{∘0}(x) = x` and
`F^{∘(k+1)} = F ∘ F^{∘k}`. In Lean the `k`-th iterate is `(fun G : PowerSeries ℤ => (F.subst G : PowerSeries ℤ))^[k] X`, where
`F.subst G` is Mathlib's substitution `F(G(x))` of a series `G` with zero constant term.

OEIS A396099, A396798 and A396807 (Paul D. Hanna) are the cases `r = 2, 4, 5`. The main theorem
(`iterate_coeff_modEq`, `inverse_iterate_coeff_modEq`) describes every iterate modulo `2r`:
for every integer `k` and `n ≥ 1`, the coefficient of `x^n` in `F^{∘k}` is congruent to
`k^(n-1)` modulo `2r`, plus the correction `r·C(n-2, 2)` (for `n ≥ 4`) when `r` is even and
`k` is odd. The iterates with negative `k` are the iterates of the compositional inverse `G`
of `F`, the series with `G(F(x)) = x`. The conjectures of A396807 are the case `r = 5`, and the
seven conjectures of A396798 about the iterates `F^{∘2}, …, F^{∘8}` are the case `r = 4`. The
conjectures of A396099 and the corrected first conjecture of A396798 are stated separately.
-/

public section

namespace OEISProofs.ConsecutiveIterates

open PowerSeries

/-- For every natural number `r`, the equation `F = x + F^{∘r}·F^{∘(r+1)}` has exactly one
solution `F` with integer coefficients, constant term `0` and coefficient of `x` equal
to `1`. -/
theorem existsUnique (r : ℕ) :
    ∃! F : PowerSeries ℤ, coeff 0 F = 0 ∧ coeff 1 F = 1 ∧
      F = X + (fun G : PowerSeries ℤ => (F.subst G : PowerSeries ℤ))^[r] X * (fun G : PowerSeries ℤ => (F.subst G : PowerSeries ℤ))^[r + 1] X := by
  sorry

/-- For `r ≥ 1`, every `k ≥ 0` and every `n ≥ 1`, the coefficient of `x^n` in the `k`-th
iterate of the solution is congruent modulo `2r` to `k^(n-1)`, plus `r·C(n-2, 2)` when `r`
is even, `k` is odd and `n ≥ 4`. -/
theorem iterate_coeff_modEq (r : ℕ) (hr : 0 < r) (F : PowerSeries ℤ) (h0 : coeff 0 F = 0)
    (h1 : coeff 1 F = 1)
    (hF : F = X + (fun G : PowerSeries ℤ => (F.subst G : PowerSeries ℤ))^[r] X * (fun G : PowerSeries ℤ => (F.subst G : PowerSeries ℤ))^[r + 1] X)
    (k n : ℕ) (hn : 1 ≤ n) :
    coeff n ((fun G : PowerSeries ℤ => (F.subst G : PowerSeries ℤ))^[k] X) ≡
      (k : ℤ) ^ (n - 1) +
        (if Even r ∧ Odd k then (r : ℤ) * (if 4 ≤ n then ((n - 2).choose 2 : ℤ) else 0)
          else 0) [ZMOD (2 * r : ℕ)] := by
  sorry

/-- The same description for the negative iterates: if `G(F(x)) = x`, the coefficient of
`x^n` (`n ≥ 1`) in the `k`-th iterate of `G` is congruent modulo `2r` to `(-k)^(n-1)`, plus
`r·C(n-2, 2)` when `r` is even, `k` is odd and `n ≥ 4`. -/
theorem inverse_iterate_coeff_modEq (r : ℕ) (hr : 0 < r) (F : PowerSeries ℤ)
    (h0 : coeff 0 F = 0) (h1 : coeff 1 F = 1)
    (hF : F = X + (fun G : PowerSeries ℤ => (F.subst G : PowerSeries ℤ))^[r] X * (fun G : PowerSeries ℤ => (F.subst G : PowerSeries ℤ))^[r + 1] X)
    (G : PowerSeries ℤ) (hG : G.subst F = X) (k n : ℕ) (hn : 1 ≤ n) :
    coeff n ((fun H : PowerSeries ℤ => (G.subst H : PowerSeries ℤ))^[k] X) ≡
      (-(k : ℤ)) ^ (n - 1) +
        (if Even r ∧ Odd k then (r : ℤ) * (if 4 ≤ n then ((n - 2).choose 2 : ℤ) else 0)
          else 0) [ZMOD (2 * r : ℕ)] := by
  sorry

/-- The four conjectures of A396099 (`r = 2`, so `F = x + F(F(x))·F(F(F(x)))`): every
coefficient `a(n)` with `n ≥ 1` is odd; for `n ≥ 3`, `a(n) ≡ 3 (mod 4)` if `n ≡ 0, 1 (mod 4)`
and `a(n) ≡ 1 (mod 4)` otherwise; the coefficients of `F(F(x))` beyond `x²` are divisible by
`4`; and the coefficients of `F(x) - x·F(F(F(x)))` beyond `x²` are `≡ 2 (mod 4)`. -/
theorem a396099_conjectures (F : PowerSeries ℤ) (h0 : coeff 0 F = 0) (h1 : coeff 1 F = 1)
    (hF : F = X + F.subst F * F.subst (F.subst F)) :
    (∀ n : ℕ, 0 < n → Odd (coeff n F)) ∧
      (∀ n : ℕ, 3 ≤ n → coeff n F ≡ (if n % 4 = 0 ∨ n % 4 = 1 then 3 else 1) [ZMOD 4]) ∧
      (∀ n : ℕ, 2 < n → coeff n (F.subst F) ≡ 0 [ZMOD 4]) ∧
      (∀ n : ℕ, 2 < n → coeff n (F - X * F.subst (F.subst F)) ≡ 2 [ZMOD 4]) := by
  sorry

/-- The corrected first conjecture of A396798 (`r = 4`): for `n ≥ 2`, `a(n) ≡ 5 (mod 8)` if
`n ≡ 0, 1 (mod 4)` and `a(n) ≡ 1 (mod 8)` otherwise, so the residues repeat `1, 1, 5, 5` from
`n = 2` on. The entry conjectured this block from `n = 1`, which fails: `a(3) = 9 ≡ 1 (mod 8)`. -/
theorem a396798_residues (F : PowerSeries ℤ) (h0 : coeff 0 F = 0) (h1 : coeff 1 F = 1)
    (hF : F = X + (fun G : PowerSeries ℤ => (F.subst G : PowerSeries ℤ))^[4] X * (fun G : PowerSeries ℤ => (F.subst G : PowerSeries ℤ))^[5] X)
    (n : ℕ) (hn : 2 ≤ n) :
    coeff n F ≡ (if n % 4 = 0 ∨ n % 4 = 1 then 5 else 1) [ZMOD 8] := by
  sorry

end OEISProofs.ConsecutiveIterates
