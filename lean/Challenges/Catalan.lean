module

public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Data.Int.ModEq
public import Mathlib.Algebra.Group.Nat.Even

/-!
# Catalan-type equations (OEIS A393172, A393171, A389536, A195194)

All series have integer coefficients; a series is *normalized* if it has the form
`x + a(2)x² + ⋯`. `F.subst B` is Mathlib's substitution `F(B(x))` of a series `B` with zero
constant term.

The solutions of the equations below reduce, modulo `2`, `4` or `8`, to expressions in the
Catalan series `C(x) = x + x² + 2x³ + 5x⁴ + ⋯`, the solution of `C = x + C²` with `C(0) = 0`,
whose coefficient of `x^n` is odd exactly when `n` is a power of `2`.

* **A393172.** `F(x - x²) = x + F(x)²`. Conjectured: for `n > 1`, `a(n) ≡ 2 (mod 4)` if `n` is
  a power of `2`, and `4 ∣ a(n)` otherwise.
* **A393171.** `B(x) = x + B(C(x))²`. Conjectured: for `n > 2`, `a(n) ≡ 4 (mod 8)` if `n = 2^k`
  or `n = 2^k + 1` with `k ≥ 1`, and `8 ∣ a(n)` otherwise.
* **A389536.** `F(x² + 2x³) = x·F(x)` (the entry writes `A(x) = A(x² + 2x³)/x`). Conjectured: for `n > 1`, `a(n) ≡ 2 (mod 4)` if
  `n = 2^k + 1`, and `4 ∣ a(n)` otherwise.
* **A195194.** The infinitely nested series reversion
  `A(x) = Series_Reversion(x - x·Series_Reversion(x - 2x·Series_Reversion(x - 3x·⋯)))`. It is
  formalized as a sequence of normalized series `F₀, F₁, …` in which `F_j` and
  `x - (j+1)·x·F_{j+1}` are compositional inverses of each other; `A = F₀`. The theorem
  `a195194_finite_tower` ties this to the nest in the definition: cut off after `d` reversions,
  with the innermost reversion replaced by `x`, the nest has the same coefficients as `A` up to
  degree `d + 1`. Conjectured: `a(n)` is odd exactly when `n` is a power of `2`.

Context: these are congruences for the coefficients of power series defined by functional
equations. The residues of the Catalan numbers modulo `4` and `8` were determined by Eu, Liu
and Yeh (European J. Combin. 29 (2008)); see also Deutsch and Sagan (J. Number Theory 117
(2006)), and Kauers, Krattenthaler and Müller (Electron. J. Combin. 18(2) (2012), P37) for a
method for the behaviour modulo powers of `2` of recursively defined sequences.
-/

public section

namespace OEISProofs.Catalan

open PowerSeries

/-- A393172: the equation `F(x - x²) = x + F²` has exactly one normalized solution. -/
theorem a393172_existsUnique :
    ∃! F : PowerSeries ℤ, coeff 0 F = 0 ∧ coeff 1 F = 1 ∧ F.subst (X - X ^ 2) = X + F ^ 2 := by
  sorry

/-- A393172: for `n > 1`, `a(n) ≡ 2 (mod 4)` exactly when `n` is a power of `2`, and
`4 ∣ a(n)` exactly when it is not. -/
theorem a393172_coeff (F : PowerSeries ℤ) (h0 : coeff 0 F = 0) (h1 : coeff 1 F = 1)
    (hF : F.subst (X - X ^ 2) = X + F ^ 2) (n : ℕ) (hn : 1 < n) :
    (coeff n F ≡ 2 [ZMOD 4] ↔ ∃ k : ℕ, n = 2 ^ k) ∧
      ((4 : ℤ) ∣ coeff n F ↔ ¬∃ k : ℕ, n = 2 ^ k) := by
  sorry

/-- A393171: if `C` is the Catalan series (`C = x + C²`, `C(0) = 0`), the equation
`B = x + B(C(x))²` has exactly one normalized solution. -/
theorem a393171_existsUnique (C : PowerSeries ℤ) (hC0 : coeff 0 C = 0) (hC : C = X + C ^ 2) :
    ∃! B : PowerSeries ℤ, coeff 0 B = 0 ∧ coeff 1 B = 1 ∧ B = X + (B.subst C) ^ 2 := by
  sorry

/-- A393171: for `n > 2`, `a(n) ≡ 4 (mod 8)` exactly when `n = 2^k` or `n = 2^k + 1` for some
`k ≥ 1`, and `8 ∣ a(n)` exactly when it is not. -/
theorem a393171_coeff (C : PowerSeries ℤ) (hC0 : coeff 0 C = 0) (hC : C = X + C ^ 2)
    (B : PowerSeries ℤ) (h0 : coeff 0 B = 0) (h1 : coeff 1 B = 1)
    (hB : B = X + (B.subst C) ^ 2) (n : ℕ) (hn : 2 < n) :
    (coeff n B ≡ 4 [ZMOD 8] ↔ ∃ k : ℕ, 1 ≤ k ∧ (n = 2 ^ k ∨ n = 2 ^ k + 1)) ∧
      ((8 : ℤ) ∣ coeff n B ↔ ¬∃ k : ℕ, 1 ≤ k ∧ (n = 2 ^ k ∨ n = 2 ^ k + 1)) := by
  sorry

/-- A389536: the equation `F(x² + 2x³) = x·F` has exactly one normalized solution. -/
theorem a389536_existsUnique :
    ∃! F : PowerSeries ℤ, coeff 0 F = 0 ∧ coeff 1 F = 1 ∧
      F.subst (X ^ 2 + 2 * X ^ 3) = X * F := by
  sorry

/-- A389536: for `n > 1`, `a(n) ≡ 2 (mod 4)` exactly when `n = 2^k + 1`, and `4 ∣ a(n)` exactly
when it is not. -/
theorem a389536_coeff (F : PowerSeries ℤ) (h0 : coeff 0 F = 0) (h1 : coeff 1 F = 1)
    (hF : F.subst (X ^ 2 + 2 * X ^ 3) = X * F) (n : ℕ) (hn : 1 < n) :
    (coeff n F ≡ 2 [ZMOD 4] ↔ ∃ k : ℕ, n = 2 ^ k + 1) ∧
      ((4 : ℤ) ∣ coeff n F ↔ ¬∃ k : ℕ, n = 2 ^ k + 1) := by
  sorry

/-- A195194: there is exactly one sequence `F₀, F₁, …` of normalized series such that, for
every `j`, `F_j` and `x - (j+1)·x·F_{j+1}` are compositional inverses of each other. -/
theorem a195194_existsUnique :
    ∃! F : ℕ → PowerSeries ℤ, (∀ j, coeff 0 (F j) = 0 ∧ coeff 1 (F j) = 1) ∧
      ∀ j, (X - C ((j + 1 : ℕ) : ℤ) * X * F (j + 1)).subst (F j) = X ∧
        (F j).subst (X - C ((j + 1 : ℕ) : ℤ) * X * F (j + 1)) = X := by
  sorry

/-- A195194: let `G d j` be the nest of depth `d` starting at level `j`, that is, `G 0 j = x`
and `G (d+1) j` is the compositional inverse of `x - (j+1)·x·G d (j+1)`. Then the coefficients of
`x^n` in `G d 0` and in `A = F₀` agree for `n ≤ d + 1`. So the nested reversion of the
definition, cut off after `d` reversions, gives `a(0), …, a(d+1)` correctly. -/
theorem a195194_finite_tower (F : ℕ → PowerSeries ℤ)
    (hF0 : ∀ j, coeff 0 (F j) = 0 ∧ coeff 1 (F j) = 1)
    (hF : ∀ j, (X - C ((j + 1 : ℕ) : ℤ) * X * F (j + 1)).subst (F j) = X ∧
      (F j).subst (X - C ((j + 1 : ℕ) : ℤ) * X * F (j + 1)) = X)
    (G : ℕ → ℕ → PowerSeries ℤ) (hG0 : ∀ j, G 0 j = X)
    (hG : ∀ d j, coeff 0 (G (d + 1) j) = 0 ∧ coeff 1 (G (d + 1) j) = 1 ∧
      (X - C ((j + 1 : ℕ) : ℤ) * X * G d (j + 1)).subst (G (d + 1) j) = X ∧
      (G (d + 1) j).subst (X - C ((j + 1 : ℕ) : ℤ) * X * G d (j + 1)) = X)
    (d n : ℕ) (hn : n ≤ d + 1) :
    coeff n (G d 0) = coeff n (F 0) := by
  sorry

/-- A195194: the coefficient `a(n)` of `x^n` in `A = F₀` is odd exactly when `n` is a power
of `2`. -/
theorem a195194_coeff (F : ℕ → PowerSeries ℤ) (hF0 : ∀ j, coeff 0 (F j) = 0 ∧ coeff 1 (F j) = 1)
    (hF : ∀ j, (X - C ((j + 1 : ℕ) : ℤ) * X * F (j + 1)).subst (F j) = X ∧
      (F j).subst (X - C ((j + 1 : ℕ) : ℤ) * X * F (j + 1)) = X)
    (n : ℕ) :
    Odd (coeff n (F 0)) ↔ ∃ k : ℕ, n = 2 ^ k := by
  sorry

end OEISProofs.Catalan
