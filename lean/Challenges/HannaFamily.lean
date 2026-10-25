module

public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Algebra.Group.Nat.Even

/-!
# The family `A(x·A - m·x·A²) = x²` (OEIS A396843, A396844)

For an integer `m`, consider power series `A(x) = x + a(2)x² + a(3)x³ + ⋯` with integer
coefficients that satisfy

  `A(x·A(x) - m·x·A(x)²) = x²`.

`U.subst B` is Mathlib's substitution `U(B(x))` of a power series `B` with zero constant
term into `U`, and `C m` is the constant series `m`. The number of ones in the binary
expansion of `k` is written `(Nat.digits 2 k).sum`.

OEIS A396843 (Paul D. Hanna) is the case `m = 3`. Its first conjecture says that every
coefficient `a(n)` with `n ≥ 1` is odd (`odd_coeff`). Its second conjecture lists the
residues of `a(n)` modulo `9`; it is false as stated, and `residues_mod_nine` gives the
correct classification. OEIS A396844 is the case `m = 4`; its conjectured residues modulo
`16` fail exactly at `n = 4^k + 1` with `k ≥ 2` (`n = 17, 65, 257, …`), and
`residues_mod_sixteen` gives the correct classification. The remaining theorems concern the
whole family, for every `m` or for `m ≥ 2` as stated, and are proved in the paper on A396843.

Context: these are congruences for the coefficients of power series defined by functional
equations. Results of this kind are known, for example, for the Catalan and Motzkin numbers
(Deutsch and Sagan, J. Number Theory 117 (2006); Eu, Liu and Yeh, European J. Combin. 29
(2008)), and Kauers, Krattenthaler and Müller (Electron. J. Combin. 18(2) (2012), P37) give a
method for the behaviour modulo powers of `2` of recursively defined sequences.
-/

public section

namespace OEISProofs.HannaFamily

open PowerSeries

/-- For every integer `m`, the equation `A(x·A - m·x·A²) = x²` has exactly one solution `A`
with integer coefficients, constant term `0` and coefficient of `x` equal to `1`. -/
theorem existsUnique (m : ℤ) :
    ∃! U : PowerSeries ℤ, coeff 0 U = 0 ∧ coeff 1 U = 1 ∧
      U.subst (X * U - C m * X * U ^ 2) = X ^ 2 := by
  sorry

/-- If `m` is odd, every coefficient `a(n)` with `n ≥ 1` is odd. For `m = 3` this is the
first conjecture of A396843. -/
theorem odd_coeff (m : ℤ) (hm : Odd m) (U : PowerSeries ℤ) (h0 : coeff 0 U = 0)
    (h1 : coeff 1 U = 1) (hU : U.subst (X * U - C m * X * U ^ 2) = X ^ 2)
    (n : ℕ) (hn : 1 ≤ n) :
    Odd (coeff n U) := by
  sorry

/-- If `m` is even, every coefficient `a(n)` with `n ≥ 2` is even. -/
theorem even_coeff (m : ℤ) (hm : Even m) (U : PowerSeries ℤ) (h0 : coeff 0 U = 0)
    (h1 : coeff 1 U = 1) (hU : U.subst (X * U - C m * X * U ^ 2) = X ^ 2)
    (n : ℕ) (hn : 2 ≤ n) :
    Even (coeff n U) := by
  sorry

/-- For `m ≥ 2`, the residues modulo `m²`: `a(2^j + 1) ≡ m·(-1)^j`, and `m²` divides every
other coefficient `a(n)` with `n ≥ 2`. -/
theorem modEq_sq (m : ℤ) (hm : 2 ≤ m) (U : PowerSeries ℤ) (h0 : coeff 0 U = 0)
    (h1 : coeff 1 U = 1) (hU : U.subst (X * U - C m * X * U ^ 2) = X ^ 2) :
    (∀ j : ℕ, coeff (2 ^ j + 1) U ≡ m * (-1) ^ j [ZMOD m ^ 2]) ∧
      (∀ n : ℕ, 2 ≤ n → (¬∃ j : ℕ, n = 2 ^ j + 1) → m ^ 2 ∣ coeff n U) := by
  sorry

/-- For every integer `m` and `n ≥ 1`, `m^s` divides `a(n)`, where `s` is the number of ones
in the binary expansion of `n - 1`. This is the statement about `a(n)` in the theorem on binary
digits of the paper on A396843; the companion statement for the coefficients of the inverse
series is proved in `Entries/A396843.lean` but is not compared here. -/
theorem pow_digitSum_dvd (m : ℤ) (U : PowerSeries ℤ) (h0 : coeff 0 U = 0)
    (h1 : coeff 1 U = 1) (hU : U.subst (X * U - C m * X * U ^ 2) = X ^ 2)
    (n : ℕ) (hn : 1 ≤ n) :
    m ^ (Nat.digits 2 (n - 1)).sum ∣ coeff n U := by
  sorry

/-- Let `m ≥ 2`, and let `p` be a prime dividing `m` exactly `e` times. Then for `n ≥ 2`,
`p^(e·s)` divides `a(n)`, where `s` is the number of ones in the binary expansion of
`n - 1`; and `p` divides `a(n)` exactly `e` times if and only if `n = 2^j + 1`. -/
theorem prime_pow_dvd (m : ℤ) (hm : 2 ≤ m) (p : ℕ) (hp : p.Prime) (hpm : (p : ℤ) ∣ m)
    (e : ℕ) (he : (p : ℤ) ^ e ∣ m ∧ ¬(p : ℤ) ^ (e + 1) ∣ m)
    (U : PowerSeries ℤ) (h0 : coeff 0 U = 0)
    (h1 : coeff 1 U = 1) (hU : U.subst (X * U - C m * X * U ^ 2) = X ^ 2)
    (n : ℕ) (hn : 2 ≤ n) :
    (p : ℤ) ^ (e * (Nat.digits 2 (n - 1)).sum) ∣ coeff n U ∧
      (((p : ℤ) ^ e ∣ coeff n U ∧ ¬(p : ℤ) ^ (e + 1) ∣ coeff n U) ↔
        ∃ j : ℕ, n = 2 ^ j + 1) := by
  sorry

/-- The residues modulo `9` for `m = 3` (OEIS A396843): `a(4^k + 1) ≡ 3`,
`a(2·4^k + 1) ≡ 6`, and `9` divides every other coefficient `a(n)` with `n ≥ 2`. -/
theorem residues_mod_nine (U : PowerSeries ℤ) (h0 : coeff 0 U = 0)
    (h1 : coeff 1 U = 1) (hU : U.subst (X * U - C 3 * X * U ^ 2) = X ^ 2) :
    (∀ k : ℕ, coeff (4 ^ k + 1) U ≡ 3 [ZMOD 9]) ∧
      (∀ k : ℕ, coeff (2 * 4 ^ k + 1) U ≡ 6 [ZMOD 9]) ∧
      (∀ n : ℕ, 2 ≤ n → (¬∃ k : ℕ, n = 4 ^ k + 1) → (¬∃ k : ℕ, n = 2 * 4 ^ k + 1) →
        (9 : ℤ) ∣ coeff n U) := by
  sorry

/-- The residues modulo `16` for `m = 4` (OEIS A396844): `a(4^k + 1) ≡ 4`,
`a(2·4^k + 1) ≡ 12`, and `16` divides every other coefficient `a(n)` with `n ≥ 2`. -/
theorem residues_mod_sixteen (U : PowerSeries ℤ) (h0 : coeff 0 U = 0)
    (h1 : coeff 1 U = 1) (hU : U.subst (X * U - C 4 * X * U ^ 2) = X ^ 2) :
    (∀ k : ℕ, coeff (4 ^ k + 1) U ≡ 4 [ZMOD 16]) ∧
      (∀ k : ℕ, coeff (2 * 4 ^ k + 1) U ≡ 12 [ZMOD 16]) ∧
      (∀ n : ℕ, 2 ≤ n → (¬∃ k : ℕ, n = 4 ^ k + 1) → (¬∃ k : ℕ, n = 2 * 4 ^ k + 1) →
        (16 : ℤ) ∣ coeff n U) := by
  sorry

end OEISProofs.HannaFamily
