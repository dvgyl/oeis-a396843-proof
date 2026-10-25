module

public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Data.Int.ModEq
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Further OEIS results (A396102, A397346, A394576)

All series are formal power series. `F.subst B` is Mathlib's substitution `F(B(x))` of a
series `B` with zero constant term, and the `k`-th compositional iterate of `U` is
`(fun G : PowerSeries ℤ => (U.subst G : PowerSeries ℤ))^[k] X`. A series is *normalized* if it
has the form `x + a(2)x² + ⋯`.

* **A396102.** `A(A(A(x))) = (1+x)·A(A(x))`, conjectured `a(n) ≡ 1 (mod 3)`. It is the case
  `r = 3` of the family `U^{∘r} = (1+x)·U^{∘(r-1)}`, for which every coefficient is `1` modulo
  `r` and the `k`-th iterate has coefficients `≡ k^(n-1) (mod r)`.
* **A397346.** `A(x) = exp(x + ∑_{n≥2} (2n²-1)/(2n²)·a(n)·x^n)`. Conjectured: from `n = 2` on,
  `a(n) mod 8` repeats `4, 2, 0, 2`. The entry's recurrence (its formula (7)) is
  `a(0) = a(1) = 1`, `a(n+2) = 2(n+2)a(n+1) + (n+2)∑_{i<n} (2(i+2)²-1)/(i+2)·a(i+2)·a(n-i)`.
  `a397346_exp_iff` shows that the entry's equation has exactly one solution, the generating
  function of the solution of the recurrence; the other theorems concern that solution: it
  consists of integers with `n ∣ a(n)`, and `a(n)/n ≡ 6 (mod 8)` if `n ≡ 3 (mod 4)` and
  `≡ 2 (mod 8)` otherwise.
* **A394576.** `a(1) = 1`, and `a(n+1)` is the least integer greater than `a(n)` that is not a
  sum `a(k) + a(k+1) + a(k+2)` of three consecutive earlier terms. Conjectured:
  `a(n) ≤ ⌊(4n-1)/3⌋`. Proved: `⌊(4n-3)/3⌋ ≤ a(n) ≤ ⌊(4n-1)/3⌋`, so `a(3k) = 4k - 1`. In Lean
  the sequence is indexed from `0`: `f m` is `a(m+1)`, and natural-number division `/` is the
  floor.

Context: A396102 and A397346 concern congruences for the coefficients of power series defined by functional
equations. Results of this kind are known, for example, for the Catalan and Motzkin numbers
(Deutsch and Sagan, J. Number Theory 117 (2006); Eu, Liu and Yeh, European J. Combin. 29
(2008)), and Kauers, Krattenthaler and Müller (Electron. J. Combin. 18(2) (2012), P37) give a
method for the behaviour modulo powers of `2` of recursively defined sequences.
-/

public section

namespace OEISProofs.FurtherResults

open PowerSeries

/-- A396102 and its family: for `r ≥ 1`, the equation `U^{∘r} = (1+x)·U^{∘(r-1)}` has exactly
one normalized solution. A396102 is the case `r = 3`. -/
theorem a396102_existsUnique (r : ℕ) (hr : 1 ≤ r) :
    ∃! U : PowerSeries ℤ, coeff 0 U = 0 ∧ coeff 1 U = 1 ∧
      (fun G : PowerSeries ℤ => (U.subst G : PowerSeries ℤ))^[r] X = (1 + X) * (fun G : PowerSeries ℤ => (U.subst G : PowerSeries ℤ))^[r - 1] X := by
  sorry

/-- A396102 and its family: for `r ≥ 1`, every coefficient `a(n)` (`n ≥ 1`) of the solution of
`U^{∘r} = (1+x)·U^{∘(r-1)}` is `≡ 1 (mod r)`, and the coefficient of `x^n` in the `k`-th
iterate is `≡ k^(n-1) (mod r)`. For `r = 3` this is the conjecture of A396102. -/
theorem a396102_coeff (r : ℕ) (hr : 1 ≤ r) (U : PowerSeries ℤ) (h0 : coeff 0 U = 0)
    (h1 : coeff 1 U = 1)
    (hU : (fun G : PowerSeries ℤ => (U.subst G : PowerSeries ℤ))^[r] X = (1 + X) * (fun G : PowerSeries ℤ => (U.subst G : PowerSeries ℤ))^[r - 1] X) :
    (∀ n : ℕ, 1 ≤ n → coeff n U ≡ 1 [ZMOD r]) ∧
      (∀ k n : ℕ, 1 ≤ n → coeff n ((fun G : PowerSeries ℤ => (U.subst G : PowerSeries ℤ))^[k] X) ≡ (k : ℤ) ^ (n - 1) [ZMOD r]) := by
  sorry

/-- A397346: the recurrence of the entry (its formula (7)) has exactly one solution. -/
theorem a397346_existsUnique :
    ∃! s : ℕ → ℚ, s 0 = 1 ∧ s 1 = 1 ∧ ∀ n : ℕ,
      s (n + 2) = 2 * (n + 2 : ℚ) * s (n + 1) +
        (n + 2 : ℚ) * ∑ i : Fin n,
          (2 * (i.val + 2 : ℚ) ^ 2 - 1) / (i.val + 2 : ℚ) * s (i.val + 2) * s (n - i.val) := by
  sorry

/-- A397346: the solution of the recurrence consists of integers `z(n)` with `n ∣ z(n)` for
`n ≥ 1`; the quotient `z(n)/n` is `≡ 6 (mod 8)` if `n ≡ 3 (mod 4)` and `≡ 2 (mod 8)` otherwise
(`n ≥ 2`); and so `z(n) mod 8` repeats `4, 2, 0, 2` from `n = 2` on. -/
theorem a397346_coeff (s : ℕ → ℚ) (h0 : s 0 = 1) (h1 : s 1 = 1)
    (hs : ∀ n : ℕ,
      s (n + 2) = 2 * (n + 2 : ℚ) * s (n + 1) +
        (n + 2 : ℚ) * ∑ i : Fin n,
          (2 * (i.val + 2 : ℚ) ^ 2 - 1) / (i.val + 2 : ℚ) * s (i.val + 2) * s (n - i.val)) :
    ∃ z : ℕ → ℤ, (∀ n, s n = (z n : ℚ)) ∧ (∀ n : ℕ, 0 < n → (n : ℤ) ∣ z n) ∧
      (∀ n : ℕ, 2 ≤ n → z n / n ≡ (if n % 4 = 3 then 6 else 2) [ZMOD 8]) ∧
      (∀ k : ℕ, z (4 * k + 2) ≡ 4 [ZMOD 8] ∧ z (4 * k + 3) ≡ 2 [ZMOD 8] ∧
        z (4 * k + 4) ≡ 0 [ZMOD 8] ∧ z (4 * k + 5) ≡ 2 [ZMOD 8]) := by
  sorry

/-- A397346: the entry's equation `A = exp(H_A)`, where `H_A = x + ∑_{n≥2} (2n²-1)/(2n²)·a(n)·x^n`
is built from the coefficients `a(n)` of `A` itself, has exactly one solution over `ℚ`: the
generating function `∑ s(n)xⁿ` of the solution `s` of the recurrence (7). Here `exp(H)` is
Mathlib's substitution `(exp ℚ).subst H`. -/
theorem a397346_exp_iff (s : ℕ → ℚ) (h0 : s 0 = 1) (h1 : s 1 = 1)
    (hs : ∀ n : ℕ,
      s (n + 2) = 2 * (n + 2 : ℚ) * s (n + 1) +
        (n + 2 : ℚ) * ∑ i : Fin n,
          (2 * (i.val + 2 : ℚ) ^ 2 - 1) / (i.val + 2 : ℚ) * s (i.val + 2) * s (n - i.val))
    (A : PowerSeries ℚ) :
    A = ((exp ℚ).subst (PowerSeries.mk fun n =>
        if n = 0 then 0 else if n = 1 then 1 else
          (2 * (n : ℚ) ^ 2 - 1) / (2 * (n : ℚ) ^ 2) * coeff n A) : PowerSeries ℚ) ↔
      A = PowerSeries.mk s := by
  sorry

/-- A394576 (indexed from `0`, so `f m = a(m+1)`): there is exactly one sequence obeying the
greedy rule of the entry. -/
theorem a394576_existsUnique :
    ∃! f : ℕ → ℕ, f 0 = 1 ∧ ∀ n,
      f n < f (n + 1) ∧
      (∀ k, 1 ≤ k → k + 1 ≤ n → f (n + 1) ≠ f (k - 1) + f k + f (k + 1)) ∧
      ∀ t, f n < t → (∀ k, 1 ≤ k → k + 1 ≤ n → t ≠ f (k - 1) + f k + f (k + 1)) →
        f (n + 1) ≤ t := by
  sorry

/-- A394576: `⌊(4n-3)/3⌋ ≤ a(n) ≤ ⌊(4n-1)/3⌋` for `n ≥ 1` (here `a(n) = f (n - 1)`), hence
`a(3k) = 4k - 1`; and the positive integers that are terms are exactly those that are not
sums of three consecutive terms. -/
theorem a394576_bounds (f : ℕ → ℕ)
    (hf : f 0 = 1 ∧ ∀ n,
      f n < f (n + 1) ∧
      (∀ k, 1 ≤ k → k + 1 ≤ n → f (n + 1) ≠ f (k - 1) + f k + f (k + 1)) ∧
      ∀ t, f n < t → (∀ k, 1 ≤ k → k + 1 ≤ n → t ≠ f (k - 1) + f k + f (k + 1)) →
        f (n + 1) ≤ t) :
    (∀ n : ℕ, 1 ≤ n → (4 * n - 3) / 3 ≤ f (n - 1) ∧ f (n - 1) ≤ (4 * n - 1) / 3) ∧
      (∀ k : ℕ, 1 ≤ k → f (3 * k - 1) = 4 * k - 1) ∧
      (∀ t : ℕ, 0 < t → ((∃ n, f n = t) ↔
        ¬∃ k, 1 ≤ k ∧ f (k - 1) + f k + f (k + 1) = t)) := by
  sorry

end OEISProofs.FurtherResults
