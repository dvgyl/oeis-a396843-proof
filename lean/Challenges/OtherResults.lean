module

public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.Data.Int.ModEq
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Further OEIS results (A396093, A392210, A396102, A380056, A397346, A394576)

`F.subst B` is Mathlib's substitution `F(B(x))` of a series `B` with zero constant term, and
the `k`-th compositional iterate of `U` is `(fun G : PowerSeries ℤ => (U.subst G : PowerSeries ℤ))^[k] X`. A series is
*normalized* if it has the form `x + a(2)x² + ⋯`.

* **A396093.** `A = B(B(B(x)))` with `B(x) = x/(1-x)²`. Conjectured: `a(2n)` is even for
  `n ≥ 1`, and `a(2n-1)` is even exactly when `n = 5k - 2`; both follow from the complete
  rule: `a(n)` is odd exactly when `n ≡ 1, 3, 7, 9 (mod 10)`.
* **A392210.** The infinitely nested square `x + sq(x/(1-x) + sq(x/(1-2x) + sq(x/(1-3x) + ⋯)))`
  with `sq(y) = y²`; the entry observes that `a(2n-1)` is even for `n > 1`. It is formalized
  through formula (1) of the entry, `F(x) = x + F(x/(1-x))²`, as the unique normalized solution
  (`x/(1-x)` is written `X * PowerSeries.mk 1`). The accompanying paper proves that the nested
  expression defines the same series; that step is not formalized.
* **A396102.** `A(A(A(x))) = (1+x)·A(A(x))`, conjectured `a(n) ≡ 1 (mod 3)`. It is the case
  `r = 3` of the family `U^{∘r} = (1+x)·U^{∘(r-1)}`, for which every coefficient is `1` modulo
  `r` and the `k`-th iterate has coefficients `≡ k^(n-1) (mod r)`.
* **A380056.** `a(n) = n!·[x^n] (e^x - 1)/cos(2x)`. Conjectured: `a(n) ≡ 1 (mod 4)` for `n ≥ 1`,
  and `5 ∣ a(4n)`. Proved: in addition `a(n) ≡ 2·2^n + 3·4^n (mod 5)`, so `5 ∣ a(n)` exactly
  when `4 ∣ n`. The series `A` is characterized by `A(x)·cos(2x) = e^x - 1` over `ℚ`.
* **A397346.** `A(x) = exp(x + ∑_{n≥2} (2n²-1)/(2n²)·a(n)·x^n)`. Conjectured: from `n = 2` on,
  `a(n) mod 8` repeats `4, 2, 0, 2`. The entry's recurrence (its formula (7)) is
  `a(0) = a(1) = 1`, `a(n+2) = 2(n+2)a(n+1) + (n+2)∑_{i<n} (2(i+2)²-1)/(i+2)·a(i+2)·a(n-i)`.
  The theorems below concern the solution of this recurrence: it consists of integers with
  `n ∣ a(n)`, `a(n)/n ≡ 6 (mod 8)` if `n ≡ 3 (mod 4)` and `≡ 2 (mod 8)` otherwise, and its
  generating function satisfies `A' = A·H'` for the series `H` inside the exponential. The
  final step, from `A' = A·H'` and `A(0) = 1` to `A = exp(H)`, is proved in the accompanying
  paper and is not formalized.
* **A394576.** `a(1) = 1`, and `a(n+1)` is the least integer greater than `a(n)` that is not a
  sum `a(k) + a(k+1) + a(k+2)` of three consecutive earlier terms. Conjectured:
  `a(n) ≤ ⌊(4n-1)/3⌋`. Proved: `⌊(4n-3)/3⌋ ≤ a(n) ≤ ⌊(4n-1)/3⌋`, so `a(3k) = 4k - 1`. In Lean
  the sequence is indexed from `0`: `f m` is `a(m+1)`, and natural-number division `/` is the
  floor.
-/

public section

namespace OEISProofs.OtherResults

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

/-- A397346: the generating function `A = ∑ s(n)x^n` of the solution satisfies `A' = A·H'`,
where `H = x + ∑_{n≥2} (2n²-1)/(2n²)·s(n)·x^n` is the series inside the exponential in the
entry's definition. -/
theorem a397346_derivative (s : ℕ → ℚ) (h0 : s 0 = 1) (h1 : s 1 = 1)
    (hs : ∀ n : ℕ,
      s (n + 2) = 2 * (n + 2 : ℚ) * s (n + 1) +
        (n + 2 : ℚ) * ∑ i : Fin n,
          (2 * (i.val + 2 : ℚ) ^ 2 - 1) / (i.val + 2 : ℚ) * s (i.val + 2) * s (n - i.val)) :
    derivative (PowerSeries.mk s) =
      PowerSeries.mk s * derivative (PowerSeries.mk fun n =>
        if n = 0 then 0 else if n = 1 then 1 else (2 * (n : ℚ) ^ 2 - 1) / (2 * (n : ℚ) ^ 2) * s n) := by
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

end OEISProofs.OtherResults
