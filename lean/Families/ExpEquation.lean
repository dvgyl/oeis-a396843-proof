module

public import Families.ExpRecurrence
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# A397346: the exponential equation

The entry defines its sequence by `A(x) = exp(H_A(x))`, where
`H_A = x + ∑_{n≥2} (2n²-1)/(2n²)·a(n)·x^n` is built from the coefficients `a(n)` of `A`
itself. This module shows that this equation has exactly one solution over `ℚ`, namely the
generating function of the recurrence solved in `Families.ExpRecurrence`. The exponential is
Mathlib's `PowerSeries.exp`, and `exp(H)` is the substitution `(exp ℚ).subst H`.

Written by Claude Opus 5.5 for Dev D. Goyal.
-/

@[expose] public section

namespace Families.ExpEquation

open PowerSeries

noncomputable section

/-- The series `H_A = x + ∑_{n≥2} (2n²-1)/(2n²)·a(n)·x^n` inside the exponential. -/
def exponent (A : PowerSeries ℚ) : PowerSeries ℚ := PowerSeries.mk fun n =>
  if n = 0 then 0 else if n = 1 then 1 else
    (2 * (n : ℚ) ^ 2 - 1) / (2 * (n : ℚ) ^ 2) * coeff n A

/-- The equation `A = exp(H_A)` of the entry. -/
def Equation (A : PowerSeries ℚ) : Prop :=
  A = ((exp ℚ).subst (exponent A) : PowerSeries ℚ)

theorem coeff_exponent (A : PowerSeries ℚ) (n : ℕ) :
    coeff n (exponent A) = if n = 0 then 0 else if n = 1 then 1 else
      (2 * (n : ℚ) ^ 2 - 1) / (2 * (n : ℚ) ^ 2) * coeff n A :=
  coeff_mk _ _

theorem constantCoeff_exponent (A : PowerSeries ℚ) : constantCoeff (exponent A) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_exponent]
  simp

theorem coeff_zero_exp_subst {G : PowerSeries ℚ} (hG : constantCoeff G = 0) :
    coeff 0 ((exp ℚ).subst G : PowerSeries ℚ) = 1 := by
  rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_eq,
    constantCoeff_subst_of_constantCoeff_zero (S := ℚ) hG (exp ℚ), constantCoeff_exp, map_one]

/-- The chain rule for `exp(G)`: `(exp G)' = exp(G)·G'`. -/
theorem derivative_exp_subst {G : PowerSeries ℚ} (hG : constantCoeff G = 0) :
    derivative ((exp ℚ).subst G : PowerSeries ℚ) =
      ((exp ℚ).subst G : PowerSeries ℚ) * derivative G := by
  rw [derivative_subst (HasSubst.of_constantCoeff_zero' hG), derivative_exp]

/-- Two series with the same constant term that satisfy `F' = F·G'` for the same `G` are
equal. -/
theorem linear_unique {F K G : PowerSeries ℚ} (h0 : coeff 0 F = coeff 0 K)
    (hF : derivative F = F * derivative G) (hK : derivative K = K * derivative G) :
    F = K := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · exact h0
    · have eF := congrArg (coeff n) hF
      have eK := congrArg (coeff n) hK
      rw [coeff_derivative, coeff_mul] at eF eK
      have hsum : ∑ p ∈ Finset.antidiagonal n, coeff p.1 F * coeff p.2 (derivative G) =
          ∑ p ∈ Finset.antidiagonal n, coeff p.1 K * coeff p.2 (derivative G) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [ih p.1 (by have := Finset.mem_antidiagonal.mp hp; omega)]
      have hn : (n : ℚ) + 1 ≠ 0 := by positivity
      exact mul_right_cancel₀ hn (by rw [eF, eK, hsum])

/-- The coefficient of `x^n` in `A' = A·H_A'`, with the term `a(0)·H_A'` split off. -/
theorem coeff_differential {A : PowerSeries ℚ} (hA0 : coeff 0 A = 1)
    (hA : derivative A = A * derivative (exponent A)) (n : ℕ) :
    coeff (n + 1) A * ((n : ℚ) + 1) =
      (∑ k ∈ Finset.range n,
        coeff (k + 1) A * (coeff (n - (k + 1) + 1) (exponent A) * ((n - (k + 1) : ℕ) + 1))) +
      coeff (n + 1) (exponent A) * ((n : ℚ) + 1) := by
  have e := congrArg (coeff n) hA
  rw [coeff_derivative, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ'] at e
  simpa only [Nat.sub_zero, hA0, one_mul, coeff_derivative] using e

/-- The equation `A' = A·H_A'` with `A(0) = 1` has at most one solution: comparing the
coefficients of `x^n` determines `a(n+1)` from `a(0), …, a(n)`, because the coefficient of
`a(n+1)` is `(n+1)/(2(n+1)²) ≠ 0`. -/
theorem differential_unique {A B : PowerSeries ℚ} (hA0 : coeff 0 A = 1) (hB0 : coeff 0 B = 1)
    (hA : derivative A = A * derivative (exponent A))
    (hB : derivative B = B * derivative (exponent B)) : A = B := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · rw [hA0, hB0]
    · have eA := coeff_differential hA0 hA n
      have eB := coeff_differential hB0 hB n
      have hrest : ∑ k ∈ Finset.range n,
            coeff (k + 1) A * (coeff (n - (k + 1) + 1) (exponent A) * ((n - (k + 1) : ℕ) + 1)) =
          ∑ k ∈ Finset.range n,
            coeff (k + 1) B * (coeff (n - (k + 1) + 1) (exponent B) * ((n - (k + 1) : ℕ) + 1)) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' := Finset.mem_range.mp hk
        rw [ih (k + 1) (by omega), coeff_exponent, coeff_exponent, ih (n - (k + 1) + 1) (by omega)]
      rw [hrest] at eA
      rw [coeff_exponent] at eA eB
      rcases n with _ | m
      · simp only [Finset.range_zero, Finset.sum_empty, zero_add] at eA eB
        simp at eA eB
        rw [eA, eB]
      · simp only [show m + 1 + 1 ≠ 0 by omega, show m + 1 + 1 ≠ 1 by omega, ite_false]
          at eA eB
        set c : ℚ := (2 * ((m + 1 + 1 : ℕ) : ℚ) ^ 2 - 1) / (2 * ((m + 1 + 1 : ℕ) : ℚ) ^ 2)
        have hc : (1 - c) * (2 * ((m + 1 + 1 : ℕ) : ℚ) ^ 2) = 1 := by
          have h2 : (2 * ((m + 1 + 1 : ℕ) : ℚ) ^ 2) ≠ 0 := by positivity
          simp only [c]
          field_simp
          ring
        have hc0 : 1 - c ≠ 0 := left_ne_zero_of_mul_eq_one hc
        have hn : ((m + 1 : ℕ) : ℚ) + 1 ≠ 0 := by positivity
        have key : (coeff (m + 1 + 1) A - coeff (m + 1 + 1) B) *
            ((((m + 1 : ℕ) : ℚ) + 1) * (1 - c)) = 0 := by
          linear_combination eA - eB
        rcases mul_eq_zero.mp key with h | h
        · exact sub_eq_zero.mp h
        · exact absurd h (mul_ne_zero hn hc0)

theorem exponent_generatingFunction :
    exponent ExpRecurrence.generatingFunction = ExpRecurrence.exponentSeries := by
  ext n
  rw [coeff_exponent, ExpRecurrence.exponentSeries, ExpRecurrence.generatingFunction,
    coeff_mk, coeff_mk]

theorem coeff_zero_generatingFunction : coeff 0 ExpRecurrence.generatingFunction = 1 := by
  simp [ExpRecurrence.generatingFunction, ExpRecurrence.a]

theorem generatingFunction_differential :
    derivative ExpRecurrence.generatingFunction =
      ExpRecurrence.generatingFunction * derivative (exponent ExpRecurrence.generatingFunction) := by
  rw [exponent_generatingFunction]
  exact ExpRecurrence.a_differential_equation

/-- Every solution of `A = exp(H_A)` satisfies `A(0) = 1` and `A' = A·H_A'`. -/
theorem differential_of_equation {A : PowerSeries ℚ} (hA : Equation A) :
    coeff 0 A = 1 ∧ derivative A = A * derivative (exponent A) := by
  constructor
  · rw [hA]
    exact coeff_zero_exp_subst (constantCoeff_exponent A)
  · conv_lhs => rw [hA]
    rw [derivative_exp_subst (constantCoeff_exponent A), ← hA]

/-- The generating function of the recurrence solves `A = exp(H_A)`. -/
theorem generatingFunction_equation : Equation ExpRecurrence.generatingFunction := by
  apply linear_unique (G := exponent ExpRecurrence.generatingFunction)
  · rw [coeff_zero_generatingFunction, coeff_zero_exp_subst (constantCoeff_exponent _)]
  · exact generatingFunction_differential
  · exact derivative_exp_subst (constantCoeff_exponent _)

/-- Every solution of `A = exp(H_A)` is the generating function of the recurrence. -/
theorem equation_unique {A : PowerSeries ℚ} (hA : Equation A) :
    A = ExpRecurrence.generatingFunction := by
  obtain ⟨h0, hD⟩ := differential_of_equation hA
  exact differential_unique h0 coeff_zero_generatingFunction hD generatingFunction_differential

theorem equation_iff (A : PowerSeries ℚ) :
    Equation A ↔ A = ExpRecurrence.generatingFunction :=
  ⟨equation_unique, fun h => h ▸ generatingFunction_equation⟩

theorem existence_uniqueness : ∃! A : PowerSeries ℚ, Equation A :=
  ⟨_, generatingFunction_equation, fun _ h => equation_unique h⟩

end

end Families.ExpEquation
