module

public import Solutions.Common
public import Families

/-!
# Solution for the results with short proofs

Each statement of `Challenges.ShortResults` is derived from the libraries
`Families.RationalParity` (A396093), `Families.NestedBinomial` (A392210) and
`Families.ExpCosine` (A380056).
-/

public section

namespace OEISProofs.ShortResults

open PowerSeries Hanna.Series Families

theorem a396093_coeff (B : PowerSeries ℤ) (hB : B * (1 - X) ^ 2 = X) :
    (∀ n : ℕ, Even (coeff n (B.subst (B.subst B))) ↔
        ¬(n % 10 = 1 ∨ n % 10 = 3 ∨ n % 10 = 7 ∨ n % 10 = 9)) ∧
      (∀ n : ℕ, Even (coeff (2 * n) (B.subst (B.subst B)))) ∧
      (∀ n : ℕ, 1 ≤ n → (Even (coeff (2 * n - 1) (B.subst (B.subst B))) ↔
        ∃ k : ℕ, 1 ≤ k ∧ n = 5 * k - 2)) := by
  have hne : ((1 : PowerSeries ℤ) - X) ^ 2 ≠ 0 := by
    apply pow_ne_zero
    intro h
    have := congrArg (coeff 0) h
    simp at this
  have hBeq : B = RationalParity.B :=
    mul_right_cancel₀ hne (hB.trans RationalParity.B_denominator.symm)
  have hA : B.subst (B.subst B) = RationalParity.A := by
    rw [hBeq, RationalParity.A_definition]; rfl
  rw [hA]
  exact ⟨RationalParity.a396093_even_iff, RationalParity.a396093_even_indices,
    RationalParity.a396093_odd_indices_original⟩

theorem a392210_existsUnique :
    ∃! F : PowerSeries ℤ, coeff 0 F = 0 ∧ coeff 1 F = 1 ∧
      F = X + (F.subst (X * PowerSeries.mk (1 : ℕ → ℤ))) ^ 2 := by
  obtain ⟨F, ⟨⟨h0, h1⟩, hF⟩, huniq⟩ := NestedBinomial.existence_uniqueness (R := ℤ)
  exact ⟨F, ⟨h0, h1, hF⟩, fun G ⟨g0, g1, gG⟩ => huniq G ⟨⟨g0, g1⟩, gG⟩⟩

theorem a392210_coeff (F : PowerSeries ℤ) (h0 : coeff 0 F = 0) (h1 : coeff 1 F = 1)
    (hF : F = X + (F.subst (X * PowerSeries.mk (1 : ℕ → ℤ))) ^ 2) (n : ℕ) (hn : 1 < n) :
    Even (coeff (2 * n - 1) F) := by
  rw [NestedBinomial.A_unique (R := ℤ) ⟨h0, h1⟩ hF]
  exact NestedBinomial.a392210_odd_indices n hn

theorem a380056_existsUnique :
    ∃! A : PowerSeries ℚ, A * rescale (2 : ℚ) (cos ℚ) = exp ℚ - 1 :=
  ExpCosine.a380056_source_existence_uniqueness

theorem a380056_eq (A : PowerSeries ℚ) (hA : A * rescale (2 : ℚ) (cos ℚ) = exp ℚ - 1) :
    A = ExpCosine.A :=
  ExpCosine.a380056_source_existence_uniqueness.unique hA ExpCosine.a380056_source_equation

theorem a380056_integral (A : PowerSeries ℚ) (hA : A * rescale (2 : ℚ) (cos ℚ) = exp ℚ - 1)
    (n : ℕ) :
    ∃ z : ℤ, (z : ℚ) = (n.factorial : ℚ) * coeff n A :=
  ⟨ExpCosine.a n, by rw [a380056_eq A hA, ExpCosine.A_integral_coefficients]⟩

theorem a380056_coeff (A : PowerSeries ℚ) (hA : A * rescale (2 : ℚ) (cos ℚ) = exp ℚ - 1)
    (a : ℕ → ℤ) (ha : ∀ n, (a n : ℚ) = (n.factorial : ℚ) * coeff n A) :
    (∀ n : ℕ, 1 ≤ n → a n ≡ 1 [ZMOD 4]) ∧
      (∀ n : ℕ, a n ≡ 2 * 2 ^ n + 3 * 4 ^ n [ZMOD 5]) ∧
      (∀ n : ℕ, (5 : ℤ) ∣ a n ↔ 4 ∣ n) := by
  have hEq : a = ExpCosine.a := by
    funext n
    have h := ha n
    rw [a380056_eq A hA, ExpCosine.A_integral_coefficients] at h
    exact_mod_cast h
  subst hEq
  refine ⟨fun n hn => ?_, fun n => ?_, ExpCosine.a380056_five_dvd_iff⟩
  · rw [modEq_four]
    simpa using ExpCosine.a380056_mod_four n hn
  · rw [modEq_five]
    simpa using ExpCosine.a380056_mod_five_formula n

end OEISProofs.ShortResults
