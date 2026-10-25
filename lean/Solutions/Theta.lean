module

public import Solutions.Common
public import Families
public import Entries.A355872

/-!
# Solution for the theta series and theta-type equations

Each statement of `Challenges.Theta` is derived from the libraries
`Families.ThetaSubstitution` (A378580, A378581), `Families.ThetaRational` (A380060,
A380680) and `Families.BilateralTheta` with the coefficientwise source equation of
`Entries.A355872`.
-/

public section

namespace OEISProofs.Theta

open PowerSeries Hanna.Series

theorem eq_theta (T : PowerSeries ℤ) (hT0 : coeff 0 T = 1)
    (hTsq : ∀ n : ℕ, 0 < n → (∃ k : ℕ, n = k ^ 2) → coeff n T = 2)
    (hTns : ∀ n : ℕ, 0 < n → (¬∃ k : ℕ, n = k ^ 2) → coeff n T = 0) :
    T = ThetaSubstitution.theta := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [hT0, coeff_zero_eq_constantCoeff_apply, ThetaSubstitution.theta_constant]
  · rw [ThetaSubstitution.theta_coefficient n hn]
    by_cases h : ∃ k : ℕ, n = k ^ 2
    · rw [hTsq n hn h, if_pos (show ThetaSubstitution.squareIndex n from h)]
    · rw [hTns n hn h, if_neg (show ¬ThetaSubstitution.squareIndex n from h)]

theorem quotient_existsUnique (T : PowerSeries ℤ) (hT0 : coeff 0 T = 1)
    (hTsq : ∀ n : ℕ, 0 < n → (∃ k : ℕ, n = k ^ 2) → coeff n T = 2)
    (hTns : ∀ n : ℕ, 0 < n → (¬∃ k : ℕ, n = k ^ 2) → coeff n T = 0) :
    ∃! A : PowerSeries ℤ, constantCoeff A = 1 ∧ A.subst (X * invOfUnit A 1) = T := by
  rw [eq_theta T hT0 hTsq hTns]
  exact ThetaSubstitution.a378580_source_existence_uniqueness

theorem quotient_coeff (T : PowerSeries ℤ) (hT0 : coeff 0 T = 1)
    (hTsq : ∀ n : ℕ, 0 < n → (∃ k : ℕ, n = k ^ 2) → coeff n T = 2)
    (hTns : ∀ n : ℕ, 0 < n → (¬∃ k : ℕ, n = k ^ 2) → coeff n T = 0)
    (A : PowerSeries ℤ) (hA0 : constantCoeff A = 1) (hA : A.subst (X * invOfUnit A 1) = T) :
    (∀ n : ℕ, 0 < n → (∃ k : ℕ, n = k ^ 2) → coeff n A ≡ 2 [ZMOD 4]) ∧
      (∀ n : ℕ, 0 < n → (¬∃ k : ℕ, n = k ^ 2) → (4 : ℤ) ∣ coeff n A) := by
  rw [eq_theta T hT0 hTsq hTns] at hA
  rw [ThetaSubstitution.a378580_source_uniqueness hA0 hA]
  refine ⟨fun n hn h => ?_, fun n hn h => (ThetaSubstitution.a378580_four_dvd_iff n hn).2 h⟩
  exact (modEq_four _ _).2 (by
    rw [(ThetaSubstitution.a378580_square_iff n hn).2 h]; rfl)

theorem product_existsUnique (T : PowerSeries ℤ) (hT0 : coeff 0 T = 1)
    (hTsq : ∀ n : ℕ, 0 < n → (∃ k : ℕ, n = k ^ 2) → coeff n T = 2)
    (hTns : ∀ n : ℕ, 0 < n → (¬∃ k : ℕ, n = k ^ 2) → coeff n T = 0) :
    ∃! A : PowerSeries ℤ, constantCoeff A = 1 ∧ A.subst (X * A) = T := by
  rw [eq_theta T hT0 hTsq hTns]
  exact ThetaSubstitution.a378581_source_existence_uniqueness

theorem product_coeff (T : PowerSeries ℤ) (hT0 : coeff 0 T = 1)
    (hTsq : ∀ n : ℕ, 0 < n → (∃ k : ℕ, n = k ^ 2) → coeff n T = 2)
    (hTns : ∀ n : ℕ, 0 < n → (¬∃ k : ℕ, n = k ^ 2) → coeff n T = 0)
    (A : PowerSeries ℤ) (hA0 : constantCoeff A = 1) (hA : A.subst (X * A) = T) :
    (∀ n : ℕ, 0 < n → (∃ k : ℕ, n = k ^ 2) → coeff n A ≡ 2 [ZMOD 4]) ∧
      (∀ n : ℕ, 0 < n → (¬∃ k : ℕ, n = k ^ 2) → (4 : ℤ) ∣ coeff n A) := by
  rw [eq_theta T hT0 hTsq hTns] at hA
  rw [ThetaSubstitution.a378581_source_uniqueness hA0 hA]
  refine ⟨fun n hn h => ?_, fun n hn h => (ThetaSubstitution.a378581_four_dvd_iff n hn).2 h⟩
  exact (modEq_four _ _).2 (by
    rw [(ThetaSubstitution.a378581_square_iff n hn).2 h]; rfl)

theorem implicit_existsUnique :
    ∃! A : PowerSeries ℤ, A = 1 + 2 * PowerSeries.mk (fun n =>
      ∑ k ∈ Finset.range (n + 1), coeff n
        (X ^ ((k + 1) ^ 2) * ((A - X ^ (k + 1)) * invOfUnit (1 - X ^ (k + 1) * A) 1) ^ (k + 1))) :=
  Families.ThetaRational.a380060_existence_uniqueness

theorem implicit_coeff (A : PowerSeries ℤ)
    (hA : A = 1 + 2 * PowerSeries.mk (fun n =>
      ∑ k ∈ Finset.range (n + 1), coeff n
        (X ^ ((k + 1) ^ 2) * ((A - X ^ (k + 1)) * invOfUnit (1 - X ^ (k + 1) * A) 1) ^ (k + 1))))
    (n : ℕ) (hn : 0 < n) :
    (coeff n A ≡ 2 [ZMOD 4] ↔ ∃ j : ℕ, n = j ^ 2) ∧
      ((4 : ℤ) ∣ coeff n A ↔ ¬∃ j : ℕ, n = j ^ 2) := by
  rw [Families.ThetaRational.a380060_source_uniqueness hA, modEq_four]
  push_cast
  exact ⟨Families.ThetaRational.a380060_square_iff n hn,
    Families.ThetaRational.a380060_four_dvd_iff n hn⟩

theorem explicit_coeff (A : PowerSeries ℤ)
    (hA : A = 1 + 2 * PowerSeries.mk (fun n =>
      ∑ k ∈ Finset.range (n + 1), coeff n
        (X ^ ((k + 1) ^ 2) * ((2 - X ^ (k + 1)) * invOfUnit (1 - X ^ (k + 1) * 2) 1) ^ (k + 1)))) :
    (∀ n : ℕ, 0 < n →
      ((coeff n A ≡ 2 [ZMOD 4] ↔ ∃ j : ℕ, n = 2 * j ^ 2) ∧
        ((4 : ℤ) ∣ coeff n A ↔ ¬∃ j : ℕ, n = 2 * j ^ 2))) ∧
      coeff 1 A = 4 ∧ coeff 2 A = 6 := by
  have hA' : A = Families.ThetaRational.A380680 := hA
  rw [hA']
  refine ⟨fun n hn => ?_, Families.ThetaRational.a380680_coeff_one,
    Families.ThetaRational.a380680_coeff_two⟩
  rw [modEq_four]
  push_cast
  exact ⟨Families.ThetaRational.a380680_twice_square_iff n hn,
    Families.ThetaRational.a380680_four_dvd_iff n hn⟩

theorem bilateral_existsUnique :
    ∃! A : PowerSeries ℤ, ∀ n : ℕ,
      (∑ᶠ m : ℤ, coeff n ((-X) ^ (m.natAbs ^ 2) * A ^ ((m - 1).natAbs ^ 2))) = coeff n X :=
  OEIS.A355872.source_existence_uniqueness

theorem bilateral_coeff (A : PowerSeries ℤ)
    (hA : ∀ n : ℕ,
      (∑ᶠ m : ℤ, coeff n ((-X) ^ (m.natAbs ^ 2) * A ^ ((m - 1).natAbs ^ 2))) = coeff n X) :
    (∀ n : ℕ, n % 4 ≠ 1 → coeff n A = 0) ∧
      (∀ n : ℕ, 1 ≤ n → coeff (4 * n - 3) A ≡ 2 * (-1) ^ (n - 1) [ZMOD 16]) := by
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · rw [OEIS.A355872.source_existence_uniqueness.unique hA
      OEIS.A355872.canonical_literal_source]
    exact OEIS.A355872.canonical_sparse_support n hn
  · rw [modEq_sixteen, OEIS.A355872.source_mod_sixteen A hA n hn]
    push_cast
    rfl

end OEISProofs.Theta
