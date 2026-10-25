module

public import Solutions.Common
public import Families

/-!
# Solution for the equations with an exact halving step

Each statement of `Challenges.Halving` is derived from the libraries
`Families.LacunaryInverse` (A389537), `Families.SquareReversion` (A389542),
`Families.CubicReversion` (the family `R(3x²) = 2x² + R² + 2s·R³`) and
`Families.CubicConsequences` (A389474, A389475).
-/

public section

namespace OEISProofs.Halving

open PowerSeries Hanna.Series Families

theorem a389537_existsUnique :
    ∃! A : PowerSeries ℤ, coeff 0 A = 0 ∧ coeff 1 A = 1 ∧ A.subst (A - X) = A ^ 2 := by
  obtain ⟨A, ⟨⟨h0, h1⟩, hA⟩, huniq⟩ := LacunaryInverse.source_existence_uniqueness (S := ℤ)
  exact ⟨A, ⟨h0, h1, hA⟩, fun G ⟨g0, g1, gG⟩ => huniq G ⟨⟨g0, g1⟩, gG⟩⟩

theorem a389537_coeff (A : PowerSeries ℤ) (h0 : coeff 0 A = 0) (h1 : coeff 1 A = 1)
    (hA : A.subst (A - X) = A ^ 2) (n : ℕ) (hn : 2 < n) :
    (coeff n A ≡ 2 [ZMOD 4] ↔ ∃ k : ℕ, n = 3 * 2 ^ k) ∧
      ((4 : ℤ) ∣ coeff n A ↔ ¬∃ k : ℕ, n = 3 * 2 ^ k) := by
  rw [LacunaryInverse.A_unique A ⟨h0, h1⟩ hA]
  exact two_or_zero _ (LacunaryInverse.a389537_residue n hn)

theorem a389542_existsUnique :
    ∃! A : PowerSeries ℤ, coeff 0 A = 0 ∧ coeff 1 A = 1 ∧
      A.subst (A ^ 2 - X ^ 2) = 4 * A ^ 3 := by
  obtain ⟨A, ⟨⟨h0, h1⟩, hA⟩, huniq⟩ := SquareReversion.a389542_existence_uniqueness
  exact ⟨A, ⟨h0, h1, hA⟩, fun G ⟨g0, g1, gG⟩ => huniq G ⟨⟨g0, g1⟩, gG⟩⟩

theorem a389542_coeff (A : PowerSeries ℤ) (h0 : coeff 0 A = 0) (h1 : coeff 1 A = 1)
    (hA : A.subst (A ^ 2 - X ^ 2) = 4 * A ^ 3) (n : ℕ) (hn : 1 < n) :
    (coeff n A ≡ 2 [ZMOD 4] ↔ ∃ k : ℕ, n = 2 ^ k + 1) ∧
      ((4 : ℤ) ∣ coeff n A ↔ ¬∃ k : ℕ, n = 2 ^ k + 1) := by
  rw [SquareReversion.a389542_unique A ⟨h0, h1⟩ hA]
  rw [modEq_four]
  push_cast
  exact ⟨SquareReversion.a389542_two_mod_four_iff n hn,
    SquareReversion.a389542_four_dvd_iff n hn⟩

theorem cubic_family_existsUnique (s : ℤ) :
    ∃! R : PowerSeries ℤ, coeff 0 R = 0 ∧ coeff 1 R = 1 ∧
      R.subst (3 * X ^ 2 : PowerSeries ℤ) = 2 * X ^ 2 + R ^ 2 + 2 * C s * R ^ 3 := by
  obtain ⟨R, ⟨⟨h0, h1⟩, hR⟩, huniq⟩ := CubicReversion.existence_uniqueness s
  exact ⟨R, ⟨h0, h1, hR⟩, fun G ⟨g0, g1, gG⟩ => huniq G ⟨⟨g0, g1⟩, gG⟩⟩

theorem a389474_existsUnique :
    ∃! A : PowerSeries ℤ, coeff 0 A = 0 ∧ coeff 1 A = 1 ∧
      A.subst (X ^ 2 + 2 * X ^ 3 + 2 * A ^ 2) = 3 * A ^ 2 := by
  obtain ⟨A, ⟨⟨h0, h1⟩, hA⟩, huniq⟩ := CubicReversion.a389474_existence_uniqueness
  exact ⟨A, ⟨h0, h1, hA⟩, fun G ⟨g0, g1, gG⟩ => huniq G ⟨⟨g0, g1⟩, gG⟩⟩

theorem a389474_coeff (A : PowerSeries ℤ) (h0 : coeff 0 A = 0) (h1 : coeff 1 A = 1)
    (hA : A.subst (X ^ 2 + 2 * X ^ 3 + 2 * A ^ 2) = 3 * A ^ 2) :
    (∀ n : ℕ, coeff n (A ^ 2) ≡ coeff n (X ^ 2 + 2 * X ^ 3 : PowerSeries ℤ) [ZMOD 9]) ∧
      (∀ n k : ℕ, (3 : ℤ) ∣ coeff n (A ^ (3 * k) - (A.subst (X ^ 3 : PowerSeries ℤ)) ^ k)) := by
  rw [CubicReversion.a389474_unique A ⟨h0, h1⟩ hA]
  refine ⟨fun n => ?_, fun n k => ?_⟩
  · have hmap : PowerSeries.map (Int.castRingHom (ZMod 9)) (CubicReversion.a389474 ^ 2) =
        PowerSeries.map (Int.castRingHom (ZMod 9)) (X ^ 2 + 2 * X ^ 3) := by
      rw [CubicReversion.a389474_square_mod_nine]
      simp [map_ofNat]
    have h := congrArg (coeff n) hmap
    rw [coeff_map, coeff_map] at h
    exact (modEq_nine _ _).2 h
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 (CubicReversion.a389474_conjecture_4 n k)

theorem a389475_existsUnique :
    ∃! A : PowerSeries ℤ, coeff 0 A = 0 ∧ coeff 1 A = 1 ∧
      A.subst (3 * X ^ 2 : PowerSeries ℤ) = 2 * X ^ 2 + A ^ 2 - 2 * A ^ 3 := by
  obtain ⟨A, ⟨⟨h0, h1⟩, hA⟩, huniq⟩ := CubicReversion.a389475_existence_uniqueness
  exact ⟨A, ⟨h0, h1, hA⟩, fun G ⟨g0, g1, gG⟩ => huniq G ⟨⟨g0, g1⟩, gG⟩⟩

theorem a389475_coeff (A : PowerSeries ℤ) (h0 : coeff 0 A = 0) (h1 : coeff 1 A = 1)
    (hA : A.subst (3 * X ^ 2 : PowerSeries ℤ) = 2 * X ^ 2 + A ^ 2 - 2 * A ^ 3) :
    (∀ n : ℕ, (3 : ℤ) ∣ coeff n (A ^ 3 - A.subst (X ^ 3 : PowerSeries ℤ))) ∧
      (∀ n : ℕ, (3 : ℤ) ∣ coeff n (A ^ 2 - X ^ 2 - 2 * A.subst (X ^ 3 : PowerSeries ℤ))) := by
  rw [CubicReversion.a389475_unique A ⟨h0, h1⟩ hA]
  exact ⟨fun n => (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 (CubicReversion.a389475_conjecture_4a n),
    fun n => (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 (CubicReversion.a389475_conjecture_4b n)⟩

end OEISProofs.Halving
