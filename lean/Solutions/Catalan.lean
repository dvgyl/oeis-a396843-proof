module

public import Solutions.Common
public import Families

/-!
# Solution for the Catalan-type equations

Each statement of `Challenges.Catalan` is derived from the libraries
`Families.CatalanComposition` (A393172, A393171), `Families.MahlerParity` (A389536),
`Families.DifferentialParity` (A397588) and `Families.NestedReversion` (A195194).
-/

public section

namespace OEISProofs.Catalan

open PowerSeries Hanna.Series Families

/-- A series `C` with `C(0) = 0` and `C = x + C²` is the Catalan series of the library. -/
theorem eq_catalan (C : PowerSeries ℤ) (hC0 : coeff 0 C = 0) (hC : C = X + C ^ 2) :
    C = CatalanComposition.catalan := by
  have hsq : coeff 1 (C ^ 2) = 0 := by
    rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_succ]
    simp [hC0]
  have hC1 : coeff 1 C = 1 := by
    rw [hC, map_add, hsq, coeff_one_X, add_zero]
  have hCn : Normalized C := ⟨hC0, hC1⟩
  have hNC : compose (CatalanComposition.N : PowerSeries ℤ) C = X := by
    rw [CatalanComposition.N, compose_sub _ _ _ hCn.constantCoeff,
      compose_pow _ _ _ hCn.constantCoeff, compose_X_left _ hCn.constantCoeff]
    calc C - C ^ 2 = X + C ^ 2 - C ^ 2 := by rw [← hC]
      _ = X := by ring
  exact (inverse_unique CatalanComposition.N_normalized hCn CatalanComposition.catalan_N
    hNC).symm

theorem a393172_existsUnique :
    ∃! F : PowerSeries ℤ, coeff 0 F = 0 ∧ coeff 1 F = 1 ∧ F.subst (X - X ^ 2) = X + F ^ 2 := by
  obtain ⟨F, ⟨⟨h0, h1⟩, hF⟩, huniq⟩ := CatalanComposition.a393172_existence_uniqueness (R := ℤ)
  exact ⟨F, ⟨h0, h1, hF⟩, fun G ⟨g0, g1, gG⟩ => huniq G ⟨⟨g0, g1⟩, gG⟩⟩

theorem a393172_coeff (F : PowerSeries ℤ) (h0 : coeff 0 F = 0) (h1 : coeff 1 F = 1)
    (hF : F.subst (X - X ^ 2) = X + F ^ 2) (n : ℕ) (hn : 1 < n) :
    (coeff n F ≡ 2 [ZMOD 4] ↔ ∃ k : ℕ, n = 2 ^ k) ∧
      ((4 : ℤ) ∣ coeff n F ↔ ¬∃ k : ℕ, n = 2 ^ k) := by
  obtain ⟨h2, h4⟩ := CatalanStatements.first_arbitrary_source F h0 h1 hF n hn
  rw [modEq_four, dvd_four]
  exact ⟨by simpa using h2, h4⟩

theorem a393171_existsUnique (C : PowerSeries ℤ) (hC0 : coeff 0 C = 0) (hC : C = X + C ^ 2) :
    ∃! B : PowerSeries ℤ, coeff 0 B = 0 ∧ coeff 1 B = 1 ∧ B = X + (B.subst C) ^ 2 := by
  rw [eq_catalan C hC0 hC]
  obtain ⟨B, ⟨⟨h0, h1⟩, hB⟩, huniq⟩ :=
    CatalanComposition.a393171_named_existence_uniqueness (R := ℤ)
  exact ⟨B, ⟨h0, h1, hB⟩, fun G ⟨g0, g1, gG⟩ => huniq G ⟨⟨g0, g1⟩, gG⟩⟩

theorem a393171_coeff (C : PowerSeries ℤ) (hC0 : coeff 0 C = 0) (hC : C = X + C ^ 2)
    (B : PowerSeries ℤ) (h0 : coeff 0 B = 0) (h1 : coeff 1 B = 1)
    (hB : B = X + (B.subst C) ^ 2) (n : ℕ) (hn : 2 < n) :
    (coeff n B ≡ 4 [ZMOD 8] ↔ ∃ k : ℕ, 1 ≤ k ∧ (n = 2 ^ k ∨ n = 2 ^ k + 1)) ∧
      ((8 : ℤ) ∣ coeff n B ↔ ¬∃ k : ℕ, 1 ≤ k ∧ (n = 2 ^ k ∨ n = 2 ^ k + 1)) := by
  rw [eq_catalan C hC0 hC] at hB
  have hBeq : B = CatalanComposition.B :=
    (CatalanComposition.a393171_named_existence_uniqueness (R := ℤ)).unique ⟨⟨h0, h1⟩, hB⟩
      ⟨CatalanComposition.B_normalized, CatalanComposition.B_fixed⟩
  rw [hBeq]
  obtain ⟨h4, h8⟩ := CatalanStatements.second_residue n hn
  rw [modEq_eight, dvd_eight]
  exact ⟨by simpa using h4, h8⟩

theorem a389536_existsUnique :
    ∃! F : PowerSeries ℤ, coeff 0 F = 0 ∧ coeff 1 F = 1 ∧
      F.subst (X ^ 2 + 2 * X ^ 3) = X * F := by
  obtain ⟨F, ⟨⟨h0, h1⟩, hF⟩, huniq⟩ := MahlerParity.existence_uniqueness (R := ℤ)
  exact ⟨F, ⟨h0, h1, hF⟩, fun G ⟨g0, g1, gG⟩ => huniq G ⟨⟨g0, g1⟩, gG⟩⟩

theorem a389536_coeff (F : PowerSeries ℤ) (h0 : coeff 0 F = 0) (h1 : coeff 1 F = 1)
    (hF : F.subst (X ^ 2 + 2 * X ^ 3) = X * F) (n : ℕ) (hn : 1 < n) :
    (coeff n F ≡ 2 [ZMOD 4] ↔ ∃ k : ℕ, n = 2 ^ k + 1) ∧
      ((4 : ℤ) ∣ coeff n F ↔ ¬∃ k : ℕ, n = 2 ^ k + 1) := by
  have hFeq : F = MahlerParity.A :=
    MahlerParity.solution_unique ⟨h0, h1⟩ MahlerParity.A_normalized hF MahlerParity.A_equation
  rw [hFeq]
  obtain ⟨h2, _⟩ := MahlerParity.a389536_residue n hn
  rw [modEq_four]
  exact ⟨by simpa [MahlerParity.a] using h2, MahlerParity.a389536_four_dvd_iff n hn⟩

theorem a397588_existsUnique :
    ∃! F : PowerSeries ℤ, coeff 0 F = 0 ∧ coeff 1 F = 1 ∧ F = X + derivative (X * F ^ 2) := by
  obtain ⟨F, ⟨⟨h0, h1⟩, hF⟩, huniq⟩ := DifferentialParity.existence_uniqueness (R := ℤ)
  exact ⟨F, ⟨h0, h1, hF⟩, fun G ⟨g0, g1, gG⟩ => huniq G ⟨⟨g0, g1⟩, gG⟩⟩

theorem a397588_coeff (F : PowerSeries ℤ) (h0 : coeff 0 F = 0) (h1 : coeff 1 F = 1)
    (hF : F = X + derivative (X * F ^ 2)) :
    (∀ n : ℕ, Odd (coeff n F) ↔ ∃ k : ℕ, n = 2 ^ k) ∧
      (∀ n : ℕ, 1 < n → (3 : ℤ) ∣ coeff n F) := by
  have hFeq : F = DifferentialParity.A :=
    DifferentialParity.solution_unique ⟨h0, h1⟩ DifferentialParity.A_normalized hF
      DifferentialParity.A_equation
  rw [hFeq]
  exact ⟨DifferentialParity.a397588_parity, DifferentialParity.a397588_divisible_by_three⟩

theorem a195194_existsUnique :
    ∃! F : ℕ → PowerSeries ℤ, (∀ j, coeff 0 (F j) = 0 ∧ coeff 1 (F j) = 1) ∧
      ∀ j, (X - C ((j + 1 : ℕ) : ℤ) * X * F (j + 1)).subst (F j) = X ∧
        (F j).subst (X - C ((j + 1 : ℕ) : ℤ) * X * F (j + 1)) = X :=
  NestedReversion.source_existence_uniqueness (NestedReversion.weights ℤ)

theorem a195194_coeff (F : ℕ → PowerSeries ℤ) (hF0 : ∀ j, coeff 0 (F j) = 0 ∧ coeff 1 (F j) = 1)
    (hF : ∀ j, (X - C ((j + 1 : ℕ) : ℤ) * X * F (j + 1)).subst (F j) = X ∧
      (F j).subst (X - C ((j + 1 : ℕ) : ℤ) * X * F (j + 1)) = X)
    (n : ℕ) :
    Odd (coeff n (F 0)) ↔ ∃ k : ℕ, n = 2 ^ k := by
  have hFeq : F = NestedReversion.tail (NestedReversion.weights ℤ) :=
    (NestedReversion.source_existence_uniqueness (NestedReversion.weights ℤ)).unique
      ⟨hF0, hF⟩ ⟨NestedReversion.tail_normalized _, fun j =>
        ⟨NestedReversion.tail_right_inverse _ j, NestedReversion.tail_left_inverse _ j⟩⟩
  rw [hFeq]
  exact NestedReversion.a195194_parity n

end OEISProofs.Catalan
