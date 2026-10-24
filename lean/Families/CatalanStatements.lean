import Families.CatalanComposition
import Families.NestedBinomial

/-!
Explicit source and conclusion statements for A393172, A393171, and the
elementary A392210 odd-index observation. AI-generated for Dev D. Goyal.
-/

namespace Families.CatalanStatements

open PowerSeries Hanna.Series
open CatalanComposition

noncomputable section

theorem first_existence :
    ∃! F : PowerSeries ℤ,
      (coeff ℤ 0 F=0 ∧ coeff ℤ 1 F=1) ∧ compose F (X-X^2)=X+F^2 :=
  a393172_existence_uniqueness

theorem first_definition :
    coeff ℤ 0 CatalanComposition.A=0 ∧ coeff ℤ 1 CatalanComposition.A=1 ∧
      compose (CatalanComposition.A : PowerSeries ℤ) (X-X^2)=X+CatalanComposition.A^2 :=
  ⟨A_normalized.1,A_normalized.2,A_equation⟩

theorem first_residue (n : ℕ) (hn : 1<n) :
    (((coeff ℤ n CatalanComposition.A : ℤ) : ZMod 4)=2 ↔ ∃ k : ℕ, n=2^k) ∧
    (((coeff ℤ n CatalanComposition.A : ℤ) : ZMod 4)=0 ↔ ¬∃ k : ℕ, n=2^k) :=
  a393172_residue n hn

theorem first_arbitrary_source (F : PowerSeries ℤ)
    (h0 : coeff ℤ 0 F=0) (h1 : coeff ℤ 1 F=1)
    (he : compose F (X-X^2)=X+F^2) (n : ℕ) (hn : 1<n) :
    (((coeff ℤ n F : ℤ) : ZMod 4)=2 ↔ ∃ k : ℕ, n=2^k) ∧
    (((coeff ℤ n F : ℤ) : ZMod 4)=0 ↔ ¬∃ k : ℕ, n=2^k) := by
  rw [A_unique ⟨h0,h1⟩ he]
  exact first_residue n hn

theorem second_existence :
    ∃! F : PowerSeries ℤ,
      (coeff ℤ 0 F=0 ∧ coeff ℤ 1 F=1) ∧ compose F (X-X^2)=X-X^2+F^2 :=
  a393171_existence_uniqueness

theorem second_named_existence :
    ∃! F : PowerSeries ℤ,
      (coeff ℤ 0 F=0 ∧ coeff ℤ 1 F=1) ∧ F=X+(compose F catalan)^2 :=
  a393171_named_existence_uniqueness

theorem second_definition :
    coeff ℤ 0 B=0 ∧ coeff ℤ 1 B=1 ∧
      compose (B : PowerSeries ℤ) (X-X^2)=X-X^2+B^2 ∧
      (B : PowerSeries ℤ)=X+(compose B catalan)^2 :=
  ⟨B_normalized.1,B_normalized.2,B_equation,B_fixed⟩

theorem second_residue (n : ℕ) (hn : 2<n) :
    (((coeff ℤ n B : ℤ) : ZMod 8)=4 ↔ ∃ k : ℕ, 1≤k ∧ (n=2^k ∨ n=2^k+1)) ∧
    (((coeff ℤ n B : ℤ) : ZMod 8)=0 ↔ ¬∃ k : ℕ, 1≤k ∧ (n=2^k ∨ n=2^k+1)) :=
  a393171_residue n hn

theorem second_arbitrary_source (F : PowerSeries ℤ)
    (h0 : coeff ℤ 0 F=0) (h1 : coeff ℤ 1 F=1)
    (he : compose F (X-X^2)=X-X^2+F^2) (n : ℕ) (hn : 2<n) :
    (((coeff ℤ n F : ℤ) : ZMod 8)=4 ↔ ∃ k : ℕ, 1≤k ∧ (n=2^k ∨ n=2^k+1)) ∧
    (((coeff ℤ n F : ℤ) : ZMod 8)=0 ↔ ¬∃ k : ℕ, 1≤k ∧ (n=2^k ∨ n=2^k+1)) := by
  rw [B_unique ⟨h0,h1⟩ he]
  exact second_residue n hn

theorem third_existence :
    ∃! F : PowerSeries ℤ,
      (coeff ℤ 0 F=0 ∧ coeff ℤ 1 F=1) ∧
        F=X+(compose F Hanna.Related.ScaledInverse.geometric)^2 :=
  NestedBinomial.existence_uniqueness

theorem third_definition :
    coeff ℤ 0 NestedBinomial.A=0 ∧ coeff ℤ 1 NestedBinomial.A=1 ∧
      (NestedBinomial.A : PowerSeries ℤ)=
        X+(compose NestedBinomial.A Hanna.Related.ScaledInverse.geometric)^2 ∧
      (Hanna.Related.ScaledInverse.geometric : PowerSeries ℤ)*(1-X)=X :=
  ⟨NestedBinomial.A_normalized.1,NestedBinomial.A_normalized.2,
    NestedBinomial.A_equation,NestedBinomial.rational_argument⟩

theorem third_evenness (n : ℕ) (hn : 1<n) :
    Even (coeff ℤ (2*n-1) NestedBinomial.A) := NestedBinomial.a392210_odd_indices n hn

theorem third_arbitrary_source (F : PowerSeries ℤ)
    (h0 : coeff ℤ 0 F=0) (h1 : coeff ℤ 1 F=1)
    (he : F=X+(compose F Hanna.Related.ScaledInverse.geometric)^2)
    (n : ℕ) (hn : 1<n) : Even (coeff ℤ (2*n-1) F) := by
  rw [NestedBinomial.A_unique ⟨h0,h1⟩ he]
  exact third_evenness n hn

end
end Families.CatalanStatements
