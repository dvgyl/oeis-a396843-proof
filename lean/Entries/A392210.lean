import Families.CatalanStatements

/-!
# OEIS A392210

Statements of the results in the accompanying paper (listed in `CONTENTS.md` at the
repository root), proved using the shared libraries of this project.
Formalization written by ChatGPT (OpenAI) for Dev D. Goyal.
-/

namespace OEIS.A392210

open Families
open PowerSeries Hanna.Series Families.CatalanComposition

noncomputable section
attribute [local instance] Classical.propDecidable

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
end OEIS.A392210
