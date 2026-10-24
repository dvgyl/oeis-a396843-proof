import Families.CatalanStatements

/-!
# OEIS A393171

Statements of the results in the accompanying paper (listed in `CONTENTS.md` at the
repository root), proved using the shared libraries of this project.
Formalization written by ChatGPT (OpenAI) for Dev D. Goyal.
-/

namespace OEIS.A393171

open Families
open PowerSeries Hanna.Series Families.CatalanComposition

noncomputable section
attribute [local instance] Classical.propDecidable

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

theorem link_to_first_sequence :
    (B : PowerSeries ℤ)=X+(CatalanComposition.A : PowerSeries ℤ)^2 := rfl

theorem link_composed_catalan :
    compose (B : PowerSeries ℤ) catalan=CatalanComposition.A :=
  CatalanComposition.B_composed_catalan

theorem complete_series_mod_eight :
    PowerSeries.map (Int.castRingHom (ZMod 8)) (B : PowerSeries ℤ)=
      X+X^2+4*(catalan-X-X*catalan) := by
  rw [CatalanComposition.map_B, CatalanComposition.B_mod_eight]

theorem divisibility_complement (n : ℕ) (hn : 2<n) :
    (8 : ℤ) ∣ coeff ℤ n (B : PowerSeries ℤ) ↔
      ¬∃ k : ℕ, 1≤k ∧ (n=2^k ∨ n=2^k+1) :=
  CatalanComposition.a393171_eight_dvd_iff n hn

end
end OEIS.A393171
