import Families.ElementaryStatements

/-!
# OEIS A397588

Statements of the results in the accompanying paper (listed in `CONTENTS.md` at the
repository root), proved using the shared libraries of this project.
Formalization written by ChatGPT (OpenAI) for Dev D. Goyal.
-/

namespace OEIS.A397588

open Families
open PowerSeries Hanna.Series 

noncomputable section
attribute [local instance] Classical.propDecidable

theorem differential_existence :
    ∃! F : PowerSeries ℤ,
      (coeff ℤ 0 F=0 ∧ coeff ℤ 1 F=1) ∧ F=X+derivative ℤ (X*F^2) :=
  DifferentialParity.existence_uniqueness

theorem differential_definition :
    coeff ℤ 0 DifferentialParity.A=0 ∧
    coeff ℤ 1 DifferentialParity.A=1 ∧
    (DifferentialParity.A : PowerSeries ℤ)=
      X+derivative ℤ (X*DifferentialParity.A^2) :=
  ⟨DifferentialParity.A_normalized.1,DifferentialParity.A_normalized.2,
    DifferentialParity.A_equation⟩

theorem differential_source_unique (F : PowerSeries ℤ)
    (h0 : coeff ℤ 0 F=0) (h1 : coeff ℤ 1 F=1)
    (he : F=X+derivative ℤ (X*F^2)) : F=DifferentialParity.A :=
  DifferentialParity.solution_unique ⟨h0,h1⟩ DifferentialParity.A_normalized
    he DifferentialParity.A_equation

theorem differential_parity (n : ℕ) :
    Odd (coeff ℤ n DifferentialParity.A) ↔ ∃ k : ℕ, n=2^k :=
  DifferentialParity.a397588_parity n

theorem differential_mod_three :
    PowerSeries.map (Int.castRingHom (ZMod 3)) DifferentialParity.A=X := by
  rw [DifferentialParity.map_A, DifferentialParity.A_mod_three]

theorem differential_divisible_by_three (n : ℕ) (hn : 1<n) :
    (3 : ℤ) ∣ coeff ℤ n DifferentialParity.A :=
  DifferentialParity.a397588_divisible_by_three n hn


end
end OEIS.A397588
