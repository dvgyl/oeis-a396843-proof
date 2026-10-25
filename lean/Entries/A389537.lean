module

public import Families.LacunaryInverse

/-!
# OEIS A389537

Statements of the results in the accompanying paper (listed in `CONTENTS.md` at the
repository root), proved using the shared libraries of this project.
Formalization written by ChatGPT (OpenAI) for Dev D. Goyal.
-/

@[expose] public section

namespace OEIS.A389537

open Families
open PowerSeries Hanna.Series Families.LacunaryInverse

noncomputable section
attribute [local instance] Classical.propDecidable

theorem auxiliary_exists_unique : ∃! U : PowerSeries ℤ, Normalized U ∧ U=X-compose U (X^2) :=
  auxiliary_existence_uniqueness

theorem auxiliary_equation : (R : PowerSeries ℤ)+compose R (X^2)=X := R_equation

theorem inverse_right : compose (R : PowerSeries ℤ) A=X := R_A

theorem inverse_left : compose (A : PowerSeries ℤ) R=X := A_R

theorem normalized : coeff (R := ℤ) 0 (A : PowerSeries ℤ)=0 ∧ coeff (R := ℤ) 1 (A : PowerSeries ℤ)=1 :=
  A_normalized

theorem source_equation : compose (A : PowerSeries ℤ) (A-X)=A^2 := A_equation

theorem source_exists_unique : ∃! U : PowerSeries ℤ, Normalized U ∧ compose U (U-X)=U^2 :=
  source_existence_uniqueness

theorem source_unique (U : PowerSeries ℤ) (hU : Normalized U) (he : compose U (U-X)=U^2) : U=A :=
  A_unique U hU he

theorem series_mod_two : PowerSeries.map (Int.castRingHom (ZMod 2)) (A : PowerSeries ℤ)=X+X^2 := by
  rw [map_A, A_mod_two]

theorem integer_decomposition : (A : PowerSeries ℤ)=X+X^2+2*H := A_decomposition

theorem half_equation_mod_two : PowerSeries.map (Int.castRingHom (ZMod 2)) H +
    (PowerSeries.map (Int.castRingHom (ZMod 2)) H)^2=X^3 := H_mod_two_equation

theorem half_binary_support (n : ℕ) : coeff (R := (ZMod 2)) n (PowerSeries.map (Int.castRingHom (ZMod 2)) H)=1 ↔
    ∃ k : ℕ, n=3*2^k := H_mod_two_coeff n

theorem residue_mod_four (n : ℕ) (hn : 2<n) :
    (coeff (R := ℤ) n (A : PowerSeries ℤ) : ZMod 4)=
      if ∃ k : ℕ, n=3*2^k then 2 else 0 := a389537_residue n hn

end
end OEIS.A389537
