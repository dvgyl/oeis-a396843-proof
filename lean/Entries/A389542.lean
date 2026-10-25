module

public import Families.SquareReversion

/-!
# OEIS A389542

Statements of the results in the accompanying paper (listed in `CONTENTS.md` at the
repository root), proved using the shared libraries of this project.
Formalization written by ChatGPT (OpenAI) for Dev D. Goyal.
-/

@[expose] public section

namespace OEIS.A389542

open Families
open PowerSeries Hanna.Series Families.SquareReversion

noncomputable section
attribute [local instance] Classical.propDecidable

theorem auxiliary_exists_unique : ∃! G : PowerSeries ℤ, Normalized G ∧
    G=X+G^2-2*X*compose G (4*X^3) := L_existence_uniqueness

theorem normalized : coeff (R := ℤ) 0 (A389542 : PowerSeries ℤ)=0 ∧
    coeff (R := ℤ) 1 (A389542 : PowerSeries ℤ)=1 := A389542_normalized

theorem auxiliary_definition : (R : PowerSeries ℤ)=X-2*X*L := rfl

theorem inverse_equation : (R : PowerSeries ℤ)^2+compose R (4*X^3)=X^2 := R_equation

theorem inverse_right : compose (R : PowerSeries ℤ) A389542=X := compose_R_A

theorem inverse_left : compose (A389542 : PowerSeries ℤ) R=X := compose_A_R

theorem source_equation : compose (A389542 : PowerSeries ℤ) (A389542^2-X^2)=4*A389542^3 :=
  a389542_equation

theorem source_exists_unique : ∃! G : PowerSeries ℤ, Normalized G ∧
    compose G (G^2-X^2)=4*G^3 := a389542_existence_uniqueness

theorem source_unique (G : PowerSeries ℤ) (hG : Normalized G)
    (he : compose G (G^2-X^2)=4*G^3) : G=A389542 := a389542_unique G hG he

theorem auxiliary_parity (n : ℕ) : coeff (R := (ZMod 2)) n L=1 ↔ ∃ k : ℕ, n=2^k := L_coeff_one_iff n

theorem inverse_involution : compose (R : PowerSeries (ZMod 4)) R=X := R_involution_mod_four

theorem inverse_mod_four : (A389542 : PowerSeries (ZMod 4))=R := A_eq_R_mod_four

theorem series_mod_four : PowerSeries.map (Int.castRingHom (ZMod 4)) (A389542 : PowerSeries ℤ)=
    X-2*X*(L : PowerSeries (ZMod 4)) := a389542_series_mod_four

theorem residue_mod_four (n : ℕ) (hn : 1<n) :
    (coeff (R := ℤ) n (A389542 : PowerSeries ℤ) : ZMod 4)=
      if ∃ k : ℕ, n=2^k+1 then 2 else 0 := a389542_residue n hn

theorem exceptional_iff (n : ℕ) (hn : 1<n) :
    (coeff (R := ℤ) n (A389542 : PowerSeries ℤ) : ZMod 4)=2 ↔
      ∃ k : ℕ, n=2^k+1 := a389542_two_mod_four_iff n hn

theorem four_dvd_iff (n : ℕ) (hn : 1<n) :
    (4 : ℤ) ∣ coeff (R := ℤ) n (A389542 : PowerSeries ℤ) ↔
      ¬ ∃ k : ℕ, n=2^k+1 := a389542_four_dvd_iff n hn

end
end OEIS.A389542
