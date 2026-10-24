import Round3.LacunaryInverse

/-!
# Literal-source and unbounded-coefficient contracts for A389537

AI-generated for Dev D. Goyal. Review status: see AUTHORSHIP.md.
-/
namespace Round3.LacunaryContracts
open PowerSeries Hanna.Series LacunaryInverse
attribute [local instance] Classical.propDecidable

example : ∃! U : PowerSeries ℤ, Normalized U ∧ U=X-compose U (X^2) :=
  auxiliary_existence_uniqueness

example : (R : PowerSeries ℤ)+compose R (X^2)=X := R_equation
example : compose (R : PowerSeries ℤ) A=X := R_A
example : compose (A : PowerSeries ℤ) R=X := A_R
example : coeff ℤ 0 (A : PowerSeries ℤ)=0 ∧ coeff ℤ 1 (A : PowerSeries ℤ)=1 :=
  A_normalized
example : compose (A : PowerSeries ℤ) (A-X)=A^2 := A_equation
example : ∃! U : PowerSeries ℤ, Normalized U ∧ compose U (U-X)=U^2 :=
  source_existence_uniqueness
example (U : PowerSeries ℤ) (hU : Normalized U) (he : compose U (U-X)=U^2) : U=A :=
  A_unique U hU he
example : PowerSeries.map (Int.castRingHom (ZMod 2)) (A : PowerSeries ℤ)=X+X^2 := by
  rw [map_A, A_mod_two]
example : (A : PowerSeries ℤ)=X+X^2+2*H := A_decomposition
example : PowerSeries.map (Int.castRingHom (ZMod 2)) H +
    (PowerSeries.map (Int.castRingHom (ZMod 2)) H)^2=X^3 := H_mod_two_equation
example (n : ℕ) : coeff (ZMod 2) n (PowerSeries.map (Int.castRingHom (ZMod 2)) H)=1 ↔
    ∃ k : ℕ, n=3*2^k := H_mod_two_coeff n
example (n : ℕ) (hn : 2<n) :
    (coeff ℤ n (A : PowerSeries ℤ) : ZMod 4)=
      if ∃ k : ℕ, n=3*2^k then 2 else 0 := a389537_residue n hn

end Round3.LacunaryContracts
