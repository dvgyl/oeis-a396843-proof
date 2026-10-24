import Round3.SquareReversion

/-!
# Explicit source and congruence contracts for OEIS A389542

These independently written types fix the integer coefficient domain, literal
source equation, normalized unique solution, genuine compositional inverse,
and unbounded residue pattern with the OEIS indexing.

AI-generated for Dev D. Goyal. Review status: see AUTHORSHIP.md.
-/

namespace Round3.SquareContracts

open PowerSeries Hanna.Series SquareReversion

attribute [local instance] Classical.propDecidable

example : ∃! G : PowerSeries ℤ, Normalized G ∧
    G=X+G^2-2*X*compose G (4*X^3) := L_existence_uniqueness

example : coeff ℤ 0 (A389542 : PowerSeries ℤ)=0 ∧
    coeff ℤ 1 (A389542 : PowerSeries ℤ)=1 := A389542_normalized

example : (R : PowerSeries ℤ)=X-2*X*L := rfl

example : (R : PowerSeries ℤ)^2+compose R (4*X^3)=X^2 := R_equation

example : compose (R : PowerSeries ℤ) A389542=X := compose_R_A

example : compose (A389542 : PowerSeries ℤ) R=X := compose_A_R

example : compose (A389542 : PowerSeries ℤ) (A389542^2-X^2)=4*A389542^3 :=
  a389542_equation

example : ∃! G : PowerSeries ℤ, Normalized G ∧
    compose G (G^2-X^2)=4*G^3 := a389542_existence_uniqueness

example (G : PowerSeries ℤ) (hG : Normalized G)
    (he : compose G (G^2-X^2)=4*G^3) : G=A389542 := a389542_unique G hG he

example (n : ℕ) : coeff (ZMod 2) n L=1 ↔ ∃ k : ℕ, n=2^k := L_coeff_one_iff n

example : compose (R : PowerSeries (ZMod 4)) R=X := R_involution_mod_four

example : (A389542 : PowerSeries (ZMod 4))=R := A_eq_R_mod_four

example : PowerSeries.map (Int.castRingHom (ZMod 4)) (A389542 : PowerSeries ℤ)=
    X-2*X*(L : PowerSeries (ZMod 4)) := a389542_series_mod_four

example (n : ℕ) (hn : 1<n) :
    (coeff ℤ n (A389542 : PowerSeries ℤ) : ZMod 4)=
      if ∃ k : ℕ, n=2^k+1 then 2 else 0 := a389542_residue n hn

example (n : ℕ) (hn : 1<n) :
    (coeff ℤ n (A389542 : PowerSeries ℤ) : ZMod 4)=2 ↔
      ∃ k : ℕ, n=2^k+1 := a389542_two_mod_four_iff n hn

example (n : ℕ) (hn : 1<n) :
    (4 : ℤ) ∣ coeff ℤ n (A389542 : PowerSeries ℤ) ↔
      ¬ ∃ k : ℕ, n=2^k+1 := a389542_four_dvd_iff n hn

end Round3.SquareContracts
