import Round3.ThetaSubstitution

/-!
# Literal acceptance contracts for the two theta-substitution conjectures

These explicitly state the source equations, genuine unit quotient, full
integer existence and uniqueness, square indexing, and unbounded conclusions.
AI-generated for Dev D. Goyal. Review status: see AUTHORSHIP.md.
-/

namespace Round3.ThetaContracts

open PowerSeries Hanna.Series ThetaSubstitution

attribute [local instance] Classical.propDecidable

example : constantCoeff ℤ (theta (R:=ℤ))=1 := theta_constant

example (n : ℕ) (hn : 0<n) :
    coeff ℤ n (theta (R:=ℤ))=if ∃ k : ℕ, n=k^2 then 2 else 0 :=
  theta_coefficient n hn

example : constantCoeff ℤ A378580=1 := a378580_constant

example : constantCoeff ℤ A378581=1 := a378581_constant

example : A378580*(X*PowerSeries.invOfUnit A378580 1)=X :=
  a378580_quotient_identity

example : compose A378580 (X*PowerSeries.invOfUnit A378580 1)=theta :=
  a378580_source_equation

example : compose A378581 (X*A378581)=theta := a378581_source_equation

example : ∃! A : PowerSeries ℤ, constantCoeff ℤ A=1 ∧
    compose A (X*PowerSeries.invOfUnit A 1)=theta :=
  a378580_source_existence_uniqueness

example : ∃! A : PowerSeries ℤ, constantCoeff ℤ A=1 ∧
    compose A (X*A)=theta := a378581_source_existence_uniqueness

example (A : PowerSeries ℤ) (hA : constantCoeff ℤ A=1)
    (he : compose A (X*PowerSeries.invOfUnit A 1)=theta) : A=A378580 :=
  a378580_source_uniqueness hA he

example (A : PowerSeries ℤ) (hA : constantCoeff ℤ A=1)
    (he : compose A (X*A)=theta) : A=A378581 := a378581_source_uniqueness hA he

example : PowerSeries.map (Int.castRingHom (ZMod 4)) A378580=theta :=
  a378580_series_mod_four

example : PowerSeries.map (Int.castRingHom (ZMod 4)) A378581=theta :=
  a378581_series_mod_four

example (n : ℕ) (hn : 0<n) :
    (coeff ℤ n A378580 : ZMod 4)=if ∃ k : ℕ, n=k^2 then 2 else 0 :=
  a378580_congruence n hn

example (n : ℕ) (hn : 0<n) :
    (coeff ℤ n A378581 : ZMod 4)=if ∃ k : ℕ, n=k^2 then 2 else 0 :=
  a378581_congruence n hn

example (n : ℕ) (hn : 0<n) :
    (coeff ℤ n A378580 : ZMod 4)=2 ↔ ∃ k : ℕ, n=k^2 :=
  a378580_square_iff n hn

example (n : ℕ) (hn : 0<n) :
    (coeff ℤ n A378581 : ZMod 4)=2 ↔ ∃ k : ℕ, n=k^2 :=
  a378581_square_iff n hn

example (n : ℕ) (hn : 0<n) :
    (4 : ℤ) ∣ coeff ℤ n A378580 ↔ ¬ ∃ k : ℕ, n=k^2 := a378580_four_dvd_iff n hn

example (n : ℕ) (hn : 0<n) :
    (4 : ℤ) ∣ coeff ℤ n A378581 ↔ ¬ ∃ k : ℕ, n=k^2 := a378581_four_dvd_iff n hn

end Round3.ThetaContracts
