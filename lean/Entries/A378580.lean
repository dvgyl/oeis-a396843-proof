import Families.ThetaSubstitution

/-!
# OEIS A378580

Statements of the results in the accompanying paper (listed in `CONTENTS.md` at the
repository root), proved using the shared libraries of this project.
Formalization written by ChatGPT (OpenAI) for Dev D. Goyal.
-/

namespace OEIS.A378580

open PowerSeries Hanna.Series ThetaSubstitution

noncomputable section
attribute [local instance] Classical.propDecidable

theorem theta_constant_term : constantCoeff ℤ (theta (R:=ℤ))=1 := theta_constant

theorem theta_coefficient_formula (n : ℕ) (hn : 0<n) :
    coeff ℤ n (theta (R:=ℤ))=if ∃ k : ℕ, n=k^2 then 2 else 0 :=
  theta_coefficient n hn

theorem minus_constant : constantCoeff ℤ A378580=1 := a378580_constant

theorem quotient_identity : A378580*(X*PowerSeries.invOfUnit A378580 1)=X :=
  a378580_quotient_identity

theorem minus_source : compose A378580 (X*PowerSeries.invOfUnit A378580 1)=theta :=
  a378580_source_equation

theorem minus_exists_unique : ∃! A : PowerSeries ℤ, constantCoeff ℤ A=1 ∧
    compose A (X*PowerSeries.invOfUnit A 1)=theta :=
  a378580_source_existence_uniqueness

theorem minus_unique (A : PowerSeries ℤ) (hA : constantCoeff ℤ A=1)
    (he : compose A (X*PowerSeries.invOfUnit A 1)=theta) : A=A378580 :=
  a378580_source_uniqueness hA he

theorem minus_series_mod_four : PowerSeries.map (Int.castRingHom (ZMod 4)) A378580=theta :=
  a378580_series_mod_four

theorem minus_congruence (n : ℕ) (hn : 0<n) :
    (coeff ℤ n A378580 : ZMod 4)=if ∃ k : ℕ, n=k^2 then 2 else 0 :=
  a378580_congruence n hn

theorem minus_square_iff (n : ℕ) (hn : 0<n) :
    (coeff ℤ n A378580 : ZMod 4)=2 ↔ ∃ k : ℕ, n=k^2 :=
  a378580_square_iff n hn

theorem minus_four_dvd_iff (n : ℕ) (hn : 0<n) :
    (4 : ℤ) ∣ coeff ℤ n A378580 ↔ ¬ ∃ k : ℕ, n=k^2 := a378580_four_dvd_iff n hn


end
end OEIS.A378580
