import Families.ThetaRationalStatements

/-!
# OEIS A380060

Statements of the results in the accompanying paper (listed in `CONTENTS.md` at the
repository root), proved using the shared libraries of this project.
Formalization written by ChatGPT (OpenAI) for Dev D. Goyal.
-/

namespace OEIS.A380060

open Families
open PowerSeries Hanna.Series ThetaSubstitution Families.ThetaRational

noncomputable section
attribute [local instance] Classical.propDecidable

theorem implicit_source_exists_unique :
    ∃! A : PowerSeries ℤ, A=1+2*PowerSeries.mk (fun n =>
      ∑ k ∈ Finset.range (n+1), coeff ℤ n
        (X^((k+1)^2)*((A-X^(k+1))*unitInv (1-X^(k+1)*A))^(k+1))) :=
  a380060_existence_uniqueness

theorem implicit_actual_source (n : ℕ) :
    coeff ℤ n A380060=coeff ℤ n (1 : PowerSeries ℤ)+
      2*∑ k ∈ Finset.range (n+1), coeff ℤ n
        (X^((k+1)^2)*((A380060-X^(k+1))*unitInv (1-X^(k+1)*A380060))^(k+1)) :=
  a380060_coefficient_formula n

theorem a380060_statement (n : ℕ) (hn : 0<n) :
    ((coeff ℤ n A380060 : ZMod 4)=2 ↔ ∃ j : ℕ, n=j^2) ∧
    ((4 : ℤ) ∣ coeff ℤ n A380060 ↔ ¬∃ j : ℕ, n=j^2) :=
  ⟨a380060_square_iff n hn,a380060_four_dvd_iff n hn⟩

theorem complete_series_mod_four :
    PowerSeries.map (Int.castRingHom (ZMod 4)) A380060=1+2*squareSeries 1 :=
  Families.ThetaRational.a380060_series_mod_four

end
end OEIS.A380060
