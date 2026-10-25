module

public import Families.ThetaRationalStatements

/-!
# OEIS A380680

Statements of the results in the accompanying paper (listed in `CONTENTS.md` at the
repository root), proved using the shared libraries of this project.
Formalization written by ChatGPT (OpenAI) for Dev D. Goyal.
-/

@[expose] public section

namespace OEIS.A380680

open Families
open PowerSeries Hanna.Series ThetaSubstitution Families.ThetaRational

noncomputable section
attribute [local instance] Classical.propDecidable

theorem explicit_actual_source (n : ℕ) :
    coeff (R := ℤ) n A380680=coeff (R := ℤ) n (1 : PowerSeries ℤ)+
      2*∑ k ∈ Finset.range (n+1), coeff (R := ℤ) n
        (X^((k+1)^2)*((2-X^(k+1))*unitInv (1-X^(k+1)*2))^(k+1)) :=
  a380680_coefficient_formula n

theorem a380680_corrected_statement (n : ℕ) (hn : 0<n) :
    ((coeff (R := ℤ) n A380680 : ZMod 4)=2 ↔ ∃ j : ℕ, n=2*j^2) ∧
    ((4 : ℤ) ∣ coeff (R := ℤ) n A380680 ↔ ¬∃ j : ℕ, n=2*j^2) :=
  ⟨a380680_twice_square_iff n hn,a380680_four_dvd_iff n hn⟩

theorem a380680_counterexamples : coeff (R := ℤ) 1 A380680=4 ∧ coeff (R := ℤ) 2 A380680=6 :=
  ⟨a380680_coeff_one,a380680_coeff_two⟩

theorem a380680_literal_statement_is_false :
    ¬(∀ n : ℕ, 0<n → ((coeff (R := ℤ) n A380680 : ZMod 4)=2 ↔ ∃ j : ℕ, n=j^2)) :=
  a380680_literal_conjecture_false

theorem a380680_complement_is_false :
    ¬(∀ n : ℕ, 0<n → (¬∃ j : ℕ, n=j^2) → (4 : ℤ) ∣ coeff (R := ℤ) n A380680) :=
  a380680_nonsquare_clause_false

theorem complete_series_mod_four :
    PowerSeries.map (Int.castRingHom (ZMod 4)) A380680=1+2*squareSeries 2 :=
  Families.ThetaRational.a380680_series_mod_four

end
end OEIS.A380680
