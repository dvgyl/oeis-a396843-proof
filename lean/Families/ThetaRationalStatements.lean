import Families.ThetaRational

/-!
Explicit statements for OEIS A380060 and A380680.
AI-generated for Dev D. Goyal; the second entry's literal conjecture is false.
-/

namespace Families.ThetaRationalStatements

open PowerSeries ThetaSubstitution Families.ThetaRational

noncomputable section

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

theorem explicit_actual_source (n : ℕ) :
    coeff ℤ n A380680=coeff ℤ n (1 : PowerSeries ℤ)+
      2*∑ k ∈ Finset.range (n+1), coeff ℤ n
        (X^((k+1)^2)*((2-X^(k+1))*unitInv (1-X^(k+1)*2))^(k+1)) :=
  a380680_coefficient_formula n

theorem a380060_statement (n : ℕ) (hn : 0<n) :
    ((coeff ℤ n A380060 : ZMod 4)=2 ↔ ∃ j : ℕ, n=j^2) ∧
    ((4 : ℤ) ∣ coeff ℤ n A380060 ↔ ¬∃ j : ℕ, n=j^2) :=
  ⟨a380060_square_iff n hn,a380060_four_dvd_iff n hn⟩

theorem a380680_corrected_statement (n : ℕ) (hn : 0<n) :
    ((coeff ℤ n A380680 : ZMod 4)=2 ↔ ∃ j : ℕ, n=2*j^2) ∧
    ((4 : ℤ) ∣ coeff ℤ n A380680 ↔ ¬∃ j : ℕ, n=2*j^2) :=
  ⟨a380680_twice_square_iff n hn,a380680_four_dvd_iff n hn⟩

theorem a380680_counterexamples : coeff ℤ 1 A380680=4 ∧ coeff ℤ 2 A380680=6 :=
  ⟨a380680_coeff_one,a380680_coeff_two⟩

theorem a380680_literal_statement_is_false :
    ¬(∀ n : ℕ, 0<n → ((coeff ℤ n A380680 : ZMod 4)=2 ↔ ∃ j : ℕ, n=j^2)) :=
  a380680_literal_conjecture_false

theorem a380680_complement_is_false :
    ¬(∀ n : ℕ, 0<n → (¬∃ j : ℕ, n=j^2) → (4 : ℤ) ∣ coeff ℤ n A380680) :=
  a380680_nonsquare_clause_false

end

end Families.ThetaRationalStatements
