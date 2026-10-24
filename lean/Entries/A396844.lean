import Hanna.Acceptance

/-!
Separate typed proof interface for OEIS A396844.
The complete implementation is in the imported, preserved libraries.
AI disclosure: ChatGPT (OpenAI) generated this presentation for Dev D. Goyal.
Review status: see AUTHORSHIP.md.
-/

namespace FinalCollection.A396844

open PowerSeries Hanna

theorem source_existence_uniqueness (R : Type*) [CommRing R] :
    ∃! U : PowerSeries R, Series.Normalized U ∧ Series.Psi (4 : R) U = X^2 := by
  exact Hanna.Acceptance.existence_uniqueness R 4

theorem even_positive_tail :
    a 4 1 = 1 ∧ ∀ n ≥ 2, (2 : ℤ) ∣ a 4 n := by
  exact Hanna.Acceptance.parity_even 4 (by decide)

theorem binary_divisibility (n : ℕ) (hn : 1 ≤ n) :
    (4 : ℤ)^binaryWeight (n-1) ∣ a 4 n := by
  exact Hanna.Acceptance.binary_divisibility_integer 4 (by decide) n hn

theorem residues_parameter_four :
    (∀ k : ℕ, (16:ℤ) ∣ a 4 (4^k+1) - 4) ∧
    (∀ k : ℕ, (16:ℤ) ∣ a 4 (2*4^k+1) - 12) ∧
    (∀ n : ℕ, 2 ≤ n → (¬∃ k : ℕ, n = 4^k+1) →
      (¬∃ k : ℕ, n = 2*4^k+1) → (16:ℤ) ∣ a 4 n) := by
  exact Hanna.Acceptance.residues_parameter_four

end FinalCollection.A396844
