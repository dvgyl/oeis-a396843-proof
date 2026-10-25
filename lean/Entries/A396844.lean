module

public import Hanna.Statements

/-!
# OEIS A396844

Statements of the results in the accompanying paper (listed in `CONTENTS.md` at the
repository root), proved using the shared libraries of this project.
Formalization written by ChatGPT (OpenAI) for Dev D. Goyal.
-/

@[expose] public section

namespace OEIS.A396844

open PowerSeries Hanna

theorem source_existence_uniqueness (R : Type*) [CommRing R] :
    ∃! U : PowerSeries R, Series.Normalized U ∧ Series.Psi (4 : R) U = X^2 := by
  exact Hanna.Statements.existence_uniqueness R 4

theorem even_positive_tail :
    a 4 1 = 1 ∧ ∀ n ≥ 2, (2 : ℤ) ∣ a 4 n := by
  exact Hanna.Statements.parity_even 4 (by decide)

theorem binary_divisibility (n : ℕ) (hn : 1 ≤ n) :
    (4 : ℤ)^binaryWeight (n-1) ∣ a 4 n := by
  exact Hanna.Statements.binary_divisibility_integer 4 (by decide) n hn

theorem residues_parameter_four :
    (∀ k : ℕ, (16:ℤ) ∣ a 4 (4^k+1) - 4) ∧
    (∀ k : ℕ, (16:ℤ) ∣ a 4 (2*4^k+1) - 12) ∧
    (∀ n : ℕ, 2 ≤ n → (¬∃ k : ℕ, n = 4^k+1) →
      (¬∃ k : ℕ, n = 2*4^k+1) → (16:ℤ) ∣ a 4 n) := by
  exact Hanna.Statements.residues_parameter_four

end OEIS.A396844
