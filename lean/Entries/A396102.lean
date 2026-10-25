module

public import Families.InverseIterate

/-!
# OEIS A396102

Statements of the results in the accompanying paper (listed in `CONTENTS.md` at the
repository root), proved using the shared libraries of this project.
Formalization written by ChatGPT (OpenAI) for Dev D. Goyal.
-/

@[expose] public section

namespace OEIS.A396102

open PowerSeries Hanna.Series

noncomputable section

open Consecutive

abbrev A : PowerSeries ℤ := InverseIterate.A396102

theorem normalized : Normalized A := InverseIterate.F_normalized 3

theorem source_equation : compose A (compose A A) = (1+X)*compose A A :=
  InverseIterate.a396102_definition

theorem source_unique (U : PowerSeries ℤ) (hU : Normalized U)
    (he : compose U (compose U U) = (1+X)*compose U U) : U = A :=
  InverseIterate.a396102_unique U hU he

theorem source_existence_uniqueness :
    ∃! U : PowerSeries ℤ, Normalized U ∧
      compose U (compose U U) = (1+X)*compose U U := by
  refine ⟨A, ⟨normalized, source_equation⟩, ?_⟩
  intro U hU
  exact source_unique U hU.1 hU.2

theorem coefficient_congruence (n : ℕ) (hn : 1 ≤ n) :
    (coeff (R := ℤ) n A : ZMod 3) = 1 :=
  InverseIterate.a396102_congruence n hn

theorem iterate_congruence (k n : ℕ) (hn : 1 ≤ n) :
    (coeff (R := ℤ) n (iter A k) : ZMod 3) = (k : ZMod 3)^(n-1) :=
  InverseIterate.iterate_coefficient_congruence 3 k n hn

theorem family_source_existence (r : ℕ) :
    ∃! U : PowerSeries ℤ, Normalized U ∧
      iter U (r+1) = (1+X)*iter U r :=
  InverseIterate.F_original_existence_uniqueness r

theorem family_source_equation (r : ℕ) :
    iter (InverseIterate.F (S:=ℤ) (r+1)) (r+1) =
      (1+X)*iter (InverseIterate.F (r+1)) r :=
  InverseIterate.F_original_equation r

theorem auxiliary_source_equation (r : ℕ) :
    InverseIterate.R (S:=ℤ) r =
      X-InverseIterate.R r*iter (InverseIterate.R r) r :=
  InverseIterate.R_equation r

theorem inverse_right (r : ℕ) :
    compose (InverseIterate.R (S:=ℤ) r) (InverseIterate.F r) = X :=
  InverseIterate.compose_R_F r

theorem inverse_left (r : ℕ) :
    compose (InverseIterate.F (S:=ℤ) r) (InverseIterate.R r) = X :=
  InverseIterate.compose_F_R r

theorem family_coefficient_congruence (r n : ℕ) (hn : 1 ≤ n) :
    (coeff (R := ℤ) n (InverseIterate.F r) : ZMod r) = 1 :=
  InverseIterate.coefficient_congruence r n hn

theorem family_iterate_congruence (r k n : ℕ) (hn : 1 ≤ n) :
    (coeff (R := ℤ) n (iter (InverseIterate.F r) k) : ZMod r) =
      (k : ZMod r)^(n-1) :=
  InverseIterate.iterate_coefficient_congruence r k n hn

end
end OEIS.A396102
