module

public import Families.NestedStatements

/-!
# OEIS A195194

Statements of the results in the accompanying paper (listed in `CONTENTS.md` at the
repository root), proved using the shared libraries of this project.
Formalization written by ChatGPT (OpenAI) for Dev D. Goyal.
-/

@[expose] public section

namespace OEIS.A195194

open Families
open PowerSeries Hanna.Series Families.NestedReversion

noncomputable section
attribute [local instance] Classical.propDecidable

theorem normalized_source : coeff (R := ℤ) 0 A=0 ∧ coeff (R := ℤ) 1 A=1 := A_normalized

theorem all_tails_normalized : ∀ j : ℕ, Normalized (tail (weights ℤ) j) :=
  tail_normalized (weights ℤ)

theorem all_tails_source : ∀ j : ℕ,
    compose (X-C (R := ℤ) (j+1)*X*tail (weights ℤ) (j+1)) (tail (weights ℤ) j)=X ∧
    compose (tail (weights ℤ) j) (X-C (R := ℤ) (j+1)*X*tail (weights ℤ) (j+1))=X := by
  intro j
  exact ⟨tail_right_inverse (weights ℤ) j, tail_left_inverse (weights ℤ) j⟩

theorem nested_definition_unique : ∃! F : ℕ → PowerSeries ℤ,
    (∀ j : ℕ, Normalized (F j)) ∧ (∀ j : ℕ,
      compose (X-C (R := ℤ) (j+1)*X*F (j+1)) (F j)=X ∧
      compose (F j) (X-C (R := ℤ) (j+1)*X*F (j+1))=X) :=
  source_existence_uniqueness (weights ℤ)

theorem first_tail_reversion :
    compose (X-X*tail (weights ℤ) 1) A=X ∧
    compose A (X-X*tail (weights ℤ) 1)=X := ⟨A_source, A_source_left⟩

theorem finite_nest_coefficients (d n : ℕ) (hn : n<d+2) :
    coeff (R := ℤ) n (approximation (weights ℤ) d 0)=a n := by
  have h := X_pow_dvd_iff.mp (approximation_agrees (weights ℤ) d 0) n hn
  exact sub_eq_zero.mp h

theorem binary_equation :
    PowerSeries.map (Int.castRingHom (ZMod 2)) A-
      (PowerSeries.map (Int.castRingHom (ZMod 2)) A)^2=X := A_mod_two_quadratic

theorem exact_parity (n : ℕ) :
    Odd (coeff (R := ℤ) n A) ↔ ∃ k : ℕ, n=2^k := a195194_parity n

theorem arbitrary_weights_unique {R : Type*} [CommRing R] (w : ℕ → R) :
    ∃! F : ℕ → PowerSeries R,
      (∀ j, Normalized (F j)) ∧ (∀ j,
        compose (pre (w j) (F (j+1))) (F j)=X ∧
        compose (F j) (pre (w j) (F (j+1)))=X) :=
  Families.NestedReversion.source_existence_uniqueness w

theorem arbitrary_finite_depth {R : Type*} [CommRing R] (w : ℕ → R) (d j : ℕ) :
    (X : PowerSeries R)^(d+2) ∣ approximation w d j-tail w j :=
  Families.NestedReversion.approximation_agrees w d j

end
end OEIS.A195194
