module

public import Hanna.Series.Inverse
public import Mathlib.Algebra.Polynomial.Eval.Defs

@[expose] public section

namespace Hanna

open PowerSeries

variable {R : Type*} [CommRing R]

noncomputable def A (m : R) : PowerSeries R := Series.solution m
noncomputable def B (m : R) : PowerSeries R :=
  Series.inverse (A m) (Series.solution_normalized m)

lemma A_normalized (m : R) : Series.Normalized (A m) := Series.solution_normalized m
lemma B_normalized (m : R) : Series.Normalized (B m) :=
  Series.inverse_normalized (A m) (A_normalized m)
lemma A_equation (m : R) : Series.Psi m (A m) = X^2 := Series.solution_equation m
lemma A_comp_B (m : R) : Series.compose (A m) (B m) = X :=
  Series.compose_inverse_right (A m) (A_normalized m)
lemma B_comp_A (m : R) : Series.compose (B m) (A m) = X :=
  Series.compose_inverse_left (A m) (A_normalized m)

variable {S : Type*} [CommRing S]

lemma map_A (f : R →+* S) (m : R) : PowerSeries.map f (A m) = A (f m) :=
  Series.map_solution f m

lemma map_B (f : R →+* S) (m : R) : PowerSeries.map f (B m) = B (f m) := by
  apply Series.inverse_unique (A_normalized (f m)) (B_normalized (f m))
  · rw [← map_A f m, ← Series.map_compose f (B m) (A m) (A_normalized m).constantCoeff,
      B_comp_A, PowerSeries.map_X]
  · exact A_comp_B (f m)

noncomputable def a (m : ℤ) (n : ℕ) : ℤ := coeff (R := ℤ) n (A m)
noncomputable def b (m : ℤ) (n : ℕ) : ℤ := coeff (R := ℤ) n (B m)
noncomputable def P (n : ℕ) : Polynomial ℤ := coeff (R := (Polynomial ℤ)) n (A Polynomial.X)
noncomputable def Q (n : ℕ) : Polynomial ℤ := coeff (R := (Polynomial ℤ)) n (B Polynomial.X)

lemma coefficient_polynomial_specialization (m : ℤ) (n : ℕ) :
    Polynomial.eval m (P n) = a m n ∧ Polynomial.eval m (Q n) = b m n := by
  have hA := congrArg (coeff (R := ℤ) n) (map_A (Polynomial.evalRingHom m) Polynomial.X)
  have hB := congrArg (coeff (R := ℤ) n) (map_B (Polynomial.evalRingHom m) Polynomial.X)
  constructor
  · simpa [P, a] using hA
  · simpa [Q, b] using hB

end Hanna
