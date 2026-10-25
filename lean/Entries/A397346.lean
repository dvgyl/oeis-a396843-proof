module

public import Families.ExpRecurrence
public import Families.ExpEquation

/-!
Independent type statements for the exact finite recurrence and original
modulo-eight conjecture of OEIS A397346. AI-generated for Dev D. Goyal.
-/

@[expose] public section

namespace OEIS.A397346

open scoped BigOperators
open Families.ExpRecurrence

theorem canonical_literal_recurrence :
    (a 0 : ℚ)=1 ∧ (a 1 : ℚ)=1 ∧ ∀ n : ℕ,
      (a (n+2) : ℚ) = 2*(n+2 : ℚ)*(a (n+1) : ℚ) +
        (n+2 : ℚ)*∑ i : Fin n,
          (2*(i.val+2 : ℚ)^2-1)/(i.val+2 : ℚ)*
            (a (i.val+2) : ℚ)*(a (n-i.val) : ℚ) :=
  a_source

theorem literal_recurrence_existence_uniqueness :
    ∃! s : ℕ → ℚ,
      s 0=1 ∧ s 1=1 ∧ ∀ n : ℕ,
        s (n+2) = 2*(n+2 : ℚ)*s (n+1) +
          (n+2 : ℚ)*∑ i : Fin n,
            (2*(i.val+2 : ℚ)^2-1)/(i.val+2 : ℚ)*s (i.val+2)*s (n-i.val) :=
  source_existence_uniqueness

theorem every_source_solution_is_integer_and_has_the_conjectured_residues
    (s : ℕ → ℚ) (h0 : s 0=1) (h1 : s 1=1)
    (hr : ∀ n : ℕ,
      s (n+2) = 2*(n+2 : ℚ)*s (n+1) +
        (n+2 : ℚ)*∑ i : Fin n,
          (2*(i.val+2 : ℚ)^2-1)/(i.val+2 : ℚ)*s (i.val+2)*s (n-i.val)) :
    ∃ z : ℕ → ℤ,
      (∀ n, s n=(z n : ℚ)) ∧
      (∀ n : ℕ, 0<n → (n : ℤ) ∣ z n) ∧
      (∀ k : ℕ,
        (z (4*k+2) : ZMod 8)=4 ∧ (z (4*k+3) : ZMod 8)=2 ∧
        (z (4*k+4) : ZMod 8)=0 ∧ (z (4*k+5) : ZMod 8)=2) := by
  refine ⟨a, ?_, index_dvd_a, a397346_block⟩
  have he := source_unique (show Source s from ⟨h0,h1,hr⟩) a_source
  intro n
  exact congrFun he n

theorem original_all_index_conjecture (k : ℕ) :
    (a (4*k+2) : ZMod 8)=4 ∧ (a (4*k+3) : ZMod 8)=2 ∧
    (a (4*k+4) : ZMod 8)=0 ∧ (a (4*k+5) : ZMod 8)=2 :=
  a397346_block k

theorem stronger_quotient_congruence (n : ℕ) (hn : 2≤n) :
    (b n : ZMod 8)=if n%4=3 then 6 else 2 :=
  b_mod_eight n hn

theorem exact_source_differential_identity :
    PowerSeries.derivative (R := ℚ)
      (PowerSeries.mk fun n => (a n : ℚ)) =
    (PowerSeries.mk fun n => (a n : ℚ)) *
      PowerSeries.derivative (R := ℚ)
        (PowerSeries.mk fun n =>
          if n=0 then 0 else if n=1 then 1 else
            (2*(n : ℚ)^2-1)/(2*(n : ℚ)^2)*(a n : ℚ)) :=
  a_differential_equation

theorem exponential_equation_existence_uniqueness :
    ∃! A : PowerSeries ℚ, Families.ExpEquation.Equation A :=
  Families.ExpEquation.existence_uniqueness

theorem exponential_equation_solution (A : PowerSeries ℚ) :
    Families.ExpEquation.Equation A ↔ A = PowerSeries.mk fun n => (a n : ℚ) :=
  Families.ExpEquation.equation_iff A

theorem displayed_initial_values :
    a 0=1 ∧ a 1=1 ∧ a 2=4 ∧ a 3=66 ∧ a 4=2248 :=
  a_initial_values

end OEIS.A397346
