module

public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace Hanna.Series

variable {R : Type*} [CommRing R]

def Triangular (F : (ℕ → R) → ℕ → R) : Prop :=
  ∀ n a b, (∀ k < n, a k = b k) → F a n - F b n = a n - b n

noncomputable def triangularCoeffs (F : (ℕ → R) → ℕ → R) (target : ℕ → R) : ℕ → R :=
  WellFounded.fix Nat.lt_wfRel.wf fun n rec =>
    target n - F (fun k => if h : k < n then rec k h else 0) n

theorem triangularCoeffs_eq (F : (ℕ → R) → ℕ → R) (target : ℕ → R) (n : ℕ) :
    triangularCoeffs F target n = target n -
      F (fun k => if k < n then triangularCoeffs F target k else 0) n := by
  rw [triangularCoeffs, WellFounded.fix_eq]
  rfl

theorem triangularCoeffs_spec (F : (ℕ → R) → ℕ → R) (hF : Triangular F)
    (target : ℕ → R) : F (triangularCoeffs F target) = target := by
  funext n
  let a := triangularCoeffs F target
  let b : ℕ → R := fun k => if k < n then a k else 0
  have hab : ∀ k < n, a k = b k := by
    intro k hk
    simp [b, hk]
  have hd := hF n a b hab
  have hb : b n = 0 := by simp [b]
  have ha : a n = target n - F b n := triangularCoeffs_eq F target n
  rw [hb, ha] at hd
  linear_combination hd

theorem triangular_existsUnique (F : (ℕ → R) → ℕ → R) (hF : Triangular F)
    (target : ℕ → R) : ∃! a, F a = target := by
  refine ⟨triangularCoeffs F target, triangularCoeffs_spec F hF target, ?_⟩
  intro b hb
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hd := hF n b (triangularCoeffs F target) ih
    rw [hb, triangularCoeffs_spec F hF target, sub_self] at hd
    exact sub_eq_zero.mp hd.symm

end Hanna.Series
