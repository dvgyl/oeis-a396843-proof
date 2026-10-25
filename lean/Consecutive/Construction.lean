module

public import Consecutive.Basic

/-! Canonical normalized solutions over arbitrary commutative rings. -/

@[expose] public section

namespace Consecutive

open PowerSeries Hanna.Series

variable {R : Type*} [CommRing R]

lemma equation_triangular (r : ℕ) :
    Triangular (fun (a : ℕ → R) n => coeff (n+2) (ofTail a-step r (ofTail a))) := by
  intro n a b hab
  have hd := (agree_iff_X_pow_dvd_sub (n+2) (ofTail a) (ofTail b)).mp
    (ofTail_agree a b n hab)
  have hp := step_contraction r (n+2) (normalized_ofTail a) (normalized_ofTail b) hd
  have hc := X_pow_dvd_iff.mp hp (n+2) (by omega)
  simp only [map_sub, coeff_ofTail] at hc ⊢
  linear_combination -hc

theorem solution_exists (r : ℕ) :
    ∃ F : PowerSeries R, Normalized F ∧ F=step r F := by
  let op := fun (a : ℕ → R) n => coeff (n+2) (ofTail a-step r (ofTail a))
  let a := triangularCoeffs op (fun _ => 0)
  have ha := triangularCoeffs_spec op (equation_triangular r) (fun _ => 0)
  refine ⟨ofTail a, normalized_ofTail a, ?_⟩
  have hs := step_normalized r (normalized_ofTail a)
  ext n
  rcases n with _ | (_ | n)
  · exact (normalized_ofTail a).1.trans hs.1.symm
  · exact (normalized_ofTail a).2.trans hs.2.symm
  · have hc := congrFun ha n
    change coeff (n+2) (ofTail a-step r (ofTail a))=0 at hc
    simpa only [map_sub, sub_eq_zero, Nat.succ_eq_add_one, Nat.add_assoc] using hc

theorem solution_unique (r : ℕ) {A B : PowerSeries R}
    (hA : Normalized A) (hB : Normalized B)
    (hEA : A=step r A) (hEB : B=step r B) : A=B := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hd := (agree_iff_X_pow_dvd_sub n A B).mp ih
    have hp := step_contraction r n hA hB hd
    have hc := X_pow_dvd_iff.mp hp n (by omega)
    rw [← hEA, ← hEB, map_sub, sub_eq_zero] at hc
    exact hc

theorem existence_uniqueness (r : ℕ) :
    ∃! F : PowerSeries R, Normalized F ∧ F=step r F := by
  obtain ⟨F,hF,hE⟩ := solution_exists (R:=R) r
  exact ⟨F,⟨hF,hE⟩,fun G hG => solution_unique r hG.1 hF hG.2 hE⟩

noncomputable def solution (r : ℕ) : PowerSeries R :=
  (existence_uniqueness (R:=R) r).exists.choose

theorem solution_normalized (r : ℕ) : Normalized (solution (R:=R) r) :=
  (existence_uniqueness (R:=R) r).exists.choose_spec.1

theorem solution_equation (r : ℕ) :
    solution (R:=R) r=step r (solution (R:=R) r) :=
  (existence_uniqueness (R:=R) r).exists.choose_spec.2

variable {S : Type*} [CommRing S]

theorem map_solution (f : R →+* S) (r : ℕ) :
    PowerSeries.map f (solution (R:=R) r)=solution (R:=S) r := by
  apply solution_unique r ((solution_normalized r).map f) (solution_normalized r)
  · rw [← map_step f r (solution_normalized r), ← solution_equation]
  · exact solution_equation r

noncomputable def a (r n : ℕ) : ℤ := coeff (R := ℤ) n (solution (R:=ℤ) r)

noncomputable def iterateCoeff (r k n : ℕ) : ℤ :=
  coeff (R := ℤ) n (iter (solution (R:=ℤ) r) k)

@[simp] theorem a_zero (r : ℕ) : a r 0=0 := (solution_normalized r).1

@[simp] theorem a_one (r : ℕ) : a r 1=1 := (solution_normalized r).2

end Consecutive
