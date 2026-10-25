module

public import Hanna.Series.Construction

@[expose] public section

namespace Hanna.Series

open PowerSeries

variable {R : Type*} [CommRing R]

lemma compose_triangular (A : PowerSeries R) (hA : Normalized A) :
    Triangular (fun (a : ℕ → R) n => coeff (n+2) (compose A (ofTail a))) := by
  intro n a b hab
  have hd := (agree_iff_X_pow_dvd_sub (n+2) (ofTail a) (ofTail b)).mp
    (ofTail_agree a b n hab)
  have hp := compose_normalized_inner_error A (ofTail a) (ofTail b) (n+2)
    hA (normalized_ofTail a).constantCoeff (normalized_ofTail b).constantCoeff hd
  have hc := X_pow_dvd_iff.mp hp (n+2) (by omega)
  simpa only [map_sub, coeff_ofTail, sub_eq_zero] using hc

lemma right_inverse_exists (A : PowerSeries R) (hA : Normalized A) :
    ∃ B : PowerSeries R, Normalized B ∧ compose A B = X := by
  let F : (ℕ → R) → ℕ → R := fun (a : ℕ → R) n => coeff (n+2) (compose A (ofTail a))
  obtain ⟨a, ha, _⟩ := triangular_existsUnique F (compose_triangular A hA) (fun _ => 0)
  refine ⟨ofTail a, normalized_ofTail a, ?_⟩
  have hnorm := hA.compose (normalized_ofTail a)
  ext n
  rcases n with _ | (_ | n)
  · simpa using hnorm.1
  · simpa using hnorm.2
  · have hc := congrFun ha n
    change coeff (n+2) (compose A (ofTail a)) = 0 at hc
    simpa [Nat.succ_eq_add_one, Nat.add_assoc, coeff_X] using hc

lemma left_inverse_of_right_inverse {A B : PowerSeries R}
    (hB : Normalized B) (hAB : compose A B = X) :
    compose B A = X := by
  obtain ⟨D, hD, hBD⟩ := right_inverse_exists B hB
  have hAD : A = D := by
    calc
      A = compose A X := (compose_X_right A).symm
      _ = compose A (compose B D) := congrArg (compose A) hBD.symm
      _ = compose (compose A B) D :=
        (compose_assoc A B D hB.constantCoeff hD.constantCoeff).symm
      _ = compose X D := congrArg (fun E => compose E D) hAB
      _ = D := compose_X_left D hD.constantCoeff
  rw [hAD, hBD]

lemma inverse_unique {A B D : PowerSeries R}
    (hA : Normalized A) (hD : Normalized D)
    (hBA : compose B A = X) (hAD : compose A D = X) : B = D := by
  calc
    B = compose B X := (compose_X_right B).symm
    _ = compose B (compose A D) := congrArg (compose B) hAD.symm
    _ = compose (compose B A) D :=
      (compose_assoc B A D hA.constantCoeff hD.constantCoeff).symm
    _ = compose X D := congrArg (fun E => compose E D) hBA
    _ = D := compose_X_left D hD.constantCoeff

theorem compositional_inverse (A : PowerSeries R) (hA : Normalized A) :
    ∃! B : PowerSeries R, Normalized B ∧ compose A B = X ∧ compose B A = X := by
  obtain ⟨B, hB, hAB⟩ := right_inverse_exists A hA
  have hBA := left_inverse_of_right_inverse hB hAB
  refine ⟨B, ⟨hB, hAB, hBA⟩, ?_⟩
  intro D hD
  exact inverse_unique hA hB hD.2.2 hAB

noncomputable def inverse (A : PowerSeries R) (hA : Normalized A) : PowerSeries R :=
  (compositional_inverse A hA).exists.choose

lemma inverse_normalized (A : PowerSeries R) (hA : Normalized A) :
    Normalized (inverse A hA) :=
  (compositional_inverse A hA).exists.choose_spec.1

lemma compose_inverse_right (A : PowerSeries R) (hA : Normalized A) :
    compose A (inverse A hA) = X :=
  (compositional_inverse A hA).exists.choose_spec.2.1

lemma compose_inverse_left (A : PowerSeries R) (hA : Normalized A) :
    compose (inverse A hA) A = X :=
  (compositional_inverse A hA).exists.choose_spec.2.2

variable {S : Type*} [CommRing S]

lemma map_inverse (f : R →+* S) (A : PowerSeries R) (hA : Normalized A) :
    PowerSeries.map f (inverse A hA) =
      inverse (PowerSeries.map f A) (hA.map f) := by
  apply inverse_unique (hA.map f)
    (inverse_normalized (PowerSeries.map f A) (hA.map f))
  · rw [← map_compose f (inverse A hA) A hA.constantCoeff,
      compose_inverse_left, PowerSeries.map_X]
  · exact compose_inverse_right (PowerSeries.map f A) (hA.map f)

end Hanna.Series
