import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Substitution

namespace Hanna.Series

open PowerSeries

variable {R : Type*} [CommRing R]

/-- The constant coefficient is zero, and the linear coefficient is one. -/
def Normalized (A : PowerSeries R) : Prop :=
  coeff R 0 A = 0 ∧ coeff R 1 A = 1

/-- The outer series is the first argument. -/
noncomputable def compose (outer inner : PowerSeries R) : PowerSeries R :=
  MvPowerSeries.subst (fun (_ : Unit) => inner) outer

noncomputable def T (m : R) (A : PowerSeries R) : PowerSeries R :=
  X * A - C R m * X * A ^ 2

noncomputable def Psi (m : R) (A : PowerSeries R) : PowerSeries R :=
  compose A (T m A)

def Agree (n : ℕ) (A B : PowerSeries R) : Prop :=
  ∀ k < n, coeff R k A = coeff R k B

lemma Normalized.constantCoeff {A : PowerSeries R} (hA : Normalized A) :
    constantCoeff R A = 0 := by
  simpa only [coeff_zero_eq_constantCoeff_apply] using hA.1

@[simp] theorem normalized_X : Normalized (X : PowerSeries R) := by
  simp [Normalized, coeff_X]

theorem hasSubst_of_constantCoeff_zero {B : PowerSeries R}
    (hB : constantCoeff R B = 0) :
    MvPowerSeries.HasSubst (fun (_ : Unit) => B) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hB)

@[simp] theorem constantCoeff_T (m : R) (A : PowerSeries R) :
    constantCoeff R (T m A) = 0 := by
  simp [T]

@[simp] theorem compose_X_right (A : PowerSeries R) : compose A X = A := by
  unfold compose
  have h : (fun _ : Unit => (X : PowerSeries R)) = MvPowerSeries.X := by
    funext u
    cases u
    rfl
  rw [h, MvPowerSeries.subst_self]
  rfl

@[simp] theorem compose_X_left (B : PowerSeries R) (hB : constantCoeff R B = 0) :
    compose X B = B :=
  MvPowerSeries.subst_X (hasSubst_of_constantCoeff_zero hB) ()

theorem compose_add (A B D : PowerSeries R) (hD : constantCoeff R D = 0) :
    compose (A + B) D = compose A D + compose B D :=
  MvPowerSeries.subst_add (hasSubst_of_constantCoeff_zero hD) A B

theorem compose_sub (A B D : PowerSeries R) (hD : constantCoeff R D = 0) :
    compose (A - B) D = compose A D - compose B D := by
  simpa only [MvPowerSeries.substAlgHom_apply, compose] using
    map_sub (MvPowerSeries.substAlgHom (R := R)
      (hasSubst_of_constantCoeff_zero hD)) A B

theorem compose_mul (A B D : PowerSeries R) (hD : constantCoeff R D = 0) :
    compose (A * B) D = compose A D * compose B D :=
  MvPowerSeries.subst_mul (hasSubst_of_constantCoeff_zero hD) A B

theorem compose_pow (A B : PowerSeries R) (n : ℕ) (hB : constantCoeff R B = 0) :
    compose (A ^ n) B = compose A B ^ n :=
  MvPowerSeries.subst_pow (hasSubst_of_constantCoeff_zero hB) A n

@[simp] theorem compose_C (r : R) (B : PowerSeries R) (hB : constantCoeff R B = 0) :
    compose (C R r) B = C R r := by
  simpa only [MvPowerSeries.substAlgHom_apply, compose] using
    (MvPowerSeries.substAlgHom (R := R)
      (hasSubst_of_constantCoeff_zero hB)).commutes r

theorem compose_assoc (A B D : PowerSeries R)
    (hB : constantCoeff R B = 0) (hD : constantCoeff R D = 0) :
    compose (compose A B) D = compose A (compose B D) :=
  MvPowerSeries.subst_comp_subst_apply
    (hasSubst_of_constantCoeff_zero hB) (hasSubst_of_constantCoeff_zero hD) A

theorem coeff_pow_eq_zero {B : PowerSeries R} (hB : constantCoeff R B = 0)
    {n k : ℕ} (hnk : n < k) : coeff R n (B ^ k) = 0 :=
  (X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hB) k)) n hnk

theorem coeff_compose (A B : PowerSeries R) (hB : constantCoeff R B = 0) (n : ℕ) :
    coeff R n (compose A B) =
      ∑ k ∈ Finset.range (n + 1), coeff R k A * coeff R n (B ^ k) := by
  classical
  change MvPowerSeries.coeff R (Finsupp.single () n)
    (MvPowerSeries.subst (fun (_ : Unit) => B) A) = _
  rw [MvPowerSeries.coeff_subst (hasSubst_of_constantCoeff_zero hB)]
  calc
    _ = ∑ᶠ k : ℕ, coeff R k A * coeff R n (B ^ k) := by
      apply finsum_eq_of_bijective (fun d : Unit →₀ ℕ => d ())
      · constructor
        · intro a b hab
          exact Finsupp.unique_ext hab
        · intro k
          exact ⟨Finsupp.single () k, by simp⟩
      · intro d
        rw [Finsupp.unique_single d]
        simp [PowerSeries.coeff, Finsupp.prod_single_index]
    _ = _ := by
      apply finsum_eq_sum_of_support_subset
      intro k hk
      apply Finset.mem_range.mpr
      apply Classical.byContradiction
      intro h
      have hnk : n < k := Nat.lt_of_succ_le (Nat.le_of_not_gt h)
      exact hk (by simp [coeff_pow_eq_zero hB hnk])

@[simp] theorem constantCoeff_compose (A B : PowerSeries R)
    (hB : constantCoeff R B = 0) :
    constantCoeff R (compose A B) = constantCoeff R A := by
  simpa [coeff_zero_eq_constantCoeff_apply] using coeff_compose A B hB 0

theorem coeff_one_compose (A B : PowerSeries R) (hB : constantCoeff R B = 0) :
    coeff R 1 (compose A B) = coeff R 1 A * coeff R 1 B := by
  rw [coeff_compose A B hB]
  simp [Finset.sum_range_succ]

theorem Normalized.compose {A B : PowerSeries R} (hA : Normalized A)
    (hB : Normalized B) : Normalized (compose A B) := by
  constructor
  · rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_compose A B hB.constantCoeff]
    exact hA.constantCoeff
  · rw [coeff_one_compose A B hB.constantCoeff, hA.2, hB.2, one_mul]

variable {S : Type*} [CommRing S]

theorem constantCoeff_map (f : R →+* S) (A : PowerSeries R) :
    constantCoeff S (PowerSeries.map f A) = f (constantCoeff R A) := by
  simpa only [coeff_zero_eq_constantCoeff_apply] using PowerSeries.coeff_map f 0 A

theorem map_compose (f : R →+* S) (A B : PowerSeries R)
    (hB : constantCoeff R B = 0) :
    PowerSeries.map f (compose A B) =
      compose (PowerSeries.map f A) (PowerSeries.map f B) := by
  have hmap : constantCoeff S (PowerSeries.map f B) = 0 := by
    rw [constantCoeff_map, hB, map_zero]
  ext n
  rw [PowerSeries.coeff_map, coeff_compose A B hB,
    coeff_compose _ _ hmap, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_mul, PowerSeries.coeff_map, ← map_pow, PowerSeries.coeff_map]

theorem Normalized.map {A : PowerSeries R} (hA : Normalized A) (f : R →+* S) :
    Normalized (PowerSeries.map f A) := by
  constructor
  · rw [PowerSeries.coeff_map, hA.1, map_zero]
  · rw [PowerSeries.coeff_map, hA.2, map_one]

theorem map_T (f : R →+* S) (m : R) (A : PowerSeries R) :
    PowerSeries.map f (T m A) = T (f m) (PowerSeries.map f A) := by
  simp only [T, map_sub, map_mul, map_pow, PowerSeries.map_X, PowerSeries.map_C]

theorem map_Psi (f : R →+* S) (m : R) (A : PowerSeries R) :
    PowerSeries.map f (Psi m A) = Psi (f m) (PowerSeries.map f A) := by
  rw [Psi, map_compose f A (T m A) (constantCoeff_T m A), map_T, Psi]

end Hanna.Series
