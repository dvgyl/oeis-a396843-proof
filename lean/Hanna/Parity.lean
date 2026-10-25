module

public import Hanna.Canonical
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace Hanna.Parity

open PowerSeries

private abbrev F := ZMod 2
private abbrev U : PowerSeries F := PowerSeries.mk 1
private noncomputable abbrev H : PowerSeries F := X * U

private theorem two_eq_zero : (2 : PowerSeries F) = 0 := by
  change C (2 : F) = 0
  rw [show (2 : F) = 0 by decide]
  simp

private theorem neg_eq_self (V : PowerSeries F) : -V = V := by
  ext n
  simp [ZMod.neg_eq_self_mod_two]

private theorem u_geometric : U * (1 + X) = 1 := by
  simpa [U, sub_eq_add_neg, neg_eq_self] using
    (PowerSeries.mk_one_mul_one_sub_eq_one F)

private theorem h_normalized : Series.Normalized H := by
  constructor
  · simp [H]
  · rw [show (1:ℕ) = 0 + 1 by omega, PowerSeries.coeff_succ_X_mul]
    simp [U]

private theorem h_coeff (n : ℕ) (hn : 1 ≤ n) : coeff n H = 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [H, PowerSeries.coeff_succ_X_mul]
  simp [U]

private theorem t_eq : Series.T (1 : F) H = X ^ 2 * U ^ 2 := by
  have hg := u_geometric
  have htwo : (2 : PowerSeries F) = 0 := two_eq_zero
  change X * (X * U) - C 1 * X * (X * U) ^ 2 = X ^ 2 * U ^ 2
  simp only [map_one, one_mul]
  have h : U + X * U ^ 2 = U ^ 2 := by
    linear_combination U * hg + (U - U ^ 2) * htwo
  calc
    X * (X * U) - X * (X * U) ^ 2 = X ^ 2 * (U + X * U ^ 2) := by
      rw [sub_eq_add_neg, neg_eq_self]
      ring
    _ = X ^ 2 * U ^ 2 := by rw [h]

private theorem one_add_t : (1 : PowerSeries F) + Series.T 1 H = U ^ 2 := by
  rw [t_eq]
  have hg := u_geometric
  have htwo := two_eq_zero
  have hsquare : (1 + (X : PowerSeries F)) ^ 2 = 1 + X ^ 2 := by
    calc
      (1 + (X : PowerSeries F)) ^ 2 = 1 + 2 * X + X ^ 2 := by ring
      _ = 1 + X ^ 2 := by rw [htwo]; ring
  have hu2 : U ^ 2 * (1 + X ^ 2) = 1 := by
    rw [← hsquare, ← mul_pow, hg, one_pow]
  linear_combination -hu2 + X ^ 2 * U ^ 2 * htwo

private theorem h_equation : Series.Psi (1 : F) H = X ^ 2 := by
  let V : PowerSeries F := Series.T 1 H
  have hv : constantCoeff V = 0 := Series.constantCoeff_T 1 H
  have h_one : Series.compose (1 : PowerSeries F) V = 1 := by
    change Series.compose (C 1) V = 1
    rw [Series.compose_C 1 V hv]
    rfl
  have hgeom : Series.compose U V * (1 + V) = 1 := by
    calc
      Series.compose U V * (1 + V) =
          Series.compose (U * (1 + X)) V := by
            rw [Series.compose_mul U (1 + X) V hv]
            congr 1
            rw [Series.compose_add 1 X V hv]
            rw [h_one, Series.compose_X_left V hv]
      _ = 1 := by
        rw [u_geometric]
        exact h_one
  have hh : Series.compose H V * (1 + V) = V := by
    rw [show H = X * U from rfl, Series.compose_mul X U V hv,
      Series.compose_X_left V hv]
    calc
      V * Series.compose U V * (1 + V) = V * (Series.compose U V * (1 + V)) := by ring
      _ = V := by rw [hgeom, mul_one]
  have hx : X ^ 2 * (1 + V) = V := by
    dsimp [V]
    rw [one_add_t, t_eq]
  have hunit : IsUnit (1 + V) := by
    apply isUnit_iff_exists_inv.mpr
    exact ⟨Series.compose U V, by simpa [mul_comm] using hgeom⟩
  unfold Series.Psi
  exact hunit.mul_right_cancel (hh.trans hx.symm)

private theorem A_one : A (1 : F) = H :=
  Series.solution_unique 1 (A_normalized 1) h_normalized (A_equation 1) h_equation

private theorem A_zero : A (0 : F) = X := by
  apply Series.solution_unique 0 (A_normalized 0) Series.normalized_X (A_equation 0)
  change Series.compose X (Series.T 0 X) = X ^ 2
  rw [Series.compose_X_left _ (Series.constantCoeff_T 0 X)]
  simp [Series.T, pow_two]

private theorem odd_cast_one {m : ℤ} (hm : Odd m) : (m : F) = 1 := by
  obtain ⟨k, rfl⟩ := Odd.exists_bit1 hm
  simp [show (2 : F) = 0 by decide]

private theorem even_cast_zero {m : ℤ} (hm : Even m) : (m : F) = 0 := by
  obtain ⟨k, rfl⟩ := hm
  have htwo : (2 : F) = 0 := by decide
  calc
    ((k + k : ℤ) : F) = (2 : F) * (k : F) := by push_cast; ring
    _ = 0 := by rw [htwo, zero_mul]

theorem odd_coeff (m : ℤ) (hm : Odd m) (n : ℕ) (hn : 1 ≤ n) : Odd (a m n) := by
  have hmap := congrArg (coeff n) (map_A (Int.castRingHom F) m)
  have hcast : ((a m n : ℤ) : F) = 1 := by
    simpa [a, odd_cast_one hm, A_one, PowerSeries.coeff_map, h_coeff n hn] using hmap
  by_contra hodd
  have heven : Even (a m n) := Int.not_odd_iff_even.mp hodd
  have hzero : ((a m n : ℤ) : F) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (a m n) 2).mpr
      (even_iff_two_dvd.mp heven)
  exact zero_ne_one (hzero.symm.trans hcast)

theorem even_coeff (m : ℤ) (hm : Even m) :
    a m 1 = 1 ∧ ∀ n ≥ 2, (2 : ℤ) ∣ a m n := by
  constructor
  · exact (A_normalized m).2
  · intro n hn
    have hmap := congrArg (coeff n) (map_A (Int.castRingHom F) m)
    have hcast : ((a m n : ℤ) : F) = 0 := by
      have hnX : coeff n (X : PowerSeries F) = 0 := by
        simp [coeff_X, show n ≠ 1 by omega]
      simpa [a, even_cast_zero hm, A_zero, PowerSeries.coeff_map, hnX] using hmap
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a m n) 2).mp hcast

end Hanna.Parity
