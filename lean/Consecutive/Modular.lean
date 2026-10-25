module

public import Consecutive.Construction
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# Rational representatives for consecutive-iterate equations

All identities in this file are identities of formal power series.  The
nilpotent calculations are certified ring identities, not finite coefficient
tests.  In particular they are valid over rings with zero divisors.
-/

@[expose] public section

namespace Consecutive

open PowerSeries Hanna.Series

noncomputable section

variable {R : Type*} [CommRing R]

/-- The geometric series `1 / (1 - a X)`, defined coefficientwise. -/
def geom (a : R) : PowerSeries R := PowerSeries.mk (fun n => a ^ n)

/-- The formal fractional-linear series `X / (1 - a X)`. -/
def mobius (a : R) : PowerSeries R := X * geom a

/-- The correction term `X^4 / (1-X)^3`. -/
def correction : PowerSeries R := X ^ 4 * geom (1 : R) ^ 3

/-- The representative used for the even parameter. -/
def candidate (c : R) : PowerSeries R := mobius 1 + C c * correction

@[simp] theorem coeff_geom (a : R) (n : ℕ) : coeff n (geom a) = a ^ n :=
  coeff_mk _ _

@[simp] theorem constantCoeff_geom (a : R) : constantCoeff (geom a) = 1 := by
  simp [geom]

@[simp] theorem constantCoeff_mobius (a : R) : constantCoeff (mobius a) = 0 := by
  simp [mobius]

@[simp] theorem constantCoeff_correction : constantCoeff (correction : PowerSeries R) = 0 := by
  simp [correction]

@[simp] theorem constantCoeff_candidate (c : R) : constantCoeff (candidate c) = 0 := by
  simp [candidate]

theorem geom_inverse (a : R) : (1 - C a * X) * geom a = 1 := by
  ext n
  cases n with
  | zero => simp
  | succ n => simp [sub_mul, mul_assoc, pow_succ]; ring

theorem geom_one : geom (1 : R) = PowerSeries.mk 1 := by
  ext n
  simp [geom]

theorem mobius_normalized (a : R) : Normalized (mobius a) := by
  constructor
  · simp [mobius]
  · simp [mobius]

theorem candidate_normalized (c : R) : Normalized (candidate c) := by
  constructor
  · simp [candidate]
  · simp [candidate, correction, mobius, coeff_X_pow_mul']

@[simp] theorem compose_one (B : PowerSeries R) (hB : constantCoeff B = 0) :
    compose 1 B = 1 := by
  simpa using compose_C (1 : R) B hB

theorem geom_compose_inverse (a : R) (B : PowerSeries R)
    (hB : constantCoeff B = 0) :
    (1 - C a * B) * compose (geom a) B = 1 := by
  have h := congrArg (fun F => compose F B) (geom_inverse a)
  simpa only [compose_mul _ _ _ hB, compose_sub _ _ _ hB,
    compose_one _ hB, compose_C _ _ hB, compose_X_left _ hB] using h

private theorem inverse_unique {T : Type*} [CommRing T] (d u v : T)
    (hu : d * u = 1) (hv : d * v = 1) : u = v := by
  calc
    u = u * (d * v) := by rw [hv, mul_one]
    _ = (d * u) * v := by ring
    _ = v := by rw [hu, one_mul]

theorem mobius_compose (a b : R) :
    compose (mobius a) (mobius b) = mobius (a + b) := by
  let x : PowerSeries R := X
  let A : PowerSeries R := C a
  let B : PowerSeries R := C b
  let u := geom b
  let v := geom (a + b)
  have hu : (1 - B * x) * u = 1 := geom_inverse b
  have hv : (1 - (A + B) * x) * v = 1 := by
    simpa only [map_add] using geom_inverse (a + b)
  have hi : (1 - A * (x * u)) * ((1 - B * x) * v) = 1 := by
    linear_combination v * hv - A * x * v * hu + (1 - v) * hv
  have hs : compose (geom a) (mobius b) = (1 - B * x) * v :=
    inverse_unique _ _ _ (geom_compose_inverse a (mobius b) (constantCoeff_mobius b)) hi
  rw [mobius, compose_mul _ _ _ (constantCoeff_mobius b),
    compose_X_left _ (constantCoeff_mobius b), hs]
  change x * u * ((1 - B * x) * v) = x * v
  linear_combination x * v * hu

theorem iter_mobius (a : R) (k : ℕ) : iter (mobius a) k = mobius ((k : R) * a) := by
  induction k with
  | zero =>
      simp only [iter, Nat.cast_zero, zero_mul]
      ext n
      cases n with
      | zero => simp [mobius, geom, coeff_X]
      | succ n =>
          by_cases hn : n = 0
          · simp [mobius, geom, coeff_X, hn]
          · simp [mobius, geom, coeff_X, hn]
  | succ k ih =>
      rw [iter, ih, mobius_compose]
      apply congrArg (mobius (R:=R))
      push_cast
      ring

/- The following lemmas isolate every use of nilpotence in ordinary ring algebra. -/

private theorem nil_mul_pow {T : Type*} [CommRing T] (c a b : T)
    (hc : c * c = 0) (n : ℕ) : c * (a + c * b) ^ n = c * a ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      calc
        c * ((a + c * b) ^ n * (a + c * b)) =
            (c * (a + c * b) ^ n) * a + (c * c) * (a + c * b) ^ n * b := by ring
        _ = c * a ^ n * a := by rw [ih, hc]; ring
        _ = c * (a ^ n * a) := by ring

private theorem rational_comp_self {T : Type*} [CommRing T] (x u q v c : T)
    (hu : (1 - x) * u = 1) (hq : (1 - 2*x) * q = 1)
    (hc : c*c = 0) (h2c : 2*c = 0)
    (hv : (1 - (x*u + c*x^4*u^3)) * v = 1) :
    (x*u + c*x^4*u^3)*v + c*(x*u + c*x^4*u^3)^4*v^3 = x*q := by
  let f := x*u + c*x^4*u^3
  let w := (1-x)*q + c*x^4*u*q^2
  have hw : (1-f)*w = 1 := by
    dsimp [f, w]
    linear_combination
      (-x*q-c*x^4*u*q^2-c*x^4*u^2*q)*hu +
      (1+c*x^4*u^2*q)*hq - x^8*u^4*q^2*hc
  have hvw : v = w := inverse_unique _ _ _ hv hw
  rw [hvw]
  have hprod : f*w = x*u*(1-x)*q +
      c*(x^5*u^2*q^2 + x^4*u^3*(1-x)*q) := by
    dsimp [f, w]
    linear_combination x^8*u^4*q^2*hc
  have hpowf : c*f^4 = c*(x*u)^4 := by
    simpa [f, mul_assoc] using nil_mul_pow c (x*u) (x^4*u^3) hc 4
  have hpoww : c*w^3 = c*((1-x)*q)^3 := by
    have heq : w = (1-x)*q+c*(x^4*u*q^2) := by dsimp [w]; ring
    rw [heq]
    exact nil_mul_pow c ((1-x)*q) (x^4*u*q^2) hc 3
  have hcorr : c*f^4*w^3 = c*x^4*u^4*(1-x)^3*q^3 := by
    calc
      c*f^4*w^3 = (c*f^4)*w^3 := by ring
      _ = (c*(x*u)^4)*w^3 := by rw [hpowf]
      _ = (x*u)^4*(c*w^3) := by ring
      _ = (x*u)^4*(c*((1-x)*q)^3) := by rw [hpoww]
      _ = _ := by ring
  have hbase : x*u*(1-x)*q = x*q := by linear_combination x*q*hu
  have hs1 : x^4*u^3*(1-x)*q = x^4*u^2*q := by
    linear_combination x^4*u^2*q*hu
  have hs2 : x^4*u^4*(1-x)^3*q^3 = x^4*u*q^3 := by
    calc
      _ = x^4*u*q^3*((1-x)*u)^3 := by ring
      _ = _ := by rw [hu]; ring
  have he : x^5*u^2*q^2 + x^4*u^2*q + x^4*u*q^3 = 2*x^4*q^3 := by
    linear_combination
      (2*x^4*q^3+x^4*u*q^2)*hu - (x^4*u*q^2+x^4*u^2*q)*hq
  change f*w + c*f^4*w^3 = x*q
  rw [hprod, hcorr, hbase, hs1]
  rw [show c*x^4*u^4*(1-x)^3*q^3 = c*(x^4*u^4*(1-x)^3*q^3) by ring, hs2]
  calc
    _ = x*q + c*(x^5*u^2*q^2+x^4*u^2*q+x^4*u*q^3) := by ring
    _ = x*q + c*(2*x^4*q^3) := by rw [he]
    _ = x*q := by linear_combination x^4*q^3*h2c

private theorem rational_shift {T : Type*} [CommRing T] (x u v c : T)
    (hu : (1-x)*u = 1) (hc : c*c = 0)
    (hv : (1-(x+c*x^2))*v = 1) :
    (x+c*x^2)*v+c*(x+c*x^2)^4*v^3 =
      x*u+c*x^4*u^3+c*x^2*u^2 := by
  let w := u+c*x^2*u^2
  have hw : (1-(x+c*x^2))*w = 1 := by
    dsimp [w]
    linear_combination (1+c*x^2*u)*hu - x^4*u^2*hc
  have hvw : v = w := inverse_unique _ _ _ hv hw
  rw [hvw]
  have hp := nil_mul_pow c x (x^2) hc 4
  have hw3 : c*w^3 = c*u^3 := by
    simpa [w, mul_assoc] using nil_mul_pow c u (x^2*u^2) hc 3
  have hterm : c*(x+c*x^2)^4*w^3 = c*x^4*u^3 := by
    calc
      _ = (c*(x+c*x^2)^4)*w^3 := by ring
      _ = (c*x^4)*w^3 := by rw [hp]
      _ = x^4*(c*w^3) := by ring
      _ = x^4*(c*u^3) := by rw [hw3]
      _ = _ := by ring
  rw [hterm]
  dsimp [w]
  linear_combination -c*x^2*u*hu + x^4*u^2*hc

private theorem rational_fixedpoint {T : Type*} [CommRing T] (x u c : T)
    (hu : (1-x)*u = 1) (hc : c*c = 0) (h2c : 2*c = 0) :
    x*u+c*x^4*u^3 =
      x+(x+c*x^2)*(x*u+c*x^4*u^3+c*x^2*u^2) := by
  linear_combination
    (x+c*x^3*u*(x*u-1))*hu - x^3*u*h2c -
      (x^6*u^3+x^4*u^2)*hc

theorem candidate_comp_self (c : R) (hc : c*c = 0) (h2c : 2*c = 0) :
    compose (candidate c) (candidate c) = mobius 2 := by
  have hcc : C c * C c = 0 := by rw [← map_mul, hc, map_zero]
  have h2cc : 2 * C c = 0 := by
    simpa only [map_mul, map_ofNat, map_zero] using congrArg (C) h2c
  have hu : (1-X)*geom (1:R) = 1 := by simpa using geom_inverse (1:R)
  have hq : (1-2*X)*geom (2:R) = 1 := by simpa [map_ofNat] using geom_inverse (2:R)
  have hv := geom_compose_inverse (1:R) (candidate c) (constantCoeff_candidate c)
  simp only [map_one, one_mul] at hv
  have hv' : (1-(X*geom 1+C c*X^4*geom 1^3))*
      compose (geom 1) (candidate c) = 1 := by
    simpa only [candidate, correction, mobius, mul_assoc] using hv
  have h := rational_comp_self (X : PowerSeries R) (geom 1) (geom 2)
    (compose (geom 1) (candidate c)) (C c) hu hq hcc h2cc hv'
  change compose (X*geom 1+C c*(X^4*geom 1^3)) (candidate c) = X*geom 2
  simp only [compose_add _ _ _ (constantCoeff_candidate c),
    compose_mul _ _ _ (constantCoeff_candidate c), compose_pow _ _ _ (constantCoeff_candidate c),
    compose_C _ _ (constantCoeff_candidate c), compose_X_left _ (constantCoeff_candidate c)]
  simpa only [candidate, correction, mobius, mul_assoc] using h

theorem candidate_comp_shift (c : R) (hc : c*c = 0) :
    compose (candidate c) (X+C c*X^2) =
      candidate c + C c*X^2*geom (1:R)^2 := by
  have hB : constantCoeff (X+C c*X^2) = 0 := by simp
  have hcc : C c * C c = 0 := by rw [← map_mul, hc, map_zero]
  have hu : (1-X)*geom (1:R) = 1 := by simpa using geom_inverse (1:R)
  have hv := geom_compose_inverse (1:R) (X+C c*X^2) hB
  simp only [map_one, one_mul] at hv
  have h := rational_shift (X : PowerSeries R) (geom 1)
    (compose (geom 1) (X+C c*X^2)) (C c) hu hcc hv
  simpa only [candidate, correction, mobius, compose_add _ _ _ hB,
    compose_mul _ _ _ hB, compose_pow _ _ _ hB,
    compose_C _ _ hB, compose_X_left _ hB, mul_assoc] using h

theorem candidate_equation_shift (c : R) (hc : c*c = 0) (h2c : 2*c = 0) :
    candidate c = X+(X+C c*X^2)*compose (candidate c) (X+C c*X^2) := by
  rw [candidate_comp_shift c hc]
  have hcc : C c * C c = 0 := by rw [← map_mul, hc, map_zero]
  have h2cc : 2 * C c = 0 := by
    simpa only [map_mul, map_ofNat, map_zero] using congrArg (C) h2c
  have hu : (1-X)*geom (1:R) = 1 := by simpa using geom_inverse (1:R)
  simpa only [candidate, correction, mobius, mul_assoc] using
    rational_fixedpoint (X : PowerSeries R) (geom 1) (C c) hu hcc h2cc

theorem mobius_of_square_zero (a : R) (ha : a*a = 0) :
    mobius a = X+C a*X^2 := by
  have hAA : C a*C a = 0 := by rw [← map_mul, ha, map_zero]
  have hi : (1-C a*X)*(1+C a*X) = (1 : PowerSeries R) := by
    linear_combination -(X : PowerSeries R)^2*hAA
  have hg : geom a = 1+C a*X := inverse_unique _ _ _ (geom_inverse a) hi
  rw [mobius, hg]
  ring

theorem iter_candidate_even (c : R) (hc : c*c = 0) (h2c : 2*c = 0) (k : ℕ) :
    iter (candidate c) (2*k) = mobius (2*(k:R)) := by
  have ht : iter (candidate c) 2 = mobius 2 := by
    simpa only [iter_succ, iter_one, iter_zero, compose_X_right] using candidate_comp_self c hc h2c
  rw [iter_mul (candidate_normalized c) 2 k, ht, iter_mobius]
  rw [mul_comm (k:R) 2]

private theorem mul_pow_eq_of_mul_eq {T : Type*} [CommRing T] (c a b : T)
    (h : c*a = c*b) (n : ℕ) : c*a^n = c*b^n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      calc
        c*(a^n*a) = (c*a^n)*a := by ring
        _ = (c*b^n)*a := by rw [ih]
        _ = b^n*(c*a) := by ring
        _ = b^n*(c*b) := by rw [h]
        _ = c*(b^n*b) := by ring

/-- Substitution respects an equality after multiplication by a constant. -/
theorem weighted_compose (c : R) (A B D : PowerSeries R)
    (hB : constantCoeff B = 0) (hD : constantCoeff D = 0)
    (hBD : C c*B = C c*D) :
    C c*compose A B = C c*compose A D := by
  ext n
  rw [coeff_C_mul, coeff_C_mul, coeff_compose A B hB, coeff_compose A D hD,
    Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hp := congrArg (coeff n) (mul_pow_eq_of_mul_eq (C c) B D hBD k)
  simp only [coeff_C_mul] at hp
  linear_combination coeff k A * hp

theorem weighted_mobius (c a : R) (hca : c*a = 0) :
    C c*mobius a = C c*X := by
  have h := geom_inverse a
  have hzero : C c*C a = 0 := by rw [← map_mul, hca, map_zero]
  dsimp [mobius]
  linear_combination C c*X*h + X^2*geom a*hzero

theorem iter_candidate_odd (c : R) (hc : c*c = 0) (h2c : 2*c = 0) (k : ℕ) :
    iter (candidate c) (2*k+1) = mobius (2*(k:R)+1)+C c*correction := by
  have hca : c*(2*(k:R)) = 0 := by linear_combination (k:R)*h2c
  have hw := weighted_compose c correction (mobius (2*(k:R))) X
    (constantCoeff_mobius _) (by simp) (weighted_mobius c _ hca)
  rw [compose_X_right] at hw
  rw [iter_succ, iter_candidate_even c hc h2c]
  change compose (mobius 1+C c*correction) (mobius (2*(k:R))) = _
  rw [compose_add _ _ _ (constantCoeff_mobius _),
    compose_mul _ _ _ (constantCoeff_mobius _),
    compose_C _ _ (constantCoeff_mobius _), mobius_compose, hw]
  rw [add_comm 1 (2*(k:R))]

theorem candidate_fixedpoint_even (r : ℕ) (hr : Even r)
    (hc : (r:R)*(r:R) = 0) (h2c : 2*(r:R) = 0) :
    step r (candidate (r:R)) = candidate (r:R) := by
  have hi : iter (candidate (r:R)) r = X+C (r:R)*X^2 := by
    obtain ⟨k, hk⟩ := even_iff_two_dvd.mp hr
    have h := iter_candidate_even (r:R) hc h2c k
    rw [← hk] at h
    have hcast : 2*(k:R) = (r:R) := by rw [hk]; push_cast; ring
    rw [hcast, mobius_of_square_zero (r:R) hc] at h
    exact h
  rw [step, iter_succ, hi]
  exact (candidate_equation_shift (r:R) hc h2c).symm

theorem mobius_equation_of_params (a b : R) (hs : a+b = 1) (hp : a*b = 0) :
    mobius 1 = X+mobius a*mobius b := by
  have hsC : C a+C b = 1 := by simpa using congrArg (C) hs
  have hpC : C a*C b = 0 := by rw [← map_mul, hp, map_zero]
  have hd : (1-C a*X)*(1-C b*X) = (1 : PowerSeries R)-X := by
    linear_combination -(X : PowerSeries R)*hsC + X^2*hpC
  have hi : (1-X)*(geom a*geom b) = (1 : PowerSeries R) := by
    rw [← hd]
    calc
      _ = ((1-C a*X)*geom a)*((1-C b*X)*geom b) := by ring
      _ = 1 := by rw [geom_inverse a, geom_inverse b]; ring
  have hg : geom (1:R) = geom a*geom b :=
    inverse_unique _ _ _ (by simpa using geom_inverse (1:R)) hi
  have ht : (1-X)*geom (1:R) = 1 := by simpa using geom_inverse (1:R)
  dsimp [mobius]
  calc
    _ = X+X^2*geom (1:R) := by linear_combination (X : PowerSeries R)*ht
    _ = X+X^2*(geom a*geom b) := by rw [hg]
    _ = _ := by ring

theorem mobius_fixedpoint (r : ℕ) (hs : 2*(r:R) = 0)
    (hp : (r:R)*((r:R)+1) = 0) : step r (mobius (1:R)) = mobius 1 := by
  rw [step, iter_mobius, iter_mobius]
  simp only [mul_one, Nat.cast_add, Nat.cast_one]
  symm
  apply mobius_equation_of_params
  · linear_combination hs
  · exact hp

/-- The residual whose coefficients give the fourth A396099 conjecture. -/
theorem candidate_residual (c : R) (hc : c*c = 0) :
    candidate c-X*compose (candidate c) (X+C c*X^2) =
      X-C c*X^3*geom (1:R) := by
  rw [candidate_comp_shift c hc]
  have hu : (1-X)*geom (1:R) = 1 := by simpa using geom_inverse (1:R)
  dsimp [candidate, correction, mobius]
  linear_combination
    (X+C c*X^3*geom (1:R)*(X*geom (1:R)-1))*hu

theorem two_parameter_zero (r : ℕ) : 2*(r : ZMod (2*r)) = 0 := by
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using ZMod.natCast_self (2*r)

theorem even_parameter_square_zero (r : ℕ) (hr : Even r) :
    (r : ZMod (2*r))*(r : ZMod (2*r)) = 0 := by
  rw [← Nat.cast_mul]
  apply (ZMod.natCast_eq_zero_iff (r*r) (2*r)).mpr
  obtain ⟨k, rfl⟩ := even_iff_two_dvd.mp hr
  exact ⟨k, by ring⟩

theorem odd_parameter_product_zero (r : ℕ) (hr : Odd r) :
    (r : ZMod (2*r))*((r : ZMod (2*r))+1) = 0 := by
  have h : ((r*(r+1) : ℕ) : ZMod (2*r)) = 0 := by
    apply (ZMod.natCast_eq_zero_iff (r*(r+1)) (2*r)).mpr
    obtain ⟨k, rfl⟩ := hr.exists_bit1
    exact ⟨k+1, by ring⟩
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using h

theorem solution_mod_even (r : ℕ) (hr : Even r) :
    solution (R:=ZMod (2*r)) r = candidate (r : ZMod (2*r)) := by
  apply Consecutive.solution_unique r (solution_normalized r) (candidate_normalized _)
    (solution_equation r)
  exact (candidate_fixedpoint_even r hr (even_parameter_square_zero r hr)
    (two_parameter_zero r)).symm

theorem solution_mod_odd (r : ℕ) (hr : Odd r) :
    solution (R:=ZMod (2*r)) r = mobius 1 := by
  apply Consecutive.solution_unique r (solution_normalized r) (mobius_normalized _)
    (solution_equation r)
  exact (mobius_fixedpoint r (two_parameter_zero r) (odd_parameter_product_zero r hr)).symm

/-- Complete natural-iterate formula, as an equality of actual series modulo `2*r`. -/
theorem iter_solution_mod (r k : ℕ) :
    iter (solution (R:=ZMod (2*r)) r) k =
      mobius (k : ZMod (2*r)) +
        if Even r ∧ Odd k then C (R := (ZMod (2*r))) (r : ZMod (2*r))*correction else 0 := by
  by_cases hr : Even r
  · rw [solution_mod_even r hr]
    rcases Nat.even_or_odd k with hk | hk
    · obtain ⟨j, rfl⟩ := even_iff_two_dvd.mp hk
      rw [iter_candidate_even _ (even_parameter_square_zero r hr) (two_parameter_zero r)]
      have hnot : ¬Odd (2*j) := by simp
      simp only [hnot, and_false, if_false, add_zero, Nat.cast_mul, Nat.cast_ofNat]
    · obtain ⟨j, rfl⟩ := hk.exists_bit1
      rw [iter_candidate_odd _ (even_parameter_square_zero r hr) (two_parameter_zero r)]
      have hod : Odd (2*j+1) := ⟨j, by omega⟩
      simp only [hr, hod, and_self, if_true, Nat.cast_add, Nat.cast_mul,
        Nat.cast_ofNat, Nat.cast_one]
  · rw [solution_mod_odd r (Nat.not_even_iff_odd.mp hr), iter_mobius]
    simp only [mul_one, hr, false_and, if_false, add_zero]

/-- The same formula explicitly applied to the integer solution by coefficient reduction. -/
theorem map_iter_solution_mod (r k : ℕ) :
    PowerSeries.map (Int.castRingHom (ZMod (2*r)))
      (iter (solution (R:=ℤ) r) k) =
        mobius (k : ZMod (2*r)) +
          if Even r ∧ Odd k then C (R := (ZMod (2*r))) (r : ZMod (2*r))*correction else 0 := by
  rw [map_iter _ (solution_normalized r), map_solution, iter_solution_mod]

@[simp] theorem mobius_zero : mobius (0:R) = X := by
  simpa using (iter_mobius (1:R) 0).symm

theorem coeff_two_iter_solution_mod (r k : ℕ) :
    coeff (R := (ZMod (2*r))) 2 (iter (solution (R:=ZMod (2*r)) r) k) =
      (k : ZMod (2*r)) := by
  rw [iter_solution_mod]
  split_ifs
  · rw [map_add, coeff_C_mul]
    simp [mobius, correction, coeff_X_pow_mul']
  · simp [mobius]

/-- Exact composition order: the identity occurs precisely at multiples of `2*r`. -/
theorem iter_solution_mod_eq_X_iff (r k : ℕ) :
    iter (solution (R:=ZMod (2*r)) r) k = X ↔ 2*r ∣ k := by
  constructor
  · intro h
    have he := congrArg (coeff (R := (ZMod (2*r))) 2) h
    rw [coeff_two_iter_solution_mod] at he
    have hz : (k : ZMod (2*r)) = 0 := by simpa [coeff_X] using he
    exact (ZMod.natCast_eq_zero_iff k (2*r)).mp hz
  · intro h
    have hz : (k : ZMod (2*r)) = 0 :=
      (ZMod.natCast_eq_zero_iff k (2*r)).mpr h
    have hk : Even k := even_iff_two_dvd.mpr ((dvd_mul_right 2 r).trans h)
    have hn : ¬Odd k := Nat.not_odd_iff_even.mpr hk
    rw [iter_solution_mod]
    simp [hz, hn]

theorem iter_solution_mod_period (r : ℕ) :
    iter (solution (R:=ZMod (2*r)) r) (2*r) = X :=
  (iter_solution_mod_eq_X_iff r (2*r)).mpr (dvd_refl _)

end
end Consecutive
