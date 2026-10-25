module

public import Hanna.Series.Inverse
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

/-!
# Coefficient reduction from modulus four to modulus two

Elementary exact arithmetic and power-series transport shared by several
families. AI-generated for Dev D. Goyal.
-/

@[expose] public section

namespace Families.ModFour

open PowerSeries Hanna.Series

def reduce : ZMod 4 →+* ZMod 2 := ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)

theorem double_eq_iff (u v : ZMod 4) :
    2*u=2*v ↔ reduce u=reduce v := by
  exact (by decide : ∀ u v : ZMod 4, 2*u=2*v ↔ reduce u=reduce v) u v

theorem double_eq_of_mod_two (u v : ZMod 4) (h : reduce u=reduce v) :
    2*u=2*v := (double_eq_iff u v).2 h

theorem series_double_eq_iff (U V : PowerSeries (ZMod 4)) :
    2*U=2*V ↔ PowerSeries.map reduce U=PowerSeries.map reduce V := by
  constructor
  · intro h
    ext n
    have hc := congrArg (coeff (R := (ZMod 4)) n) h
    simp only [two_mul, map_add] at hc
    simpa only [coeff_map] using (double_eq_iff (coeff (R := (ZMod 4)) n U)
      (coeff (R := (ZMod 4)) n V)).1 (by simpa only [two_mul] using hc)
  · intro h
    ext n
    have hc := congrArg (coeff (R := (ZMod 2)) n) h
    simp only [coeff_map] at hc
    simpa only [two_mul, map_add] using
      double_eq_of_mod_two (coeff (R := (ZMod 4)) n U) (coeff (R := (ZMod 4)) n V) hc

theorem series_double_eq_of_mod_two (U V : PowerSeries (ZMod 4))
    (h : PowerSeries.map reduce U=PowerSeries.map reduce V) : 2*U=2*V :=
  (series_double_eq_iff U V).2 h

theorem reduce_int_map (U : PowerSeries ℤ) :
    PowerSeries.map reduce (PowerSeries.map (Int.castRingHom (ZMod 4)) U)=
      PowerSeries.map (Int.castRingHom (ZMod 2)) U := by
  ext n
  simp

/-- Coefficientwise halving; exactness is asserted only with a proved parity hypothesis. -/
noncomputable def half (U : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk (fun n => coeff (R := ℤ) n U / 2)

theorem two_mul_half (U : PowerSeries ℤ)
    (h : PowerSeries.map (Int.castRingHom (ZMod 2)) U=0) : 2*half U=U := by
  ext n
  have hc := congrArg (coeff (R := (ZMod 2)) n) h
  simp only [coeff_map, Int.coe_castRingHom, map_zero] at hc
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (coeff (R := ℤ) n U) 2).1 hc
  obtain ⟨k,hk⟩ := hd
  simp only [two_mul, map_add, half, coeff_mk]
  omega

theorem half_constantCoeff (U : PowerSeries ℤ) (h : constantCoeff (R := ℤ) U=0) :
    constantCoeff (R := ℤ) (half U)=0 := by
  simpa [half, coeff_zero_eq_constantCoeff] using congrArg (fun z : ℤ => z/2) h

end Families.ModFour
