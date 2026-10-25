module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Int.ModEq

/-!
# Helper lemmas for the Solution modules

Conversions between congruences of integers and equalities in `ZMod n`.
-/

public section

namespace OEISProofs

theorem modEq_iff_cast (a b : ℤ) (c : ℕ) : a ≡ b [ZMOD c] ↔ (a : ZMod c) = (b : ZMod c) :=
  (ZMod.intCast_eq_intCast_iff a b c).symm

theorem dvd_iff_cast (a : ℤ) (c : ℕ) : (c : ℤ) ∣ a ↔ (a : ZMod c) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd a c).symm

theorem modEq_four (a b : ℤ) : a ≡ b [ZMOD 4] ↔ (a : ZMod 4) = (b : ZMod 4) := modEq_iff_cast a b 4
theorem modEq_five (a b : ℤ) : a ≡ b [ZMOD 5] ↔ (a : ZMod 5) = (b : ZMod 5) := modEq_iff_cast a b 5
theorem modEq_eight (a b : ℤ) : a ≡ b [ZMOD 8] ↔ (a : ZMod 8) = (b : ZMod 8) := modEq_iff_cast a b 8
theorem modEq_nine (a b : ℤ) : a ≡ b [ZMOD 9] ↔ (a : ZMod 9) = (b : ZMod 9) := modEq_iff_cast a b 9
theorem modEq_sixteen (a b : ℤ) : a ≡ b [ZMOD 16] ↔ (a : ZMod 16) = (b : ZMod 16) :=
  modEq_iff_cast a b 16

theorem dvd_three (a : ℤ) : (3 : ℤ) ∣ a ↔ (a : ZMod 3) = 0 := dvd_iff_cast a 3
theorem dvd_four (a : ℤ) : (4 : ℤ) ∣ a ↔ (a : ZMod 4) = 0 := dvd_iff_cast a 4
theorem dvd_eight (a : ℤ) : (8 : ℤ) ∣ a ↔ (a : ZMod 8) = 0 := dvd_iff_cast a 8

/-- A residue `2` or `0` modulo `4`, according to a condition `P`, gives the two statements
used in the Challenges. -/
theorem two_or_zero (a : ℤ) {P : Prop} {inst : Decidable P}
    (h : (a : ZMod 4) = if P then 2 else 0) :
    (a ≡ 2 [ZMOD 4] ↔ P) ∧ ((4 : ℤ) ∣ a ↔ ¬P) := by
  rw [modEq_four, dvd_four, h]
  by_cases hP : P <;> simp [hP] <;> decide

end OEISProofs
