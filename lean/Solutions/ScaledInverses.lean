module

public import Solutions.Common
public import Related

/-!
# Solution for the scaled inverses `A(x - x·A(qx)/q) = x`

Each statement of `Challenges.ScaledInverses` is derived from the library
`Hanna.Related.ScaledInverse`, where the equation is written with `compose`,
`argument` and `scaleTail`; these unfold to the expressions used in the Challenge.
-/

public section

namespace OEISProofs.ScaledInverses

open PowerSeries Hanna.Series Hanna.Related.ScaledInverse

theorem source_iff (q : ℤ) (A : PowerSeries ℤ) :
    (coeff 0 A = 0 ∧ coeff 1 A = 1 ∧
      A.subst (X - X * PowerSeries.mk (fun n => q ^ (n - 1) * coeff n A)) = X) ↔
    (Normalized A ∧ SourceEquation q A) :=
  ⟨fun ⟨h0, h1, h⟩ => ⟨⟨h0, h1⟩, h⟩, fun ⟨⟨h0, h1⟩, h⟩ => ⟨h0, h1, h⟩⟩

theorem eq_scaledSolution (q : ℤ) (A : PowerSeries ℤ) (h0 : coeff 0 A = 0) (h1 : coeff 1 A = 1)
    (hA : A.subst (X - X * PowerSeries.mk (fun n => q ^ (n - 1) * coeff n A)) = X) :
    A = scaledSolution q :=
  (Hanna.Related.ScaledInverse.existence_uniqueness q).unique ((source_iff q A).1 ⟨h0, h1, hA⟩)
    ⟨scaledSolution_normalized q, scaledSolution_equation q⟩

theorem existsUnique (q : ℤ) :
    ∃! A : PowerSeries ℤ, coeff 0 A = 0 ∧ coeff 1 A = 1 ∧
      A.subst (X - X * PowerSeries.mk (fun n => q ^ (n - 1) * coeff n A)) = X := by
  obtain ⟨A, hA, huniq⟩ := Hanna.Related.ScaledInverse.existence_uniqueness q
  exact ⟨A, (source_iff q A).2 hA, fun B hB => huniq B ((source_iff q B).1 hB)⟩

theorem coeff_modEq_one (q : ℕ) (A : PowerSeries ℤ) (h0 : coeff 0 A = 0) (h1 : coeff 1 A = 1)
    (hA : A.subst (X - X * PowerSeries.mk (fun n => (q : ℤ) ^ (n - 1) * coeff n A)) = X)
    (n : ℕ) (hn : 1 ≤ n) :
    coeff n A ≡ 1 [ZMOD (q + 1 : ℕ)] := by
  rw [eq_scaledSolution (q : ℤ) A h0 h1 hA]
  have h := integer_mod_parameter_add_one q n hn
  exact (ZMod.intCast_eq_intCast_iff _ _ _).1 (by rw [Int.cast_one]; exact h)

theorem odd_coeff_iff (q : ℤ) (hq : Even q) (A : PowerSeries ℤ) (h0 : coeff 0 A = 0)
    (h1 : coeff 1 A = 1)
    (hA : A.subst (X - X * PowerSeries.mk (fun n => q ^ (n - 1) * coeff n A)) = X)
    (n : ℕ) :
    Odd (coeff n A) ↔ ∃ k : ℕ, n = 2 ^ k := by
  rw [eq_scaledSolution q A h0 h1 hA]
  have hq2 : ((q : ℤ) : ZMod 2) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd q 2).2 (by exact_mod_cast even_iff_two_dvd.mp hq)
  exact integer_coeff_odd_iff q hq2 n

end OEISProofs.ScaledInverses
