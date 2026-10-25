module

public import Families.CubicReversion

/-!
AI-generated formalization by ChatGPT (OpenAI) for Dev D. Goyal.

# Exact OEIS endpoints for A389474 and A389475

Both series below are defined over the integers, their source equations and
uniqueness are proved, and the four OEIS conjectures follow for every index.
The cube identities are applications of the characteristic-three Frobenius map.
The stronger square identity modulo nine uses a square-zero inner argument.
-/

@[expose] public section

namespace Families.CubicReversion

open PowerSeries Hanna.Series

noncomputable section

variable {R : Type*} [CommRing R]

theorem compose_natCast (n : ℕ) (B : PowerSeries R)
    (hB : constantCoeff B=0) : compose (n : PowerSeries R) B=n := by
  simpa only [map_natCast] using compose_C (n : R) B hB

/-- The exact functional equation defining A389474. -/
def SourceEquation (A : PowerSeries R) : Prop :=
  compose A (X^2+2*X^3+2*A^2)=3*A^2

theorem source_of_inverse {A B : PowerSeries R} (hA : Normalized A)
    (hB : Normalized B) (hAB : compose A B=X) (hBA : compose B A=X)
    (he : Equation (1 : R) B) : SourceEquation A := by
  have h3X : constantCoeff (3*X^2 : PowerSeries R)=0 := by simp
  have h3A : constantCoeff (3*A^2)=0 := by simp [hA.constantCoeff]
  have h2 : compose (2 : PowerSeries R) A=2 := by simpa using compose_natCast 2 A hA.constantCoeff
  have h3 : compose (3 : PowerSeries R) A=3 := by simpa using compose_natCast 3 A hA.constantCoeff
  have hBAeq : compose B (3*A^2)=X^2+2*X^3+2*A^2 := by
    have h := congrArg (fun F : PowerSeries R => compose F A) he
    change compose (compose B (3*X^2)) A =
      compose (2*X^2+B^2+2*C 1*B^3) A at h
    rw [compose_assoc B _ A h3X hA.constantCoeff] at h
    simp only [compose_add _ _ _ hA.constantCoeff, compose_mul _ _ _ hA.constantCoeff,
      compose_pow _ _ _ hA.constantCoeff, compose_natCast _ _ hA.constantCoeff,
      compose_C _ _ hA.constantCoeff, compose_X_left _ hA.constantCoeff,
      map_one, mul_one, hBA, h2, h3] at h
    linear_combination h
  unfold SourceEquation
  calc
    compose A (X^2+2*X^3+2*A^2)=compose A (compose B (3*A^2)) := by rw [hBAeq]
    _=compose (compose A B) (3*A^2) :=
      (compose_assoc A B _ hB.constantCoeff h3A).symm
    _=3*A^2 := by rw [hAB, compose_X_left _ h3A]

theorem equation_of_inverse_source {A B : PowerSeries R} (hA : Normalized A)
    (hB : Normalized B) (hAB : compose A B=X) (hBA : compose B A=X)
    (he : SourceEquation A) : Equation (1 : R) B := by
  have hV : constantCoeff (X^2+2*X^3+2*A^2)=0 := by simp [hA.constantCoeff]
  have hW : constantCoeff (B^2+2*B^3+2*X^2)=0 := by simp [hB.constantCoeff]
  have h2 : compose (2 : PowerSeries R) B=2 := by simpa using compose_natCast 2 B hB.constantCoeff
  have h3 : compose (3 : PowerSeries R) B=3 := by simpa using compose_natCast 3 B hB.constantCoeff
  have hAW : compose A (B^2+2*B^3+2*X^2)=3*X^2 := by
    have h := congrArg (fun F : PowerSeries R => compose F B) he
    change compose (compose A (X^2+2*X^3+2*A^2)) B=compose (3*A^2) B at h
    rw [compose_assoc A _ B hV hB.constantCoeff] at h
    simpa only [compose_add _ _ _ hB.constantCoeff, compose_mul _ _ _ hB.constantCoeff,
      compose_pow _ _ _ hB.constantCoeff, compose_natCast _ _ hB.constantCoeff,
      compose_X_left _ hB.constantCoeff, hAB, h2, h3] using h
  unfold Equation
  calc
    compose B (3*X^2)=compose B (compose A (B^2+2*B^3+2*X^2)) := by rw [hAW]
    _=compose (compose B A) (B^2+2*B^3+2*X^2) :=
      (compose_assoc B A _ hA.constantCoeff hW).symm
    _=2*X^2+B^2+2*C 1*B^3 := by rw [hBA, compose_X_left _ hW]; simp; ring

/-- The canonical integer series in A389475. -/
def a389475 : PowerSeries ℤ := cubicSolution (-1)

theorem a389475_normalized : Normalized a389475 := cubicSolution_normalized (-1)

theorem a389475_equation :
    compose a389475 (3*X^2)=2*X^2+a389475^2-2*a389475^3 := by
  have h := cubicSolution_equation (-1)
  unfold Equation at h
  unfold a389475
  simpa only [map_neg, map_one, mul_neg, mul_one, neg_mul, ← sub_eq_add_neg] using h

theorem a389475_unique (A : PowerSeries ℤ) (hA : Normalized A)
    (he : compose A (3*X^2)=2*X^2+A^2-2*A^3) : A=a389475 := by
  apply solution_unique (-1) hA a389475_normalized _ (cubicSolution_equation (-1))
  simpa only [Equation, map_neg, map_one, mul_neg, mul_one, neg_mul, ← sub_eq_add_neg] using he

/-- The canonical integer series in A389474, obtained by genuine reversion. -/
def a389474 : PowerSeries ℤ := inverse (cubicSolution 1) (cubicSolution_normalized 1)

theorem a389474_normalized : Normalized a389474 :=
  inverse_normalized _ (cubicSolution_normalized 1)

theorem a389474_equation :
    compose a389474 (X^2+2*X^3+2*a389474^2)=3*a389474^2 :=
  source_of_inverse a389474_normalized (cubicSolution_normalized 1)
    (compose_inverse_left _ _) (compose_inverse_right _ _) (cubicSolution_equation 1)

theorem a389474_unique (A : PowerSeries ℤ) (hA : Normalized A)
    (he : compose A (X^2+2*X^3+2*A^2)=3*A^2) : A=a389474 := by
  let B := inverse A hA
  have hB : Normalized B := inverse_normalized A hA
  have hAB : compose A B=X := compose_inverse_right A hA
  have hBA : compose B A=X := compose_inverse_left A hA
  have hBe : Equation (1 : ℤ) B := equation_of_inverse_source hA hB hAB hBA he
  have hBcanonical : B=cubicSolution 1 :=
    solution_unique 1 hB (cubicSolution_normalized 1) hBe (cubicSolution_equation 1)
  apply inverse_unique (cubicSolution_normalized 1) a389474_normalized
  · rw [← hBcanonical]; exact hAB
  · exact compose_inverse_right _ _

/-- Existence and uniqueness for A389474's literal original source equation. -/
theorem a389474_existence_uniqueness :
    ∃! A : PowerSeries ℤ, Normalized A ∧
      compose A (X^2+2*X^3+2*A^2)=3*A^2 := by
  exact ⟨a389474, ⟨a389474_normalized, a389474_equation⟩,
    fun A hA => a389474_unique A hA.1 hA.2⟩

/-- Existence and uniqueness for A389475's literal original source equation. -/
theorem a389475_existence_uniqueness :
    ∃! A : PowerSeries ℤ, Normalized A ∧
      compose A (3*X^2)=2*X^2+A^2-2*A^3 := by
  exact ⟨a389475, ⟨a389475_normalized, a389475_equation⟩,
    fun A hA => a389475_unique A hA.1 hA.2⟩

/-- Evaluating a normalized series at a square-zero series returns the argument. -/
theorem compose_square_zero (A B : PowerSeries R) (hA : Normalized A)
    (hB : constantCoeff B=0) (hsq : B^2=0) : compose A B=B := by
  obtain ⟨D,rfl⟩ := hA.decompose
  rw [compose_add _ _ _ hB, compose_mul _ _ _ hB, compose_pow _ _ _ hB,
    compose_X_left _ hB, hsq, zero_mul, add_zero]

theorem map_sourceEquation {S : Type*} [CommRing S] (f : R →+* S)
    (A : PowerSeries R) (hA : Normalized A) (he : SourceEquation A) :
    SourceEquation (PowerSeries.map f A) := by
  have hz : constantCoeff (X^2+2*X^3+2*A^2)=0 := by simp [hA.constantCoeff]
  have h := congrArg (PowerSeries.map f) he
  change PowerSeries.map f (compose A (X^2+2*X^3+2*A^2))=PowerSeries.map f (3*A^2) at h
  simpa only [SourceEquation, map_compose f A _ hz, map_add, map_mul, map_pow,
    map_ofNat, PowerSeries.map_X] using h

/-- The square-zero argument proves a full identity over Z/9Z. -/
theorem source_square_mod_nine (A : PowerSeries (ZMod 9)) (hA : Normalized A)
    (he : SourceEquation A) : A^2=X^2+2*X^3 := by
  have hV : constantCoeff (R := (ZMod 9)) (X^2+2*X^3+2*A^2)=0 := by simp [hA.constantCoeff]
  have h3A : constantCoeff (R := (ZMod 9)) (3*A^2)=0 := by simp [hA.constantCoeff]
  have hthree : (3 : PowerSeries (ZMod 9))^2=0 := by
    have h : (3 : ZMod 9)^2=0 := by decide
    simpa only [map_pow, map_ofNat, map_zero] using congrArg (C (R := (ZMod 9))) h
  have hnil : (3*A^2)^2=0 := by rw [mul_pow, hthree, zero_mul]
  have h := congrArg (compose (inverse A hA)) he
  change compose (inverse A hA) (compose A (X^2+2*X^3+2*A^2))=
    compose (inverse A hA) (3*A^2) at h
  rw [← compose_assoc _ _ _ hA.constantCoeff hV, compose_inverse_left,
    compose_X_left _ hV,
    compose_square_zero _ _ (inverse_normalized A hA) h3A hnil] at h
  linear_combination -h

/-- Stronger than A389474's first conjecture: the entire square modulo nine. -/
theorem a389474_square_mod_nine :
    PowerSeries.map (Int.castRingHom (ZMod 9)) (a389474^2)=X^2+2*X^3 := by
  rw [map_pow]
  apply source_square_mod_nine _ (a389474_normalized.map _)
  exact map_sourceEquation _ a389474 a389474_normalized a389474_equation

/-- A389474 conjecture (3), at every n greater than three. -/
theorem a389474_conjecture_3 (n : ℕ) (hn : 3<n) :
    ((coeff (R := ℤ) n (a389474^2) : ℤ) : ZMod 9)=0 := by
  have h := congrArg (coeff (R := (ZMod 9)) n) a389474_square_mod_nine
  rw [coeff_map] at h
  simpa only [Int.coe_castRingHom, two_mul, map_add, coeff_X_pow,
    if_neg (show n≠2 by omega), if_neg (show n≠3 by omega), zero_add] using h

/-- Integer power-series Frobenius, including every coefficient and every power. -/
theorem integer_cube_power (A : PowerSeries ℤ) (k : ℕ) :
    PowerSeries.map (Int.castRingHom (ZMod 3)) (A^(3*k))=
      PowerSeries.map (Int.castRingHom (ZMod 3)) ((compose A (X^3))^k) := by
  have hz : constantCoeff (R := ℤ) (X^3 : PowerSeries ℤ)=0 := by simp
  simp only [map_pow, pow_mul, map_compose _ A _ hz, PowerSeries.map_X]
  rw [cube_substitution (PowerSeries.map (Int.castRingHom (ZMod 3)) A)]

/-- A389474 conjecture (4), strengthened to allow n=0 and k=0. -/
theorem a389474_conjecture_4 (n k : ℕ) :
    ((coeff (R := ℤ) n (a389474^(3*k)-(compose a389474 (X^3))^k) : ℤ) : ZMod 3)=0 := by
  have h := congrArg (coeff (R := (ZMod 3)) n) (integer_cube_power a389474 k)
  simp only [coeff_map, Int.coe_castRingHom] at h
  simpa only [map_sub, Int.cast_sub, sub_eq_zero] using h

/-- A389475 conjecture (4a), as an equality of whole series modulo three. -/
theorem a389475_cube_mod_three :
    PowerSeries.map (Int.castRingHom (ZMod 3)) (a389475^3)=
      PowerSeries.map (Int.castRingHom (ZMod 3)) (compose a389475 (X^3)) := by
  simpa only [mul_one, pow_one] using integer_cube_power a389475 1

/-- A389475 conjecture (4b), as an equality of whole series modulo three. -/
theorem a389475_square_mod_three :
    PowerSeries.map (Int.castRingHom (ZMod 3)) (a389475^2)=
      X^2+2*PowerSeries.map (Int.castRingHom (ZMod 3)) (compose a389475 (X^3)) := by
  let f := Int.castRingHom (ZMod 3)
  let A := PowerSeries.map f a389475
  have hA : Normalized A := a389475_normalized.map f
  have he : residual (-1 : ZMod 3) A=0 := by
    have h := congrArg (PowerSeries.map f)
      ((equation_iff_residual (-1) a389475).mp (cubicSolution_equation (-1)))
    simpa only [map_residual, map_neg, map_one, map_zero] using h
  have hthree : (3 : PowerSeries (ZMod 3))=0 := by
    have h : (3 : ZMod 3)=0 := by decide
    simpa only [map_ofNat, map_zero] using congrArg (C (R := (ZMod 3))) h
  have hzero : compose A (0 : PowerSeries (ZMod 3))=0 :=
    compose_square_zero A 0 hA (by simp) (by simp)
  have hchar : (3 : PowerSeries (ZMod 3))*X^2=0 := by rw [hthree, zero_mul]
  simp only [residual, map_neg, map_one, mul_neg, mul_one, neg_mul,
    hthree, zero_mul, hzero, sub_zero] at he
  have hresult : A^2=X^2+2*A^3 := by linear_combination he-hchar
  rw [map_pow]
  change A^2=X^2+2*PowerSeries.map f (compose a389475 (X^3))
  rw [← a389475_cube_mod_three, map_pow]
  exact hresult

/-- Coefficient form of A389475 conjecture (4a), at every index. -/
theorem a389475_conjecture_4a (n : ℕ) :
    ((coeff (R := ℤ) n (a389475^3-compose a389475 (X^3)) : ℤ) : ZMod 3)=0 := by
  have h := congrArg (coeff (R := (ZMod 3)) n) a389475_cube_mod_three
  simp only [coeff_map, Int.coe_castRingHom] at h
  simpa only [map_sub, Int.cast_sub, sub_eq_zero] using h

/-- Coefficient form of A389475 conjecture (4b), at every index. -/
theorem a389475_conjecture_4b (n : ℕ) :
    ((coeff (R := ℤ) n (a389475^2-X^2-2*compose a389475 (X^3)) : ℤ) : ZMod 3)=0 := by
  have hz : PowerSeries.map (Int.castRingHom (ZMod 3))
      (a389475^2-X^2-2*compose a389475 (X^3))=0 := by
    simp only [map_sub, map_pow, map_mul, map_ofNat, PowerSeries.map_X]
    have h := a389475_square_mod_three
    simp only [map_pow] at h
    linear_combination h
  have h := congrArg (coeff (R := (ZMod 3)) n) hz
  simpa only [coeff_map, Int.coe_castRingHom, map_zero] using h

end
end Families.CubicReversion
