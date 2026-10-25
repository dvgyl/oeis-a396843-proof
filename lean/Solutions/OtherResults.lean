module

public import Solutions.Common
public import Families
public import Entries.A394576

/-!
# Solution for the further OEIS results

Each statement of `Challenges.OtherResults` is derived from the libraries
`Families.RationalParity` (A396093), `Families.NestedBinomial` (A392210),
`Families.InverseIterate` (A396102), `Families.ExpCosine` (A380056),
`Families.ExpRecurrence` (A397346) and `Families.GreedyTriple` (A394576).
-/

public section

namespace OEISProofs.OtherResults

open PowerSeries Hanna.Series Families

theorem iterate_eq_iter (U : PowerSeries ℤ) (k : ℕ) :
    (fun G : PowerSeries ℤ => (U.subst G : PowerSeries ℤ))^[k] X = Consecutive.iter U k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih]; rfl

theorem a396093_coeff (B : PowerSeries ℤ) (hB : B * (1 - X) ^ 2 = X) :
    (∀ n : ℕ, Even (coeff n (B.subst (B.subst B))) ↔
        ¬(n % 10 = 1 ∨ n % 10 = 3 ∨ n % 10 = 7 ∨ n % 10 = 9)) ∧
      (∀ n : ℕ, Even (coeff (2 * n) (B.subst (B.subst B)))) ∧
      (∀ n : ℕ, 1 ≤ n → (Even (coeff (2 * n - 1) (B.subst (B.subst B))) ↔
        ∃ k : ℕ, 1 ≤ k ∧ n = 5 * k - 2)) := by
  have hne : ((1 : PowerSeries ℤ) - X) ^ 2 ≠ 0 := by
    apply pow_ne_zero
    intro h
    have := congrArg (coeff 0) h
    simp at this
  have hBeq : B = RationalParity.B :=
    mul_right_cancel₀ hne (hB.trans RationalParity.B_denominator.symm)
  have hA : B.subst (B.subst B) = RationalParity.A := by
    rw [hBeq, RationalParity.A_definition]; rfl
  rw [hA]
  exact ⟨RationalParity.a396093_even_iff, RationalParity.a396093_even_indices,
    RationalParity.a396093_odd_indices_original⟩

theorem a392210_existsUnique :
    ∃! F : PowerSeries ℤ, coeff 0 F = 0 ∧ coeff 1 F = 1 ∧
      F = X + (F.subst (X * PowerSeries.mk (1 : ℕ → ℤ))) ^ 2 := by
  obtain ⟨F, ⟨⟨h0, h1⟩, hF⟩, huniq⟩ := NestedBinomial.existence_uniqueness (R := ℤ)
  exact ⟨F, ⟨h0, h1, hF⟩, fun G ⟨g0, g1, gG⟩ => huniq G ⟨⟨g0, g1⟩, gG⟩⟩

theorem a392210_coeff (F : PowerSeries ℤ) (h0 : coeff 0 F = 0) (h1 : coeff 1 F = 1)
    (hF : F = X + (F.subst (X * PowerSeries.mk (1 : ℕ → ℤ))) ^ 2) (n : ℕ) (hn : 1 < n) :
    Even (coeff (2 * n - 1) F) := by
  rw [NestedBinomial.A_unique (R := ℤ) ⟨h0, h1⟩ hF]
  exact NestedBinomial.a392210_odd_indices n hn

theorem a396102_existsUnique (r : ℕ) (hr : 1 ≤ r) :
    ∃! U : PowerSeries ℤ, coeff 0 U = 0 ∧ coeff 1 U = 1 ∧
      (fun G : PowerSeries ℤ => (U.subst G : PowerSeries ℤ))^[r] X = (1 + X) * (fun G : PowerSeries ℤ => (U.subst G : PowerSeries ℤ))^[r - 1] X := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le' hr
  obtain ⟨U, ⟨⟨h0, h1⟩, hU⟩, huniq⟩ := InverseIterate.F_original_existence_uniqueness (S := ℤ) r
  refine ⟨U, ⟨h0, h1, ?_⟩, fun G ⟨g0, g1, gG⟩ => huniq G ⟨⟨g0, g1⟩, ?_⟩⟩
  · rw [iterate_eq_iter, iterate_eq_iter, Nat.add_sub_cancel]; exact hU
  · rw [iterate_eq_iter, iterate_eq_iter, Nat.add_sub_cancel] at gG; exact gG

theorem a396102_coeff (r : ℕ) (hr : 1 ≤ r) (U : PowerSeries ℤ) (h0 : coeff 0 U = 0)
    (h1 : coeff 1 U = 1)
    (hU : (fun G : PowerSeries ℤ => (U.subst G : PowerSeries ℤ))^[r] X = (1 + X) * (fun G : PowerSeries ℤ => (U.subst G : PowerSeries ℤ))^[r - 1] X) :
    (∀ n : ℕ, 1 ≤ n → coeff n U ≡ 1 [ZMOD r]) ∧
      (∀ k n : ℕ, 1 ≤ n → coeff n ((fun G : PowerSeries ℤ => (U.subst G : PowerSeries ℤ))^[k] X) ≡ (k : ℤ) ^ (n - 1) [ZMOD r]) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le' hr
  rw [iterate_eq_iter, iterate_eq_iter, Nat.add_sub_cancel] at hU
  have hUeq : U = InverseIterate.F (r + 1) :=
    (InverseIterate.F_original_existence_uniqueness (S := ℤ) r).unique ⟨⟨h0, h1⟩, hU⟩
      ⟨InverseIterate.F_normalized (r + 1), InverseIterate.F_original_equation r⟩
  refine ⟨fun n hn => ?_, fun k n hn => ?_⟩
  · rw [hUeq, modEq_iff_cast]
    simpa [InverseIterate.a] using InverseIterate.coefficient_congruence (r + 1) n hn
  · rw [iterate_eq_iter, hUeq, modEq_iff_cast]
    simpa using InverseIterate.iterate_coefficient_congruence (r + 1) k n hn

theorem a380056_existsUnique :
    ∃! A : PowerSeries ℚ, A * rescale (2 : ℚ) (cos ℚ) = exp ℚ - 1 :=
  ExpCosine.a380056_source_existence_uniqueness

theorem a380056_eq (A : PowerSeries ℚ) (hA : A * rescale (2 : ℚ) (cos ℚ) = exp ℚ - 1) :
    A = ExpCosine.A :=
  ExpCosine.a380056_source_existence_uniqueness.unique hA ExpCosine.a380056_source_equation

theorem a380056_integral (A : PowerSeries ℚ) (hA : A * rescale (2 : ℚ) (cos ℚ) = exp ℚ - 1)
    (n : ℕ) :
    ∃ z : ℤ, (z : ℚ) = (n.factorial : ℚ) * coeff n A :=
  ⟨ExpCosine.a n, by rw [a380056_eq A hA, ExpCosine.A_integral_coefficients]⟩

theorem a380056_coeff (A : PowerSeries ℚ) (hA : A * rescale (2 : ℚ) (cos ℚ) = exp ℚ - 1)
    (a : ℕ → ℤ) (ha : ∀ n, (a n : ℚ) = (n.factorial : ℚ) * coeff n A) :
    (∀ n : ℕ, 1 ≤ n → a n ≡ 1 [ZMOD 4]) ∧
      (∀ n : ℕ, a n ≡ 2 * 2 ^ n + 3 * 4 ^ n [ZMOD 5]) ∧
      (∀ n : ℕ, (5 : ℤ) ∣ a n ↔ 4 ∣ n) := by
  have hEq : a = ExpCosine.a := by
    funext n
    have h := ha n
    rw [a380056_eq A hA, ExpCosine.A_integral_coefficients] at h
    exact_mod_cast h
  subst hEq
  refine ⟨fun n hn => ?_, fun n => ?_, ExpCosine.a380056_five_dvd_iff⟩
  · rw [modEq_four]
    simpa using ExpCosine.a380056_mod_four n hn
  · rw [modEq_five]
    simpa using ExpCosine.a380056_mod_five_formula n

theorem a397346_existsUnique :
    ∃! s : ℕ → ℚ, s 0 = 1 ∧ s 1 = 1 ∧ ∀ n : ℕ,
      s (n + 2) = 2 * (n + 2 : ℚ) * s (n + 1) +
        (n + 2 : ℚ) * ∑ i : Fin n,
          (2 * (i.val + 2 : ℚ) ^ 2 - 1) / (i.val + 2 : ℚ) * s (i.val + 2) * s (n - i.val) :=
  ExpRecurrence.source_existence_uniqueness

theorem a397346_coeff (s : ℕ → ℚ) (h0 : s 0 = 1) (h1 : s 1 = 1)
    (hs : ∀ n : ℕ,
      s (n + 2) = 2 * (n + 2 : ℚ) * s (n + 1) +
        (n + 2 : ℚ) * ∑ i : Fin n,
          (2 * (i.val + 2 : ℚ) ^ 2 - 1) / (i.val + 2 : ℚ) * s (i.val + 2) * s (n - i.val)) :
    ∃ z : ℕ → ℤ, (∀ n, s n = (z n : ℚ)) ∧ (∀ n : ℕ, 0 < n → (n : ℤ) ∣ z n) ∧
      (∀ n : ℕ, 2 ≤ n → z n / n ≡ (if n % 4 = 3 then 6 else 2) [ZMOD 8]) ∧
      (∀ k : ℕ, z (4 * k + 2) ≡ 4 [ZMOD 8] ∧ z (4 * k + 3) ≡ 2 [ZMOD 8] ∧
        z (4 * k + 4) ≡ 0 [ZMOD 8] ∧ z (4 * k + 5) ≡ 2 [ZMOD 8]) := by
  have hs' : s = fun n => (ExpRecurrence.a n : ℚ) :=
    ExpRecurrence.source_unique ⟨h0, h1, hs⟩ ExpRecurrence.a_source
  have ha : ∀ n : ℕ, 0 < n → ExpRecurrence.a n = n * ExpRecurrence.b n := fun n hn => by
    simp [ExpRecurrence.a, Nat.pos_iff_ne_zero.mp hn]
  refine ⟨ExpRecurrence.a, fun n => by rw [hs'], fun n hn => ⟨_, ha n hn⟩,
    fun n hn => ?_, fun k => ?_⟩
  · rw [ha n (by omega), Int.mul_ediv_cancel_left _ (by exact_mod_cast (by omega : n ≠ 0)),
      modEq_eight, ExpRecurrence.b_mod_eight n hn]
    split_ifs <;> rfl
  · obtain ⟨e2, e3, e4, e5⟩ := ExpRecurrence.a397346_block k
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [modEq_eight]
    · rw [e2]; rfl
    · rw [e3]; rfl
    · rw [e4]; rfl
    · rw [e5]; rfl

theorem a397346_derivative (s : ℕ → ℚ) (h0 : s 0 = 1) (h1 : s 1 = 1)
    (hs : ∀ n : ℕ,
      s (n + 2) = 2 * (n + 2 : ℚ) * s (n + 1) +
        (n + 2 : ℚ) * ∑ i : Fin n,
          (2 * (i.val + 2 : ℚ) ^ 2 - 1) / (i.val + 2 : ℚ) * s (i.val + 2) * s (n - i.val)) :
    derivative (PowerSeries.mk s) =
      PowerSeries.mk s * derivative (PowerSeries.mk fun n =>
        if n = 0 then 0 else if n = 1 then 1 else (2 * (n : ℚ) ^ 2 - 1) / (2 * (n : ℚ) ^ 2) * s n) := by
  have hs' : s = fun n => (ExpRecurrence.a n : ℚ) :=
    ExpRecurrence.source_unique ⟨h0, h1, hs⟩ ExpRecurrence.a_source
  subst hs'
  exact ExpRecurrence.a_differential_equation

theorem a394576_existsUnique :
    ∃! f : ℕ → ℕ, f 0 = 1 ∧ ∀ n,
      f n < f (n + 1) ∧
      (∀ k, 1 ≤ k → k + 1 ≤ n → f (n + 1) ≠ f (k - 1) + f k + f (k + 1)) ∧
      ∀ t, f n < t → (∀ k, 1 ≤ k → k + 1 ≤ n → t ≠ f (k - 1) + f k + f (k + 1)) →
        f (n + 1) ≤ t :=
  GreedyTriple.existence_uniqueness

theorem a394576_bounds (f : ℕ → ℕ)
    (hf : f 0 = 1 ∧ ∀ n,
      f n < f (n + 1) ∧
      (∀ k, 1 ≤ k → k + 1 ≤ n → f (n + 1) ≠ f (k - 1) + f k + f (k + 1)) ∧
      ∀ t, f n < t → (∀ k, 1 ≤ k → k + 1 ≤ n → t ≠ f (k - 1) + f k + f (k + 1)) →
        f (n + 1) ≤ t) :
    (∀ n : ℕ, 1 ≤ n → (4 * n - 3) / 3 ≤ f (n - 1) ∧ f (n - 1) ≤ (4 * n - 1) / 3) ∧
      (∀ k : ℕ, 1 ≤ k → f (3 * k - 1) = 4 * k - 1) ∧
      (∀ t : ℕ, 0 < t → ((∃ n, f n = t) ↔
        ¬∃ k, 1 ≤ k ∧ f (k - 1) + f k + f (k + 1) = t)) := by
  have hfeq : f = GreedyTriple.sequence :=
    GreedyTriple.greedy_unique hf GreedyTriple.greedy_specification
  subst hfeq
  refine ⟨fun n hn => ?_, fun k hk => ?_, OEIS.A394576.complementary_ranges⟩
  · have h := GreedyTriple.a394576_bounds n hn
    simpa [GreedyTriple.a, Nat.pos_iff_ne_zero.mp hn] using h
  · have h := GreedyTriple.a394576_every_third k hk
    simpa [GreedyTriple.a, show 3 * k ≠ 0 by omega] using h

end OEISProofs.OtherResults
