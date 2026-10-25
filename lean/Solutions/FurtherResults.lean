module

public import Solutions.Common
public import Families
public import Entries.A394576

/-!
# Solution for the further OEIS results

Each statement of `Challenges.FurtherResults` is derived from the libraries
`Families.InverseIterate` (A396102), `Families.ExpRecurrence` and `Families.ExpEquation`
(A397346) and `Families.GreedyTriple` (A394576).
-/

public section

namespace OEISProofs.FurtherResults

open PowerSeries Hanna.Series Families

theorem iterate_eq_iter (U : PowerSeries ℤ) (k : ℕ) :
    (fun G : PowerSeries ℤ => (U.subst G : PowerSeries ℤ))^[k] X = Consecutive.iter U k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih]; rfl

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

theorem a397346_exp_iff (s : ℕ → ℚ) (h0 : s 0 = 1) (h1 : s 1 = 1)
    (hs : ∀ n : ℕ,
      s (n + 2) = 2 * (n + 2 : ℚ) * s (n + 1) +
        (n + 2 : ℚ) * ∑ i : Fin n,
          (2 * (i.val + 2 : ℚ) ^ 2 - 1) / (i.val + 2 : ℚ) * s (i.val + 2) * s (n - i.val))
    (A : PowerSeries ℚ) :
    A = ((exp ℚ).subst (PowerSeries.mk fun n =>
        if n = 0 then 0 else if n = 1 then 1 else
          (2 * (n : ℚ) ^ 2 - 1) / (2 * (n : ℚ) ^ 2) * coeff n A) : PowerSeries ℚ) ↔
      A = PowerSeries.mk s := by
  have hs' : s = fun n => (ExpRecurrence.a n : ℚ) :=
    ExpRecurrence.source_unique ⟨h0, h1, hs⟩ ExpRecurrence.a_source
  subst hs'
  exact ExpEquation.equation_iff A

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

end OEISProofs.FurtherResults
