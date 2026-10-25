module

public import Solutions.Common
public import Consecutive

/-!
# Solution for the consecutive iterates `F = x + F^{∘r}·F^{∘(r+1)}`

Each statement of `Challenges.ConsecutiveIterates` is derived from the library
`Consecutive`, where the iterates are `Consecutive.iter F k` (equal to the iterates
`(fun G : PowerSeries ℤ => (F.subst G : PowerSeries ℤ))^[k] X` of the Challenge) and the signed iterates are
`Consecutive.ziter`.
-/

public section

namespace OEISProofs.ConsecutiveIterates

open PowerSeries Hanna.Series Consecutive

theorem iterate_eq_iter (F : PowerSeries ℤ) (k : ℕ) :
    (fun G : PowerSeries ℤ => (F.subst G : PowerSeries ℤ))^[k] X = iter F k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih]; rfl

theorem source_iff (r : ℕ) (F : PowerSeries ℤ) :
    (coeff 0 F = 0 ∧ coeff 1 F = 1 ∧
      F = X + (fun G : PowerSeries ℤ => (F.subst G : PowerSeries ℤ))^[r] X * (fun G : PowerSeries ℤ => (F.subst G : PowerSeries ℤ))^[r + 1] X) ↔
    (Normalized F ∧ F = step r F) := by
  rw [iterate_eq_iter, iterate_eq_iter]
  exact ⟨fun ⟨h0, h1, h⟩ => ⟨⟨h0, h1⟩, h⟩, fun ⟨⟨h0, h1⟩, h⟩ => ⟨h0, h1, h⟩⟩

theorem eq_solution (r : ℕ) (F : PowerSeries ℤ) (h0 : coeff 0 F = 0) (h1 : coeff 1 F = 1)
    (hF : F = X + (fun G : PowerSeries ℤ => (F.subst G : PowerSeries ℤ))^[r] X * (fun G : PowerSeries ℤ => (F.subst G : PowerSeries ℤ))^[r + 1] X) :
    F = Consecutive.solution r :=
  (Consecutive.existence_uniqueness r).unique ((source_iff r F).1 ⟨h0, h1, hF⟩)
    ⟨Consecutive.solution_normalized r, Consecutive.solution_equation r⟩

theorem existsUnique (r : ℕ) :
    ∃! F : PowerSeries ℤ, coeff 0 F = 0 ∧ coeff 1 F = 1 ∧
      F = X + (fun G : PowerSeries ℤ => (F.subst G : PowerSeries ℤ))^[r] X * (fun G : PowerSeries ℤ => (F.subst G : PowerSeries ℤ))^[r + 1] X := by
  obtain ⟨F, hF, huniq⟩ := Consecutive.existence_uniqueness (R := ℤ) r
  exact ⟨F, (source_iff r F).2 hF, fun G hG => huniq G ((source_iff r G).1 hG)⟩

theorem modEq_of_integerIterateCoeff (r : ℕ) (hr : 0 < r) (k : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    integerIterateCoeff r k n ≡
      k ^ (n - 1) +
        (if Even r ∧ Odd k then (r : ℤ) * (if 4 ≤ n then ((n - 2).choose 2 : ℤ) else 0)
          else 0) [ZMOD (2 * r : ℕ)] := by
  apply (ZMod.intCast_eq_intCast_iff _ _ _).1
  rw [integerIterateCoeff_mod r hr k n hn]
  push_cast
  rfl

theorem iterate_coeff_modEq (r : ℕ) (hr : 0 < r) (F : PowerSeries ℤ) (h0 : coeff 0 F = 0)
    (h1 : coeff 1 F = 1)
    (hF : F = X + (fun G : PowerSeries ℤ => (F.subst G : PowerSeries ℤ))^[r] X * (fun G : PowerSeries ℤ => (F.subst G : PowerSeries ℤ))^[r + 1] X)
    (k n : ℕ) (hn : 1 ≤ n) :
    coeff n ((fun G : PowerSeries ℤ => (F.subst G : PowerSeries ℤ))^[k] X) ≡
      (k : ℤ) ^ (n - 1) +
        (if Even r ∧ Odd k then (r : ℤ) * (if 4 ≤ n then ((n - 2).choose 2 : ℤ) else 0)
          else 0) [ZMOD (2 * r : ℕ)] := by
  rw [iterate_eq_iter, eq_solution r F h0 h1 hF]
  have h := modEq_of_integerIterateCoeff r hr (k : ℤ) n hn
  simpa only [integerIterateCoeff, ziter_nat, Int.odd_coe_nat] using h

theorem inverse_iterate_coeff_modEq (r : ℕ) (hr : 0 < r) (F : PowerSeries ℤ)
    (h0 : coeff 0 F = 0) (h1 : coeff 1 F = 1)
    (hF : F = X + (fun G : PowerSeries ℤ => (F.subst G : PowerSeries ℤ))^[r] X * (fun G : PowerSeries ℤ => (F.subst G : PowerSeries ℤ))^[r + 1] X)
    (G : PowerSeries ℤ) (hG : G.subst F = X) (k n : ℕ) (hn : 1 ≤ n) :
    coeff n ((fun H : PowerSeries ℤ => (G.subst H : PowerSeries ℤ))^[k] X) ≡
      (-(k : ℤ)) ^ (n - 1) +
        (if Even r ∧ Odd k then (r : ℤ) * (if 4 ≤ n then ((n - 2).choose 2 : ℤ) else 0)
          else 0) [ZMOD (2 * r : ℕ)] := by
  have hFs := eq_solution r F h0 h1 hF
  have hGF : compose G (Consecutive.solution r) = X := by rw [← hFs]; exact hG
  have hGinv : G = inverse (Consecutive.solution r) (Consecutive.solution_normalized r) :=
    inverse_unique (Consecutive.solution_normalized r) (inverse_normalized _ _) hGF
      (compose_inverse_right _ _)
  rw [iterate_eq_iter, hGinv]
  have h := modEq_of_integerIterateCoeff r hr (-(k : ℤ)) n hn
  simpa only [integerIterateCoeff, ziter_neg_nat, odd_neg, Int.odd_coe_nat] using h

theorem a396099_conjectures (F : PowerSeries ℤ) (h0 : coeff 0 F = 0) (h1 : coeff 1 F = 1)
    (hF : F = X + F.subst F * F.subst (F.subst F)) :
    (∀ n : ℕ, 0 < n → Odd (coeff n F)) ∧
      (∀ n : ℕ, 3 ≤ n → coeff n F ≡ (if n % 4 = 0 ∨ n % 4 = 1 then 3 else 1) [ZMOD 4]) ∧
      (∀ n : ℕ, 2 < n → coeff n (F.subst F) ≡ 0 [ZMOD 4]) ∧
      (∀ n : ℕ, 2 < n → coeff n (F - X * F.subst (F.subst F)) ≡ 2 [ZMOD 4]) := by
  obtain ⟨hodd, hres, hsecond, hdiff⟩ := a396099_all_four (F := F) ⟨h0, h1⟩ hF
  refine ⟨hodd, fun n hn => ?_, fun n hn => ?_, fun n hn => ?_⟩
  · rw [modEq_four]
    exact (hres n hn).trans (by split_ifs <;> rfl)
  · rw [modEq_four, Int.cast_zero]
    exact hsecond n hn
  · rw [modEq_four]
    exact (hdiff n hn).trans (by norm_num)

theorem a396798_residues (F : PowerSeries ℤ) (h0 : coeff 0 F = 0) (h1 : coeff 1 F = 1)
    (hF : F = X + (fun G : PowerSeries ℤ => (F.subst G : PowerSeries ℤ))^[4] X * (fun G : PowerSeries ℤ => (F.subst G : PowerSeries ℤ))^[5] X)
    (n : ℕ) (hn : 2 ≤ n) :
    coeff n F ≡ (if n % 4 = 0 ∨ n % 4 = 1 then 5 else 1) [ZMOD 8] := by
  rw [eq_solution 4 F h0 h1 hF]
  rw [modEq_eight]
  have h := a396798_corrected_residue n hn
  simp only [a] at h
  rw [h]
  split_ifs <;> rfl

end OEISProofs.ConsecutiveIterates
