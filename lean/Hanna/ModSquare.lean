import Hanna.Recurrences

namespace Hanna
open PowerSeries

lemma parameter_dvd_fg (m : ℤ) (r : ℕ) (hr : 1 ≤ r) : m ∣ f m r ∧ m ∣ g m r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    have hf : m ∣ f m r := by
      rw [f_recurrence m r hr]
      apply dvd_add
      · split_ifs with he
        · exact (ih (r/2) (Nat.div_lt_self (by omega) (by omega))
            (by obtain ⟨k, hk⟩ := he; omega)).2
        · exact dvd_zero m
      · exact dvd_mul_right m _
    refine ⟨hf, ?_⟩
    rw [g_recurrence m r hr]
    apply dvd_sub (dvd_neg.mpr hf)
    apply Finset.dvd_sum
    intro j hj
    exact dvd_mul_of_dvd_left (ih j (Finset.mem_Ico.mp hj).2 (Finset.mem_Ico.mp hj).1).1 _

lemma parameter_dvd_coeff_G_pow (m : ℤ) (k r : ℕ) (hr : 1 ≤ r) :
    m ∣ coeff ℤ r ((G m)^k) := by
  induction k generalizing r with
  | zero => simp [show r ≠ 0 by omega]
  | succ k ih =>
    rw [pow_succ, coeff_mul]
    apply Finset.dvd_sum
    intro ij hij
    have hij' := Finset.mem_antidiagonal.mp hij
    by_cases hi : 1 ≤ ij.1
    · exact dvd_mul_of_dvd_left (ih ij.1 hi) _
    · have hj : 1 ≤ ij.2 := by omega
      exact dvd_mul_of_dvd_right (parameter_dvd_fg m ij.2 hj).2 _

lemma square_dvd_g_add_f (m : ℤ) (r : ℕ) (hr : 1 ≤ r) :
    m^2 ∣ g m r + f m r := by
  rw [g_recurrence m r hr]
  have heq : -f m r - (∑ j ∈ Finset.Ico 1 r,
      f m j * coeff ℤ (r-j) ((G m)^(j+1))) + f m r =
      -(∑ j ∈ Finset.Ico 1 r, f m j * coeff ℤ (r-j) ((G m)^(j+1))) := by ring
  rw [heq, dvd_neg]
  apply Finset.dvd_sum
  intro j hj
  rw [pow_two]
  exact mul_dvd_mul (parameter_dvd_fg m j (Finset.mem_Ico.mp hj).1).1
    (parameter_dvd_coeff_G_pow m (j+1) (r-j) (by have := (Finset.mem_Ico.mp hj).2; omega))

lemma square_dvd_f_step (m : ℤ) (r : ℕ) (hr : 2 ≤ r) :
    m^2 ∣ f m r - (if Even r then g m (r/2) else 0) := by
  rw [f_recurrence m r (by omega), add_sub_cancel_left, pow_two]
  apply mul_dvd_mul_left
  apply Finset.dvd_sum
  intro ij hij
  have hij' := Finset.mem_antidiagonal.mp hij
  by_cases hi : 1 ≤ ij.1
  · exact dvd_mul_of_dvd_left (parameter_dvd_fg m ij.1 hi).1 _
  · exact dvd_mul_of_dvd_right (parameter_dvd_fg m ij.2 (by omega)).1 _

lemma f_one (m : ℤ) : f m 1 = m := by
  rw [f_recurrence m 1 (by omega)]
  simp

lemma square_dvd_f_even_add (m : ℤ) (r : ℕ) (hr : 1 ≤ r) :
    m^2 ∣ f m (2*r) + f m r := by
  have h := square_dvd_f_step m (2*r) (by omega)
  have he : Even (2*r) := ⟨r, by omega⟩
  simp only [he, ite_true, show 2*r/2 = r by omega] at h
  have h' := dvd_add h (square_dvd_g_add_f m r hr)
  convert h' using 1; ring

lemma square_dvd_f_odd (m : ℤ) (r : ℕ) (hr : 2 ≤ r) (he : ¬Even r) :
    m^2 ∣ f m r := by
  simpa only [he, ite_false, sub_zero] using square_dvd_f_step m r hr

end Hanna

namespace Hanna

lemma square_dvd_f_pow_two (m : ℤ) (j : ℕ) :
    m^2 ∣ f m (2^j) - m*(-1)^j := by
  induction j with
  | zero => simp [f_one]
  | succ j ih =>
    have h := square_dvd_f_even_add m (2^j) (by have := Nat.two_pow_pos j; omega)
    have hd := dvd_sub h ih
    have heq : f m (2*2^j) + f m (2^j) - (f m (2^j) - m*(-1)^j) =
        f m (2^(j+1)) - m*(-1)^(j+1) := by
      rw [pow_succ, pow_succ]
      ring_nf
    rwa [heq] at hd

lemma square_dvd_f_nonpow (m : ℤ) (r : ℕ) (hr : 1 ≤ r)
    (hn : ¬∃ j : ℕ, r = 2^j) : m^2 ∣ f m r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    have hr2 : 2 ≤ r := by
      by_contra h
      have heq : r = 1 := by omega
      exact hn ⟨0, by simpa using heq⟩
    by_cases he : Even r
    · have hrdiv : 1 ≤ r/2 := by omega
      have heq : r = 2*(r/2) := by obtain ⟨k,hk⟩ := he; omega
      have hd := ih (r/2) (Nat.div_lt_self (by omega) (by omega)) hrdiv (by
        rintro ⟨j,hj⟩
        apply hn
        refine ⟨j+1, ?_⟩
        rw [heq, hj, pow_succ]
        omega)
      have hs := square_dvd_f_even_add m (r/2) hrdiv
      rw [← heq] at hs
      simpa using dvd_sub hs hd
    · exact square_dvd_f_odd m r hr2 he

lemma mod_parameter_squared (m : ℤ) (_hm : 2 ≤ m) :
    (∀ j : ℕ, m^2 ∣ a m (2^j+1) - m*(-1)^j) ∧
    (∀ n : ℕ, 2 ≤ n → (¬∃ j : ℕ, n = 2^j+1) → m^2 ∣ a m n) := by
  constructor
  · intro j
    simpa only [f_eq_coeff_A, a] using square_dvd_f_pow_two m j
  · intro n hn hpow
    have h := square_dvd_f_nonpow m (n-1) (by omega) (by
      rintro ⟨j,hj⟩
      exact hpow ⟨j, by omega⟩)
    simpa only [f_eq_coeff_A, a, Nat.sub_add_cancel (by omega : 1 ≤ n)] using h

end Hanna

namespace Hanna

lemma two_pow_twice (k : ℕ) : (2:ℕ)^(2*k) = 4^k := by
  rw [pow_mul]
  norm_num

lemma two_pow_twice_add_one (k : ℕ) : (2:ℕ)^(2*k+1) = 2*4^k := by
  rw [pow_succ, two_pow_twice]
  omega

lemma power_two_index_split (n : ℕ) (hn : ∃ j : ℕ, n = 2^j+1) :
    (∃ k : ℕ, n = 4^k+1) ∨ (∃ k : ℕ, n = 2*4^k+1) := by
  obtain ⟨j, rfl⟩ := hn
  by_cases he : j%2 = 0
  · left
    refine ⟨j/2, ?_⟩
    have hj : j = 2*(j/2) := by omega
    conv_lhs => rw [hj, two_pow_twice]
  · right
    refine ⟨j/2, ?_⟩
    have hj : j = 2*(j/2)+1 := by omega
    conv_lhs => rw [hj, two_pow_twice_add_one]

lemma mod_square_even_exponent (m : ℤ) (hm : 2 ≤ m) (k : ℕ) :
    m^2 ∣ a m (4^k+1) - m := by
  have h := (mod_parameter_squared m hm).1 (2*k)
  simpa [two_pow_twice, pow_mul] using h

lemma mod_square_odd_exponent (m : ℤ) (hm : 2 ≤ m) (k : ℕ) :
    m^2 ∣ a m (2*4^k+1) - (m^2-m) := by
  have h := (mod_parameter_squared m hm).1 (2*k+1)
  have hs : (-1:ℤ)^(2*k+1) = -1 := by
    rw [pow_succ, pow_mul]
    norm_num
  have h' : m^2 ∣ a m (2*4^k+1) + m := by
    simpa only [two_pow_twice_add_one, hs, mul_neg_one, sub_neg_eq_add] using h
  have h'' := dvd_sub h' (dvd_refl (m^2))
  convert h'' using 1; ring

lemma mod_square_outside_classes (m : ℤ) (hm : 2 ≤ m) (n : ℕ) (hn : 2 ≤ n)
    (h₀ : ¬∃ k : ℕ, n = 4^k+1) (h₁ : ¬∃ k : ℕ, n = 2*4^k+1) :
    m^2 ∣ a m n := by
  apply (mod_parameter_squared m hm).2 n hn
  intro hp
  exact (power_two_index_split n hp).elim h₀ h₁

lemma residues_parameter_three :
    (∀ k : ℕ, (9:ℤ) ∣ a 3 (4^k+1) - 3) ∧
    (∀ k : ℕ, (9:ℤ) ∣ a 3 (2*4^k+1) - 6) ∧
    (∀ n : ℕ, 2 ≤ n → (¬∃ k : ℕ, n = 4^k+1) →
      (¬∃ k : ℕ, n = 2*4^k+1) → (9:ℤ) ∣ a 3 n) := by
  constructor
  · intro k
    simpa using mod_square_even_exponent 3 (by norm_num) k
  constructor
  · intro k
    simpa using mod_square_odd_exponent 3 (by norm_num) k
  · intro n hn h₀ h₁
    simpa using mod_square_outside_classes 3 (by norm_num) n hn h₀ h₁

lemma residues_parameter_four :
    (∀ k : ℕ, (16:ℤ) ∣ a 4 (4^k+1) - 4) ∧
    (∀ k : ℕ, (16:ℤ) ∣ a 4 (2*4^k+1) - 12) ∧
    (∀ n : ℕ, 2 ≤ n → (¬∃ k : ℕ, n = 4^k+1) →
      (¬∃ k : ℕ, n = 2*4^k+1) → (16:ℤ) ∣ a 4 n) := by
  constructor
  · intro k
    simpa using mod_square_even_exponent 4 (by norm_num) k
  constructor
  · intro k
    simpa using mod_square_odd_exponent 4 (by norm_num) k
  · intro n hn h₀ h₁
    simpa using mod_square_outside_classes 4 (by norm_num) n hn h₀ h₁

end Hanna
