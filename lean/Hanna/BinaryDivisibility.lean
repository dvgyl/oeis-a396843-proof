module

public import Hanna.Recurrences
public import Hanna.BinaryWeight

@[expose] public section

namespace Hanna
open PowerSeries
variable {R : Type*} [CommRing R]

lemma binary_product_dvd (m x y : R) (i j : ℕ)
    (hx : m ^ binaryWeight i ∣ x) (hy : m ^ binaryWeight j ∣ y) :
    m ^ binaryWeight (i+j) ∣ x*y := by
  apply (pow_dvd_pow m (binaryWeight_add_le i j)).trans
  simpa only [pow_add] using mul_dvd_mul hx hy

lemma binary_coeff_pow_dvd (m : R) (H : PowerSeries R) (d k : ℕ)
    (hH : ∀ i ≤ d, m ^ binaryWeight i ∣ coeff i H) :
    m ^ binaryWeight d ∣ coeff d (H^k) := by
  induction k generalizing d with
  | zero =>
    by_cases hd : d = 0
    · subst d
      simp
    · simp [coeff_one, hd]
  | succ k ih =>
    rw [pow_succ, coeff_mul]
    apply Finset.dvd_sum
    intro ij hij
    have hs := Finset.mem_antidiagonal.mp hij
    have hi : ij.1 ≤ d := by omega
    have hj : ij.2 ≤ d := by omega
    simpa only [hs] using binary_product_dvd m _ _ ij.1 ij.2
      (ih ij.1 (fun i hi' => hH i (hi'.trans hi))) (hH ij.2 hj)

lemma binary_divisibility_shifted (m : R) (r : ℕ) :
    m ^ binaryWeight r ∣ f m r ∧ m ^ binaryWeight r ∣ g m r := by
  induction r using Nat.strongRecOn with
  | ind r ih =>
    by_cases hr : r = 0
    · subst r
      simp
    have hrpos : 1 ≤ r := by omega
    have hf : m ^ binaryWeight r ∣ f m r := by
      rw [f_recurrence m r hrpos]
      apply dvd_add
      · split_ifs with heven
        · have hhalf : r/2 < r := by omega
          have hweight : binaryWeight r = binaryWeight (r/2) := by
            rw [binaryWeight_step, Nat.even_iff.mp heven, zero_add]
          rw [hweight]
          exact (ih (r/2) hhalf).2
        · exact dvd_zero _
      · rw [Finset.mul_sum]
        apply Finset.dvd_sum
        intro ij hij
        have hs := Finset.mem_antidiagonal.mp hij
        have hi : ij.1 < r := by omega
        have hj : ij.2 < r := by omega
        have hp := binary_product_dvd m _ _ ij.1 ij.2 (ih ij.1 hi).1 (ih ij.2 hj).1
        have hw : binaryWeight r ≤ 1 + binaryWeight (ij.1+ij.2) := by
          have hb := binaryWeight_succ_le (r-1)
          have heq : r-1+1 = r := by omega
          rw [heq] at hb
          rw [hs]
          omega
        apply (pow_dvd_pow m hw).trans
        simpa only [pow_add, pow_one] using mul_dvd_mul (dvd_refl m) hp
    refine ⟨hf, ?_⟩
    rw [g_recurrence m r hrpos]
    apply dvd_sub (dvd_neg.mpr hf)
    apply Finset.dvd_sum
    intro j hj
    have hjlo : 1 ≤ j := (Finset.mem_Ico.mp hj).1
    have hjhi : j < r := (Finset.mem_Ico.mp hj).2
    have hd : r-j < r := by omega
    have hp := binary_coeff_pow_dvd m (G m) (r-j) (j+1)
      (fun i hi => (ih i (by omega)).2)
    have hs : j+(r-j) = r := by omega
    simpa only [hs] using binary_product_dvd m _ _ j (r-j) (ih j hjhi).1 hp

lemma binary_divisibility_coeff_A (m : R) (n : ℕ) (hn : 1 ≤ n) :
    m ^ binaryWeight (n-1) ∣ coeff n (A m) := by
  have h := (binary_divisibility_shifted m (n-1)).1
  rw [f_eq_coeff_A] at h
  simpa only [Nat.sub_add_cancel hn] using h

lemma binary_divisibility_coeff_B (m : R) (n : ℕ) (hn : 1 ≤ n) :
    m ^ binaryWeight (n-1) ∣ coeff n (B m) := by
  have h := (binary_divisibility_shifted m (n-1)).2
  rw [g_eq_coeff_B] at h
  simpa only [Nat.sub_add_cancel hn] using h

lemma binary_divisibility_polynomial (n : ℕ) (hn : 1 ≤ n) :
    (Polynomial.X : Polynomial ℤ) ^ binaryWeight (n-1) ∣ P n :=
  binary_divisibility_coeff_A Polynomial.X n hn

lemma inverse_binary_divisibility_polynomial (n : ℕ) (hn : 1 ≤ n) :
    (Polynomial.X : Polynomial ℤ) ^ binaryWeight (n-1) ∣ Q n :=
  binary_divisibility_coeff_B Polynomial.X n hn

lemma binary_divisibility_integer (m : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    m ^ binaryWeight (n-1) ∣ a m n :=
  binary_divisibility_coeff_A m n hn

lemma inverse_binary_divisibility_integer (m : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    m ^ binaryWeight (n-1) ∣ b m n :=
  binary_divisibility_coeff_B m n hn

lemma power_of_two_index (m : ℤ) (k : ℕ) : m^k ∣ a m (2^k) := by
  have h := binary_divisibility_integer m (2^k) (Nat.two_pow_pos k)
  simpa only [binaryWeight_two_pow_sub_one] using h

end Hanna
