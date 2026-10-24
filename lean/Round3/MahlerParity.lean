import Round3.ModFour
import Hanna.Related.ScaledParity
import More.CubicFrobenius

/-!
# OEIS A389536: exact residues modulo four

Construct the normalized integral series satisfying `A(X^2+2X^3)=X*A`.
Its coefficients above degree one are two modulo four precisely at the
indices one greater than a power of two, and zero otherwise.

AI disclosure: OpenAI ChatGPT generated these proofs for Dev D. Goyal.
No exclusive priority is claimed; see AUTHORSHIP.md.
-/

namespace Round3.MahlerParity

open PowerSeries Hanna.Series

noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S]

def B : PowerSeries R := X^2+2*X^3

theorem B_constantCoeff : constantCoeff R (B : PowerSeries R)=0 := by simp [B]

theorem B_order : (X : PowerSeries R)^2 ∣ (B : PowerSeries R) := by
  refine ⟨1+2*X, ?_⟩
  dsimp [B]
  ring

def residual (G : PowerSeries R) : PowerSeries R := X*G-compose G B

theorem residual_vanish_initial (G : PowerSeries R) (hG : Normalized G) :
    (X : PowerSeries R)^3 ∣ residual G := by
  obtain ⟨D,rfl⟩ := hG.decompose
  have hb : (X : PowerSeries R)^4 ∣ (B : PowerSeries R)^2 := by
    simpa [pow_two] using X_pow_dvd_product B_order B_order
  have hb3 : (X : PowerSeries R)^3 ∣ (B : PowerSeries R)^2 :=
    (pow_dvd_pow X (by omega : 3≤4)).trans hb
  have hd := dvd_sub (dvd_mul_right ((X : PowerSeries R)^3) (D-2))
    (dvd_mul_of_dvd_left hb3 (compose D B))
  unfold residual
  rw [compose_add _ _ _ B_constantCoeff, compose_mul _ _ _ B_constantCoeff,
    compose_pow _ _ _ B_constantCoeff, compose_X_left _ B_constantCoeff]
  convert hd using 1
  dsimp [B]
  ring

theorem residual_perturbation (G H : PowerSeries R) (r : ℕ) (hr : 2≤r)
    (hGH : (X : PowerSeries R)^r ∣ G-H) :
    (X : PowerSeries R)^(r+2) ∣ residual G-residual H-X*(G-H) := by
  have hc := compose_outer_vanish (G-H) (B : PowerSeries R) r 2
    B_constantCoeff hGH B_order
  have hd : (X : PowerSeries R)^(r+2) ∣ compose (G-H) B :=
    (pow_dvd_pow X (by omega : r+2≤2*r)).trans hc
  rw [compose_sub _ _ _ B_constantCoeff] at hd
  convert dvd_neg.mpr hd using 1
  unfold residual
  ring

theorem equation_triangular :
    Triangular (fun a n => coeff R (n+3) (residual (ofTail a))) := by
  intro n a b hab
  have hd := (agree_iff_X_pow_dvd_sub (n+2) (ofTail a) (ofTail b)).mp
    (ofTail_agree a b n hab)
  have hp := residual_perturbation (ofTail a) (ofTail b) (n+2) (by omega) hd
  have hc := X_pow_dvd_iff.mp hp (n+3) (by omega)
  have hx (G : PowerSeries R) : coeff R (n+3) (X*G)=coeff R (n+2) G := by
    simpa only [show n+3=(n+2)+1 by omega] using coeff_succ_X_mul (n+2) G
  simp only [map_sub, hx, coeff_ofTail] at hc ⊢
  linear_combination hc

theorem solution_exists :
    ∃ G : PowerSeries R, Normalized G ∧ compose G B=X*G := by
  let op := fun a n => coeff R (n+3) (residual (ofTail a))
  let a := triangularCoeffs op (fun _ => 0)
  have ha := triangularCoeffs_spec op equation_triangular (fun _ => 0)
  refine ⟨ofTail a, normalized_ofTail a, ?_⟩
  have he : residual (ofTail a)=0 := by
    ext n
    by_cases hn : n<3
    · exact X_pow_dvd_iff.mp (residual_vanish_initial _ (normalized_ofTail a)) n hn
    · have hc := congrFun ha (n-3)
      change coeff R (n-3+3) (residual (ofTail a))=0 at hc
      simpa only [Nat.sub_add_cancel (by omega : 3≤n), map_zero] using hc
  exact (sub_eq_zero.mp he).symm

theorem solution_unique {G H : PowerSeries R} (hG : Normalized G)
    (hH : Normalized H) (heG : compose G B=X*G) (heH : compose H B=X*H) : G=H := by
  have hzG : residual G=0 := sub_eq_zero.mpr heG.symm
  have hzH : residual H=0 := sub_eq_zero.mpr heH.symm
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n<2
    · rcases (by omega : n=0 ∨ n=1) with rfl | rfl
      · exact hG.1.trans hH.1.symm
      · exact hG.2.trans hH.2.symm
    · have hd := (agree_iff_X_pow_dvd_sub n G H).mp ih
      have hp := residual_perturbation G H n (by omega) hd
      have hc := X_pow_dvd_iff.mp hp (n+1) (by omega)
      rw [hzG,hzH,sub_self] at hc
      simp only [zero_sub, map_neg, coeff_succ_X_mul, map_sub, neg_eq_zero, sub_eq_zero] at hc
      exact hc

theorem existence_uniqueness :
    ∃! G : PowerSeries R, Normalized G ∧ compose G (X^2+2*X^3)=X*G := by
  obtain ⟨G,hG,heG⟩ := solution_exists (R:=R)
  exact ⟨G,⟨hG,heG⟩,fun H hH => solution_unique hH.1 hG hH.2 heG⟩

def A : PowerSeries R := (existence_uniqueness (R:=R)).exists.choose

theorem A_normalized : Normalized (A : PowerSeries R) :=
  (existence_uniqueness (R:=R)).exists.choose_spec.1

theorem A_equation : compose (A : PowerSeries R) (X^2+2*X^3)=X*A :=
  (existence_uniqueness (R:=R)).exists.choose_spec.2

theorem map_A (f : R →+* S) :
    PowerSeries.map f (A : PowerSeries R)=(A : PowerSeries S) := by
  apply solution_unique (A_normalized.map f) A_normalized _ A_equation
  have h := congrArg (PowerSeries.map f) (A_equation (R:=R))
  rw [Hanna.Series.map_compose f _ _ (by simp)] at h
  simpa only [B, map_add, map_mul, map_pow, map_ofNat, PowerSeries.map_X] using h

private abbrev H : PowerSeries (ZMod 4) :=
  Hanna.Related.ScaledInverse.scaledSolution 0

private def candidate : PowerSeries (ZMod 4) := X+2*(X*H)

private theorem candidate_normalized : Normalized candidate := by
  have hH := Hanna.Related.ScaledInverse.scaledSolution_normalized (0 : ZMod 4)
  constructor
  · simp [candidate]
  · simp [candidate, two_mul, hH.1, coeff_succ_X_mul]

private theorem double_composition : 2*compose H B=2*H^2 := by
  apply Round3.ModFour.series_double_eq_of_mod_two
  rw [map_compose _ _ _ B_constantCoeff, map_pow]
  have hB : PowerSeries.map Round3.ModFour.reduce (B : PowerSeries (ZMod 4))=X^2 := by
    have htwo : (2 : PowerSeries (ZMod 2))=0 := by
      have ht : (2 : ZMod 2)=0 := by decide
      simpa only [map_ofNat, map_zero] using congrArg (C (ZMod 2)) ht
    simp only [B, map_add, map_pow, map_mul, map_ofNat, PowerSeries.map_X,
      htwo, zero_mul, add_zero]
  rw [hB]
  exact (More.CubicReversion.square_substitution (PowerSeries.map Round3.ModFour.reduce H)).symm

private theorem candidate_equation : compose candidate B=X*candidate := by
  have hfour : (4 : PowerSeries (ZMod 4))=0 := by
    have h : (4 : ZMod 4)=0 := by decide
    simpa only [map_ofNat, map_zero] using congrArg (C (ZMod 4)) h
  have htwo : compose (2 : PowerSeries (ZMod 4)) B=2 := by
    simpa only [map_ofNat] using compose_C (2 : ZMod 4) B B_constantCoeff
  have hH := Hanna.Related.ScaledInverse.scaledSolution_zero_quadratic (R:=ZMod 4)
  unfold candidate
  rw [compose_add _ _ _ B_constantCoeff, compose_mul _ _ _ B_constantCoeff,
    compose_mul _ _ _ B_constantCoeff, compose_X_left _ B_constantCoeff, htwo]
  change B+2*(B*compose H B)=X*(X+2*(X*H))
  have hd := double_composition
  dsimp [B] at hd ⊢
  linear_combination (X : PowerSeries (ZMod 4))^2*hd -
    2*X^2*hH + X^3*compose H (X^2+2*X^3)*hfour

/-- Full series identity modulo four; the comparison series is proved equal
to the canonical solution by uniqueness. -/
theorem A_mod_four : (A : PowerSeries (ZMod 4))=X+2*(X*H) :=
  solution_unique A_normalized candidate_normalized A_equation candidate_equation

def a (n : ℕ) : ℤ := coeff ℤ n A

private theorem double_residue (u : ZMod 4) :
    (2*u=2 ↔ Round3.ModFour.reduce u=1) ∧
    (2*u=0 ↔ Round3.ModFour.reduce u≠1) := by
  exact (by decide : ∀ u : ZMod 4,
    (2*u=2 ↔ Round3.ModFour.reduce u=1) ∧
    (2*u=0 ↔ Round3.ModFour.reduce u≠1)) u

/-- Exact source conjecture, with both the exceptional and complementary cases. -/
theorem a389536_residue (n : ℕ) (hn : 1<n) :
    ((a n : ZMod 4)=2 ↔ ∃ k : ℕ, n=2^k+1) ∧
    ((a n : ZMod 4)=0 ↔ ¬∃ k : ℕ, n=2^k+1) := by
  have hm := congrArg (coeff (ZMod 4) n) (map_A (Int.castRingHom (ZMod 4)))
  rw [coeff_map, A_mod_four] at hm
  change (a n : ZMod 4)=coeff (ZMod 4) n (X+2*(X*H)) at hm
  have he : (a n : ZMod 4)=2*coeff (ZMod 4) (n-1) H := by
    rw [hm]
    have hn' : n=(n-1)+1 := by omega
    rw [hn']
    simp only [map_add, coeff_X, if_neg (by omega : n-1+1≠1), two_mul,
      map_add, coeff_succ_X_mul, zero_add, Nat.add_sub_cancel]
  rw [he, (double_residue _).1, (double_residue _).2]
  have hmap := congrArg (coeff (ZMod 2) (n-1))
    (Hanna.Related.ScaledInverse.map_scaledSolution Round3.ModFour.reduce (0 : ZMod 4))
  simp only [coeff_map, map_zero] at hmap
  rw [hmap]
  have hp := Hanna.Related.ScaledInverse.scaledSolution_zero_coeff_one_iff (n-1)
  have hi : (∃ k : ℕ, n-1=2^k) ↔ ∃ k : ℕ, n=2^k+1 := by
    constructor <;> rintro ⟨k,hk⟩ <;> exact ⟨k, by omega⟩
  exact ⟨hp.trans hi, not_congr (hp.trans hi)⟩

/-- The complementary clause stated literally as integer divisibility. -/
theorem a389536_four_dvd_iff (n : ℕ) (hn : 1<n) :
    (4 : ℤ) ∣ a n ↔ ¬∃ k : ℕ, n=2^k+1 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd (a n) 4).symm.trans (a389536_residue n hn).2

end
end Round3.MahlerParity
