import More.StirlingTransform
import More.PowerPeriodicity
import More.TailPeriodicity

/-!
# Eventual totient periods for all integral factorial Stirling transforms

AI disclosure: OpenAI ChatGPT generated these mathematical proofs and their
formalization for Dev D. Goyal.  OEIS source statements and prior-art discussion are
recorded in `docs/STIRLING_PERIODICITY.md`.

The generic theorem applies to every integer coefficient sequence, and therefore
to the coefficient form of every integral `G(exp(x)-1)`.  Seven named results
instantiate the exact Stirling formulas in the current OEIS entries.
-/

namespace More.Stirling

/-- The universal conjecture: totient is a tail period, with explicit onset `m`. -/
theorem transform_totient_period (c : ℕ → ℤ) (m : ℕ) (hm : 0 < m)
    (n : ℕ) (hn : m ≤ n) :
    (transform c (n + m.totient) : ZMod m) = (transform c n : ZMod m) := by
  apply transform_periodic_of_powers c m m.totient n hm hn
  intro a
  exact More.PowerPeriodicity.pow_totient_add_eq m hm a n hn

/-- A period dividing the totient, stated with all quantifiers explicit. -/
theorem transform_eventually_periodic (c : ℕ → ℤ) (m : ℕ) (hm : 0 < m) :
    ∃ p : ℕ, 0 < p ∧ p ∣ m.totient ∧
      ∀ n : ℕ, m ≤ n →
        (transform c (n + p) : ZMod m) = (transform c n : ZMod m) := by
  refine ⟨m.totient, Nat.totient_pos.mpr hm, dvd_refl _, ?_⟩
  intro n hn
  exact transform_totient_period c m hm n hn

/-- The least positive period of the tail starting at `m` divides the totient.
The statement also certifies that this number is itself a period and is minimal. -/
theorem transform_exact_tail_period (c : ℕ → ℤ) (m : ℕ) (hm : 0 < m) :
    let f := fun n : ℕ => (transform c (m + n) : ZMod m)
    0 < More.TailPeriodicity.leastPeriod f ∧
      More.TailPeriodicity.leastPeriod f ∣ m.totient ∧
      (∀ n, f (n + More.TailPeriodicity.leastPeriod f) = f n) ∧
      (∀ q, 0 < q → (∀ n, f (n + q) = f n) →
        More.TailPeriodicity.leastPeriod f ≤ q) := by
  apply More.TailPeriodicity.leastPeriod_spec _ m.totient (Nat.totient_pos.mpr hm)
  intro n
  simpa only [Nat.add_assoc] using
    transform_totient_period c m hm (m + n) (Nat.le_add_right m n)

theorem A052895_period (m : ℕ) (hm : 0 < m) (n : ℕ) (hn : m ≤ n) :
    (A052895 (n + m.totient) : ZMod m) = (A052895 n : ZMod m) :=
  transform_totient_period _ m hm n hn

theorem A064618_period (m : ℕ) (hm : 0 < m) (n : ℕ) (hn : m ≤ n) :
    (A064618 (n + m.totient) : ZMod m) = (A064618 n : ZMod m) :=
  transform_totient_period _ m hm n hn

theorem A354242_period (m : ℕ) (hm : 0 < m) (n : ℕ) (hn : m ≤ n) :
    (A354242 (n + m.totient) : ZMod m) = (A354242 n : ZMod m) :=
  transform_totient_period _ m hm n hn

theorem A167137_period (m : ℕ) (hm : 0 < m) (n : ℕ) (hn : m ≤ n) :
    (A167137 (n + m.totient) : ZMod m) = (A167137 n : ZMod m) :=
  transform_totient_period _ m hm n hn

theorem A305550_period (m : ℕ) (hm : 0 < m) (n : ℕ) (hn : m ≤ n) :
    (A305550 (n + m.totient) : ZMod m) = (A305550 n : ZMod m) :=
  transform_totient_period _ m hm n hn

theorem A306082_period (m : ℕ) (hm : 0 < m) (n : ℕ) (hn : m ≤ n) :
    (A306082 (n + m.totient) : ZMod m) = (A306082 n : ZMod m) :=
  transform_totient_period _ m hm n hn

theorem A080253_period (m : ℕ) (hm : 0 < m) (n : ℕ) (hn : m ≤ n) :
    (A080253 (n + m.totient) : ZMod m) = (A080253 n : ZMod m) :=
  transform_totient_period _ m hm n hn

theorem A052895_leastPeriod_dvd (m : ℕ) (hm : 0 < m) :
    More.TailPeriodicity.leastPeriod (fun n => (A052895 (m + n) : ZMod m)) ∣ m.totient :=
  (transform_exact_tail_period _ m hm).2.1

theorem A064618_leastPeriod_dvd (m : ℕ) (hm : 0 < m) :
    More.TailPeriodicity.leastPeriod (fun n => (A064618 (m + n) : ZMod m)) ∣ m.totient :=
  (transform_exact_tail_period _ m hm).2.1

theorem A354242_leastPeriod_dvd (m : ℕ) (hm : 0 < m) :
    More.TailPeriodicity.leastPeriod (fun n => (A354242 (m + n) : ZMod m)) ∣ m.totient :=
  (transform_exact_tail_period _ m hm).2.1

theorem A167137_leastPeriod_dvd (m : ℕ) (hm : 0 < m) :
    More.TailPeriodicity.leastPeriod (fun n => (A167137 (m + n) : ZMod m)) ∣ m.totient :=
  (transform_exact_tail_period _ m hm).2.1

theorem A305550_leastPeriod_dvd (m : ℕ) (hm : 0 < m) :
    More.TailPeriodicity.leastPeriod (fun n => (A305550 (m + n) : ZMod m)) ∣ m.totient :=
  (transform_exact_tail_period _ m hm).2.1

theorem A306082_leastPeriod_dvd (m : ℕ) (hm : 0 < m) :
    More.TailPeriodicity.leastPeriod (fun n => (A306082 (m + n) : ZMod m)) ∣ m.totient :=
  (transform_exact_tail_period _ m hm).2.1

theorem A080253_leastPeriod_dvd (m : ℕ) (hm : 0 < m) :
    More.TailPeriodicity.leastPeriod (fun n => (A080253 (m + n) : ZMod m)) ∣ m.totient :=
  (transform_exact_tail_period _ m hm).2.1

end More.Stirling
