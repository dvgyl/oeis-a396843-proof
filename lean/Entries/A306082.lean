import More.StirlingPeriodicity

/-!
# A306082: separate formal entry in the final collection

AI disclosure: ChatGPT (OpenAI) generated this explicitly typed presentation
for Dev D. Goyal. Review status: see AUTHORSHIP.md. Complete mathematical
implementations are preserved in the imported modules. Source and historical
scope are documented in papers/A306082.tex (ChatGPT's original draft:
history/chatgpt-collection/manuscripts/A306082.tex).
-/

namespace FinalCollection.A306082



noncomputable section

open Finset

abbrev a (n : ℕ) : ℤ := More.Stirling.A306082 n

theorem source_formula (n : ℕ) :
    a n = ∑ k ∈ range (n+1),
      More.Stirling.squarePartitionWeight k * (k.factorial : ℤ) * (More.Stirling.second n k : ℤ) := by
  classical
  rfl

theorem period (m n : ℕ) (hm : 0 < m) (hn : m ≤ n) :
    (a (n+m.totient) : ZMod m) = (a n : ZMod m) :=
  More.Stirling.A306082_period m hm n hn

theorem least_period_divides (m : ℕ) (hm : 0 < m) :
    More.TailPeriodicity.leastPeriod (fun n => (a (m+n) : ZMod m)) ∣ m.totient :=
  More.Stirling.A306082_leastPeriod_dvd m hm

theorem least_period_specification (m : ℕ) (hm : 0 < m) :
    let f := fun n : ℕ => (a (m+n) : ZMod m)
    0 < More.TailPeriodicity.leastPeriod f ∧
      More.TailPeriodicity.leastPeriod f ∣ m.totient ∧
      (∀ n, f (n+More.TailPeriodicity.leastPeriod f) = f n) ∧
      (∀ q, 0 < q → (∀ n, f (n+q) = f n) →
        More.TailPeriodicity.leastPeriod f ≤ q) :=
  More.Stirling.transform_exact_tail_period More.Stirling.squarePartitionWeight m hm

theorem square_weight_definition (k : ℕ) :
    More.Stirling.squarePartitionWeight k =
      ((Finset.univ.filter fun p : Nat.Partition k =>
        ∀ j ∈ p.parts, Nat.sqrt j * Nat.sqrt j = j).card : ℤ) := by
  classical
  rfl

end
end FinalCollection.A306082
