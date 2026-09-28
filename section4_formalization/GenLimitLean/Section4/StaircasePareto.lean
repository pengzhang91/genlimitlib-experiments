import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Tactic

/-!
The schedule comparison used in the staircase theorem.
Indices in this file start at zero; index `i` corresponds to target `L_(i+1)`
in the manuscript. No hypothesis about a generator is needed for this lemma.
-/

namespace Section4.StaircasePareto

def prefixCount (σ : ℕ → Bool) (i : ℕ) : ℕ :=
  ((Finset.range i).filter fun k => σ k = true).card

def scheduleMistakes (σ : ℕ → Bool) (i : ℕ) : ℕ :=
  prefixCount σ i + if σ i = true then 0 else 1

theorem prefixCount_succ (σ : ℕ → Bool) (i : ℕ) :
    prefixCount σ (i + 1) = prefixCount σ i + if σ i = true then 1 else 0 := by
  classical
  unfold prefixCount
  rw [Finset.range_add_one, Finset.filter_insert]
  cases h : σ i <;> simp [h, Finset.mem_filter, Finset.mem_range]

theorem prefixCount_congr {σ τ : ℕ → Bool} {i : ℕ}
    (h : ∀ k < i, τ k = σ k) : prefixCount τ i = prefixCount σ i := by
  unfold prefixCount
  congr 1
  apply Finset.filter_congr
  intro k hk
  rw [h k (Finset.mem_range.mp hk)]

/-- Distinct binary schedules have incomparable vectors of mistake counts. -/
theorem schedule_eq_of_mistakes_le {σ τ : ℕ → Bool}
    (h : ∀ i, scheduleMistakes τ i ≤ scheduleMistakes σ i) : τ = σ := by
  funext i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    have hc := prefixCount_congr ih
    have h0 := h i
    have h1 := h (i + 1)
    have h2 := h (i + 2)
    have ct1 := prefixCount_succ τ i
    have cs1 := prefixCount_succ σ i
    have ct2 := prefixCount_succ τ (i + 1)
    have cs2 := prefixCount_succ σ (i + 1)
    simp only [Nat.add_assoc] at ct2 cs2
    unfold scheduleMistakes at h0 h1 h2
    cases ht : τ i <;> cases hs : σ i
    · rfl
    · simp [ht, hs] at h0
      omega
    · cases ht1 : τ (i + 1) <;> cases hs1 : σ (i + 1) <;>
        cases ht2 : τ (i + 2) <;> cases hs2 : σ (i + 2) <;>
        simp [ht, hs, ht1, hs1, ht2, hs2] at h0 h1 h2 ct1 cs1 ct2 cs2 <;> omega
    · rfl

/-- A profile between one schedule and another must have identical mistake counts.
This is the step that turns domination by schedules into Pareto optimality. -/
theorem profile_sandwich {σ τ : ℕ → Bool} {M : ℕ → ℕ}
    (hLower : ∀ i, scheduleMistakes τ i ≤ M i)
    (hUpper : ∀ i, M i ≤ scheduleMistakes σ i) :
    τ = σ ∧ ∀ i, M i = scheduleMistakes σ i := by
  have hEq := schedule_eq_of_mistakes_le (fun i => (hLower i).trans (hUpper i))
  refine ⟨hEq, fun i => Nat.le_antisymm (hUpper i) ?_⟩
  simpa [hEq] using hLower i

end Section4.StaircasePareto
