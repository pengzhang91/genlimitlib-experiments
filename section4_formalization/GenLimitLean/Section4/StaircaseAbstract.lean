import Section4.StaircaseRepresentation
import Section4.StaircaseTransportProfiles

namespace Section4.Staircase

/-- The exact frontier for arbitrary abstract staircase blocks, with their
original ambient universe and all fresh ordered-history competitors. -/
theorem abstract_exact_frontier {X : Type*} (C R : ℕ → Set X)
    (hCf : ∀ i, (C i).Finite) (hCn : ∀ i, (C i).Nonempty)
    (hRi : ∀ i, (R i).Infinite) (hRc : ∀ i, (R i).Countable)
    (hCC : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hRR : Pairwise (fun i j => Disjoint (R i) (R j)))
    (hCR : ∀ i j, Disjoint (C i) (R j)) :
    ∃ Q : Realization X,
      (∀ i, Q.target i = (⋃ k ≤ i, C k) ∪ R i) ∧
      (∀ i, Q.family.size i = ∑ k ∈ Finset.range (i+1), Nat.card (C k)) ∧
      (∀ σ : ℕ → Bool, Q.Fresh (Q.scheduleGenerator σ) ∧
        (∀ i m, Q.MistakeBound (Q.scheduleGenerator σ) i m ↔ Family.mistakeCount σ i ≤ m) ∧
        (∀ i d, Q.DeadlineBound (Q.scheduleGenerator σ) i d ↔ Q.family.deadline σ i ≤ d) ∧
        Q.ParetoMinimal (Q.scheduleGenerator σ)) ∧
      (∀ G, Q.Fresh G → ∃ σ, Q.Dominates (Q.scheduleGenerator σ) G) ∧
      (∀ G, Q.Fresh G → (Q.ParetoMinimal G ↔ ∃ σ, Q.SameProfile G (Q.scheduleGenerator σ))) := by
  obtain ⟨ha,e,he⟩ := exists_representation C R hCf hCn hRi hRc hCC hRR hCR
  let Q : Realization X := ⟨Family.ofBlocks (fun i => Nat.card (C i)) ha,e⟩
  exact ⟨Q,he,fun _ => rfl,Q.exact_frontier⟩

/-- The appendix's abstract staircase theorem, stated directly with the exact
worst-case extended-natural profiles, including possibly unbounded competitors. -/
theorem abstract_exact_staircase_frontier {X : Type*} (C R : ℕ → Set X)
    (hCf : ∀ i, (C i).Finite) (hCn : ∀ i, (C i).Nonempty)
    (hRi : ∀ i, (R i).Infinite) (hRc : ∀ i, (R i).Countable)
    (hCC : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hRR : Pairwise (fun i j => Disjoint (R i) (R j)))
    (hCR : ∀ i j, Disjoint (C i) (R j)) :
    ∃ Q : Realization X,
      (∀ i, Q.target i = (⋃ k ≤ i, C k) ∪ R i) ∧
      (∀ i, Q.family.size i = ∑ k ∈ Finset.range (i+1), Nat.card (C k)) ∧
      (∀ σ : ℕ → Bool, Q.Fresh (Q.scheduleGenerator σ) ∧
        (∀ i, Q.worstMistakes (Q.scheduleGenerator σ) i = (Family.mistakeCount σ i : ℕ∞) ∧
          Q.worstDeadline (Q.scheduleGenerator σ) i = (Q.family.deadline σ i : ℕ∞)) ∧
        Q.ParetoMinimal (Q.scheduleGenerator σ)) ∧
      (∀ G, Q.Fresh G → ∃ σ : ℕ → Bool, ∀ i,
        (Family.mistakeCount σ i : ℕ∞) ≤ Q.worstMistakes G i ∧
        (Q.family.deadline σ i : ℕ∞) ≤ Q.worstDeadline G i) ∧
      (∀ G, Q.Fresh G → (Q.ParetoMinimal G ↔
        ∃ σ : ℕ → Bool, Q.SameProfile G (Q.scheduleGenerator σ))) := by
  obtain ⟨ha,e,he⟩ := exists_representation C R hCf hCn hRi hRc hCC hRR hCR
  let Q : Realization X := ⟨Family.ofBlocks (fun i => Nat.card (C i)) ha,e⟩
  exact ⟨Q,he,fun _ => rfl,Q.exact_staircase_frontier⟩

end Section4.Staircase

#print axioms Section4.Staircase.abstract_exact_frontier
#print axioms Section4.Staircase.abstract_exact_staircase_frontier
