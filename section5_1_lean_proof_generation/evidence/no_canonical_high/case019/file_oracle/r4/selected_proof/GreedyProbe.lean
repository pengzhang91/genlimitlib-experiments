import Stage3Model
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.SignedIntegers
open Set

namespace GP
noncomputable def greedyOutput (code : ℕ → ℤ) (hinj : Function.Injective code)
    (input : ℕ → ℤ) (t : ℕ) : ℤ := by
  let used : Finset ℤ := Finset.univ.image (fun s : Fin t => greedyOutput code hinj input s)
  let forbidden : Finset ℤ := GenLimit.Generic.sample input (t + 1) ∪ used
  have hrange : (Set.range code).Infinite := Set.infinite_range_of_injective hinj
  exact Classical.choose (hrange.diff forbidden.finite_toSet).nonempty
termination_by t

theorem greedyOutput_mem_range (code : ℕ → ℤ) (hinj : Function.Injective code)
    (input : ℕ → ℤ) (t : ℕ) : greedyOutput code hinj input t ∈ Set.range code := by
  rw [greedyOutput]
  exact (Classical.choose_spec _).1

theorem greedyOutput_fresh_input (code : ℕ → ℤ) (hinj : Function.Injective code)
    (input : ℕ → ℤ) (t : ℕ) :
    greedyOutput code hinj input t ∉ GenLimit.Generic.sample input (t + 1) := by
  rw [greedyOutput]
  exact fun h => (Classical.choose_spec _).2 (Finset.mem_union_left _ h)

theorem greedyOutput_novel (code : ℕ → ℤ) (hinj : Function.Injective code)
    (input : ℕ → ℤ) {s t : ℕ} (hst : s < t) :
    greedyOutput code hinj input s ≠ greedyOutput code hinj input t := by
  intro heq
  rw [greedyOutput] at heq
  have hused : greedyOutput code hinj input s ∈
      Finset.univ.image (fun r : Fin t => greedyOutput code hinj input r) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨s, hst⟩, rfl⟩
  exact (Classical.choose_spec _).2 (Finset.mem_union_right _ (heq ▸ hused))
end GP
