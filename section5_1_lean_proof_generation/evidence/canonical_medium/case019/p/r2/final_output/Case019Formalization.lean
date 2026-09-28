import Case019Helpers

open Stage3Case019

namespace Case019Formalization

/-- The canonical marker-and-tail witness family is extensionally uncountable,
all of its languages are infinite, and its two branches are distinguished by
level-`q` presentations exactly as required by the separation construction. -/
theorem stage3_separation_witness_backbone :
    ∀ q : ℕ, ∃ family : LanguageClass ℤ,
      ¬family.Countable ∧
      (∀ K ∈ family, K.Infinite) ∧
      (∀ K input,
        negativeBranch q K →
        GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q →
        ¬(↑(markers q) : Set ℤ) ⊆ Set.range input) ∧
      (∀ K input,
        positiveBranch q K →
        GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q →
        ∃ T, (↑(markers q) : Set ℤ) ⊆
          ↑(GenLimit.Generic.sample input T)) := by
  intro q
  refine ⟨witnessFamily q, witnessFamily_not_countable q, ?_, ?_, ?_⟩
  · intro K hK
    exact witnessFamily_infinite q hK
  · intro K input hK hp
    exact markers_not_subset_range_of_negativeBranch hK hp
  · intro K input hK hp
    exact markers_eventually_sampled_of_positiveBranch hK hp

end Case019Formalization
