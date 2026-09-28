import CountableScratch

open Stage3Case019

namespace Stage3Case019Proof

/-- Strongest fully checked partial endpoint: the complete countable clause,
together with all non-positive components of the adjacent-level separation. -/
theorem stage3_verified_partial :
    CountableClause ∧
      ∀ q,
        ¬(GenLimit.NoiseLossFeedback.finiteOmissionClass q).Countable ∧
          (∀ K ∈ GenLimit.NoiseLossFeedback.finiteOmissionClass q,
            K.Infinite) ∧
          (∀ gen : Generator ℤ,
            ∃ K ∈ GenLimit.NoiseLossFeedback.finiteOmissionClass q,
              ∃ input : Stream ℤ,
                GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
                    input K (q + 1) ∧
                  ¬SampleFreshGeneratesAfterInput
                    input (outputAfterInput gen input) K) := by
  refine ⟨stage3_countable_half_density, ?_⟩
  intro q
  exact separation_witness_structure q

end Stage3Case019Proof
