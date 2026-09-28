import «output».Countable

namespace Stage3Case019

open Set

/-- Checked adjacent-level impossibility component for the canonical P12 class. -/
theorem finiteOmissionClass_adjacent_failure (q : ℕ) :
    ∀ gen : Generator ℤ,
      ∃ K ∈ GenLimit.NoiseLossFeedback.finiteOmissionClass q,
        ∃ input : Stream ℤ,
          GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
              input K (q + 1) ∧
            ¬SampleFreshGeneratesAfterInput
              input (outputAfterInput gen input) K := by
  intro gen
  have hnot :
      ¬GenLimit.NoiseLossFeedback.IsLimitGeneratorWithNoiseLevel gen
        (GenLimit.NoiseLossFeedback.finiteOmissionClass q) (q + 1) := by
    intro hgen
    exact GenLimit.NoiseLossFeedback.finiteNoiseLevel_lower q ⟨gen, hgen⟩
  simp only [GenLimit.NoiseLossFeedback.IsLimitGeneratorWithNoiseLevel] at hnot
  push_neg at hnot
  obtain ⟨K, hK, input, hinput, hfail⟩ := hnot
  refine ⟨K, hK, input, hinput, ?_⟩
  simpa [SampleFreshGeneratesAfterInput, outputAfterInput,
    GenLimit.NoiseLossFeedback.CorrectAt,
    GenLimit.NoiseLossFeedback.outputAt,
    GenLimit.NoiseLossFeedback.observedThrough] using hfail

/-- Checked infinitude component for every member of the same class. -/
theorem finiteOmissionClass_infinite (q : ℕ) :
    ∀ K ∈ GenLimit.NoiseLossFeedback.finiteOmissionClass q, K.Infinite :=
  GenLimit.NoiseLossFeedback.finiteOmissionClass_uus q

end Stage3Case019
