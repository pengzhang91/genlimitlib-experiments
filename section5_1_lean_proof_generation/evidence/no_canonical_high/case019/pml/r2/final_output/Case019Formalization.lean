import Stage3Model
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation

open Stage3Case019

namespace Stage3Case019

open GenLimit.Generic
open GenLimit.NoiseLossFeedback

theorem finiteOmissionClass_infinite (q : ℕ) :
    ∀ K ∈ finiteOmissionClass q, K.Infinite := by
  exact finiteOmissionClass_uus q

theorem finiteOmissionClass_level_succ_failure (q : ℕ) :
    ∀ gen : Generator ℤ,
      ∃ K ∈ finiteOmissionClass q, ∃ input : Stream ℤ,
        InjectiveValueContaminatedPresentationAtMost input K (q + 1) ∧
          ¬SampleFreshGeneratesAfterInput
            input (outputAfterInput gen input) K := by
  intro gen
  by_contra hbad
  apply finiteNoiseLevel_lower q
  refine ⟨gen, ?_⟩
  intro K hK input hinput
  have hrun :
      SampleFreshGeneratesAfterInput
        input (outputAfterInput gen input) K := by
    by_contra hrun
    exact hbad ⟨K, hK, input, hinput, hrun⟩
  simpa [SampleFreshGeneratesAfterInput, outputAfterInput,
    GenLimit.NoiseLossFeedback.CorrectAt, outputAt, observedThrough] using hrun

end Stage3Case019
