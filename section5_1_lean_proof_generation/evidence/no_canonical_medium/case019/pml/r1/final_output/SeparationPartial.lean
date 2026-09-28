import output.Helpers

open Set
open GenLimit.Generic
open Stage3Case019

namespace Stage3Case019

open GenLimit.NoiseLossFeedback

/-- The supplied hierarchy witness already gives uncountability, infinitude,
level-q eventual validity/freshness, and the exact adjacent-level lower bound.
The missing strengthening is output novelty plus quarter density. -/
theorem stage3_uncountable_separation_core :
    ∀ q, ∃ family : LanguageClass ℤ,
      ¬family.Countable ∧
      (∀ K ∈ family, K.Infinite) ∧
      (∃ gen : Generator ℤ,
        ∀ K ∈ family, ∀ input : Stream ℤ,
          InjectiveValueContaminatedPresentationAtMost input K q →
            SampleFreshGeneratesAfterInput
              input (outputAfterInput gen input) K) ∧
      (∀ gen : Generator ℤ,
        ∃ K ∈ family, ∃ input : Stream ℤ,
          InjectiveValueContaminatedPresentationAtMost input K (q + 1) ∧
            ¬SampleFreshGeneratesAfterInput
              input (outputAfterInput gen input) K) := by
  intro q
  refine ⟨finiteOmissionClass q, finiteOmissionClass_uncountable q,
    finiteOmissionClass_uus q, ?_, finiteNoiseLevel_lower_afterInput q⟩
  obtain ⟨gen, hgen⟩ := finiteNoiseLevel_upper q
  refine ⟨gen, ?_⟩
  intro K hK input hinput
  obtain ⟨T, hT⟩ := hgen K hK input hinput
  refine ⟨T, ?_⟩
  intro t ht
  have hc := hT t ht
  simpa [SampleFreshGeneratesAfterInput, outputAfterInput,
    GenLimit.NoiseLossFeedback.CorrectAt,
    GenLimit.NoiseLossFeedback.outputAt] using hc

end Stage3Case019
