import Stage3Model
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation

open Set
open Stage3Case019

namespace TestNegative
open GenLimit GenLimit.NoiseLossFeedback

theorem negative_part (q : ℕ) :
    ∀ gen : Generator ℤ,
      ∃ K ∈ finiteOmissionClass q, ∃ input : Stream ℤ,
        GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
            input K (q + 1) ∧
          ¬SampleFreshGeneratesAfterInput
            input (outputAfterInput gen input) K := by
  intro gen
  have h := finiteNoiseLevel_lower q
  rw [GeneratableInLimitWithNoiseLevel, not_exists] at h
  have hg := h gen
  unfold IsLimitGeneratorWithNoiseLevel at hg
  push_neg at hg
  obtain ⟨K, hK, input, hinput, hfail⟩ := hg
  refine ⟨K, hK, input, hinput, ?_⟩
  intro hsuccess
  obtain ⟨T, hT⟩ := hsuccess
  obtain ⟨t, ht, hbad⟩ := hfail T
  exact hbad (hT t ht)

end TestNegative
