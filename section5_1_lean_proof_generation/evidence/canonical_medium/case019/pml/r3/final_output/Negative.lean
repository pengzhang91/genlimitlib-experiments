import Stage3Model
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation

open Set Filter
open Stage3Case019

namespace Stage3Case019Proof

open GenLimit.NoiseLossFeedback

private theorem not_sampleFresh_iff_not_limit_correct
    (gen : Generator ℤ) (K : Language ℤ) (input : Stream ℤ) :
    (¬ SampleFreshGeneratesAfterInput input (outputAfterInput gen input) K) ↔
      ¬ (∃ T, ∀ t, T ≤ t → CorrectAt gen K input t) := by
  rfl

theorem finiteOmission_negative_clause (q : ℕ) :
    ∀ gen : Generator ℤ,
      ∃ K ∈ finiteOmissionClass q, ∃ input : Stream ℤ,
        GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
            input K (q + 1) ∧
          ¬ SampleFreshGeneratesAfterInput
            input (outputAfterInput gen input) K := by
  intro gen
  by_contra h
  apply finiteNoiseLevel_lower q
  refine ⟨gen, ?_⟩
  intro K hK input hinput
  by_contra hfail
  exact h ⟨K, hK, input, hinput,
    (not_sampleFresh_iff_not_limit_correct gen K input).mpr hfail⟩

end Stage3Case019Proof
