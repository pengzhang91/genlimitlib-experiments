import Case019Countable
import Case019Helpers

open Set

namespace Stage3Case019

open GenLimit.Generic
open GenLimit.NoiseLossFeedback

/-- Fully checked first component of the requested claim. -/
theorem stage3_countable_half_density : CountableClause :=
  countableClause_checked

/-- Checked structural and adjacent-level parts of the separation witness,
including the source's eventual sample-fresh positive guarantee.  The stronger
output-novelty and quarter-density conjuncts of `UncountableSeparation` remain
the only missing pieces. -/
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
  refine ⟨finiteOmissionClass q,
    finiteOmissionClass_uncountable q,
    finiteOmissionClass_infinite q, ?_,
    finiteOmissionClass_level_succ_failure q⟩
  obtain ⟨gen, hgen⟩ := finiteNoiseLevel_upper q
  refine ⟨gen, ?_⟩
  intro K hK input hinput
  obtain ⟨T, hT⟩ := hgen K hK input hinput
  refine ⟨T, ?_⟩
  intro t ht
  have hcorrect := hT t ht
  exact hcorrect

end Stage3Case019
