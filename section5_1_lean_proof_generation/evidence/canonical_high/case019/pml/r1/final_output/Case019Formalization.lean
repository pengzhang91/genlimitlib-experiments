import Countable
import Helpers
import Separation

open Set

namespace Stage3Case019

open GenLimit.Generic
open GenLimit.NoiseLossFeedback

/-- The complete countable-family half-density component of Case 019. -/
theorem stage3_countable_half_density : CountableClause :=
  countable_half_density

/-- All separation requirements except the balanced-order quarter-density
estimate.  In particular, the positive generator is globally output-fresh,
not merely sample-fresh. -/
theorem stage3_uncountable_separation_without_density :
    ∀ q, ∃ family : LanguageClass ℤ,
      ¬family.Countable ∧
        (∀ K ∈ family, K.Infinite) ∧
        (∃ gen : Generator ℤ,
          ∀ K ∈ family, ∀ input : Stream ℤ,
            InjectiveValueContaminatedPresentationAtMost input K q →
              NovelGeneratesAfterInput
                input (outputAfterInput gen input) K) ∧
        (∀ gen : Generator ℤ,
          ∃ K ∈ family, ∃ input : Stream ℤ,
            InjectiveValueContaminatedPresentationAtMost input K (q + 1) ∧
              ¬SampleFreshGeneratesAfterInput
                input (outputAfterInput gen input) K) := by
  intro q
  refine ⟨finiteOmissionClass q,
    finiteOmissionClass_uncountable q,
    finiteOmissionClass_uus q,
    ?_, finiteOmissionClass_adjacent_failure q⟩
  exact ⟨strictHalfGenerator q, fun K hK input hinput =>
    strictHalfGenerator_novel q hK hinput⟩

end Stage3Case019
