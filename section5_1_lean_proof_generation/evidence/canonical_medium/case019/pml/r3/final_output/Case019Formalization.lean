import Stage3Model
import output.PrefixCausality
import output.Negative
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteOmissionSeparation

open Set Filter
open Stage3Case019

namespace Stage3Case019Proof

/-- The supplied P12 separating class consists entirely of infinite languages. -/
theorem finiteOmissionClass_all_infinite (q : ℕ) :
    ∀ K ∈ GenLimit.NoiseLossFeedback.finiteOmissionClass q, K.Infinite := by
  exact GenLimit.NoiseLossFeedback.finiteOmissionClass_uus q

/-- Checked negative half of the requested adjacent-level separation, for the
exact extensional P12 class and the exact stage-3 semantic timing convention. -/
theorem adjacent_level_failure (q : ℕ) :
    ∀ gen : Generator ℤ,
      ∃ K ∈ GenLimit.NoiseLossFeedback.finiteOmissionClass q,
        ∃ input : Stream ℤ,
          GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
              input K (q + 1) ∧
            ¬ SampleFreshGeneratesAfterInput
              input (outputAfterInput gen input) K :=
  finiteOmission_negative_clause q

end Stage3Case019Proof
