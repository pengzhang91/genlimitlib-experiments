import DensitySweep

namespace Stage3Case019

open GenLimit
open GenLimit.Generic
open GenLimit.NoiseLossFeedback

theorem stage3_uncountable_separation : SeparationClause := by
  intro q
  refine ⟨finiteOmissionClass q, finiteOmissionClass_uncountable q,
    finiteOmissionClass_uus q, ?_, finiteOmissionClass_negative q⟩
  refine ⟨PairSweep.generator q, ?_⟩
  intro K hK input hinput
  rcases hK with hfirst | hsecond
  · exact ⟨PairSweep.first_novel_valid hfirst hinput,
      PairSweep.first_density hfirst hinput⟩
  · exact ⟨PairSweep.second_novel_valid hsecond hinput,
      PairSweep.second_density hsecond hinput⟩

end Stage3Case019
