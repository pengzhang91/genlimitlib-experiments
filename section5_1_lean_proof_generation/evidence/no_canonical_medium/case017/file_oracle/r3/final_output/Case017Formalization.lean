import Stage3Model
import Helpers

open Stage3Case017

open Stage3Case017Proof

noncomputable section

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hfamily
  refine ⟨greedyGenerator family, ?_⟩
  intro input hinj hpresentation hcore
  let output := trajectory (greedyGenerator family) input
  refine ⟨output, trajectory_follows (greedyGenerator family) input, ?_⟩
  intro j hj
  constructor
  · exact eventual_novel family input hcore j hj
  · apply max_le
    · exact half_core_density family input hinj hcore j hj (hfamily j)
    · apply relativeLowerDensity_mono
      · intro z hz
        constructor
        · exact missing_core_subset_generatorFirst family input hcore hz
        · exact hz.1 j hj
      · exact Set.inter_subset_right
