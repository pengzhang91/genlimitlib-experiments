import Helpers

open Set

open Stage3Case017

open Case017

 theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hfamily
  refine ⟨onlineGen family, ?_⟩
  intro input hinj _ hInf
  let output := trajectory (onlineGen family) input
  refine ⟨output, trajectory_follows (onlineGen family) input, ?_⟩
  intro j hj
  constructor
  · refine ⟨stabilizationTime hm family input, ?_⟩
    intro t ht
    refine ⟨?_, onlineGen_not_input family input t, ?_⟩
    · exact informationCore_subset family input hj
        (onlineGen_mem_core hm family input hInf ht)
    · intro s hs
      exact onlineGen_ne_previous family input hs
  · apply max_le
    · exact half_core_density hm family hfamily input hinj hInf hj
    · apply relativeLowerDensity_mono
      · intro z hz
        refine ⟨unpresented_core_subset_generatorFirst hm family input hInf hz, ?_⟩
        exact informationCore_subset family input hj hz.1
      · exact Set.inter_subset_right
