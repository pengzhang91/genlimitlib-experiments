import AnalyticProof

open Set Filter
open scoped Topology

namespace Stage3Case017

noncomputable section

lemma generatorFirst_inter_core_subset_target {m : ℕ}
    {family : Fin m → Language} {input : Stream} {j : Fin m}
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.GeneratorFirst input (trajectory (greedyGenerator family) input) ∩
        informationCore family input ⊆ family j := by
  intro z hz
  exact informationCore_subset hj hz.2

lemma generatorFirst_inter_core_subset_generatorFirst_inter_target {m : ℕ}
    {family : Fin m → Language} {input : Stream} {j : Fin m}
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.GeneratorFirst input (trajectory (greedyGenerator family) input) ∩
        informationCore family input ⊆
      GenLimit.GeneratorFirst input (trajectory (greedyGenerator family) input) ∩
        family j := by
  intro z hz
  exact ⟨hz.1, informationCore_subset hj hz.2⟩

lemma core_diff_range_subset_generatorFirst_inter_target {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite) {j : Fin m}
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (trajectory (greedyGenerator family) input) ∩
        family j := by
  intro z hz
  exact ⟨core_diff_range_subset_generatorFirst family input hcore hz,
    informationCore_subset hj hz.1⟩

end

end Stage3Case017

open Set Filter
open scoped Topology

 theorem stage3_result : Stage3Case017.MainClaim := by
  intro m _ family hfamily
  refine ⟨Stage3Case017.greedyGenerator family, ?_⟩
  intro input _ _ hcore
  refine ⟨Stage3Case017.trajectory (Stage3Case017.greedyGenerator family) input,
    Stage3Case017.trajectory_follows _ _, ?_⟩
  intro j hj
  refine ⟨Stage3Case017.greedy_novel family input hcore j hj, ?_⟩
  apply max_le
  · let I := Stage3Case017.informationCore family input
    let D := GenLimit.GeneratorFirst input
      (Stage3Case017.trajectory (Stage3Case017.greedyGenerator family) input)
    have hIK : I ⊆ family j := Stage3Case017.informationCore_subset hj
    have hDIK : D ∩ I ⊆ family j :=
      Stage3Case017.generatorFirst_inter_core_subset_target hj
    have hhalf :
        (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity I (family j) ≤
          GenLimit.PatientScope.relativeLowerDensity (D ∩ I) (family j) := by
      apply Stage3Case017.half_density_le_of_prefix_bound hIK hDIK (hfamily j)
      intro n
      simpa only [I, D, Nat.add_assoc] using
        Stage3Case017.core_prefix_count_le family input hcore n
    exact hhalf.trans
      (Stage3Case017.relativeLowerDensity_mono
        (Stage3Case017.generatorFirst_inter_core_subset_generatorFirst_inter_target hj)
        Set.inter_subset_right)
  · exact Stage3Case017.relativeLowerDensity_mono
      (Stage3Case017.core_diff_range_subset_generatorFirst_inter_target
        family input hcore hj)
      Set.inter_subset_right
