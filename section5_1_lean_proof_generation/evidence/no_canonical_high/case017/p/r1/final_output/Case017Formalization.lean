import Stage3Model
import Case017Helpers

open Set Filter
open scoped Topology

open Case017Proof

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hfamily
  refine ⟨familyGenerator family, ?_⟩
  intro input hinj hpresentation hcore
  obtain ⟨T, hstable⟩ := exists_stable_time family input
  let output := trajectory (familyGenerator family) input
  refine ⟨output, trajectory_follows (familyGenerator family) input, ?_⟩
  intro j hj
  refine ⟨novel_after_stable family input hcore hstable j hj, ?_⟩
  apply max_le
  · exact half_core_density_le family input hinj hcore hstable j hj (hfamily j)
  · exact unseen_density_le family input hcore hstable j hj
