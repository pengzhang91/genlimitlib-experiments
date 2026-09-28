import Stage3Model
import Case017Helpers

open Set

noncomputable section

 theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hinfinite
  refine ⟨Stage3Case017Proof.onlineGenerator family, ?_⟩
  intro input hinjective hpartial hcore
  let output := Stage3Case017Proof.trajectory
    (Stage3Case017Proof.onlineGenerator family) input
  refine ⟨output, Stage3Case017Proof.trajectory_follows _ _, ?_⟩
  intro j hj
  refine ⟨Stage3Case017Proof.trajectory_novel family input hcore j hj, ?_⟩
  apply max_le
  · exact Stage3Case017Proof.half_core_density family input hcore j hj
  · exact Stage3Case017Proof.never_presented_density family input hcore j hj
