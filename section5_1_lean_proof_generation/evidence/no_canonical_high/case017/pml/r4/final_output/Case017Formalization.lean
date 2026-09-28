import Stage3Model
import Case017Helpers

open Stage3Case017

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hfamily
  refine ⟨Stage3Case017Proof.greedyGenerator family, ?_⟩
  intro input hinputInjective hpresentation hcore
  let output := Stage3Case017Proof.trajectory
    (Stage3Case017Proof.greedyGenerator family) input
  refine ⟨output, Stage3Case017Proof.trajectory_follows _ _, ?_⟩
  intro j hinputK
  have hcoreK : informationCore family input ⊆ family j := by
    intro x hx
    exact hx j hinputK
  constructor
  · exact Stage3Case017Proof.greedy_novel_generates
      family input hcore (family j) hcoreK
  · exact Stage3Case017Proof.density_max_bound
      family input hcore (family j) hinputK hcoreK (hfamily j)
