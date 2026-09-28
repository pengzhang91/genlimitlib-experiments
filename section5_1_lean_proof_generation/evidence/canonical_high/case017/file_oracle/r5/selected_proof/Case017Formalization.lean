import Case017Helpers

open Stage3Case017Proof

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hfamily
  refine ⟨familyGenerator family, ?_⟩
  intro input hinj hexists hcore
  refine ⟨trajectory (familyGenerator family) input,
    trajectory_follows (familyGenerator family) input, ?_⟩
  intro j hj
  exact ⟨novelGeneratesInLimit family input hcore hj,
    density_bound family hfamily input hinj hcore hj⟩
