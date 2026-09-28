import Case017Helpers

open Stage3Case017
open Stage3Case017Proof

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hFamilyInfinite
  refine ⟨coreGenerator family, ?_⟩
  intro input hInjective hCompatible hCoreInfinite
  let output := run (coreGenerator family) input
  have hFollows : Follows (coreGenerator family) input output :=
    run_follows (coreGenerator family) input
  refine ⟨output, hFollows, ?_⟩
  intro j hStream
  refine ⟨eventual_novel family input output hFollows hCoreInfinite hStream, ?_⟩
  exact density_bounds family hFamilyInfinite input output hInjective
    hFollows hCoreInfinite hStream
