import Stage3Model
import Case017Helpers

open Set

open Stage3Case017
open Stage3Case017Proof

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m _ family hInfinite
  refine ⟨familyGenerator family, ?_⟩
  intro input hInjective _ hCoreInfinite
  refine ⟨run family input, run_follows family input, ?_⟩
  intro j hStream
  constructor
  · obtain ⟨T, hTrace⟩ :=
      run_eventually_core_fresh family input hCoreInfinite
    refine ⟨T, ?_⟩
    intro t ht
    have hAt := hTrace t ht
    refine ⟨?_, ?_, hAt.2.2⟩
    · exact (hAt.1 j hStream)
    · simpa [GenLimit.sample, GenLimit.Generic.sample] using hAt.2.1
  · exact target_density_bounds family input hInjective hCoreInfinite
      j (hInfinite j) hStream
