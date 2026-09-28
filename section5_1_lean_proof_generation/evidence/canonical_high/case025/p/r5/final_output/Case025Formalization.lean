import Case025Helpers

open Stage3Case025

/-- Every local online rule has a canonical trajectory. -/
theorem stage3_trajectory_exists (gen : OnlineGenerator) (input : Stream) :
    ∃ output, Follows gen input output := by
  exact ⟨Case025.trajectory gen input, Case025.trajectory_follows gen input⟩

/-- Checked finite-contamination reduction.  Starting from the positive engine,
this supplies eventual novel generation in the original target and retains the
half-density estimate on the actual input range.  The remaining analytic step
is invariance of relative lower density under deleting finitely many values. -/
theorem stage3_finite_noise_reduction : Case025.FiniteNoiseTransferWithoutDensity := by
  exact Case025.finite_noise_transfer_without_density
