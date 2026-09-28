import DensityTransfer

open Set

namespace Stage3Case025

open GenLimit.PatientScope

/-- The finite-addition transfer from the supplied canonical proof. -/
theorem finite_noise_transfer_checked : FiniteNoiseTransferPrinciple := by
  intro hpositive family hinfinite
  obtain ⟨gen, hgen⟩ :=
    hpositive (finiteExpansion family) (finiteExpansion_infinite family hinfinite)
  refine ⟨gen, ?_⟩
  intro i input hpresentation
  obtain ⟨n, hpresents⟩ := noisy_range_is_expansion family i input hpresentation
  obtain ⟨output, hfollows, hnovel, hdensity⟩ := hgen n input hpresents
  refine ⟨output, hfollows, ?_, ?_⟩
  · have hKR : family i ⊆ finiteExpansion family n := by
      intro x hx
      rw [← hpresents]
      exact hpresentation.1 hx
    have hfin : (finiteExpansion family n \ family i).Finite := by
      rw [← hpresents]
      exact range_diff_finite_of_finitelyManyViolations input (family i) hpresentation.2
    exact novelGeneratesInLimit_of_subset_finite_diff
      input output (family i) (finiteExpansion family n) hKR hfin hnovel
  · have hKR : family i ⊆ finiteExpansion family n := by
      intro x hx
      rw [← hpresents]
      exact hpresentation.1 hx
    have hfin : (finiteExpansion family n \ family i).Finite := by
      rw [← hpresents]
      exact range_diff_finite_of_finitelyManyViolations input (family i) hpresentation.2
    exact hdensity.trans (finite_extension_density_le
      (GenLimit.GeneratorFirst input output) (family i)
      (finiteExpansion family n) (hinfinite i) hKR hfin)

end Stage3Case025
