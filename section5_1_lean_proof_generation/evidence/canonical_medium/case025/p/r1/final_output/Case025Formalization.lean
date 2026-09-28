import Case025Helpers

open Stage3Case025

/-- Checked finite-contamination reduction used by the canonical transfer:
every admissible stream exactly presents a member of the fixed finite-extension
closure of the original indexed family. -/
theorem stage3_finite_extension_reduction
    (family : ℕ → Language) (i : ℕ) (input : Stream)
    (hp : CompleteFiniteOccurrencePresentation input (family i)) :
    ∃ j, GenLimit.Presents input (Case025.finiteExtensionFamily family j) := by
  exact Case025.presents_some_finiteExtension family hp

/-- Checked validity portion of the finite-noise transfer. -/
theorem stage3_novel_finite_noise_transfer
    {input output : Stream} {R K : Language}
    (hnovel : GenLimit.NovelGeneratesInLimit input output R)
    (hfinite : (R \ K).Finite) :
    GenLimit.NovelGeneratesInLimit input output K := by
  exact Case025.novel_of_novel_of_finite_diff hnovel hfinite
