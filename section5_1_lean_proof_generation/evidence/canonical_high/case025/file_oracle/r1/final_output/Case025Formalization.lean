import Transfer

open Set Filter

namespace Stage3Case025Formalization

noncomputable section

/-- Finite occurrence noise is transferred through the coded family of all
finite expansions, without requiring the input stream to be injective. -/
theorem finiteNoiseTransfer : Stage3Case025.FiniteNoiseTransferPrinciple := by
  intro hPositive family hInfinite
  let O := oracleOfFamily family hInfinite
  let expanded :=
    GenLimit.InfiniteContamination.finiteExpansionOracleFamily O
  obtain ⟨gen, hgen⟩ := hPositive expanded.language expanded.infinite'
  refine ⟨gen, ?_⟩
  intro i input hPresentation
  obtain ⟨j, hPresents⟩ :=
    exists_expansion_index_for_occurrence_presentation
      O (z := i) (input := input) (by
        change family i ⊆ Set.range input
        exact hPresentation.1) hPresentation.2
  obtain ⟨output, hFollows, hNovelExpanded, hDensityExpanded⟩ :=
    hgen j input hPresents
  refine ⟨output, hFollows, ?_, ?_⟩
  · have hfinite : (Set.range input \ family i).Finite :=
      GenLimit.InfiniteContamination.displayedNoise_finite hPresentation.2
    have hNovelRange :
        GenLimit.NovelGeneratesInLimit input output (Set.range input) := by
      rw [hPresents]
      exact hNovelExpanded
    exact novelGeneratesInLimit_of_finite_extraneous
      hfinite (fun _ hx => hx.1) hNovelRange
  · have hfinite : (Set.range input \ family i).Finite :=
      GenLimit.InfiniteContamination.displayedNoise_finite hPresentation.2
    have hDensityRange :
        (1 / 2 : ℝ) ≤
          GenLimit.PatientScope.relativeLowerDensity
            (GenLimit.GeneratorFirst input output ∩ Set.range input)
            (Set.range input) := by
      rw [hPresents]
      exact hDensityExpanded
    exact hDensityRange.trans
      (relativeLowerDensity_of_finite_extension
        (hInfinite i) hPresentation.1 hfinite)

end

end Stage3Case025Formalization

/-- Primary endpoint: presentation-dependent half-density under finite
occurrence-counted contamination. -/
theorem stage3_result : Stage3Case025.MainClaim := by
  exact Stage3Case025Formalization.finiteNoiseTransfer
    Stage3Case025Formalization.positiveEngine
