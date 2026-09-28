import DensityPartial

open Stage3Case019

/-- Checked partial milestone for the positive half of the separation clause:
at every finite noise level there is an uncountable extensional family of
infinite integer languages with one uniform generator that is valid and novel
on every legal presentation and has balanced relative lower density at least
one quarter.  The adjacent-level impossibility is not asserted here. -/
theorem stage3_uncountable_quarter_density_partial :
    ∀ q : ℕ,
      ∃ family : LanguageClass ℤ,
        ¬family.Countable ∧
        (∀ K ∈ family, K.Infinite) ∧
        ∃ gen : Generator ℤ,
          ∀ K ∈ family, ∀ input : Stream ℤ,
            GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q →
              NovelGeneratesAfterInput input (outputAfterInput gen input) K ∧
              (1 / 4 : ℝ) ≤ balancedRelativeLowerDensity
                (GeneratorFirstOn input (outputAfterInput gen input) ∩ K) K := by
  intro q
  refine ⟨Case019.commonHalfFamily,
    Case019.commonHalfFamily_uncountable,
    Case019.commonHalfFamily_infinite, ?_⟩
  obtain ⟨gen, hgen⟩ := Case019.commonHalfFamily_uniform_quarter
  refine ⟨gen, ?_⟩
  intro K hK input _
  exact hgen K hK input
