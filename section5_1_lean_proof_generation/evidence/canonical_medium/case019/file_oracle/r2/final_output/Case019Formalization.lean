import «output».SeparationPartial

/-- Fully checked first component of the Case 019 target. -/
theorem stage3_countable_half_density : Stage3Case019.CountableClause :=
  Stage3Case019.stage3_countable_half_density

/-- Fully checked adjacent-level negative component for the P12 witness class. -/
theorem stage3_adjacent_noise_failure (q : ℕ) :
    ∀ gen : Stage3Case019.Generator ℤ,
      ∃ K ∈ GenLimit.NoiseLossFeedback.finiteOmissionClass q,
        ∃ input : Stage3Case019.Stream ℤ,
          GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
              input K (q + 1) ∧
            ¬Stage3Case019.SampleFreshGeneratesAfterInput
              input (Stage3Case019.outputAfterInput gen input) K :=
  Stage3Case019.finiteOmissionClass_adjacent_failure q
