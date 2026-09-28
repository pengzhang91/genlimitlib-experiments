import Helpers

open Stage3Case025

/-- The finite-occurrence-noise reduction is checked through eventual target
validity and the positive engine's density guarantee on the finite extension.
The remaining step is finite-extension invariance of relative lower density. -/
theorem stage3_finite_noise_reduction_checked
    (hpositive : PositivePresentationHalfDensity) :
    ∀ family : ℕ → Language, (∀ i, (family i).Infinite) →
      ∃ gen : OnlineGenerator,
        ∀ i (input : Stream),
          CompleteFiniteOccurrencePresentation input (family i) →
            ∃ output : Stream, ∃ E : Language,
              E.Finite ∧
              Follows gen input output ∧
              GenLimit.NovelGeneratesInLimit input output (family i) ∧
              (1 / 2 : ℝ) ≤
                GenLimit.PatientScope.relativeLowerDensity
                  (GenLimit.GeneratorFirst input output ∩ (family i ∪ E))
                  (family i ∪ E) := by
  exact positive_engine_finite_noise_reduction hpositive
