import Helpers

open Stage3Case025

/-- Checked partial result: the positive-presentation engine, applied to the
family closed under finite extensions, supplies one generator that is
ultimately valid for the original target.  Its certified density statement is
still relative to the finite extension; removing that finite perturbation from
`relativeLowerDensity` is the remaining transfer lemma. -/
theorem stage3_finite_extension_reduction
    (hpositive : PositivePresentationHalfDensity) :
    ∀ family : ℕ → Language, (∀ i, (family i).Infinite) →
      ∃ gen : OnlineGenerator,
        ∀ i (input : Stream),
          CompleteFiniteOccurrencePresentation input (family i) →
            let E := noiseValues input (family i)
            ∃ output : Stream,
              Follows gen input output ∧
              GenLimit.NovelGeneratesInLimit input output (family i) ∧
              (1 / 2 : ℝ) ≤
                GenLimit.PatientScope.relativeLowerDensity
                  (GenLimit.GeneratorFirst input output ∩ (family i ∪ E))
                  (family i ∪ E) := by
  intro family hinf
  obtain ⟨gen, hgen⟩ := positive_engine_on_finite_extensions hpositive family hinf
  refine ⟨gen, ?_⟩
  intro i input hpresent
  dsimp
  obtain ⟨output, hfollows, hnovel, hdensity⟩ := hgen i input hpresent
  have hE : (noiseValues input (family i)).Finite := noiseValues_finite hpresent.2
  exact ⟨output, hfollows, novel_remove_finite hE hnovel, hdensity⟩
