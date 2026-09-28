import Stage3Model
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation

open Set
open Stage3Case019

namespace Case019

noncomputable def oracleOfFamily
    (family : LanguageFamily ℕ) (hinf : ∀ i, (family i).Infinite) :
    GenLimit.OracleFamily where
  language := family
  infinite' := hinf
  query i x := by classical exact if x ∈ family i then true else false
  query_spec i x := by classical simp

/-- A bounded injective value-contaminated presentation is a finite-noise,
finite-omission presentation in the P17 interface. -/
theorem finiteContamination_of_bounded
    {input : Stream ℕ} {K : Language ℕ} {q : ℕ}
    (h : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
      input K q) :
    GenLimit.InfiniteContamination.FiniteNoiseFiniteOmissionEnumeration
      input K := by
  refine ⟨h.1, ?_, ?_⟩
  · apply (GenLimit.Generic.finite_valuesOutside_iff_finitelyManyViolations_of_injective
      h.1).mp
    exact ((GenLimit.Generic.setDifferenceAtMost_iff_finite_ncard_le _ _ _).mp h.2.2).1
  · unfold GenLimit.InfiniteContamination.FiniteOmissions
    rw [Set.diff_eq_empty.mpr h.2.1]
    exact Set.finite_empty

/-- Every legal input in the countable clause is an exact presentation of a
member of the supplied finite-expansion family. -/
theorem exists_exact_finiteExpansion
    (family : LanguageFamily ℕ) (hinf : ∀ i, (family i).Infinite)
    {i q : ℕ} {input : Stream ℕ}
    (h : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
      input (family i) q) :
    ∃ j,
      GenLimit.InfiniteContamination.finiteExpansionBaseIndex j = i ∧
      GenLimit.Generic.Presents input
        ((GenLimit.InfiniteContamination.finiteExpansionOracleFamily
          (oracleOfFamily family hinf)).language j) := by
  exact GenLimit.InfiniteContamination.exists_finiteExpansion_index_for_stream
    (oracleOfFamily family hinf) (finiteContamination_of_bounded h)

/-- The P12 sweep generator supplies the exact inclusive-time sample-fresh
positive guarantee needed by the separation statement, before adding its
extra output-novelty and density obligations. -/
theorem finiteOmissionClass_sampleFresh_upper (q : ℕ) :
    ∃ gen : Generator ℤ,
      ∀ K ∈ GenLimit.NoiseLossFeedback.finiteOmissionClass q,
        ∀ input : Stream ℤ,
          GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
              input K q →
            SampleFreshGeneratesAfterInput
              input (outputAfterInput gen input) K := by
  obtain ⟨gen, hgen⟩ :=
    GenLimit.NoiseLossFeedback.finiteNoiseLevel_upper q
  refine ⟨gen, ?_⟩
  intro K hK input hinput
  have h := hgen K hK input hinput
  simpa [SampleFreshGeneratesAfterInput, outputAfterInput,
    GenLimit.NoiseLossFeedback.CorrectAt,
    GenLimit.NoiseLossFeedback.outputAt,
    GenLimit.NoiseLossFeedback.observedThrough] using h

/-- Exact adjacent-level impossibility in the predicates of `Stage3Model`.
This is the complete negative conjunct required of the eventual separating
family. -/
theorem finiteOmissionClass_sampleFresh_lower (q : ℕ) :
    ∀ gen : Generator ℤ,
      ∃ K ∈ GenLimit.NoiseLossFeedback.finiteOmissionClass q,
        ∃ input : Stream ℤ,
          GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
              input K (q + 1) ∧
            ¬SampleFreshGeneratesAfterInput
              input (outputAfterInput gen input) K := by
  classical
  intro gen
  by_contra hcounter
  apply GenLimit.NoiseLossFeedback.finiteNoiseLevel_lower q
  refine ⟨gen, ?_⟩
  intro K hK input hinput
  have hfresh : SampleFreshGeneratesAfterInput
      input (outputAfterInput gen input) K := by
    by_contra hfail
    apply hcounter
    exact ⟨K, hK, input, hinput, hfail⟩
  simpa [SampleFreshGeneratesAfterInput, outputAfterInput,
    GenLimit.NoiseLossFeedback.CorrectAt,
    GenLimit.NoiseLossFeedback.outputAt,
    GenLimit.NoiseLossFeedback.observedThrough] using hfresh

/-- All languages in the supplied adjacent-level witness are infinite. -/
theorem finiteOmissionClass_infinite (q : ℕ) :
    ∀ K ∈ GenLimit.NoiseLossFeedback.finiteOmissionClass q, K.Infinite :=
  GenLimit.NoiseLossFeedback.finiteOmissionClass_uus q

end Case019
