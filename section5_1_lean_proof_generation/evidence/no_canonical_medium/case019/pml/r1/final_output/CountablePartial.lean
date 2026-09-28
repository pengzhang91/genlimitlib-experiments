import output.PatientAdapter
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency

open Set Filter
open GenLimit.Generic
open Stage3Case019

namespace Stage3Case019

open GenLimit
open GenLimit.InfiniteContamination
open GenLimit.PatientMachine

noncomputable def familyOracle
    (family : LanguageFamily ℕ) (hinfinite : ∀ i, (family i).Infinite) :
    OracleFamily where
  language := family
  infinite' := hinfinite
  query i x := by
    classical
    exact if x ∈ family i then true else false
  query_spec i x := by
    classical
    simp

private theorem finiteContamination_of_stage3
    {input : Stream ℕ} {K : Language ℕ} {q : ℕ}
    (h : InjectiveValueContaminatedPresentationAtMost input K q) :
    FiniteNoiseFiniteOmissionEnumeration input K := by
  refine ⟨h.1, ?_, ?_⟩
  · rw [finiteNoise_iff_valuesOutside_finite_of_injective h.1]
    exact (setDifferenceAtMost_iff_finite_ncard_le _ _ _).mp h.2.2 |>.1
  · apply Set.finite_empty.subset
    intro x hx
    exact hx.2 (h.2.1 hx.1)

 theorem countable_expansion_patient
    (q : ℕ) (family : LanguageFamily ℕ)
    (hinfinite : ∀ i, (family i).Infinite) :
    ∃ gen : Generator ℕ,
      ∀ i (input : Stream ℕ),
        InjectiveValueContaminatedPresentationAtMost input (family i) q →
          ∃ j,
            finiteExpansionBaseIndex j = i ∧
            GenLimit.Generic.Presents input ((finiteExpansionOracleFamily
              (familyOracle family hinfinite)).language j) ∧
            NovelGeneratesInLimit input (outputAfterInput gen input)
              ((finiteExpansionOracleFamily
                (familyOracle family hinfinite)).language j) ∧
            (1 / 2 : ℝ) ≤ PatientScope.relativeLowerDensity
              (GeneratorFirst input (outputAfterInput gen input) ∩
                (finiteExpansionOracleFamily
                  (familyOracle family hinfinite)).language j)
              ((finiteExpansionOracleFamily
                (familyOracle family hinfinite)).language j) := by
  let O := finiteExpansionOracleFamily (familyOracle family hinfinite)
  refine ⟨patientGenerator O, ?_⟩
  intro i input hinput
  have hcontam := finiteContamination_of_stage3 hinput
  obtain ⟨j, hj, hpresents⟩ :=
    exists_finiteExpansion_index_for_stream
      (familyOracle family hinfinite) hcontam
  refine ⟨j, hj, hpresents, ?_, ?_⟩
  · obtain ⟨⟨T, hT⟩, _⟩ :=
      patientScope_generation_and_lowerDensity O input hpresents
    refine ⟨T, ?_⟩
    intro t ht
    have hs := hT t ht
    refine ⟨?_, ?_, ?_⟩
    · rw [outputAfterInput_patientGenerator]
      exact hs.1
    · rw [outputAfterInput_patientGenerator]
      intro hmem
      obtain ⟨s, hslt, hse⟩ := GenLimit.mem_sample_iff.mp hmem
      exact hs.2.1 s (by omega) hse
    · simpa only [outputAfterInput_patientGenerator] using hs.2.2
  · have hd :=
      (patientScope_generation_and_lowerDensity O input hpresents).2
    change (1 / 2 : ℝ) ≤ PatientScope.relativeLowerDensity
      (GeneratorFirst input (outputAfterInput (patientGenerator O) input) ∩
        O.language j) (O.language j)
    have hout : outputAfterInput (patientGenerator O) input =
        PatientMachine.output O input := by
      funext t
      exact outputAfterInput_patientGenerator O input t
    rw [hout]
    exact hd

end Stage3Case019
