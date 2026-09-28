import Case019Foundations
import DensityScratch
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency

namespace Stage3Case019Proof

open Stage3Case019
open GenLimit
open GenLimit.Generic

private theorem finiteContamination_of_atMost
    {input : ℕ → ℕ} {K : Set ℕ} {q : ℕ}
    (hinput : InjectiveValueContaminatedPresentationAtMost input K q) :
    InfiniteContamination.FiniteNoiseFiniteOmissionEnumeration input K := by
  refine ⟨hinput.1, ?_, ?_⟩
  · exact
      (InfiniteContamination.finiteNoise_iff_valuesOutside_finite_of_injective
        hinput.1).mpr
        ((setDifferenceAtMost_iff_finite_ncard_le
          (Set.range input) K q).mp hinput.2.2).1
  · unfold InfiniteContamination.FiniteOmissions
    rw [Set.diff_eq_empty.mpr hinput.2.1]
    exact Set.finite_empty

private theorem patient_novel_transfer
    {O : OracleFamily} {input : ℕ → ℕ} {j : ℕ} {K : Set ℕ}
    (hK : K ⊆ O.language j)
    (hfinite : (O.language j \ K).Finite)
    (hseen : O.language j \ K ⊆ Set.range input)
    (hpatient :
      ∃ T, ∀ t, T ≤ t →
        PatientMachine.output O input t ∈ O.language j ∧
        (∀ s, s ≤ t → input s ≠ PatientMachine.output O input t) ∧
        (∀ s, s < t → PatientMachine.output O input s ≠
          PatientMachine.output O input t)) :
    NovelGeneratesInLimit input
      (outputAfterInput (patientGenerator O) input) K := by
  classical
  obtain ⟨Tpatient, hTpatient⟩ := hpatient
  obtain ⟨Tseen, hTseen⟩ :=
    finset_eventually_subset_sample
      (InfiniteContamination.stream_presents_range input)
      hfinite.toFinset (by
        intro x hx
        exact hseen ((Set.Finite.mem_toFinset hfinite).mp hx))
  refine ⟨max Tpatient Tseen, ?_⟩
  intro t ht
  have hp := hTpatient t ((Nat.le_max_left _ _).trans ht)
  have hs : hfinite.toFinset ⊆ Generic.sample input (t + 1) := by
    intro x hx
    exact Generic.sample_mono
      ((Nat.le_max_right _ _).trans ht |>.trans (Nat.le_succ t))
      (hTseen hx)
  rw [outputAfterInput_patientGenerator]
  refine ⟨?_, ?_, ?_⟩
  · by_contra hout
    have hbad : PatientMachine.output O input t ∈ hfinite.toFinset :=
      (Set.Finite.mem_toFinset hfinite).mpr ⟨hp.1, hout⟩
    obtain ⟨s, hsle, heq⟩ := Generic.mem_sample_iff.mp (hs hbad)
    exact hp.2.1 s (by omega) heq
  · intro hsample
    obtain ⟨s, hsle, heq⟩ := GenLimit.mem_sample_iff.mp hsample
    exact hp.2.1 s (by omega) heq
  · simpa only [outputAfterInput_patientGenerator] using hp.2.2

/-- Countable-family half density at every finite contamination level. -/
theorem stage3_countable_half_density : CountableClause := by
  intro q family hinf
  let O := familyOracle family hinf
  let E := InfiniteContamination.finiteExpansionOracleFamily O
  refine ⟨patientGenerator E, ?_⟩
  intro i input hinput
  have hcontam := finiteContamination_of_atMost hinput
  obtain ⟨j, hjbase, hjPresents⟩ :=
    InfiniteContamination.exists_finiteExpansion_index_for_stream O hcontam
  have hpatient :=
    PatientMachine.patientScope_generation_and_lowerDensity E input hjPresents
  have hKsubsetRange : family i ⊆ Set.range input := hinput.2.1
  have hRangeDiff : (Set.range input \ family i).Finite :=
    ((setDifferenceAtMost_iff_finite_ncard_le
      (Set.range input) (family i) q).mp hinput.2.2).1
  have hnovel : NovelGeneratesInLimit input
      (outputAfterInput (patientGenerator E) input) (family i) := by
    apply patient_novel_transfer
        (O := E) (j := j) (K := family i)
    · rw [← hjPresents]
      exact hKsubsetRange
    · rw [← hjPresents]
      exact hRangeDiff
    · rw [← hjPresents]
      exact Set.diff_subset
    · exact hpatient.1
  refine ⟨hnovel, ?_⟩
  have hdensityTransfer := relativeLowerDensity_inter_of_subset_finite
    (G := GeneratorFirst input (PatientMachine.output E input))
    (E := E.language j) (K := family i) (hinf i)
    (by rw [← hjPresents]; exact hKsubsetRange)
    (by rw [← hjPresents]; exact hRangeDiff)
  have houtEq :
      outputAfterInput (patientGenerator E) input =
        PatientMachine.output E input := by
    funext t
    exact outputAfterInput_patientGenerator E input t
  rw [houtEq]
  exact hpatient.2.trans hdensityTransfer

end Stage3Case019Proof
