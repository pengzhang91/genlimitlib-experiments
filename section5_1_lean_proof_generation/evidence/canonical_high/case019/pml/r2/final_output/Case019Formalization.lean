import Stage3Model
import Case019Helpers

open Set Filter
open GenLimit GenLimit.Generic
open Case019Helpers
open Stage3Case019

theorem stage3_countable_half_density : CountableClause := by
  intro q family hInfinite
  classical
  let O := oracleOfFamily family hInfinite
  let E := InfiniteContamination.finiteExpansionOracleFamily O
  refine ⟨patientGenerator E, ?_⟩
  intro i input hinput
  have hcontam := finiteNoiseFiniteOmission_of_injectiveValueContaminated hinput
  obtain ⟨j, hjbase, hjPresents⟩ :=
    InfiniteContamination.exists_finiteExpansion_index_for_stream O hcontam
  have hpatient := PatientMachine.patientScope_generation_and_lowerDensity
    E input hjPresents
  rcases hpatient with ⟨⟨T, hT⟩, hdensity⟩
  have hdiff : (E.language j \ family i).Finite := by
    have h := finiteExpansion_diff_base_finite O j
    simpa [O, hjbase] using h
  obtain ⟨Tbad, hTbad⟩ :=
    eventually_patientOutput_not_mem_finite E input hdiff
  have hnovel : NovelGeneratesInLimit input
      (outputAfterInput (patientGenerator E) input) (family i) := by
    refine ⟨max T Tbad, ?_⟩
    intro t ht
    have htT : T ≤ t := le_trans (Nat.le_max_left _ _) ht
    have htBad : Tbad ≤ t := le_trans (Nat.le_max_right _ _) ht
    obtain ⟨hmemE, hfresh, hnew⟩ := hT t htT
    have hnotDiff := hTbad t htBad
    have hmemK : PatientMachine.output E input t ∈ family i := by
      by_contra hnotK
      exact hnotDiff ⟨hmemE, hnotK⟩
    rw [outputAfterInput_patientGenerator]
    refine ⟨hmemK, ?_, hnew⟩
    intro hsamp
    obtain ⟨s, hs, heq⟩ := GenLimit.mem_sample_iff.mp hsamp
    exact hfresh s (by omega) heq
  refine ⟨hnovel, ?_⟩
  have htargetSub : family i ⊆ E.language j := by
    rw [← hjPresents]
    exact hinput.2.1
  have hsourceSub :
      GeneratorFirst input (PatientMachine.output E input) ∩ E.language j ⊆
        E.language j := inter_subset_right
  have houtputSub :
      GeneratorFirst input (PatientMachine.output E input) ∩ family i ⊆
        family i := inter_subset_right
  have hnumDiff :
      ((GeneratorFirst input (PatientMachine.output E input) ∩ E.language j) \
        (GeneratorFirst input (PatientMachine.output E input) ∩ family i)).Finite := by
    apply hdiff.subset
    intro x hx
    exact ⟨hx.1.2, fun hxK => hx.2 ⟨hx.1.1, hxK⟩⟩
  have htransfer := relativeLowerDensity_transfer_finite
    hsourceSub houtputSub htargetSub hnumDiff (hInfinite i)
  rw [outputAfterInput_patientGenerator]
  exact hdensity.trans htransfer


 theorem stage3_uncountable_separation : SeparationClause := by
  intro q
  classical
  refine ⟨GenLimit.NoiseLossFeedback.finiteOmissionClass q,
    finiteOmissionClass_uncountable q,
    GenLimit.NoiseLossFeedback.finiteOmissionClass_uus q, ?_, ?_⟩
  · refine ⟨freshSweepGenerator q, ?_⟩
    intro K hK input hinput
    let output := outputAfterInput (freshSweepGenerator q) input
    have hinjective : Function.Injective output :=
      freshSweep_output_injective q input
    have hvalid : ∃ T, ∀ t, T ≤ t → output t ∈ K := by
      rcases hK with hfirst | hsecond
      · obtain ⟨hmarkers, j, htail⟩ := hfirst
        obtain ⟨Tdetect, hTdetect⟩ :=
          GenLimit.NoiseLossFeedback.allMarkers_eventually_observed
            hinput hmarkers
        let F : Set ℤ := ↑((Finset.range j).image
          GenLimit.UnionClosedness.positiveCode)
        have hF : F.Finite := Finset.finite_toSet _
        obtain ⟨Tavoid, hTavoid⟩ :=
          eventually_injective_not_mem_finite output hinjective hF
        refine ⟨max Tdetect Tavoid, ?_⟩
        intro t ht
        have hdetect : GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆
            Generic.sample input (t + 1) := by
          exact hTdetect t (le_trans (Nat.le_max_left _ _) ht)
        have havoid : output t ∉ F :=
          hTavoid t (le_trans (Nat.le_max_right _ _) ht)
        obtain ⟨k, hk, hout, _hfresh, _hnew⟩ :=
          freshSweep_run_spec q input t
        have houtPositive : output t =
            GenLimit.UnionClosedness.positiveCode k := by
          simpa [output, sweepCode, hdetect] using hout
        apply htail
        rw [houtPositive]
        by_cases hkj : j ≤ k
        · refine ⟨k - j, ?_⟩
          exact congrArg GenLimit.UnionClosedness.positiveCode (by omega)
        · exfalso
          apply havoid
          rw [houtPositive]
          simpa [F] using
            (Finset.mem_image.mpr
              ⟨k, Finset.mem_range.mpr (by omega), rfl⟩ :
                GenLimit.UnionClosedness.positiveCode k ∈
                  (Finset.range j).image
                    GenLimit.UnionClosedness.positiveCode)
      · refine ⟨0, ?_⟩
        intro t _ht
        have hnoDetect : ¬GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆
            Generic.sample input (t + 1) :=
          GenLimit.NoiseLossFeedback.not_allMarkers_observed_second
            hsecond hinput t
        obtain ⟨k, hk, hout, _hfresh, _hnew⟩ :=
          freshSweep_run_spec q input t
        have houtNegative : output t =
            GenLimit.UnionClosedness.negativeCode k := by
          simpa [output, sweepCode, hnoDetect] using hout
        rw [houtNegative]
        exact hsecond.1 (GenLimit.UnionClosedness.negativeCode_mem k)
    obtain ⟨T, hT⟩ := hvalid
    have hnovel : NovelGeneratesAfterInput input output K := by
      refine ⟨T, ?_⟩
      intro t ht
      obtain ⟨k, hk, hout, hfresh, hnew⟩ :=
        freshSweep_run_spec q input t
      exact ⟨hT t ht, hfresh, hnew⟩
    refine ⟨hnovel, ?_⟩
    let D := GeneratorFirstOn input output ∩ K
    have hD : ∀ t, T ≤ t → output t ∈ D := by
      intro t ht
      refine ⟨?_, hT t ht⟩
      refine ⟨t, rfl, ?_⟩
      intro s hs heq
      obtain ⟨k, hk, hout, hfresh, hnew⟩ :=
        freshSweep_run_spec q input t
      exact hfresh (Generic.mem_sample_iff.mpr ⟨s, by omega, heq⟩)
    have hcount := ambient_prefix_counting_of_ranked_outputs
      output D T hinjective hD (freshSweep_rank_bound q input)
    have hquarter := relativeLowerDensity_quarter_of_ambient_counting
      (D := balancedRanks D) (K := balancedRanks K)
      (preimage_mono inter_subset_right)
      (balancedRanks_infinite
        (GenLimit.NoiseLossFeedback.finiteOmissionClass_uus q K hK))
      (4 * T + 10) hcount
    simpa [D, output, balancedRelativeLowerDensity] using hquarter
  · intro gen
    by_contra hnone
    push_neg at hnone
    apply GenLimit.NoiseLossFeedback.finiteNoiseLevel_lower q
    refine ⟨gen, ?_⟩
    intro K hK input hinput
    obtain ⟨T, hT⟩ := hnone K hK input hinput
    refine ⟨T, ?_⟩
    intro t ht
    have h := hT t ht
    simpa [SampleFreshGeneratesAfterInput, outputAfterInput,
      GenLimit.NoiseLossFeedback.outputAt,
      GenLimit.NoiseLossFeedback.observedThrough] using h

 theorem stage3_result : MainClaim := by
  exact ⟨stage3_countable_half_density, stage3_uncountable_separation⟩
