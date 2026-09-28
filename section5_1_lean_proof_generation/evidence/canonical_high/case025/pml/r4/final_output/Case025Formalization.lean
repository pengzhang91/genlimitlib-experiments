import Helpers

open Stage3Case025

open GenLimit

/-- The patient-scope machine supplies the exact positive-presentation engine. -/
theorem stage3_positive_engine : PositivePresentationHalfDensity := by
  intro family hInfinite
  let O := Stage3Case025.oracleOfFamily family hInfinite
  refine ⟨Stage3Case025.Causal.onlineGenerator O, ?_⟩
  intro i input hPresents
  let output := GenLimit.PatientMachine.output O input
  have hmain :=
    GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
      O input (z := i) hPresents
  refine ⟨output, Stage3Case025.Causal.follows_onlineGenerator O input, ?_, ?_⟩
  · obtain ⟨T, hT⟩ := hmain.1
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨hmem, hfreshInput, hfreshOutput⟩ := hT t ht
    refine ⟨hmem, ?_, hfreshOutput⟩
    rw [GenLimit.mem_sample_iff]
    push_neg
    intro s hs
    exact hfreshInput s (Nat.le_of_lt_succ hs)
  · simpa [output, GenLimit.PatientMachine.patientLowerDensity] using hmain.2

/-- Finite occurrence noise is absorbed by the coded finite-expansion family. -/
theorem stage3_finite_noise_transfer : FiniteNoiseTransferPrinciple := by
  intro _
  intro family hInfinite
  let O := Stage3Case025.oracleOfFamily family hInfinite
  let Oplus := GenLimit.InfiniteContamination.finiteExpansionOracleFamily O
  refine ⟨Stage3Case025.Causal.onlineGenerator Oplus, ?_⟩
  intro i input hPresentation
  let output := GenLimit.PatientMachine.output Oplus input
  have hnoiseFinite :
      (GenLimit.InfiniteContamination.displayedNoise input (family i)).Finite :=
    GenLimit.InfiniteContamination.displayedNoise_finite hPresentation.2
  have homissionFinite :
      (GenLimit.InfiniteContamination.displayedOmissions input (family i)).Finite := by
    have hempty :
        GenLimit.InfiniteContamination.displayedOmissions input (family i) = ∅ := by
      exact Set.diff_eq_empty.mpr hPresentation.1
    rw [hempty]
    exact Set.finite_empty
  let data : GenLimit.InfiniteContamination.FiniteExpansionCode :=
    (i,
      Finset.equivBitIndices.symm hnoiseFinite.toFinset,
      Finset.equivBitIndices.symm homissionFinite.toFinset)
  let j := GenLimit.InfiniteContamination.encodeFiniteExpansionCode data
  have hPresents : GenLimit.Presents input (Oplus.language j) := by
    change Set.range input =
      GenLimit.InfiniteContamination.finiteExpansionLanguage O j
    have hadd :
        (↑hnoiseFinite.toFinset : Set ℕ) =
          GenLimit.InfiniteContamination.displayedNoise input (family i) :=
      Set.Finite.coe_toFinset hnoiseFinite
    have hremove :
        (↑homissionFinite.toFinset : Set ℕ) =
          GenLimit.InfiniteContamination.displayedOmissions input (family i) :=
      Set.Finite.coe_toFinset homissionFinite
    rw [GenLimit.InfiniteContamination.finiteExpansionLanguage]
    simp only [j, data,
      GenLimit.InfiniteContamination.finiteExpansionCode_encode,
      Equiv.apply_symm_apply]
    rw [hadd, hremove]
    exact
      (GenLimit.InfiniteContamination.finiteExpansion_displayedNoise_displayedOmissions
        input (family i)).symm
  have hmain :=
    GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
      Oplus input (z := j) hPresents
  refine ⟨output, Stage3Case025.Causal.follows_onlineGenerator Oplus input, ?_, ?_⟩
  · obtain ⟨Tvalid, hTvalid⟩ := hmain.1
    have hOutputInjective : Function.Injective output := by
      intro s t heq
      rcases lt_trichotomy s t with hst | hst | hst
      · exact False.elim
          (GenLimit.PatientMachine.output_ne_of_lt Oplus input hst heq)
      · exact hst
      · exact False.elim
          (GenLimit.PatientMachine.output_ne_of_lt Oplus input hst heq.symm)
    have hbadTimes :
        (output ⁻¹' (Set.range input \ family i)).Finite :=
      hnoiseFinite.preimage hOutputInjective.injOn
    obtain ⟨bound, hbound⟩ := hbadTimes.bddAbove
    refine ⟨max Tvalid (bound + 1), ?_⟩
    intro t ht
    have htValid : Tvalid ≤ t := (Nat.le_max_left _ _).trans ht
    have htBound : bound < t := by
      have : bound + 1 ≤ t := (Nat.le_max_right _ _).trans ht
      omega
    obtain ⟨hmemRange, hfreshInput, hfreshOutput⟩ := hTvalid t htValid
    have hmemTarget : output t ∈ family i := by
      by_contra hnot
      have htBad : t ∈ output ⁻¹' (Set.range input \ family i) := by
        refine ⟨?_, hnot⟩
        rw [hPresents]
        exact hmemRange
      exact (Nat.not_lt_of_ge (hbound htBad)) htBound
    refine ⟨hmemTarget, ?_, hfreshOutput⟩
    rw [GenLimit.mem_sample_iff]
    push_neg
    intro s hs
    exact hfreshInput s (Nat.le_of_lt_succ hs)
  · have hsubset : family i ⊆ Oplus.language j := by
      rw [← hPresents]
      exact hPresentation.1
    have hfiniteDiff : (Oplus.language j \ family i).Finite := by
      rw [← hPresents]
      exact hnoiseFinite
    have hhalfExpanded :
        (1 / 2 : ℝ) ≤
          GenLimit.PatientScope.relativeLowerDensity
            (GenLimit.GeneratorFirst input output ∩ Oplus.language j)
            (Oplus.language j) := by
      simpa [output, GenLimit.PatientMachine.patientLowerDensity] using hmain.2
    exact
      Stage3Case025.DensityTransfer.half_relativeLowerDensity_of_finite_super
        (Q := GenLimit.GeneratorFirst input output)
        (K := family i) (R := Oplus.language j)
        (hInfinite i) hsubset hfiniteDiff hhalfExpanded

/-- Primary endpoint. -/
theorem stage3_result : MainClaim := by
  exact stage3_finite_noise_transfer stage3_positive_engine
