import DensityTransfer

open Filter
open Set

namespace Stage3Case025

open GenLimit
open PatientBridge
open DensityTransfer
open GenLimit.InfiniteContamination

theorem finiteNoiseTransfer :
    FiniteNoiseTransferPrinciple := by
  intro _positiveEngine
  intro family hInfinite
  let baseOracle := oracleOfFamily family hInfinite
  let expandedOracle := finiteExpansionOracleFamily baseOracle
  refine ⟨onlineGenerator expandedOracle, ?_⟩
  intro i input hPresentation
  let target : Set ℕ := family i
  let presented : Set ℕ := Set.range input
  let noise : Set ℕ := presented \ target
  have hTargetPresented : target ⊆ presented := hPresentation.1
  have hNoiseFinite : noise.Finite := by
    exact displayedNoise_finite hPresentation.2
  let data : FiniteExpansionCode :=
    (i, Finset.equivBitIndices.symm hNoiseFinite.toFinset,
      Finset.equivBitIndices.symm ∅)
  let expandedIndex := encodeFiniteExpansionCode data
  have hExpandedLanguage :
      (expandedOracle.language expandedIndex) = presented := by
    change finiteExpansionLanguage baseOracle expandedIndex = presented
    rw [finiteExpansionLanguage]
    simp only [expandedIndex, data, finiteExpansionCode_encode,
      Equiv.apply_symm_apply]
    rw [Set.Finite.coe_toFinset hNoiseFinite]
    dsimp only [baseOracle, oracleOfFamily]
    rw [show family i = target by rfl]
    ext x
    simp only [finiteExpansion, Set.mem_diff, Set.mem_union]
    constructor
    · rintro ⟨hxTarget | hxNoise, _⟩
      · exact hTargetPresented hxTarget
      · exact hxNoise.1
    · intro hxPresented
      refine ⟨?_, by simp⟩
      by_cases hxTarget : x ∈ target
      · exact Or.inl hxTarget
      · exact Or.inr ⟨hxPresented, hxTarget⟩
  have hPresents : Presents input (expandedOracle.language expandedIndex) := by
    change Set.range input = expandedOracle.language expandedIndex
    exact hExpandedLanguage.symm
  let output : Stream := GenLimit.PatientMachine.output expandedOracle input
  refine ⟨output, follows_onlineGenerator expandedOracle input, ?_, ?_⟩
  · obtain ⟨hNovelPresented, _hDensityPresented⟩ :=
      GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
        expandedOracle input (z := expandedIndex) hPresents
    obtain ⟨validFrom, hValidFrom⟩ := hNovelPresented
    have hBadOutputTimes : (output ⁻¹' noise).Finite := by
      exact hNoiseFinite.preimage
        (GenLimit.PatientMachine.output_injective expandedOracle input).injOn
    have hEventuallyAvoidsNoise : ∀ᶠ t : ℕ in atTop, output t ∉ noise := by
      rw [← Nat.cofinite_eq_atTop]
      exact hBadOutputTimes.eventually_cofinite_notMem
    rw [eventually_atTop] at hEventuallyAvoidsNoise
    obtain ⟨avoidFrom, hAvoidFrom⟩ := hEventuallyAvoidsNoise
    refine ⟨max validFrom avoidFrom, ?_⟩
    intro t ht
    have hValid := hValidFrom t ((Nat.le_max_left _ _).trans ht)
    have hAvoid := hAvoidFrom t ((Nat.le_max_right _ _).trans ht)
    have hInPresented : output t ∈ presented := by
      rw [← hExpandedLanguage]
      exact hValid.1
    refine ⟨?_, ?_, hValid.2.2⟩
    · by_contra hNotTarget
      exact hAvoid ⟨hInPresented, hNotTarget⟩
    · rw [GenLimit.mem_sample_iff]
      rintro ⟨s, hs, heq⟩
      exact hValid.2.1 s (Nat.lt_succ_iff.mp hs) heq
  · obtain ⟨_hNovelPresented, hDensityPresented⟩ :=
      GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
        expandedOracle input (z := expandedIndex) hPresents
    have hDensityPresented' :
        (1 / 2 : ℝ) ≤ PatientScope.relativeLowerDensity
          (GeneratorFirst input output ∩ presented) presented := by
      simpa [GenLimit.PatientMachine.patientLowerDensity, output,
        hExpandedLanguage] using hDensityPresented
    have hTransfer := relativeLowerDensity_finite_extension
      (Q := GeneratorFirst input output)
      (K := target) (R := presented)
      (hInfinite i) hTargetPresented hNoiseFinite
    have hDensityTarget := hDensityPresented'.trans hTransfer
    simpa [target, presented, output, hExpandedLanguage] using hDensityTarget

end Stage3Case025

open Stage3Case025

/-- Primary endpoint: the unchanged semantic half-density theorem. -/
theorem stage3_result : Stage3Case025.MainClaim := by
  exact Stage3Case025.finiteNoiseTransfer
    Stage3Case025.positivePresentationHalfDensity
