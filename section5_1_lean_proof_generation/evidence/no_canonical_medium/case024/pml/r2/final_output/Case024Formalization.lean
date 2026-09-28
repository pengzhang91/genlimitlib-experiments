import Case024Helpers

open Filter MeasureTheory
open scoped Topology

namespace Case024

open Stage3Case024
open GenLimit

lemma core_ssubset_univ : core ⊂ (Set.univ : Set ℕ) := by
  refine Set.ssubset_univ_iff.mpr ?_
  intro heq
  have hm : marker 0 ∈ core := by rw [heq]; trivial
  exact marker_nonsquare 0 hm

lemma expected_core_le_one
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (input : Stream) (output : Ω → Stream)
    (hint : DensityIntegrable μ core input output) :
    expectedUpperDensity μ core input output ≤ 1 := by
  unfold expectedUpperDensity
  unfold DensityIntegrable at hint
  calc
    (∫ ω, relativeUpperDensity
        (GeneratorFirst input (output ω)) core ∂μ)
        ≤ ∫ _ : Ω, (1 : ℝ) ∂μ := by
          apply integral_mono_ae hint (integrable_const (1 : ℝ))
          exact Filter.Eventually.of_forall fun ω =>
            relativeUpperDensity_le_one
              (GeneratorFirst input (output ω)) core
    _ = 1 := by simp

lemma expected_univ_eq_zero
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (input : Stream) (output : Ω → Stream)
    (hvalid : EventuallyFreshValid μ core input output) :
    expectedUpperDensity μ Set.univ input output = 0 := by
  unfold expectedUpperDensity
  calc
    (∫ ω, relativeUpperDensity
        (GeneratorFirst input (output ω)) Set.univ ∂μ)
        = ∫ _ : Ω, (0 : ℝ) ∂μ := by
          apply integral_congr_ae
          exact hvalid.mono fun ω hω =>
            relativeUpperDensity_generatorFirst_univ_eq_zero hω
    _ = 0 := by simp

lemma pairObstruction : PairObstruction core Set.univ commonInput := by
  intro Ω _ μ _ gen output _ _ hintCore _ hvalidCore _
  have hcore := expected_core_le_one μ commonInput output hintCore
  have huniv := expected_univ_eq_zero μ commonInput output hvalidCore
  constructor
  · rw [huniv, add_zero]
    exact hcore
  · intro hboth
    rw [huniv] at hboth
    linarith [hboth.2]

lemma targetFamily_zero {r : ℕ} (hr : 2 ≤ r) :
    targetFamily (⟨0, by omega⟩ : Fin r) = core := by
  ext x
  simp [targetFamily, initialMarkers]
  omega

lemma manyTargetObstruction {r : ℕ} (hr : 2 ≤ r) :
    ManyTargetObstruction (@targetFamily r) commonInput := by
  intro Ω _ μ _ gen output _ _ _ hvalid
  let first : Fin r := ⟨0, by omega⟩
  let last : Fin r := lastIndex r (by omega)
  have hvalidCore : EventuallyFreshValid μ core commonInput output := by
    have h := hvalid first
    simpa [first, targetFamily_zero hr] using h
  refine ⟨last, ?_⟩
  rw [show targetFamily last = Set.univ by
    simpa [last] using targetFamily_last (r := r) (by omega)]
  exact expected_univ_eq_zero μ commonInput output hvalidCore

lemma manyTargetWitness {r : ℕ} (hr : 2 ≤ r) :
    ManyTargetWitness (@targetFamily r) commonInput := by
  refine ⟨targetFamily_strictlyNested, ?_, globallyFeasible_family,
    manyTargetObstruction hr⟩
  intro j
  exact commonInput_legal_family j

end Case024

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · refine ⟨Case024.core, Set.univ, Case024.commonInput,
      Case024.core_ssubset_univ, Case024.commonInput_legal_core,
      Case024.commonInput_legal_univ, Case024.pairObstruction⟩
  · intro r hr
    exact ⟨@Case024.targetFamily r, Case024.commonInput,
      Case024.manyTargetWitness hr⟩
