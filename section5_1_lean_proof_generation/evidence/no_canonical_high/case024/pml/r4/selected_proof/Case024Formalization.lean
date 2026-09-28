import Case024Helpers

open Filter MeasureTheory
open scoped Topology

open Stage3Case024

namespace Stage3Case024.Case024

lemma expectedUpperDensity_univ_eq_zero
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (output : Ω → Stream)
    (hvalid : EventuallyFreshValid μ core input output) :
    expectedUpperDensity μ Set.univ input output = 0 := by
  unfold expectedUpperDensity
  calc
    (∫ ω, relativeUpperDensity
        (GenLimit.GeneratorFirst input (output ω)) Set.univ ∂μ) =
        ∫ _ : Ω, (0 : ℝ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hvalid] with ω hω
      exact relativeUpperDensity_generatorFirst_eq_zero hω
    _ = 0 := by simp

lemma expectedUpperDensity_le_one
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (K : Language) (output : Ω → Stream)
    (hint : DensityIntegrable μ K input output) :
    expectedUpperDensity μ K input output ≤ 1 := by
  change Integrable
    (fun ω => relativeUpperDensity
      (GenLimit.GeneratorFirst input (output ω)) K) μ at hint
  unfold expectedUpperDensity
  calc
    (∫ ω, relativeUpperDensity
        (GenLimit.GeneratorFirst input (output ω)) K ∂μ) ≤
        ∫ _ : Ω, (1 : ℝ) ∂μ := by
      apply integral_mono hint (integrable_const 1)
      intro ω
      exact relativeUpperDensity_le_one _ _
    _ = 1 := by simp

lemma pairObstruction : PairObstruction core Set.univ input := by
  intro Ω _ μ _ gen output _ _ hintCore _ hvalidCore _
  have hzero : expectedUpperDensity μ Set.univ input output = 0 :=
    expectedUpperDensity_univ_eq_zero μ output hvalidCore
  have hone : expectedUpperDensity μ core input output ≤ 1 :=
    expectedUpperDensity_le_one μ core output hintCore
  constructor
  · rw [hzero, add_zero]
    exact hone
  · rw [hzero]
    norm_num

lemma manyTargetObstruction {r : ℕ} (hr : 2 ≤ r) :
    ManyTargetObstruction (@family r) input := by
  intro Ω _ μ _ gen output _ _ _ hvalid
  let first : Fin r := firstIndex (by omega)
  let top : Fin r := topIndex (by omega)
  have hvalidCore : EventuallyFreshValid μ core input output := by
    simpa [first, family_first_eq_core hr] using hvalid first
  refine ⟨top, ?_⟩
  rw [show family top = Set.univ by
    simpa [top] using family_top_eq_univ (by omega : 0 < r)]
  exact expectedUpperDensity_univ_eq_zero μ output hvalidCore

lemma manyTargetWitness {r : ℕ} (hr : 2 ≤ r) :
    ManyTargetWitness (@family r) input := by
  exact ⟨family_strictlyNested,
    fun j => input_legal_family j,
    family_globallyFeasible,
    manyTargetObstruction hr⟩

end Stage3Case024.Case024

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · refine ⟨Stage3Case024.Case024.core, Set.univ,
      Stage3Case024.Case024.input,
      Stage3Case024.Case024.core_ssubset_univ,
      ?_, ?_, Stage3Case024.Case024.pairObstruction⟩
    · simpa [Stage3Case024.Case024.family_first_eq_core (r := 2) (by omega)] using
        (Stage3Case024.Case024.input_legal_family
          (Stage3Case024.Case024.firstIndex (by omega : 0 < 2)))
    · have h := Stage3Case024.Case024.input_legal_family
          (Stage3Case024.Case024.topIndex (by omega : 0 < 2))
      simpa [Stage3Case024.Case024.family_top_eq_univ (r := 2) (by omega)] using h
  · intro r hr
    exact ⟨@Stage3Case024.Case024.family r,
      Stage3Case024.Case024.input,
      Stage3Case024.Case024.manyTargetWitness hr⟩
