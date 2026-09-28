import Helpers

open Filter MeasureTheory
open scoped Topology

open Stage3Case024

namespace Case024

private theorem core_ssubset_univ : core ⊂ (Set.univ : Set ℕ) := by
  refine ⟨Set.subset_univ _, ?_⟩
  intro hback
  exact extraPoint_not_core 0 (hback (Set.mem_univ _))

private theorem pairObstruction : PairObstruction core Set.univ commonInput := by
  intro Ω _ μ _ gen output _ _ hIntCore hIntUniv hValidCore _
  have hzeroAE : ∀ᵐ ω ∂μ,
      relativeUpperDensity
        (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ = 0 := by
    filter_upwards [hValidCore] with ω hω
    exact relativeUpperDensity_generatorFirst_univ_zero hω
  have hExpectedUniv : expectedUpperDensity μ Set.univ commonInput output = 0 := by
    unfold expectedUpperDensity
    exact integral_eq_zero_of_ae hzeroAE
  have hExpectedCore : expectedUpperDensity μ core commonInput output ≤ 1 := by
    unfold expectedUpperDensity
    calc
      (∫ ω, relativeUpperDensity
          (GenLimit.GeneratorFirst commonInput (output ω)) core ∂μ)
          ≤ ∫ _ : Ω, (1 : ℝ) ∂μ := by
            apply integral_mono_ae hIntCore
              (integrable_const (1 : ℝ))
            exact Filter.Eventually.of_forall fun ω =>
              relativeUpperDensity_le_one
                (GenLimit.GeneratorFirst commonInput (output ω)) core
      _ = 1 := by simp
  rw [hExpectedUniv, add_zero]
  refine ⟨hExpectedCore, ?_⟩
  rintro ⟨hhalfCore, hhalfUniv⟩
  norm_num at hhalfUniv

private theorem manyObstruction {r : ℕ} (hr : 2 ≤ r) :
    ManyTargetObstruction (family r) commonInput := by
  intro Ω _ μ _ gen output _ _ _ hValid
  let first : Fin r := ⟨0, by omega⟩
  let last : Fin r := ⟨r - 1, by omega⟩
  refine ⟨last, ?_⟩
  have hfirst : family r first = core := by
    rw [family_nonlast_eq first (by simp [first]; omega)]
    simp [extras, first]
  have hlast : family r last = Set.univ := by
    simpa [last] using family_last_eq_univ (r := r) (by omega)
  have hzeroAE : ∀ᵐ ω ∂μ,
      relativeUpperDensity
        (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ = 0 := by
    filter_upwards [hValid first] with ω hω
    apply relativeUpperDensity_generatorFirst_univ_zero
    simpa [hfirst] using hω
  rw [hlast]
  unfold expectedUpperDensity
  exact integral_eq_zero_of_ae hzeroAE

end Case024

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · refine ⟨Case024.core, Set.univ, Case024.commonInput,
      Case024.core_ssubset_univ,
      Case024.commonInput_legal Case024.core Set.Subset.rfl Case024.core_infinite,
      Case024.commonInput_legal Set.univ (Set.subset_univ Case024.core) Set.infinite_univ,
      Case024.pairObstruction⟩
  · intro r hr
    refine ⟨Case024.family r, Case024.commonInput, ?_⟩
    refine ⟨Case024.strict_family hr, ?_, Case024.globallyFeasible_family r,
      Case024.manyObstruction hr⟩
    intro j
    exact Case024.commonInput_legal (Case024.family r j)
      (Case024.core_subset_family r j) (Case024.family_infinite r j)
