import Case024Helpers

open Filter MeasureTheory
open scoped Topology BigOperators

namespace Case024

open GenLimit.InfiniteContamination

private theorem squares_ssubset_univ : Squares ⊂ (Set.univ : Set ℕ) := by
  refine Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_univ _, ?_⟩
  intro heq
  have htwo : 2 ∈ Squares := heq.symm ▸ Set.mem_univ 2
  rcases htwo with ⟨k, hk⟩
  have hklt : k < 2 := by
    by_contra hnot
    have hge : 2 ≤ k := Nat.le_of_not_gt hnot
    have hfour : 4 ≤ k * k := Nat.mul_le_mul hge hge
    omega
  interval_cases k <;> norm_num at hk

private theorem pairObstruction :
    Stage3Case024.PairObstruction Squares Set.univ commonInput := by
  intro Ω _ μ _ gen output _ _ hintSquares hintUniv hvalidSquares _
  have hzeroAE :
      (fun ω => Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ) =ᵐ[μ]
        (fun _ => 0) := by
    filter_upwards [hvalidSquares] with ω hω
    exact relativeUpperDensity_univ_eq_zero hω
  have hunivZero :
      Stage3Case024.expectedUpperDensity μ Set.univ commonInput output = 0 := by
    unfold Stage3Case024.expectedUpperDensity
    calc
      (∫ ω, Stage3Case024.relativeUpperDensity
          (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ ∂μ) =
          ∫ _ : Ω, (0 : ℝ) ∂μ := integral_congr_ae hzeroAE
      _ = 0 := by simp
  have hsquaresLe :
      Stage3Case024.expectedUpperDensity μ Squares commonInput output ≤ 1 := by
    unfold Stage3Case024.expectedUpperDensity
    calc
      (∫ ω, Stage3Case024.relativeUpperDensity
          (GenLimit.GeneratorFirst commonInput (output ω)) Squares ∂μ) ≤
          ∫ _ : Ω, (1 : ℝ) ∂μ := by
            apply integral_mono_ae hintSquares (integrable_const 1)
            exact Eventually.of_forall fun ω =>
              relativeUpperDensity_le_one _ _
      _ = 1 := by simp
  constructor
  · rw [hunivZero, add_zero]
    exact hsquaresLe
  · intro hboth
    rw [hunivZero] at hboth
    linarith

private theorem nestedFamily_obstruction {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetObstruction (nestedFamily r) commonInput := by
  intro Ω _ μ _ gen output _ _ _ hvalid
  let first : Fin r := ⟨0, by omega⟩
  let last : Fin r := ⟨r - 1, by omega⟩
  have hvalidSquares :
      Stage3Case024.EventuallyFreshValid μ Squares commonInput output := by
    simpa [first, nestedFamily_zero hr] using hvalid first
  have hzeroAE :
      (fun ω => Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ) =ᵐ[μ]
        (fun _ => 0) := by
    filter_upwards [hvalidSquares] with ω hω
    exact relativeUpperDensity_univ_eq_zero hω
  refine ⟨last, ?_⟩
  rw [show nestedFamily r last = Set.univ by
    simpa [last] using nestedFamily_last hr]
  unfold Stage3Case024.expectedUpperDensity
  calc
    (∫ ω, Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ ∂μ) =
        ∫ _ : Ω, (0 : ℝ) ∂μ := integral_congr_ae hzeroAE
    _ = 0 := by simp

private theorem manyTargetWitness {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetWitness (nestedFamily r) commonInput := by
  refine ⟨nestedFamily_strict hr, ?_, nestedFamily_globallyFeasible hr,
    nestedFamily_obstruction hr⟩
  intro j
  exact nestedFamily_legal j

end Case024

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · refine ⟨Case024.Squares, Set.univ, Case024.commonInput,
      Case024.squares_ssubset_univ, Case024.commonInput_legal_squares,
      Case024.commonInput_legal_univ, Case024.pairObstruction⟩
  · intro r hr
    exact ⟨Case024.nestedFamily r, Case024.commonInput,
      Case024.manyTargetWitness hr⟩
