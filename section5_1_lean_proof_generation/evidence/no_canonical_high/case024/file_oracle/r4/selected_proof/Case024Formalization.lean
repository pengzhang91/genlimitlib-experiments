import Case024Helpers

open Filter MeasureTheory
open scoped Topology

namespace Case024

open Stage3Case024
open GenLimit.InfiniteContamination

lemma squares_ssubset_univ : Squares ⊂ (Set.univ : Language) := by
  apply Set.ssubset_iff_subset_ne.mpr
  refine ⟨Set.subset_univ _, ?_⟩
  intro heq
  have hw : sparseBetweenSquares 0 ∈ Squares := by
    rw [heq]
    exact Set.mem_univ _
  exact sparseBetweenSquares_nonsquare 0 hw

lemma pairObstruction : PairObstruction Squares Set.univ commonInput := by
  intro Ω _ μ _ gen output _hfollow _hmeas hIntSquares hIntUniv hValidSquares _hValidUniv
  have hzero : expectedUpperDensity μ Set.univ commonInput output = 0 := by
    unfold expectedUpperDensity
    calc
      (∫ ω, relativeUpperDensity
          (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ ∂μ) =
          ∫ _ : Ω, (0 : ℝ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hValidSquares] with ω hω
        exact relativeUpperDensity_univ_eq_zero (generatorFirst_diff_finite hω)
      _ = 0 := integral_zero Ω ℝ
  have hle : expectedUpperDensity μ Squares commonInput output ≤ 1 := by
    unfold expectedUpperDensity
    calc
      (∫ ω, relativeUpperDensity
          (GenLimit.GeneratorFirst commonInput (output ω)) Squares ∂μ) ≤
          ∫ _ : Ω, (1 : ℝ) ∂μ := by
        apply integral_mono_ae hIntSquares (integrable_const (1 : ℝ))
        filter_upwards [] with ω
        exact relativeUpperDensity_le_one _ _
      _ = 1 := by simp
  constructor
  · rw [hzero]
    linarith
  · rintro ⟨_hSquaresHalf, hUnivHalf⟩
    rw [hzero] at hUnivHalf
    norm_num at hUnivHalf

lemma family_manyTargetObstruction {r : ℕ} (hr : 2 ≤ r) :
    ManyTargetObstruction (family r) commonInput := by
  intro Ω _ μ _ gen output _hfollow _hmeas _hInt hValid
  let first : Fin r := ⟨0, by omega⟩
  let last : Fin r := ⟨r - 1, by omega⟩
  refine ⟨last, ?_⟩
  have hValidSquares : EventuallyFreshValid μ Squares commonInput output := by
    simpa [first, family_zero hr] using hValid first
  rw [show family r last = Set.univ by simpa [last] using family_last (by omega : 1 ≤ r)]
  unfold expectedUpperDensity
  calc
    (∫ ω, relativeUpperDensity
        (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ ∂μ) =
        ∫ _ : Ω, (0 : ℝ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hValidSquares] with ω hω
      exact relativeUpperDensity_univ_eq_zero (generatorFirst_diff_finite hω)
    _ = 0 := integral_zero Ω ℝ

lemma family_manyTargetWitness {r : ℕ} (hr : 2 ≤ r) :
    ManyTargetWitness (family r) commonInput := by
  exact ⟨family_strictlyNested hr, family_legal r,
    family_globallyFeasible r, family_manyTargetObstruction hr⟩

end Case024

open Stage3Case024

 theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · exact ⟨Case024.Squares, Set.univ, Case024.commonInput,
      Case024.squares_ssubset_univ,
      Case024.legal_commonInput (fun _ hx => hx),
      Case024.legal_commonInput (Set.subset_univ _),
      Case024.pairObstruction⟩
  · intro r hr
    exact ⟨Case024.family r, Case024.commonInput,
      Case024.family_manyTargetWitness hr⟩
