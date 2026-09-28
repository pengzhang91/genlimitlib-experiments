import Case024Helpers

open Filter MeasureTheory
open scoped Topology

namespace Stage3Case024Proof

open GenLimit
open GenLimit.InfiniteContamination

lemma pairObstruction :
    Stage3Case024.PairObstruction squareCore Set.univ commonInput := by
  intro Ω instMeas μ instProb gen output hfollow hmeas hintCore hintUniv
    hvalidCore hvalidUniv
  have hdensityUniv : ∀ᵐ ω ∂μ,
      Stage3Case024.relativeUpperDensity
        (GeneratorFirst commonInput (output ω)) Set.univ = 0 :=
    hvalidCore.mono (fun ω hω => generatorFirst_density_univ_zero hω)
  have hexpectUniv :
      Stage3Case024.expectedUpperDensity μ Set.univ commonInput output = 0 := by
    unfold Stage3Case024.expectedUpperDensity
    exact integral_eq_zero_of_ae hdensityUniv
  have hexpectCore :
      Stage3Case024.expectedUpperDensity μ squareCore commonInput output ≤ 1 := by
    unfold Stage3Case024.expectedUpperDensity
    calc
      (∫ ω, Stage3Case024.relativeUpperDensity
          (GeneratorFirst commonInput (output ω)) squareCore ∂μ) ≤
          ∫ _ : Ω, (1 : ℝ) ∂μ := by
            apply integral_mono_ae hintCore (integrable_const 1)
            exact Filter.Eventually.of_forall (fun ω =>
              relativeUpperDensity_le_one _ _)
      _ = 1 := by simp
  constructor
  · rw [hexpectUniv, add_zero]
    exact hexpectCore
  · intro hboth
    rw [hexpectUniv] at hboth
    linarith

lemma pairWitness :
    ∃ K₀ K₁ : Stage3Case024.Language, ∃ input : Stage3Case024.Stream,
      K₀ ⊂ K₁ ∧ Stage3Case024.Legal input K₀ ∧
        Stage3Case024.Legal input K₁ ∧
        Stage3Case024.PairObstruction K₀ K₁ input := by
  refine ⟨squareCore, Set.univ, commonInput, ?_, ?_, ?_, pairObstruction⟩
  · rw [Set.ssubset_iff_subset_ne]
    exact ⟨Set.subset_univ _, squareCore_ne_univ⟩
  · exact commonInput_legal squareCore squareCore_infinite Set.Subset.rfl
  · exact commonInput_legal Set.univ Set.infinite_univ (Set.subset_univ _)

lemma targetFamily_manyTargetObstruction {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetObstruction (targetFamily r) commonInput := by
  intro Ω instMeas μ instProb gen output hfollow hmeas hint hvalid
  let first : Fin r := ⟨0, by omega⟩
  let last : Fin r := ⟨r - 1, by omega⟩
  have hfirst : targetFamily r first = squareCore := by
    have hne : (0 : ℕ) ≠ r - 1 := by omega
    simp [targetFamily, first, hne, addedBefore]
  have hlast : targetFamily r last = Set.univ := by
    simp [targetFamily, last]
  have hvalidCore : Stage3Case024.EventuallyFreshValid
      μ squareCore commonInput output := by
    simpa [hfirst] using hvalid first
  have hdensityUniv : ∀ᵐ ω ∂μ,
      Stage3Case024.relativeUpperDensity
        (GeneratorFirst commonInput (output ω)) Set.univ = 0 :=
    hvalidCore.mono (fun ω hω => generatorFirst_density_univ_zero hω)
  refine ⟨last, ?_⟩
  rw [hlast]
  unfold Stage3Case024.expectedUpperDensity
  exact integral_eq_zero_of_ae hdensityUniv

lemma manyTargetWitness {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetWitness (targetFamily r) commonInput := by
  refine ⟨targetFamily_strictlyNested hr, ?_, targetFamily_globallyFeasible,
    targetFamily_manyTargetObstruction hr⟩
  intro j
  exact targetFamily_legal r j

lemma manyTargetClaim :
    ∀ r : ℕ, 2 ≤ r →
      ∃ family : Fin r → Stage3Case024.Language, ∃ input : Stage3Case024.Stream,
        Stage3Case024.ManyTargetWitness family input := by
  intro r hr
  exact ⟨targetFamily r, commonInput, manyTargetWitness hr⟩

end Stage3Case024Proof

open Stage3Case024Proof

theorem stage3_result : Stage3Case024.MainClaim := by
  exact ⟨pairWitness, manyTargetClaim⟩
