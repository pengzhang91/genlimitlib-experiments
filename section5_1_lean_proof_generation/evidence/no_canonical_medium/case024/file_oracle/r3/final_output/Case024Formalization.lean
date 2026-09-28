import Stage3Model
import output.Helpers

open Filter MeasureTheory
open scoped Topology

open Case024Helpers
open GenLimit.InfiniteContamination

namespace Case024Proof

lemma pair_obstruction :
    Stage3Case024.PairObstruction Sq (Sq ∪ Set.Ici 0) commonInput := by
  intro Ω _ μ _ gen output _ _ hIntSq hIntDense hValidSq _
  have hdense :
      (fun ω => Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst commonInput (output ω)) (Sq ∪ Set.Ici 0))
        =ᵐ[μ] 0 := by
    filter_upwards [hValidSq] with ω hω
    exact relative_density_dense_zero hω 0
  have hExpectedDense :
      Stage3Case024.expectedUpperDensity μ (Sq ∪ Set.Ici 0) commonInput output = 0 := by
    unfold Stage3Case024.expectedUpperDensity
    calc
      (∫ ω, Stage3Case024.relativeUpperDensity
          (GenLimit.GeneratorFirst commonInput (output ω)) (Sq ∪ Set.Ici 0) ∂μ)
          = ∫ _ : Ω, (0 : ℝ) ∂μ := integral_congr_ae hdense
      _ = 0 := integral_zero Ω ℝ
  have hExpectedSq :
      Stage3Case024.expectedUpperDensity μ Sq commonInput output ≤ 1 := by
    unfold Stage3Case024.expectedUpperDensity
    have hmono := integral_mono_ae hIntSq (integrable_const (1 : ℝ))
      (Eventually.of_forall fun ω =>
        relative_density_le_one (GenLimit.GeneratorFirst commonInput (output ω)) Sq)
    simpa using hmono
  constructor
  · rw [hExpectedDense]
    simpa using hExpectedSq
  · rw [hExpectedDense]
    intro h
    linarith [h.2]

lemma pair_witness :
    ∃ K₀ K₁ : Stage3Case024.Language, ∃ input : Stage3Case024.Stream,
      K₀ ⊂ K₁ ∧ Stage3Case024.Legal input K₀ ∧
        Stage3Case024.Legal input K₁ ∧
        Stage3Case024.PairObstruction K₀ K₁ input := by
  refine ⟨Sq, Sq ∪ Set.Ici 0, commonInput, ?_,
    commonInput_legal Sq Set.Subset.rfl,
    commonInput_legal (Sq ∪ Set.Ici 0) Set.subset_union_left,
    pair_obstruction⟩
  rw [Set.ssubset_iff_subset_ne]
  constructor
  · exact Set.subset_union_left
  · intro heq
    let witness := sparseBetweenSquares 0
    have hw1 : witness ∈ Sq ∪ Set.Ici 0 := by
      exact Set.mem_union_right _ (by simp)
    have hw0 : witness ∉ Sq := sparseBetweenSquares_nonsquare 0
    rw [heq] at hw0
    exact hw0 hw1

lemma many_target_obstruction {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetObstruction (nestedFamily r) commonInput := by
  intro Ω _ μ _ gen output _ _ _ hValid
  let zero : Fin r := ⟨0, by omega⟩
  let one : Fin r := ⟨1, by omega⟩
  refine ⟨one, ?_⟩
  have hzeroValid :
      ∀ᵐ ω ∂μ, GenLimit.NovelGeneratesInLimit commonInput (output ω) Sq := by
    simpa [zero, nestedFamily_zero r (by omega)] using hValid zero
  have hdense :
      (fun ω => Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst commonInput (output ω))
        (nestedFamily r one)) =ᵐ[μ] 0 := by
    filter_upwards [hzeroValid] with ω hω
    rw [nestedFamily_one r (by omega)]
    exact relative_density_dense_zero hω (sparseBetweenSquares (r - 1))
  unfold Stage3Case024.expectedUpperDensity
  calc
    (∫ ω, Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst commonInput (output ω)) (nestedFamily r one) ∂μ)
        = ∫ _ : Ω, (0 : ℝ) ∂μ := integral_congr_ae hdense
    _ = 0 := integral_zero Ω ℝ

lemma many_witness (r : ℕ) (hr : 2 ≤ r) :
    ∃ family : Fin r → Stage3Case024.Language, ∃ input : Stage3Case024.Stream,
      Stage3Case024.ManyTargetWitness family input := by
  refine ⟨nestedFamily r, commonInput, nestedFamily_strict hr, ?_,
    nestedFamily_feasible hr, many_target_obstruction hr⟩
  intro j
  exact commonInput_legal (nestedFamily r j) (nestedFamily_core r j)

end Case024Proof

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · exact Case024Proof.pair_witness
  · intro r hr
    exact Case024Proof.many_witness r hr
