import Helpers
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Set Filter
open scoped Topology BigOperators

namespace Stage3Proof
open Stage3S2B

lemma affineCast_tendsto : Tendsto (fun n : ℕ => ((12 * n + 10 : ℕ) : ℝ)) atTop atTop := by
  apply Filter.tendsto_atTop_mono (fun n => ?_) (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  exact_mod_cast (by omega : n ≤ 12 * n + 10)

lemma logb_affine_div_tendsto :
    Tendsto (fun n : ℕ => Real.logb 2 ((12 * n + 10 : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  let a : ℕ → ℝ := fun n => ((12 * n + 10 : ℕ) : ℝ)
  have ha : Tendsto a atTop atTop := affineCast_tendsto
  have hlo : (Real.logb 2 ∘ a) =o[atTop] (id ∘ a) :=
    Real.isLittleO_logb_id_atTop.comp_tendsto ha
  have hzero : Tendsto (fun n => Real.logb 2 (a n) / a n) atTop (𝓝 0) := by
    simpa [Function.comp_def, id_eq] using hlo.tendsto_div_nhds_zero
  have hratio : Tendsto (fun n : ℕ => a n / (n : ℝ)) atTop (𝓝 12) := by
    have hc : Tendsto (fun n : ℕ => (10 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 10
    have hconst : Tendsto (fun _ : ℕ => (12 : ℝ)) atTop (𝓝 12) := tendsto_const_nhds
    have hsum := hconst.add hc
    have heq : (fun n : ℕ => a n / (n : ℝ)) =ᶠ[atTop]
        (fun n : ℕ => (12 : ℝ) + 10 / (n : ℝ)) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      dsimp [a]
      push_cast
      field_simp
    simpa using hsum.congr' heq.symm
  have hprod := hzero.mul hratio
  convert hprod using 1
  · funext n
    dsimp [a]
    by_cases hn : n = 0
    · subst n; simp
    · have ha0 : (((12 * n + 10 : ℕ) : ℝ)) ≠ 0 := by positivity
      field_simp
  · norm_num

end Stage3Proof

namespace Stage3Proof
open Stage3S2B

lemma core_prefixRatio_tendsto (gen : FeedbackGenerator) :
    Tendsto ((orderedTarget gen).prefixRatio core) atTop (𝓝 0) := by
  let g : ℕ → ℝ := fun n =>
    Real.logb 2 ((12 * n + 10 : ℕ) : ℝ) / (n : ℝ) + 1 / (n : ℝ)
  have hg : Tendsto g atTop (𝓝 0) := by
    have hlog := logb_affine_div_tendsto
    have hone : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 1
    simpa [g] using hlog.add hone
  apply squeeze_zero (fun n => ?_) (fun n => ?_) hg
  · unfold GenLimit.KleinbergWei.OrderedLanguage.prefixRatio
    split <;> positivity
  · unfold GenLimit.KleinbergWei.OrderedLanguage.prefixRatio
    split
    · subst n; dsimp [g]; simp only [Nat.cast_zero, div_zero, one_div, inv_zero, add_zero]; exact le_rfl
    · rename_i hn
      have hcount := core_prefixCount_le_log gen n
      have hcast : ((orderedTarget gen).prefixCount core n : ℝ) ≤
          (Nat.log2 (12 * n + 10) : ℝ) + 1 := by exact_mod_cast hcount
      have hlog : (Nat.log2 (12 * n + 10) : ℝ) ≤
          Real.logb 2 ((12 * n + 10 : ℕ) : ℝ) := Real.log2_le_logb _
      have hn0 : 0 ≤ (n : ℝ) := by positivity
      calc
        ((orderedTarget gen).prefixCount core n : ℝ) / (n : ℝ)
            ≤ ((Nat.log2 (12 * n + 10) : ℝ) + 1) / (n : ℝ) :=
          div_le_div_of_nonneg_right hcast hn0
        _ ≤ (Real.logb 2 ((12 * n + 10 : ℕ) : ℝ) + 1) / (n : ℝ) :=
          div_le_div_of_nonneg_right (add_le_add_right hlog 1) hn0
        _ = g n := by simp [g, add_div]

lemma prefixCount_mono {K : OrderedLanguage} {A B : Language} (hAB : A ⊆ B) (n : ℕ) :
    K.prefixCount A n ≤ K.prefixCount B n := by
  unfold GenLimit.KleinbergWei.OrderedLanguage.prefixCount
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, hAB hi.2⟩

lemma prefixRatio_mono {K : OrderedLanguage} {A B : Language} (hAB : A ⊆ B) (n : ℕ) :
    K.prefixRatio A n ≤ K.prefixRatio B n := by
  unfold GenLimit.KleinbergWei.OrderedLanguage.prefixRatio
  split
  · rfl
  · exact div_le_div_of_nonneg_right (by exact_mod_cast prefixCount_mono hAB n) (by positivity)

lemma scored_prefixRatio_tendsto (gen : FeedbackGenerator) :
    Tendsto ((orderedTarget gen).prefixRatio
      (scored (realizedTarget gen) (interactionTranscript gen).presentation
        (interactionTranscript gen).output)) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => ?_) (fun n => ?_) (core_prefixRatio_tendsto gen)
  · unfold GenLimit.KleinbergWei.OrderedLanguage.prefixRatio
    split <;> positivity
  · apply prefixRatio_mono
    exact scored_subset_core gen

lemma scored_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity
      (scored (realizedTarget gen) (interactionTranscript gen).presentation
        (interactionTranscript gen).output) = 0 := by
  unfold GenLimit.KleinbergWei.OrderedLanguage.upperDensity
  exact (scored_prefixRatio_tendsto gen).limsup_eq

end Stage3Proof
