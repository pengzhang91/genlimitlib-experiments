import Helpers
import Mathlib.Data.Nat.Sqrt
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import GenLimit.Paper39_DenseGeneration.Abstract.Density

open Set Filter

namespace Stage3Proof

open Stage3S2B

lemma exists_odd_candidate_not_mem (s : Finset ℕ) :
    ∃ k ≤ s.card, 2 * k + 3 ∉ s := by
  by_contra h
  push_neg at h
  let candidates := (Finset.range (s.card + 1)).image (fun k => 2 * k + 3)
  have hcandidates : candidates.card = s.card + 1 := by
    rw [show candidates.card = (Finset.range (s.card + 1)).card by
      exact Finset.card_image_of_injective _ (by
        intro a b hab
        change 2 * a + 3 = 2 * b + 3 at hab
        omega)]
    simp
  have hsubset : candidates ⊆ s := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨k, hk, rfl⟩
    apply h k
    have := Finset.mem_range.mp hk
    omega
  have := Finset.card_le_card hsubset
  omega

lemma nextPresentation_odd_le {t : ℕ} (h : History t) (ht : t % 2 ≠ 0) :
    nextPresentation h ≤ 6 * t + 3 := by
  classical
  obtain ⟨k, hk, hknot⟩ := exists_odd_candidate_not_mem (forbidden h)
  have hkcard : k ≤ 3 * t := hk.trans (forbidden_card_le h)
  have hkOrd : 2 * k + 3 ∈ ordinary := by
    rintro ⟨j, hj⟩
    cases j with
    | zero => norm_num at hj
    | succ j =>
        have heven : Even (2 ^ (j + 1)) :=
          Nat.even_pow.mpr ⟨even_two, by omega⟩
        have hmod := Nat.even_iff.mp heven
        change 2 ^ (j + 1) = 2 * k + 3 at hj
        rw [hj] at hmod
        omega
  have hfind : nextPresentation h ≤ 2 * k + 3 := by
    unfold nextPresentation
    simp only [ht, if_false]
    exact Nat.find_min' (exists_ordinary_not_forbidden h) ⟨hkOrd, hknot⟩
  omega

lemma presentation_odd_le (gen : FeedbackGenerator) (r : ℕ) :
    presentation gen (2 * r + 1) ≤ 12 * r + 9 := by
  rw [presentation_eq_next]
  have hodd : (2 * r + 1) % 2 ≠ 0 := by omega
  have := nextPresentation_odd_le (histories gen (2 * r + 1)) hodd
  omega

end Stage3Proof

namespace Stage3Proof

open Stage3S2B
open GenLimit.KleinbergWei

lemma target_infinite (gen : FeedbackGenerator) : (target gen).Infinite := by
  apply (Set.infinite_range_of_injective (presentation_injective gen)).mono
  intro z hz
  rcases hz with ⟨t, rfl⟩
  exact presentation_mem_target gen t

noncomputable def orderedTarget (gen : FeedbackGenerator) : Stage3S2B.OrderedLanguage := by
  classical
  exact {
    carrier := target gen
    enumeration := Nat.nth (fun z => z ∈ target gen)
    enumeration_injective := Nat.nth_injective (target_infinite gen)
    range_enumeration := Nat.range_nth_of_infinite (target_infinite gen)
  }

lemma orderedTarget_inherits (gen : FeedbackGenerator) :
    InheritsAmbientOrder (orderedTarget gen) :=
  Nat.nth_strictMono (target_infinite gen)

noncomputable def targetCount (gen : FeedbackGenerator) (n : ℕ) : ℕ := by
  classical
  exact Nat.count (fun z => z ∈ target gen) n

lemma target_count_linear_lower (gen : FeedbackGenerator) (n : ℕ) :
    n + 1 ≤ targetCount gen (12 * n + 10) := by
  classical
  letI : DecidablePred (fun z => z ∈ target gen) := Classical.decPred _
  let oddValues := (Finset.range (n + 1)).image
    (fun r => presentation gen (2 * r + 1))
  have hcard : oddValues.card = n + 1 := by
    rw [show oddValues.card = (Finset.range (n + 1)).card by
      exact Finset.card_image_of_injective _ (by
        intro a b hab
        have ht : 2 * a + 1 = 2 * b + 1 := presentation_injective gen hab
        omega)]
    simp
  unfold targetCount
  rw [Nat.count_eq_card_filter_range]
  rw [← hcard]
  apply Finset.card_le_card
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨r, hr, rfl⟩
  have hrle : r ≤ n := by
    have := Finset.mem_range.mp hr
    omega
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr ?_, presentation_mem_target gen (2 * r + 1)⟩
  have hle := presentation_odd_le gen r
  omega

lemma orderedTarget_enumeration_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).enumeration n ≤ 12 * n + 9 := by
  classical
  letI : DecidablePred (fun z => z ∈ target gen) := Classical.decPred _
  change Nat.nth (fun z => z ∈ target gen) n ≤ 12 * n + 9
  have hcount := target_count_linear_lower gen n
  have hltCount : n < targetCount gen (12 * n + 10) := by omega
  unfold targetCount at hltCount
  have hnth := Nat.nth_lt_of_lt_count hltCount
  omega

end Stage3Proof

namespace Stage3Proof

open Stage3S2B
open GenLimit.KleinbergWei

lemma orderedTarget_prefixCount_core_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).prefixCount core n ≤ Nat.log2 (12 * n + 10) + 1 := by
  classical
  let indices := (Finset.range n).filter
    (fun i => (orderedTarget gen).enumeration i ∈ core)
  let values := indices.image (orderedTarget gen).enumeration
  have hcard : indices.card = values.card := by
    symm
    exact Finset.card_image_of_injective _ (orderedTarget gen).enumeration_injective
  have hsubset : values ⊆ (Finset.range (Nat.log2 (12 * n + 10) + 1)).image
      (fun k => 2 ^ k) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
    have hiIndex : i < n := (Finset.mem_filter.mp hi).1 |> Finset.mem_range.mp
    have hiCore : (orderedTarget gen).enumeration i ∈ core :=
      (Finset.mem_filter.mp hi).2
    rcases hiCore with ⟨k, hk⟩
    change 2 ^ k = (orderedTarget gen).enumeration i at hk
    apply Finset.mem_image.mpr
    refine ⟨k, Finset.mem_range.mpr ?_, hk⟩
    have henum : (orderedTarget gen).enumeration i ≤ 12 * i + 9 :=
      orderedTarget_enumeration_le gen i
    have hpow : 2 ^ k ≤ 12 * n + 10 := by
      rw [hk]
      omega
    have hklog : k ≤ Nat.log2 (12 * n + 10) :=
      (Nat.le_log2 (by omega : 12 * n + 10 ≠ 0)).mpr hpow
    omega
  unfold GenLimit.KleinbergWei.OrderedLanguage.prefixCount
  change indices.card ≤ _
  rw [hcard]
  calc
    values.card ≤ ((Finset.range (Nat.log2 (12 * n + 10) + 1)).image
        (fun k => 2 ^ k)).card := Finset.card_le_card hsubset
    _ ≤ (Finset.range (Nat.log2 (12 * n + 10) + 1)).card :=
      Finset.card_image_le
    _ = Nat.log2 (12 * n + 10) + 1 := Finset.card_range _

end Stage3Proof

namespace Stage3Proof

open Stage3S2B
open GenLimit.KleinbergWei
open scoped Topology

lemma log2_linear_le (n : ℕ) :
    Nat.log2 (12 * n + 10) ≤ Nat.log2 (n + 1) + 4 := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  calc
    Nat.log 2 (12 * n + 10) ≤ Nat.log 2 ((((n + 1) * 2) * 2) * 2 * 2) := by
      apply Nat.log_mono_right
      omega
    _ = Nat.log 2 (n + 1) + 4 := by
      rw [Nat.log_mul_base (b := 2) (n := (n + 1) * 2 * 2 * 2)
        (by omega) (by positivity)]
      rw [Nat.log_mul_base (b := 2) (n := (n + 1) * 2 * 2)
        (by omega) (by positivity)]
      rw [Nat.log_mul_base (b := 2) (n := (n + 1) * 2)
        (by omega) (by positivity)]
      rw [Nat.log_mul_base (b := 2) (n := n + 1)
        (by omega) (by positivity)]

lemma tendsto_shifted_natLog2_div :
    Tendsto (fun n : ℕ => (Nat.log2 (n + 1) : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have hbase : Tendsto
      (fun n : ℕ => (Nat.log2 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply] using
      (GenLimit.tendsto_natLog2_div).comp (tendsto_add_atTop_nat 1)
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hfactor : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (n : ℝ))
      atTop (𝓝 1) := by
    have hadd := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add hinv
    have heq : (fun n : ℕ => (1 : ℝ) + 1 / (n : ℝ)) =ᶠ[atTop]
        (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (n : ℝ)) := by
      filter_upwards [eventually_ne_atTop 0] with n hn
      push_cast
      field_simp
    simpa only [add_zero] using hadd.congr' heq
  have hmul := hbase.mul hfactor
  have heq :
      (fun n : ℕ => (Nat.log2 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) *
        (((n + 1 : ℕ) : ℝ) / (n : ℝ))) =ᶠ[atTop]
      (fun n : ℕ => (Nat.log2 (n + 1) : ℝ) / (n : ℝ)) := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    push_cast
    field_simp
  simpa only [zero_mul] using hmul.congr' heq

lemma tendsto_core_error :
    Tendsto (fun n : ℕ => ((Nat.log2 (12 * n + 10) + 1 : ℕ) : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
  have hlog := tendsto_shifted_natLog2_div
  have hconst : Tendsto (fun n : ℕ => (5 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  let upper : ℕ → ℝ := fun n =>
    ((Nat.log2 (n + 1) + 5 : ℕ) : ℝ) / (n : ℝ)
  have hupper : Tendsto upper atTop (𝓝 0) := by
    simpa only [upper, Nat.cast_add, Nat.cast_ofNat, add_div, zero_add] using hlog.add hconst
  apply squeeze_zero
  · intro n
    positivity
  · intro n
    apply div_le_div_of_nonneg_right
    · change ((Nat.log2 (12 * n + 10) + 1 : ℕ) : ℝ) ≤
        ((Nat.log2 (n + 1) + 5 : ℕ) : ℝ)
      exact_mod_cast Nat.add_le_add_right (log2_linear_le n) 1
    · positivity
  · exact hupper

lemma orderedTarget_core_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity core = 0 := by
  have hbound : ∀ n, (orderedTarget gen).prefixRatio core n ≤
      ((Nat.log2 (12 * n + 10) + 1 : ℕ) : ℝ) / (n : ℝ) := by
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · simp only [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, hn, if_false]
      apply div_le_div_of_nonneg_right
      · exact_mod_cast orderedTarget_prefixCount_core_le gen n
      · positivity
  have htendsto : Tendsto ((orderedTarget gen).prefixRatio core) atTop (𝓝 0) :=
    squeeze_zero
      (fun n => (orderedTarget gen).prefixRatio_nonneg core n)
      hbound tendsto_core_error
  exact htendsto.limsup_eq

lemma orderedTarget_scored_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity
      (scored (target gen) (presentation gen) (output gen)) = 0 := by
  apply le_antisymm
  · calc
      (orderedTarget gen).upperDensity
          (scored (target gen) (presentation gen) (output gen)) ≤
          (orderedTarget gen).upperDensity core :=
        (orderedTarget gen).upperDensity_mono (scored_subset_core gen)
      _ = 0 := orderedTarget_core_upperDensity_zero gen
  · exact (orderedTarget gen).upperDensity_nonneg _

end Stage3Proof
