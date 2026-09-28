import S2BFormalization

open Set Function Filter
open Stage3S2B

namespace Stage3S2BProof

lemma odd_round_bound (gen : FeedbackGenerator) (k : ℕ) :
    runPresentation gen (2 * k + 1) ≤ 12 * k + 9 := by
  have hodd : ¬ Even (2 * k + 1) := Nat.not_even_iff_odd.mpr ⟨k, by omega⟩
  rw [runPresentation_of_not_even gen hodd]
  have hmiss := missingIndex_le_card (usedValues (runPrefix gen (2 * k + 1)))
  have hcard := usedValues_card_le (runPrefix gen (2 * k + 1))
  unfold oddCode
  omega

lemma runTarget_infinite (gen : FeedbackGenerator) : (runTarget gen).Infinite := by
  exact (Set.infinite_range_of_injective core_injective).mono (core_subset_runTarget gen)

noncomputable def orderedRunTarget (gen : FeedbackGenerator) : OrderedLanguage where
  carrier := runTarget gen
  enumeration := Nat.nth (fun z => z ∈ runTarget gen)
  enumeration_injective := Nat.nth_injective (runTarget_infinite gen)
  range_enumeration := Nat.range_nth_of_infinite (runTarget_infinite gen)

lemma orderedRunTarget_strictMono (gen : FeedbackGenerator) :
    StrictMono (orderedRunTarget gen).enumeration := by
  exact Nat.nth_strictMono (runTarget_infinite gen)

lemma scored_subset_core (gen : FeedbackGenerator) :
    scored (runTarget gen) (runTranscript gen).presentation (runTranscript gen).output ⊆ core := by
  intro z hz
  rcases hz with ⟨hzK, t, hout, hfresh⟩
  by_contra hcore
  have hord : z ∈ ordinary := hcore
  change runOutput gen t = z at hout
  change z ∉ observedThrough (runPresentation gen) t at hfresh
  obtain ⟨s, hs⟩ := hzK
  by_cases hst : s ≤ t
  · apply hfresh
    exact ⟨s, hst, by simpa [runTranscript] using hs⟩
  · have hordout : runOutput gen t ∈ ordinary := by rw [hout]; exact hord
    exact (future_presentation_ne_output gen (lt_of_not_ge hst) hordout) (hs.trans hout.symm)

noncomputable def ambientCount (A : Set ℕ) (B : ℕ) : ℕ := by
  classical
  exact ((Finset.range B).filter fun z => z ∈ A).card

lemma target_count_lower (gen : FeedbackGenerator) (n : ℕ) :
    n + 1 ≤ ambientCount (runTarget gen) (12 * n + 10) := by
  classical
  unfold ambientCount
  let f : ℕ → ℕ := fun k => runPresentation gen (2 * k + 1)
  let S := (Finset.range (n + 1)).image f
  have hf : Function.Injective f := by
    apply (runPresentation_injective gen).comp
    intro a b h
    simp [f] at h
    omega
  have hcard : S.card = n + 1 := by
    simp [S, Finset.card_image_of_injective _ hf]
  rw [← hcard]
  apply Finset.card_le_card
  intro z hz
  simp only [S, Finset.mem_image, Finset.mem_range] at hz
  obtain ⟨k, hk, rfl⟩ := hz
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact lt_of_le_of_lt (odd_round_bound gen k) (by omega)
  · exact ⟨2 * k + 1, rfl⟩

lemma ordered_nth_bound (gen : FeedbackGenerator) (n : ℕ) :
    (orderedRunTarget gen).enumeration n < 12 * n + 10 := by
  classical
  apply Nat.nth_lt_of_lt_count
  rw [Nat.count_eq_card_filter_range]
  exact lt_of_lt_of_le (Nat.lt_succ_self n) (target_count_lower gen n)

lemma core_count_upper (B : ℕ) :
    ambientCount core B ≤ Nat.log2 B + 1 := by
  classical
  unfold ambientCount
  let S := (Finset.range B).filter (fun z => z ∈ core)
  let T := (Finset.range (Nat.log2 B + 1)).image (fun k : ℕ => 2 ^ k)
  have hsub : S ⊆ T := by
    intro z hz
    simp only [S, Finset.mem_filter, Finset.mem_range] at hz
    obtain ⟨k, rfl⟩ := hz.2
    simp only [T, Finset.mem_image, Finset.mem_range]
    refine ⟨k, ?_, rfl⟩
    rw [Nat.log2_eq_log_two]
    have hklog : k ≤ Nat.log 2 (2 ^ k) := Nat.le_log_of_pow_le (by omega) le_rfl
    have hmono : Nat.log 2 (2 ^ k) ≤ Nat.log 2 B := Nat.log_mono_right (Nat.le_of_lt hz.1)
    omega
  calc
    S.card ≤ T.card := Finset.card_le_card hsub
    _ ≤ (Finset.range (Nat.log2 B + 1)).card := Finset.card_image_le
    _ = Nat.log2 B + 1 := Finset.card_range _

lemma prefixCount_core_upper (gen : FeedbackGenerator) (n : ℕ) :
    (orderedRunTarget gen).prefixCount core n ≤ Nat.log2 (12 * n + 10) + 1 := by
  classical
  unfold GenLimit.KleinbergWei.OrderedLanguage.prefixCount
  let S := (Finset.range n).filter (fun i => (orderedRunTarget gen).enumeration i ∈ core)
  let T := (Finset.range (12 * n + 10)).filter (fun z => z ∈ core)
  have hcardImage : (S.image (orderedRunTarget gen).enumeration).card = S.card := by
    exact Finset.card_image_of_injective _ (orderedRunTarget gen).enumeration_injective
  rw [← hcardImage]
  have hsub : S.image (orderedRunTarget gen).enumeration ⊆ T := by
    intro z hz
    simp only [Finset.mem_image, S, Finset.mem_filter, Finset.mem_range] at hz
    obtain ⟨i, ⟨hi, hicore⟩, rfl⟩ := hz
    simp only [T, Finset.mem_filter, Finset.mem_range]
    exact ⟨lt_of_lt_of_le (ordered_nth_bound gen i) (by omega), hicore⟩
  calc
    (S.image (orderedRunTarget gen).enumeration).card ≤ T.card := Finset.card_le_card hsub
    _ = ambientCount core (12 * n + 10) := by rfl
    _ ≤ Nat.log2 (12 * n + 10) + 1 := core_count_upper _

lemma log_linear_bound {n : ℕ} (hn : n ≠ 0) :
    Nat.log2 (12 * n + 10) ≤ Nat.log2 n + 5 := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  have hnPow : n < 2 ^ (Nat.log 2 n + 1) := by
    simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self (by omega : 1 < 2) n
  have hbound : 12 * n + 10 < 2 ^ (Nat.log 2 n + 6) := by
    calc
      12 * n + 10 ≤ 22 * n := by omega
      _ < 32 * 2 ^ (Nat.log 2 n + 1) := by omega
      _ = 2 ^ (Nat.log 2 n + 6) := by
        rw [show 32 = 2 ^ 5 by norm_num, ← pow_add]
        congr 1
        omega
  have hlog : Nat.log 2 (12 * n + 10) < Nat.log 2 n + 6 :=
    Nat.log_lt_of_lt_pow (by omega) hbound
  omega

lemma prefixRatio_core_tendsto_zero (gen : FeedbackGenerator) :
    Tendsto ((orderedRunTarget gen).prefixRatio core) atTop (nhds 0) := by
  apply squeeze_zero
    (fun n => (orderedRunTarget gen).prefixRatio_nonneg core n)
    (fun n => ?_)
  · simpa [Nat.add_comm] using GenLimit.tendsto_countingError_div 6
  · by_cases hn : n = 0
    · simp [hn]
    · simp only [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, hn, if_false]
      apply div_le_div_of_nonneg_right
      · exact_mod_cast (prefixCount_core_upper gen n).trans (by
          have := log_linear_bound hn
          omega)
      · positivity

lemma upperDensity_core_zero (gen : FeedbackGenerator) :
    (orderedRunTarget gen).upperDensity core = 0 := by
  exact (prefixRatio_core_tendsto_zero gen).limsup_eq

lemma upperDensity_scored_zero (gen : FeedbackGenerator) :
    (orderedRunTarget gen).upperDensity
      (scored (runTarget gen) (runTranscript gen).presentation (runTranscript gen).output) = 0 := by
  apply le_antisymm
  · calc
      (orderedRunTarget gen).upperDensity
          (scored (runTarget gen) (runTranscript gen).presentation (runTranscript gen).output) ≤
          (orderedRunTarget gen).upperDensity core :=
        (orderedRunTarget gen).upperDensity_mono (scored_subset_core gen)
      _ = 0 := upperDensity_core_zero gen
  · exact (orderedRunTarget gen).upperDensity_nonneg _

lemma negative_claim : NegativeClaim := by
  intro gen _hgen
  refine ⟨runTarget gen, runTarget_mem_targetClass gen,
    runPresenter gen, runTranscript gen, orderedRunTarget gen, ?_⟩
  refine ⟨rfl, orderedRunTarget_strictMono gen, run_presented gen,
    run_follows_protocol gen, run_clean gen, runPresentation_injective gen,
    run_complete gen, upperDensity_scored_zero gen⟩

end Stage3S2BProof

example : Stage3S2B.MainClaim := by
  exact ⟨Stage3S2BProof.targetClass_not_countable, Stage3S2BProof.uniform_without_samples, Stage3S2BProof.negative_claim⟩
