import Case019Formalization
import Mathlib.Data.Nat.Nth

open Set Filter
open scoped Topology
open GenLimit GenLimit.Generic

namespace Test

open GenLimit.NoiseLossFeedback GenLimit.UnionClosedness

noncomputable def uncountableEmbedding (q : ℕ) (A : Set ℕ) : Set ℤ :=
  (↑(omissionMarkerFinset q) : Set ℤ) ∪ positiveIntegers ∪ negativeCode '' A

lemma uncountableEmbedding_mem (q : ℕ) (A : Set ℕ) :
    uncountableEmbedding q A ∈ finiteOmissionClass q := by
  left
  refine ⟨?_, 0, ?_⟩
  · intro z hz; exact Or.inl (Or.inl hz)
  · rintro z ⟨k, rfl⟩
    simpa using Or.inl (Or.inr (positiveCode_mem k))

lemma uncountableEmbedding_injective (q : ℕ) :
    Function.Injective (uncountableEmbedding q) := by
  intro A B h
  ext n
  have hneg : negativeCode n ∉ (↑(omissionMarkerFinset q) : Set ℤ) :=
    negativeCode_not_marker q n
  have hnotpos : negativeCode n ∉ positiveIntegers := by
    exact Int.not_lt_of_ge (Int.le_of_lt (negativeCode_mem n))
  have hiff (C : Set ℕ) : negativeCode n ∈ uncountableEmbedding q C ↔ n ∈ C := by
    simp [uncountableEmbedding, hneg, hnotpos,
      Set.mem_image, negativeCode_injective.eq_iff]
  rw [← hiff A, h, hiff B]

lemma finiteOmissionClass_not_countable (q : ℕ) :
    ¬(finiteOmissionClass q).Countable := by
  intro hc
  have hrange : (Set.range (uncountableEmbedding q)).Countable :=
    hc.mono (by rintro _ ⟨A, rfl⟩; exact uncountableEmbedding_mem q A)
  have huniv : (Set.univ : Set (Set ℕ)).Countable := by
    apply Set.countable_of_injective_of_countable_image
      (s := (Set.univ : Set (Set ℕ)))
      (f := uncountableEmbedding q)
    · exact (uncountableEmbedding_injective q).injOn
    · simpa only [Set.image_univ] using hrange
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ
    (Set.countable_univ_iff.mp huniv)

lemma separation_negative (q : ℕ) (gen : Generator ℤ) :
    ∃ K ∈ finiteOmissionClass q, ∃ input : Stream ℤ,
      InjectiveValueContaminatedPresentationAtMost input K (q+1) ∧
      ¬Stage3Case019.SampleFreshGeneratesAfterInput
        input (Stage3Case019.outputAfterInput gen input) K := by
  by_contra h
  push_neg at h
  apply finiteNoiseLevel_lower q
  refine ⟨gen, ?_⟩
  intro K hK input hinput
  exact h K hK input hinput

end Test

namespace Test

open GenLimit.NoiseLossFeedback GenLimit.UnionClosedness

noncomputable def missingIndex (code : ℕ → ℤ) (n : ℕ) {m : ℕ}
    (xs : Fin m → ℤ) : ℕ :=
  Nat.nth (fun k => code k ∉ GenLimit.Generic.sequenceSample xs) n

lemma missingSet_infinite (code : ℕ → ℤ) (hcode : Function.Injective code)
    {m : ℕ} (xs : Fin m → ℤ) :
    {k | code k ∉ GenLimit.Generic.sequenceSample xs}.Infinite := by
  have hfin : {k | code k ∈ GenLimit.Generic.sequenceSample xs}.Finite :=
    (GenLimit.Generic.sequenceSample xs).finite_toSet.preimage hcode.injOn
  simpa only [Set.compl_setOf] using hfin.infinite_compl

lemma missingIndex_missing (code : ℕ → ℤ) (hcode : Function.Injective code)
    (n : ℕ) {m : ℕ} (xs : Fin m → ℤ) :
    code (missingIndex code n xs) ∉ GenLimit.Generic.sequenceSample xs := by
  exact Nat.nth_mem_of_infinite (missingSet_infinite code hcode xs) n

lemma missingIndex_ge (code : ℕ → ℤ) (hcode : Function.Injective code)
    (n : ℕ) {m : ℕ} (xs : Fin m → ℤ) :
    n ≤ missingIndex code n xs := by
  exact Nat.le_nth (fun hf => (missingSet_infinite code hcode xs) hf |>.elim)

lemma count_pred_mono {p r : ℕ → Prop} [DecidablePred p] [DecidablePred r]
    (hpr : ∀ k, p k → r k) (n : ℕ) : Nat.count p n ≤ Nat.count r n := by
  simp only [Nat.count_eq_card_filter_range]
  apply Finset.card_le_card
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
  exact ⟨hk.1, hpr k hk.2⟩

lemma missingIndex_strict_stream (code : ℕ → ℤ) (hcode : Function.Injective code)
    (stream : ℕ → ℤ) {s t : ℕ} (hst : s < t) :
    missingIndex code (s+1) (fun k : Fin (s+1) => stream k) <
      missingIndex code (t+1) (fun k : Fin (t+1) => stream k) := by
  classical
  let ps : ℕ → Prop := fun k => code k ∉ GenLimit.Generic.sample stream (s+1)
  let pt : ℕ → Prop := fun k => code k ∉ GenLimit.Generic.sample stream (t+1)
  have hsampS : GenLimit.Generic.sequenceSample (fun k : Fin (s+1) => stream k) =
      GenLimit.Generic.sample stream (s+1) := GenLimit.Generic.sequenceSample_prefix _ _
  have hsampT : GenLimit.Generic.sequenceSample (fun k : Fin (t+1) => stream k) =
      GenLimit.Generic.sample stream (t+1) := GenLimit.Generic.sequenceSample_prefix _ _
  have hps : {k | ps k}.Infinite := by
    simpa [ps, hsampS] using missingSet_infinite code hcode
      (fun k : Fin (s+1) => stream k)
  have hpt : {k | pt k}.Infinite := by
    simpa [pt, hsampT] using missingSet_infinite code hcode
      (fun k : Fin (t+1) => stream k)
  have hsub : ∀ k, pt k → ps k := by
    intro k hk hmem
    exact hk (GenLimit.Generic.sample_mono (by omega) hmem)
  rw [missingIndex, missingIndex, hsampS, hsampT]
  change Nat.nth ps (s+1) < Nat.nth pt (t+1)
  by_contra hnot
  have hle : Nat.nth pt (t+1) ≤ Nat.nth ps (s+1) := Nat.le_of_not_gt hnot
  have hc1 : Nat.count pt (Nat.nth pt (t+1)) ≤
      Nat.count ps (Nat.nth pt (t+1)) := count_pred_mono hsub _
  have hc2 : Nat.count ps (Nat.nth pt (t+1)) ≤
      Nat.count ps (Nat.nth ps (s+1)) := Nat.count_monotone ps hle
  rw [Nat.count_nth_of_infinite hpt] at hc1
  rw [Nat.count_nth_of_infinite hps] at hc2
  omega

noncomputable def denseNoiseSweepGenerator (q : ℕ) : Generator ℤ :=
  fun n xs =>
    if omissionMarkerFinset q ⊆ GenLimit.Generic.sequenceSample xs then
      positiveCode (missingIndex positiveCode n xs)
    else
      negativeCode (missingIndex negativeCode n xs)

end Test

namespace Test

open GenLimit.NoiseLossFeedback GenLimit.UnionClosedness

lemma denseNoiseSweep_first_novel
    {q : ℕ} {K : Set ℤ} (hK : K ∈ finiteOmissionFirstClass q)
    {input : Stream ℤ}
    (hinput : InjectiveValueContaminatedPresentationAtMost input K q) :
    Stage3Case019.NovelGeneratesAfterInput input
      (Stage3Case019.outputAfterInput (denseNoiseSweepGenerator q) input) K := by
  obtain ⟨hmarkers, j, htail⟩ := hK
  obtain ⟨Td, hTd⟩ := allMarkers_eventually_observed hinput hmarkers
  refine ⟨max Td j, ?_⟩
  intro t ht
  have hdetect : omissionMarkerFinset q ⊆ observedThrough input t :=
    hTd t ((Nat.le_max_left _ _).trans ht)
  have hsample : GenLimit.Generic.sequenceSample (fun k : Fin (t+1) => input k) =
      observedThrough input t := GenLimit.Generic.sequenceSample_prefix _ _
  have hout : Stage3Case019.outputAfterInput (denseNoiseSweepGenerator q) input t =
      positiveCode (missingIndex positiveCode (t+1)
        (fun k : Fin (t+1) => input k)) := by
    simp [Stage3Case019.outputAfterInput, GenLimit.Generic.output,
      denseNoiseSweepGenerator, hsample, hdetect]
  rw [hout]
  constructor
  · apply htail
    refine ⟨missingIndex positiveCode (t+1) (fun k : Fin (t+1) => input k) - j, ?_⟩
    have hge := missingIndex_ge positiveCode positiveCode_injective (t+1)
      (fun k : Fin (t+1) => input k)
    change positiveCode (j + (missingIndex positiveCode (t+1)
      (fun k : Fin (t+1) => input k) - j)) = _
    rw [Nat.add_sub_of_le]
    omega
  constructor
  · simpa [hsample] using
      missingIndex_missing positiveCode positiveCode_injective (t+1)
        (fun k : Fin (t+1) => input k)
  · intro s hs
    have hsampleS : GenLimit.Generic.sequenceSample (fun k : Fin (s+1) => input k) =
        observedThrough input s := GenLimit.Generic.sequenceSample_prefix _ _
    by_cases hdetectS : omissionMarkerFinset q ⊆ observedThrough input s
    · have houtS : Stage3Case019.outputAfterInput (denseNoiseSweepGenerator q) input s =
          positiveCode (missingIndex positiveCode (s+1)
            (fun k : Fin (s+1) => input k)) := by
        simp [Stage3Case019.outputAfterInput, GenLimit.Generic.output,
          denseNoiseSweepGenerator, hsampleS, hdetectS]
      rw [houtS]
      exact fun heq => (ne_of_lt
        (missingIndex_strict_stream positiveCode positiveCode_injective input hs))
          (positiveCode_injective heq)
    · have houtS : Stage3Case019.outputAfterInput (denseNoiseSweepGenerator q) input s =
          negativeCode (missingIndex negativeCode (s+1)
            (fun k : Fin (s+1) => input k)) := by
        simp [Stage3Case019.outputAfterInput, GenLimit.Generic.output,
          denseNoiseSweepGenerator, hsampleS, hdetectS]
      rw [houtS]
      intro heq
      have hn := negativeCode_mem (missingIndex negativeCode (s+1)
        (fun k : Fin (s+1) => input k))
      have hp := positiveCode_mem (missingIndex positiveCode (t+1)
        (fun k : Fin (t+1) => input k))
      rw [heq] at hn
      exact (Int.not_lt_of_ge (Int.le_of_lt hp)) hn

lemma denseNoiseSweep_second_novel
    {q : ℕ} {K : Set ℤ} (hK : K ∈ finiteOmissionSecondClass q)
    {input : Stream ℤ}
    (hinput : InjectiveValueContaminatedPresentationAtMost input K q) :
    Stage3Case019.NovelGeneratesAfterInput input
      (Stage3Case019.outputAfterInput (denseNoiseSweepGenerator q) input) K := by
  refine ⟨0, ?_⟩
  intro t _
  have hno : ¬omissionMarkerFinset q ⊆ observedThrough input t :=
    not_allMarkers_observed_second hK hinput t
  have hsample : GenLimit.Generic.sequenceSample (fun k : Fin (t+1) => input k) =
      observedThrough input t := GenLimit.Generic.sequenceSample_prefix _ _
  have hout : Stage3Case019.outputAfterInput (denseNoiseSweepGenerator q) input t =
      negativeCode (missingIndex negativeCode (t+1)
        (fun k : Fin (t+1) => input k)) := by
    simp [Stage3Case019.outputAfterInput, GenLimit.Generic.output,
      denseNoiseSweepGenerator, hsample, hno]
  rw [hout]
  constructor
  · exact hK.1 (negativeCode_mem _)
  constructor
  · simpa [hsample] using
      missingIndex_missing negativeCode negativeCode_injective (t+1)
        (fun k : Fin (t+1) => input k)
  · intro s hs
    have hnoS : ¬omissionMarkerFinset q ⊆ observedThrough input s :=
      not_allMarkers_observed_second hK hinput s
    have hsampleS : GenLimit.Generic.sequenceSample (fun k : Fin (s+1) => input k) =
        observedThrough input s := GenLimit.Generic.sequenceSample_prefix _ _
    have houtS : Stage3Case019.outputAfterInput (denseNoiseSweepGenerator q) input s =
        negativeCode (missingIndex negativeCode (s+1)
          (fun k : Fin (s+1) => input k)) := by
      simp [Stage3Case019.outputAfterInput, GenLimit.Generic.output,
        denseNoiseSweepGenerator, hsampleS, hnoS]
    rw [houtS]
    exact fun heq => (ne_of_lt
      (missingIndex_strict_stream negativeCode negativeCode_injective input hs))
        (negativeCode_injective heq)

end Test

namespace Test

lemma sequenceSample_card_le {α : Type*}
    {m : ℕ} (xs : Fin m → α) :
    (GenLimit.Generic.sequenceSample xs).card ≤ m := by
  classical
  unfold GenLimit.Generic.sequenceSample
  exact Finset.card_image_le.trans (by simp)

lemma missingIndex_le_add (code : ℕ → ℤ) (hcode : Function.Injective code)
    (n : ℕ) {m : ℕ} (xs : Fin m → ℤ) :
    missingIndex code n xs ≤ n + m := by
  classical
  let sample := GenLimit.Generic.sequenceSample xs
  let p : ℕ → Prop := fun k => code k ∉ sample
  let present := (Finset.range (n+m+1)).filter (fun k => code k ∈ sample)
  have himage : present.image code ⊆ sample := by
    intro z hz
    simp only [Finset.mem_image] at hz
    obtain ⟨k, hk, rfl⟩ := hz
    exact (Finset.mem_filter.mp hk).2
  have hpresent : present.card ≤ m := by
    calc
      present.card = (present.image code).card :=
        (Finset.card_image_iff.mpr (fun a _ b _ hab => hcode hab)).symm
      _ ≤ sample.card := Finset.card_le_card himage
      _ ≤ m := sequenceSample_card_le xs
  have hpartition := Finset.filter_card_add_filter_neg_card_eq_card
    (s := Finset.range (n+m+1)) (p := fun k => code k ∈ sample)
  have hcount : n < Nat.count p (n+m+1) := by
    rw [Nat.count_eq_card_filter_range]
    change n < ((Finset.range (n+m+1)).filter fun k => code k ∉ sample).card
    change n < ((Finset.range (n+m+1)).filter fun k => ¬code k ∈ sample).card
    dsimp [present] at hpresent
    rw [Finset.card_range] at hpartition
    omega
  have hlt : Nat.nth p n < n+m+1 := Nat.nth_lt_of_lt_count hcount
  simpa [missingIndex, p, sample] using Nat.lt_succ_iff.mp hlt

lemma balanced_negativeCode (n : ℕ) :
    Stage3Case019.balanced (2*n+1) = GenLimit.UnionClosedness.negativeCode n := by
  simp [Stage3Case019.balanced, GenLimit.UnionClosedness.negativeCode, Int.negSucc_eq]

lemma balanced_positiveCode (n : ℕ) :
    Stage3Case019.balanced (2*n+2) = GenLimit.UnionClosedness.positiveCode n := by
  simp [Stage3Case019.balanced, GenLimit.UnionClosedness.positiveCode]
  omega

end Test

namespace Test

lemma relativeLowerDensity_quarter_of_counting
    {A K : Set ℕ} (hK : K.Infinite) (hA : A ⊆ K) (C : ℕ)
    (hcount : ∀ n, GenLimit.PatientScope.prefixCount K n ≤
      4 * GenLimit.PatientScope.prefixCount A n + C) :
    (1 / 4 : ℝ) ≤ GenLimit.PatientScope.relativeLowerDensity A K := by
  let N := GenLimit.PatientScope.prefixCount K
  let D := GenLimit.PatientScope.prefixCount A
  let g : ℕ → ℝ := fun n => (1/4 : ℝ) - (C : ℝ) / (4 * (N n : ℝ))
  have hN : Tendsto N atTop atTop :=
    GenLimit.PatientScope.tendsto_prefixCount_atTop hK
  have hcast : Tendsto (fun n => (N n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have herr : Tendsto (fun n => (C : ℝ) / (4 * (N n : ℝ))) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => (C : ℝ)) atTop (𝓝 (C : ℝ)) := tendsto_const_nhds
    have hfour : Tendsto (fun n => 4 * (N n : ℝ)) atTop atTop :=
      hcast.const_mul_atTop (by norm_num : (0 : ℝ) < 4)
    exact hc.div_atTop hfour
  have hg : Tendsto g atTop (𝓝 (1/4 : ℝ)) := by
    simpa [g] using tendsto_const_nhds.sub herr
  have hNpos : ∀ᶠ n : ℕ in atTop, 0 < N n :=
    hN.eventually (eventually_gt_atTop 0)
  have hcompare : ∀ᶠ n : ℕ in atTop,
      g n ≤ (D n : ℝ) / (N n : ℝ) := by
    filter_upwards [hNpos] with n hn
    have hnR : (0 : ℝ) < N n := by exact_mod_cast hn
    have hcR : (N n : ℝ) ≤ 4 * (D n : ℝ) + C := by
      exact_mod_cast hcount n
    dsimp [g]
    rw [le_div_iff₀ hnR]
    field_simp [hnR.ne']
    nlinarith
  unfold GenLimit.PatientScope.relativeLowerDensity
  change (1/4 : ℝ) ≤ liminf (fun n => (D n : ℝ) / (N n : ℝ)) atTop
  calc
    (1/4 : ℝ) = liminf g atTop := hg.liminf_eq.symm
    _ ≤ _ := liminf_le_liminf hcompare hg.isBoundedUnder_ge
      (isCoboundedUnder_ge_of_le atTop (fun n => relativeRatio_le_one hA n))

lemma rank_mem_generatorFirst
    {gen : Generator ℤ} {input : Stream ℤ} {K : Set ℤ} {T t r : ℕ}
    (hgood : ∀ u, T ≤ u →
      Stage3Case019.outputAfterInput gen input u ∈ K ∧
      Stage3Case019.outputAfterInput gen input u ∉ GenLimit.Generic.sample input (u+1) ∧
      ∀ s, s < u → Stage3Case019.outputAfterInput gen input s ≠
        Stage3Case019.outputAfterInput gen input u)
    (hT : T ≤ t)
    (hr : Stage3Case019.balanced r =
      Stage3Case019.outputAfterInput gen input t) :
    r ∈ Stage3Case019.balancedRanks
      (Stage3Case019.GeneratorFirstOn input
        (Stage3Case019.outputAfterInput gen input) ∩ K) := by
  have ht := hgood t hT
  change Stage3Case019.balanced r ∈
    Stage3Case019.GeneratorFirstOn input
      (Stage3Case019.outputAfterInput gen input) ∩ K
  rw [hr]
  refine ⟨?_, ht.1⟩
  refine ⟨t, rfl, ?_⟩
  intro s hs heq
  apply ht.2.1
  exact GenLimit.Generic.mem_sample_iff.mpr
    ⟨s, Nat.lt_succ_iff.mpr hs, heq⟩

end Test

namespace Test

lemma prefixCount_quarter_bound
    {A K : Set ℕ} (T : ℕ) (rank : ℕ → ℕ)
    (hrank : ∀ t, T ≤ t → rank t ∈ A)
    (hbound : ∀ t, T ≤ t → rank t < 4*t+7)
    (hinj : Set.InjOn rank {t | T ≤ t}) :
    ∀ n, GenLimit.PatientScope.prefixCount K n ≤
      4 * GenLimit.PatientScope.prefixCount A n + (4*T+7) := by
  classical
  intro n
  let rounds := Finset.Ico T (n/4-1)
  have hsubset : rounds.image rank ⊆
      (Finset.range n).filter (fun k => k ∈ A) := by
    intro r hr
    simp only [Finset.mem_image] at hr
    obtain ⟨t, ht, rfl⟩ := hr
    have ht' := Finset.mem_Ico.mp ht
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, hrank t ht'.1⟩
    have hb := hbound t ht'.1
    omega
  have himage : (rounds.image rank).card = rounds.card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    apply hinj
    · exact Finset.mem_Ico.mp ha |>.1
    · exact Finset.mem_Ico.mp hb |>.1
    · exact hab
  have hcard : rounds.card ≤ GenLimit.PatientScope.prefixCount A n := by
    unfold GenLimit.PatientScope.prefixCount
    rw [← himage]
    exact Finset.card_le_card hsubset
  have hrounds : rounds.card = n/4-1-T := by
    simp [rounds]
  have hKn : GenLimit.PatientScope.prefixCount K n ≤ n := by
    unfold GenLimit.PatientScope.prefixCount
    exact (Finset.card_filter_le _ _).trans (by simp)
  rw [hrounds] at hcard
  have hdiv : n % 4 + 4 * (n / 4) = n := Nat.mod_add_div n 4
  omega

end Test

namespace Test

open GenLimit.NoiseLossFeedback GenLimit.UnionClosedness

lemma first_balancedRanks_infinite {q : ℕ} {K : Set ℤ}
    (hK : K ∈ finiteOmissionFirstClass q) :
    (Stage3Case019.balancedRanks K).Infinite := by
  obtain ⟨_, j, htail⟩ := hK
  have hinj : Function.Injective (fun k : ℕ => 2*(j+k)+2) := by
    intro a b hab
    dsimp at hab
    omega
  apply (Set.infinite_range_of_injective hinj).mono
  rintro r ⟨k, rfl⟩
  change Stage3Case019.balanced (2*(j+k)+2) ∈ K
  rw [balanced_positiveCode]
  exact htail ⟨k, rfl⟩

lemma second_balancedRanks_infinite {q : ℕ} {K : Set ℤ}
    (hK : K ∈ finiteOmissionSecondClass q) :
    (Stage3Case019.balancedRanks K).Infinite := by
  have hinj : Function.Injective (fun k : ℕ => 2*k+1) := by
    intro a b hab
    dsimp at hab
    omega
  apply (Set.infinite_range_of_injective hinj).mono
  rintro r ⟨k, rfl⟩
  change Stage3Case019.balanced (2*k+1) ∈ K
  rw [balanced_negativeCode]
  exact hK.1 (negativeCode_mem k)

lemma denseNoiseSweep_first_density
    {q : ℕ} {K : Set ℤ} (hK : K ∈ finiteOmissionFirstClass q)
    {input : Stream ℤ}
    (hinput : InjectiveValueContaminatedPresentationAtMost input K q) :
    (1/4 : ℝ) ≤ Stage3Case019.balancedRelativeLowerDensity
      (Stage3Case019.GeneratorFirstOn input
        (Stage3Case019.outputAfterInput (denseNoiseSweepGenerator q) input) ∩ K) K := by
  let output := Stage3Case019.outputAfterInput (denseNoiseSweepGenerator q) input
  let A := Stage3Case019.balancedRanks
    (Stage3Case019.GeneratorFirstOn input output ∩ K)
  let KR := Stage3Case019.balancedRanks K
  obtain ⟨Tnov, hnov⟩ := denseNoiseSweep_first_novel hK hinput
  have hmarkers := hK.1
  obtain ⟨Td, hTd⟩ := allMarkers_eventually_observed hinput hmarkers
  let T := max Tnov Td
  let rank : ℕ → ℕ := fun t =>
    2 * missingIndex positiveCode (t+1) (fun k : Fin (t+1) => input k) + 2
  have hrank : ∀ t, T ≤ t → rank t ∈ A := by
    intro t ht
    have hdetect : omissionMarkerFinset q ⊆ observedThrough input t :=
      hTd t ((Nat.le_max_right _ _).trans ht)
    have hsample : GenLimit.Generic.sequenceSample (fun k : Fin (t+1) => input k) =
        observedThrough input t := GenLimit.Generic.sequenceSample_prefix _ _
    have hout : output t = positiveCode
        (missingIndex positiveCode (t+1) (fun k : Fin (t+1) => input k)) := by
      simp [output, Stage3Case019.outputAfterInput, GenLimit.Generic.output,
        denseNoiseSweepGenerator, hsample, hdetect]
    apply rank_mem_generatorFirst hnov ((Nat.le_max_left _ _).trans ht)
    dsimp [rank]
    rw [balanced_positiveCode]
    exact hout.symm
  have hbound : ∀ t, T ≤ t → rank t < 4*t+7 := by
    intro t _
    have hb := missingIndex_le_add positiveCode positiveCode_injective (t+1)
      (fun k : Fin (t+1) => input k)
    dsimp [rank]
    omega
  have hinj : Set.InjOn rank {t | T ≤ t} := by
    intro s hs t ht heq
    dsimp [rank] at heq
    have hidx : missingIndex positiveCode (s+1) (fun k : Fin (s+1) => input k) =
        missingIndex positiveCode (t+1) (fun k : Fin (t+1) => input k) := by omega
    by_contra hst
    rcases lt_or_gt_of_ne hst with hlt | hgt
    · exact (ne_of_lt (missingIndex_strict_stream positiveCode positiveCode_injective input hlt)) hidx
    · exact (ne_of_lt (missingIndex_strict_stream positiveCode positiveCode_injective input hgt)) hidx.symm
  have hcount := prefixCount_quarter_bound (K := KR) T rank hrank hbound hinj
  unfold Stage3Case019.balancedRelativeLowerDensity
  apply relativeLowerDensity_quarter_of_counting (A := A) (K := KR)
    (first_balancedRanks_infinite hK) (C := 4*T+7)
  · intro r hr
    exact hr.2
  · exact hcount

lemma denseNoiseSweep_second_density
    {q : ℕ} {K : Set ℤ} (hK : K ∈ finiteOmissionSecondClass q)
    {input : Stream ℤ}
    (hinput : InjectiveValueContaminatedPresentationAtMost input K q) :
    (1/4 : ℝ) ≤ Stage3Case019.balancedRelativeLowerDensity
      (Stage3Case019.GeneratorFirstOn input
        (Stage3Case019.outputAfterInput (denseNoiseSweepGenerator q) input) ∩ K) K := by
  let output := Stage3Case019.outputAfterInput (denseNoiseSweepGenerator q) input
  let A := Stage3Case019.balancedRanks
    (Stage3Case019.GeneratorFirstOn input output ∩ K)
  let KR := Stage3Case019.balancedRanks K
  obtain ⟨Tnov, hnov⟩ := denseNoiseSweep_second_novel hK hinput
  let rank : ℕ → ℕ := fun t =>
    2 * missingIndex negativeCode (t+1) (fun k : Fin (t+1) => input k) + 1
  have hrank : ∀ t, Tnov ≤ t → rank t ∈ A := by
    intro t ht
    have hno : ¬omissionMarkerFinset q ⊆ observedThrough input t :=
      not_allMarkers_observed_second hK hinput t
    have hsample : GenLimit.Generic.sequenceSample (fun k : Fin (t+1) => input k) =
        observedThrough input t := GenLimit.Generic.sequenceSample_prefix _ _
    have hout : output t = negativeCode
        (missingIndex negativeCode (t+1) (fun k : Fin (t+1) => input k)) := by
      simp [output, Stage3Case019.outputAfterInput, GenLimit.Generic.output,
        denseNoiseSweepGenerator, hsample, hno]
    apply rank_mem_generatorFirst hnov ht
    dsimp [rank]
    rw [balanced_negativeCode]
    exact hout.symm
  have hbound : ∀ t, Tnov ≤ t → rank t < 4*t+7 := by
    intro t _
    have hb := missingIndex_le_add negativeCode negativeCode_injective (t+1)
      (fun k : Fin (t+1) => input k)
    dsimp [rank]
    omega
  have hinj : Set.InjOn rank {t | Tnov ≤ t} := by
    intro s hs t ht heq
    dsimp [rank] at heq
    have hidx : missingIndex negativeCode (s+1) (fun k : Fin (s+1) => input k) =
        missingIndex negativeCode (t+1) (fun k : Fin (t+1) => input k) := by omega
    by_contra hst
    rcases lt_or_gt_of_ne hst with hlt | hgt
    · exact (ne_of_lt (missingIndex_strict_stream negativeCode negativeCode_injective input hlt)) hidx
    · exact (ne_of_lt (missingIndex_strict_stream negativeCode negativeCode_injective input hgt)) hidx.symm
  have hcount := prefixCount_quarter_bound (K := KR) Tnov rank hrank hbound hinj
  unfold Stage3Case019.balancedRelativeLowerDensity
  apply relativeLowerDensity_quarter_of_counting (A := A) (K := KR)
    (second_balancedRanks_infinite hK) (C := 4*Tnov+7)
  · intro r hr
    exact hr.2
  · exact hcount

end Test

namespace Test

open GenLimit.NoiseLossFeedback

lemma separation_clause : Stage3Case019.SeparationClause := by
  intro q
  refine ⟨finiteOmissionClass q, finiteOmissionClass_not_countable q,
    finiteOmissionClass_uus q, ?_, separation_negative q⟩
  refine ⟨denseNoiseSweepGenerator q, ?_⟩
  intro K hK input hinput
  rcases hK with hfirst | hsecond
  · exact ⟨denseNoiseSweep_first_novel hfirst hinput,
      denseNoiseSweep_first_density hfirst hinput⟩
  · exact ⟨denseNoiseSweep_second_novel hsecond hinput,
      denseNoiseSweep_second_density hsecond hinput⟩

end Test

theorem stage3_result : Stage3Case019.MainClaim :=
  ⟨Test.countable_half_density, Test.separation_clause⟩
