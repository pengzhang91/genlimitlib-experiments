import output.CountableProof
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Set Filter
open Stage3Case019
open scoped Topology

namespace Case019

open GenLimit.UnionClosedness
open GenLimit.NoiseLossFeedback

@[simp] theorem balanced_negative (n : ℕ) : balanced (2*n+1) = negativeCode n := by
  unfold balanced negativeCode
  simp [Nat.add_mod, Nat.mul_mod, Nat.add_div, Int.negSucc_eq]

@[simp] theorem balanced_positive (n : ℕ) : balanced (2*n+2) = positiveCode n := by
  unfold balanced positiveCode
  simp [Nat.add_mod, Nat.mul_mod, Nat.add_div]

theorem balanced_surjective : Function.Surjective balanced := by
  intro z
  rcases z with n | n
  · cases n with
    | zero => exact ⟨0, rfl⟩
    | succ n => exact ⟨2*n+2, balanced_positive n⟩
  · exact ⟨2*n+1, balanced_negative n⟩

end Case019

namespace Case019

private theorem exists_bounded_fresh_index
    (code : ℕ → ℤ) (hcode : Function.Injective code) (F : Finset ℤ) :
    ∃ n < F.card + 1, code n ∉ F := by
  classical
  by_contra h
  push_neg at h
  have hsub : (Finset.range (F.card + 1)).image code ⊆ F := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨n, hn, rfl⟩ := hz
    exact h n (Finset.mem_range.mp hn)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hcode, Finset.card_range] at hc
  omega

noncomputable def boundedFreshIndex
    (code : ℕ → ℤ) (hcode : Function.Injective code) (F : Finset ℤ) : ℕ :=
  Classical.choose (exists_bounded_fresh_index code hcode F)

private theorem boundedFreshIndex_lt
    (code : ℕ → ℤ) (hcode : Function.Injective code) (F : Finset ℤ) :
    boundedFreshIndex code hcode F < F.card + 1 :=
  (Classical.choose_spec (exists_bounded_fresh_index code hcode F)).1

private theorem boundedFreshIndex_fresh
    (code : ℕ → ℤ) (hcode : Function.Injective code) (F : Finset ℤ) :
    code (boundedFreshIndex code hcode F) ∉ F :=
  (Classical.choose_spec (exists_bounded_fresh_index code hcode F)).2

noncomputable def greedyIndices
    (code : ℕ → ℤ) (hcode : Function.Injective code)
    (input : Stream ℤ) : ℕ → List ℕ
  | 0 => []
  | t + 1 =>
      let previous := greedyIndices code hcode input t
      let forbidden := GenLimit.Generic.sample input (t + 1) ∪
        (previous.toFinset.image code)
      previous ++ [boundedFreshIndex code hcode forbidden]

@[simp] theorem greedyIndices_length
    (code : ℕ → ℤ) (hcode : Function.Injective code)
    (input : Stream ℤ) (t : ℕ) :
    (greedyIndices code hcode input t).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [greedyIndices, ih]

noncomputable def greedyOutput
    (code : ℕ → ℤ) (hcode : Function.Injective code)
    (input : Stream ℤ) (t : ℕ) : ℤ :=
  code ((greedyIndices code hcode input (t + 1)).getLast (by
    simp [greedyIndices]))

private theorem greedyOutput_eq_freshIndex
    (code : ℕ → ℤ) (hcode : Function.Injective code)
    (input : Stream ℤ) (t : ℕ) :
    greedyOutput code hcode input t =
      code (boundedFreshIndex code hcode
        (GenLimit.Generic.sample input (t + 1) ∪
          ((greedyIndices code hcode input t).toFinset.image code))) := by
  simp [greedyOutput, greedyIndices]

private theorem greedyOutput_fresh_sample
    (code : ℕ → ℤ) (hcode : Function.Injective code)
    (input : Stream ℤ) (t : ℕ) :
    greedyOutput code hcode input t ∉ GenLimit.Generic.sample input (t + 1) := by
  rw [greedyOutput_eq_freshIndex]
  exact fun h => boundedFreshIndex_fresh code hcode _ (Finset.mem_union_left _ h)

private theorem greedyOutput_index_bound
    (code : ℕ → ℤ) (hcode : Function.Injective code)
    (input : Stream ℤ) (t : ℕ) :
    ∃ n ≤ 2 * t + 1, greedyOutput code hcode input t = code n := by
  classical
  let F := GenLimit.Generic.sample input (t + 1) ∪
    ((greedyIndices code hcode input t).toFinset.image code)
  refine ⟨boundedFreshIndex code hcode F, ?_, greedyOutput_eq_freshIndex code hcode input t⟩
  have hsample : (GenLimit.Generic.sample input (t + 1)).card ≤ t + 1 := by
    exact GenLimit.Generic.sample_card_le input (t + 1)
  have hprevious : ((greedyIndices code hcode input t).toFinset.image code).card ≤ t := by
    calc
      _ ≤ (greedyIndices code hcode input t).toFinset.card := Finset.card_image_le
      _ ≤ (greedyIndices code hcode input t).length := List.toFinset_card_le _
      _ = t := greedyIndices_length code hcode input t
  have hF : F.card ≤ 2 * t + 1 := by
    exact (Finset.card_union_le _ _).trans (by omega)
  exact Nat.le_of_lt_succ ((boundedFreshIndex_lt code hcode F).trans_le (Nat.add_le_add_right hF 1))

end Case019

namespace Case019

private theorem sample_congr_int
    {a b : Stream ℤ} {n : ℕ} (h : ∀ k, k < n → a k = b k) :
    GenLimit.Generic.sample a n = GenLimit.Generic.sample b n := by
  ext x
  simp only [GenLimit.Generic.mem_sample_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, (h k hk).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, h k hk⟩

private theorem greedyIndices_congr
    (code : ℕ → ℤ) (hcode : Function.Injective code)
    {a b : Stream ℤ} {n : ℕ} (h : ∀ k, k < n → a k = b k) :
    greedyIndices code hcode a n = greedyIndices code hcode b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [greedyIndices]
      have hp := ih (fun k hk => h k (Nat.lt.step hk))
      rw [hp, sample_congr_int h]

private theorem greedyIndices_prefix
    (code : ℕ → ℤ) (hcode : Function.Injective code)
    (input : Stream ℤ) {s t : ℕ} (hst : s ≤ t) :
    greedyIndices code hcode input s <+: greedyIndices code hcode input t := by
  induction t, hst using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ t _ ih =>
      exact ih.trans (by simp [greedyIndices])

private theorem greedyOutput_mem_indices
    (code : ℕ → ℤ) (hcode : Function.Injective code)
    (input : Stream ℤ) {s t : ℕ} (hst : s < t) :
    greedyOutput code hcode input s ∈
      (greedyIndices code hcode input t).toFinset.image code := by
  rw [Finset.mem_image]
  let indices := greedyIndices code hcode input (s + 1)
  let last := indices.getLast (by simp [indices, greedyIndices])
  refine ⟨last, ?_, ?_⟩
  · rw [List.mem_toFinset]
    exact (greedyIndices_prefix code hcode input (Nat.succ_le_iff.mpr hst)).subset
      (List.getLast_mem _)
  · rfl

private theorem greedyOutput_ne_previous
    (code : ℕ → ℤ) (hcode : Function.Injective code)
    (input : Stream ℤ) {s t : ℕ} (hst : s < t) :
    greedyOutput code hcode input s ≠ greedyOutput code hcode input t := by
  intro heq
  have hmem := greedyOutput_mem_indices code hcode input hst
  have hfresh := boundedFreshIndex_fresh code hcode
    (GenLimit.Generic.sample input (t + 1) ∪
      ((greedyIndices code hcode input t).toFinset.image code))
  apply hfresh
  apply Finset.mem_union_right
  rw [← greedyOutput_eq_freshIndex code hcode input t]
  exact heq ▸ hmem


private theorem greedyOutput_congr
    (code : ℕ → ℤ) (hcode : Function.Injective code)
    {a b : Stream ℤ} {t : ℕ} (h : ∀ k, k < t + 1 → a k = b k) :
    greedyOutput code hcode a t = greedyOutput code hcode b t := by
  unfold greedyOutput
  congr 1
  apply List.getLast_congr
  exact greedyIndices_congr code hcode h

noncomputable def greedyPrefixGenerator
    (code : ℕ → ℤ) (hcode : Function.Injective code) : Generator ℤ :=
  fun n xs =>
    if hn : n = 0 then code 0
    else
      greedyOutput code hcode
        (fun k => if hk : k < n then xs ⟨k, hk⟩ else 0) (n - 1)

@[simp] theorem greedyPrefixGenerator_outputAfterInput
    (code : ℕ → ℤ) (hcode : Function.Injective code)
    (input : Stream ℤ) (t : ℕ) :
    outputAfterInput (greedyPrefixGenerator code hcode) input t =
      greedyOutput code hcode input t := by
  unfold outputAfterInput GenLimit.Generic.output greedyPrefixGenerator
  simp only [Nat.succ_ne_zero, ↓reduceDIte, Nat.add_sub_cancel]
  unfold greedyOutput
  congr 1
  apply List.getLast_congr
  apply greedyIndices_congr
  intro k hk
  rw [dif_pos hk]

end Case019

namespace Case019

open GenLimit.UnionClosedness
open GenLimit.NoiseLossFeedback

noncomputable def denseNoiseOutput (q : ℕ) (input : Stream ℤ) (t : ℕ) : ℤ :=
  if omissionMarkerFinset q ⊆ GenLimit.Generic.sample input (t + 1) then
    greedyOutput positiveCode positiveCode_injective input t
  else
    greedyOutput negativeCode negativeCode_injective input t

noncomputable def denseNoiseGenerator (q : ℕ) : Generator ℤ :=
  fun n xs =>
    if hn : n = 0 then 0
    else denseNoiseOutput q
      (fun k => if hk : k < n then xs ⟨k, hk⟩ else 0) (n - 1)

@[simp] theorem denseNoiseGenerator_outputAfterInput
    (q : ℕ) (input : Stream ℤ) (t : ℕ) :
    outputAfterInput (denseNoiseGenerator q) input t = denseNoiseOutput q input t := by
  unfold outputAfterInput GenLimit.Generic.output denseNoiseGenerator denseNoiseOutput
  simp only [Nat.succ_ne_zero, ↓reduceDIte, Nat.add_sub_cancel]
  have hp : ∀ k, k < t + 1 →
      (fun k => if hk : k < t + 1 then input k else 0) k = input k :=
    fun k hk => dif_pos hk
  rw [sample_congr_int hp]
  split_ifs
  · exact greedyOutput_congr positiveCode positiveCode_injective hp
  · exact greedyOutput_congr negativeCode negativeCode_injective hp

private theorem denseNoiseOutput_fresh_sample
    (q : ℕ) (input : Stream ℤ) (t : ℕ) :
    denseNoiseOutput q input t ∉ GenLimit.Generic.sample input (t + 1) := by
  unfold denseNoiseOutput
  split_ifs
  · exact greedyOutput_fresh_sample positiveCode positiveCode_injective input t
  · exact greedyOutput_fresh_sample negativeCode negativeCode_injective input t

private theorem marker_detection_mono
    {q s t : ℕ} {input : Stream ℤ} (hst : s ≤ t)
    (h : omissionMarkerFinset q ⊆ GenLimit.Generic.sample input (s + 1)) :
    omissionMarkerFinset q ⊆ GenLimit.Generic.sample input (t + 1) := by
  intro z hz
  exact GenLimit.Generic.sample_mono (by omega) (h hz)

private theorem positiveCode_ne_negativeCode (m n : ℕ) :
    positiveCode m ≠ negativeCode n := by
  intro h
  have hp : 0 < positiveCode m := positiveCode_mem m
  have hn : negativeCode n < 0 := negativeCode_mem n
  rw [h] at hp
  omega

private theorem denseNoiseOutput_ne_of_lt
    (q : ℕ) (input : Stream ℤ) {s t : ℕ} (hlt : s < t) :
    denseNoiseOutput q input s ≠ denseNoiseOutput q input t := by
  unfold denseNoiseOutput
  by_cases hs : omissionMarkerFinset q ⊆ GenLimit.Generic.sample input (s + 1)
  · have ht := marker_detection_mono (Nat.le_of_lt hlt) hs
    simp only [if_pos hs, if_pos ht]
    exact greedyOutput_ne_previous positiveCode positiveCode_injective input hlt
  · by_cases ht : omissionMarkerFinset q ⊆ GenLimit.Generic.sample input (t + 1)
    · simp only [if_neg hs, if_pos ht]
      obtain ⟨m, _hm, hm⟩ := greedyOutput_index_bound negativeCode negativeCode_injective input s
      obtain ⟨n, _hn, hn⟩ := greedyOutput_index_bound positiveCode positiveCode_injective input t
      rw [hm, hn]
      exact (positiveCode_ne_negativeCode n m).symm
    · simp only [if_neg hs, if_neg ht]
      exact greedyOutput_ne_previous negativeCode negativeCode_injective input hlt

private theorem denseNoiseOutput_injective
    (q : ℕ) (input : Stream ℤ) : Function.Injective (denseNoiseOutput q input) := by
  intro s t heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact denseNoiseOutput_ne_of_lt q input hlt heq
  · exact denseNoiseOutput_ne_of_lt q input hgt heq.symm

private theorem denseNoiseOutput_rank_bound
    (q : ℕ) (input : Stream ℤ) (t : ℕ) :
    ∃ r < 4 * t + 5, balanced r = denseNoiseOutput q input t := by
  unfold denseNoiseOutput
  split_ifs
  · obtain ⟨n, hn, hout⟩ := greedyOutput_index_bound positiveCode positiveCode_injective input t
    refine ⟨2*n+2, by omega, ?_⟩
    rw [balanced_positive, hout]
  · obtain ⟨n, hn, hout⟩ := greedyOutput_index_bound negativeCode negativeCode_injective input t
    refine ⟨2*n+1, by omega, ?_⟩
    rw [balanced_negative, hout]

private theorem denseNoiseOutput_eventually_mem_first
    {q : ℕ} {K : Set ℤ} (hK : K ∈ finiteOmissionFirstClass q)
    {input : Stream ℤ}
    (henum : NoisyEnumerationWithLevel input K q) :
    ∃ T, ∀ t, T ≤ t → denseNoiseOutput q input t ∈ K := by
  classical
  obtain ⟨hmarkers, j, htail⟩ := hK
  obtain ⟨Td, hTd⟩ := allMarkers_eventually_observed henum hmarkers
  let bad : Set ℕ := {t | denseNoiseOutput q input t ∉ K}
  have hbad : bad ⊆ Set.Iio Td ∪
      (denseNoiseOutput q input) ⁻¹' (positiveCode '' (Finset.range j : Set ℕ)) := by
    intro t ht
    by_cases htt : t < Td
    · exact Or.inl htt
    · right
      have hdetect := hTd t (Nat.le_of_not_gt htt)
      change denseNoiseOutput q input t ∈ positiveCode '' (Finset.range j : Set ℕ)
      unfold denseNoiseOutput
      rw [if_pos hdetect]
      obtain ⟨n, _hn, hout⟩ := greedyOutput_index_bound positiveCode positiveCode_injective input t
      rw [hout]
      have hnlt : n < j := by
        by_contra hn
        have hpos : positiveCode n ∈ K := htail ⟨n-j, by
          unfold positiveCode
          apply Int.ofNat_inj.mpr
          omega⟩
        exact ht (by simpa [denseNoiseOutput, hdetect, hout] using hpos)
      exact ⟨n, Finset.mem_coe.mpr (Finset.mem_range.mpr hnlt), rfl⟩
  have himageFinite : (positiveCode '' (Finset.range j : Set ℕ)).Finite :=
    (Finset.finite_toSet (Finset.range j)).image positiveCode
  have hpreFinite : ((denseNoiseOutput q input) ⁻¹'
      (positiveCode '' (Finset.range j : Set ℕ))).Finite :=
    himageFinite.preimage (denseNoiseOutput_injective q input).injOn
  have hbadFinite : bad.Finite :=
    (Set.finite_Iio Td).union hpreFinite |>.subset hbad
  refine ⟨if hne : bad.Nonempty then hbadFinite.toFinset.max' (by
    obtain ⟨t, ht⟩ := hne
    exact ⟨t, Set.Finite.mem_toFinset hbadFinite |>.2 ht⟩) + 1 else 0, ?_⟩
  intro t ht
  by_contra hnot
  have htbad : t ∈ bad := hnot
  split at ht
  · rename_i hne
    have hle := Finset.le_max' hbadFinite.toFinset t (Set.Finite.mem_toFinset hbadFinite |>.2 htbad)
    omega
  · rename_i hne
    exact hne ⟨t, htbad⟩

private theorem denseNoiseOutput_mem_second
    {q : ℕ} {K : Set ℤ} (hK : K ∈ finiteOmissionSecondClass q)
    {input : Stream ℤ}
    (henum : NoisyEnumerationWithLevel input K q) (t : ℕ) :
    denseNoiseOutput q input t ∈ K := by
  have hno := not_allMarkers_observed_second hK henum t
  unfold denseNoiseOutput
  rw [if_neg hno]
  obtain ⟨n, _hn, hout⟩ := greedyOutput_index_bound negativeCode negativeCode_injective input t
  rw [hout]
  exact hK.1 (negativeCode_mem n)

private theorem denseNoise_novel
    {q : ℕ} {K : Set ℤ} (hK : K ∈ finiteOmissionClass q)
    {input : Stream ℤ}
    (henum : NoisyEnumerationWithLevel input K q) :
    NovelGeneratesAfterInput input (denseNoiseOutput q input) K := by
  have hevent : ∃ T, ∀ t, T ≤ t → denseNoiseOutput q input t ∈ K := by
    rcases hK with hfirst | hsecond
    · exact denseNoiseOutput_eventually_mem_first hfirst henum
    · exact ⟨0, fun t _ => denseNoiseOutput_mem_second hsecond henum t⟩
  obtain ⟨T, hT⟩ := hevent
  refine ⟨T, fun t ht => ⟨hT t ht, denseNoiseOutput_fresh_sample q input t, ?_⟩⟩
  intro s hs
  intro heq
  exact Nat.ne_of_lt hs (denseNoiseOutput_injective q input heq)

end Case019

namespace Case019

noncomputable def denseNoiseRank (q : ℕ) (input : Stream ℤ) (t : ℕ) : ℕ :=
  Classical.choose (denseNoiseOutput_rank_bound q input t)

private theorem denseNoiseRank_lt (q : ℕ) (input : Stream ℤ) (t : ℕ) :
    denseNoiseRank q input t < 4 * t + 5 :=
  (Classical.choose_spec (denseNoiseOutput_rank_bound q input t)).1

private theorem balanced_denseNoiseRank (q : ℕ) (input : Stream ℤ) (t : ℕ) :
    balanced (denseNoiseRank q input t) = denseNoiseOutput q input t :=
  (Classical.choose_spec (denseNoiseOutput_rank_bound q input t)).2

private theorem denseNoiseRank_injective (q : ℕ) (input : Stream ℤ) :
    Function.Injective (denseNoiseRank q input) := by
  intro s t h
  apply denseNoiseOutput_injective q input
  rw [← balanced_denseNoiseRank q input s, ← balanced_denseNoiseRank q input t, h]

private theorem eventual_rank_count
    {q : ℕ} {input : Stream ℤ} {K : Set ℤ}
    (hnovel : NovelGeneratesAfterInput input (denseNoiseOutput q input) K) :
    ∃ T, ∀ n, 4 * (T + 2) ≤ n →
      n ≤ 4 * GenLimit.PatientScope.prefixCount
        (balancedRanks (GeneratorFirstOn input (denseNoiseOutput q input) ∩ K)) n +
        (4 * T + 7) := by
  classical
  obtain ⟨T, hT⟩ := hnovel
  refine ⟨T, ?_⟩
  intro n hn
  let upper := n / 4 - 1
  let times := Finset.Ico T upper
  let ranks := times.image (denseNoiseRank q input)
  have hupper : T ≤ upper := by
    dsimp [upper]
    omega
  have hranksCard : ranks.card = upper - T := by
    dsimp [ranks, times]
    rw [Finset.card_image_of_injective _ (denseNoiseRank_injective q input)]
    simp
  have hranksSubset : ranks ⊆ GenLimit.PatientScope.prefixFinset
      (balancedRanks (GeneratorFirstOn input (denseNoiseOutput q input) ∩ K)) n := by
    intro r hr
    rw [Finset.mem_image] at hr
    obtain ⟨t, ht, rfl⟩ := hr
    have htT : T ≤ t := (Finset.mem_Ico.mp ht).1
    have htupper : t < upper := (Finset.mem_Ico.mp ht).2
    apply GenLimit.PatientScope.mem_prefixFinset.mpr
    constructor
    · have hrl := denseNoiseRank_lt q input t
      dsimp [upper] at htupper
      omega
    · change balanced (denseNoiseRank q input t) ∈
        GeneratorFirstOn input (denseNoiseOutput q input) ∩ K
      rw [balanced_denseNoiseRank]
      have hgood := hT t htT
      refine ⟨?_, hgood.1⟩
      refine ⟨t, rfl, ?_⟩
      intro s hs
      intro heq
      apply hgood.2.1
      apply GenLimit.Generic.mem_sample_iff.mpr
      exact ⟨s, by omega, heq⟩
  have hcount : upper - T ≤ GenLimit.PatientScope.prefixCount
      (balancedRanks (GeneratorFirstOn input (denseNoiseOutput q input) ∩ K)) n := by
    rw [← hranksCard]
    exact Finset.card_le_card hranksSubset
  dsimp [upper] at hupper hcount
  omega

private theorem quarter_density_of_count_bound
    {A K : Set ℕ} (hK : K.Infinite) (hAK : A ⊆ K)
    (c N : ℕ) (hbound : ∀ n, N ≤ n →
      n ≤ 4 * GenLimit.PatientScope.prefixCount A n + c) :
    (1 / 4 : ℝ) ≤ GenLimit.PatientScope.relativeLowerDensity A K := by
  classical
  let denom : ℕ → ℕ := GenLimit.PatientScope.prefixCount K
  let numer : ℕ → ℕ := GenLimit.PatientScope.prefixCount A
  let ratio : ℕ → ℝ := fun n => (numer n : ℝ) / (denom n : ℝ)
  let error : ℕ → ℝ := fun n => (c : ℝ) / (4 * (denom n : ℝ))
  let lower : ℕ → ℝ := fun n => (1 / 4 : ℝ) - error n
  have hden := GenLimit.PatientScope.tendsto_prefixCount_atTop hK
  have hdenR : Tendsto (fun n => (denom n : ℝ)) atTop atTop := by
    simpa [denom, Function.comp_apply] using tendsto_natCast_atTop_atTop.comp hden
  have herr : Tendsto error atTop (𝓝 0) := by
    unfold error
    exact tendsto_const_nhds.div_atTop (hdenR.const_mul_atTop (by norm_num : (0 : ℝ) < 4))
  have hlower : Tendsto lower atTop (𝓝 (1 / 4 : ℝ)) := by
    simpa [lower] using tendsto_const_nhds.sub herr
  have hcompare : ∀ᶠ n in atTop, lower n ≤ ratio n := by
    filter_upwards [eventually_ge_atTop N, hden.eventually (eventually_gt_atTop 0)] with n hnN hpos
    have hKn : denom n ≤ n := by
      change ((Finset.range n).filter (fun x => x ∈ K)).card ≤ n
      simpa using Finset.card_filter_le (Finset.range n) (fun x => x ∈ K)
    have hraw := hbound n hnN
    have hcount : denom n ≤ 4 * numer n + c := by
      exact hKn.trans hraw
    have hposR : (0 : ℝ) < denom n := by exact_mod_cast hpos
    have hcountR : (denom n : ℝ) ≤ 4 * (numer n : ℝ) + c := by exact_mod_cast hcount
    dsimp [lower, error, ratio]
    rw [le_div_iff₀ hposR]
    field_simp [hposR.ne']
    nlinarith
  have hratio_nonneg : ∀ n, 0 ≤ ratio n := by
    intro n
    dsimp [ratio]
    positivity
  have hratio_le : ∀ n, ratio n ≤ 1 := by
    intro n
    dsimp [ratio, numer, denom]
    by_cases hz : GenLimit.PatientScope.prefixCount K n = 0
    · simp [hz]
    · rw [div_le_one (by positivity)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAK n
  unfold GenLimit.PatientScope.relativeLowerDensity
  change (1 / 4 : ℝ) ≤ liminf ratio atTop
  rw [← hlower.liminf_eq]
  exact liminf_le_liminf hcompare hlower.isBoundedUnder_ge
    (isCoboundedUnder_ge_of_le atTop hratio_le)

private theorem denseNoise_quarter_density
    {q : ℕ} {K : Set ℤ} (hKinf : K.Infinite)
    {input : Stream ℤ}
    (hnovel : NovelGeneratesAfterInput input (denseNoiseOutput q input) K) :
    (1 / 4 : ℝ) ≤ balancedRelativeLowerDensity
      (GeneratorFirstOn input (denseNoiseOutput q input) ∩ K) K := by
  obtain ⟨T, hcount⟩ := eventual_rank_count hnovel
  unfold balancedRelativeLowerDensity
  apply quarter_density_of_count_bound
    (hKinf.preimage (fun z _ => balanced_surjective z))
    (preimage_mono inter_subset_right)
    (4 * T + 7) (4 * (T + 2))
  exact hcount

end Case019

namespace Case019
open GenLimit.UnionClosedness
open GenLimit.NoiseLossFeedback


private def finiteOmissionEmbedding (q : ℕ) (S : Set ℕ) : Set ℤ :=
  (omissionMarkerFinset q : Set ℤ) ∪ positiveTail 0 ∪ negativeCode '' S

private theorem negativeCode_not_positiveTail (n : ℕ) :
    negativeCode n ∉ positiveTail 0 := by
  rintro ⟨k, hk⟩
  have hnegative : negativeCode n < 0 := negativeCode_mem n
  have hpositive : 0 < positiveCode (0 + k) := positiveCode_mem (0 + k)
  change positiveCode (0 + k) = negativeCode n at hk
  rw [hk] at hpositive
  omega

private theorem negativeCode_mem_finiteOmissionEmbedding_iff
    (q n : ℕ) (S : Set ℕ) :
    negativeCode n ∈ finiteOmissionEmbedding q S ↔ n ∈ S := by
  constructor
  · intro h
    change
      (negativeCode n ∈ (omissionMarkerFinset q : Set ℤ) ∨
        negativeCode n ∈ positiveTail 0) ∨
        negativeCode n ∈ negativeCode '' S at h
    rcases h with (hmarker | hpositive) | himage
    · exact False.elim (negativeCode_not_marker q n hmarker)
    · exact False.elim (negativeCode_not_positiveTail n hpositive)
    · obtain ⟨m, hm, hmn⟩ := himage
      exact (negativeCode_injective hmn) ▸ hm
  · intro hn
    exact Or.inr ⟨n, hn, rfl⟩

private theorem finiteOmissionEmbedding_injective (q : ℕ) :
    Function.Injective (finiteOmissionEmbedding q) := by
  intro S T hST
  ext n
  rw [← negativeCode_mem_finiteOmissionEmbedding_iff q n S,
    hST, negativeCode_mem_finiteOmissionEmbedding_iff q n T]

private theorem finiteOmissionEmbedding_mem_class (q : ℕ) (S : Set ℕ) :
    finiteOmissionEmbedding q S ∈ finiteOmissionClass q := by
  apply Set.mem_union_left
  constructor
  · intro z hz
    exact Or.inl (Or.inl hz)
  · refine ⟨0, ?_⟩
    intro z hz
    exact Or.inl (Or.inr hz)

private theorem finiteOmissionClass_not_countable (q : ℕ) :
    ¬(finiteOmissionClass q).Countable := by
  intro hcountable
  have himageSubset :
      finiteOmissionEmbedding q '' (Set.univ : Set (Set ℕ)) ⊆
        finiteOmissionClass q := by
    rintro K ⟨S, _hS, rfl⟩
    exact finiteOmissionEmbedding_mem_class q S
  have himageCountable :
      (finiteOmissionEmbedding q '' (Set.univ : Set (Set ℕ))).Countable :=
    hcountable.mono himageSubset
  have hunivCountable : (Set.univ : Set (Set ℕ)).Countable :=
    Set.countable_of_injective_of_countable_image
      (finiteOmissionEmbedding_injective q).injOn himageCountable
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ
    (Set.countable_univ_iff.mp hunivCountable)

private theorem finiteNoiseLevel_failure (q : ℕ) (gen : Generator ℤ) :
    ∃ K ∈ finiteOmissionClass q, ∃ input : Stream ℤ,
      NoisyEnumerationWithLevel input K (q + 1) ∧
        ¬SampleFreshGeneratesAfterInput
          input (outputAfterInput gen input) K := by
  by_contra hfailure
  push_neg at hfailure
  apply finiteNoiseLevel_lower q
  refine ⟨gen, ?_⟩
  intro K hK input henum
  obtain ⟨T, hT⟩ := hfailure K hK input henum
  refine ⟨T, ?_⟩
  intro t ht
  simpa [CorrectAt, outputAfterInput] using hT t ht

theorem uncountable_separation (q : ℕ) : UncountableSeparation q := by
  refine ⟨finiteOmissionClass q, finiteOmissionClass_not_countable q,
    finiteOmissionClass_uus q, ?_, finiteNoiseLevel_failure q⟩
  refine ⟨denseNoiseGenerator q, ?_⟩
  intro K hK input henum
  have hnovel := denseNoise_novel hK henum
  have hout :
      outputAfterInput (denseNoiseGenerator q) input =
        denseNoiseOutput q input := by
    funext t
    exact denseNoiseGenerator_outputAfterInput q input t
  rw [hout]
  exact ⟨hnovel,
    denseNoise_quarter_density (finiteOmissionClass_uus q K hK) hnovel⟩

end Case019
