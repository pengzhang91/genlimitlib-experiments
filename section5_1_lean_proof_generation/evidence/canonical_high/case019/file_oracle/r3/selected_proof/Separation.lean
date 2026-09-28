import Countable
import Mathlib.Data.Nat.Nth

open Set Filter
open scoped Topology

namespace Case019Helpers

open GenLimit
open GenLimit.Generic
open GenLimit.NoiseLossFeedback
open GenLimit.UnionClosedness

noncomputable def missingPositiveIndex {n : ℕ} (xs : Fin n → ℤ) : ℕ :=
  Nat.nth (fun k => positiveCode k ∉ sequenceSample xs) n

noncomputable def missingNegativeIndex {n : ℕ} (xs : Fin n → ℤ) : ℕ :=
  Nat.nth (fun k => negativeCode k ∉ sequenceSample xs) n

 theorem missingPositive_infinite {n : ℕ} (xs : Fin n → ℤ) :
    {k | positiveCode k ∉ sequenceSample xs}.Infinite := by
  intro hfin
  have hrange : Set.range positiveCode ⊆
      positiveCode '' hfin.toFinset ∪ (sequenceSample xs : Set ℤ) := by
    rintro z ⟨k, rfl⟩
    by_cases hk : positiveCode k ∈ sequenceSample xs
    · exact Or.inr hk
    · exact Or.inl ⟨k, by simpa using hk, rfl⟩
  have hu : (positiveCode '' (hfin.toFinset : Set ℕ) ∪
      (sequenceSample xs : Set ℤ)).Finite :=
    (hfin.toFinset.finite_toSet.image _).union (sequenceSample xs).finite_toSet
  exact positiveIntegers_infinite (by
    rw [← range_positiveCode]
    exact hu.subset hrange)

 theorem missingNegative_infinite {n : ℕ} (xs : Fin n → ℤ) :
    {k | negativeCode k ∉ sequenceSample xs}.Infinite := by
  intro hfin
  have hrange : Set.range negativeCode ⊆
      negativeCode '' hfin.toFinset ∪ (sequenceSample xs : Set ℤ) := by
    rintro z ⟨k, rfl⟩
    by_cases hk : negativeCode k ∈ sequenceSample xs
    · exact Or.inr hk
    · exact Or.inl ⟨k, by simpa using hk, rfl⟩
  have hu : (negativeCode '' (hfin.toFinset : Set ℕ) ∪
      (sequenceSample xs : Set ℤ)).Finite :=
    (hfin.toFinset.finite_toSet.image _).union (sequenceSample xs).finite_toSet
  exact negativeIntegers_infinite (by
    rw [← range_negativeCode]
    exact hu.subset hrange)

noncomputable def denseSweepGenerator (q : ℕ) : Generator ℤ :=
  fun n xs =>
    if omissionMarkerFinset q ⊆ sequenceSample xs then
      positiveCode (missingPositiveIndex xs)
    else
      negativeCode (missingNegativeIndex xs)

 theorem denseSweepGenerator_fresh (q : ℕ) {n : ℕ} (xs : Fin n → ℤ) :
    denseSweepGenerator q n xs ∉ sequenceSample xs := by
  unfold denseSweepGenerator
  split
  · exact Nat.nth_mem_of_infinite (missingPositive_infinite xs) n
  · exact Nat.nth_mem_of_infinite (missingNegative_infinite xs) n

 theorem nth_anti_of_subset {p r : ℕ → Prop}
    (hp : {n | p n}.Infinite) (hr : {n | r n}.Infinite)
    (hsub : ∀ n, r n → p n) (k : ℕ) :
    Nat.nth p k ≤ Nat.nth r k := by
  classical
  rw [← Nat.count_le_iff_le_nth hr]
  calc
    Nat.count r (Nat.nth p k) ≤ Nat.count p (Nat.nth p k) :=
      Nat.count_mono_left hsub
    _ = k := Nat.count_nth_of_infinite hp k

 theorem sequenceSample_prefix_subset {stream : Stream ℤ} {s t : ℕ} (hst : s ≤ t) :
    (sequenceSample (fun k : Fin s => stream k) : Set ℤ) ⊆
      sequenceSample (fun k : Fin t => stream k) := by
  intro x hx
  change x ∈ sequenceSample (fun k : Fin s => stream k) at hx
  change x ∈ sequenceSample (fun k : Fin t => stream k)
  rw [mem_sequenceSample_iff] at hx ⊢
  obtain ⟨k, hk⟩ := hx
  exact ⟨⟨k, lt_of_lt_of_le k.isLt hst⟩, hk⟩

 theorem positive_missing_index_strict {stream : Stream ℤ} {s t : ℕ} (hst : s < t) :
    missingPositiveIndex (fun k : Fin s => stream k) <
      missingPositiveIndex (fun k : Fin t => stream k) := by
  let ps : ℕ → Prop := fun k => positiveCode k ∉
    sequenceSample (fun j : Fin s => stream j)
  let pt : ℕ → Prop := fun k => positiveCode k ∉
    sequenceSample (fun j : Fin t => stream j)
  have hps : {k | ps k}.Infinite := missingPositive_infinite _
  have hpt : {k | pt k}.Infinite := missingPositive_infinite _
  have hsub : ∀ k, pt k → ps k := by
    intro k hk hmem
    exact hk (sequenceSample_prefix_subset hst.le hmem)
  calc
    missingPositiveIndex (fun k : Fin s => stream k) = Nat.nth ps s := rfl
    _ < Nat.nth ps t := (Nat.nth_lt_nth hps).2 hst
    _ ≤ Nat.nth pt t := nth_anti_of_subset hps hpt hsub t
    _ = missingPositiveIndex (fun k : Fin t => stream k) := rfl

 theorem negative_missing_index_strict {stream : Stream ℤ} {s t : ℕ} (hst : s < t) :
    missingNegativeIndex (fun k : Fin s => stream k) <
      missingNegativeIndex (fun k : Fin t => stream k) := by
  let ps : ℕ → Prop := fun k => negativeCode k ∉
    sequenceSample (fun j : Fin s => stream j)
  let pt : ℕ → Prop := fun k => negativeCode k ∉
    sequenceSample (fun j : Fin t => stream j)
  have hps : {k | ps k}.Infinite := missingNegative_infinite _
  have hpt : {k | pt k}.Infinite := missingNegative_infinite _
  have hsub : ∀ k, pt k → ps k := by
    intro k hk hmem
    exact hk (sequenceSample_prefix_subset hst.le hmem)
  calc
    missingNegativeIndex (fun k : Fin s => stream k) = Nat.nth ps s := rfl
    _ < Nat.nth ps t := (Nat.nth_lt_nth hps).2 hst
    _ ≤ Nat.nth pt t := nth_anti_of_subset hps hpt hsub t
    _ = missingNegativeIndex (fun k : Fin t => stream k) := rfl

 theorem denseSweepGenerator_outputs_ne (q : ℕ) (stream : Stream ℤ) {s t : ℕ}
    (hst : s < t) :
    Stage3Case019.outputAfterInput (denseSweepGenerator q) stream s ≠
      Stage3Case019.outputAfterInput (denseSweepGenerator q) stream t := by
  unfold Stage3Case019.outputAfterInput Generic.output denseSweepGenerator
  by_cases hs : omissionMarkerFinset q ⊆
      sequenceSample (fun k : Fin (s + 1) => stream k)
  · have ht : omissionMarkerFinset q ⊆
        sequenceSample (fun k : Fin (t + 1) => stream k) :=
      fun x hx => sequenceSample_prefix_subset (by omega) (hs hx)
    simp only [hs, ht, ↓reduceIte]
    intro h
    exact (ne_of_lt (positive_missing_index_strict (stream := stream)
      (Nat.add_lt_add_right hst 1))) (positiveCode_injective h)
  · by_cases ht : omissionMarkerFinset q ⊆
        sequenceSample (fun k : Fin (t + 1) => stream k)
    · simp only [hs, ht, ↓reduceIte]
      intro h
      exact (ne_of_lt (lt_trans
        (negativeCode_mem (missingNegativeIndex (fun k : Fin (s + 1) => stream k)))
        (positiveCode_mem (missingPositiveIndex (fun k : Fin (t + 1) => stream k))))) h
    · simp only [hs, ht, ↓reduceIte]
      intro h
      exact (ne_of_lt (negative_missing_index_strict (stream := stream)
        (Nat.add_lt_add_right hst 1))) (negativeCode_injective h)


 theorem nth_missing_le_two {n : ℕ} (xs : Fin n → ℤ)
    (code : ℕ → ℤ) (hcode : Function.Injective code)
    (hinf : {k | code k ∉ sequenceSample xs}.Infinite) :
    Nat.nth (fun k => code k ∉ sequenceSample xs) n ≤ 2 * n := by
  classical
  letI : DecidableEq ℤ := Classical.decEq ℤ
  let blocked := (Finset.range (2 * n + 1)).filter
    (fun k => code k ∈ sequenceSample xs)
  let fresh := (Finset.range (2 * n + 1)).filter
    (fun k => code k ∉ sequenceSample xs)
  have hblocked : blocked.card ≤ n := by
    have himage : Finset.image code blocked ⊆ sequenceSample xs := by
      intro z hz
      rw [Finset.mem_image] at hz
      obtain ⟨k, hk, rfl⟩ := hz
      exact (Finset.mem_filter.mp hk).2
    calc
      blocked.card = (Finset.image code blocked).card :=
        (Finset.card_image_of_injective blocked hcode).symm
      _ ≤ (sequenceSample xs).card := Finset.card_le_card himage
      _ ≤ n := by
        simpa [sequenceSample] using
          (Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := xs))
  have hfresh : n < fresh.card := by
    have hpartition := Finset.filter_card_add_filter_neg_card_eq_card
      (s := Finset.range (2 * n + 1))
      (fun k => code k ∉ sequenceSample xs)
    have hp : fresh.card + blocked.card = 2 * n + 1 := by
      simpa [fresh, blocked, Finset.card_range] using hpartition
    omega
  by_contra hnot
  have hleNth : 2 * n + 1 ≤ Nat.nth
      (fun k => code k ∉ sequenceSample xs) n := by omega
  have hcount : Nat.count (fun k => code k ∉ sequenceSample xs) (2 * n + 1) ≤ n :=
    (Nat.count_le_iff_le_nth hinf).2 hleNth
  rw [Nat.count_eq_card_filter_range] at hcount
  exact (not_le_of_gt hfresh) hcount

 theorem missingPositiveIndex_le_two {n : ℕ} (xs : Fin n → ℤ) :
    missingPositiveIndex xs ≤ 2 * n :=
  nth_missing_le_two xs positiveCode positiveCode_injective (missingPositive_infinite xs)

 theorem missingNegativeIndex_le_two {n : ℕ} (xs : Fin n → ℤ) :
    missingNegativeIndex xs ≤ 2 * n :=
  nth_missing_le_two xs negativeCode negativeCode_injective (missingNegative_infinite xs)


 theorem balanced_negativeCode (k : ℕ) :
    Stage3Case019.balanced (2 * k + 1) = negativeCode k := by
  simp [Stage3Case019.balanced, negativeCode, Int.negSucc_eq]

 theorem balanced_positiveCode (k : ℕ) :
    Stage3Case019.balanced (2 * k + 2) = positiveCode k := by
  simp [Stage3Case019.balanced, positiveCode]
  congr 1 <;> omega

noncomputable def denseSweepRank (q : ℕ) (stream : Stream ℤ) (t : ℕ) : ℕ :=
  if omissionMarkerFinset q ⊆
      sequenceSample (fun k : Fin (t + 1) => stream k) then
    2 * missingPositiveIndex (fun k : Fin (t + 1) => stream k) + 2
  else
    2 * missingNegativeIndex (fun k : Fin (t + 1) => stream k) + 1

 theorem balanced_denseSweepRank (q : ℕ) (stream : Stream ℤ) (t : ℕ) :
    Stage3Case019.balanced (denseSweepRank q stream t) =
      Stage3Case019.outputAfterInput (denseSweepGenerator q) stream t := by
  unfold denseSweepRank Stage3Case019.outputAfterInput Generic.output denseSweepGenerator
  split
  · exact balanced_positiveCode _
  · exact balanced_negativeCode _

 theorem denseSweepRank_le (q : ℕ) (stream : Stream ℤ) (t : ℕ) :
    denseSweepRank q stream t ≤ 4 * t + 6 := by
  unfold denseSweepRank
  split
  · have h := missingPositiveIndex_le_two
      (fun k : Fin (t + 1) => stream k)
    omega
  · have h := missingNegativeIndex_le_two
      (fun k : Fin (t + 1) => stream k)
    omega

 theorem denseSweepRank_injective (q : ℕ) (stream : Stream ℤ) :
    Function.Injective (denseSweepRank q stream) := by
  intro s t hst
  apply le_antisymm
  · by_contra h
    have hts : t < s := Nat.lt_of_not_ge h
    have hout := denseSweepGenerator_outputs_ne q stream hts
    apply hout
    rw [← balanced_denseSweepRank q stream t,
      ← balanced_denseSweepRank q stream s, hst]
  · by_contra h
    have hst' : s < t := Nat.lt_of_not_ge h
    have hout := denseSweepGenerator_outputs_ne q stream hst'
    apply hout
    rw [← balanced_denseSweepRank q stream s,
      ← balanced_denseSweepRank q stream t, hst]

 theorem denseSweep_firstOn (q : ℕ) (stream : Stream ℤ) (t : ℕ) :
    Stage3Case019.outputAfterInput (denseSweepGenerator q) stream t ∈
      Stage3Case019.GeneratorFirstOn stream
        (Stage3Case019.outputAfterInput (denseSweepGenerator q) stream) := by
  refine ⟨t, rfl, ?_⟩
  intro s hs heq
  have hfresh := denseSweepGenerator_fresh q
    (fun k : Fin (t + 1) => stream k)
  apply hfresh
  rw [mem_sequenceSample_iff]
  exact ⟨⟨s, by omega⟩, heq⟩

 theorem denseSweep_prefixCount_lower
    (q T : ℕ) (stream : Stream ℤ) (K : Set ℤ)
    (hvalid : ∀ t, T ≤ t →
      Stage3Case019.outputAfterInput (denseSweepGenerator q) stream t ∈ K) (n : ℕ) :
    (n - 6) / 4 - T ≤ PatientScope.prefixCount
      (Stage3Case019.balancedRanks
        (Stage3Case019.GeneratorFirstOn stream
          (Stage3Case019.outputAfterInput (denseSweepGenerator q) stream) ∩ K)) n := by
  classical
  let times := Finset.Ico T ((n - 6) / 4)
  let ranks := times.image (denseSweepRank q stream)
  have hranksCard : ranks.card = times.card := by
    exact Finset.card_image_of_injective times (denseSweepRank_injective q stream)
  have hsubset : ranks ⊆ PatientScope.prefixFinset
      (Stage3Case019.balancedRanks
        (Stage3Case019.GeneratorFirstOn stream
          (Stage3Case019.outputAfterInput (denseSweepGenerator q) stream) ∩ K)) n := by
    intro r hr
    rw [Finset.mem_image] at hr
    obtain ⟨t, ht, rfl⟩ := hr
    have htI := Finset.mem_Ico.mp ht
    apply PatientScope.mem_prefixFinset.mpr
    constructor
    · have hrank := denseSweepRank_le q stream t
      have htm : t < (n - 6) / 4 := htI.2
      have hfour : 4 * ((n - 6) / 4) ≤ n - 6 := Nat.mul_div_le (n - 6) 4
      omega
    · change Stage3Case019.balanced (denseSweepRank q stream t) ∈
        Stage3Case019.GeneratorFirstOn stream
          (Stage3Case019.outputAfterInput (denseSweepGenerator q) stream) ∩ K
      rw [balanced_denseSweepRank]
      exact ⟨denseSweep_firstOn q stream t, hvalid t htI.1⟩
  calc
    (n - 6) / 4 - T = times.card := by simp [times]
    _ = ranks.card := hranksCard.symm
    _ ≤ _ := Finset.card_le_card hsubset

 def encodedSecond (q : ℕ) (A : Set ℕ) : Set ℤ :=
  negativeIntegers ∪ {z | ∃ n ∈ A, z = positiveCode (q + n)}

 theorem encodedSecond_mem (q : ℕ) (A : Set ℕ) :
    encodedSecond q A ∈ finiteOmissionClass q := by
  right
  constructor
  · exact subset_union_left
  · rw [Set.disjoint_left]
    intro z hz hzmark
    rcases hz with hzneg | ⟨n, hnA, rfl⟩
    · exact (Int.not_lt_of_ge (omissionMarker_nonnegative hzmark)) hzneg
    · obtain ⟨k, hk, heq⟩ := mem_omissionMarkerFinset_iff.mp hzmark
      have : k = q + n + 1 := by
        simpa [positiveCode] using congrArg Int.toNat heq
      omega

 theorem encodedSecond_injective (q : ℕ) : Function.Injective (encodedSecond q) := by
  intro A B hAB
  ext n
  have hposA : positiveCode (q + n) ∈ encodedSecond q A ↔ n ∈ A := by
    constructor
    · intro h
      rcases h with hneg | ⟨m, hm, heq⟩
      · exact False.elim ((Int.not_lt_of_ge (le_of_lt (positiveCode_mem _))) hneg)
      · exact (Nat.add_left_cancel (positiveCode_injective heq)).symm ▸ hm
    · intro hn
      exact Or.inr ⟨n, hn, rfl⟩
  have hposB : positiveCode (q + n) ∈ encodedSecond q B ↔ n ∈ B := by
    constructor
    · intro h
      rcases h with hneg | ⟨m, hm, heq⟩
      · exact False.elim ((Int.not_lt_of_ge (le_of_lt (positiveCode_mem _))) hneg)
      · exact (Nat.add_left_cancel (positiveCode_injective heq)).symm ▸ hm
    · intro hn
      exact Or.inr ⟨n, hn, rfl⟩
  rw [← hposA, ← hposB, hAB]

 theorem finiteOmissionClass_not_countable (q : ℕ) :
    ¬(finiteOmissionClass q).Countable := by
  intro hcount
  have hrange : (Set.range (encodedSecond q)).Countable := by
    apply hcount.mono
    rintro L ⟨A, rfl⟩
    exact encodedSecond_mem q A
  haveI : Countable (Set.range (encodedSecond q)) := hrange.to_subtype
  have hinj : Function.Injective
      (fun A : Set ℕ => (⟨encodedSecond q A, ⟨A, rfl⟩⟩ :
        Set.range (encodedSecond q))) := by
    intro A B h
    exact encodedSecond_injective q (congrArg Subtype.val h)
  have hsets : Countable (Set ℕ) := hinj.countable
  exact powerSet_not_countable ℕ hsets


 theorem balanced_surjective : Function.Surjective Stage3Case019.balanced := by
  intro z
  cases z with
  | ofNat n =>
      cases n with
      | zero => exact ⟨0, rfl⟩
      | succ k =>
          refine ⟨2 * k + 2, ?_⟩
          simpa [positiveCode] using balanced_positiveCode k
  | negSucc k => exact ⟨2 * k + 1, balanced_negativeCode k⟩

 theorem balancedRanks_infinite {K : Set ℤ} (hK : K.Infinite) :
    (Stage3Case019.balancedRanks K).Infinite := by
  apply hK.preimage
  intro z hz
  exact balanced_surjective z

 theorem prefixCount_le_index (A : Set ℕ) (n : ℕ) :
    PatientScope.prefixCount A n ≤ n := by
  classical
  unfold PatientScope.prefixCount PatientScope.prefixFinset
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range n)

 theorem denseSweep_quarter_density
    (q T : ℕ) (stream : Stream ℤ) (K : Set ℤ) (hK : K.Infinite)
    (hvalid : ∀ t, T ≤ t →
      Stage3Case019.outputAfterInput (denseSweepGenerator q) stream t ∈ K) :
    (1 / 4 : ℝ) ≤ Stage3Case019.balancedRelativeLowerDensity
      (Stage3Case019.GeneratorFirstOn stream
        (Stage3Case019.outputAfterInput (denseSweepGenerator q) stream) ∩ K) K := by
  let D := Stage3Case019.balancedRanks
    (Stage3Case019.GeneratorFirstOn stream
      (Stage3Case019.outputAfterInput (denseSweepGenerator q) stream) ∩ K)
  let E := Stage3Case019.balancedRanks K
  let c : ℝ := 4 * T + 9
  let g : ℕ → ℝ := fun n => (1 / 4 : ℝ) - c / (4 * (n : ℝ))
  let ratio : ℕ → ℝ := fun n =>
    (PatientScope.prefixCount D n : ℝ) / (PatientScope.prefixCount E n : ℝ)
  have hEinf : E.Infinite := balancedRanks_infinite hK
  have hEtend : Tendsto (fun n => (PatientScope.prefixCount E n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (PatientScope.tendsto_prefixCount_atTop hEinf)
  have hg : Tendsto g atTop (𝓝 (1 / 4 : ℝ)) := by
    have hzero : Tendsto (fun n : ℕ => c / (4 * (n : ℝ))) atTop (𝓝 0) := by
      have hden : Tendsto (fun n : ℕ => (4 : ℝ) * (n : ℝ)) atTop atTop := by
        exact tendsto_natCast_atTop_atTop.const_mul_atTop
          (by norm_num : (0 : ℝ) < 4)
      exact tendsto_const_nhds.div_atTop hden
    simpa [g] using
      (tendsto_const_nhds.sub hzero : Tendsto
        (fun n : ℕ => (1 / 4 : ℝ) - c / (4 * (n : ℝ)))
        atTop (𝓝 ((1 / 4 : ℝ) - 0)))
  have hcompare : ∀ᶠ n : ℕ in atTop, g n ≤ ratio n := by
    filter_upwards [eventually_ge_atTop (4 * T + 10),
      hEtend.eventually (eventually_gt_atTop 0)] with n hn hEpos
    have hnpos : 0 < n := by omega
    have hfloor : T ≤ (n - 6) / 4 := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      omega
    have hDnat := denseSweep_prefixCount_lower q T stream K hvalid n
    change (n - 6) / 4 - T ≤ PatientScope.prefixCount D n at hDnat
    have hnBound : n ≤ 4 * PatientScope.prefixCount D n + (4 * T + 9) := by
      have hdiv : n - 6 < 4 * ((n - 6) / 4 + 1) := by
        exact Nat.lt_mul_div_succ (n - 6) (by omega)
      have hsub : (n - 6) / 4 = ((n - 6) / 4 - T) + T := by omega
      omega
    have hEn : PatientScope.prefixCount E n ≤ n := prefixCount_le_index E n
    have hER : (0 : ℝ) < PatientScope.prefixCount E n := by exact_mod_cast hEpos
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hDnonneg : (0 : ℝ) ≤ PatientScope.prefixCount D n := Nat.cast_nonneg _
    have hratioDn :
        (PatientScope.prefixCount D n : ℝ) / (n : ℝ) ≤ ratio n := by
      dsimp [ratio]
      exact div_le_div_of_nonneg_left hDnonneg hER (by exact_mod_cast hEn)
    have hnBoundR : (n : ℝ) ≤
        4 * (PatientScope.prefixCount D n : ℝ) + c := by
      dsimp [c]
      exact_mod_cast hnBound
    apply le_trans _ hratioDn
    dsimp [g]
    rw [le_div_iff₀ hnR]
    field_simp [hnR.ne']
    nlinarith
  have hratioUpper : ∀ n, ratio n ≤ 1 := by
    intro n
    dsimp [ratio]
    have hsub : D ⊆ E := by
      intro r hr
      exact hr.2
    by_cases hzero : PatientScope.prefixCount E n = 0
    · simp [hzero]
    · rw [div_le_one]
      · exact_mod_cast PatientScope.prefixCount_mono hsub n
      · exact_mod_cast Nat.pos_of_ne_zero hzero
  rw [Stage3Case019.balancedRelativeLowerDensity,
    PatientScope.relativeLowerDensity]
  change (1 / 4 : ℝ) ≤ liminf ratio atTop
  calc
    (1 / 4 : ℝ) = liminf g atTop := hg.liminf_eq.symm
    _ ≤ liminf ratio atTop := liminf_le_liminf hcompare hg.isBoundedUnder_ge
      (isCoboundedUnder_ge_of_le atTop hratioUpper)

 theorem denseSweep_positive
    (q : ℕ) {K : Set ℤ} (hKclass : K ∈ finiteOmissionClass q)
    (input : Stream ℤ)
    (hinput : InjectiveValueContaminatedPresentationAtMost input K q) :
    Stage3Case019.NovelGeneratesAfterInput input
      (Stage3Case019.outputAfterInput (denseSweepGenerator q) input) K ∧
    (1 / 4 : ℝ) ≤ Stage3Case019.balancedRelativeLowerDensity
      (Stage3Case019.GeneratorFirstOn input
        (Stage3Case019.outputAfterInput (denseSweepGenerator q) input) ∩ K) K := by
  have hKinf : K.Infinite := finiteOmissionClass_uus q K hKclass
  obtain ⟨T, hcorrect⟩ : ∃ T, ∀ t, T ≤ t →
      Stage3Case019.outputAfterInput (denseSweepGenerator q) input t ∈ K ∧
      Stage3Case019.outputAfterInput (denseSweepGenerator q) input t ∉ sample input (t + 1) := by
    rcases hKclass with hfirst | hsecond
    · obtain ⟨hmarkers, j, htail⟩ := hfirst
      obtain ⟨Td, hTd⟩ := allMarkers_eventually_observed hinput hmarkers
      refine ⟨max Td j, ?_⟩
      intro t ht
      have hdetect : omissionMarkerFinset q ⊆ observedThrough input t :=
        hTd t (le_trans (Nat.le_max_left _ _) ht)
      have hsample : sequenceSample (fun k : Fin (t + 1) => input k) =
          observedThrough input t := sequenceSample_prefix input (t + 1)
      have hidx : t + 1 ≤ missingPositiveIndex
          (fun k : Fin (t + 1) => input k) :=
        (Nat.nth_strictMono
          (missingPositive_infinite (fun k : Fin (t + 1) => input k))).id_le _
      have hjidx : j ≤ missingPositiveIndex
          (fun k : Fin (t + 1) => input k) := by
        have hjt : j ≤ t := le_trans (Nat.le_max_right _ _) ht
        omega
      have htailmem : positiveCode (missingPositiveIndex
          (fun k : Fin (t + 1) => input k)) ∈ positiveTail j := by
        refine ⟨missingPositiveIndex (fun k : Fin (t + 1) => input k) - j, ?_⟩
        change positiveCode (j + (missingPositiveIndex
          (fun k : Fin (t + 1) => input k) - j)) = _
        rw [Nat.add_sub_of_le hjidx]
      constructor
      · unfold Stage3Case019.outputAfterInput Generic.output denseSweepGenerator
        simp [hsample, hdetect, htail htailmem]
      · rw [← sequenceSample_prefix input (t + 1)]
        exact denseSweepGenerator_fresh q _
    · refine ⟨0, ?_⟩
      intro t _
      have hno : ¬omissionMarkerFinset q ⊆ observedThrough input t :=
        not_allMarkers_observed_second hsecond hinput t
      have hsample : sequenceSample (fun k : Fin (t + 1) => input k) =
          observedThrough input t := sequenceSample_prefix input (t + 1)
      constructor
      · unfold Stage3Case019.outputAfterInput Generic.output denseSweepGenerator
        simp [hsample, hno, hsecond.1 (negativeCode_mem _)]
      · rw [← sequenceSample_prefix input (t + 1)]
        exact denseSweepGenerator_fresh q _
  constructor
  · refine ⟨T, ?_⟩
    intro t ht
    refine ⟨(hcorrect t ht).1, (hcorrect t ht).2, ?_⟩
    intro s hst
    exact denseSweepGenerator_outputs_ne q input hst
  · exact denseSweep_quarter_density q T input K hKinf (fun t ht => (hcorrect t ht).1)


 theorem separation_negative (q : ℕ) (gen : Generator ℤ) :
    ∃ K ∈ finiteOmissionClass q, ∃ input : Stream ℤ,
      InjectiveValueContaminatedPresentationAtMost input K (q + 1) ∧
      ¬Stage3Case019.SampleFreshGeneratesAfterInput input
        (Stage3Case019.outputAfterInput gen input) K := by
  by_contra hnone
  push_neg at hnone
  apply finiteNoiseLevel_lower q
  refine ⟨gen, ?_⟩
  intro K hK input hinput
  have hall := hnone K hK input hinput
  simpa [Stage3Case019.SampleFreshGeneratesAfterInput,
    Stage3Case019.outputAfterInput, GenLimit.NoiseLossFeedback.CorrectAt, outputAt] using hall

 theorem uncountable_separation : Stage3Case019.SeparationClause := by
  intro q
  refine ⟨finiteOmissionClass q, finiteOmissionClass_not_countable q,
    finiteOmissionClass_uus q, ?_, ?_⟩
  · exact ⟨denseSweepGenerator q, fun K hK input hinput =>
      denseSweep_positive q hK input hinput⟩
  · exact separation_negative q

end Case019Helpers
