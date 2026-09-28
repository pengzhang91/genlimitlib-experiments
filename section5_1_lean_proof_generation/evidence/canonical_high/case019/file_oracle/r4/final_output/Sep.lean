import output.Helpers
import Mathlib

open Set

namespace Stage3Case019Proof

open GenLimit
open GenLimit.Generic
open GenLimit.NoiseLossFeedback
open GenLimit.UnionClosedness

private theorem exists_positive_not_mem (used : Finset ℤ) :
    ∃ n : ℕ, positiveCode n ∉ used := by
  obtain ⟨z, hz, hzu⟩ :=
    (positiveIntegers_infinite.diff used.finite_toSet).nonempty
  rw [← range_positiveCode] at hz
  obtain ⟨n, rfl⟩ := hz
  exact ⟨n, hzu⟩

private theorem exists_negative_not_mem (used : Finset ℤ) :
    ∃ n : ℕ, negativeCode n ∉ used := by
  obtain ⟨z, hz, hzu⟩ :=
    (negativeIntegers_infinite.diff used.finite_toSet).nonempty
  rw [← range_negativeCode] at hz
  obtain ⟨n, rfl⟩ := hz
  exact ⟨n, hzu⟩

noncomputable def denseSweepOutput (q : ℕ) (input : Stage3Case019.Stream ℤ) : ℕ → ℤ
  | t =>
      let used := GenLimit.Generic.sample input (t + 1) ∪
        Finset.univ.image (fun s : Fin t => denseSweepOutput q input s)
      if omissionMarkerFinset q ⊆ GenLimit.Generic.sample input (t + 1) then
        positiveCode (Nat.find (exists_positive_not_mem used))
      else
        negativeCode (Nat.find (exists_negative_not_mem used))
termination_by t => t

example (q : ℕ) (input : Stage3Case019.Stream ℤ) (t : ℕ) :
    denseSweepOutput q input t ∉ GenLimit.Generic.sample input (t+1) := by
  rw [denseSweepOutput]
  split
  · have hs := Nat.find_spec (exists_positive_not_mem
      (GenLimit.Generic.sample input (t + 1) ∪
        Finset.univ.image (fun s : Fin t => denseSweepOutput q input s)))
    exact fun h => hs (Finset.mem_union_left _ h)
  · have hs := Nat.find_spec (exists_negative_not_mem
      (GenLimit.Generic.sample input (t + 1) ∪
        Finset.univ.image (fun s : Fin t => denseSweepOutput q input s)))
    exact fun h => hs (Finset.mem_union_left _ h)


private theorem find_positive_le_card (used : Finset ℤ) :
    Nat.find (exists_positive_not_mem used) ≤ used.card := by
  let candidates := (Finset.range (used.card + 1)).image positiveCode
  have hcandidates : candidates.card = used.card + 1 := by
    simpa [candidates] using
      Finset.card_image_of_injective (Finset.range (used.card + 1))
        positiveCode_injective
  have hlt : used.card < candidates.card := by omega
  obtain ⟨z, hzCandidates, hzUsed⟩ :=
    Finset.exists_mem_not_mem_of_card_lt_card hlt
  obtain ⟨n, hnRange, rfl⟩ := Finset.mem_image.mp hzCandidates
  have hn : n < used.card + 1 := Finset.mem_range.mp hnRange
  exact (Nat.find_min' (exists_positive_not_mem used) hzUsed).trans
    (by omega)

private theorem find_negative_le_card (used : Finset ℤ) :
    Nat.find (exists_negative_not_mem used) ≤ used.card := by
  let candidates := (Finset.range (used.card + 1)).image negativeCode
  have hcandidates : candidates.card = used.card + 1 := by
    simpa [candidates] using
      Finset.card_image_of_injective (Finset.range (used.card + 1))
        negativeCode_injective
  have hlt : used.card < candidates.card := by omega
  obtain ⟨z, hzCandidates, hzUsed⟩ :=
    Finset.exists_mem_not_mem_of_card_lt_card hlt
  obtain ⟨n, hnRange, rfl⟩ := Finset.mem_image.mp hzCandidates
  have hn : n < used.card + 1 := Finset.mem_range.mp hnRange
  exact (Nat.find_min' (exists_negative_not_mem used) hzUsed).trans
    (by omega)

private theorem denseSweepOutput_not_sample
    (q : ℕ) (input : Stage3Case019.Stream ℤ) (t : ℕ) :
    denseSweepOutput q input t ∉ GenLimit.Generic.sample input (t + 1) := by
  rw [denseSweepOutput]
  split
  · have hs := Nat.find_spec (exists_positive_not_mem
      (GenLimit.Generic.sample input (t + 1) ∪
        Finset.univ.image (fun s : Fin t => denseSweepOutput q input s)))
    exact fun h => hs (Finset.mem_union_left _ h)
  · have hs := Nat.find_spec (exists_negative_not_mem
      (GenLimit.Generic.sample input (t + 1) ∪
        Finset.univ.image (fun s : Fin t => denseSweepOutput q input s)))
    exact fun h => hs (Finset.mem_union_left _ h)

private theorem denseSweepOutput_ne_previous
    (q : ℕ) (input : Stage3Case019.Stream ℤ) {s t : ℕ} (hst : s < t) :
    denseSweepOutput q input s ≠ denseSweepOutput q input t := by
  have hnot : denseSweepOutput q input t ∉
      Finset.univ.image (fun u : Fin t => denseSweepOutput q input u) := by
    rw [denseSweepOutput]
    split
    · have hs := Nat.find_spec (exists_positive_not_mem
        (GenLimit.Generic.sample input (t + 1) ∪
          Finset.univ.image (fun u : Fin t => denseSweepOutput q input u)))
      exact fun h => hs (Finset.mem_union_right _ h)
    · have hs := Nat.find_spec (exists_negative_not_mem
        (GenLimit.Generic.sample input (t + 1) ∪
          Finset.univ.image (fun u : Fin t => denseSweepOutput q input u)))
      exact fun h => hs (Finset.mem_union_right _ h)
  intro heq
  apply hnot
  apply Finset.mem_image.mpr
  exact ⟨⟨s, hst⟩, Finset.mem_univ _, heq⟩

private theorem denseSweepOutput_injective
    (q : ℕ) (input : Stage3Case019.Stream ℤ) :
    Function.Injective (denseSweepOutput q input) := by
  intro s t h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hst | hts
  · exact denseSweepOutput_ne_previous q input hst h
  · exact denseSweepOutput_ne_previous q input hts h.symm

noncomputable def denseSweepRank
    (q : ℕ) (input : Stage3Case019.Stream ℤ) (t : ℕ) : ℕ :=
  let used := GenLimit.Generic.sample input (t + 1) ∪
    Finset.univ.image (fun s : Fin t => denseSweepOutput q input s)
  if omissionMarkerFinset q ⊆ GenLimit.Generic.sample input (t + 1) then
    2 * Nat.find (exists_positive_not_mem used) + 2
  else
    2 * Nat.find (exists_negative_not_mem used) + 1

private theorem balanced_odd_negative (n : ℕ) :
    Stage3Case019.balanced (2 * n + 1) = negativeCode n := by
  rw [show 2 * n + 1 = (2 * n) + 1 by omega]
  simp only [Stage3Case019.balanced]
  have hmod : (2 * n) % 2 = 0 := by omega
  rw [hmod]
  simp only [↓reduceIte]
  have hdiv : (2 * n) / 2 = n := by omega
  rw [hdiv]
  simp [negativeCode, Int.negSucc_eq]

private theorem balanced_even_positive (n : ℕ) :
    Stage3Case019.balanced (2 * n + 2) = positiveCode n := by
  rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega]
  simp only [Stage3Case019.balanced, Nat.add_sub_cancel]
  have hmod : (2 * n + 1) % 2 = 1 := by omega
  rw [hmod]
  simp only [OfNat.ofNat, ↓reduceIte]
  have hdiv : (2 * n + 1) / 2 = n := by omega
  rw [hdiv]
  simp [positiveCode]

private theorem balanced_denseSweepRank
    (q : ℕ) (input : Stage3Case019.Stream ℤ) (t : ℕ) :
    Stage3Case019.balanced (denseSweepRank q input t) =
      denseSweepOutput q input t := by
  rw [denseSweepOutput]
  simp only [denseSweepRank]
  split <;> simp [balanced_even_positive, balanced_odd_negative]

private theorem denseSweepRank_le
    (q : ℕ) (input : Stage3Case019.Stream ℤ) (t : ℕ) :
    denseSweepRank q input t ≤ 4 * t + 4 := by
  let used := GenLimit.Generic.sample input (t + 1) ∪
    Finset.univ.image (fun s : Fin t => denseSweepOutput q input s)
  have hsample : (GenLimit.Generic.sample input (t + 1)).card ≤ t + 1 :=
    GenLimit.Generic.sample_card_le input (t + 1)
  have himage :
      (Finset.univ.image (fun s : Fin t => denseSweepOutput q input s)).card ≤ t := by
    calc
      _ ≤ Finset.univ.card := Finset.card_image_le
      _ = t := Finset.card_fin t
  have hused : used.card ≤ 2 * t + 1 := by
    calc
      used.card ≤ (GenLimit.Generic.sample input (t + 1)).card +
          (Finset.univ.image (fun s : Fin t => denseSweepOutput q input s)).card :=
        Finset.card_union_le _ _
      _ ≤ (t + 1) + t := Nat.add_le_add hsample himage
      _ = 2 * t + 1 := by omega
  simp only [denseSweepRank]
  split
  · have hfind := find_positive_le_card used
    omega
  · have hfind := find_negative_le_card used
    omega


private theorem genericSample_eq_of_eq_on_le
    {a b : Stage3Case019.Stream ℤ} {t : ℕ}
    (h : ∀ k, k ≤ t → a k = b k) :
    GenLimit.Generic.sample a (t + 1) =
      GenLimit.Generic.sample b (t + 1) := by
  classical
  ext x
  simp only [GenLimit.Generic.mem_sample_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, (h k (by omega)).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, h k (by omega)⟩

private theorem denseSweepOutput_eq_of_eq_on_le
    (q : ℕ) {a b : Stage3Case019.Stream ℤ} :
    ∀ t, (∀ k, k ≤ t → a k = b k) →
      denseSweepOutput q a t = denseSweepOutput q b t := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
      intro hab
      have hsamp := genericSample_eq_of_eq_on_le hab
      have himage :
          Finset.univ.image (fun s : Fin t => denseSweepOutput q a s) =
            Finset.univ.image (fun s : Fin t => denseSweepOutput q b s) := by
        apply Finset.image_congr
        intro s hs
        exact ih s (by exact s.isLt) (fun k hk => hab k (by omega))
      rw [denseSweepOutput, denseSweepOutput, hsamp, himage]

private def denseSweepExtension {n : ℕ} (history : Fin n → ℤ) :
    Stage3Case019.Stream ℤ :=
  fun k => if hk : k < n then history ⟨k, hk⟩ else 0

noncomputable def denseSweepGenerator (q : ℕ) : Stage3Case019.Generator ℤ
  | 0, _ => 0
  | t + 1, history =>
      denseSweepOutput q (denseSweepExtension history) t

private theorem denseSweepGenerator_outputAfterInput
    (q : ℕ) (input : Stage3Case019.Stream ℤ) (t : ℕ) :
    Stage3Case019.outputAfterInput (denseSweepGenerator q) input t =
      denseSweepOutput q input t := by
  apply denseSweepOutput_eq_of_eq_on_le q
  intro k hk
  simp [Stage3Case019.outputAfterInput, denseSweepGenerator,
    denseSweepExtension, show k < t + 1 by omega]


private theorem injective_eventually_avoids_finite
    {α : Type*} {f : ℕ → α} (hf : Function.Injective f)
    {S : Set α} (hS : S.Finite) :
    ∃ T, ∀ t, T ≤ t → f t ∉ S := by
  classical
  have hpre : (f ⁻¹' S).Finite := hS.preimage hf.injOn
  obtain ⟨T, hT⟩ := Finset.exists_nat_subset_range hpre.toFinset
  refine ⟨T, ?_⟩
  intro t ht hmem
  have htFin : t ∈ hpre.toFinset := by simpa using hmem
  have htRange := hT htFin
  have : t < T := Finset.mem_range.mp htRange
  omega

private theorem positive_diff_finite_of_tail_subset
    {K : Set ℤ} {j : ℕ} (htail : positiveTail j ⊆ K) :
    (positiveIntegers \ K).Finite := by
  let F := (Finset.range j).image positiveCode
  apply F.finite_toSet.subset
  intro z hz
  obtain ⟨n, rfl⟩ := (show z ∈ Set.range positiveCode by
    rw [range_positiveCode]
    exact hz.1)
  have hn : n < j := by
    by_contra h
    have htailMem : positiveCode n ∈ positiveTail j := by
      refine ⟨n - j, ?_⟩
      have hidx : j + (n - j) = n := Nat.add_sub_of_le (Nat.le_of_not_gt h)
      exact congrArg positiveCode hidx
    exact hz.2 (htail htailMem)
  exact Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr hn, rfl⟩

private theorem denseSweep_eventual_validity
    (q : ℕ) {K : Set ℤ} (hK : K ∈ finiteOmissionClass q)
    (input : Stage3Case019.Stream ℤ)
    (hinput : InjectiveValueContaminatedPresentationAtMost input K q) :
    ∃ T, ∀ t, T ≤ t → denseSweepOutput q input t ∈ K := by
  rcases hK with hfirst | hsecond
  · obtain ⟨hmarkers, j, htail⟩ := hfirst
    obtain ⟨Tmarkers, hTmarkers⟩ :=
      allMarkers_eventually_observed hinput hmarkers
    let bad := positiveIntegers \ K
    have hbad : bad.Finite := positive_diff_finite_of_tail_subset htail
    obtain ⟨Tbad, hTbad⟩ := injective_eventually_avoids_finite
      (denseSweepOutput_injective q input) hbad
    refine ⟨max Tmarkers Tbad, ?_⟩
    intro t ht
    have hmarkersNow : omissionMarkerFinset q ⊆
        GenLimit.Generic.sample input (t + 1) := by
      exact hTmarkers t ((Nat.le_max_left _ _).trans ht)
    have hpositive : denseSweepOutput q input t ∈ positiveIntegers := by
      rw [denseSweepOutput]
      simp [hmarkersNow, positiveCode_mem]
    have hnotBad : denseSweepOutput q input t ∉ bad :=
      hTbad t ((Nat.le_max_right _ _).trans ht)
    exact not_not.mp (fun hnotK => hnotBad ⟨hpositive, hnotK⟩)
  · refine ⟨0, ?_⟩
    intro t _
    have hnoMarkers : ¬omissionMarkerFinset q ⊆
        GenLimit.Generic.sample input (t + 1) := by
      simpa [observedThrough] using
        not_allMarkers_observed_second hsecond hinput t
    have hnegative : denseSweepOutput q input t ∈ negativeIntegers := by
      rw [denseSweepOutput]
      simp [hnoMarkers, negativeCode_mem]
    exact hsecond.1 hnegative

private def integerRank : ℤ → ℕ
  | .ofNat 0 => 0
  | .ofNat (n + 1) => 2 * n + 2
  | .negSucc n => 2 * n + 1

private theorem balanced_integerRank (z : ℤ) :
    Stage3Case019.balanced (integerRank z) = z := by
  cases z with
  | ofNat n =>
      cases n with
      | zero => rfl
      | succ n => exact balanced_even_positive n
  | negSucc n => exact balanced_odd_negative n

private theorem integerRank_injective : Function.Injective integerRank := by
  intro z w h
  have := congrArg Stage3Case019.balanced h
  simpa [balanced_integerRank] using this

private theorem balancedRanks_infinite {K : Set ℤ} (hK : K.Infinite) :
    (Stage3Case019.balancedRanks K).Infinite := by
  have himage : (integerRank '' K).Infinite := hK.image integerRank_injective.injOn
  apply himage.mono
  rintro n ⟨z, hzK, rfl⟩
  change Stage3Case019.balanced (integerRank z) ∈ K
  rwa [balanced_integerRank]

private theorem lowerDensity_quarter_of_counting
    (N D : ℕ → ℕ) (r : ℕ)
    (hN : Filter.Tendsto N Filter.atTop Filter.atTop)
    (hcount : ∀ n, N n ≤ 4 * D n + r)
    (hDle : ∀ n, D n ≤ N n) :
    (1 / 4 : ℝ) ≤
      Filter.liminf (fun n : ℕ => (D n : ℝ) / (N n : ℝ)) Filter.atTop := by
  open Filter in
    let g : ℕ → ℝ := fun n => (1 / 4 : ℝ) - (r : ℝ) / (4 * (N n : ℝ))
    have herr : Tendsto (fun n : ℕ => (r : ℝ) / (4 * (N n : ℝ))) atTop
        (nhds 0) := by
      have hNR : Tendsto (fun n : ℕ => (N n : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp hN
      exact tendsto_const_nhds.div_atTop (hNR.const_mul_atTop (by norm_num : (0 : ℝ) < 4))
    have hg : Tendsto g atTop (nhds (1 / 4 : ℝ)) := by
      simpa only [g, sub_zero] using tendsto_const_nhds.sub herr
    have hNpos : ∀ᶠ n : ℕ in atTop, 0 < N n :=
      hN.eventually (eventually_gt_atTop 0)
    have hcompare : ∀ᶠ n : ℕ in atTop,
        g n ≤ (D n : ℝ) / (N n : ℝ) := by
      filter_upwards [hNpos] with n hn
      have hnR : (0 : ℝ) < N n := by exact_mod_cast hn
      have hcR : (N n : ℝ) ≤ 4 * (D n : ℝ) + r := by
        exact_mod_cast hcount n
      dsimp [g]
      rw [le_div_iff₀ hnR]
      field_simp [hnR.ne']
      nlinarith
    have hratio : ∀ n, (D n : ℝ) / (N n : ℝ) ≤ 1 := by
      intro n
      by_cases hn : N n = 0
      · simp [hn]
      · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
        exact_mod_cast hDle n
    calc
      (1 / 4 : ℝ) = liminf g atTop := hg.liminf_eq.symm
      _ ≤ liminf (fun n : ℕ => (D n : ℝ) / (N n : ℝ)) atTop :=
        liminf_le_liminf hcompare hg.isBoundedUnder_ge
          (isCoboundedUnder_ge_of_le atTop hratio)

private theorem denseSweep_density
    (q : ℕ) {K : Set ℤ} (hKinfinite : K.Infinite)
    (input : Stage3Case019.Stream ℤ) (T : ℕ)
    (hvalid : ∀ t, T ≤ t → denseSweepOutput q input t ∈ K) :
    (1 / 4 : ℝ) ≤
      Stage3Case019.balancedRelativeLowerDensity
        (Stage3Case019.GeneratorFirstOn input (denseSweepOutput q input) ∩ K) K := by
  classical
  let D : Set ℕ := Stage3Case019.balancedRanks
    (Stage3Case019.GeneratorFirstOn input (denseSweepOutput q input) ∩ K)
  let N : ℕ → ℕ := GenLimit.PatientScope.prefixCount
    (Stage3Case019.balancedRanks K)
  let DC : ℕ → ℕ := GenLimit.PatientScope.prefixCount D
  have hsubset : D ⊆ Stage3Case019.balancedRanks K := by
    intro n hn
    change Stage3Case019.balanced n ∈ K
    exact hn.2
  have hDle : ∀ n, DC n ≤ N n := by
    intro n
    exact GenLimit.PatientScope.prefixCount_mono hsubset n
  have hN : Filter.Tendsto N Filter.atTop Filter.atTop :=
    GenLimit.PatientScope.tendsto_prefixCount_atTop
      (balancedRanks_infinite hKinfinite)
  have hcount : ∀ n, N n ≤ 4 * DC n + (4 * T + 7) := by
    intro n
    let rounds := Finset.Ico T (n / 4 - 1)
    have hrankIn : ∀ t ∈ rounds,
        denseSweepRank q input t ∈ GenLimit.PatientScope.prefixFinset D n := by
      intro t ht
      have htIco := Finset.mem_Ico.mp ht
      apply GenLimit.PatientScope.mem_prefixFinset.mpr
      constructor
      · have hrank := denseSweepRank_le q input t
        omega
      · change Stage3Case019.balanced (denseSweepRank q input t) ∈
          Stage3Case019.GeneratorFirstOn input (denseSweepOutput q input) ∩ K
        rw [balanced_denseSweepRank]
        refine ⟨⟨t, rfl, ?_⟩, hvalid t htIco.1⟩
        intro s hs heq
        apply denseSweepOutput_not_sample q input t
        apply GenLimit.Generic.mem_sample_iff.mpr
        exact ⟨s, by omega, heq⟩
    have hrankInj : Set.InjOn (denseSweepRank q input) rounds := by
      intro s hs t ht hst
      apply denseSweepOutput_injective q input
      rw [← balanced_denseSweepRank q input s,
        ← balanced_denseSweepRank q input t, hst]
    have hcard : rounds.card ≤ DC n := by
      unfold DC GenLimit.PatientScope.prefixCount
      exact Finset.card_le_card_of_injOn (denseSweepRank q input) hrankIn hrankInj
    have hrounds : rounds.card = (n / 4 - 1) - T := by
      simp [rounds]
    have hNle : N n ≤ n := by
      unfold N GenLimit.PatientScope.prefixCount
      calc
        (GenLimit.PatientScope.prefixFinset
            (Stage3Case019.balancedRanks K) n).card
            ≤ (Finset.range n).card := by
              unfold GenLimit.PatientScope.prefixFinset
              exact Finset.card_filter_le _ _
        _ = n := Finset.card_range n
    rw [hrounds] at hcard
    omega
  have hquarter := lowerDensity_quarter_of_counting N DC (4 * T + 7) hN hcount hDle
  simpa [Stage3Case019.balancedRelativeLowerDensity,
    GenLimit.PatientScope.relativeLowerDensity, N, DC, D] using hquarter

theorem stage3_uncountable_separation : Stage3Case019.SeparationClause := by
  intro q
  refine ⟨finiteOmissionClass q, finiteOmissionClass_not_countable q,
    finiteOmissionClass_uus q, ?_, finiteOmissionClass_negative q⟩
  refine ⟨denseSweepGenerator q, ?_⟩
  intro K hK input hinput
  obtain ⟨T, hvalid⟩ := denseSweep_eventual_validity q hK input hinput
  have houtEq :
      Stage3Case019.outputAfterInput (denseSweepGenerator q) input =
        denseSweepOutput q input := by
    funext t
    exact denseSweepGenerator_outputAfterInput q input t
  constructor
  · refine ⟨T, ?_⟩
    intro t ht
    rw [houtEq]
    exact ⟨hvalid t ht, denseSweepOutput_not_sample q input t,
      fun s hs => denseSweepOutput_ne_previous q input hs⟩
  · rw [houtEq]
    exact denseSweep_density q (finiteOmissionClass_uus q K hK) input T hvalid

end Stage3Case019Proof
