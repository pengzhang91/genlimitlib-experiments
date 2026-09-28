import CountableClause

open Set Filter
open scoped Topology

namespace Stage3Case019

noncomputable section

private def restrictHistory {α : Type*} {n : ℕ}
    (xs : Fin n → α) (k : Fin n) : Fin k → α :=
  fun j => xs ⟨j, lt_trans j.isLt k.isLt⟩

private theorem exists_code_not_mem
    (code : ℕ → ℤ) (hinf : (Set.range code).Infinite)
    (F : Finset ℤ) : ∃ k, code k ∉ F := by
  obtain ⟨z, hzrange, hzF⟩ :=
    (hinf.diff F.finite_toSet).nonempty
  obtain ⟨k, rfl⟩ := hzrange
  exact ⟨k, hzF⟩

private noncomputable def firstCodeOutside
    (code : ℕ → ℤ) (hinf : (Set.range code).Infinite)
    (F : Finset ℤ) : ℕ :=
  Nat.find (exists_code_not_mem code hinf F)

private theorem firstCodeOutside_spec
    (code : ℕ → ℤ) (hinf : (Set.range code).Infinite)
    (F : Finset ℤ) :
    code (firstCodeOutside code hinf F) ∉ F :=
  Nat.find_spec (exists_code_not_mem code hinf F)

private theorem firstCodeOutside_le_card
    (code : ℕ → ℤ) (hinj : Function.Injective code)
    (hinf : (Set.range code).Infinite) (F : Finset ℤ) :
    firstCodeOutside code hinf F ≤ F.card := by
  by_contra h
  have hlt : F.card < firstCodeOutside code hinf F := Nat.lt_of_not_ge h
  let I := (Finset.range (F.card + 1)).image code
  have hsub : I ⊆ F := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    have hklt : k < firstCodeOutside code hinf F := by
      have : k < F.card + 1 := Finset.mem_range.mp hk
      omega
    exact Classical.byContradiction fun hnot =>
      Nat.find_min (exists_code_not_mem code hinf F) hklt hnot
  have hcardI : I.card = F.card + 1 := by
    rw [Finset.card_image_of_injective]
    · simp [I]
    · exact hinj
  have := Finset.card_le_card hsub
  rw [hcardI] at this
  omega

private noncomputable def noRepeatSweep (i n : ℕ) (xs : Fin n → ℤ) : ℤ :=
  let prior := Finset.univ.image fun k : Fin n =>
    noRepeatSweep i k (restrictHistory xs k)
  let forbidden := GenLimit.Generic.sequenceSample xs ∪ prior
  if GenLimit.NoiseLossFeedback.omissionMarkerFinset i ⊆
      GenLimit.Generic.sequenceSample xs then
    GenLimit.UnionClosedness.positiveCode
      (firstCodeOutside GenLimit.UnionClosedness.positiveCode
        (by rw [GenLimit.UnionClosedness.range_positiveCode];
            exact GenLimit.UnionClosedness.positiveIntegers_infinite)
        forbidden)
  else
    GenLimit.UnionClosedness.negativeCode
      (firstCodeOutside GenLimit.UnionClosedness.negativeCode
        (by rw [GenLimit.UnionClosedness.range_negativeCode];
            exact GenLimit.UnionClosedness.negativeIntegers_infinite)
        forbidden)
termination_by n
decreasing_by exact k.isLt

private theorem noRepeatSweep_mem_side_and_bound (i : ℕ) {n : ℕ}
    (xs : Fin n → ℤ) :
    let detected := GenLimit.NoiseLossFeedback.omissionMarkerFinset i ⊆
      GenLimit.Generic.sequenceSample xs
    let z := noRepeatSweep i n xs
    z ∉ GenLimit.Generic.sequenceSample xs ∧
      z ∉ Finset.univ.image (fun k : Fin n =>
        noRepeatSweep i k (restrictHistory xs k)) ∧
      if detected then
        ∃ m ≤ 2 * n, z = GenLimit.UnionClosedness.positiveCode m
      else
        ∃ m ≤ 2 * n, z = GenLimit.UnionClosedness.negativeCode m := by
  dsimp only
  let prior := Finset.univ.image fun k : Fin n =>
    noRepeatSweep i k (restrictHistory xs k)
  let forbidden := GenLimit.Generic.sequenceSample xs ∪ prior
  have hsampleCard : (GenLimit.Generic.sequenceSample xs).card ≤ n := by
    unfold GenLimit.Generic.sequenceSample
    calc
      (@Finset.image (Fin n) ℤ (Classical.decEq ℤ) xs Finset.univ).card ≤
          Finset.univ.card :=
        @Finset.card_image_le (Fin n) ℤ Finset.univ xs (Classical.decEq ℤ)
      _ = n := by simp
  have hpriorCard : prior.card ≤ n := by
    dsimp [prior]
    calc
      (@Finset.image (Fin n) ℤ Int.instDecidableEq
          (fun k : Fin n => noRepeatSweep i k (restrictHistory xs k))
          Finset.univ).card ≤ Finset.univ.card :=
        @Finset.card_image_le (Fin n) ℤ Finset.univ
          (fun k : Fin n => noRepeatSweep i k (restrictHistory xs k))
          Int.instDecidableEq
      _ = n := by simp
  have hforbiddenCard : forbidden.card ≤ 2 * n := by
    exact (Finset.card_union_le _ _).trans (by omega)
  by_cases hd : GenLimit.NoiseLossFeedback.omissionMarkerFinset i ⊆
      GenLimit.Generic.sequenceSample xs
  · let hinf : (Set.range GenLimit.UnionClosedness.positiveCode).Infinite := by
      rw [GenLimit.UnionClosedness.range_positiveCode]
      exact GenLimit.UnionClosedness.positiveIntegers_infinite
    let m := firstCodeOutside GenLimit.UnionClosedness.positiveCode hinf forbidden
    have hmF := firstCodeOutside_spec
      GenLimit.UnionClosedness.positiveCode hinf forbidden
    have hmbound := (firstCodeOutside_le_card
      GenLimit.UnionClosedness.positiveCode
      GenLimit.UnionClosedness.positiveCode_injective hinf forbidden).trans
        hforbiddenCard
    have hout : noRepeatSweep i n xs =
        GenLimit.UnionClosedness.positiveCode m := by
      rw [noRepeatSweep.eq_1]
      simp only [hd, if_true]
      rfl
    rw [hout]
    refine ⟨?_, ?_, ?_⟩
    · exact fun h => hmF (Finset.mem_union_left _ h)
    · exact fun h => hmF (Finset.mem_union_right _ h)
    · simp only [hd, if_true]
      exact ⟨m, hmbound, rfl⟩
  · let hinf : (Set.range GenLimit.UnionClosedness.negativeCode).Infinite := by
      rw [GenLimit.UnionClosedness.range_negativeCode]
      exact GenLimit.UnionClosedness.negativeIntegers_infinite
    let m := firstCodeOutside GenLimit.UnionClosedness.negativeCode hinf forbidden
    have hmF := firstCodeOutside_spec
      GenLimit.UnionClosedness.negativeCode hinf forbidden
    have hmbound := (firstCodeOutside_le_card
      GenLimit.UnionClosedness.negativeCode
      GenLimit.UnionClosedness.negativeCode_injective hinf forbidden).trans
        hforbiddenCard
    have hout : noRepeatSweep i n xs =
        GenLimit.UnionClosedness.negativeCode m := by
      rw [noRepeatSweep.eq_1]
      simp only [hd, if_false]
      rfl
    rw [hout]
    refine ⟨?_, ?_, ?_⟩
    · exact fun h => hmF (Finset.mem_union_left _ h)
    · exact fun h => hmF (Finset.mem_union_right _ h)
    · simp only [hd, if_false]
      exact ⟨m, hmbound, rfl⟩



private theorem noRepeatSweep_output_spec (i : ℕ) (input : Stream ℤ) (t : ℕ) :
    let z := outputAfterInput (noRepeatSweep i) input t
    z ∉ GenLimit.Generic.sample input (t + 1) ∧
      (∀ s, s < t → outputAfterInput (noRepeatSweep i) input s ≠ z) ∧
      if GenLimit.NoiseLossFeedback.omissionMarkerFinset i ⊆
          GenLimit.Generic.sample input (t + 1) then
        ∃ m ≤ 2 * (t + 1), z = GenLimit.UnionClosedness.positiveCode m
      else
        ∃ m ≤ 2 * (t + 1), z = GenLimit.UnionClosedness.negativeCode m := by
  dsimp only [outputAfterInput, GenLimit.Generic.output]
  have h := noRepeatSweep_mem_side_and_bound i
    (xs := fun k : Fin (t + 1) => input k)
  rw [GenLimit.Generic.sequenceSample_prefix input (t + 1)] at h
  refine ⟨h.1, ?_, h.2.2⟩
  intro s hst heq
  apply h.2.1
  apply Finset.mem_image.mpr
  let k : Fin (t + 1) := ⟨s + 1, by omega⟩
  refine ⟨k, Finset.mem_univ k, ?_⟩
  calc
    noRepeatSweep i k
        (restrictHistory (fun j : Fin (t + 1) => input j) k) =
      outputAfterInput (noRepeatSweep i) input s := by
        dsimp [k, outputAfterInput, GenLimit.Generic.output]
        congr 1
    _ = noRepeatSweep i (t + 1)
        (fun j : Fin (t + 1) => input j) := heq

private theorem balanced_negativeCode (m : ℕ) :
    balanced (2 * m + 1) = GenLimit.UnionClosedness.negativeCode m := by
  have hmod : (2 * m) % 2 = 0 := by omega
  simp [balanced, hmod, GenLimit.UnionClosedness.negativeCode,
    Int.negSucc_eq]

private theorem balanced_positiveCode (m : ℕ) :
    balanced (2 * m + 2) = GenLimit.UnionClosedness.positiveCode m := by
  have hmod : (2 * m + 1) % 2 = 1 := by omega
  have hdiv : (2 * m + 1) / 2 = m := by omega
  simp [balanced, hmod, hdiv, GenLimit.UnionClosedness.positiveCode]

private theorem balancedRanks_negativeCode {A : Set ℤ} {m : ℕ}
    (hm : GenLimit.UnionClosedness.negativeCode m ∈ A) :
    2 * m + 1 ∈ balancedRanks A := by
  change balanced (2 * m + 1) ∈ A
  rw [balanced_negativeCode]
  exact hm

private theorem balancedRanks_positiveCode {A : Set ℤ} {m : ℕ}
    (hm : GenLimit.UnionClosedness.positiveCode m ∈ A) :
    2 * m + 2 ∈ balancedRanks A := by
  change balanced (2 * m + 2) ∈ A
  rw [balanced_positiveCode]
  exact hm



private theorem quarter_density_of_ranked_outputs
    (input output : Stream ℤ) (K : Language ℤ)
    (hKR : (balancedRanks K).Infinite) (T : ℕ)
    (hvalid : ∀ t, T ≤ t →
      output t ∈ K ∧
        output t ∉ GenLimit.Generic.sample input (t + 1) ∧
        ∀ s, s < t → output s ≠ output t)
    (hrank : ∀ t, T ≤ t →
      ∃ r < 4 * t + 7, balanced r = output t) :
    (1 / 4 : ℝ) ≤ balancedRelativeLowerDensity
      (GeneratorFirstOn input output ∩ K) K := by
  classical
  let A : Set ℕ := balancedRanks (GeneratorFirstOn input output ∩ K)
  let R : Set ℕ := balancedRanks K
  let c := T + 2
  have hcount : ∀ n, n / 4 - c ≤ GenLimit.PatientScope.prefixCount A n := by
    intro n
    let k := n / 4 - c
    let rank : Fin k → ℕ := fun s =>
      Classical.choose (hrank (T + s) (by omega))
    have hrank_lt (s : Fin k) : rank s < 4 * (T + s) + 7 := by
      exact (Classical.choose_spec (hrank (T + s) (by omega))).1
    have hrank_eq (s : Fin k) : balanced (rank s) = output (T + s) := by
      exact (Classical.choose_spec (hrank (T + s) (by omega))).2
    have hrank_prefix (s : Fin k) : rank s < n := by
      have hs := s.isLt
      have hrs := hrank_lt s
      dsimp [k, c] at hs
      omega
    have hrank_mem (s : Fin k) : rank s ∈ A := by
      change balanced (rank s) ∈ GeneratorFirstOn input output ∩ K
      rw [hrank_eq]
      refine ⟨?_, (hvalid (T + s) (by omega)).1⟩
      refine ⟨T + s, rfl, ?_⟩
      intro u hu heq
      exact (hvalid (T + s) (by omega)).2.1 <|
        GenLimit.Generic.mem_sample_iff.mpr ⟨u, by omega, heq⟩
    have hrank_injective : Function.Injective rank := by
      intro a b hab
      by_contra hne
      rcases lt_or_gt_of_ne hne with hablt | hbalt
      · exact (hvalid (T + b) (by omega)).2.2 (T + a) (by omega) <|
          (hrank_eq a).symm.trans <| congrArg balanced hab |>.trans (hrank_eq b)
      · exact (hvalid (T + a) (by omega)).2.2 (T + b) (by omega) <|
          (hrank_eq b).symm.trans <| congrArg balanced hab.symm |>.trans (hrank_eq a)
    let I := Finset.univ.image rank
    have hIcard : I.card = k := by
      dsimp [I]
      rw [Finset.card_image_of_injective]
      · simp
      · exact hrank_injective
    have hIsub : I ⊆ GenLimit.PatientScope.prefixFinset A n := by
      intro r hr
      obtain ⟨s, _hs, rfl⟩ := Finset.mem_image.mp hr
      exact GenLimit.PatientScope.mem_prefixFinset.mpr
        ⟨hrank_prefix s, hrank_mem s⟩
    change k ≤ GenLimit.PatientScope.prefixCount A n
    rw [← hIcard]
    exact Finset.card_le_card hIsub
  have hAR : A ⊆ R := by
    intro r hr
    exact hr.2
  have hDleN : ∀ n, GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount R n :=
    fun n => GenLimit.PatientScope.prefixCount_mono hAR n
  have hNle : ∀ n, GenLimit.PatientScope.prefixCount R n ≤ n := by
    intro n
    unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
    exact (Finset.card_filter_le _ _).trans_eq (by simp)
  let g : ℕ → ℝ := fun n =>
    (1 / 4 : ℝ) - ((4 * c + 3 : ℕ) : ℝ) / (4 * (n : ℝ))
  have hg : Tendsto g atTop (𝓝 (1 / 4 : ℝ)) := by
    have he : Tendsto
        (fun n : ℕ => ((4 * c + 3 : ℕ) : ℝ) / (4 * (n : ℝ)))
        atTop (𝓝 0) := by
      have hbase : Tendsto
          (fun n : ℕ => (((4 * c + 3 : ℕ) : ℝ) / 4) / (n : ℝ))
          atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      simpa only [div_div] using hbase
    simpa only [g, sub_zero] using
      (tendsto_const_nhds.sub he : Tendsto
        (fun n : ℕ => (1 / 4 : ℝ) -
          ((4 * c + 3 : ℕ) : ℝ) / (4 * (n : ℝ)))
        atTop (𝓝 ((1 / 4 : ℝ) - 0)))
  have hcompare : ∀ᶠ n : ℕ in atTop,
      g n ≤ (GenLimit.PatientScope.prefixCount A n : ℝ) /
        GenLimit.PatientScope.prefixCount R n := by
    have hRpos : ∀ᶠ n : ℕ in atTop,
        0 < GenLimit.PatientScope.prefixCount R n :=
      (GenLimit.PatientScope.tendsto_prefixCount_atTop hKR).eventually
        (eventually_gt_atTop 0)
    filter_upwards [hRpos] with n hn
    have hnpos : 0 < n := lt_of_lt_of_le hn (hNle n)
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hNR : (0 : ℝ) < GenLimit.PatientScope.prefixCount R n := by
      exact_mod_cast hn
    have hnat : n ≤
        4 * GenLimit.PatientScope.prefixCount A n + (4 * c + 3) := by
      have hdiv : n / 4 ≤ GenLimit.PatientScope.prefixCount A n + c :=
        Nat.sub_le_iff_le_add.mp (hcount n)
      have hmod : n ≤ 4 * (n / 4) + 3 := by omega
      omega
    have hreal : (n : ℝ) ≤
        4 * GenLimit.PatientScope.prefixCount A n + (4 * c + 3) := by
      exact_mod_cast hnat
    have hgDn : g n ≤
        (GenLimit.PatientScope.prefixCount A n : ℝ) / n := by
      norm_num [Nat.cast_add, Nat.cast_mul] at hreal
      dsimp [g]
      rw [le_div_iff₀ hnR]
      field_simp [hnR.ne']
      norm_num [Nat.cast_add, Nat.cast_mul]
      nlinarith
    calc
      g n ≤ (GenLimit.PatientScope.prefixCount A n : ℝ) / n := hgDn
      _ ≤ (GenLimit.PatientScope.prefixCount A n : ℝ) /
          GenLimit.PatientScope.prefixCount R n := by
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hNR
          (by exact_mod_cast hNle n)
  have hratio_le_one : ∀ n,
      (GenLimit.PatientScope.prefixCount A n : ℝ) /
          GenLimit.PatientScope.prefixCount R n ≤ 1 := by
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount R n = 0
    · simp [hn]
    · rw [div_le_one (by positivity)]
      exact_mod_cast hDleN n
  rw [balancedRelativeLowerDensity,
    GenLimit.PatientScope.relativeLowerDensity]
  change (1 / 4 : ℝ) ≤ liminf
    (fun n : ℕ => (GenLimit.PatientScope.prefixCount A n : ℝ) /
      GenLimit.PatientScope.prefixCount R n) atTop
  calc
    (1 / 4 : ℝ) = liminf g atTop := hg.liminf_eq.symm
    _ ≤ liminf
        (fun n : ℕ => (GenLimit.PatientScope.prefixCount A n : ℝ) /
          GenLimit.PatientScope.prefixCount R n) atTop :=
      liminf_le_liminf hcompare hg.isBoundedUnder_ge
        (isCoboundedUnder_ge_of_le atTop hratio_le_one)



private theorem noRepeatSweep_output_injective (i : ℕ) (input : Stream ℤ) :
    Function.Injective (outputAfterInput (noRepeatSweep i) input) := by
  intro a b hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with hablt | hbalt
  · exact (noRepeatSweep_output_spec i input b).2.1 a hablt hab
  · exact (noRepeatSweep_output_spec i input a).2.1 b hbalt hab.symm

private theorem noRepeatSweep_first_result
    {i : ℕ} {K : Language ℤ}
    (hK : K ∈ GenLimit.NoiseLossFeedback.finiteOmissionFirstClass i)
    (input : Stream ℤ)
    (henum : GenLimit.NoiseLossFeedback.NoisyEnumerationWithLevel input K i) :
    NovelGeneratesAfterInput input
        (outputAfterInput (noRepeatSweep i) input) K ∧
      (1 / 4 : ℝ) ≤ balancedRelativeLowerDensity
        (GeneratorFirstOn input (outputAfterInput (noRepeatSweep i) input) ∩ K) K := by
  classical
  obtain ⟨hmarkers, j, htail⟩ := hK
  obtain ⟨Td, hTd⟩ :=
    GenLimit.NoiseLossFeedback.allMarkers_eventually_observed henum hmarkers
  let output := outputAfterInput (noRepeatSweep i) input
  let bad : Set ℤ :=
    ↑((Finset.range j).image GenLimit.UnionClosedness.positiveCode)
  let badTimes : Set ℕ := output ⁻¹' bad
  have hbadFinite : bad.Finite := by
    exact ((Finset.range j).image
      GenLimit.UnionClosedness.positiveCode).finite_toSet
  have hbadTimesFinite : badTimes.Finite := by
    exact hbadFinite.preimage
      (noRepeatSweep_output_injective i input).injOn
  let B := hbadTimesFinite.toFinset.sup id + 1
  let T := max Td B
  have hnotBad : ∀ t, B ≤ t → t ∉ badTimes := by
    intro t ht hmem
    have htmem : t ∈ hbadTimesFinite.toFinset :=
      hbadTimesFinite.mem_toFinset.mpr hmem
    have hle : t ≤ hbadTimesFinite.toFinset.sup id :=
      Finset.le_sup (f := id) htmem
    dsimp [B] at ht
    omega
  have hvalid : ∀ t, T ≤ t →
      output t ∈ K ∧
        output t ∉ GenLimit.Generic.sample input (t + 1) ∧
        ∀ s, s < t → output s ≠ output t := by
    intro t ht
    have htTd : Td ≤ t := le_trans (Nat.le_max_left _ _) ht
    have htB : B ≤ t := le_trans (Nat.le_max_right _ _) ht
    have hdetect : GenLimit.NoiseLossFeedback.omissionMarkerFinset i ⊆
        GenLimit.Generic.sample input (t + 1) := hTd t htTd
    have hs := noRepeatSweep_output_spec i input t
    dsimp only at hs
    dsimp [output]
    rw [if_pos hdetect] at hs
    obtain ⟨hfresh, hnovel, m, hmbound, hout⟩ := hs
    have hmj : j ≤ m := by
      by_contra hm
      have hmj' : m < j := Nat.lt_of_not_ge hm
      apply hnotBad t htB
      change output t ∈ bad
      dsimp [bad, output]
      simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_range]
      exact ⟨m, hmj', hout.symm⟩
    refine ⟨?_, hfresh, hnovel⟩
    rw [hout]
    apply htail
    exact ⟨m - j, by
      simpa using congrArg GenLimit.UnionClosedness.positiveCode
        (Nat.add_sub_of_le hmj)⟩
  have hrank : ∀ t, T ≤ t →
      ∃ r < 4 * t + 7, balanced r = output t := by
    intro t ht
    have htTd : Td ≤ t := le_trans (Nat.le_max_left _ _) ht
    have hdetect : GenLimit.NoiseLossFeedback.omissionMarkerFinset i ⊆
        GenLimit.Generic.sample input (t + 1) := hTd t htTd
    have hs := noRepeatSweep_output_spec i input t
    dsimp only at hs
    rw [if_pos hdetect] at hs
    obtain ⟨_hfresh, _hnovel, m, hmbound, hout⟩ := hs
    refine ⟨2 * m + 2, by omega, ?_⟩
    exact (balanced_positiveCode m).trans hout.symm
  have hKR : (balancedRanks K).Infinite := by
    let ranks : ℕ → ℕ := fun k => 2 * (j + k) + 2
    have hranksInj : Function.Injective ranks := by
      intro a b hab
      dsimp [ranks] at hab
      omega
    apply (Set.infinite_range_of_injective hranksInj).mono
    rintro r ⟨k, rfl⟩
    change balanced (ranks k) ∈ K
    dsimp [ranks]
    rw [balanced_positiveCode]
    apply htail
    exact ⟨k, rfl⟩
  constructor
  · exact ⟨T, hvalid⟩
  · exact quarter_density_of_ranked_outputs input output K hKR T hvalid hrank

private theorem noRepeatSweep_second_result
    {i : ℕ} {K : Language ℤ}
    (hK : K ∈ GenLimit.NoiseLossFeedback.finiteOmissionSecondClass i)
    (input : Stream ℤ)
    (henum : GenLimit.NoiseLossFeedback.NoisyEnumerationWithLevel input K i) :
    NovelGeneratesAfterInput input
        (outputAfterInput (noRepeatSweep i) input) K ∧
      (1 / 4 : ℝ) ≤ balancedRelativeLowerDensity
        (GeneratorFirstOn input (outputAfterInput (noRepeatSweep i) input) ∩ K) K := by
  let output := outputAfterInput (noRepeatSweep i) input
  have hvalid : ∀ t, 0 ≤ t →
      output t ∈ K ∧
        output t ∉ GenLimit.Generic.sample input (t + 1) ∧
        ∀ s, s < t → output s ≠ output t := by
    intro t _ht
    have hnoDetect : ¬GenLimit.NoiseLossFeedback.omissionMarkerFinset i ⊆
        GenLimit.Generic.sample input (t + 1) :=
      GenLimit.NoiseLossFeedback.not_allMarkers_observed_second hK henum t
    have hs := noRepeatSweep_output_spec i input t
    dsimp only at hs
    dsimp [output]
    rw [if_neg hnoDetect] at hs
    obtain ⟨hfresh, hnovel, m, _hmbound, hout⟩ := hs
    refine ⟨?_, hfresh, hnovel⟩
    rw [hout]
    exact hK.1 (GenLimit.UnionClosedness.negativeCode_mem m)
  have hrank : ∀ t, 0 ≤ t →
      ∃ r < 4 * t + 7, balanced r = output t := by
    intro t _ht
    have hnoDetect : ¬GenLimit.NoiseLossFeedback.omissionMarkerFinset i ⊆
        GenLimit.Generic.sample input (t + 1) :=
      GenLimit.NoiseLossFeedback.not_allMarkers_observed_second hK henum t
    have hs := noRepeatSweep_output_spec i input t
    dsimp only at hs
    rw [if_neg hnoDetect] at hs
    obtain ⟨_hfresh, _hnovel, m, hmbound, hout⟩ := hs
    refine ⟨2 * m + 1, by omega, ?_⟩
    exact (balanced_negativeCode m).trans hout.symm
  have hKR : (balancedRanks K).Infinite := by
    let ranks : ℕ → ℕ := fun k => 2 * k + 1
    have hranksInj : Function.Injective ranks := by
      intro a b hab
      dsimp [ranks] at hab
      omega
    apply (Set.infinite_range_of_injective hranksInj).mono
    rintro r ⟨k, rfl⟩
    change balanced (ranks k) ∈ K
    dsimp [ranks]
    rw [balanced_negativeCode]
    exact hK.1 (GenLimit.UnionClosedness.negativeCode_mem k)
  constructor
  · exact ⟨0, hvalid⟩
  · exact quarter_density_of_ranked_outputs input output K hKR 0 hvalid hrank

private def encodedFirstLanguage (i : ℕ) (A : Set ℕ) : Language ℤ :=
  (GenLimit.NoiseLossFeedback.omissionMarkerFinset i : Set ℤ) ∪
    GenLimit.UnionClosedness.positiveIntegers ∪
      GenLimit.UnionClosedness.negativeCode '' A

private theorem negativeCode_mem_encodedFirstLanguage_iff
    (i n : ℕ) (A : Set ℕ) :
    GenLimit.UnionClosedness.negativeCode n ∈ encodedFirstLanguage i A ↔ n ∈ A := by
  constructor
  · rintro (hleft | himage)
    · rcases hleft with hmarker | hpositive
      · exact False.elim
          (GenLimit.NoiseLossFeedback.negativeCode_not_marker i n hmarker)
      · change 0 < GenLimit.UnionClosedness.negativeCode n at hpositive
        exact False.elim <| (Int.not_lt_of_ge (Int.le_of_lt hpositive))
          (GenLimit.UnionClosedness.negativeCode_mem n)
    · obtain ⟨m, hmA, hmn⟩ := himage
      have hmn' : m = n :=
        GenLimit.UnionClosedness.negativeCode_injective hmn
      simpa [hmn'] using hmA
  · intro hn
    exact Or.inr ⟨n, hn, rfl⟩

private theorem encodedFirstLanguage_injective (i : ℕ) :
    Function.Injective (encodedFirstLanguage i) := by
  intro A B hAB
  ext n
  rw [← negativeCode_mem_encodedFirstLanguage_iff i n A,
    hAB, negativeCode_mem_encodedFirstLanguage_iff i n B]

private theorem encodedFirstLanguage_mem_class (i : ℕ) (A : Set ℕ) :
    encodedFirstLanguage i A ∈
      GenLimit.NoiseLossFeedback.finiteOmissionClass i := by
  left
  constructor
  · exact fun z hz => Or.inl (Or.inl hz)
  · refine ⟨0, ?_⟩
    rintro z ⟨k, rfl⟩
    exact Or.inl <| Or.inr <|
      by simpa using GenLimit.UnionClosedness.positiveCode_mem k

private theorem finiteOmissionClass_not_countable (i : ℕ) :
    ¬(GenLimit.NoiseLossFeedback.finiteOmissionClass i).Countable := by
  intro hcount
  have hrange : (Set.range (encodedFirstLanguage i)).Countable := by
    apply hcount.mono
    exact Set.range_subset_iff.mpr (encodedFirstLanguage_mem_class i)
  have hpre := hrange.preimage_of_injOn
    (encodedFirstLanguage_injective i).injOn
  have hpreUniv : encodedFirstLanguage i ⁻¹'
      Set.range (encodedFirstLanguage i) = Set.univ := by
    ext A
    simp
  rw [hpreUniv] at hpre
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ
    (Set.countable_univ_iff.mp hpre)

/-- The uncountable adjacent-level separation milestone. -/
theorem stage3_uncountable_separation : SeparationClause := by
  intro i
  let family := GenLimit.NoiseLossFeedback.finiteOmissionClass i
  refine ⟨family, finiteOmissionClass_not_countable i, ?_, ?_, ?_⟩
  · exact GenLimit.NoiseLossFeedback.finiteOmissionClass_uus i
  · refine ⟨noRepeatSweep i, ?_⟩
    intro K hK input henum
    rcases hK with hfirst | hsecond
    · exact noRepeatSweep_first_result hfirst input henum
    · exact noRepeatSweep_second_result hsecond input henum
  · intro gen
    by_contra hcounter
    apply GenLimit.NoiseLossFeedback.finiteNoiseLevel_lower i
    refine ⟨gen, ?_⟩
    intro K hK input henum
    have hall : SampleFreshGeneratesAfterInput input
        (outputAfterInput gen input) K := by
      by_contra hfail
      apply hcounter
      exact ⟨K, hK, input, henum, hfail⟩
    exact hall

end

end Stage3Case019
