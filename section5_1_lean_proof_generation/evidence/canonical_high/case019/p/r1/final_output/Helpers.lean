import Stage3Model

namespace Stage3Case019.Local

def codedLanguage (S : Set ℕ) : Set ℤ :=
  Set.range Int.negSucc ∪ {z | ∃ n ∈ S, z = Int.ofNat (n + 1)}

theorem codedLanguage_mem_iff (S : Set ℕ) (n : ℕ) :
    Int.ofNat (n + 1) ∈ codedLanguage S ↔ n ∈ S := by
  constructor
  · rintro (⟨m, hm⟩ | ⟨k, hk, heq⟩)
    · cases hm
    · have hnk : n = k := by
        injection heq with heq
        omega
      simpa [hnk] using hk
  · intro hn
    exact Or.inr ⟨n, hn, rfl⟩

theorem codedLanguage_injective : Function.Injective codedLanguage := by
  intro S T h
  ext n
  rw [← codedLanguage_mem_iff S n, h, codedLanguage_mem_iff T n]

theorem codedLanguage_infinite (S : Set ℕ) : (codedLanguage S).Infinite := by
  refine (Set.infinite_range_of_injective (f := Int.negSucc) ?_).mono ?_
  · intro m n h
    exact Int.negSucc_inj.mp h
  · intro z hz
    exact Or.inl hz

def uncountableLanguages : Set (Set ℤ) := Set.range codedLanguage

theorem uncountableLanguages_not_countable : ¬uncountableLanguages.Countable := by
  intro h
  have hpre := h.preimage codedLanguage_injective
  have huniv : (Set.univ : Set (Set ℕ)).Countable := by
    simpa [uncountableLanguages] using hpre
  rw [Set.countable_iff_exists_surjective (by simp)] at huniv
  obtain ⟨f, hf⟩ := huniv
  let diagonal : Set ℕ := {n | n ∉ (f n).1}
  obtain ⟨k, hk⟩ := hf ⟨diagonal, by simp⟩
  have hdiag : (f k).1 = diagonal := congrArg Subtype.val hk
  by_cases hmem : k ∈ (f k).1
  · have : k ∉ diagonal := by simpa [diagonal] using hmem
    exact this (hdiag ▸ hmem)
  · have : k ∈ diagonal := by simpa [diagonal] using hmem
    exact hmem (hdiag ▸ this)

theorem uncountableLanguages_infinite :
    ∀ K ∈ uncountableLanguages, K.Infinite := by
  rintro K ⟨S, rfl⟩
  exact codedLanguage_infinite S

end Stage3Case019.Local

namespace Stage3Case019.Local

def markers (q : ℕ) : Set ℤ := {z | ∃ n ≤ q, z = Int.ofNat n}

def positiveTail (j : ℕ) : Set ℤ := {z | ∃ n, j ≤ n ∧ z = Int.ofNat n}

def negativeHalf : Set ℤ := Set.range Int.negSucc

def familyA (q : ℕ) : Set (Set ℤ) :=
  {K | markers q ⊆ K ∧ ∃ j, positiveTail j ⊆ K}

def familyB (q : ℕ) : Set (Set ℤ) :=
  {K | negativeHalf ⊆ K ∧ Disjoint K (markers q)}

def witnessFamily (q : ℕ) : Set (Set ℤ) := familyA q ∪ familyB q

def separationCode (q : ℕ) (S : Set ℕ) : Set ℤ :=
  markers q ∪ positiveTail (q + 1) ∪ {z | ∃ n ∈ S, z = Int.negSucc n}

theorem separationCode_neg_mem_iff (q n : ℕ) (S : Set ℕ) :
    Int.negSucc n ∈ separationCode q S ↔ n ∈ S := by
  constructor
  · rintro ((hmark | htail) | ⟨k, hk, heq⟩)
    · obtain ⟨m, hm, heq⟩ := hmark
      cases heq
    · obtain ⟨m, hm, heq⟩ := htail
      cases heq
    · have hnk : n = k := Int.negSucc_inj.mp heq
      simpa [hnk] using hk
  · intro hn
    exact Or.inr ⟨n, hn, rfl⟩

theorem separationCode_injective (q : ℕ) : Function.Injective (separationCode q) := by
  intro S T h
  ext n
  rw [← separationCode_neg_mem_iff q n S, h, separationCode_neg_mem_iff q n T]

theorem positiveTail_infinite (j : ℕ) : (positiveTail j).Infinite := by
  let f : ℕ → ℤ := fun n => Int.ofNat (j + n)
  have hf : Function.Injective f := by
    intro m n h
    have : j + m = j + n := Int.ofNat_inj.mp h
    omega
  apply (Set.infinite_range_of_injective hf).mono
  rintro z ⟨n, rfl⟩
  exact ⟨j + n, by omega, rfl⟩

theorem negativeHalf_infinite : negativeHalf.Infinite := by
  exact Set.infinite_range_of_injective (by
    intro m n h
    exact Int.negSucc_inj.mp h)

theorem separationCode_mem_familyA (q : ℕ) (S : Set ℕ) :
    separationCode q S ∈ familyA q := by
  constructor
  · intro z hz
    exact Or.inl (Or.inl hz)
  · exact ⟨q + 1, fun z hz => Or.inl (Or.inr hz)⟩

theorem witnessFamily_infinite (q : ℕ) :
    ∀ K ∈ witnessFamily q, K.Infinite := by
  rintro K (hA | hB)
  · obtain ⟨_, j, hj⟩ := hA
    exact (positiveTail_infinite j).mono hj
  · exact negativeHalf_infinite.mono hB.1

theorem range_injective_set_not_countable
    {β : Type*} (f : Set ℕ → β) (hf : Function.Injective f) :
    ¬(Set.range f).Countable := by
  intro h
  have hpre := h.preimage hf
  have huniv : (Set.univ : Set (Set ℕ)).Countable := by
    simpa using hpre
  rw [Set.countable_iff_exists_surjective (by simp)] at huniv
  obtain ⟨g, hg⟩ := huniv
  let diagonal : Set ℕ := {n | n ∉ (g n).1}
  obtain ⟨k, hk⟩ := hg ⟨diagonal, by simp⟩
  have hdiag : (g k).1 = diagonal := congrArg Subtype.val hk
  by_cases hmem : k ∈ (g k).1
  · have : k ∉ diagonal := by simpa [diagonal] using hmem
    exact this (hdiag ▸ hmem)
  · have : k ∈ diagonal := by simpa [diagonal] using hmem
    exact hmem (hdiag ▸ this)

theorem witnessFamily_not_countable (q : ℕ) : ¬(witnessFamily q).Countable := by
  intro h
  have hrange : (Set.range (separationCode q)).Countable := by
    apply h.mono
    rintro K ⟨S, rfl⟩
    exact Or.inl (separationCode_mem_familyA q S)
  exact range_injective_set_not_countable (separationCode q)
    (separationCode_injective q) hrange

end Stage3Case019.Local

namespace Stage3Case019.Local

noncomputable def markerFinset (q : ℕ) : Finset ℤ :=
  (Finset.range (q + 1)).image Int.ofNat

theorem mem_markerFinset_iff (q : ℕ) (z : ℤ) :
    z ∈ markerFinset q ↔ z ∈ markers q := by
  simp [markerFinset, markers, Nat.lt_succ_iff, eq_comm]

theorem markerFinset_card (q : ℕ) : (markerFinset q).card = q + 1 := by
  rw [markerFinset, Finset.card_image_of_injective]
  · simp
  · intro m n h
    exact Int.ofNat_inj.mp h

theorem familyB_markers_outside {q : ℕ} {K : Set ℤ}
    (hK : K ∈ familyB q) : markers q ⊆ Kᶜ := by
  intro z hz hzin
  exact Set.disjoint_left.1 hK.2 hzin hz

theorem level_q_familyB_omits_marker {q : ℕ} {K : Set ℤ}
    (hK : K ∈ familyB q) {input : Stream ℤ}
    (hp : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q) :
    ¬markers q ⊆ Set.range input := by
  intro hall
  obtain ⟨F, hF, hcard⟩ := hp.2.2
  have hsubset : markerFinset q ⊆ F := by
    intro z hz
    have hzmark : z ∈ markers q := (mem_markerFinset_iff q z).mp hz
    have hzrange : z ∈ Set.range input := hall hzmark
    have hznotK : z ∉ K := familyB_markers_outside hK hzmark
    have : z ∈ (Set.range input \ K) := ⟨hzrange, hznotK⟩
    change z ∈ (F : Set ℤ)
    rw [hF]
    exact this
  have hle := Finset.card_le_card hsubset
  rw [markerFinset_card] at hle
  omega

end Stage3Case019.Local

namespace Stage3Case019.Local

noncomputable def freshIndex (rank : ℕ → ℤ) (hrank : Function.Injective rank)
    (forbidden : Finset ℤ) : ℕ :=
  Nat.find (by
    obtain ⟨z, ⟨n, rfl⟩, hz⟩ :=
      (Set.infinite_range_of_injective hrank).exists_not_mem_finset forbidden
    exact ⟨n, hz⟩)

theorem freshIndex_not_mem (rank : ℕ → ℤ) (hrank : Function.Injective rank)
    (forbidden : Finset ℤ) : rank (freshIndex rank hrank forbidden) ∉ forbidden := by
  exact Nat.find_spec (by
    obtain ⟨z, ⟨n, rfl⟩, hz⟩ :=
      (Set.infinite_range_of_injective hrank).exists_not_mem_finset forbidden
    exact ⟨n, hz⟩)

def negativeRank (n : ℕ) : ℤ := Int.negSucc n

def positiveRank (n : ℕ) : ℤ := Int.ofNat n

theorem negativeRank_injective : Function.Injective negativeRank := by
  intro m n h
  exact Int.negSucc_inj.mp h

theorem positiveRank_injective : Function.Injective positiveRank := by
  intro m n h
  exact Int.ofNat_inj.mp h

noncomputable def branchOutput (q : ℕ) : (t : ℕ) → (Fin t → ℤ) → ℤ
  | t, history =>
      let prior : Finset ℤ := Finset.univ.image fun s : Fin t =>
        branchOutput q s.1 (fun i => history (Fin.castLE (Nat.le_of_lt s.2) i))
      let forbidden := GenLimit.Generic.sequenceSample history ∪ prior
      if markerFinset q ⊆ GenLimit.Generic.sequenceSample history then
        positiveRank (freshIndex positiveRank positiveRank_injective forbidden)
      else
        negativeRank (freshIndex negativeRank negativeRank_injective forbidden)
termination_by t history => t

noncomputable def branchGenerator (q : ℕ) : Generator ℤ := branchOutput q

end Stage3Case019.Local

namespace Stage3Case019.Local

theorem branchOutput_fresh (q t : ℕ) (history : Fin t → ℤ) :
    branchOutput q t history ∉ GenLimit.Generic.sequenceSample history ∧
      ∀ s : Fin t,
        branchOutput q t history ≠
          branchOutput q s.1 (fun i => history (Fin.castLE (Nat.le_of_lt s.2) i)) := by
  rw [branchOutput]
  split <;> rename_i hmode
  · have hfresh := freshIndex_not_mem positiveRank positiveRank_injective
        (GenLimit.Generic.sequenceSample history ∪
          Finset.univ.image fun s : Fin t =>
            branchOutput q s.1 (fun i => history (Fin.castLE (Nat.le_of_lt s.2) i)))
    constructor
    · intro hmem
      exact hfresh (Finset.mem_union_left _ hmem)
    · intro s heq
      exact hfresh (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s, by simp, heq.symm⟩))
  · have hfresh := freshIndex_not_mem negativeRank negativeRank_injective
        (GenLimit.Generic.sequenceSample history ∪
          Finset.univ.image fun s : Fin t =>
            branchOutput q s.1 (fun i => history (Fin.castLE (Nat.le_of_lt s.2) i)))
    constructor
    · intro hmem
      exact hfresh (Finset.mem_union_left _ hmem)
    · intro s heq
      exact hfresh (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s, by simp, heq.symm⟩))

end Stage3Case019.Local

namespace Stage3Case019.Local

theorem sequenceSample_stream_prefix (input : Stream α) (t : ℕ) :
    GenLimit.Generic.sequenceSample (fun i : Fin t => input i) =
      GenLimit.Generic.sample input t := by
  ext z
  simp only [GenLimit.Generic.sequenceSample, GenLimit.Generic.sample,
    Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.2, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

theorem branchGenerator_sample_fresh (q : ℕ) (input : Stream ℤ) (t : ℕ) :
    outputAfterInput (branchGenerator q) input t ∉
      GenLimit.Generic.sample input (t + 1) := by
  change branchOutput q (t + 1) (fun i => input i) ∉ _
  rw [← sequenceSample_stream_prefix input (t + 1)]
  exact (branchOutput_fresh q (t + 1) (fun i => input i)).1

theorem branchGenerator_norepeat (q : ℕ) (input : Stream ℤ) {s t : ℕ}
    (hst : s < t) :
    outputAfterInput (branchGenerator q) input s ≠
      outputAfterInput (branchGenerator q) input t := by
  change branchOutput q (s + 1) (fun i => input i) ≠
    branchOutput q (t + 1) (fun i => input i)
  symm
  let k : Fin (t + 1) := ⟨s + 1, by omega⟩
  have h := (branchOutput_fresh q (t + 1) (fun i => input i)).2 k
  simpa [k] using h

end Stage3Case019.Local

namespace Stage3Case019.Local

theorem branchOutput_negative_of_markers_missing (q t : ℕ) (history : Fin t → ℤ)
    (hmissing : ¬markerFinset q ⊆ GenLimit.Generic.sequenceSample history) :
    ∃ n, branchOutput q t history = Int.negSucc n := by
  rw [branchOutput]
  split
  · contradiction
  · exact ⟨_, rfl⟩

theorem branchOutput_positive_of_markers_seen (q t : ℕ) (history : Fin t → ℤ)
    (hseen : markerFinset q ⊆ GenLimit.Generic.sequenceSample history) :
    ∃ n, branchOutput q t history = Int.ofNat n := by
  rw [branchOutput]
  split
  · exact ⟨_, rfl⟩
  · contradiction

theorem familyB_markers_ne_sample {q : ℕ} {K : Set ℤ}
    (hK : K ∈ familyB q) {input : Stream ℤ}
    (hp : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q)
    (t : ℕ) :
    ¬markerFinset q ⊆ GenLimit.Generic.sample input t := by
  intro hall
  apply level_q_familyB_omits_marker hK hp
  intro z hz
  have hzfin : z ∈ markerFinset q := (mem_markerFinset_iff q z).mpr hz
  have hzsample := hall hzfin
  simp only [GenLimit.Generic.sample, Finset.mem_image, Finset.mem_range] at hzsample
  obtain ⟨s, hs, rfl⟩ := hzsample
  exact ⟨s, rfl⟩

theorem branchGenerator_novel_familyB {q : ℕ} {K : Set ℤ}
    (hK : K ∈ familyB q) {input : Stream ℤ}
    (hp : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q) :
    NovelGeneratesAfterInput input (outputAfterInput (branchGenerator q) input) K := by
  refine ⟨0, ?_⟩
  intro t ht
  have hmissing : ¬markerFinset q ⊆
      GenLimit.Generic.sequenceSample (fun i : Fin (t + 1) => input i) := by
    rw [sequenceSample_stream_prefix]
    exact familyB_markers_ne_sample hK hp (t + 1)
  obtain ⟨n, hout⟩ := branchOutput_negative_of_markers_missing q (t + 1)
    (fun i => input i) hmissing
  constructor
  · apply hK.1
    exact ⟨n, hout.symm⟩
  constructor
  · exact branchGenerator_sample_fresh q input t
  · intro s hst
    exact branchGenerator_norepeat q input hst

end Stage3Case019.Local
