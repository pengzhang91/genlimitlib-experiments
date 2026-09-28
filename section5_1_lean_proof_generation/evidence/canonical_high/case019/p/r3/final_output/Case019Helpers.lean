import Stage3Model
import Mathlib

open Set Filter
open scoped Topology

namespace Case019

abbrev Language (α : Type*) := Stage3Case019.Language α
abbrev Stream (α : Type*) := Stage3Case019.Stream α
abbrev Generator (α : Type*) := Stage3Case019.Generator α

 def markers (q : ℕ) : Set ℤ := {z | 0 ≤ z ∧ z ≤ (q : ℤ)}
 def negativeLine : Set ℤ := {z | z < 0}
 def nonnegativeLine : Set ℤ := {z | 0 ≤ z}
 def tail (j : ℕ) : Set ℤ := {z | (j : ℤ) ≤ z}

 def typeA (q : ℕ) (K : Set ℤ) : Prop :=
  markers q ⊆ K ∧ ∃ j : ℕ, tail j ⊆ K

 def typeB (q : ℕ) (K : Set ℤ) : Prop :=
  negativeLine ⊆ K ∧ Disjoint K (markers q)

 def separationFamily (q : ℕ) : Set (Set ℤ) :=
  {K | typeA q K ∨ typeB q K}

 def codedLanguage (q : ℕ) (S : Set ℕ) : Set ℤ :=
  markers q ∪ tail (q + 1) ∪ {z | ∃ n ∈ S, z = -((n : ℤ) + 1)}

 lemma codedLanguage_typeA (q : ℕ) (S : Set ℕ) :
    typeA q (codedLanguage q S) := by
  refine ⟨?_, q + 1, ?_⟩
  · intro z hz
    exact Or.inl (Or.inl hz)
  · intro z hz
    exact Or.inl (Or.inr hz)

 lemma codedLanguage_mem (q : ℕ) (S : Set ℕ) :
    codedLanguage q S ∈ separationFamily q :=
  Or.inl (codedLanguage_typeA q S)

 lemma neg_code_not_marker (q n : ℕ) :
    -((n : ℤ) + 1) ∉ markers q := by
  intro h
  have : (0 : ℤ) ≤ -((n : ℤ) + 1) := h.1
  omega

 lemma neg_code_not_tail (q n : ℕ) :
    -((n : ℤ) + 1) ∉ tail (q + 1) := by
  intro h
  dsimp [tail] at h
  omega

 lemma neg_code_mem_coded_iff (q : ℕ) (S : Set ℕ) (n : ℕ) :
    -((n : ℤ) + 1) ∈ codedLanguage q S ↔ n ∈ S := by
  constructor
  · intro h
    rcases h with h | h
    · rcases h with h | h
      · exact False.elim (neg_code_not_marker q n h)
      · exact False.elim (neg_code_not_tail q n h)
    · rcases h with ⟨m, hm, heq⟩
      have : m = n := by omega
      simpa [this] using hm
  · intro hn
    exact Or.inr ⟨n, hn, rfl⟩

 lemma codedLanguage_injective (q : ℕ) :
    Function.Injective (codedLanguage q) := by
  intro S T h
  ext n
  rw [← neg_code_mem_coded_iff q S n, ← neg_code_mem_coded_iff q T n, h]

 lemma powerset_nat_not_countable :
    ¬(Set.univ : Set (Set ℕ)).Countable := by
  intro h
  obtain ⟨f, hf⟩ := h.exists_surjective (Set.univ_nonempty : (Set.univ : Set (Set ℕ)).Nonempty)
  let diagonal : Set ℕ := {n | n ∉ (f n : Set ℕ)}
  obtain ⟨k, hk⟩ := hf ⟨diagonal, Set.mem_univ diagonal⟩
  have hk' : (f k : Set ℕ) = diagonal := congrArg Subtype.val hk
  have hiff : k ∈ diagonal ↔ k ∉ (f k : Set ℕ) := Iff.rfl
  by_cases hmem : k ∈ diagonal
  · exact (hiff.mp hmem) (by simpa [hk'] using hmem)
  · apply hmem
    apply hiff.mpr
    simpa [hk'] using hmem

 lemma separationFamily_uncountable (q : ℕ) :
    ¬(separationFamily q).Countable := by
  intro hcount
  have hpre : ((codedLanguage q) ⁻¹' separationFamily q).Countable :=
    hcount.preimage (codedLanguage_injective q)
  have huniv : (codedLanguage q) ⁻¹' separationFamily q = Set.univ := by
    ext S
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    exact codedLanguage_mem q S
  exact powerset_nat_not_countable (huniv ▸ hpre)

 lemma tail_infinite (j : ℕ) : (tail j).Infinite := by
  have hrange : Set.range (fun n : ℕ => ((j + n : ℕ) : ℤ)) ⊆ tail j := by
    rintro z ⟨n, rfl⟩
    dsimp [tail]
    omega
  exact (Set.infinite_range_of_injective (fun _ _ h => by omega)).mono hrange

 lemma negativeLine_infinite : negativeLine.Infinite := by
  have hrange : Set.range (fun n : ℕ => -((n : ℤ) + 1)) ⊆ negativeLine := by
    rintro z ⟨n, rfl⟩
    dsimp [negativeLine]
    omega
  exact (Set.infinite_range_of_injective (fun _ _ h => by omega)).mono hrange

 lemma separationFamily_infinite_languages (q : ℕ) :
    ∀ K ∈ separationFamily q, K.Infinite := by
  intro K hK
  rcases hK with hA | hB
  · obtain ⟨_, j, hj⟩ := hA
    exact (tail_infinite j).mono hj
  · exact negativeLine_infinite.mono hB.1

end Case019

namespace Case019

 def markerFinset (q : ℕ) : Finset ℤ :=
  (Finset.range (q + 1)).image Int.ofNat

 lemma coe_markerFinset (q : ℕ) : (markerFinset q : Set ℤ) = markers q := by
  ext z
  constructor
  · intro hz
    rcases Finset.mem_image.mp hz with ⟨n, hn, rfl⟩
    simp only [Finset.mem_range] at hn
    constructor
    · exact Int.ofNat_nonneg n
    · simpa using (show (n : ℤ) ≤ (q : ℤ) by
        exact_mod_cast (Nat.le_of_lt_succ hn))
  · intro hz
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz.1
    apply Finset.mem_image.mpr
    refine ⟨n, ?_, rfl⟩
    simp only [Finset.mem_range]
    exact Nat.lt_succ_iff.mpr (by exact_mod_cast hz.2)

 def halfValue (nonnegative : Bool) (n : ℕ) : ℤ :=
  if nonnegative then (n : ℤ) else -((n : ℤ) + 1)

 lemma halfValue_injective (side : Bool) : Function.Injective (halfValue side) := by
  intro m n h
  unfold halfValue at h
  split at h <;> omega

 lemma halfValue_mem (side : Bool) (n : ℕ) :
    halfValue side n ∈ if side then nonnegativeLine else negativeLine := by
  cases side <;> simp [halfValue, nonnegativeLine, negativeLine]
  omega

 noncomputable def pickFresh (side : Bool) (banned : Finset ℤ) : ℤ := by
  let blocked : Finset ℕ := banned.preimage (halfValue side) (halfValue_injective side).injOn
  let n := Nat.find (Finset.exists_not_mem blocked)
  exact halfValue side n

 lemma pickFresh_not_mem (side : Bool) (banned : Finset ℤ) :
    pickFresh side banned ∉ banned := by
  unfold pickFresh
  dsimp only
  rw [← Finset.mem_preimage]
  exact Nat.find_spec (Finset.exists_not_mem _)

 lemma pickFresh_mem (side : Bool) (banned : Finset ℤ) :
    pickFresh side banned ∈ if side then nonnegativeLine else negativeLine := by
  unfold pickFresh
  dsimp only
  exact halfValue_mem side _

 noncomputable def markerGenerator (q : ℕ) : Generator ℤ
  | 0, _ => 0
  | t + 1, xs =>
      let shown := GenLimit.Generic.sequenceSample xs
      let previous : Finset ℤ := Finset.univ.image (fun s : Fin t =>
        markerGenerator q (s + 1) (fun i : Fin (s + 1) =>
          xs (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt s.isLt)) i)))
      let side : Bool := decide (markerFinset q ⊆ shown)
      pickFresh side (shown ∪ previous)
termination_by t xs => t

 lemma markerGenerator_step (q t : ℕ) (xs : Fin (t + 1) → ℤ) :
    markerGenerator q (t + 1) xs =
      let shown := GenLimit.Generic.sequenceSample xs
      let previous : Finset ℤ := Finset.univ.image (fun s : Fin t =>
        markerGenerator q (s + 1) (fun i : Fin (s + 1) =>
          xs (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt s.isLt)) i)))
      let side : Bool := decide (markerFinset q ⊆ shown)
      pickFresh side (shown ∪ previous) := by
  rw [markerGenerator]

 lemma output_markerGenerator (q : ℕ) (input : Stream ℤ) (t : ℕ) :
    Stage3Case019.outputAfterInput (markerGenerator q) input t =
      markerGenerator q (t + 1) (fun i : Fin (t + 1) => input i) := rfl

 lemma sequenceSample_eq_sample (input : Stream ℤ) (t : ℕ) :
    GenLimit.Generic.sequenceSample (fun i : Fin t => input i) =
      GenLimit.Generic.sample input t := by
  ext z
  simp only [GenLimit.Generic.sequenceSample, GenLimit.Generic.sample,
    Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, i.isLt, hi⟩
  · rintro ⟨n, hn, heq⟩
    exact ⟨⟨n, hn⟩, heq⟩

 lemma markerGenerator_fresh_sample (q : ℕ) (input : Stream ℤ) (t : ℕ) :
    Stage3Case019.outputAfterInput (markerGenerator q) input t ∉
      GenLimit.Generic.sample input (t + 1) := by
  rw [output_markerGenerator, markerGenerator_step]
  let shown := GenLimit.Generic.sequenceSample (fun i : Fin (t + 1) => input i)
  let previous : Finset ℤ := Finset.univ.image (fun s : Fin t =>
    markerGenerator q (s + 1) (fun i : Fin (s + 1) =>
      input (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt s.isLt)) i)))
  let side : Bool := decide (markerFinset q ⊆ shown)
  change pickFresh side (shown ∪ previous) ∉ GenLimit.Generic.sample input (t + 1)
  intro hmem
  apply pickFresh_not_mem side (shown ∪ previous)
  apply Finset.mem_union.mpr
  left
  simpa [shown, sequenceSample_eq_sample] using hmem

 lemma markerGenerator_novel (q : ℕ) (input : Stream ℤ) (s t : ℕ) (hst : s < t) :
    Stage3Case019.outputAfterInput (markerGenerator q) input s ≠
      Stage3Case019.outputAfterInput (markerGenerator q) input t := by
  intro heq
  rw [output_markerGenerator q input t, markerGenerator_step] at heq
  let shown := GenLimit.Generic.sequenceSample (fun i : Fin (t + 1) => input i)
  let previous : Finset ℤ := Finset.univ.image (fun r : Fin t =>
    markerGenerator q (r + 1) (fun i : Fin (r + 1) =>
      input (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt r.isLt)) i)))
  let side : Bool := decide (markerFinset q ⊆ shown)
  change Stage3Case019.outputAfterInput (markerGenerator q) input s =
    pickFresh side (shown ∪ previous) at heq
  have hmem : Stage3Case019.outputAfterInput (markerGenerator q) input s ∈ previous := by
    apply Finset.mem_image.mpr
    refine ⟨⟨s, hst⟩, Finset.mem_univ _, ?_⟩
    rfl
  apply pickFresh_not_mem side (shown ∪ previous)
  apply Finset.mem_union.mpr
  right
  rwa [← heq]

 lemma markerGenerator_half_mem (q : ℕ) (input : Stream ℤ) (t : ℕ) :
    let shown := GenLimit.Generic.sample input (t + 1)
    Stage3Case019.outputAfterInput (markerGenerator q) input t ∈
      if markerFinset q ⊆ shown then nonnegativeLine else negativeLine := by
  rw [output_markerGenerator, markerGenerator_step]
  let shown := GenLimit.Generic.sequenceSample (fun i : Fin (t + 1) => input i)
  let previous : Finset ℤ := Finset.univ.image (fun s : Fin t =>
    markerGenerator q (s + 1) (fun i : Fin (s + 1) =>
      input (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt s.isLt)) i)))
  let side : Bool := decide (markerFinset q ⊆ shown)
  change pickFresh side (shown ∪ previous) ∈
    if markerFinset q ⊆ GenLimit.Generic.sample input (t + 1) then
      nonnegativeLine else negativeLine
  have hs : shown = GenLimit.Generic.sample input (t + 1) := by
    simpa [shown] using sequenceSample_eq_sample input (t + 1)
  rw [← hs]
  simpa [side] using pickFresh_mem side (shown ∪ previous)

end Case019

namespace Case019

 lemma markerFinset_card (q : ℕ) : (markerFinset q).card = q + 1 := by
  rw [markerFinset, Finset.card_image_of_injective _]
  · exact Finset.card_range (q + 1)
  · exact fun _ _ h => Int.ofNat.inj h

 lemma markerFinset_mem_markers {q : ℕ} {z : ℤ} (hz : z ∈ markerFinset q) :
    z ∈ markers q := by
  rw [← coe_markerFinset q]
  exact hz

 lemma sample_mono (input : Stream ℤ) : Monotone (GenLimit.Generic.sample input) := by
  classical
  intro s t hst
  intro z hz
  simp only [GenLimit.Generic.sample, Finset.mem_image, Finset.mem_range] at hz ⊢
  rcases hz with ⟨n, hn, rfl⟩
  exact ⟨n, lt_of_lt_of_le hn hst, rfl⟩

 lemma mem_sample_of_lt (input : Stream ℤ) {n t : ℕ} (h : n < t) :
    input n ∈ GenLimit.Generic.sample input t := by
  classical
  simp only [GenLimit.Generic.sample, Finset.mem_image, Finset.mem_range]
  exact ⟨n, h, rfl⟩

 lemma output_injective (q : ℕ) (input : Stream ℤ) :
    Function.Injective (Stage3Case019.outputAfterInput (markerGenerator q) input) := by
  intro s t heq
  rcases lt_trichotomy s t with h | h | h
  · exact False.elim (markerGenerator_novel q input s t h heq)
  · exact h
  · exact False.elim (markerGenerator_novel q input t s h heq.symm)

 lemma typeB_never_markers
    (q : ℕ) (K : Set ℤ) (input : Stream ℤ)
    (hB : typeB q K)
    (hp : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q) :
    ∀ t, ¬ markerFinset q ⊆ GenLimit.Generic.sample input (t + 1) := by
  intro t hmarkers
  rcases hp.2.2 with ⟨F, hF, hcard⟩
  have hsub : markerFinset q ⊆ F := by
    intro z hz
    have hzsample := hmarkers hz
    have hzrange : z ∈ Set.range input := by
      classical
      simp only [GenLimit.Generic.sample, Finset.mem_image, Finset.mem_range] at hzsample
      rcases hzsample with ⟨n, hn, rfl⟩
      exact ⟨n, rfl⟩
    have hzmarker : z ∈ markers q := markerFinset_mem_markers hz
    have hznotK : z ∉ K := by
      intro hzK
      exact Set.disjoint_left.1 hB.2 hzK hzmarker
    have : z ∈ Set.range input \ K := ⟨hzrange, hznotK⟩
    simpa [← hF] using this
  have := Finset.card_le_card hsub
  rw [markerFinset_card] at this
  omega

 lemma markers_eventually_shown
    (q : ℕ) (K : Set ℤ) (input : Stream ℤ)
    (hmarkersK : markers q ⊆ K)
    (hcover : K ⊆ Set.range input) :
    ∃ T, markerFinset q ⊆ GenLimit.Generic.sample input T := by
  let when : (z : ↥(markerFinset q)) → ℕ := fun z =>
    Classical.choose (hcover (hmarkersK (markerFinset_mem_markers z.property)))
  have hwhen (z : ↥(markerFinset q)) : input (when z) = z :=
    Classical.choose_spec (hcover (hmarkersK (markerFinset_mem_markers z.property)))
  let times : Finset ℕ := Finset.univ.image when
  obtain ⟨T, hT⟩ := Finset.exists_nat_subset_range times
  refine ⟨T, ?_⟩
  intro z hz
  let zz : ↥(markerFinset q) := ⟨z, hz⟩
  have htime : when zz < T := by
    apply Finset.mem_range.mp
    apply hT
    exact Finset.mem_image.mpr ⟨zz, Finset.mem_univ _, rfl⟩
  change (zz : ℤ) ∈ GenLimit.Generic.sample input T
  rw [← hwhen zz]
  exact mem_sample_of_lt input htime

 lemma typeA_bad_finite (q : ℕ) (K : Set ℤ) (hA : typeA q K) :
    (nonnegativeLine \ K).Finite := by
  obtain ⟨_, j, hj⟩ := hA
  apply (Set.finite_Ico (0 : ℤ) (j : ℤ)).subset
  intro z hz
  refine ⟨hz.1, ?_⟩
  by_contra hnot
  have hjz : (j : ℤ) ≤ z := le_of_not_gt hnot
  exact hz.2 (hj hjz)

 lemma markerGenerator_eventually_valid
    (q : ℕ) (K : Set ℤ) (input : Stream ℤ)
    (hK : K ∈ separationFamily q)
    (hp : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q) :
    ∃ T, ∀ t, T ≤ t →
      Stage3Case019.outputAfterInput (markerGenerator q) input t ∈ K := by
  rcases hK with hA | hB
  · obtain ⟨Tmark, hTmark⟩ := markers_eventually_shown q K input hA.1 hp.2.1
    let out := Stage3Case019.outputAfterInput (markerGenerator q) input
    let bad := nonnegativeLine \ K
    have hbad : bad.Finite := typeA_bad_finite q K hA
    have hpre : (out ⁻¹' bad).Finite :=
      hbad.preimage (output_injective q input).injOn
    obtain ⟨M, hM⟩ := hpre.exists_le
    refine ⟨max Tmark (M + 1), ?_⟩
    intro t ht
    have htmark : Tmark ≤ t + 1 := by omega
    have hshown : markerFinset q ⊆ GenLimit.Generic.sample input (t + 1) :=
      hTmark.trans ((sample_mono input) htmark)
    have houtnonneg : out t ∈ nonnegativeLine := by
      have := markerGenerator_half_mem q input t
      dsimp only at this
      simp [hshown] at this
      exact this
    by_contra houtK
    have htbad : t ∈ out ⁻¹' bad := ⟨houtnonneg, houtK⟩
    have := hM t htbad
    omega
  · refine ⟨0, ?_⟩
    intro t _
    have hnot := typeB_never_markers q K input hB hp t
    have houtneg := markerGenerator_half_mem q input t
    dsimp only at houtneg
    simp [hnot] at houtneg
    exact hB.1 houtneg

 lemma markerGenerator_novel_limit
    (q : ℕ) (K : Set ℤ) (input : Stream ℤ)
    (hK : K ∈ separationFamily q)
    (hp : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q) :
    Stage3Case019.NovelGeneratesAfterInput input
      (Stage3Case019.outputAfterInput (markerGenerator q) input) K := by
  obtain ⟨T, hvalid⟩ := markerGenerator_eventually_valid q K input hK hp
  refine ⟨T, ?_⟩
  intro t ht
  refine ⟨hvalid t ht, markerGenerator_fresh_sample q input t, ?_⟩
  intro s hst
  exact markerGenerator_novel q input s t hst

end Case019


namespace Case019

open GenLimit.PatientScope

lemma prefixCount_mono (S : Set ℕ) : Monotone (prefixCount S) := by
  intro n m hnm
  apply Finset.card_le_card
  intro x hx
  simp only [prefixCount, prefixFinset, Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨lt_of_lt_of_le hx.1 hnm, hx.2⟩

lemma prefixCount_tendsto_atTop {S : Set ℕ} (hS : S.Infinite) :
    Tendsto (prefixCount S) atTop atTop := by
  rw [tendsto_atTop]
  intro c
  obtain ⟨s, hsS, hscard⟩ := hS.exists_subset_card_eq c
  obtain ⟨n, hsn⟩ := Finset.exists_nat_subset_range s
  filter_upwards [eventually_ge_atTop n] with m hnm
  rw [← hscard]
  apply Finset.card_le_card
  intro x hx
  simp only [prefixCount, prefixFinset, Finset.mem_filter, Finset.mem_range]
  exact ⟨lt_of_lt_of_le (Finset.mem_range.mp (hsn hx)) hnm, hsS hx⟩

lemma relativeLowerDensity_ge_of_linear_prefix_bound
    {A K : Set ℕ} (hK : K.Infinite) (hAK : A ⊆ K) (d C : ℕ) (hd : 0 < d)
    (hbound : ∀ n, prefixCount K n ≤ d * prefixCount A n + C) :
    (1 / (d : ℝ)) ≤ relativeLowerDensity A K := by
  unfold relativeLowerDensity
  let ratio : ℕ → ℝ := fun n =>
    (prefixCount A n : ℝ) / (prefixCount K n : ℝ)
  have hratio_nonneg : ∀ n, 0 ≤ ratio n := fun n =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hratio_le : ∀ n, ratio n ≤ 1 := by
    intro n
    by_cases hk : prefixCount K n = 0
    · simp [ratio, hk]
    · apply (div_le_one (by positivity)).2
      exact_mod_cast (Finset.card_le_card (fun x hx => by
        simp only [prefixCount, prefixFinset, Finset.mem_filter, Finset.mem_range] at hx ⊢
        exact ⟨hx.1, hAK hx.2⟩))
  have hcob : IsCoboundedUnder (fun x y : ℝ => x ≥ y) atTop ratio :=
    isCoboundedUnder_ge_of_le atTop hratio_le
  have hbdd : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop ratio := by
    change ∃ b : ℝ, ∀ᶠ n : ℕ in atTop, ratio n ≥ b
    exact ⟨0, Filter.Eventually.of_forall hratio_nonneg⟩
  apply (le_liminf_iff' hcob hbdd).2
  intro y hy
  have hgap : 0 < (1 / (d : ℝ)) - y := sub_pos.mpr hy
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have ht := (prefixCount_tendsto_atTop hK).eventually_ge_atTop
    (Nat.ceil ((C : ℝ) / ((d : ℝ) * ((1 / (d : ℝ)) - y))) + 1)
  filter_upwards [ht] with n hn
  have hkNat : 0 < prefixCount K n := by
    have : 0 < Nat.ceil ((C : ℝ) / ((d : ℝ) * ((1 / (d : ℝ)) - y))) + 1 := Nat.zero_lt_succ _
    omega
  have hkR : 0 < (prefixCount K n : ℝ) := by exact_mod_cast hkNat
  have hceil :
      (C : ℝ) / ((d : ℝ) * ((1 / (d : ℝ)) - y)) <
        (prefixCount K n : ℝ) := by
    have hleceil : (C : ℝ) / ((d : ℝ) * ((1 / (d : ℝ)) - y)) ≤
        Nat.ceil ((C : ℝ) / ((d : ℝ) * ((1 / (d : ℝ)) - y))) := Nat.le_ceil _
    have hceilNat : Nat.ceil ((C : ℝ) / ((d : ℝ) * ((1 / (d : ℝ)) - y))) + 1 ≤
        prefixCount K n := hn
    exact lt_of_le_of_lt hleceil (by exact_mod_cast (Nat.lt_of_succ_le hceilNat))
  have hden : 0 < (d : ℝ) * ((1 / (d : ℝ)) - y) := mul_pos hdR hgap
  have hC : (C : ℝ) <
      ((d : ℝ) * ((1 / (d : ℝ)) - y)) * (prefixCount K n : ℝ) := by
    rw [div_lt_iff₀ hden] at hceil
    nlinarith
  have hbR : (prefixCount K n : ℝ) ≤
      (d : ℝ) * (prefixCount A n : ℝ) + (C : ℝ) := by exact_mod_cast hbound n
  change y ≤ ratio n
  rw [le_div_iff₀ hkR]
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdR
  have hdinv : (d : ℝ) * (1 / (d : ℝ)) = 1 := by field_simp
  have hC' : (C : ℝ) < (1 - (d : ℝ) * y) * (prefixCount K n : ℝ) := by
    calc
      (C : ℝ) < ((d : ℝ) * ((1 / (d : ℝ)) - y)) * (prefixCount K n : ℝ) := hC
      _ = (1 - (d : ℝ) * y) * (prefixCount K n : ℝ) := by rw [mul_sub, hdinv]
  nlinarith

end Case019


namespace Case019

lemma balanced_surjective : Function.Surjective Stage3Case019.balanced := by
  intro z
  cases z with
  | ofNat n =>
      cases n with
      | zero => exact ⟨0, rfl⟩
      | succ n =>
          refine ⟨2 * (n + 1), ?_⟩
          rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
          simp only [Stage3Case019.balanced]
          split
          · rename_i h
            have : (2 * n + 1) % 2 = 1 := by omega
            omega
          · have hdiv : (2 * n + 1) / 2 = n := by omega
            rw [hdiv]
  | negSucc n =>
      refine ⟨2 * n + 1, ?_⟩
      simp only [Stage3Case019.balanced]
      split
      · have hdiv : (2 * n) / 2 = n := by omega
        rw [hdiv, Int.negSucc_eq]
        simp
      · rename_i h
        have : (2 * n) % 2 = 0 := by omega
        omega

lemma balancedRanks_infinite {K : Set ℤ} (hK : K.Infinite) :
    (Stage3Case019.balancedRanks K).Infinite := by
  intro hfinite
  have himage : (Stage3Case019.balanced '' Stage3Case019.balancedRanks K).Finite :=
    hfinite.image _
  have heq : Stage3Case019.balanced '' Stage3Case019.balancedRanks K = K := by
    apply Set.Subset.antisymm
    · rintro z ⟨n, hn, rfl⟩
      exact hn
    · intro z hz
      obtain ⟨n, rfl⟩ := balanced_surjective z
      exact ⟨n, hz, rfl⟩
  exact hK (heq ▸ himage)

lemma balanced_density_quarter_of_prefix_bound
    {A K : Set ℤ} (hK : K.Infinite) (hAK : A ⊆ K) (C : ℕ)
    (hbound : ∀ n,
      GenLimit.PatientScope.prefixCount (Stage3Case019.balancedRanks K) n ≤
        4 * GenLimit.PatientScope.prefixCount (Stage3Case019.balancedRanks A) n + C) :
    (1 / 4 : ℝ) ≤ Stage3Case019.balancedRelativeLowerDensity A K := by
  apply relativeLowerDensity_ge_of_linear_prefix_bound
    (balancedRanks_infinite hK) _ 4 C (by omega) hbound
  intro n hn
  exact hAK hn

end Case019


namespace Case019

open GenLimit.PatientScope

lemma prefixFinset_mono_set {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    prefixFinset A n ⊆ prefixFinset B n := by
  intro x hx
  simp only [prefixFinset, Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨hx.1, hAB hx.2⟩

lemma prefixCount_union_le (A B : Set ℕ) (n : ℕ) :
    prefixCount (A ∪ B) n ≤ prefixCount A n + prefixCount B n := by
  classical
  unfold prefixCount
  have hsub : prefixFinset (A ∪ B) n ⊆ prefixFinset A n ∪ prefixFinset B n := by
    intro x hx
    simp only [prefixFinset, Finset.mem_filter, Finset.mem_range, Finset.mem_union] at hx ⊢
    rcases hx.2 with hA | hB
    · exact Or.inl ⟨hx.1, hA⟩
    · exact Or.inr ⟨hx.1, hB⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le (prefixFinset A n) (prefixFinset B n))

lemma prefixCount_finite_union_bound (A : Set ℕ) (E : Finset ℕ) (n : ℕ) :
    prefixCount (A ∪ (E : Set ℕ)) n ≤ prefixCount A n + E.card := by
  refine (prefixCount_union_le A E n).trans ?_
  exact Nat.add_le_add_left (Finset.card_le_card (by
    intro x hx
    simp only [prefixFinset, Finset.mem_filter] at hx
    exact hx.2)) _

lemma prefixCount_partner_bound
    {T A D : Set ℕ} (E : Finset ℕ) (partner : ℕ → ℕ)
    (hcover : T ⊆ A ∪ D)
    (hpartner : ∀ x, x ∈ A \ (E : Set ℕ) → partner x ∈ D ∧ partner x < x)
    (hinj : Set.InjOn partner (A \ (E : Set ℕ))) :
    ∀ n, prefixCount T n ≤ 2 * prefixCount D n + E.card := by
  intro n
  have hT : prefixCount T n ≤ prefixCount (A ∪ D) n :=
    Finset.card_le_card (prefixFinset_mono_set hcover n)
  have hAD := prefixCount_union_le A D n
  have hAcover : A ⊆ (A \ (E : Set ℕ)) ∪ (E : Set ℕ) := by
    intro x hx
    by_cases hE : x ∈ E
    · exact Or.inr hE
    · exact Or.inl ⟨hx, hE⟩
  have hA : prefixCount A n ≤ prefixCount (A \ (E : Set ℕ)) n + E.card :=
    (Finset.card_le_card (prefixFinset_mono_set hAcover n)).trans
      (prefixCount_finite_union_bound (A \ (E : Set ℕ)) E n)
  have hordinary : prefixCount (A \ (E : Set ℕ)) n ≤ prefixCount D n := by
    classical
    unfold prefixCount
    let source := prefixFinset (A \ (E : Set ℕ)) n
    let target := prefixFinset D n
    have hmap : source.image partner ⊆ target := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
      have hxmem : x < n ∧ x ∈ A ∧ x ∉ E := by
        simpa [source, prefixFinset] using hx
      have hx' : x ∈ A \ (E : Set ℕ) := ⟨hxmem.2.1, hxmem.2.2⟩
      have hp := hpartner x hx'
      have hxn : x < n := hxmem.1
      simp only [target, prefixFinset, Finset.mem_filter, Finset.mem_range]
      exact ⟨hp.2.trans hxn, hp.1⟩
    calc
      source.card = (source.image partner).card := by
        symm
        apply Finset.card_image_iff.mpr
        intro x hx y hy hxy
        apply hinj
        · have hxmem : x < n ∧ x ∈ A ∧ x ∉ E := by
            simpa [source, prefixFinset] using hx
          exact ⟨hxmem.2.1, hxmem.2.2⟩
        · have hymem : y < n ∧ y ∈ A ∧ y ∉ E := by
            simpa [source, prefixFinset] using hy
          exact ⟨hymem.2.1, hymem.2.2⟩
        · exact hxy
      _ ≤ target.card := Finset.card_le_card hmap
  omega

end Case019
