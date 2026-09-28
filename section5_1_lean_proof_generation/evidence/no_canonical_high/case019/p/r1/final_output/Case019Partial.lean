import Stage3Model
import Mathlib.Data.Int.Interval

open Set
open Stage3Case019

namespace Case019Partial

noncomputable def markers (q : ℕ) : Finset ℤ :=
  (Finset.range (q + 1)).image (fun n : ℕ => (n : ℤ))

def positiveRay : Set ℤ := Set.Ioi 0

def negativeRay : Set ℤ := Set.Iio 0

def positiveSide (q : ℕ) (K : Set ℤ) : Prop :=
  (markers q : Set ℤ) ⊆ K ∧ positiveRay ⊆ K

def negativeSide (q : ℕ) (K : Set ℤ) : Prop :=
  Disjoint (markers q : Set ℤ) K ∧ negativeRay ⊆ K

def separationFamily (q : ℕ) : LanguageClass ℤ :=
  {K | positiveSide q K ∨ negativeSide q K}

@[simp] theorem mem_markers {q : ℕ} {z : ℤ} :
    z ∈ markers q ↔ ∃ n < q + 1, (n : ℤ) = z := by
  simp [markers]

@[simp] theorem natCast_mem_markers {q n : ℕ} :
    (n : ℤ) ∈ markers q ↔ n < q + 1 := by
  simp [mem_markers]

@[simp] theorem card_markers (q : ℕ) : (markers q).card = q + 1 := by
  rw [markers]
  calc
    (Finset.image (fun n : ℕ => (n : ℤ)) (Finset.range (q + 1))).card =
        (Finset.range (q + 1)).card := Finset.card_image_iff.mpr (by
          intro a ha b hb hab
          exact Int.ofNat_injective hab)
    _ = q + 1 := Finset.card_range _

def encodeNegative (q : ℕ) (A : Set ℕ) : Set ℤ :=
  negativeRay ∪ {z | ∃ n ∈ A, z = (q + 1 + n : ℕ)}

theorem encodeNegative_negativeSide (q : ℕ) (A : Set ℕ) :
    negativeSide q (encodeNegative q A) := by
  constructor
  · rw [Set.disjoint_left]
    intro z hz henc
    rcases (mem_markers.mp hz) with ⟨n, hn, rfl⟩
    rcases henc with hneg | ⟨m, hm, heq⟩
    · exact (show ¬(0 : ℤ) > (n : ℤ) by omega) hneg
    · have : n = q + 1 + m := by exact_mod_cast heq
      omega
  · exact fun z hz => Or.inl hz

theorem encodeNegative_injective (q : ℕ) : Function.Injective (encodeNegative q) := by
  intro A B hAB
  ext n
  have hnonneg : ¬((q + 1 + n : ℕ) : ℤ) < 0 := by omega
  constructor <;> intro hn
  · have hmem : ((q + 1 + n : ℕ) : ℤ) ∈ encodeNegative q A :=
      Or.inr ⟨n, hn, rfl⟩
    rw [hAB] at hmem
    rcases hmem with hneg | ⟨m, hm, heq⟩
    · exact False.elim (hnonneg hneg)
    · have hnat : q + 1 + n = q + 1 + m := by exact_mod_cast heq
      have : n = m := Nat.add_left_cancel hnat
      simpa [this] using hm
  · have hmem : ((q + 1 + n : ℕ) : ℤ) ∈ encodeNegative q B :=
      Or.inr ⟨n, hn, rfl⟩
    rw [← hAB] at hmem
    rcases hmem with hneg | ⟨m, hm, heq⟩
    · exact False.elim (hnonneg hneg)
    · have hnat : q + 1 + n = q + 1 + m := by exact_mod_cast heq
      have : n = m := Nat.add_left_cancel hnat
      simpa [this] using hm

theorem separationFamily_uncountable (q : ℕ) :
    ¬(separationFamily q).Countable := by
  intro hcount
  have hrange : (Set.range (encodeNegative q)).Countable :=
    hcount.mono fun K hK => by
      rcases hK with ⟨A, rfl⟩
      exact Or.inr (encodeNegative_negativeSide q A)
  have hpre := hrange.preimage (encodeNegative_injective q)
  have huniv : (Set.univ : Set (Set ℕ)).Countable := by
    simpa using hpre
  have hnonempty : (Set.univ : Set (Set ℕ)).Nonempty := ⟨∅, trivial⟩
  rcases huniv.exists_surjective hnonempty with ⟨f, hf⟩
  let diagonal : Set ℕ := {n | n ∉ (f n : Set ℕ)}
  rcases hf ⟨diagonal, trivial⟩ with ⟨k, hk⟩
  have hk' : (f k : Set ℕ) = diagonal := congrArg Subtype.val hk
  have hdiag : k ∈ diagonal ↔ k ∉ diagonal := by
    change (k ∉ (f k : Set ℕ)) ↔ k ∉ diagonal
    rw [hk']
  by_cases hmem : k ∈ diagonal
  · exact (hdiag.mp hmem) hmem
  · exact hmem (hdiag.mpr hmem)

theorem separationFamily_infinite (q : ℕ) :
    ∀ K ∈ separationFamily q, K.Infinite := by
  intro K hK
  rcases hK with hpos | hneg
  · exact (Set.Ioi_infinite (0 : ℤ)).mono hpos.2
  · exact (Set.Iio_infinite (0 : ℤ)).mono hneg.2

end Case019Partial

namespace Case019Partial

noncomputable def priorOutputs (gen : Generator ℤ) {t : ℕ} (xs : Fin t → ℤ) : Finset ℤ :=
  Finset.univ.image fun s : Fin t => gen s (fun i => xs (Fin.castLE s.isLt.le i))

noncomputable def rayGenerator (q : ℕ) : Generator ℤ :=
  fun t xs =>
    let previous := Finset.univ.image fun s : Fin t =>
      rayGenerator q s (fun i => xs (Fin.castLE s.isLt.le i))
    let used := GenLimit.Generic.sequenceSample xs ∪ previous
    if markers q ⊆ GenLimit.Generic.sequenceSample xs then
      Classical.choose ((Set.Ioi_infinite (0 : ℤ)).exists_notMem_finset used)
    else
      Classical.choose ((Set.Iio_infinite (0 : ℤ)).exists_notMem_finset used)
termination_by t => t
decreasing_by exact s.isLt

end Case019Partial

namespace Case019Partial

private theorem rayGenerator_positive_aux (q t : ℕ) (xs : Fin t → ℤ)
    (hmode : markers q ⊆ GenLimit.Generic.sequenceSample xs) :
    0 < rayGenerator q t xs := by
  rw [rayGenerator.eq_1]
  simp only [hmode, ↓reduceIte]
  exact (Classical.choose_spec
    ((Set.Ioi_infinite (0 : ℤ)).exists_notMem_finset
      (GenLimit.Generic.sequenceSample xs ∪
        Finset.univ.image fun s : Fin t =>
          rayGenerator q s (fun i => xs (Fin.castLE s.isLt.le i))))).1

private theorem rayGenerator_negative_aux (q t : ℕ) (xs : Fin t → ℤ)
    (hmode : ¬markers q ⊆ GenLimit.Generic.sequenceSample xs) :
    rayGenerator q t xs < 0 := by
  rw [rayGenerator.eq_1]
  simp only [hmode, ↓reduceIte]
  exact (Classical.choose_spec
    ((Set.Iio_infinite (0 : ℤ)).exists_notMem_finset
      (GenLimit.Generic.sequenceSample xs ∪
        Finset.univ.image fun s : Fin t =>
          rayGenerator q s (fun i => xs (Fin.castLE s.isLt.le i))))).1

theorem rayGenerator_positive (q t : ℕ) (xs : Fin t → ℤ)
    (hmode : markers q ⊆ GenLimit.Generic.sequenceSample xs) :
    rayGenerator q t xs ∈ positiveRay :=
  rayGenerator_positive_aux q t xs hmode

theorem rayGenerator_negative (q t : ℕ) (xs : Fin t → ℤ)
    (hmode : ¬markers q ⊆ GenLimit.Generic.sequenceSample xs) :
    rayGenerator q t xs ∈ negativeRay :=
  rayGenerator_negative_aux q t xs hmode

theorem rayGenerator_fresh (q t : ℕ) (xs : Fin t → ℤ) :
    rayGenerator q t xs ∉ GenLimit.Generic.sequenceSample xs ∪
      priorOutputs (rayGenerator q) xs := by
  rw [rayGenerator.eq_1]
  split_ifs with hmode
  · exact (Classical.choose_spec
      ((Set.Ioi_infinite (0 : ℤ)).exists_notMem_finset
        (GenLimit.Generic.sequenceSample xs ∪
          Finset.univ.image fun s : Fin t =>
            rayGenerator q s (fun i => xs (Fin.castLE s.isLt.le i))))).2
  · exact (Classical.choose_spec
      ((Set.Iio_infinite (0 : ℤ)).exists_notMem_finset
        (GenLimit.Generic.sequenceSample xs ∪
          Finset.univ.image fun s : Fin t =>
            rayGenerator q s (fun i => xs (Fin.castLE s.isLt.le i))))).2

end Case019Partial

namespace Case019Partial

@[simp] theorem sequenceSample_streamPrefix {α : Type*} [DecidableEq α]
    (input : Stream α) (t : ℕ) :
    GenLimit.Generic.sequenceSample (fun i : Fin t => input i) =
      GenLimit.Generic.sample input t := by
  ext x
  simp [GenLimit.Generic.sequenceSample, GenLimit.Generic.sample]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.isLt, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

theorem finset_eventually_subset_sample {α : Type*} [DecidableEq α]
    (F : Finset α) (input : Stream α) (hF : (F : Set α) ⊆ Set.range input) :
    ∃ T, F ⊆ GenLimit.Generic.sample input T := by
  let witness : F → ℕ := fun x => Classical.choose (hF x.property)
  have witness_spec : ∀ x : F, input (witness x) = x := by
    intro x
    exact Classical.choose_spec (hF x.property)
  rcases Finset.exists_nat_subset_range (F.attach.image witness) with ⟨T, hT⟩
  refine ⟨T, ?_⟩
  intro x hx
  rw [GenLimit.Generic.sample, @Finset.mem_image ℕ α (Classical.decEq α)]
  let xF : F := ⟨x, hx⟩
  refine ⟨witness xF, ?_, witness_spec xF⟩
  exact hT (Finset.mem_image.mpr ⟨xF, Finset.mem_attach _ _, rfl⟩)

theorem rayGenerator_sample_fresh (q : ℕ) (input : Stream ℤ) (t : ℕ) :
    outputAfterInput (rayGenerator q) input t ∉
      GenLimit.Generic.sample input (t + 1) := by
  have hfresh := rayGenerator_fresh q (t + 1) (fun i : Fin (t + 1) => input i)
  rw [sequenceSample_streamPrefix] at hfresh
  exact fun hmem => hfresh (Finset.mem_union_left _ hmem)

theorem rayGenerator_no_repeat (q : ℕ) (input : Stream ℤ) {s t : ℕ} (hst : s < t) :
    outputAfterInput (rayGenerator q) input s ≠
      outputAfterInput (rayGenerator q) input t := by
  intro heq
  have hfresh := rayGenerator_fresh q (t + 1) (fun i : Fin (t + 1) => input i)
  apply hfresh
  apply Finset.mem_union_right
  rw [priorOutputs, Finset.mem_image]
  let r : Fin (t + 1) := ⟨s + 1, by omega⟩
  refine ⟨r, Finset.mem_univ r, ?_⟩
  simpa [r, outputAfterInput, GenLimit.Generic.output] using heq

theorem positiveSide_eventual_mode (q : ℕ) {K : Set ℤ}
    (hK : positiveSide q K) (input : Stream ℤ)
    (hcover : K ⊆ Set.range input) :
    ∃ T, ∀ t, T ≤ t →
      markers q ⊆ GenLimit.Generic.sample input (t + 1) := by
  rcases finset_eventually_subset_sample (markers q) input
      (fun z hz => hcover (hK.1 hz)) with ⟨T, hT⟩
  refine ⟨T, fun t ht => ?_⟩
  exact hT.trans (by
    intro z hz
    rw [GenLimit.Generic.sample] at hz ⊢
    exact (@Finset.mem_image ℕ ℤ (Classical.decEq ℤ) _ _ _).mpr <| by
      rcases (@Finset.mem_image ℕ ℤ (Classical.decEq ℤ) _ _ _).mp hz with ⟨s, hs, rfl⟩
      exact ⟨s, by simp only [Finset.mem_range] at hs ⊢; omega, rfl⟩)

theorem negativeSide_never_mode (q : ℕ) {K : Set ℤ}
    (hK : negativeSide q K) (input : Stream ℤ)
    (hnoise : GenLimit.Generic.ValuesOutsideAtMost input K q) :
    ∀ t, ¬markers q ⊆ GenLimit.Generic.sample input (t + 1) := by
  rcases hnoise with ⟨F, hF, hcard⟩
  intro t hmode
  have hsub : markers q ⊆ F := by
    intro z hz
    have hzsample := hmode hz
    have hzrange : z ∈ Set.range input := by
      rw [GenLimit.Generic.sample, @Finset.mem_image ℕ ℤ (Classical.decEq ℤ)] at hzsample
      rcases hzsample with ⟨s, hs, rfl⟩
      exact ⟨s, rfl⟩
    have hznotK : z ∉ K := by
      exact Set.disjoint_left.mp hK.1 hz
    have : z ∈ Set.range input \ K := ⟨hzrange, hznotK⟩
    have hzF : z ∈ (F : Set ℤ) := by
      rw [hF]
      exact this
    exact hzF
  have hcards := Finset.card_le_card hsub
  rw [card_markers] at hcards
  omega

end Case019Partial

namespace Case019Partial

theorem separationFamily_has_novel_generator (q : ℕ) :
    ∃ gen : Generator ℤ,
      ∀ K ∈ separationFamily q, ∀ input : Stream ℤ,
        GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q →
          NovelGeneratesAfterInput input (outputAfterInput gen input) K := by
  refine ⟨rayGenerator q, ?_⟩
  intro K hfamily input hpresentation
  rcases hpresentation with ⟨hinjective, hcover, hnoise⟩
  rcases hfamily with hpositive | hnegative
  · rcases positiveSide_eventual_mode q hpositive input hcover with ⟨T, hT⟩
    refine ⟨T, fun t ht => ?_⟩
    have hmode := hT t ht
    have hmode' : markers q ⊆ GenLimit.Generic.sequenceSample
        (fun i : Fin (t + 1) => input i) := by simpa using hmode
    refine ⟨?_, rayGenerator_sample_fresh q input t, ?_⟩
    · apply hpositive.2
      exact rayGenerator_positive q (t + 1) (fun i : Fin (t + 1) => input i) hmode'
    · intro s hs
      exact rayGenerator_no_repeat q input hs
  · refine ⟨0, fun t ht => ?_⟩
    have hmode := negativeSide_never_mode q hnegative input hnoise t
    have hmode' : ¬markers q ⊆ GenLimit.Generic.sequenceSample
        (fun i : Fin (t + 1) => input i) := by simpa using hmode
    refine ⟨?_, rayGenerator_sample_fresh q input t, ?_⟩
    · apply hnegative.2
      exact rayGenerator_negative q (t + 1) (fun i : Fin (t + 1) => input i) hmode'
    · intro s hs
      exact rayGenerator_no_repeat q input hs

/-- Checked structural and eventual-novelty core of the separation construction.
The density estimate and adjacent-level impossibility are not asserted here. -/
theorem separationFamily_core (q : ℕ) :
    ¬(separationFamily q).Countable ∧
      (∀ K ∈ separationFamily q, K.Infinite) ∧
      (∃ gen : Generator ℤ,
        ∀ K ∈ separationFamily q, ∀ input : Stream ℤ,
          GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q →
            NovelGeneratesAfterInput input (outputAfterInput gen input) K) := by
  exact ⟨separationFamily_uncountable q, separationFamily_infinite q,
    separationFamily_has_novel_generator q⟩

end Case019Partial
