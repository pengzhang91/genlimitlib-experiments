import Stage3Model
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import GenLimit.Paper39_DenseGeneration.Abstract.Density
import Mathlib.Data.Nat.Nth

namespace Stage3S2BProof

open Stage3S2B
open Filter
open scoped Topology

def oddCode (k : ℕ) : ℕ := 2 * k + 3

theorem oddCode_injective : Function.Injective oddCode := by
  intro a b h
  simp [oddCode] at h
  omega

theorem oddCode_not_core (k : ℕ) : oddCode k ∉ core := by
  rintro ⟨n, hn⟩
  cases n with
  | zero => simp [oddCode] at hn
  | succ n =>
      simp only [pow_succ] at hn
      have : 2 ∣ oddCode k := ⟨2 ^ n, by omega⟩
      simp [oddCode] at this

structure History (t : ℕ) where
  presentation : Fin t → ℕ
  query : Fin t → Option ℕ
  answer : Fin t → Option Bool
  output : Fin t → ℕ

def queryValues {t : ℕ} (h : History t) : Finset ℕ :=
  Finset.univ.biUnion fun i => (h.query i).toFinset

def forbidden {t : ℕ} (h : History t) : Finset ℕ :=
  (Finset.univ.image h.presentation ∪ queryValues h) ∪
    Finset.univ.image h.output

theorem card_queryValues_le {t : ℕ} (h : History t) :
    (queryValues h).card ≤ t := by
  classical
  unfold queryValues
  calc
    (Finset.univ.biUnion fun i => (h.query i).toFinset).card ≤
        ∑ i : Fin t, ((h.query i).toFinset).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin t, 1 := by
      apply Finset.sum_le_sum
      intro i _hi
      cases h.query i <;> simp
    _ = t := by simp

theorem card_forbidden_le {t : ℕ} (h : History t) :
    (forbidden h).card ≤ 3 * t := by
  classical
  unfold forbidden
  calc
    ((Finset.univ.image h.presentation ∪ queryValues h) ∪
        Finset.univ.image h.output).card ≤
        (Finset.univ.image h.presentation).card +
          (queryValues h).card + (Finset.univ.image h.output).card := by
            exact (Finset.card_union_le _ _).trans
              (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    _ ≤ t + t + t := by
      apply Nat.add_le_add
      · apply Nat.add_le_add
        · exact (Finset.card_image_le.trans_eq (Finset.card_univ.trans (Fintype.card_fin t)))
        · exact card_queryValues_le h
      · exact (Finset.card_image_le.trans_eq (Finset.card_univ.trans (Fintype.card_fin t)))
    _ = 3 * t := by omega

theorem exists_available (t : ℕ) (h : History t) :
    ∃ z ∈ (Finset.range (3 * t + 1)).image oddCode, z ∉ forbidden h := by
  classical
  apply Finset.exists_mem_notMem_of_card_lt_card
  have hforbid := card_forbidden_le h
  have hcodes : ((Finset.range (3 * t + 1)).image oddCode).card = 3 * t + 1 := by
    rw [Finset.card_image_of_injective _ oddCode_injective, Finset.card_range]
  omega

noncomputable def filler {t : ℕ} (h : History t) : ℕ :=
  Classical.choose (exists_available t h)

theorem filler_mem_codes {t : ℕ} (h : History t) :
    filler h ∈ (Finset.range (3 * t + 1)).image oddCode :=
  (Classical.choose_spec (exists_available t h)).1

theorem filler_not_forbidden {t : ℕ} (h : History t) :
    filler h ∉ forbidden h :=
  (Classical.choose_spec (exists_available t h)).2

theorem filler_bound {t : ℕ} (h : History t) : filler h < 6 * t + 5 := by
  obtain ⟨k, hk, hkEq⟩ := Finset.mem_image.mp (filler_mem_codes h)
  have hk' : k < 3 * t + 1 := Finset.mem_range.mp hk
  rw [← hkEq]
  simp only [oddCode]
  omega

theorem filler_not_core {t : ℕ} (h : History t) : filler h ∉ core := by
  obtain ⟨k, _hk, hkEq⟩ := Finset.mem_image.mp (filler_mem_codes h)
  rw [← hkEq]
  exact oddCode_not_core k

theorem filler_ne_presentation {t : ℕ} (h : History t) (i : Fin t) :
    filler h ≠ h.presentation i := by
  intro heq
  apply filler_not_forbidden h
  simp [forbidden, heq]

theorem filler_ne_query {t : ℕ} (h : History t) (i : Fin t) (z : ℕ)
    (hq : h.query i = some z) : filler h ≠ z := by
  intro heq
  apply filler_not_forbidden h
  exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr <| by
    unfold queryValues
    apply Finset.mem_biUnion.mpr
    exact ⟨i, Finset.mem_univ _, by simp [hq, heq]⟩)))

theorem filler_ne_output {t : ℕ} (h : History t) (i : Fin t) :
    filler h ≠ h.output i := by
  intro heq
  apply filler_not_forbidden h
  simp [forbidden, heq]

noncomputable def nextPresentation {t : ℕ} (h : History t) : ℕ :=
  if Even t then 2 ^ (t / 2) else filler h

noncomputable def extend (gen : FeedbackGenerator) {t : ℕ}
    (h : History t) : History (t + 1) := by
  let x := nextPresentation h
  let xp : Fin (t + 1) → ℕ := Fin.lastCases x h.presentation
  let q := gen.query t xp h.answer
  let qp : Fin (t + 1) → Option ℕ := Fin.lastCases q h.query
  let a : Option Bool := match q with
    | none => none
    | some z => some (membershipAnswer (core ∪ Set.range xp) z)
  let ap : Fin (t + 1) → Option Bool := Fin.lastCases a h.answer
  let y := gen.output t xp ap
  exact {
    presentation := xp
    query := qp
    answer := ap
    output := Fin.lastCases y h.output
  }

noncomputable def history (gen : FeedbackGenerator) : (t : ℕ) → History t
  | 0 => ⟨Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0⟩
  | t + 1 => extend gen (history gen t)

noncomputable def builtTranscript (gen : FeedbackGenerator) : Transcript where
  presentation t := (history gen (t + 1)).presentation (Fin.last t)
  query t := (history gen (t + 1)).query (Fin.last t)
  answer t := (history gen (t + 1)).answer (Fin.last t)
  output t := (history gen (t + 1)).output (Fin.last t)

noncomputable def builtTarget (gen : FeedbackGenerator) : Language :=
  core ∪ Set.range (builtTranscript gen).presentation

end Stage3S2BProof

namespace Stage3S2BProof

open Stage3S2B

@[simp] theorem history_succ (gen : FeedbackGenerator) (t : ℕ) :
    history gen (t + 1) = extend gen (history gen t) := rfl

@[simp] theorem extend_presentation_castSucc (gen : FeedbackGenerator) {t : ℕ}
    (h : History t) (i : Fin t) :
    (extend gen h).presentation i.castSucc = h.presentation i := by
  simp [extend]

@[simp] theorem extend_query_castSucc (gen : FeedbackGenerator) {t : ℕ}
    (h : History t) (i : Fin t) :
    (extend gen h).query i.castSucc = h.query i := by
  simp [extend]

@[simp] theorem extend_answer_castSucc (gen : FeedbackGenerator) {t : ℕ}
    (h : History t) (i : Fin t) :
    (extend gen h).answer i.castSucc = h.answer i := by
  simp [extend]

@[simp] theorem extend_output_castSucc (gen : FeedbackGenerator) {t : ℕ}
    (h : History t) (i : Fin t) :
    (extend gen h).output i.castSucc = h.output i := by
  simp [extend]

@[simp] theorem extend_presentation_last (gen : FeedbackGenerator) {t : ℕ}
    (h : History t) :
    (extend gen h).presentation (Fin.last t) = nextPresentation h := by
  simp [extend]

@[simp] theorem extend_query_last (gen : FeedbackGenerator) {t : ℕ}
    (h : History t) :
    (extend gen h).query (Fin.last t) =
      gen.query t (Fin.lastCases (nextPresentation h) h.presentation) h.answer := by
  simp [extend]

@[simp] theorem extend_answer_last (gen : FeedbackGenerator) {t : ℕ}
    (h : History t) :
    (extend gen h).answer (Fin.last t) =
      match gen.query t (Fin.lastCases (nextPresentation h) h.presentation) h.answer with
      | none => none
      | some z => some (membershipAnswer
          (core ∪ Set.range (Fin.lastCases (nextPresentation h) h.presentation)) z) := by
  simp [extend]

@[simp] theorem extend_output_last (gen : FeedbackGenerator) {t : ℕ}
    (h : History t) :
    (extend gen h).output (Fin.last t) =
      gen.output t (Fin.lastCases (nextPresentation h) h.presentation)
        (Fin.lastCases
          (match gen.query t (Fin.lastCases (nextPresentation h) h.presentation) h.answer with
            | none => none
            | some z => some (membershipAnswer
                (core ∪ Set.range (Fin.lastCases (nextPresentation h) h.presentation)) z))
          h.answer) := by
  simp [extend]

theorem transcript_history_prefix (gen : FeedbackGenerator) : ∀ t,
    (∀ i : Fin t, (builtTranscript gen).presentation i =
      (history gen t).presentation i) ∧
    (∀ i : Fin t, (builtTranscript gen).query i =
      (history gen t).query i) ∧
    (∀ i : Fin t, (builtTranscript gen).answer i =
      (history gen t).answer i) ∧
    (∀ i : Fin t, (builtTranscript gen).output i =
      (history gen t).output i) := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
      rcases ih with ⟨ihx, ihq, iha, ihy⟩
      constructor
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [builtTranscript]
        · simpa [history] using ihx j
      constructor
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [builtTranscript]
        · simpa [history] using ihq j
      constructor
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [builtTranscript]
        · simpa [history] using iha j
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [builtTranscript]
        · simpa [history] using ihy j

theorem transcript_presentation_eq (gen : FeedbackGenerator) (t : ℕ) :
    (builtTranscript gen).presentation t = nextPresentation (history gen t) := by
  simp [builtTranscript]

theorem transcript_query_eq (gen : FeedbackGenerator) (t : ℕ) :
    (builtTranscript gen).query t = gen.query t
      (fun i => (builtTranscript gen).presentation i)
      (fun i => (builtTranscript gen).answer i) := by
  rw [show (builtTranscript gen).query t =
      (history gen (t + 1)).query (Fin.last t) by rfl]
  simp only [history_succ, extend_query_last]
  congr 1
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [transcript_presentation_eq]
    · simpa using ((transcript_history_prefix gen t).1 j).symm
  · funext i
    exact (transcript_history_prefix gen t).2.2.1 i |>.symm

end Stage3S2BProof

namespace Stage3S2BProof

open Stage3S2B

lemma prefixPresentation_eq (gen : FeedbackGenerator) (t : ℕ) :
    (fun i : Fin (t + 1) => (builtTranscript gen).presentation i) =
      Fin.lastCases (nextPresentation (history gen t))
        (history gen t).presentation := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [transcript_presentation_eq]
  · simpa using (transcript_history_prefix gen t).1 j

lemma prefixAnswer_eq (gen : FeedbackGenerator) (t : ℕ) :
    (fun i : Fin t => (builtTranscript gen).answer i) =
      (history gen t).answer := by
  funext i
  exact (transcript_history_prefix gen t).2.2.1 i

lemma query_history_eq (gen : FeedbackGenerator) {t s : ℕ} (hts : t < s) :
    (history gen s).query ⟨t, hts⟩ = (builtTranscript gen).query t := by
  exact ((transcript_history_prefix gen s).2.1 ⟨t, hts⟩).symm

lemma presentation_of_even (gen : FeedbackGenerator) {t : ℕ} (ht : Even t) :
    (builtTranscript gen).presentation t = 2 ^ (t / 2) := by
  rw [transcript_presentation_eq]
  simp [nextPresentation, ht]

lemma presentation_of_odd (gen : FeedbackGenerator) {t : ℕ} (ht : ¬ Even t) :
    (builtTranscript gen).presentation t = filler (history gen t) := by
  rw [transcript_presentation_eq]
  simp [nextPresentation, ht]

lemma presentation_core_of_even (gen : FeedbackGenerator) {t : ℕ} (ht : Even t) :
    (builtTranscript gen).presentation t ∈ core := by
  rw [presentation_of_even gen ht]
  exact ⟨t / 2, rfl⟩

lemma presentation_not_core_of_odd (gen : FeedbackGenerator) {t : ℕ} (ht : ¬ Even t) :
    (builtTranscript gen).presentation t ∉ core := by
  rw [presentation_of_odd gen ht]
  exact filler_not_core _

lemma query_avoided_later (gen : FeedbackGenerator) {t s z : ℕ}
    (hts : t < s) (hq : (builtTranscript gen).query t = some z)
    (hz : z ∉ core) : (builtTranscript gen).presentation s ≠ z := by
  by_cases hs : Even s
  · intro heq
    apply hz
    rw [← heq]
    exact presentation_core_of_even gen hs
  · rw [presentation_of_odd gen hs]
    apply filler_ne_query
      (h := history gen s) (i := ⟨t, hts⟩) (z := z)
    rw [query_history_eq gen hts]
    exact hq

lemma query_mem_target_iff_prefix (gen : FeedbackGenerator) (t z : ℕ)
    (hq : (builtTranscript gen).query t = some z) :
    z ∈ builtTarget gen ↔
      z ∈ core ∪ Set.range (fun i : Fin (t + 1) =>
        (builtTranscript gen).presentation i) := by
  constructor
  · intro hz
    rcases hz with hzCore | ⟨s, hs⟩
    · exact Or.inl hzCore
    · by_cases hst : s ≤ t
      · exact Or.inr ⟨⟨s, Nat.lt_succ_iff.mpr hst⟩, hs⟩
      · have hts : t < s := Nat.lt_of_not_ge hst
        by_cases hzCore : z ∈ core
        · exact Or.inl hzCore
        · exact (query_avoided_later gen hts hq hzCore hs).elim
  · intro hz
    rcases hz with hzCore | ⟨i, hi⟩
    · exact Or.inl hzCore
    · exact Or.inr ⟨i, hi⟩

lemma transcript_answer_eq (gen : FeedbackGenerator) (t : ℕ) :
    (builtTranscript gen).answer t =
      match (builtTranscript gen).query t with
      | none => none
      | some z => some (membershipAnswer (builtTarget gen) z) := by
  rw [show (builtTranscript gen).answer t =
      (history gen (t + 1)).answer (Fin.last t) by rfl]
  simp only [history_succ, extend_answer_last]
  rw [← prefixPresentation_eq gen t, ← prefixAnswer_eq gen t,
    transcript_query_eq gen t]
  generalize hq0 : gen.query t
      (fun i => (builtTranscript gen).presentation i)
      (fun i => (builtTranscript gen).answer i) = q
  cases q with
  | none => rfl
  | some z =>
      have hq : (builtTranscript gen).query t = some z := by
        rw [transcript_query_eq gen t, hq0]
      simp only
      congr 1
      unfold membershipAnswer
      classical
      exact decide_eq_decide.mpr (query_mem_target_iff_prefix gen t z hq).symm

lemma construction_answer_eq (gen : FeedbackGenerator) (t : ℕ) :
    (match gen.query t
        (Fin.lastCases (nextPresentation (history gen t))
          (history gen t).presentation)
        (history gen t).answer with
      | none => none
      | some z => some (membershipAnswer
          (core ∪ Set.range (Fin.lastCases
            (nextPresentation (history gen t))
            (history gen t).presentation)) z)) =
      (builtTranscript gen).answer t := by
  exact (extend_answer_last gen (history gen t)).symm

lemma transcript_output_eq (gen : FeedbackGenerator) (t : ℕ) :
    (builtTranscript gen).output t = gen.output t
      (fun i => (builtTranscript gen).presentation i)
      (fun i => (builtTranscript gen).answer i) := by
  rw [show (builtTranscript gen).output t =
      (history gen (t + 1)).output (Fin.last t) by rfl]
  simp only [history_succ, extend_output_last]
  congr 1
  · exact (prefixPresentation_eq gen t).symm
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using construction_answer_eq gen t
    · simpa using ((transcript_history_prefix gen t).2.2.1 j).symm

lemma built_followsProtocol (gen : FeedbackGenerator) :
    FollowsProtocol gen (builtTarget gen) (builtTranscript gen) := by
  intro t
  exact ⟨transcript_query_eq gen t, transcript_answer_eq gen t,
    transcript_output_eq gen t⟩

end Stage3S2BProof

namespace Stage3S2BProof

open Stage3S2B

lemma presentation_injective (gen : FeedbackGenerator) :
    Function.Injective (builtTranscript gen).presentation := by
  have hne : ∀ {s t : ℕ}, s < t →
      (builtTranscript gen).presentation s ≠
        (builtTranscript gen).presentation t := by
    intro s t hlt hst
    by_cases hs : Even s
    · by_cases ht : Even t
      · rcases hs with ⟨a, rfl⟩
        rcases ht with ⟨b, rfl⟩
        have haDiv : (a + a) / 2 = a := by omega
        have hbDiv : (b + b) / 2 = b := by omega
        rw [presentation_of_even gen ⟨a, rfl⟩,
          presentation_of_even gen ⟨b, rfl⟩, haDiv, hbDiv] at hst
        have hab : a = b := Nat.pow_right_injective (by omega) hst
        omega
      · have hcore : (builtTranscript gen).presentation s ∈ core :=
          presentation_core_of_even gen hs
        have hnotcore : (builtTranscript gen).presentation t ∉ core :=
          presentation_not_core_of_odd gen ht
        exact hnotcore (hst ▸ hcore)
    · by_cases ht : Even t
      · have hnotcore : (builtTranscript gen).presentation s ∉ core :=
          presentation_not_core_of_odd gen hs
        have hcore : (builtTranscript gen).presentation t ∈ core :=
          presentation_core_of_even gen ht
        exact hnotcore (hst ▸ hcore)
      · have havoid := filler_ne_presentation (history gen t) ⟨s, hlt⟩
        rw [← (transcript_history_prefix gen t).1 ⟨s, hlt⟩,
          ← presentation_of_odd gen ht] at havoid
        exact havoid hst.symm
  intro s t hst
  rcases lt_trichotomy s t with hlt | rfl | hgt
  · exact (hne hlt hst).elim
  · rfl
  · exact (hne hgt hst.symm).elim

lemma built_clean (gen : FeedbackGenerator) :
    Clean (builtTranscript gen).presentation (builtTarget gen) := by
  intro t
  exact Or.inr ⟨t, rfl⟩

lemma core_presented (gen : FeedbackGenerator) (k : ℕ) :
    (builtTranscript gen).presentation (2 * k) = 2 ^ k := by
  rw [presentation_of_even gen (even_two_mul k)]
  simp

lemma built_complete (gen : FeedbackGenerator) :
    Complete (builtTranscript gen).presentation (builtTarget gen) := by
  intro z hz
  rcases hz with ⟨k, rfl⟩ | ⟨t, rfl⟩
  · exact ⟨2 * k, core_presented gen k⟩
  · exact ⟨t, rfl⟩

lemma built_targetClass (gen : FeedbackGenerator) :
    builtTarget gen ∈ targetClass := by
  refine ⟨Set.range (builtTranscript gen).presentation \ core, ?_, ?_⟩
  · intro z hz
    exact hz.2
  · change core ∪ Set.range (builtTranscript gen).presentation =
      core ∪ (Set.range (builtTranscript gen).presentation \ core)
    ext z
    simp only [Set.mem_union, Set.mem_range, Set.mem_diff]
    tauto

noncomputable def builtPresenter (gen : FeedbackGenerator) : CausalPresenter where
  next t _ _ _ _ := (builtTranscript gen).presentation t

lemma built_presentedBy (gen : FeedbackGenerator) :
    PresentedBy (builtPresenter gen) (builtTranscript gen) := by
  intro t
  rfl

lemma scored_subset_core (gen : FeedbackGenerator) :
    scored (builtTarget gen) (builtTranscript gen).presentation
      (builtTranscript gen).output ⊆ core := by
  intro z hz
  rcases hz with ⟨hzTarget, t, hout, hfresh⟩
  by_contra hzCore
  rcases hzTarget with hzCore' | ⟨s, hpres⟩
  · exact hzCore hzCore'
  · have hts : t < s := by
      by_contra hnot
      apply hfresh
      exact ⟨s, Nat.le_of_not_gt hnot, hpres⟩
    by_cases hs : Even s
    · apply hzCore
      rw [← hpres]
      exact presentation_core_of_even gen hs
    · have havoid := filler_ne_output (history gen s) ⟨t, hts⟩
      rw [← (transcript_history_prefix gen s).2.2.2 ⟨t, hts⟩,
        ← presentation_of_odd gen hs, hout, hpres] at havoid
      exact havoid rfl

end Stage3S2BProof

namespace Stage3S2BProof

open Stage3S2B
open GenLimit.KleinbergWei

lemma core_infinite : core.Infinite := by
  unfold core
  exact Set.infinite_range_of_injective (Nat.pow_right_injective (by omega))

lemma builtTarget_infinite (gen : FeedbackGenerator) : (builtTarget gen).Infinite := by
  exact core_infinite.mono (fun _ hz => Or.inl hz)

noncomputable def orderedTarget (gen : FeedbackGenerator) : Stage3S2B.OrderedLanguage where
  carrier := builtTarget gen
  enumeration := Nat.nth (fun z => z ∈ builtTarget gen)
  enumeration_injective := Nat.nth_injective (builtTarget_infinite gen)
  range_enumeration := Nat.range_nth_of_infinite (builtTarget_infinite gen)

lemma orderedTarget_strictMono (gen : FeedbackGenerator) :
    StrictMono (orderedTarget gen).enumeration :=
  Nat.nth_strictMono (builtTarget_infinite gen)

lemma filler_round_bound (gen : FeedbackGenerator) (j : ℕ) :
    (builtTranscript gen).presentation (2 * j + 1) < 12 * j + 11 := by
  have hodd : ¬ Even (2 * j + 1) := by
    rintro ⟨k, hk⟩
    omega
  rw [presentation_of_odd gen hodd]
  have hbound := filler_bound (history gen (2 * j + 1))
  omega

lemma target_nth_bound (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).enumeration n < 12 * n + 11 := by
  classical
  change Nat.nth (fun z => z ∈ builtTarget gen) n < 12 * n + 11
  apply Nat.nth_lt_of_lt_count
  rw [Nat.count_eq_card_filter_range]
  let values : Finset ℕ :=
    (Finset.range (n + 1)).image
      (fun j => (builtTranscript gen).presentation (2 * j + 1))
  have hinj : Function.Injective
      (fun j => (builtTranscript gen).presentation (2 * j + 1)) := by
    intro a b hab
    have := presentation_injective gen hab
    omega
  have hcard : values.card = n + 1 := by
    simp [values, Finset.card_image_of_injective _ hinj]
  have hsubset : values ⊆
      (Finset.range (12 * n + 11)).filter
        (fun z => z ∈ builtTarget gen) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨j, hj, rfl⟩
    have hjlt : j < n + 1 := Finset.mem_range.mp hj
    have hjle : j ≤ n := by omega
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      have hb := filler_round_bound gen j
      omega
    · exact Or.inr ⟨2 * j + 1, rfl⟩
  have hle := Finset.card_le_card hsubset
  rw [hcard] at hle
  omega

end Stage3S2BProof

namespace Stage3S2BProof

open Stage3S2B
open Filter
open scoped Topology

lemma log2_linear_bound {n : ℕ} (hn : n ≠ 0) :
    Nat.log2 (12 * n + 11) ≤ Nat.log2 n + 5 := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  calc
    Nat.log 2 (12 * n + 11) ≤ Nat.log 2 (n * 2 * 2 * 2 * 2 * 2) := by
      apply Nat.log_mono_right
      omega
    _ = Nat.log 2 n + 5 := by
      simp [Nat.log_mul_base Nat.one_lt_two, hn]

lemma core_prefixCount_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).prefixCount core n ≤ 6 + Nat.log2 n := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [GenLimit.KleinbergWei.OrderedLanguage.prefixCount]
  let indices : Finset ℕ :=
    (Finset.range n).filter
      (fun i => (orderedTarget gen).enumeration i ∈ core)
  let values : Finset ℕ := indices.image (orderedTarget gen).enumeration
  let powers : Finset ℕ :=
    (Finset.range (Nat.log2 (12 * n + 11) + 1)).image (fun k => 2 ^ k)
  have hvaluesCard : values.card = indices.card := by
    exact Finset.card_image_of_injective _
      (orderedTarget gen).enumeration_injective
  have hpowersCard : powers.card = Nat.log2 (12 * n + 11) + 1 := by
    simpa [powers] using Finset.card_image_of_injective
      (Finset.range (Nat.log2 (12 * n + 11) + 1))
      (Nat.pow_right_injective (by omega))
  have hsubset : values ⊆ powers := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
    have hirange : i < n := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    rcases (Finset.mem_filter.mp hi).2 with ⟨k, hk⟩
    apply Finset.mem_image.mpr
    refine ⟨k, ?_, hk⟩
    apply Finset.mem_range.mpr
    have henumlt : (orderedTarget gen).enumeration i <
        (orderedTarget gen).enumeration n :=
      orderedTarget_strictMono gen hirange
    change 2 ^ k = (orderedTarget gen).enumeration i at hk
    have hambient : 2 ^ k < 12 * n + 11 := by
      rw [hk]
      exact henumlt.trans (target_nth_bound gen n)
    have hklog : k ≤ Nat.log2 (12 * n + 11) := by
      apply (Nat.le_log2 (by omega)).2
      exact hambient.le
    omega
  have hcard := Finset.card_le_card hsubset
  rw [hvaluesCard, hpowersCard] at hcard
  change indices.card ≤ 6 + Nat.log2 n
  exact hcard.trans (by
    have := log2_linear_bound hn
    omega)

lemma core_prefixRatio_tendsto_zero (gen : FeedbackGenerator) :
    Tendsto ((orderedTarget gen).prefixRatio core) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds (GenLimit.tendsto_countingError_div 6)
  · exact Eventually.of_forall fun n => (orderedTarget gen).prefixRatio_nonneg core n
  · exact Eventually.of_forall fun n => by
      by_cases hn : n = 0
      · simp [hn]
      · simp only [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, hn, if_false]
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
        exact_mod_cast core_prefixCount_le gen n

lemma core_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity core = 0 := by
  exact (core_prefixRatio_tendsto_zero gen).limsup_eq

lemma scored_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity
      (scored (builtTarget gen) (builtTranscript gen).presentation
        (builtTranscript gen).output) = 0 := by
  apply le_antisymm
  · calc
      (orderedTarget gen).upperDensity
          (scored (builtTarget gen) (builtTranscript gen).presentation
            (builtTranscript gen).output) ≤
          (orderedTarget gen).upperDensity core :=
        (orderedTarget gen).upperDensity_mono (scored_subset_core gen)
      _ = 0 := core_upperDensity_zero gen
  · exact (orderedTarget gen).upperDensity_nonneg _

end Stage3S2BProof

namespace Stage3S2BProof

open Stage3S2B

noncomputable def encodedTarget (S : Set ℕ) : Language :=
  core ∪ oddCode '' S

lemma oddCode_mem_encodedTarget (S : Set ℕ) (n : ℕ) :
    oddCode n ∈ encodedTarget S ↔ n ∈ S := by
  constructor
  · rintro (hcore | ⟨m, hm, hmn⟩)
    · exact (oddCode_not_core n hcore).elim
    · exact oddCode_injective hmn ▸ hm
  · intro hn
    exact Or.inr ⟨n, hn, rfl⟩

lemma encodedTarget_mem (S : Set ℕ) : encodedTarget S ∈ targetClass := by
  refine ⟨oddCode '' S, ?_, rfl⟩
  rintro z ⟨n, _hn, rfl⟩
  exact oddCode_not_core n

lemma encodedTarget_injective : Function.Injective encodedTarget := by
  intro S T hST
  ext n
  have hprobe := Set.ext_iff.mp hST (oddCode n)
  simpa only [oddCode_mem_encodedTarget] using hprobe

lemma targetClass_uncountable : ¬ targetClass.Countable := by
  intro hcountable
  let f : Set ℕ → targetClass := fun S => ⟨encodedTarget S, encodedTarget_mem S⟩
  have hf : Function.Injective f := by
    intro S T hST
    apply encodedTarget_injective
    exact congrArg Subtype.val hST
  letI : Countable targetClass := hcountable.to_subtype
  have hpower : Countable (Set ℕ) := hf.countable
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ hpower

lemma uniformly_generatable : UniformlyGeneratableWithoutSamples := by
  refine ⟨(fun k => 2 ^ k), Nat.pow_right_injective (by omega), 0, ?_⟩
  intro K hK t _ht
  rcases hK with ⟨A, _hA, rfl⟩
  exact Or.inl ⟨t, rfl⟩

lemma faithful_witness (gen : FeedbackGenerator) :
    FaithfulNegativeWitness gen (builtTarget gen) (builtPresenter gen)
      (builtTranscript gen) (orderedTarget gen) := by
  refine ⟨rfl, orderedTarget_strictMono gen, built_presentedBy gen,
    built_followsProtocol gen, built_clean gen, presentation_injective gen,
    built_complete gen, scored_upperDensity_zero gen⟩

lemma negative_claim : NegativeClaim := by
  intro gen _huniversal
  exact ⟨builtTarget gen, built_targetClass gen, builtPresenter gen,
    builtTranscript gen, orderedTarget gen, faithful_witness gen⟩

lemma main_claim : MainClaim :=
  ⟨targetClass_uncountable, uniformly_generatable, negative_claim⟩

end Stage3S2BProof
