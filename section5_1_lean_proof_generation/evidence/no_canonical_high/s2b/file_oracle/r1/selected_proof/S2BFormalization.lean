import Stage3Model
import Mathlib.Data.Nat.Nth
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import GenLimit.Paper39_DenseGeneration.Abstract.Density

open Set Filter
open scoped Topology

namespace Stage3Proof

open Stage3S2B


lemma candidate_injective : Function.Injective (fun n : ℕ => 2 * n + 3) := by
  intro a b h
  simp only at h
  omega

lemma candidate_ordinary (n : ℕ) : 2 * n + 3 ∈ ordinary := by
  intro h
  rcases h with ⟨k, hk⟩
  cases k with
  | zero => simp at hk
  | succ k =>
      change 2 ^ (k + 1) = 2 * n + 3 at hk
      rw [Nat.pow_succ] at hk
      omega

def forbidden (t : ℕ) (xs ys : Fin t → ℕ) (qs : Fin t → Option ℕ) : Finset ℕ :=
  (Finset.univ.image xs) ∪ (Finset.univ.image ys) ∪
    (Finset.univ.image (fun i => (qs i).getD 0))

lemma forbidden_card_le (t : ℕ) (xs ys : Fin t → ℕ) (qs : Fin t → Option ℕ) :
    (forbidden t xs ys qs).card ≤ 3 * t := by
  have hx : (Finset.univ.image xs).card ≤ t := by
    simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin t))) (f := xs))
  have hy : (Finset.univ.image ys).card ≤ t := by
    simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin t))) (f := ys))
  have hq : (Finset.univ.image (fun i => (qs i).getD 0)).card ≤ t := by
    simpa using (Finset.card_image_le
      (s := (Finset.univ : Finset (Fin t))) (f := fun i => (qs i).getD 0))
  have hxy : (Finset.univ.image xs ∪ Finset.univ.image ys).card ≤ 2 * t := by
    exact (Finset.card_union_le _ _).trans (by omega)
  unfold forbidden
  exact (Finset.card_union_le _ _).trans (by omega)

lemma exists_candidate_not_forbidden
    (t : ℕ) (xs ys : Fin t → ℕ) (qs : Fin t → Option ℕ) :
    ∃ n, 2 * n + 3 ∉ forbidden t xs ys qs := by
  let s := forbidden t xs ys qs
  obtain ⟨z, hzrange, hz⟩ :=
    Set.infinite_range_of_injective candidate_injective |>.exists_not_mem_finset s
  rcases hzrange with ⟨n, rfl⟩
  exact ⟨n, hz⟩

noncomputable def chooseIndex
    (t : ℕ) (xs ys : Fin t → ℕ) (qs : Fin t → Option ℕ) : ℕ :=
  Nat.find (exists_candidate_not_forbidden t xs ys qs)

noncomputable def chooseValue
    (t : ℕ) (xs ys : Fin t → ℕ) (qs : Fin t → Option ℕ) : ℕ :=
  2 * chooseIndex t xs ys qs + 3

lemma chooseValue_not_forbidden
    (t : ℕ) (xs ys : Fin t → ℕ) (qs : Fin t → Option ℕ) :
    chooseValue t xs ys qs ∉ forbidden t xs ys qs := by
  exact Nat.find_spec (exists_candidate_not_forbidden t xs ys qs)

lemma chooseIndex_le
    (t : ℕ) (xs ys : Fin t → ℕ) (qs : Fin t → Option ℕ) :
    chooseIndex t xs ys qs ≤ 3 * t := by
  let candidates := (Finset.range (3 * t + 1)).image (fun n => 2 * n + 3)
  have hcandcard : candidates.card = 3 * t + 1 := by
    simp [candidates, Finset.card_image_iff.mpr candidate_injective.injOn]
  have hcard : (forbidden t xs ys qs).card < candidates.card := by
    rw [hcandcard]
    have := forbidden_card_le t xs ys qs
    omega
  obtain ⟨z, hzc, hzf⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [candidates, Finset.mem_image, Finset.mem_range] at hzc
  rcases hzc with ⟨n, hn, rfl⟩
  exact Nat.find_min' (exists_candidate_not_forbidden t xs ys qs) hzf |>.trans (Nat.le_of_lt_succ hn)

lemma chooseValue_le
    (t : ℕ) (xs ys : Fin t → ℕ) (qs : Fin t → Option ℕ) :
    chooseValue t xs ys qs ≤ 6 * t + 3 := by
  unfold chooseValue
  have := chooseIndex_le t xs ys qs
  omega

noncomputable def presentValue
    (t : ℕ) (xs ys : Fin t → ℕ) (qs : Fin t → Option ℕ) : ℕ :=
  if t % 2 = 0 then 2 ^ (t / 2) else chooseValue t xs ys qs

structure Round where
  presentation : ℕ
  query : Option ℕ
  answer : Option Bool
  output : ℕ

structure History (t : ℕ) where
  presentation : Fin t → ℕ
  query : Fin t → Option ℕ
  answer : Fin t → Option Bool
  output : Fin t → ℕ

noncomputable def onlineMembership {t : ℕ} (z x : ℕ) (xs : Fin t → ℕ) : Bool := by
  classical
  exact decide (z ∈ core ∨ z = x ∨ ∃ i, xs i = z)

noncomputable def makeRound (gen : FeedbackGenerator) {t : ℕ} (h : History t) : Round := by
  classical
  let x := presentValue t h.presentation h.output h.query
  let xall : Fin (t + 1) → ℕ := Fin.lastCases x h.presentation
  let q := gen.query t xall h.answer
  let a := match q with
    | none => none
    | some z => some (onlineMembership z x h.presentation)
  let aall : Fin (t + 1) → Option Bool := Fin.lastCases a h.answer
  let y := gen.output t xall aall
  exact ⟨x, q, a, y⟩

noncomputable def history (gen : FeedbackGenerator) : (t : ℕ) → History t
  | 0 => ⟨Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0⟩
  | t + 1 =>
      let h := history gen t
      let r := makeRound gen h
      ⟨Fin.lastCases r.presentation h.presentation,
       Fin.lastCases r.query h.query,
       Fin.lastCases r.answer h.answer,
       Fin.lastCases r.output h.output⟩

noncomputable def interactionRound (gen : FeedbackGenerator) (t : ℕ) : Round :=
  makeRound gen (history gen t)

noncomputable def adversarialTranscript (gen : FeedbackGenerator) : Transcript where
  presentation t := (interactionRound gen t).presentation
  query t := (interactionRound gen t).query
  answer t := (interactionRound gen t).answer
  output t := (interactionRound gen t).output

noncomputable def adversarialPresenter : CausalPresenter where
  next t xs qs _ ys := presentValue t xs ys qs

noncomputable def adversarialTarget (gen : FeedbackGenerator) : Language :=
  core ∪ Set.range (adversarialTranscript gen).presentation

lemma history_presentation (gen : FeedbackGenerator) {t : ℕ} (i : Fin t) :
    (history gen t).presentation i = (interactionRound gen i).presentation := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [history, interactionRound]
      · simp [history, ih]

lemma history_query (gen : FeedbackGenerator) {t : ℕ} (i : Fin t) :
    (history gen t).query i = (interactionRound gen i).query := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [history, interactionRound]
      · simp [history, ih]

lemma history_answer (gen : FeedbackGenerator) {t : ℕ} (i : Fin t) :
    (history gen t).answer i = (interactionRound gen i).answer := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [history, interactionRound]
      · simp [history, ih]

lemma history_output (gen : FeedbackGenerator) {t : ℕ} (i : Fin t) :
    (history gen t).output i = (interactionRound gen i).output := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [history, interactionRound]
      · simp [history, ih]

lemma interaction_presentation (gen : FeedbackGenerator) (t : ℕ) :
    (interactionRound gen t).presentation =
      presentValue t
        (fun i => (interactionRound gen i).presentation)
        (fun i => (interactionRound gen i).output)
        (fun i => (interactionRound gen i).query) := by
  change presentValue t (history gen t).presentation (history gen t).output
    (history gen t).query = _
  congr 1 <;> funext i
  · exact history_presentation gen i
  · exact history_output gen i
  · exact history_query gen i

lemma interaction_query (gen : FeedbackGenerator) (t : ℕ) :
    (interactionRound gen t).query = gen.query t
      (fun i => (adversarialTranscript gen).presentation i)
      (fun i => (adversarialTranscript gen).answer i) := by
  change gen.query t
    (Fin.lastCases (presentValue t (history gen t).presentation
      (history gen t).output (history gen t).query) (history gen t).presentation)
    (history gen t).answer = _
  congr 1
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.lastCases_last]
      rfl
    · rw [Fin.lastCases_castSucc]
      simpa [adversarialTranscript] using history_presentation gen j
  · funext i
    exact history_answer gen i

lemma interaction_answer (gen : FeedbackGenerator) (t : ℕ) :
    (interactionRound gen t).answer =
      match (interactionRound gen t).query with
      | none => none
      | some z => some (onlineMembership (t := t) z
          (interactionRound gen t).presentation
          (fun i : Fin t => (interactionRound gen i).presentation)) := by
  have hp : (history gen t).presentation =
      (fun i : Fin t => (interactionRound gen i).presentation) := by
    funext i
    exact history_presentation gen i
  change (match (interactionRound gen t).query with
    | none => none
    | some z => some (onlineMembership (t := t) z
        (interactionRound gen t).presentation (history gen t).presentation)) = _
  rw [hp]

lemma interaction_output (gen : FeedbackGenerator) (t : ℕ) :
    (interactionRound gen t).output = gen.output t
      (fun i => (adversarialTranscript gen).presentation i)
      (fun i => (adversarialTranscript gen).answer i) := by
  change gen.output t
    (Fin.lastCases (presentValue t (history gen t).presentation
      (history gen t).output (history gen t).query) (history gen t).presentation)
    (Fin.lastCases (interactionRound gen t).answer (history gen t).answer) = _
  congr 1
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.lastCases_last]
      rfl
    · rw [Fin.lastCases_castSucc]
      simpa [adversarialTranscript] using history_presentation gen j
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.lastCases_last]
      rfl
    · rw [Fin.lastCases_castSucc]
      simpa [adversarialTranscript] using history_answer gen j

lemma presentation_even (gen : FeedbackGenerator) (k : ℕ) :
    (adversarialTranscript gen).presentation (2 * k) = 2 ^ k := by
  rw [show (adversarialTranscript gen).presentation (2 * k) =
    presentValue (2 * k)
      (fun i => (interactionRound gen i).presentation)
      (fun i => (interactionRound gen i).output)
      (fun i => (interactionRound gen i).query) by
        exact interaction_presentation gen (2 * k)]
  simp [presentValue]

lemma presentation_odd (gen : FeedbackGenerator) (k : ℕ) :
    (adversarialTranscript gen).presentation (2 * k + 1) =
      chooseValue (2 * k + 1)
        (fun i => (interactionRound gen i).presentation)
        (fun i => (interactionRound gen i).output)
        (fun i => (interactionRound gen i).query) := by
  rw [show (adversarialTranscript gen).presentation (2 * k + 1) =
    presentValue (2 * k + 1)
      (fun i => (interactionRound gen i).presentation)
      (fun i => (interactionRound gen i).output)
      (fun i => (interactionRound gen i).query) by
        exact interaction_presentation gen (2 * k + 1)]
  simp [presentValue]

lemma presentation_odd_ordinary (gen : FeedbackGenerator) (k : ℕ) :
    (adversarialTranscript gen).presentation (2 * k + 1) ∈ ordinary := by
  rw [presentation_odd]
  exact candidate_ordinary _

lemma presentation_odd_le (gen : FeedbackGenerator) (k : ℕ) :
    (adversarialTranscript gen).presentation (2 * k + 1) ≤ 12 * k + 9 := by
  rw [presentation_odd]
  have := chooseValue_le (2 * k + 1)
    (fun i => (interactionRound gen i).presentation)
    (fun i => (interactionRound gen i).output)
    (fun i => (interactionRound gen i).query)
  omega

lemma odd_ne_prior_presentation (gen : FeedbackGenerator) (k : ℕ)
    (i : Fin (2 * k + 1)) :
    (adversarialTranscript gen).presentation (2 * k + 1) ≠
      (adversarialTranscript gen).presentation i := by
  rw [presentation_odd]
  have hnot := chooseValue_not_forbidden (2 * k + 1)
    (fun i => (interactionRound gen i).presentation)
    (fun i => (interactionRound gen i).output)
    (fun i => (interactionRound gen i).query)
  intro h
  apply hnot
  unfold forbidden
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  exact ⟨i, Finset.mem_univ _, h.symm⟩

lemma odd_ne_prior_output (gen : FeedbackGenerator) (k : ℕ)
    (i : Fin (2 * k + 1)) :
    (adversarialTranscript gen).presentation (2 * k + 1) ≠
      (adversarialTranscript gen).output i := by
  rw [presentation_odd]
  have hnot := chooseValue_not_forbidden (2 * k + 1)
    (fun i => (interactionRound gen i).presentation)
    (fun i => (interactionRound gen i).output)
    (fun i => (interactionRound gen i).query)
  intro h
  apply hnot
  unfold forbidden
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  exact ⟨i, Finset.mem_univ _, h.symm⟩

lemma odd_ne_prior_query (gen : FeedbackGenerator) (k : ℕ)
    (i : Fin (2 * k + 1)) (z : ℕ)
    (hq : (adversarialTranscript gen).query i = some z) :
    (adversarialTranscript gen).presentation (2 * k + 1) ≠ z := by
  rw [presentation_odd]
  have hnot := chooseValue_not_forbidden (2 * k + 1)
    (fun i => (interactionRound gen i).presentation)
    (fun i => (interactionRound gen i).output)
    (fun i => (interactionRound gen i).query)
  intro h
  apply hnot
  unfold forbidden
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  refine ⟨i, Finset.mem_univ _, ?_⟩
  simp [adversarialTranscript] at hq
  simpa [hq] using h.symm

lemma presentation_ne_of_lt (gen : FeedbackGenerator) {a b : ℕ} (hlt : a < b) :
    (adversarialTranscript gen).presentation a ≠
      (adversarialTranscript gen).presentation b := by
  by_cases hb : b % 2 = 0
  · by_cases ha : a % 2 = 0
    · have ea : a = 2 * (a / 2) := by omega
      have eb : b = 2 * (b / 2) := by omega
      rw [ea, eb, presentation_even, presentation_even]
      intro h
      have := Nat.pow_right_injective (a := 2) (by omega) h
      omega
    · have ea : a = 2 * (a / 2) + 1 := by omega
      have eb : b = 2 * (b / 2) := by omega
      rw [ea, eb, presentation_odd, presentation_even]
      intro h
      exact candidate_ordinary _ ⟨b / 2, h.symm⟩
  · have eb : b = 2 * (b / 2) + 1 := by omega
    intro h
    rw [eb] at h
    exact odd_ne_prior_presentation gen (b / 2) ⟨a, by omega⟩ h.symm

lemma presentation_injective (gen : FeedbackGenerator) :
    Function.Injective (adversarialTranscript gen).presentation := by
  intro a b h
  rcases lt_trichotomy a b with hab | hab | hab
  · exact False.elim (presentation_ne_of_lt gen hab h)
  · exact hab
  · exact False.elim (presentation_ne_of_lt gen hab h.symm)

lemma target_membership_at_query (gen : FeedbackGenerator) (t z : ℕ)
    (hq : (adversarialTranscript gen).query t = some z) :
    z ∈ adversarialTarget gen ↔
      z ∈ core ∨ z = (adversarialTranscript gen).presentation t ∨
        ∃ i : Fin t, (adversarialTranscript gen).presentation i = z := by
  constructor
  · intro hz
    rcases hz with hz | ⟨s, hs⟩
    · exact Or.inl hz
    · rcases lt_trichotomy s t with hst | hst | hst
      · exact Or.inr (Or.inr ⟨⟨s, hst⟩, hs⟩)
      · subst s
        exact Or.inr (Or.inl hs.symm)
      · by_cases he : s % 2 = 0
        · have es : s = 2 * (s / 2) := by omega
          rw [es, presentation_even] at hs
          exact Or.inl ⟨s / 2, hs⟩
        · have es : s = 2 * (s / 2) + 1 := by omega
          rw [es] at hst hs
          exfalso
          exact odd_ne_prior_query gen (s / 2) ⟨t, hst⟩ z hq hs
  · intro hz
    rcases hz with hz | hz | hz
    · exact Or.inl hz
    · exact Or.inr ⟨t, hz.symm⟩
    · rcases hz with ⟨i, hi⟩
      exact Or.inr ⟨i, hi⟩

lemma presented_by_adversary (gen : FeedbackGenerator) :
    PresentedBy adversarialPresenter (adversarialTranscript gen) := by
  intro t
  exact interaction_presentation gen t

lemma follows_protocol (gen : FeedbackGenerator) :
    FollowsProtocol gen (adversarialTarget gen) (adversarialTranscript gen) := by
  intro t
  refine ⟨interaction_query gen t, ?_, interaction_output gen t⟩
  rw [show (adversarialTranscript gen).answer t =
      (interactionRound gen t).answer by rfl]
  rw [interaction_answer]
  rw [show (adversarialTranscript gen).query t =
      (interactionRound gen t).query by rfl]
  cases hq : (interactionRound gen t).query with
  | none => simp [hq]
  | some z =>
      simp only [hq, membershipAnswer]
      unfold onlineMembership
      congr 2
      exact propext (target_membership_at_query gen t z
        (by simpa [adversarialTranscript] using hq)).symm

lemma target_in_class (gen : FeedbackGenerator) :
    adversarialTarget gen ∈ targetClass := by
  refine ⟨Set.range (adversarialTranscript gen).presentation \ core, ?_, ?_⟩
  · simpa [ordinary] using
      (Set.diff_subset_compl (Set.range (adversarialTranscript gen).presentation) core)
  · ext z
    constructor
    · intro hz
      rcases hz with hz | hz
      · exact Or.inl hz
      · by_cases hc : z ∈ core
        · exact Or.inl hc
        · exact Or.inr ⟨hz, hc⟩
    · intro hz
      rcases hz with hz | ⟨hz, _⟩
      · exact Or.inl hz
      · exact Or.inr hz

lemma presentation_clean (gen : FeedbackGenerator) :
    Clean (adversarialTranscript gen).presentation (adversarialTarget gen) := by
  intro t
  exact Or.inr ⟨t, rfl⟩

lemma presentation_complete (gen : FeedbackGenerator) :
    Complete (adversarialTranscript gen).presentation (adversarialTarget gen) := by
  intro z hz
  rcases hz with hz | hz
  · rcases hz with ⟨k, rfl⟩
    exact ⟨2 * k, presentation_even gen k⟩
  · exact hz


lemma scored_subset_core (gen : FeedbackGenerator) :
    scored (adversarialTarget gen) (adversarialTranscript gen).presentation
      (adversarialTranscript gen).output ⊆ core := by
  intro z hz
  by_contra hzcore
  have hzordinary : z ∈ ordinary := hzcore
  rcases hz.1 with hzcore' | ⟨s, hs⟩
  · exact hzcore hzcore'
  · by_cases heven : s % 2 = 0
    · have es : s = 2 * (s / 2) := by omega
      rw [es, presentation_even] at hs
      exact hzcore ⟨s / 2, hs⟩
    · have es : s = 2 * (s / 2) + 1 := by omega
      rcases hz.2 with ⟨t, hyt, hnot⟩
      have hst : t < s := by
        by_contra h
        apply hnot
        exact ⟨s, Nat.le_of_not_gt h, hs⟩
      rw [es] at hst hs
      exact odd_ne_prior_output gen (s / 2) ⟨t, hst⟩ (hs.trans hyt.symm)

lemma target_infinite (gen : FeedbackGenerator) : (adversarialTarget gen).Infinite := by
  apply (Set.infinite_range_of_injective
    (Nat.pow_right_injective (a := 2) (by omega))).mono
  intro z hz
  exact Or.inl hz

noncomputable def orderedTarget (gen : FeedbackGenerator) : OrderedLanguage where
  carrier := adversarialTarget gen
  enumeration := Nat.nth (fun z => z ∈ adversarialTarget gen)
  enumeration_injective := Nat.nth_injective (target_infinite gen)
  range_enumeration := Nat.range_nth_of_infinite (target_infinite gen)

lemma orderedTarget_inherits (gen : FeedbackGenerator) :
    InheritsAmbientOrder (orderedTarget gen) := by
  exact Nat.nth_strictMono (target_infinite gen)


lemma orderedTarget_enumeration_lt (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).enumeration n < 12 * n + 10 := by
  classical
  apply Nat.nth_lt_of_lt_count
  rw [Nat.count_eq_card_filter_range]
  let values := (Finset.range (n + 1)).image
    (fun k => (adversarialTranscript gen).presentation (2 * k + 1))
  have hcard : values.card = n + 1 := by
    unfold values
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro a _ b _ hab
      have h := presentation_injective gen hab
      omega
  have hsubset : values ⊆
      (Finset.range (12 * n + 10)).filter
        (fun z => z ∈ adversarialTarget gen) := by
    intro z hz
    simp only [values, Finset.mem_image, Finset.mem_range] at hz
    rcases hz with ⟨k, hk, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, Or.inr ⟨2 * k + 1, rfl⟩⟩
    have hk' : k ≤ n := by omega
    exact (presentation_odd_le gen k).trans_lt (by omega)
  have := Finset.card_le_card hsubset
  rw [hcard] at this
  omega

lemma orderedTarget_prefixCount_core_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).prefixCount core n ≤ Nat.log2 (12 * n + 10) + 1 := by
  classical
  let indices := (Finset.range n).filter
    (fun i => (orderedTarget gen).enumeration i ∈ core)
  let exponents := indices.image
    (fun i => Nat.log2 ((orderedTarget gen).enumeration i))
  have himage : exponents.card = indices.card := by
    unfold exponents
    rw [Finset.card_image_iff.mpr]
    intro i hi j hj hij
    change i ∈ (Finset.range n).filter
      (fun i => (orderedTarget gen).enumeration i ∈ core) at hi
    change j ∈ (Finset.range n).filter
      (fun i => (orderedTarget gen).enumeration i ∈ core) at hj
    have hi' := Finset.mem_filter.mp hi
    have hj' := Finset.mem_filter.mp hj
    rcases hi'.2 with ⟨a, ha⟩
    rcases hj'.2 with ⟨b, hb⟩
    change Nat.log2 ((orderedTarget gen).enumeration i) =
      Nat.log2 ((orderedTarget gen).enumeration j) at hij
    rw [← ha, ← hb, Nat.log2_two_pow, Nat.log2_two_pow] at hij
    apply (orderedTarget gen).enumeration_injective
    rw [← ha, ← hb, hij]
  have hsubset : exponents ⊆ Finset.range (Nat.log2 (12 * n + 10) + 1) := by
    intro a ha
    simp only [exponents, Finset.mem_image] at ha
    rcases ha with ⟨i, hi, rfl⟩
    change i ∈ (Finset.range n).filter
      (fun i => (orderedTarget gen).enumeration i ∈ core) at hi
    have hi' := Finset.mem_filter.mp hi
    simp only [Finset.mem_range] at hi'
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    apply Nat.log_mono_right
    have henum := orderedTarget_enumeration_lt gen i
    omega
  have hcard := Finset.card_le_card hsubset
  rw [himage] at hcard
  simpa [GenLimit.KleinbergWei.OrderedLanguage.prefixCount, indices] using hcard


lemma log2_linear_le (n : ℕ) (hn : 0 < n) :
    Nat.log2 (12 * n + 10) + 1 ≤ 6 + Nat.log2 n := by
  have hlinear : 12 * n + 10 ≤ 32 * n := by omega
  calc
    Nat.log2 (12 * n + 10) + 1 ≤ Nat.log2 (32 * n) + 1 := by
      exact Nat.add_le_add_right
        (by simpa [Nat.log2_eq_log_two] using Nat.log_mono_right hlinear) 1
    _ = Nat.log2 n + 6 := by
      rw [show 32 * n = (((((n * 2) * 2) * 2) * 2) * 2) by omega]
      simp [Nat.log2_eq_log_two, Nat.log_mul_base, hn.ne']
    _ = 6 + Nat.log2 n := by omega

lemma orderedTarget_core_density_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity core = 0 := by
  have hbound : ∀ n, (orderedTarget gen).prefixRatio core n ≤
      ((6 + Nat.log2 n : ℕ) : ℝ) / (n : ℝ) := by
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · simp only [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, hn, if_false]
      apply div_le_div_of_nonneg_right
      · exact_mod_cast (orderedTarget_prefixCount_core_le gen n).trans
          (log2_linear_le n (Nat.pos_of_ne_zero hn))
      · positivity
  have htendsto : Tendsto ((orderedTarget gen).prefixRatio core) atTop (nhds 0) := by
    apply squeeze_zero
      (fun n => (orderedTarget gen).prefixRatio_nonneg core n) hbound
    exact GenLimit.tendsto_countingError_div 6
  exact htendsto.limsup_eq

lemma orderedTarget_scored_density_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity
      (scored (adversarialTarget gen) (adversarialTranscript gen).presentation
        (adversarialTranscript gen).output) = 0 := by
  apply le_antisymm
  · calc
      (orderedTarget gen).upperDensity
          (scored (adversarialTarget gen) (adversarialTranscript gen).presentation
            (adversarialTranscript gen).output) ≤
          (orderedTarget gen).upperDensity core :=
        (orderedTarget gen).upperDensity_mono (scored_subset_core gen)
      _ = 0 := orderedTarget_core_density_zero gen
  · exact (orderedTarget gen).upperDensity_nonneg _


noncomputable def encodedTarget (A : Set ℕ) : Language :=
  core ∪ (fun n : ℕ => 2 * n + 3) '' A

lemma encodedTarget_mem_candidate (A : Set ℕ) (n : ℕ) :
    2 * n + 3 ∈ encodedTarget A ↔ n ∈ A := by
  constructor
  · intro h
    rcases h with hcore | himage
    · exact False.elim (candidate_ordinary n hcore)
    · rcases himage with ⟨m, hm, hmn⟩
      have : m = n := candidate_injective hmn
      simpa [this] using hm
  · intro hn
    exact Or.inr ⟨n, hn, rfl⟩

lemma encodedTarget_injective : Function.Injective encodedTarget := by
  intro A B hAB
  ext n
  rw [← encodedTarget_mem_candidate A n, hAB, encodedTarget_mem_candidate B n]

lemma encodedTarget_in_class (A : Set ℕ) : encodedTarget A ∈ targetClass := by
  refine ⟨(fun n : ℕ => 2 * n + 3) '' A, ?_, rfl⟩
  intro z hz
  rcases hz with ⟨n, _, rfl⟩
  exact candidate_ordinary n

lemma targetClass_not_countable : ¬ targetClass.Countable := by
  intro hcount
  have hpre := hcount.preimage encodedTarget_injective
  have hall : encodedTarget ⁻¹' targetClass = (Set.univ : Set (Set ℕ)) := by
    apply Set.preimage_eq_univ_iff.mpr
    intro K hK
    rcases hK with ⟨A, rfl⟩
    exact encodedTarget_in_class A
  rw [hall, Set.countable_univ_iff] at hpre
  exact (GenLimit.UnionClosedness.powerSet_not_countable ℕ) hpre

lemma uniformly_generatable : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun k : ℕ => 2 ^ k, Nat.pow_right_injective (a := 2) (by omega), 0, ?_⟩
  intro K hK t _
  rcases hK with ⟨A, hA, rfl⟩
  exact Or.inl ⟨t, rfl⟩

lemma negative_claim : NegativeClaim := by
  intro gen _
  refine ⟨adversarialTarget gen, target_in_class gen,
    adversarialPresenter, adversarialTranscript gen, orderedTarget gen, ?_⟩
  exact ⟨rfl, orderedTarget_inherits gen, presented_by_adversary gen,
    follows_protocol gen, presentation_clean gen, presentation_injective gen,
    presentation_complete gen, orderedTarget_scored_density_zero gen⟩

end Stage3Proof


theorem stage3_result : Stage3S2B.MainClaim := by
  exact ⟨Stage3Proof.targetClass_not_countable, Stage3Proof.uniformly_generatable,
    Stage3Proof.negative_claim⟩
