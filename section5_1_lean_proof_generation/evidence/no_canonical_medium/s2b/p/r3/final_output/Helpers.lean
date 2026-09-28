import Stage3Model
import Mathlib.Data.Nat.Nth
import Mathlib.Tactic

open Set Filter
open scoped Topology BigOperators

namespace Stage3Proof

open Stage3S2B

lemma pow_two_injective : Function.Injective (fun k : ℕ => 2 ^ k) := by
  intro a b h
  exact (Nat.pow_right_injective (by omega : 1 < 2)) h

noncomputable instance coreMembershipDecidable : DecidablePred (fun z => z ∈ core) :=
  fun z => Classical.propDecidable (z ∈ core)

abbrev extendFin {α : Type*} {t : ℕ} (f : Fin t → α) (a : α) : Fin (t + 1) → α :=
  Fin.lastCases a f

def forbidden (t : ℕ) (px : Fin t → ℕ) (pq : Fin t → Option ℕ)
    (py : Fin t → ℕ) : Finset ℕ :=
  Finset.univ.image px ∪ Finset.univ.image (fun i => (pq i).getD 0) ∪
    Finset.univ.image py

lemma exists_ordinary_not_forbidden (t : ℕ) (px : Fin t → ℕ)
    (pq : Fin t → Option ℕ) (py : Fin t → ℕ) :
    ∃ z, z ∈ Stage3S2B.ordinary ∧ z ∉ forbidden t px pq py := by
  obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range (forbidden t px pq py)
  refine ⟨2 * N + 3, ?_, ?_⟩
  · intro hcore
    rcases hcore with ⟨k, hk⟩
    cases k with
    | zero => simp at hk
    | succ k =>
        have heven : Even (2 ^ (k + 1)) := ⟨2 ^ k, by rw [pow_succ]; omega⟩
        have hodd : Odd (2 * N + 3) := ⟨N + 1, by omega⟩
        exact (Nat.not_even_iff_odd.mpr hodd) (hk ▸ heven)
  · intro hmem
    have := hN hmem
    simp only [Finset.mem_range] at this
    omega

noncomputable def freshOrdinary (t : ℕ) (px : Fin t → ℕ)
    (pq : Fin t → Option ℕ) (py : Fin t → ℕ) : ℕ := by
  classical
  exact Nat.find (exists_ordinary_not_forbidden t px pq py)

lemma freshOrdinary_mem (t : ℕ) (px : Fin t → ℕ)
    (pq : Fin t → Option ℕ) (py : Fin t → ℕ) :
    freshOrdinary t px pq py ∈ Stage3S2B.ordinary := by
  classical
  exact (Nat.find_spec (exists_ordinary_not_forbidden t px pq py)).1

lemma freshOrdinary_not_forbidden (t : ℕ) (px : Fin t → ℕ)
    (pq : Fin t → Option ℕ) (py : Fin t → ℕ) :
    freshOrdinary t px pq py ∉ forbidden t px pq py := by
  classical
  exact (Nat.find_spec (exists_ordinary_not_forbidden t px pq py)).2

noncomputable def diagonalPresenter : CausalPresenter where
  next t px pq _ py :=
    if h : Even t then 2 ^ (t / 2) else freshOrdinary t px pq py

structure InteractionState (t : ℕ) where
  presentation : Fin t → ℕ
  query : Fin t → Option ℕ
  answer : Fin t → Option Bool
  output : Fin t → ℕ

noncomputable def truth (P : Prop) : Bool := by
  classical
  exact decide P

structure Event where
  presentation : ℕ
  query : Option ℕ
  answer : Option Bool
  output : ℕ

noncomputable def nextEvent (gen : FeedbackGenerator) (t : ℕ)
    (s : InteractionState t) : Event := by
  classical
  let x := diagonalPresenter.next t s.presentation s.query s.answer s.output
  let px := extendFin s.presentation x
  let q := gen.query t px s.answer
  let a := q.map fun z => truth (z ∈ core ∨ ∃ i, px i = z)
  let ay := extendFin s.answer a
  let y := gen.output t px ay
  exact ⟨x, q, a, y⟩

noncomputable def InteractionState.extend {t : ℕ} (s : InteractionState t)
    (e : Event) : InteractionState (t + 1) where
  presentation := extendFin s.presentation e.presentation
  query := extendFin s.query e.query
  answer := extendFin s.answer e.answer
  output := extendFin s.output e.output

noncomputable def run (gen : FeedbackGenerator) : (t : ℕ) → InteractionState t
  | 0 => ⟨Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0⟩
  | t + 1 => (run gen t).extend (nextEvent gen t (run gen t))

noncomputable def eventAt (gen : FeedbackGenerator) (t : ℕ) : Event :=
  nextEvent gen t (run gen t)

noncomputable def interactionTranscript (gen : FeedbackGenerator) : Transcript where
  presentation t := (eventAt gen t).presentation
  query t := (eventAt gen t).query
  answer t := (eventAt gen t).answer
  output t := (eventAt gen t).output

@[simp] lemma run_succ_presentation (gen : FeedbackGenerator) (t : ℕ) :
    (run gen (t + 1)).presentation (Fin.last t) = (eventAt gen t).presentation := by
  simp [run, InteractionState.extend, eventAt, extendFin]

@[simp] lemma run_succ_query (gen : FeedbackGenerator) (t : ℕ) :
    (run gen (t + 1)).query (Fin.last t) = (eventAt gen t).query := by
  simp [run, InteractionState.extend, eventAt, extendFin]

@[simp] lemma run_succ_answer (gen : FeedbackGenerator) (t : ℕ) :
    (run gen (t + 1)).answer (Fin.last t) = (eventAt gen t).answer := by
  simp [run, InteractionState.extend, eventAt, extendFin]

@[simp] lemma run_succ_output (gen : FeedbackGenerator) (t : ℕ) :
    (run gen (t + 1)).output (Fin.last t) = (eventAt gen t).output := by
  simp [run, InteractionState.extend, eventAt, extendFin]

lemma run_history (gen : FeedbackGenerator) (t : ℕ) :
    (∀ i : Fin t, (run gen t).presentation i = (interactionTranscript gen).presentation i) ∧
    (∀ i : Fin t, (run gen t).query i = (interactionTranscript gen).query i) ∧
    (∀ i : Fin t, (run gen t).answer i = (interactionTranscript gen).answer i) ∧
    (∀ i : Fin t, (run gen t).output i = (interactionTranscript gen).output i) := by
  induction t with
  | zero => simp
  | succ t ih =>
      rcases ih with ⟨ihx, ihq, iha, ihy⟩
      constructor
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [interactionTranscript]
        · simp [run, InteractionState.extend, extendFin, ihx]
      constructor
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [interactionTranscript]
        · simp [run, InteractionState.extend, extendFin, ihq]
      constructor
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [interactionTranscript]
        · simp [run, InteractionState.extend, extendFin, iha]
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [interactionTranscript]
        · simp [run, InteractionState.extend, extendFin, ihy]

end Stage3Proof

namespace Stage3Proof

open Stage3S2B

lemma eventAt_presentation (gen : FeedbackGenerator) (t : ℕ) :
    (eventAt gen t).presentation = diagonalPresenter.next t
      (run gen t).presentation (run gen t).query (run gen t).answer (run gen t).output := by
  simp [eventAt, nextEvent]

lemma transcript_presented (gen : FeedbackGenerator) :
    PresentedBy diagonalPresenter (interactionTranscript gen) := by
  intro t
  rw [show (interactionTranscript gen).presentation t = (eventAt gen t).presentation by rfl]
  rw [eventAt_presentation]
  rcases run_history gen t with ⟨hx, hq, ha, hy⟩
  congr 1 <;> funext i
  · exact hx i
  · exact hq i
  · exact ha i
  · exact hy i

lemma presentation_even (gen : FeedbackGenerator) (k : ℕ) :
    (interactionTranscript gen).presentation (2 * k) = 2 ^ k := by
  rw [show (interactionTranscript gen).presentation (2 * k) =
    (eventAt gen (2 * k)).presentation by rfl, eventAt_presentation]
  simp [diagonalPresenter, Nat.even_iff]

lemma core_subset_target (gen : FeedbackGenerator) :
    core ⊆ Set.range (interactionTranscript gen).presentation := by
  rintro z ⟨k, rfl⟩
  exact ⟨2 * k, presentation_even gen k⟩

lemma presentation_odd_mem_ordinary (gen : FeedbackGenerator) {t : ℕ} (ht : ¬ Even t) :
    (interactionTranscript gen).presentation t ∈ ordinary := by
  rw [show (interactionTranscript gen).presentation t = (eventAt gen t).presentation by rfl,
    eventAt_presentation]
  simp [diagonalPresenter, ht, freshOrdinary_mem]

lemma presentation_odd_avoids (gen : FeedbackGenerator) {t : ℕ} (ht : ¬ Even t) :
    (interactionTranscript gen).presentation t ∉
      forbidden t (run gen t).presentation (run gen t).query (run gen t).output := by
  rw [show (interactionTranscript gen).presentation t = (eventAt gen t).presentation by rfl,
    eventAt_presentation]
  simp [diagonalPresenter, ht, freshOrdinary_not_forbidden]

lemma presentation_odd_ne_prior_presentation (gen : FeedbackGenerator) {t : ℕ}
    (ht : ¬ Even t) (i : Fin t) :
    (interactionTranscript gen).presentation t ≠ (interactionTranscript gen).presentation i := by
  intro heq
  have hav := presentation_odd_avoids gen ht
  apply hav
  unfold forbidden
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [Finset.mem_image]
  refine ⟨i, Finset.mem_univ _, ?_⟩
  rw [run_history gen t |>.1 i]
  exact heq.symm

lemma presentation_odd_ne_prior_query (gen : FeedbackGenerator) {t : ℕ}
    (ht : ¬ Even t) (i : Fin t) {z : ℕ}
    (hq : (interactionTranscript gen).query i = some z) :
    (interactionTranscript gen).presentation t ≠ z := by
  intro heq
  have hav := presentation_odd_avoids gen ht
  apply hav
  unfold forbidden
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  rw [Finset.mem_image]
  refine ⟨i, Finset.mem_univ _, ?_⟩
  rw [run_history gen t |>.2.1 i, hq]
  simp [heq]

lemma presentation_odd_ne_prior_output (gen : FeedbackGenerator) {t : ℕ}
    (ht : ¬ Even t) (i : Fin t) :
    (interactionTranscript gen).presentation t ≠ (interactionTranscript gen).output i := by
  intro heq
  have hav := presentation_odd_avoids gen ht
  apply hav
  unfold forbidden
  apply Finset.mem_union_right
  rw [Finset.mem_image]
  refine ⟨i, Finset.mem_univ _, ?_⟩
  rw [run_history gen t |>.2.2.2 i]
  exact heq.symm

lemma presentation_injective (gen : FeedbackGenerator) :
    Function.Injective (interactionTranscript gen).presentation := by
  intro s t hst
  rcases lt_trichotomy s t with hlt | heq | hgt
  · by_cases ht : Even t
    · obtain ⟨k, hk⟩ := ht
      subst t
      simp only [← two_mul] at hst hlt ⊢
      rw [presentation_even] at hst
      by_cases hs : Even s
      · obtain ⟨j, hj⟩ := hs
        subst s
        simp only [← two_mul] at hst hlt ⊢
        rw [presentation_even] at hst
        have := pow_two_injective hst
        omega
      · have hord := presentation_odd_mem_ordinary gen hs
        exact False.elim (hord (hst ▸ ⟨k, rfl⟩))
    · exact False.elim (presentation_odd_ne_prior_presentation gen ht ⟨s, hlt⟩ hst.symm)
  · exact heq
  · symm
    by_cases hs : Even s
    · obtain ⟨k, hk⟩ := hs
      subst s
      simp only [← two_mul] at hst hgt ⊢
      rw [presentation_even] at hst
      by_cases ht : Even t
      · obtain ⟨j, hj⟩ := ht
        subst t
        simp only [← two_mul] at hst hgt ⊢
        rw [presentation_even] at hst
        have := pow_two_injective hst
        omega
      · have hord := presentation_odd_mem_ordinary gen ht
        exact False.elim (hord (hst.symm ▸ ⟨k, rfl⟩))
    · exact False.elim (presentation_odd_ne_prior_presentation gen hs ⟨t, hgt⟩ hst)

lemma target_mem_class (gen : FeedbackGenerator) :
    Set.range (interactionTranscript gen).presentation ∈ targetClass := by
  refine ⟨Set.range (interactionTranscript gen).presentation \ core, ?_, ?_⟩
  · intro z hz
    exact hz.2
  · ext z
    constructor
    · intro hz
      by_cases hc : z ∈ core
      · exact Or.inl hc
      · exact Or.inr ⟨hz, hc⟩
    · rintro (hc | ⟨hz, -⟩)
      · exact core_subset_target gen hc
      · exact hz

lemma target_clean (gen : FeedbackGenerator) :
    Clean (interactionTranscript gen).presentation
      (Set.range (interactionTranscript gen).presentation) :=
  fun t => ⟨t, rfl⟩

lemma target_complete (gen : FeedbackGenerator) :
    Complete (interactionTranscript gen).presentation
      (Set.range (interactionTranscript gen).presentation) := by
  rintro z ⟨t, rfl⟩
  exact ⟨t, rfl⟩

end Stage3Proof

namespace Stage3Proof

open Stage3S2B

lemma eventAt_query (gen : FeedbackGenerator) (t : ℕ) :
    (eventAt gen t).query = gen.query t
      (extendFin (run gen t).presentation (eventAt gen t).presentation)
      (run gen t).answer := by
  simp [eventAt, nextEvent]

lemma eventAt_answer (gen : FeedbackGenerator) (t : ℕ) :
    (eventAt gen t).answer = (eventAt gen t).query.map fun z =>
      truth (z ∈ core ∨ ∃ i,
        extendFin (run gen t).presentation (eventAt gen t).presentation i = z) := by
  simp [eventAt, nextEvent]

lemma eventAt_output (gen : FeedbackGenerator) (t : ℕ) :
    (eventAt gen t).output = gen.output t
      (extendFin (run gen t).presentation (eventAt gen t).presentation)
      (extendFin (run gen t).answer (eventAt gen t).answer) := by
  simp [eventAt, nextEvent]

lemma extended_presentation_history (gen : FeedbackGenerator) (t : ℕ) :
    extendFin (run gen t).presentation (eventAt gen t).presentation =
      fun i : Fin (t + 1) => (interactionTranscript gen).presentation i := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [extendFin, interactionTranscript]
  · simp [extendFin, run_history gen t |>.1]

lemma extended_answer_history (gen : FeedbackGenerator) (t : ℕ) :
    extendFin (run gen t).answer (eventAt gen t).answer =
      fun i : Fin (t + 1) => (interactionTranscript gen).answer i := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [extendFin, interactionTranscript]
  · simp [extendFin, run_history gen t |>.2.2.1]

lemma queried_value_not_presented_later (gen : FeedbackGenerator) {t s z : ℕ}
    (hts : t < s) (hq : (interactionTranscript gen).query t = some z)
    (hz : z ∉ core) : (interactionTranscript gen).presentation s ≠ z := by
  by_cases hs : Even s
  · obtain ⟨k, hk⟩ := hs
    subst s
    simp only [← two_mul] at hts ⊢
    rw [presentation_even]
    exact fun heq => hz ⟨k, heq⟩
  · exact presentation_odd_ne_prior_query gen hs ⟨t, hts⟩ hq

lemma query_membership_characterization (gen : FeedbackGenerator) {t z : ℕ}
    (hq : (interactionTranscript gen).query t = some z) :
    z ∈ Set.range (interactionTranscript gen).presentation ↔
      z ∈ core ∨ z ∈ observedThrough (interactionTranscript gen).presentation t := by
  constructor
  · rintro ⟨s, hs⟩
    by_cases hz : z ∈ core
    · exact Or.inl hz
    · right
      by_contra hobs
      have hts : t < s := by
        by_contra hnlt
        have hle : s ≤ t := Nat.le_of_not_gt hnlt
        apply hobs
        exact ⟨s, hle, hs⟩
      exact queried_value_not_presented_later gen hts hq hz hs
  · rintro (hz | ⟨s, hst, hs⟩)
    · exact core_subset_target gen hz
    · exact ⟨s, hs⟩

lemma fin_history_iff_observed (gen : FeedbackGenerator) (t z : ℕ) :
    (∃ i : Fin (t + 1),
      (interactionTranscript gen).presentation i = z) ↔
      z ∈ observedThrough (interactionTranscript gen).presentation t := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, Nat.le_of_lt_succ i.isLt, hi⟩
  · rintro ⟨s, hst, hs⟩
    exact ⟨⟨s, Nat.lt_succ_of_le hst⟩, hs⟩

lemma interaction_follows_protocol (gen : FeedbackGenerator) :
    FollowsProtocol gen (Set.range (interactionTranscript gen).presentation)
      (interactionTranscript gen) := by
  intro t
  have hpx := extended_presentation_history gen t
  have hay := extended_answer_history gen t
  constructor
  · change (eventAt gen t).query = _
    rw [eventAt_query, hpx]
    congr 1
    funext i
    exact run_history gen t |>.2.2.1 i
  constructor
  · change (eventAt gen t).answer = _
    rw [eventAt_answer]
    cases hq : (eventAt gen t).query with
    | none => simp [interactionTranscript, hq]
    | some z =>
        simp only [Option.map_some]
        rw [show (interactionTranscript gen).query t = some z from hq]
        apply congrArg some
        unfold truth membershipAnswer
        rw [show (∃ i, extendFin (run gen t).presentation
          (eventAt gen t).presentation i = z) ↔
          z ∈ observedThrough (interactionTranscript gen).presentation t by
            rw [hpx, fin_history_iff_observed]]
        rw [← query_membership_characterization gen (show
          (interactionTranscript gen).query t = some z from hq)]
  · change (eventAt gen t).output = _
    rw [eventAt_output, hpx, hay]

end Stage3Proof

namespace Stage3Proof

open Stage3S2B

lemma odd_encoding_injective : Function.Injective (fun i : ℕ => 2 * i + 3) := by
  intro a b h
  apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2)
  exact Nat.add_right_cancel h

lemma exists_small_odd_not_mem (S : Finset ℕ) :
    ∃ i ≤ S.card, 2 * i + 3 ∉ S := by
  let A := (Finset.range (S.card + 1)).image (fun i : ℕ => 2 * i + 3)
  have hcardA : A.card = S.card + 1 := by
    dsimp [A]
    rw [Finset.card_image_iff.mpr]
    · simp
    · exact odd_encoding_injective.injOn
  have hlt : S.card < A.card := by omega
  obtain ⟨z, hzA, hzS⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  rcases Finset.mem_image.mp hzA with ⟨i, hi, rfl⟩
  exact ⟨i, Nat.lt_succ_iff.mp (by simpa using hi), hzS⟩

lemma forbidden_card_le (t : ℕ) (px : Fin t → ℕ) (pq : Fin t → Option ℕ)
    (py : Fin t → ℕ) : (forbidden t px pq py).card ≤ 3 * t := by
  let X := Finset.univ.image px
  let Q := Finset.univ.image (fun i => (pq i).getD 0)
  let Y := Finset.univ.image py
  have hx : X.card ≤ t := by
    dsimp [X]
    simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin t))) (f := px))
  have hq : Q.card ≤ t := by
    dsimp [Q]
    simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin t)))
      (f := fun i => (pq i).getD 0))
  have hy : Y.card ≤ t := by
    dsimp [Y]
    simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin t))) (f := py))
  have hxy := Finset.card_union_le X Q
  have hxyz := Finset.card_union_le (X ∪ Q) Y
  change ((X ∪ Q) ∪ Y).card ≤ 3 * t
  omega

lemma freshOrdinary_le (t : ℕ) (px : Fin t → ℕ)
    (pq : Fin t → Option ℕ) (py : Fin t → ℕ) :
    freshOrdinary t px pq py ≤ 6 * t + 3 := by
  classical
  let S := forbidden t px pq py
  obtain ⟨i, hi, hnot⟩ := exists_small_odd_not_mem S
  have hord : 2 * i + 3 ∈ ordinary := by
    intro hcore
    rcases hcore with ⟨k, hk⟩
    cases k with
    | zero => simp at hk
    | succ k =>
        have heven : Even (2 ^ (k + 1)) := ⟨2 ^ k, by rw [pow_succ]; omega⟩
        have hodd : Odd (2 * i + 3) := ⟨i + 1, by omega⟩
        exact (Nat.not_even_iff_odd.mpr hodd) (hk ▸ heven)
  have hfind : freshOrdinary t px pq py ≤ 2 * i + 3 := by
    unfold freshOrdinary
    apply Nat.find_min'
    exact ⟨hord, hnot⟩
  have hcard := forbidden_card_le t px pq py
  dsimp [S] at hi
  omega

lemma presentation_odd_le (gen : FeedbackGenerator) {t : ℕ} (ht : ¬ Even t) :
    (interactionTranscript gen).presentation t ≤ 6 * t + 3 := by
  rw [show (interactionTranscript gen).presentation t = (eventAt gen t).presentation by rfl,
    eventAt_presentation]
  simp [diagonalPresenter, ht, freshOrdinary_le]

lemma scored_subset_core (gen : FeedbackGenerator) :
    scored (Set.range (interactionTranscript gen).presentation)
      (interactionTranscript gen).presentation (interactionTranscript gen).output ⊆ core := by
  intro z hz
  rcases hz with ⟨⟨s, hs⟩, t, hyt, hobs⟩
  by_contra hzcore
  have hsodd : ¬ Even s := by
    intro hseven
    obtain ⟨k, hk⟩ := hseven
    subst s
    simp only [← two_mul] at hs
    rw [presentation_even] at hs
    exact hzcore ⟨k, hs⟩
  have hts : t < s := by
    by_contra hnlt
    apply hobs
    exact ⟨s, Nat.le_of_not_gt hnlt, hs⟩
  exact presentation_odd_ne_prior_output gen hsodd ⟨t, hts⟩ (hs.trans hyt.symm)

end Stage3Proof

namespace Stage3Proof

open Stage3S2B

noncomputable def realizedTarget (gen : FeedbackGenerator) : Language :=
  Set.range (interactionTranscript gen).presentation

noncomputable instance realizedTargetMembershipDecidable (gen : FeedbackGenerator) :
    DecidablePred (fun z => z ∈ realizedTarget gen) := fun z => Classical.propDecidable (z ∈ realizedTarget gen)

lemma realizedTarget_infinite (gen : FeedbackGenerator) : (realizedTarget gen).Infinite := by
  apply Set.infinite_of_injective_forall_mem pow_two_injective
  intro k
  exact core_subset_target gen ⟨k, rfl⟩

noncomputable def orderedTarget (gen : FeedbackGenerator) : OrderedLanguage where
  carrier := realizedTarget gen
  enumeration := Nat.nth (fun z => z ∈ realizedTarget gen)
  enumeration_injective := Nat.nth_injective (realizedTarget_infinite gen)
  range_enumeration := Nat.range_nth_of_infinite (realizedTarget_infinite gen)

lemma orderedTarget_strictMono (gen : FeedbackGenerator) :
    InheritsAmbientOrder (orderedTarget gen) :=
  Nat.nth_strictMono (realizedTarget_infinite gen)

noncomputable def filler (gen : FeedbackGenerator) (m : ℕ) : ℕ :=
  (interactionTranscript gen).presentation (2 * m + 1)

lemma filler_mem (gen : FeedbackGenerator) (m : ℕ) :
    filler gen m ∈ realizedTarget gen := ⟨2 * m + 1, rfl⟩

lemma filler_injective (gen : FeedbackGenerator) : Function.Injective (filler gen) := by
  intro a b h
  apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2)
  have := presentation_injective gen h
  omega

lemma filler_le (gen : FeedbackGenerator) (m : ℕ) : filler gen m ≤ 12 * m + 9 := by
  unfold filler
  have hodd : ¬ Even (2 * m + 1) := by simp [Nat.even_iff]
  have := presentation_odd_le gen hodd
  omega

lemma realizedTarget_count_gt (gen : FeedbackGenerator) (n : ℕ) :
    n < Nat.count (fun z => z ∈ realizedTarget gen) (12 * n + 10) := by
  rw [Nat.count_eq_card_filter_range]
  let A := (Finset.range (n + 1)).image (filler gen)
  have hcardA : A.card = n + 1 := by
    dsimp [A]
    rw [Finset.card_image_iff.mpr (filler_injective gen).injOn]
    simp
  have hsub : A ⊆ (Finset.range (12 * n + 10)).filter
      (fun z => z ∈ realizedTarget gen) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨m, hm, rfl⟩
    rw [Finset.mem_filter]
    constructor
    · simp only [Finset.mem_range] at hm ⊢
      have := filler_le gen m
      omega
    · exact filler_mem gen m
  have := Finset.card_le_card hsub
  omega

lemma orderedTarget_enumeration_lt (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).enumeration n < 12 * n + 10 := by
  exact Nat.nth_lt_of_lt_count (realizedTarget_count_gt gen n)

end Stage3Proof

namespace Stage3Proof

open Stage3S2B

noncomputable def coreExponent (gen : FeedbackGenerator) (n : ℕ)
    (i : {i // i ∈ (Finset.range n).filter
      (fun j => (orderedTarget gen).enumeration j ∈ core)}) : ℕ :=
  Classical.choose (Finset.mem_filter.mp i.property).2

lemma coreExponent_spec (gen : FeedbackGenerator) (n : ℕ)
    (i : {i // i ∈ (Finset.range n).filter
      (fun j => (orderedTarget gen).enumeration j ∈ core)}) :
    2 ^ coreExponent gen n i = (orderedTarget gen).enumeration i :=
  Classical.choose_spec (Finset.mem_filter.mp i.property).2

lemma core_prefixCount_le_log (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).prefixCount core n ≤ Nat.log2 (12 * n + 10) + 1 := by
  let I := {i // i ∈ (Finset.range n).filter
    (fun j => (orderedTarget gen).enumeration j ∈ core)}
  let f : I → Fin (Nat.log2 (12 * n + 10) + 1) := fun i => ⟨coreExponent gen n i, by
    apply Nat.lt_succ_of_le
    rw [Nat.le_log2 (by omega : 12 * n + 10 ≠ 0)]
    rw [coreExponent_spec]
    exact (orderedTarget_enumeration_lt gen i).le.trans (by
      have hi : (i : ℕ) < n := Finset.mem_range.mp (Finset.mem_filter.mp i.property).1
      omega)⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply (orderedTarget gen).enumeration_injective
    rw [← coreExponent_spec gen n i, ← coreExponent_spec gen n j]
    exact congrArg (fun k : Fin (Nat.log2 (12 * n + 10) + 1) => 2 ^ (k : ℕ)) hij
  have hc := Fintype.card_le_of_injective f hf
  simpa [GenLimit.KleinbergWei.OrderedLanguage.prefixCount, I] using hc

end Stage3Proof
