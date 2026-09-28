import Stage3Model
import Mathlib.Data.Nat.Nth
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Set Filter

namespace Stage3Proof

open Stage3S2B

structure History (t : ℕ) where
  presentation : Fin t → ℕ
  query : Fin t → Option ℕ
  answer : Fin t → Option Bool
  output : Fin t → ℕ

def History.empty : History 0 where
  presentation := Fin.elim0
  query := Fin.elim0
  answer := Fin.elim0
  output := Fin.elim0

def extend {t : ℕ} (f : Fin t → α) (x : α) : Fin (t + 1) → α :=
  Fin.lastCases x f

def forbidden {t : ℕ} (h : History t) : Finset ℕ :=
  Finset.univ.image h.presentation ∪
    Finset.univ.image (fun i => (h.query i).getD 0) ∪
    Finset.univ.image h.output

lemma forbidden_card_le {t : ℕ} (h : History t) : (forbidden h).card ≤ 3 * t := by
  unfold forbidden
  let A := Finset.univ.image h.presentation
  let B := Finset.univ.image (fun i => (h.query i).getD 0)
  let C := Finset.univ.image h.output
  change (A ∪ B ∪ C).card ≤ 3 * t
  have hA : A.card ≤ t := by
    simpa [A] using (Finset.card_image_le (s := (Finset.univ : Finset (Fin t)))
      (f := h.presentation))
  have hB : B.card ≤ t := by
    simpa [B] using (Finset.card_image_le (s := (Finset.univ : Finset (Fin t)))
      (f := fun i => (h.query i).getD 0))
  have hC : C.card ≤ t := by
    simpa [C] using (Finset.card_image_le (s := (Finset.univ : Finset (Fin t)))
      (f := h.output))
  calc
    (A ∪ B ∪ C).card ≤ (A ∪ B).card + C.card := Finset.card_union_le (A ∪ B) C
    _ ≤ (A.card + B.card) + C.card :=
      Nat.add_le_add_right (Finset.card_union_le A B) C.card
    _ ≤ t + t + t := by omega
    _ = 3 * t := by omega

lemma ordinary_infinite : ordinary.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => 2 * n + 3)
  · intro a b hab
    simp only at hab
    omega
  · intro n
    rintro ⟨k, hk⟩
    cases k with
    | zero => norm_num at hk
    | succ k =>
        have heven : Even (2 ^ (k + 1)) :=
          Nat.even_pow.mpr ⟨even_two, by omega⟩
        have hmod := Nat.even_iff.mp heven
        change 2 ^ (k + 1) = 2 * n + 3 at hk
        rw [hk] at hmod
        omega

lemma exists_ordinary_not_forbidden {t : ℕ} (h : History t) :
    ∃ z, z ∈ ordinary ∧ z ∉ forbidden h :=
  ordinary_infinite.exists_not_mem_finset (forbidden h)

noncomputable def nextPresentation {t : ℕ} (h : History t) : ℕ := by
  classical
  exact if t % 2 = 0 then 2 ^ (t / 2)
    else Nat.find (exists_ordinary_not_forbidden h)

lemma nextPresentation_odd_spec {t : ℕ} (h : History t) (ht : t % 2 ≠ 0) :
    nextPresentation h ∈ ordinary ∧ nextPresentation h ∉ forbidden h := by
  classical
  simp only [nextPresentation, ht, if_false]
  exact Nat.find_spec (exists_ordinary_not_forbidden h)

def prefixSet {t : ℕ} (p : Fin (t + 1) → ℕ) : Language := Set.range p

noncomputable def step (gen : FeedbackGenerator) {t : ℕ} (h : History t) : History (t + 1) := by
  let x := nextPresentation h
  let p := extend h.presentation x
  let q := gen.query t p h.answer
  let a := match q with
    | none => none
    | some z => some (membershipAnswer (core ∪ prefixSet p) z)
  let y := gen.output t p (extend h.answer a)
  exact {
    presentation := p
    query := extend h.query q
    answer := extend h.answer a
    output := extend h.output y
  }

noncomputable def histories (gen : FeedbackGenerator) : (t : ℕ) → History t
  | 0 => History.empty
  | t + 1 => step gen (histories gen t)

noncomputable def presentation (gen : FeedbackGenerator) : Stream :=
  fun t => (histories gen (t + 1)).presentation (Fin.last t)

noncomputable def query (gen : FeedbackGenerator) : ℕ → Option ℕ :=
  fun t => (histories gen (t + 1)).query (Fin.last t)

noncomputable def answer (gen : FeedbackGenerator) : ℕ → Option Bool :=
  fun t => (histories gen (t + 1)).answer (Fin.last t)

noncomputable def output (gen : FeedbackGenerator) : Stream :=
  fun t => (histories gen (t + 1)).output (Fin.last t)

noncomputable def transcript (gen : FeedbackGenerator) : Transcript where
  presentation := presentation gen
  query := query gen
  answer := answer gen
  output := output gen

noncomputable def target (gen : FeedbackGenerator) : Language :=
  core ∪ (Set.range (presentation gen) ∩ ordinary)

noncomputable def presenter : CausalPresenter where
  next t p q _a y := by
    classical
    exact if t % 2 = 0 then 2 ^ (t / 2)
      else Nat.find (exists_ordinary_not_forbidden ({
        presentation := p
        query := q
        answer := fun _ => none
        output := y
      } : History t))

end Stage3Proof

namespace Stage3Proof

open Stage3S2B

@[simp] lemma histories_zero (gen : FeedbackGenerator) : histories gen 0 = History.empty := rfl
@[simp] lemma histories_succ (gen : FeedbackGenerator) (t : ℕ) :
    histories gen (t + 1) = step gen (histories gen t) := rfl

lemma history_presentation_eq (gen : FeedbackGenerator) :
    ∀ t (i : Fin t), (histories gen t).presentation i = presentation gen i := by
  intro t
  induction t with
  | zero => intro i; exact Fin.elim0 i
  | succ t ih =>
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · simpa [histories_succ, step, extend] using ih j

lemma history_query_eq (gen : FeedbackGenerator) :
    ∀ t (i : Fin t), (histories gen t).query i = query gen i := by
  intro t
  induction t with
  | zero => intro i; exact Fin.elim0 i
  | succ t ih =>
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · simpa [histories_succ, step, extend] using ih j

lemma history_answer_eq (gen : FeedbackGenerator) :
    ∀ t (i : Fin t), (histories gen t).answer i = answer gen i := by
  intro t
  induction t with
  | zero => intro i; exact Fin.elim0 i
  | succ t ih =>
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · simpa [histories_succ, step, extend] using ih j

lemma history_output_eq (gen : FeedbackGenerator) :
    ∀ t (i : Fin t), (histories gen t).output i = output gen i := by
  intro t
  induction t with
  | zero => intro i; exact Fin.elim0 i
  | succ t ih =>
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · simpa [histories_succ, step, extend] using ih j

lemma presentation_eq_next (gen : FeedbackGenerator) (t : ℕ) :
    presentation gen t = nextPresentation (histories gen t) := by
  simp [presentation, histories_succ, step, extend]

lemma prefixSet_eq_observed (gen : FeedbackGenerator) (t : ℕ) :
    prefixSet (fun i : Fin (t + 1) => presentation gen i) =
      observedThrough (presentation gen) t := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, by omega, rfl⟩
  · rintro ⟨s, hs, hzs⟩
    exact ⟨⟨s, by omega⟩, hzs⟩

lemma query_eq_gen (gen : FeedbackGenerator) (t : ℕ) :
    query gen t = gen.query t (fun i => presentation gen i) (fun i => answer gen i) := by
  simp only [query, histories_succ, step, extend, Fin.lastCases_last]
  congr 1
  · funext i
    exact history_presentation_eq gen (t + 1) i
  · funext i
    exact history_answer_eq gen t i

lemma answer_eq_local (gen : FeedbackGenerator) (t : ℕ) :
    answer gen t = match query gen t with
      | none => none
      | some z => some (membershipAnswer (core ∪ observedThrough (presentation gen) t) z) := by
  have hp : extend (histories gen t).presentation (nextPresentation (histories gen t)) =
      (fun i : Fin (t + 1) => presentation gen i) := by
    funext i
    simpa [histories_succ, step] using history_presentation_eq gen (t + 1) i
  have ha : (histories gen t).answer = (fun i : Fin t => answer gen i) := by
    funext i
    exact history_answer_eq gen t i
  simp only [answer, histories_succ, step, extend, Fin.lastCases_last]
  rw [ha, query_eq_gen, hp, prefixSet_eq_observed]

lemma output_eq_gen (gen : FeedbackGenerator) (t : ℕ) :
    output gen t = gen.output t (fun i => presentation gen i) (fun i => answer gen i) := by
  simp only [output, histories_succ, step, extend, Fin.lastCases_last]
  congr 1
  · funext i
    exact history_presentation_eq gen (t + 1) i
  · funext i
    exact history_answer_eq gen (t + 1) i

end Stage3Proof

namespace Stage3Proof

open Stage3S2B

lemma presentation_even (gen : FeedbackGenerator) (r : ℕ) :
    presentation gen (2 * r) = 2 ^ r := by
  rw [presentation_eq_next]
  simp [nextPresentation]

lemma presentation_odd_mem (gen : FeedbackGenerator) (r : ℕ) :
    presentation gen (2 * r + 1) ∈ ordinary := by
  rw [presentation_eq_next]
  exact (nextPresentation_odd_spec (histories gen (2 * r + 1)) (by omega)).1

lemma prior_presentation_mem_forbidden (gen : FeedbackGenerator) {s t : ℕ} (hst : s < t) :
    presentation gen s ∈ forbidden (histories gen t) := by
  classical
  unfold forbidden
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  refine ⟨⟨s, hst⟩, Finset.mem_univ _, ?_⟩
  exact history_presentation_eq gen t ⟨s, hst⟩

lemma prior_query_mem_forbidden (gen : FeedbackGenerator) {s t z : ℕ}
    (hst : s < t) (hq : query gen s = some z) :
    z ∈ forbidden (histories gen t) := by
  classical
  unfold forbidden
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  refine ⟨⟨s, hst⟩, Finset.mem_univ _, ?_⟩
  rw [history_query_eq gen t ⟨s, hst⟩, hq]
  rfl

lemma prior_output_mem_forbidden (gen : FeedbackGenerator) {s t : ℕ} (hst : s < t) :
    output gen s ∈ forbidden (histories gen t) := by
  classical
  unfold forbidden
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  refine ⟨⟨s, hst⟩, Finset.mem_univ _, ?_⟩
  exact history_output_eq gen t ⟨s, hst⟩

lemma odd_ne_prior_presentation (gen : FeedbackGenerator) {s t : ℕ}
    (hst : s < t) (ht : t % 2 ≠ 0) : presentation gen t ≠ presentation gen s := by
  rw [presentation_eq_next]
  intro heq
  have hnot := (nextPresentation_odd_spec (histories gen t) ht).2
  apply hnot
  rw [heq]
  exact prior_presentation_mem_forbidden gen hst

lemma odd_ne_prior_query (gen : FeedbackGenerator) {s t z : ℕ}
    (hst : s < t) (ht : t % 2 ≠ 0) (hq : query gen s = some z) :
    presentation gen t ≠ z := by
  rw [presentation_eq_next]
  intro heq
  have hnot := (nextPresentation_odd_spec (histories gen t) ht).2
  apply hnot
  rw [heq]
  exact prior_query_mem_forbidden gen hst hq

lemma odd_ne_prior_output (gen : FeedbackGenerator) {s t : ℕ}
    (hst : s < t) (ht : t % 2 ≠ 0) : presentation gen t ≠ output gen s := by
  rw [presentation_eq_next]
  intro heq
  have hnot := (nextPresentation_odd_spec (histories gen t) ht).2
  apply hnot
  rw [heq]
  exact prior_output_mem_forbidden gen hst


lemma eq_two_mul_of_mod_two_eq_zero {t : ℕ} (ht : t % 2 = 0) :
    ∃ r, t = 2 * r :=
  even_iff_exists_two_mul.mp (Nat.even_iff.mpr ht)

lemma eq_two_mul_add_one_of_mod_two_ne_zero {t : ℕ} (ht : t % 2 ≠ 0) :
    ∃ r, t = 2 * r + 1 :=
  odd_iff_exists_bit1.mp (Nat.odd_iff.mpr (Nat.mod_two_ne_zero.mp ht))

lemma presentation_mem_target (gen : FeedbackGenerator) (t : ℕ) :
    presentation gen t ∈ target gen := by
  by_cases ht : t % 2 = 0
  · obtain ⟨r, rfl⟩ := eq_two_mul_of_mod_two_eq_zero ht
    left
    exact ⟨r, presentation_even gen r |>.symm⟩
  · right
    exact ⟨⟨t, rfl⟩, by
      obtain ⟨r, rfl⟩ := eq_two_mul_add_one_of_mod_two_ne_zero ht
      simpa [Nat.two_mul] using presentation_odd_mem gen r⟩

lemma target_mem_class (gen : FeedbackGenerator) : target gen ∈ targetClass := by
  exact ⟨Set.range (presentation gen) ∩ ordinary, Set.inter_subset_right, rfl⟩

lemma presentation_complete (gen : FeedbackGenerator) : Complete (presentation gen) (target gen) := by
  intro z hz
  rcases hz with hz | ⟨⟨t, rfl⟩, _⟩
  · rcases hz with ⟨r, rfl⟩
    exact ⟨2 * r, presentation_even gen r⟩
  · exact ⟨t, rfl⟩

lemma presentation_injective (gen : FeedbackGenerator) : Function.Injective (presentation gen) := by
  intro s t hst
  by_contra hne
  wlog hlt : s < t generalizing s t
  · have hts : t < s := lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm hne)
    exact this (Eq.symm hst) (Ne.symm hne) hts
  by_cases ht : t % 2 = 0
  · obtain ⟨r, rfl⟩ := eq_two_mul_of_mod_two_eq_zero ht
    have hsCore : presentation gen s ∈ core := by
      rw [hst, presentation_even]
      exact ⟨r, rfl⟩
    by_cases hs : s % 2 = 0
    · obtain ⟨q, rfl⟩ := eq_two_mul_of_mod_two_eq_zero hs
      rw [presentation_even, presentation_even] at hst
      have : q = r := by exact Nat.pow_right_injective (by omega : 2 ≤ (2 : ℕ)) hst
      omega
    · have hsOrd : presentation gen s ∈ ordinary := by
        obtain ⟨q, rfl⟩ := eq_two_mul_add_one_of_mod_two_ne_zero hs
        simpa [Nat.two_mul] using presentation_odd_mem gen q
      exact hsOrd hsCore
  · exact odd_ne_prior_presentation gen hlt ht hst.symm

lemma presented_by (gen : FeedbackGenerator) : PresentedBy presenter (transcript gen) := by
  intro t
  change presentation gen t = presenter.next t
    (fun i => presentation gen i) (fun i => query gen i)
    (fun i => answer gen i) (fun i => output gen i)
  rw [presentation_eq_next]
  unfold presenter nextPresentation
  simp only
  split <;> rename_i ht
  · rfl
  · congr 1
    have hp : (histories gen t).presentation = (fun i : Fin t => presentation gen i) := by
      funext i
      exact history_presentation_eq gen t i
    have hq' : (histories gen t).query = (fun i : Fin t => query gen i) := by
      funext i
      exact history_query_eq gen t i
    have hy : (histories gen t).output = (fun i : Fin t => output gen i) := by
      funext i
      exact history_output_eq gen t i
    have hf : forbidden (histories gen t) = forbidden ({
        presentation := fun i => presentation gen i
        query := fun i => query gen i
        answer := fun _ => none
        output := fun i => output gen i
      } : History t) := by
      simp only [forbidden, hp, hq', hy]
    funext n
    apply propext
    rw [hf]


lemma target_local_iff (gen : FeedbackGenerator) (t z : ℕ)
    (hq : query gen t = some z) :
    z ∈ target gen ↔ z ∈ core ∪ observedThrough (presentation gen) t := by
  constructor
  · intro hz
    rcases hz with hz | ⟨⟨s, hs⟩, hsOrd⟩
    · exact Or.inl hz
    · by_cases hst : s ≤ t
      · exact Or.inr ⟨s, hst, hs⟩
      · have hts : t < s := Nat.lt_of_not_ge hst
        have hsOdd : s % 2 ≠ 0 := by
          intro heven
          obtain ⟨r, rfl⟩ := eq_two_mul_of_mod_two_eq_zero heven
          apply hsOrd
          rw [presentation_even gen r] at hs
          exact hs ▸ ⟨r, rfl⟩
        exact False.elim ((odd_ne_prior_query gen hts hsOdd hq) hs)
  · intro hz
    rcases hz with hz | ⟨s, _hst, hs⟩
    · exact Or.inl hz
    · rw [← hs]
      exact presentation_mem_target gen s

lemma follows_protocol (gen : FeedbackGenerator) :
    FollowsProtocol gen (target gen) (transcript gen) := by
  intro t
  change query gen t = gen.query t (fun i => presentation gen i) (fun i => answer gen i) ∧
    answer gen t = (match query gen t with
      | none => none
      | some z => some (membershipAnswer (target gen) z)) ∧
    output gen t = gen.output t (fun i => presentation gen i) (fun i => answer gen i)
  refine ⟨query_eq_gen gen t, ?_, output_eq_gen gen t⟩
  rw [answer_eq_local]
  cases hq : query gen t with
  | none => rfl
  | some z =>
      simp only
      apply congrArg some
      classical
      unfold membershipAnswer
      exact decide_eq_decide.mpr (target_local_iff gen t z hq).symm

lemma clean_presentation (gen : FeedbackGenerator) : Clean (presentation gen) (target gen) :=
  presentation_mem_target gen

lemma scored_subset_core (gen : FeedbackGenerator) :
    scored (target gen) (presentation gen) (output gen) ⊆ core := by
  intro z hz
  rcases hz with ⟨hzK, t, hyt, hznot⟩
  rcases hzK with hzCore | ⟨⟨s, hs⟩, hsOrd⟩
  · exact hzCore
  · exfalso
    have hts : t < s := by
      by_contra hnot
      have hst : s ≤ t := Nat.le_of_not_gt hnot
      apply hznot
      exact ⟨s, hst, hs⟩
    have hsOdd : s % 2 ≠ 0 := by
      intro heven
      obtain ⟨r, rfl⟩ := eq_two_mul_of_mod_two_eq_zero heven
      apply hsOrd
      rw [presentation_even gen r] at hs
      exact hs ▸ ⟨r, rfl⟩
    exact (odd_ne_prior_output gen hts hsOdd) (hs.trans hyt.symm)

end Stage3Proof
