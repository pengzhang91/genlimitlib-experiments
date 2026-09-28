import Stage3Model
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import GenLimit.Paper39_DenseGeneration.Abstract.Density
import Mathlib.Data.Nat.Nth
import Mathlib.Tactic

open Set Filter
open GenLimit.KleinbergWei

namespace Stage3S2BProof
open Stage3S2B

structure AdvState (t : ℕ) where
  presentation : Fin t → ℕ
  query : Fin t → Option ℕ
  answer : Fin t → Option Bool
  output : Fin t → ℕ
  admitted : Finset ℕ
  rejected : Finset ℕ

noncomputable def leastOrdinaryOutside (F : Finset ℕ) : ℕ :=
  sInf {z : ℕ | z ∈ ordinary ∧ z ∉ F}

private theorem ordinary_infinite : ordinary.Infinite := by
  let f : ℕ → ℕ := fun n => 2 * n + 3
  have hf : Function.Injective f := by
    intro a b h
    dsimp [f] at h
    omega
  apply (Set.infinite_range_of_injective hf).mono
  rintro z ⟨n, rfl⟩ ⟨k, hk⟩
  change 2 ^ k = 2 * n + 3 at hk
  by_cases hk0 : k = 0
  · subst k
    simp at hk
  · have heven : Even (2 ^ k) := Nat.even_pow.mpr ⟨by simp, hk0⟩
    rw [hk] at heven
    obtain ⟨w, hw⟩ := heven
    omega

private theorem leastOrdinaryOutside_exists (F : Finset ℕ) :
    ∃ z, z ∈ ordinary ∧ z ∉ F :=
  ordinary_infinite.exists_not_mem_finset F

@[simp] theorem leastOrdinaryOutside_mem (F : Finset ℕ) :
    leastOrdinaryOutside F ∈ ordinary := by
  unfold leastOrdinaryOutside
  exact (Nat.sInf_mem (leastOrdinaryOutside_exists F)).1

@[simp] theorem leastOrdinaryOutside_not_mem (F : Finset ℕ) :
    leastOrdinaryOutside F ∉ F := by
  unfold leastOrdinaryOutside
  exact (Nat.sInf_mem (leastOrdinaryOutside_exists F)).2

noncomputable def chooseX {t : ℕ} (s : AdvState t) : ℕ :=
  if Even t then 2 ^ (t / 2)
  else leastOrdinaryOutside (s.admitted ∪ s.rejected)

noncomputable def nextAdmitted {t : ℕ} (s : AdvState t) : Finset ℕ :=
  if Even t then s.admitted else insert (chooseX s) s.admitted

noncomputable def positiveAnswer (I : Finset ℕ) (z : ℕ) : Bool := by
  classical
  exact decide (z ∈ core ∨ z ∈ I)

noncomputable def afterQueryRejected (I R : Finset ℕ) (q : Option ℕ) : Finset ℕ := by
  classical
  exact match q with
    | none => R
    | some z => if z ∈ core ∨ z ∈ I ∨ z ∈ R then R else insert z R

noncomputable def afterOutputRejected (I R : Finset ℕ) (y : ℕ) : Finset ℕ := by
  classical
  exact if y ∈ core ∨ y ∈ I ∨ y ∈ R then R else insert y R

noncomputable def step (gen : FeedbackGenerator) {t : ℕ}
    (s : AdvState t) : AdvState (t + 1) := by
  classical
  let x := chooseX s
  let I' := nextAdmitted s
  let q := gen.query t (Fin.lastCases x s.presentation) s.answer
  let b : Option Bool := q.map (positiveAnswer I')
  let Rq := afterQueryRejected I' s.rejected q
  let y := gen.output t (Fin.lastCases x s.presentation)
    (Fin.lastCases b s.answer)
  let R' := afterOutputRejected I' Rq y
  exact {
    presentation := Fin.lastCases x s.presentation
    query := Fin.lastCases q s.query
    answer := Fin.lastCases b s.answer
    output := Fin.lastCases y s.output
    admitted := I'
    rejected := R'
  }

noncomputable def states (gen : FeedbackGenerator) : (t : ℕ) → AdvState t
  | 0 => ⟨Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, ∅, ∅⟩
  | t + 1 => step gen (states gen t)

noncomputable def xStream (gen : FeedbackGenerator) : Stream :=
  fun t => (states gen (t + 1)).presentation (Fin.last t)
noncomputable def qStream (gen : FeedbackGenerator) : ℕ → Option ℕ :=
  fun t => (states gen (t + 1)).query (Fin.last t)
noncomputable def aStream (gen : FeedbackGenerator) : ℕ → Option Bool :=
  fun t => (states gen (t + 1)).answer (Fin.last t)
noncomputable def yStream (gen : FeedbackGenerator) : Stream :=
  fun t => (states gen (t + 1)).output (Fin.last t)

def limitAdmitted (gen : FeedbackGenerator) : Language :=
  {z | ∃ t, z ∈ (states gen t).admitted}
def limitRejected (gen : FeedbackGenerator) : Language :=
  {z | ∃ t, z ∈ (states gen t).rejected}
def target (gen : FeedbackGenerator) : Language := core ∪ limitAdmitted gen

noncomputable def transcript (gen : FeedbackGenerator) : Transcript :=
  ⟨xStream gen, qStream gen, aStream gen, yStream gen⟩


@[simp] theorem step_presentation_old (gen : FeedbackGenerator) {t : ℕ}
    (s : AdvState t) (i : Fin t) :
    (step gen s).presentation i.castSucc = s.presentation i := by
  classical
  simp [step]

@[simp] theorem step_query_old (gen : FeedbackGenerator) {t : ℕ}
    (s : AdvState t) (i : Fin t) :
    (step gen s).query i.castSucc = s.query i := by
  classical
  simp [step]

@[simp] theorem step_answer_old (gen : FeedbackGenerator) {t : ℕ}
    (s : AdvState t) (i : Fin t) :
    (step gen s).answer i.castSucc = s.answer i := by
  classical
  simp [step]

@[simp] theorem step_output_old (gen : FeedbackGenerator) {t : ℕ}
    (s : AdvState t) (i : Fin t) :
    (step gen s).output i.castSucc = s.output i := by
  classical
  simp [step]

@[simp] theorem states_presentation_eq (gen : FeedbackGenerator) (t : ℕ)
    (i : Fin t) : (states gen t).presentation i = xStream gen i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · simpa [states] using ih j

@[simp] theorem states_query_eq (gen : FeedbackGenerator) (t : ℕ)
    (i : Fin t) : (states gen t).query i = qStream gen i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · simpa [states] using ih j

@[simp] theorem states_answer_eq (gen : FeedbackGenerator) (t : ℕ)
    (i : Fin t) : (states gen t).answer i = aStream gen i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · simpa [states] using ih j

@[simp] theorem states_output_eq (gen : FeedbackGenerator) (t : ℕ)
    (i : Fin t) : (states gen t).output i = yStream gen i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · simpa [states] using ih j

private theorem nextAdmitted_mono {t : ℕ} (s : AdvState t) :
    s.admitted ⊆ nextAdmitted s := by
  classical
  simp [nextAdmitted]
  split <;> simp_all

private theorem afterQueryRejected_mono (I R : Finset ℕ) (q : Option ℕ) :
    R ⊆ afterQueryRejected I R q := by
  classical
  cases q <;> simp [afterQueryRejected]
  split <;> simp_all

private theorem afterOutputRejected_mono (I R : Finset ℕ) (y : ℕ) :
    R ⊆ afterOutputRejected I R y := by
  classical
  simp [afterOutputRejected]
  split <;> simp_all

private theorem admitted_mono_step (gen : FeedbackGenerator) {t : ℕ}
    (s : AdvState t) : s.admitted ⊆ (step gen s).admitted := by
  simpa [step] using nextAdmitted_mono s

private theorem rejected_mono_step (gen : FeedbackGenerator) {t : ℕ}
    (s : AdvState t) : s.rejected ⊆ (step gen s).rejected := by
  classical
  simp only [step]
  exact fun z hz => afterOutputRejected_mono _ _ _
    (afterQueryRejected_mono _ _ _ hz)

private theorem nextAdmitted_ordinary {t : ℕ} (s : AdvState t)
    (hI : ∀ z ∈ s.admitted, z ∈ ordinary) :
    ∀ z ∈ nextAdmitted s, z ∈ ordinary := by
  classical
  unfold nextAdmitted
  split
  · exact hI
  · rename_i ht
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · simp [chooseX, ht]
    · exact hI z hz

private theorem query_update_invariants (I R : Finset ℕ) (q : Option ℕ)
    (hI : ∀ z ∈ I, z ∈ ordinary) (hR : ∀ z ∈ R, z ∈ ordinary)
    (hdis : Disjoint I R) :
    (∀ z ∈ afterQueryRejected I R q, z ∈ ordinary) ∧
      Disjoint I (afterQueryRejected I R q) := by
  classical
  cases q with
  | none => exact ⟨hR, hdis⟩
  | some q =>
      simp only [afterQueryRejected]
      split
      · exact ⟨hR, hdis⟩
      · rename_i h
        push_neg at h
        constructor
        · intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz
          · exact h.1
          · exact hR z hz
        · rw [Finset.disjoint_left]
          intro z hzI hznew
          rcases Finset.mem_insert.mp hznew with rfl | hzR
          · exact h.2.1 hzI
          · exact (Finset.disjoint_left.mp hdis) hzI hzR

private theorem output_update_invariants (I R : Finset ℕ) (y : ℕ)
    (hI : ∀ z ∈ I, z ∈ ordinary) (hR : ∀ z ∈ R, z ∈ ordinary)
    (hdis : Disjoint I R) :
    (∀ z ∈ afterOutputRejected I R y, z ∈ ordinary) ∧
      Disjoint I (afterOutputRejected I R y) := by
  classical
  simp only [afterOutputRejected]
  split
  · exact ⟨hR, hdis⟩
  · rename_i h
    push_neg at h
    constructor
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact h.1
      · exact hR z hz
    · rw [Finset.disjoint_left]
      intro z hzI hznew
      rcases Finset.mem_insert.mp hznew with rfl | hzR
      · exact h.2.1 hzI
      · exact (Finset.disjoint_left.mp hdis) hzI hzR

private theorem nextAdmitted_disjoint_rejected {t : ℕ} (s : AdvState t)
    (hdis : Disjoint s.admitted s.rejected) :
    Disjoint (nextAdmitted s) s.rejected := by
  classical
  unfold nextAdmitted
  split
  · exact hdis
  · rename_i ht
    rw [Finset.disjoint_left]
    intro z hz hzR
    rcases Finset.mem_insert.mp hz with rfl | hzI
    · have hx : chooseX s = leastOrdinaryOutside (s.admitted ∪ s.rejected) := by
        simp [chooseX, ht]
      rw [hx] at hzR
      exact leastOrdinaryOutside_not_mem (s.admitted ∪ s.rejected)
        (Finset.mem_union_right _ hzR)
    · exact (Finset.disjoint_left.mp hdis) hzI hzR

private theorem state_invariants (gen : FeedbackGenerator) (t : ℕ) :
    (∀ z ∈ (states gen t).admitted, z ∈ ordinary) ∧
    (∀ z ∈ (states gen t).rejected, z ∈ ordinary) ∧
    Disjoint (states gen t).admitted (states gen t).rejected := by
  induction t with
  | zero => simp [states]
  | succ t ih =>
      classical
      let s := states gen t
      have hI : ∀ z ∈ nextAdmitted s, z ∈ ordinary :=
        nextAdmitted_ordinary s ih.1
      have hq := query_update_invariants (nextAdmitted s) s.rejected
        (gen.query t (Fin.lastCases (chooseX s) s.presentation) s.answer)
        hI ih.2.1 (nextAdmitted_disjoint_rejected s ih.2.2)
      have ho := output_update_invariants (nextAdmitted s)
        (afterQueryRejected (nextAdmitted s) s.rejected
          (gen.query t (Fin.lastCases (chooseX s) s.presentation) s.answer))
        (gen.output t (Fin.lastCases (chooseX s) s.presentation)
          (Fin.lastCases
            ((gen.query t (Fin.lastCases (chooseX s) s.presentation) s.answer).map
              (positiveAnswer (nextAdmitted s))) s.answer))
        hI hq.1 hq.2
      simpa only [states, step, s] using ⟨hI, ho⟩

private theorem admitted_mono (gen : FeedbackGenerator) (t : ℕ) :
    (states gen t).admitted ⊆ (states gen (t + 1)).admitted :=
  admitted_mono_step gen (states gen t)

private theorem rejected_mono (gen : FeedbackGenerator) (t : ℕ) :
    (states gen t).rejected ⊆ (states gen (t + 1)).rejected :=
  rejected_mono_step gen (states gen t)

private theorem admitted_mono_le (gen : FeedbackGenerator) {t u : ℕ} (h : t ≤ u) :
    (states gen t).admitted ⊆ (states gen u).admitted := by
  induction u, h using Nat.le_induction with
  | base => intro z hz; exact hz
  | succ u h ih => exact fun z hz => admitted_mono gen u (ih hz)

private theorem rejected_mono_le (gen : FeedbackGenerator) {t u : ℕ} (h : t ≤ u) :
    (states gen t).rejected ⊆ (states gen u).rejected := by
  induction u, h using Nat.le_induction with
  | base => intro z hz; exact hz
  | succ u h ih => exact fun z hz => rejected_mono gen u (ih hz)

private theorem limit_disjoint (gen : FeedbackGenerator) :
    Disjoint (limitAdmitted gen) (limitRejected gen) := by
  rw [Set.disjoint_left]
  rintro z ⟨ta, hza⟩ ⟨tr, hzr⟩
  let u := max ta tr
  have ha := admitted_mono_le gen (show ta ≤ u by simp [u]) hza
  have hr := rejected_mono_le gen (show tr ≤ u by simp [u]) hzr
  exact (Finset.disjoint_left.mp (state_invariants gen u).2.2) ha hr

private theorem limitAdmitted_ordinary (gen : FeedbackGenerator) :
    limitAdmitted gen ⊆ ordinary := by
  rintro z ⟨t, hz⟩
  exact (state_invariants gen t).1 z hz




private theorem current_x (gen : FeedbackGenerator) (t : ℕ) :
    xStream gen t = chooseX (states gen t) := by
  simp [xStream, states, step]

private theorem current_q (gen : FeedbackGenerator) (t : ℕ) :
    qStream gen t = gen.query t (fun i => xStream gen i) (fun i => aStream gen i) := by
  unfold qStream
  rw [states]
  simp only [step, Fin.lastCases_last]
  congr 1
  · funext i
    simpa [states, step] using states_presentation_eq gen (t + 1) i
  · funext i
    exact states_answer_eq gen t i

private theorem current_a (gen : FeedbackGenerator) (t : ℕ) :
    aStream gen t = (qStream gen t).map
      (positiveAnswer (nextAdmitted (states gen t))) := by
  simp [aStream, qStream, states, step]

private theorem current_y (gen : FeedbackGenerator) (t : ℕ) :
    yStream gen t = gen.output t (fun i => xStream gen i) (fun i => aStream gen i) := by
  unfold yStream
  rw [states]
  simp only [step, Fin.lastCases_last]
  congr 1
  · funext i
    simpa [states, step] using states_presentation_eq gen (t + 1) i
  · funext i
    simpa [states, step] using states_answer_eq gen (t + 1) i

private theorem current_admitted (gen : FeedbackGenerator) (t : ℕ) :
    (states gen (t + 1)).admitted = nextAdmitted (states gen t) := by
  rfl

private theorem current_rejected (gen : FeedbackGenerator) (t : ℕ) :
    (states gen (t + 1)).rejected =
      afterOutputRejected (nextAdmitted (states gen t))
        (afterQueryRejected (nextAdmitted (states gen t)) (states gen t).rejected
          (qStream gen t)) (yStream gen t) := by
  simp [qStream, yStream, states, step]

private theorem nextAdmitted_subset_limit (gen : FeedbackGenerator) (t : ℕ) :
    ↑(nextAdmitted (states gen t)) ⊆ limitAdmitted gen := by
  intro z hz
  exact ⟨t + 1, by simpa [current_admitted] using hz⟩

private theorem rejected_subset_limit (gen : FeedbackGenerator) (t : ℕ) :
    ↑((states gen t).rejected) ⊆ limitRejected gen := by
  intro z hz
  exact ⟨t, hz⟩

private theorem query_target_iff (gen : FeedbackGenerator) (t z : ℕ)
    (hq : qStream gen t = some z) :
    z ∈ target gen ↔ z ∈ core ∨ z ∈ nextAdmitted (states gen t) := by
  constructor
  · rintro (hc | ha)
    · exact Or.inl hc
    · by_contra h
      push_neg at h
      have hzR : z ∈ afterQueryRejected (nextAdmitted (states gen t))
          (states gen t).rejected (qStream gen t) := by
        by_cases hzold : z ∈ (states gen t).rejected <;>
          simp [afterQueryRejected, hq, h, hzold]
      have hzR' : z ∈ (states gen (t + 1)).rejected := by
        rw [current_rejected]
        exact afterOutputRejected_mono _ _ _ hzR
      exact False.elim ((Set.disjoint_left.mp (limit_disjoint gen)) ha ⟨t + 1, hzR'⟩)
  · rintro (hc | hI)
    · exact Or.inl hc
    · exact Or.inr (nextAdmitted_subset_limit gen t hI)

private theorem answer_eq_membership (gen : FeedbackGenerator) (t z : ℕ)
    (hq : qStream gen t = some z) :
    aStream gen t = some (membershipAnswer (target gen) z) := by
  rw [current_a, hq]
  simp only [Option.map_some]
  congr 1
  have hiff := query_target_iff gen t z hq
  simp [positiveAnswer, membershipAnswer, hiff]

private theorem follows_protocol (gen : FeedbackGenerator) :
    FollowsProtocol gen (target gen) (transcript gen) := by
  intro t
  refine ⟨current_q gen t, ?_, current_y gen t⟩
  change aStream gen t = match qStream gen t with
    | none => none
    | some z => some (membershipAnswer (target gen) z)
  cases hq : qStream gen t with
  | none => simp [current_a, hq]
  | some z => exact answer_eq_membership gen t z hq

private theorem admitted_presented (gen : FeedbackGenerator) (t : ℕ) :
    ∀ z ∈ (states gen t).admitted, ∃ i : Fin t, (states gen t).presentation i = z := by
  induction t with
  | zero => simp [states]
  | succ t ih =>
      classical
      intro z hz
      rw [current_admitted] at hz
      unfold nextAdmitted at hz
      split at hz
      · obtain ⟨i, hi⟩ := ih z hz
        exact ⟨i.castSucc, by simpa [states] using hi⟩
      · rcases Finset.mem_insert.mp hz with rfl | hz
        · exact ⟨Fin.last t, by simpa [current_x]⟩
        · obtain ⟨i, hi⟩ := ih z hz
          exact ⟨i.castSucc, by simpa [states] using hi⟩

private theorem xStream_mem_target (gen : FeedbackGenerator) (t : ℕ) :
    xStream gen t ∈ target gen := by
  unfold target
  rw [current_x]
  unfold chooseX
  split
  · rename_i he
    obtain ⟨k, hk⟩ := he
    subst t
    have hd : (k + k) / 2 = k := by omega
    rw [hd]
    exact Or.inl ⟨k, rfl⟩
  · exact Or.inr ⟨t + 1, by
      rw [current_admitted]
      simp [nextAdmitted, chooseX, *]⟩

private theorem presentation_clean (gen : FeedbackGenerator) :
    Clean (xStream gen) (target gen) := xStream_mem_target gen

private theorem presentation_complete (gen : FeedbackGenerator) :
    Complete (xStream gen) (target gen) := by
  intro z hz
  rcases hz with ⟨k, rfl⟩ | ⟨t, ht⟩
  · refine ⟨2 * k, ?_⟩
    simp [xStream, states, step, chooseX]
  · obtain ⟨i, hi⟩ := admitted_presented gen t z ht
    exact ⟨i, by simpa using hi⟩

noncomputable def presenter (gen : FeedbackGenerator) : CausalPresenter where
  next := fun t _ _ _ _ => xStream gen t

private theorem presented_by (gen : FeedbackGenerator) :
    PresentedBy (presenter gen) (transcript gen) := by
  intro t
  rfl

private theorem scored_subset_core (gen : FeedbackGenerator) :
    scored (target gen) (xStream gen) (yStream gen) ⊆ core := by
  intro z hz
  rcases hz with ⟨hzK, t, hyt, hzobs⟩
  rcases hzK with hcore | ha
  · exact hcore
  · by_cases hzI : z ∈ nextAdmitted (states gen t)
    · obtain ⟨i, hi⟩ := admitted_presented gen (t + 1) z (by
        simpa [current_admitted] using hzI)
      exact (hzobs ⟨i, by omega, by simpa using hi⟩).elim
    · have hzOrd : z ∈ ordinary := limitAdmitted_ordinary gen ha
      have hzCore : z ∉ core := hzOrd
      let Rq := afterQueryRejected (nextAdmitted (states gen t))
        (states gen t).rejected (qStream gen t)
      have hzR : z ∈ afterOutputRejected (nextAdmitted (states gen t)) Rq z := by
        by_cases hzr : z ∈ Rq <;>
          simp [afterOutputRejected, hzCore, hzI, hzr]
      have hzR' : z ∈ (states gen (t + 1)).rejected := by
        rw [current_rejected, hyt]
        exact hzR
      exact False.elim ((Set.disjoint_left.mp (limit_disjoint gen)) ha ⟨t + 1, hzR'⟩)

private theorem presented_classified (gen : FeedbackGenerator) (t : ℕ) :
    ∀ i : Fin t, (states gen t).presentation i ∈ core ∨
      (states gen t).presentation i ∈ (states gen t).admitted := by
  induction t with
  | zero => intro i; exact Fin.elim0 i
  | succ t ih =>
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [show (states gen (t + 1)).presentation (Fin.last t) =
          chooseX (states gen t) by simp [states, step]]
        unfold chooseX
        split
        · exact Or.inl ⟨t / 2, rfl⟩
        · exact Or.inr (by simp [current_admitted, nextAdmitted, chooseX, *])
      · have hj := ih j
        rcases hj with hj | hj
        · exact Or.inl (by simpa [states] using hj)
        · exact Or.inr (by simpa [states] using admitted_mono gen t hj)

private theorem xStream_not_previous (gen : FeedbackGenerator) {a b : ℕ}
    (hab : a < b) : xStream gen a ≠ xStream gen b := by
  intro heq
  have hclass := presented_classified gen b ⟨a, hab⟩
  have hprev : (states gen b).presentation ⟨a, hab⟩ = xStream gen a := by simp
  rw [hprev] at hclass
  by_cases hb : Even b
  · have hxb : xStream gen b = 2 ^ (b / 2) := by
      rw [current_x]
      simp [chooseX, hb]
    have hcoreb : xStream gen b ∈ core := ⟨b / 2, hxb.symm⟩
    rcases hclass with hca | hia
    · by_cases ha : Even a
      · have hxa : xStream gen a = 2 ^ (a / 2) := by
          rw [current_x]
          simp [chooseX, ha]
        have hp : a / 2 = b / 2 :=
          Nat.pow_right_injective (a := 2) (by norm_num) (hxa.symm.trans (heq.trans hxb))
        obtain ⟨p, rfl⟩ := ha
        obtain ⟨q, hq⟩ := hb
        subst b
        simp at hp
        omega
      · have hoa : xStream gen a ∈ ordinary := by
          rw [current_x]
          simp [chooseX, ha]
        exact hoa (heq ▸ hcoreb)
    · exact (state_invariants gen b).1 _ hia (heq ▸ hcoreb)
  · have hxb : xStream gen b =
        leastOrdinaryOutside ((states gen b).admitted ∪ (states gen b).rejected) := by
      rw [current_x]
      simp [chooseX, hb]
    have hob : xStream gen b ∈ ordinary := by rw [hxb]; simp
    rcases hclass with hca | hia
    · exact hob (heq ▸ hca)
    · have hnot : xStream gen b ∉ (states gen b).admitted := by
        rw [hxb]
        exact fun h => leastOrdinaryOutside_not_mem _ (Finset.mem_union_left _ h)
      exact hnot (heq ▸ hia)

private theorem presentation_injective (gen : FeedbackGenerator) :
    Function.Injective (xStream gen) := by
  intro a b h
  by_contra hab
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · exact xStream_not_previous gen hlt h
  · exact xStream_not_previous gen hgt h.symm



private theorem nextAdmitted_card_le {t : ℕ} (s : AdvState t) :
    (nextAdmitted s).card ≤ s.admitted.card + 1 := by
  classical
  simp only [nextAdmitted]
  split
  · omega
  · exact Finset.card_insert_le _ _

private theorem afterQueryRejected_card_le (I R : Finset ℕ) (q : Option ℕ) :
    (afterQueryRejected I R q).card ≤ R.card + 1 := by
  classical
  cases q <;> simp only [afterQueryRejected]
  · omega
  · split
    · omega
    · exact Finset.card_insert_le _ _

private theorem afterOutputRejected_card_le (I R : Finset ℕ) (y : ℕ) :
    (afterOutputRejected I R y).card ≤ R.card + 1 := by
  classical
  simp only [afterOutputRejected]
  split
  · omega
  · exact Finset.card_insert_le _ _

private theorem state_card_bounds (gen : FeedbackGenerator) (t : ℕ) :
    (states gen t).admitted.card ≤ t ∧
    (states gen t).rejected.card ≤ 2 * t := by
  induction t with
  | zero => simp [states]
  | succ t ih =>
      constructor
      · rw [states]
        change (nextAdmitted (states gen t)).card ≤ t + 1
        exact (nextAdmitted_card_le _).trans (by omega)
      · rw [states]
        change (afterOutputRejected _
          (afterQueryRejected _ (states gen t).rejected _) _).card ≤ 2 * (t + 1)
        calc
          _ ≤ (afterQueryRejected _ (states gen t).rejected _).card + 1 :=
            afterOutputRejected_card_le _ _ _
          _ ≤ ((states gen t).rejected.card + 1) + 1 :=
            Nat.add_le_add_right (afterQueryRejected_card_le _ _ _) 1
          _ ≤ 2 * (t + 1) := by omega

private theorem assigned_card_le (gen : FeedbackGenerator) (t : ℕ) :
    ((states gen t).admitted ∪ (states gen t).rejected).card ≤ 3 * t := by
  exact (Finset.card_union_le _ _).trans (by
    have h := state_card_bounds gen t
    omega)

private theorem target_mem_class (gen : FeedbackGenerator) :
    target gen ∈ targetClass :=
  ⟨limitAdmitted gen, limitAdmitted_ordinary gen, rfl⟩

private theorem target_infinite_core (gen : FeedbackGenerator) : (target gen).Infinite := by
  have hp : Function.Injective (fun k : ℕ => 2 ^ k) :=
    Nat.pow_right_injective (by norm_num)
  apply (Set.infinite_range_of_injective hp).mono
  rintro z ⟨k, rfl⟩
  exact Or.inl ⟨k, rfl⟩

noncomputable def orderedTarget (gen : FeedbackGenerator) : Stage3S2B.OrderedLanguage where
  carrier := target gen
  enumeration := Nat.nth (target gen)
  enumeration_injective := (Nat.nth_strictMono (target_infinite_core gen)).injective
  range_enumeration := Nat.range_nth_of_infinite (target_infinite_core gen)

private theorem orderedTarget_inherits (gen : FeedbackGenerator) :
    InheritsAmbientOrder (orderedTarget gen) :=
  Nat.nth_strictMono (target_infinite_core gen)

private theorem structural_negative_witness (gen : FeedbackGenerator) :
    (orderedTarget gen).carrier = target gen ∧
    InheritsAmbientOrder (orderedTarget gen) ∧
    PresentedBy (presenter gen) (transcript gen) ∧
    FollowsProtocol gen (target gen) (transcript gen) ∧
    Clean (transcript gen).presentation (target gen) ∧
    Function.Injective (transcript gen).presentation ∧
    Complete (transcript gen).presentation (target gen) ∧
    scored (target gen) (transcript gen).presentation (transcript gen).output ⊆ core := by
  exact ⟨rfl, orderedTarget_inherits gen, presented_by gen, follows_protocol gen,
    presentation_clean gen, presentation_injective gen, presentation_complete gen,
    scored_subset_core gen⟩


private def ordinaryCode (n : ℕ) : ℕ := 2 * n + 3

private theorem ordinaryCode_injective : Function.Injective ordinaryCode := by
  intro a b h
  simp [ordinaryCode] at h
  omega

private theorem ordinaryCode_mem (n : ℕ) : ordinaryCode n ∈ ordinary := by
  intro h
  obtain ⟨k, hk⟩ := h
  change 2 ^ k = 2 * n + 3 at hk
  by_cases hk0 : k = 0
  · subst k
    simp at hk
  · have heven : Even (2 ^ k) := Nat.even_pow.mpr ⟨by simp, hk0⟩
    rw [hk] at heven
    obtain ⟨w, hw⟩ := heven
    omega


private theorem leastOrdinaryOutside_le (F : Finset ℕ) :
    leastOrdinaryOutside F ≤ 2 * F.card + 3 := by
  classical
  let codes := (Finset.range (F.card + 1)).image ordinaryCode
  have hcodes : codes.card = F.card + 1 := by
    dsimp [codes]
    rw [Finset.card_image_of_injective _ ordinaryCode_injective]
    simp
  obtain ⟨z, hzCodes, hzF⟩ :=
    Finset.exists_mem_not_mem_of_card_lt_card (s := F) (t := codes) (by omega)
  rw [Finset.mem_image] at hzCodes
  obtain ⟨n, hn, rfl⟩ := hzCodes
  have hnlt : n < F.card + 1 := by simpa using hn
  have hnle : n ≤ F.card := by omega
  have hmem : ordinaryCode n ∈ {z : ℕ | z ∈ ordinary ∧ z ∉ F} :=
    ⟨ordinaryCode_mem n, hzF⟩
  unfold leastOrdinaryOutside
  exact (Nat.sInf_le hmem).trans (by dsimp [ordinaryCode]; omega)

private theorem odd_presentation_bound (gen : FeedbackGenerator) (t : ℕ)
    (ht : ¬ Even t) : xStream gen t ≤ 6 * t + 3 := by
  rw [current_x]
  simp only [chooseX, if_neg ht]
  exact (leastOrdinaryOutside_le _).trans (by
    have h := assigned_card_le gen t
    omega)

private theorem odd_presentation_bound_index (gen : FeedbackGenerator) (i : ℕ) :
    xStream gen (2 * i + 1) < 12 * i + 10 := by
  have hodd : ¬ Even (2 * i + 1) := by
    rintro ⟨k, hk⟩
    omega
  have h := odd_presentation_bound gen (2 * i + 1) hodd
  omega

private theorem target_nth_lt_linear (gen : FeedbackGenerator) (n : ℕ) :
    Nat.nth (target gen) n < 12 * n + 10 := by
  classical
  let source := Finset.range (n + 1)
  let values := source.image (fun i => xStream gen (2 * i + 1))
  let counted := (Finset.range (12 * n + 10)).filter (fun z => z ∈ target gen)
  have hvaluesCard : values.card = n + 1 := by
    rw [Finset.card_image_of_injective]
    · simp [source]
    · intro a b hab
      have hindex := presentation_injective gen hab
      omega
  have hsubset : values ⊆ counted := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨i, hi, rfl⟩ := hz
    have hin : i ≤ n := by simp [source] at hi; omega
    dsimp [counted]
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨(odd_presentation_bound_index gen i).trans_le (by omega),
      xStream_mem_target gen (2 * i + 1)⟩
  have hcount : n < Nat.count (target gen) (12 * n + 10) := by
    rw [Nat.count_eq_card_filter_range]
    exact lt_of_lt_of_le (by simpa [hvaluesCard]) (Finset.card_le_card hsubset)
  exact (Nat.lt_nth_iff_count_lt (target_infinite_core gen)).mp hcount


private theorem core_count_le_log (M : ℕ) :
    @Nat.count core (Classical.decPred core) M ≤ Nat.log2 M + 1 := by
  classical
  rw [Nat.count_eq_card_filter_range]
  calc
    ((Finset.range M).filter fun z => z ∈ core).card ≤
        ((Finset.range (Nat.log2 M + 1)).image fun k => 2 ^ k).card := by
      apply Finset.card_le_card
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_range] at hz
      obtain ⟨k, rfl⟩ := hz.2
      rw [Finset.mem_image]
      refine ⟨k, ?_, rfl⟩
      simp only [Finset.mem_range]
      have hklt : 2 ^ k < M := by simpa using hz.1
      have hM : M ≠ 0 := by omega
      have hkM : 2 ^ k ≤ M := Nat.le_of_lt hklt
      exact Nat.lt_succ_of_le ((Nat.le_log2 hM).2 hkM)
    _ ≤ (Finset.range (Nat.log2 M + 1)).card := Finset.card_image_le
    _ = Nat.log2 M + 1 := Finset.card_range _

private theorem core_prefixCount_le_log (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).prefixCount core n ≤ Nat.log2 (12 * n + 10) + 1 := by
  classical
  calc
    (orderedTarget gen).prefixCount core n ≤ @Nat.count core (Classical.decPred core) (12 * n + 10) := by
      rw [Nat.count_eq_card_filter_range]
      unfold GenLimit.KleinbergWei.OrderedLanguage.prefixCount
      apply Finset.card_le_card_of_injOn (orderedTarget gen).enumeration
      · intro i hi
        have hi' := Finset.mem_filter.mp hi
        have hin : i < n := Finset.mem_range.mp hi'.1
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_range.mpr
          ((target_nth_lt_linear gen i).trans_le (by omega)), hi'.2⟩
      · exact (orderedTarget gen).enumeration_injective.injOn
    _ ≤ Nat.log2 (12 * n + 10) + 1 := core_count_le_log _


private theorem tendsto_core_error :
    Tendsto (fun n : ℕ =>
      ((Nat.log2 (12 * n + 10) + 1 : ℕ) : ℝ) / (n : ℝ)) atTop (nhds 0) := by
  let f : ℕ → ℕ := fun n => 12 * n + 10
  have hf : Tendsto f atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    dsimp [f]
    omega
  have hlog : Tendsto (fun n : ℕ =>
      (Nat.log2 (f n) : ℝ) / (f n : ℝ)) atTop (nhds 0) := by
    simpa only [Function.comp_apply] using GenLimit.tendsto_natLog2_div.comp hf
  have hten : Tendsto (fun n : ℕ => (10 : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlinear : Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ)) atTop (nhds 12) := by
    have h : Tendsto (fun n : ℕ => (12 : ℝ) + 10 / (n : ℝ)) atTop (nhds 12) := by
      simpa using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (12 : ℝ)) atTop (nhds 12)).add hten
    apply h.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    dsimp [f]
    push_cast
    field_simp [hn]
  have hmain : Tendsto (fun n : ℕ =>
      (Nat.log2 (f n) : ℝ) / (n : ℝ)) atTop (nhds 0) := by
    have h := hlog.mul hlinear
    convert h using 1
    · apply funext
      intro n
      by_cases hn : n = 0
      · subst n
        simp [f]
      · have hfn : f n ≠ 0 := by simp [f]
        field_simp [hn, hfn]
    · norm_num
  have hone : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hsum := hmain.add hone
  simpa only [f, Nat.cast_add, Nat.cast_one, add_div, zero_add] using hsum

private theorem core_prefixRatio_tendsto_zero (gen : FeedbackGenerator) :
    Tendsto ((orderedTarget gen).prefixRatio core) atTop (nhds 0) := by
  refine squeeze_zero
    (g := fun n : ℕ => ((Nat.log2 (12 * n + 10) + 1 : ℕ) : ℝ) / (n : ℝ))
    (fun n => (orderedTarget gen).prefixRatio_nonneg core n) ?_ tendsto_core_error
  · intro n
    by_cases hn : n = 0
    · subst n
      simp [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio]
    · simp only [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, hn, if_false]
      exact div_le_div_of_nonneg_right
        (by exact_mod_cast core_prefixCount_le_log gen n) (Nat.cast_nonneg n)

private theorem core_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity core = 0 :=
  (core_prefixRatio_tendsto_zero gen).limsup_eq

private theorem scored_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity
      (scored (target gen) (xStream gen) (yStream gen)) = 0 := by
  apply le_antisymm
  · exact ((orderedTarget gen).upperDensity_mono (scored_subset_core gen)).trans_eq
      (core_upperDensity_zero gen)
  · exact (orderedTarget gen).upperDensity_nonneg _

private theorem faithful_negative_witness (gen : FeedbackGenerator) :
    FaithfulNegativeWitness gen (target gen) (presenter gen)
      (transcript gen) (orderedTarget gen) := by
  exact ⟨rfl, orderedTarget_inherits gen, presented_by gen, follows_protocol gen,
    presentation_clean gen, presentation_injective gen, presentation_complete gen,
    scored_upperDensity_zero gen⟩

private theorem negative_claim : NegativeClaim := by
  intro gen _hvalid
  exact ⟨target gen, target_mem_class gen, presenter gen, transcript gen,
    orderedTarget gen, faithful_negative_witness gen⟩

private def encodedTarget (S : Set ℕ) : Language :=
  core ∪ ordinaryCode '' S

private theorem encodedTarget_mem (S : Set ℕ) : encodedTarget S ∈ targetClass := by
  refine ⟨ordinaryCode '' S, ?_, rfl⟩
  rintro z ⟨n, hn, rfl⟩
  exact ordinaryCode_mem n

private theorem encodedTarget_injective : Function.Injective encodedTarget := by
  intro S T h
  ext n
  have hnot : ordinaryCode n ∉ core := ordinaryCode_mem n
  constructor
  · intro hnS
    have hm : ordinaryCode n ∈ encodedTarget T := by
      rw [← h]
      exact Or.inr ⟨n, hnS, rfl⟩
    rcases hm with hm | ⟨m, hmT, hmn⟩
    · exact (hnot hm).elim
    · have : m = n := ordinaryCode_injective hmn
      simpa [this] using hmT
  · intro hnT
    have hm : ordinaryCode n ∈ encodedTarget S := by
      rw [h]
      exact Or.inr ⟨n, hnT, rfl⟩
    rcases hm with hm | ⟨m, hmS, hmn⟩
    · exact (hnot hm).elim
    · have : m = n := ordinaryCode_injective hmn
      simpa [this] using hmS

private theorem targetClass_uncountable : ¬ targetClass.Countable := by
  intro hc
  let f : Set ℕ → targetClass := fun S => ⟨encodedTarget S, encodedTarget_mem S⟩
  have hf : Function.Injective f := by
    intro S T h
    apply encodedTarget_injective
    exact congrArg Subtype.val h
  letI : Countable targetClass := hc.to_subtype
  have hp : Countable (Set ℕ) := hf.countable
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ hp

private theorem uniform_positive : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t => 2 ^ t, Nat.pow_right_injective (a := 2) (by norm_num), 0, ?_⟩
  intro K hK t ht
  obtain ⟨A, hA, rfl⟩ := hK
  exact Or.inl ⟨t, rfl⟩


end Stage3S2BProof

theorem stage3_result : Stage3S2B.MainClaim := by
  exact ⟨Stage3S2BProof.targetClass_uncountable,
    Stage3S2BProof.uniform_positive, Stage3S2BProof.negative_claim⟩
