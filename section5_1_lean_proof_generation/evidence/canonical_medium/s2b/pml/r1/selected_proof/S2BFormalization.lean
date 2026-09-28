import Stage3Model
import Mathlib.Data.Nat.Nth
import GenLimit.Paper39_DenseGeneration.Abstract.Density

open Set Filter
open GenLimit.KleinbergWei

namespace Stage3Proof

open Stage3S2B
noncomputable section
open Classical

lemma oddThree_not_core (n : ℕ) : 2 * n + 3 ∉ core := by
  rintro ⟨k, hk⟩
  cases k with
  | zero => simp at hk
  | succ k =>
      have heven : Even (2 ^ (Nat.succ k)) := by
        exact Nat.even_pow.mpr ⟨by decide, Nat.succ_ne_zero k⟩
      have hodd : Odd (2 * n + 3) := ⟨n + 1, by omega⟩
      have hk' : 2 ^ (Nat.succ k) = 2 * n + 3 := by simpa [Nat.succ_eq_add_one] using hk
      rw [hk'] at heven
      exact (Nat.not_even_iff_odd.mpr hodd) heven

lemma ordinary_infinite : ordinary.Infinite := by
  apply Set.Infinite.mono _ (Set.infinite_range_of_injective (f := fun n : ℕ => 2*n+3) (by
    intro a b h
    dsimp at h
    omega))
  rintro z ⟨n, rfl⟩
  exact oddThree_not_core n

lemma exists_fresh_ordinary (I R : Finset ℕ) : ∃ z, z ∈ ordinary ∧ z ∉ I ∧ z ∉ R := by
  have hfinite : ((I : Set ℕ) ∪ (R : Set ℕ)).Finite := I.finite_toSet.union R.finite_toSet
  have hne := ordinary_infinite.diff hfinite
  rcases hne.nonempty with ⟨z, hzO, hz⟩
  have hz' : z ∉ (I : Set ℕ) ∪ (R : Set ℕ) := hz
  exact ⟨z, hzO, by simpa using fun h => hz' (Or.inl h),
    by simpa using fun h => hz' (Or.inr h)⟩

noncomputable def freshOrdinary (I R : Finset ℕ) : ℕ :=
  Nat.find (exists_fresh_ordinary I R)

lemma freshOrdinary_spec (I R : Finset ℕ) :
    freshOrdinary I R ∈ ordinary ∧ freshOrdinary I R ∉ I ∧ freshOrdinary I R ∉ R :=
  Nat.find_spec (exists_fresh_ordinary I R)

structure Prefix (t : ℕ) where
  presentation : Fin t → ℕ
  query : Fin t → Option ℕ
  answer : Fin t → Option Bool
  output : Fin t → ℕ
  admitted : Finset ℕ
  rejected : Finset ℕ

noncomputable def nextPresentationValue (t : ℕ) (p : Prefix t) : ℕ :=
  if Even t then 2 ^ (t/2) else freshOrdinary p.admitted p.rejected

noncomputable def nextPresentation (t : ℕ) (p : Prefix t) : Fin (t+1) → ℕ :=
  Fin.lastCases (nextPresentationValue t p) p.presentation

noncomputable def nextQuery (gen : FeedbackGenerator) (t : ℕ) (p : Prefix t) : Option ℕ :=
  gen.query t (nextPresentation t p) p.answer

noncomputable def nextAdmitted (t : ℕ) (p : Prefix t) : Finset ℕ :=
  if Even t then p.admitted else insert (nextPresentationValue t p) p.admitted

noncomputable def nextAnswerValue (gen : FeedbackGenerator) (t : ℕ) (p : Prefix t) : Option Bool :=
  (nextQuery gen t p).map fun z => decide (z ∈ core ∨ z ∈ nextAdmitted t p)

noncomputable def nextAnswer (gen : FeedbackGenerator) (t : ℕ) (p : Prefix t) :
    Fin (t+1) → Option Bool :=
  Fin.lastCases (nextAnswerValue gen t p) p.answer

noncomputable def nextOutput (gen : FeedbackGenerator) (t : ℕ) (p : Prefix t) : ℕ :=
  gen.output t (nextPresentation t p) (nextAnswer gen t p)

noncomputable def rejectedAfterQuery (gen : FeedbackGenerator) (t : ℕ) (p : Prefix t) : Finset ℕ :=
  match nextQuery gen t p with
  | none => p.rejected
  | some z => if z ∈ core ∨ z ∈ nextAdmitted t p then p.rejected else insert z p.rejected

noncomputable def nextRejected (gen : FeedbackGenerator) (t : ℕ) (p : Prefix t) : Finset ℕ :=
  let y := nextOutput gen t p
  let rq := rejectedAfterQuery gen t p
  if y ∈ core ∨ y ∈ nextAdmitted t p ∨ y ∈ rq then rq else insert y rq

noncomputable def extend (gen : FeedbackGenerator) (t : ℕ) (p : Prefix t) : Prefix (t+1) :=
  Prefix.mk (nextPresentation t p) (Fin.lastCases (nextQuery gen t p) p.query)
    (nextAnswer gen t p) (Fin.lastCases (nextOutput gen t p) p.output)
    (nextAdmitted t p) (nextRejected gen t p)

noncomputable def prefixes (gen : FeedbackGenerator) : (t : ℕ) → Prefix t
  | 0 => Prefix.mk Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0 ∅ ∅
  | t+1 => extend gen t (prefixes gen t)

noncomputable def adversarialTranscript (gen : FeedbackGenerator) : Transcript where
  presentation t := (prefixes gen (t+1)).presentation (Fin.last t)
  query t := (prefixes gen (t+1)).query (Fin.last t)
  answer t := (prefixes gen (t+1)).answer (Fin.last t)
  output t := (prefixes gen (t+1)).output (Fin.last t)

noncomputable def adversarialTarget (gen : FeedbackGenerator) : Language :=
  core ∪ {z | ∃ t, z ∈ (prefixes gen t).admitted}


@[simp] lemma prefixes_presentation_castSucc (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (prefixes gen (t+1)).presentation i.castSucc = (prefixes gen t).presentation i := by
  simp [prefixes, extend, nextPresentation]

@[simp] lemma prefixes_query_castSucc (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (prefixes gen (t+1)).query i.castSucc = (prefixes gen t).query i := by
  simp [prefixes, extend]

@[simp] lemma prefixes_answer_castSucc (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (prefixes gen (t+1)).answer i.castSucc = (prefixes gen t).answer i := by
  simp [prefixes, extend, nextAnswer]

@[simp] lemma prefixes_output_castSucc (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (prefixes gen (t+1)).output i.castSucc = (prefixes gen t).output i := by
  simp [prefixes, extend]

lemma transcript_prefix_presentation (gen : FeedbackGenerator) (t : ℕ) :
    ∀ i : Fin t, (adversarialTranscript gen).presentation i = (prefixes gen t).presentation i := by
  induction t with
  | zero => intro i; exact i.elim0
  | succ t ih =>
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [adversarialTranscript, prefixes, extend]
      · simpa [adversarialTranscript] using (ih j)

lemma transcript_prefix_query (gen : FeedbackGenerator) (t : ℕ) :
    ∀ i : Fin t, (adversarialTranscript gen).query i = (prefixes gen t).query i := by
  induction t with
  | zero => intro i; exact i.elim0
  | succ t ih =>
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [adversarialTranscript, prefixes, extend]
      · simpa [adversarialTranscript] using (ih j)

lemma transcript_prefix_answer (gen : FeedbackGenerator) (t : ℕ) :
    ∀ i : Fin t, (adversarialTranscript gen).answer i = (prefixes gen t).answer i := by
  induction t with
  | zero => intro i; exact i.elim0
  | succ t ih =>
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [adversarialTranscript, prefixes, extend]
      · simpa [adversarialTranscript] using (ih j)

lemma transcript_prefix_output (gen : FeedbackGenerator) (t : ℕ) :
    ∀ i : Fin t, (adversarialTranscript gen).output i = (prefixes gen t).output i := by
  induction t with
  | zero => intro i; exact i.elim0
  | succ t ih =>
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [adversarialTranscript, prefixes, extend]
      · simpa [adversarialTranscript] using (ih j)


structure PrefixInv (gen : FeedbackGenerator) (t : ℕ) : Prop where
  admitted_ordinary : ∀ z ∈ (prefixes gen t).admitted, z ∈ ordinary
  rejected_ordinary : ∀ z ∈ (prefixes gen t).rejected, z ∈ ordinary
  disjoint : Disjoint (prefixes gen t).admitted (prefixes gen t).rejected
  admitted_presented : ∀ z ∈ (prefixes gen t).admitted,
    ∃ i : Fin t, (prefixes gen t).presentation i = z
  presented_target : ∀ i : Fin t,
    (prefixes gen t).presentation i ∈ core ∨
      (prefixes gen t).presentation i ∈ (prefixes gen t).admitted

lemma admitted_mono_step (gen : FeedbackGenerator) (t : ℕ) :
    (prefixes gen t).admitted ⊆ (prefixes gen (t+1)).admitted := by
  classical
  intro z hz
  simp only [prefixes, extend]
  unfold nextAdmitted
  split <;> simp_all

lemma rejectedAfterQuery_mono (gen : FeedbackGenerator) (t : ℕ) (p : Prefix t) :
    p.rejected ⊆ rejectedAfterQuery gen t p := by
  classical
  intro z hz
  unfold rejectedAfterQuery
  cases hq : nextQuery gen t p with
  | none => exact hz
  | some q =>
      simp only [hq]
      split
      · exact hz
      · exact Finset.mem_insert_of_mem hz

lemma nextRejected_mono_rq (gen : FeedbackGenerator) (t : ℕ) (p : Prefix t) :
    rejectedAfterQuery gen t p ⊆ nextRejected gen t p := by
  classical
  intro z hz
  simp only [nextRejected]
  split
  · exact hz
  · exact Finset.mem_insert_of_mem hz

lemma rejected_mono_step (gen : FeedbackGenerator) (t : ℕ) :
    (prefixes gen t).rejected ⊆ (prefixes gen (t+1)).rejected :=
  fun _ hz => nextRejected_mono_rq gen t _ (rejectedAfterQuery_mono gen t _ hz)

lemma nextAdmitted_ordinary {gen : FeedbackGenerator} {t : ℕ}
    (hI : ∀ z ∈ (prefixes gen t).admitted, z ∈ ordinary) :
    ∀ z ∈ nextAdmitted t (prefixes gen t), z ∈ ordinary := by
  classical
  intro z hz
  unfold nextAdmitted at hz
  by_cases ht : Even t
  · simp [ht] at hz
    exact hI z hz
  · simp [ht] at hz
    rcases hz with rfl | hz
    · simpa [nextPresentationValue, ht] using
        (freshOrdinary_spec (prefixes gen t).admitted (prefixes gen t).rejected).1
    · exact hI z hz

lemma rejectedAfterQuery_ordinary {gen : FeedbackGenerator} {t : ℕ}
    (hR : ∀ z ∈ (prefixes gen t).rejected, z ∈ ordinary) :
    ∀ z ∈ rejectedAfterQuery gen t (prefixes gen t), z ∈ ordinary := by
  classical
  intro z hz
  unfold rejectedAfterQuery at hz
  cases hq : nextQuery gen t (prefixes gen t) with
  | none =>
      rw [hq] at hz
      exact hR z hz
  | some q =>
      rw [hq] at hz
      by_cases hgood : q ∈ core ∨ q ∈ nextAdmitted t (prefixes gen t)
      · simp [hgood] at hz
        exact hR z hz
      · simp [hgood] at hz
        rcases hz with rfl | hz
        · exact fun hzcore => hgood (Or.inl hzcore)
        · exact hR z hz

lemma nextRejected_ordinary {gen : FeedbackGenerator} {t : ℕ}
    (hR : ∀ z ∈ (prefixes gen t).rejected, z ∈ ordinary) :
    ∀ z ∈ nextRejected gen t (prefixes gen t), z ∈ ordinary := by
  classical
  intro z hz
  have hrq := rejectedAfterQuery_ordinary (gen := gen) (t := t) hR
  simp only [nextRejected] at hz
  by_cases hgood : nextOutput gen t (prefixes gen t) ∈ core ∨
      nextOutput gen t (prefixes gen t) ∈ nextAdmitted t (prefixes gen t) ∨
      nextOutput gen t (prefixes gen t) ∈ rejectedAfterQuery gen t (prefixes gen t)
  · simp [hgood] at hz
    exact hrq z hz
  · simp [hgood] at hz
    rcases hz with rfl | hz
    · exact fun hzcore => hgood (Or.inl hzcore)
    · exact hrq z hz

lemma admitted_disjoint_rq {gen : FeedbackGenerator} {t : ℕ}
    (hdis : Disjoint (prefixes gen t).admitted (prefixes gen t).rejected) :
    Disjoint (nextAdmitted t (prefixes gen t))
      (rejectedAfterQuery gen t (prefixes gen t)) := by
  classical
  rw [Finset.disjoint_left]
  intro z hzI hzR
  have old_or_new : z ∈ (prefixes gen t).admitted ∨
      z = freshOrdinary (prefixes gen t).admitted (prefixes gen t).rejected := by
    unfold nextAdmitted nextPresentationValue at hzI
    by_cases ht : Even t
    · exact Or.inl (by simpa [ht] using hzI)
    · simp [ht] at hzI
      rcases hzI with h | h
      · exact Or.inr h
      · exact Or.inl h
  unfold rejectedAfterQuery at hzR
  cases hq : nextQuery gen t (prefixes gen t) with
  | none =>
      rw [hq] at hzR
      rcases old_or_new with hold | rfl
      · exact Finset.disjoint_left.mp hdis hold hzR
      · exact (freshOrdinary_spec _ _).2.2 hzR
  | some q =>
      rw [hq] at hzR
      by_cases hgood : q ∈ core ∨ q ∈ nextAdmitted t (prefixes gen t)
      · simp [hgood] at hzR
        rcases old_or_new with hold | rfl
        · exact Finset.disjoint_left.mp hdis hold hzR
        · exact (freshOrdinary_spec _ _).2.2 hzR
      · simp [hgood] at hzR
        rcases hzR with rfl | hzR
        · exact hgood (Or.inr hzI)
        · rcases old_or_new with hold | rfl
          · exact Finset.disjoint_left.mp hdis hold hzR
          · exact (freshOrdinary_spec _ _).2.2 hzR

lemma next_disjoint {gen : FeedbackGenerator} {t : ℕ}
    (hdis : Disjoint (prefixes gen t).admitted (prefixes gen t).rejected) :
    Disjoint (nextAdmitted t (prefixes gen t)) (nextRejected gen t (prefixes gen t)) := by
  classical
  have hrq := Finset.disjoint_left.mp (admitted_disjoint_rq (gen := gen) (t := t) hdis)
  rw [Finset.disjoint_left]
  intro z hzI hzR
  simp only [nextRejected] at hzR
  by_cases hy : nextOutput gen t (prefixes gen t) ∈ core ∨
      nextOutput gen t (prefixes gen t) ∈ nextAdmitted t (prefixes gen t) ∨
      nextOutput gen t (prefixes gen t) ∈ rejectedAfterQuery gen t (prefixes gen t)
  · simp [hy] at hzR
    exact hrq hzI hzR
  · simp [hy] at hzR
    rcases hzR with rfl | hzR
    · exact hy (Or.inr (Or.inl hzI))
    · exact hrq hzI hzR

lemma prefixInv (gen : FeedbackGenerator) : ∀ t, PrefixInv gen t := by
  classical
  intro t
  induction t with
  | zero => constructor <;> simp [prefixes]
  | succ t ih =>
      constructor
      · exact nextAdmitted_ordinary ih.admitted_ordinary
      · exact nextRejected_ordinary ih.rejected_ordinary
      · exact next_disjoint ih.disjoint
      · intro z hz
        change z ∈ nextAdmitted t (prefixes gen t) at hz
        unfold nextAdmitted at hz
        by_cases ht : Even t
        · rw [if_pos ht] at hz
          obtain ⟨i, hi⟩ := ih.admitted_presented z hz
          exact ⟨i.castSucc, by simpa using hi⟩
        · rw [if_neg ht] at hz
          simp only [Finset.mem_insert] at hz
          rcases hz with rfl | hz
          · exact ⟨Fin.last t, by simp [prefixes, extend, nextPresentation,
                nextPresentationValue, ht]⟩
          · obtain ⟨i, hi⟩ := ih.admitted_presented z hz
            exact ⟨i.castSucc, by simpa using hi⟩
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · by_cases ht : Even t
          · exact Or.inl ⟨t / 2, by simp [prefixes, extend, nextPresentation,
                nextPresentationValue, ht]⟩
          · exact Or.inr (by simp [prefixes, extend, nextPresentation,
                nextPresentationValue, nextAdmitted, ht])
        · rcases ih.presented_target j with h | h
          · exact Or.inl (by simpa using h)
          · exact Or.inr (by
              rw [prefixes_presentation_castSucc]
              exact admitted_mono_step gen t h)


lemma admitted_mono {gen : FeedbackGenerator} {m n : ℕ} (h : m ≤ n) :
    (prefixes gen m).admitted ⊆ (prefixes gen n).admitted := by
  induction n, h using Nat.le_induction with
  | base => exact fun _ hz => hz
  | succ n hmn ih => exact fun _ hz => admitted_mono_step gen n (ih hz)

lemma rejected_mono {gen : FeedbackGenerator} {m n : ℕ} (h : m ≤ n) :
    (prefixes gen m).rejected ⊆ (prefixes gen n).rejected := by
  induction n, h using Nat.le_induction with
  | base => exact fun _ hz => hz
  | succ n hmn ih => exact fun _ hz => rejected_mono_step gen n (ih hz)

lemma rejected_not_target {gen : FeedbackGenerator} {t z : ℕ}
    (hzR : z ∈ (prefixes gen t).rejected) : z ∉ adversarialTarget gen := by
  rintro (hzC | ⟨n, hzI⟩)
  · exact (prefixInv gen t).rejected_ordinary z hzR hzC
  · by_cases hnt : n ≤ t
    · exact Finset.disjoint_left.mp (prefixInv gen t).disjoint
        (admitted_mono hnt hzI) hzR
    · have htn : t ≤ n := Nat.le_of_lt (Nat.lt_of_not_ge hnt)
      exact Finset.disjoint_left.mp (prefixInv gen n).disjoint hzI
        (rejected_mono htn hzR)

lemma query_target_iff {gen : FeedbackGenerator} {t q : ℕ}
    (hq : nextQuery gen t (prefixes gen t) = some q) :
    q ∈ adversarialTarget gen ↔ q ∈ core ∨ q ∈ nextAdmitted t (prefixes gen t) := by
  constructor
  · intro htarget
    by_contra h
    have hRq : q ∈ rejectedAfterQuery gen t (prefixes gen t) := by
      unfold rejectedAfterQuery
      rw [hq]
      simp [h]
    have hRnext : q ∈ (prefixes gen (t+1)).rejected := by
      exact nextRejected_mono_rq gen t _ hRq
    exact rejected_not_target hRnext htarget
  · rintro (hcore | hI)
    · exact Or.inl hcore
    · exact Or.inr ⟨t+1, hI⟩


lemma adversarialTarget_mem_class (gen : FeedbackGenerator) :
    adversarialTarget gen ∈ targetClass := by
  refine ⟨{z | ∃ t, z ∈ (prefixes gen t).admitted}, ?_, rfl⟩
  rintro z ⟨t, hz⟩
  exact (prefixInv gen t).admitted_ordinary z hz

lemma transcript_value (gen : FeedbackGenerator) (t : ℕ) :
    (adversarialTranscript gen).presentation t =
      nextPresentationValue t (prefixes gen t) := by
  simp [adversarialTranscript, prefixes, extend, nextPresentation]

lemma followsProtocol (gen : FeedbackGenerator) :
    FollowsProtocol gen (adversarialTarget gen) (adversarialTranscript gen) := by
  classical
  intro t
  have hp : (fun i : Fin (t+1) => (adversarialTranscript gen).presentation i) =
      nextPresentation t (prefixes gen t) := by
    funext i
    rw [transcript_prefix_presentation gen (t+1)]
    rfl
  have ha : (fun i : Fin t => (adversarialTranscript gen).answer i) =
      (prefixes gen t).answer := by
    funext i
    exact transcript_prefix_answer gen t i
  have ha' : (fun i : Fin (t+1) => (adversarialTranscript gen).answer i) =
      nextAnswer gen t (prefixes gen t) := by
    funext i
    rw [transcript_prefix_answer gen (t+1)]
    rfl
  have hq : (adversarialTranscript gen).query t = nextQuery gen t (prefixes gen t) := by
    simp [adversarialTranscript, prefixes, extend]
  constructor
  · rw [hq, nextQuery, hp, ha]
  constructor
  · rw [hq]
    have hans : (adversarialTranscript gen).answer t =
        nextAnswerValue gen t (prefixes gen t) := by
      simp [adversarialTranscript, prefixes, extend, nextAnswer]
    rw [hans]
    cases hquery : nextQuery gen t (prefixes gen t) with
    | none => simp [nextAnswerValue, hquery]
    | some q =>
        simp only [nextAnswerValue, hquery, Option.map_some]
        unfold membershipAnswer
        have hiff := query_target_iff hquery
        by_cases hmem : q ∈ adversarialTarget gen
        · have hmem' := hiff.mp hmem
          simp [hmem, hmem']
        · have hmem' : ¬(q ∈ core ∨ q ∈ nextAdmitted t (prefixes gen t)) :=
            fun h => hmem (hiff.mpr h)
          simp [hmem, hmem']
  · have hout : (adversarialTranscript gen).output t = nextOutput gen t (prefixes gen t) := by
      simp [adversarialTranscript, prefixes, extend]
    rw [hout, nextOutput, hp, ha']

lemma presentation_clean (gen : FeedbackGenerator) :
    Clean (adversarialTranscript gen).presentation (adversarialTarget gen) := by
  intro t
  have h := (prefixInv gen (t+1)).presented_target (Fin.last t)
  rw [← transcript_prefix_presentation gen (t+1)] at h
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr ⟨t+1, h⟩

lemma presentation_complete (gen : FeedbackGenerator) :
    Complete (adversarialTranscript gen).presentation (adversarialTarget gen) := by
  intro z hz
  rcases hz with hz | ⟨n, hn⟩
  · rcases hz with ⟨k, rfl⟩
    refine ⟨2*k, ?_⟩
    rw [transcript_value]
    simp [nextPresentationValue]
  · obtain ⟨i, hi⟩ := (prefixInv gen n).admitted_presented z hn
    exact ⟨i, (transcript_prefix_presentation gen n i).trans hi⟩

lemma presentation_injective (gen : FeedbackGenerator) :
    Function.Injective (adversarialTranscript gen).presentation := by
  intro i j hij
  wlog hijle : i ≤ j generalizing i j
  · exact (this hij.symm (Nat.le_of_not_ge hijle)).symm
  by_cases heq : i = j
  · exact heq
  have hijlt : i < j := lt_of_le_of_ne hijle heq
  rw [transcript_value, transcript_value] at hij
  by_cases hj : Even j
  · have hji : nextPresentationValue j (prefixes gen j) ∈ core := by
      rw [nextPresentationValue, if_pos hj]
      exact ⟨j/2, rfl⟩
    have hii : nextPresentationValue i (prefixes gen i) ∈ core := by simpa [hij] using hji
    by_cases hi : Even i
    · rw [nextPresentationValue, if_pos hi, nextPresentationValue, if_pos hj] at hij
      rcases hi with ⟨a, ha⟩
      rcases hj with ⟨b, hb⟩
      have hdiv : i / 2 < j / 2 := by omega
      have hp : 2 ^ (i/2) < 2 ^ (j/2) := Nat.pow_lt_pow_right (by decide) hdiv
      omega
    · rw [nextPresentationValue, if_neg hi] at hii
      exact False.elim ((freshOrdinary_spec _ _).1 hii)
  · have hjfresh := freshOrdinary_spec (prefixes gen j).admitted (prefixes gen j).rejected
    unfold nextPresentationValue at hij
    rw [if_neg hj] at hij
    have hiTarget := (prefixInv gen j).presented_target ⟨i, hijlt⟩
    have hiEq : (prefixes gen j).presentation ⟨i, hijlt⟩ =
        (adversarialTranscript gen).presentation i := by
      symm
      exact transcript_prefix_presentation gen j ⟨i, hijlt⟩
    rw [hiEq, transcript_value] at hiTarget
    unfold nextPresentationValue at hiTarget
    rw [hij] at hiTarget
    rcases hiTarget with hc | hI
    · exact False.elim (hjfresh.1 hc)
    · exact False.elim (hjfresh.2.1 hI)

noncomputable def adversarialPresenter (gen : FeedbackGenerator) : CausalPresenter where
  next t _ _ _ _ := (adversarialTranscript gen).presentation t

lemma presentedBy (gen : FeedbackGenerator) :
    PresentedBy (adversarialPresenter gen) (adversarialTranscript gen) := by
  intro t
  rfl

lemma targetClass_uncountable : ¬ targetClass.Countable := by
  intro hc
  let encode : Set ordinary → Language := fun A => core ∪ ((fun z : ordinary => (z : ℕ)) '' A)
  have hsub : Set.range encode ⊆ targetClass := by
    rintro K ⟨A, rfl⟩
    refine ⟨_, ?_, rfl⟩
    rintro z ⟨a, ha, rfl⟩
    exact a.property
  have hrange := hc.mono hsub
  have hinj : Function.Injective encode := by
    intro A B hAB
    ext a
    have haO : (a : ℕ) ∉ core := a.property
    have := Set.ext_iff.mp hAB (a : ℕ)
    simpa [encode, haO] using this
  have hcountA : Set.Countable (Set.univ : Set (Set ordinary)) := by
    have hpre : encode ⁻¹' Set.range encode = Set.univ := by
      ext A
      simp
    rw [← hpre]
    exact hrange.preimage hinj
  haveI : Infinite ordinary := ordinary_infinite.to_subtype
  have hnot : ¬ Countable (Set ordinary) := by
    intro hcountable
    letI : Countable (Set ordinary) := hcountable
    let den : Denumerable ordinary := Classical.choice (nonempty_denumerable ordinary)
    let e : ℕ ≃ ordinary := (@Denumerable.eqv ordinary den).symm
    obtain ⟨f, hf⟩ := (countable_iff_exists_surjective (α := Set ordinary)).mp hcountable
    let diagonal : Set ordinary := {p | p ∉ f (e.symm p)}
    obtain ⟨n, hn⟩ := hf diagonal
    let p : ordinary := e n
    have hdiag : p ∈ diagonal ↔ p ∉ diagonal := by
      have hep : e.symm p = n := by simp [p]
      constructor
      · intro hp
        change p ∉ f (e.symm p) at hp
        rw [hep, hn] at hp
        exact hp
      · intro hp
        change p ∉ f (e.symm p)
        rw [hep, hn]
        exact hp
    by_cases hp : p ∈ diagonal
    · exact (hdiag.mp hp) hp
    · exact hp (hdiag.mpr hp)
  exact hnot (Set.countable_univ_iff.mp hcountA)

lemma uniform_generation : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t => 2^t, ?_, 0, ?_⟩
  · exact Nat.pow_right_injective (by decide)
  · intro K hK t ht
    rcases hK with ⟨A, hA, rfl⟩
    exact Or.inl ⟨t, rfl⟩

lemma admitted_card_le (gen : FeedbackGenerator) : ∀ t,
    (prefixes gen t).admitted.card ≤ t := by
  intro t
  induction t with
  | zero => simp [prefixes]
  | succ t ih =>
      rw [prefixes]
      simp only [extend]
      unfold nextAdmitted
      split
      · omega
      · exact (Finset.card_insert_le _ _).trans (by omega)

lemma rejectedAfterQuery_card_le (gen : FeedbackGenerator) (t : ℕ) (p : Prefix t) :
    (rejectedAfterQuery gen t p).card ≤ p.rejected.card + 1 := by
  classical
  unfold rejectedAfterQuery
  split
  · omega
  · split
    · omega
    · exact Finset.card_insert_le _ _

lemma nextRejected_card_le (gen : FeedbackGenerator) (t : ℕ) (p : Prefix t) :
    (nextRejected gen t p).card ≤ p.rejected.card + 2 := by
  classical
  change (if nextOutput gen t p ∈ core ∨
      nextOutput gen t p ∈ nextAdmitted t p ∨
      nextOutput gen t p ∈ rejectedAfterQuery gen t p then
        rejectedAfterQuery gen t p
      else insert (nextOutput gen t p) (rejectedAfterQuery gen t p)).card ≤ _
  split
  · exact (rejectedAfterQuery_card_le gen t p).trans (by omega)
  · refine (Finset.card_insert_le _ _).trans ?_
    have h := Nat.add_le_add_right (rejectedAfterQuery_card_le gen t p) 1
    omega

lemma rejected_card_le (gen : FeedbackGenerator) : ∀ t,
    (prefixes gen t).rejected.card ≤ 2 * t := by
  intro t
  induction t with
  | zero => simp [prefixes]
  | succ t ih =>
      rw [prefixes]
      simp only [extend]
      exact (nextRejected_card_le gen t _).trans (by omega)

lemma freshOrdinary_le (I R : Finset ℕ) :
    freshOrdinary I R ≤ 2 * (I ∪ R).card + 3 := by
  classical
  let U := I ∪ R
  let candidates := (Finset.range (U.card + 1)).image (fun k => 2 * k + 3)
  have hinj : Set.InjOn (fun k => 2 * k + 3) (Finset.range (U.card + 1)) := by
    intro a ha b hb hab
    dsimp at hab
    omega
  have hcard : candidates.card = U.card + 1 := by
    calc
      candidates.card = (Finset.range (U.card + 1)).card :=
        Finset.card_image_iff.mpr hinj
      _ = U.card + 1 := Finset.card_range _
  have hex : ∃ k < U.card + 1, 2 * k + 3 ∉ U := by
    by_contra h
    push_neg at h
    have hsub : candidates ⊆ U := by
      intro z hz
      simp only [candidates, Finset.mem_image, Finset.mem_range] at hz
      rcases hz with ⟨k, hk, rfl⟩
      exact h k hk
    have hc := Finset.card_le_card hsub
    rw [hcard] at hc
    omega
  rcases hex with ⟨k, hk, hkU⟩
  have hfind := Nat.find_min' (exists_fresh_ordinary I R)
    (show 2 * k + 3 ∈ ordinary ∧ 2 * k + 3 ∉ I ∧ 2 * k + 3 ∉ R by
      refine ⟨oddThree_not_core k, ?_, ?_⟩
      · intro hkI
        exact hkU (Finset.mem_union_left _ hkI)
      · intro hkR
        exact hkU (Finset.mem_union_right _ hkR))
  dsimp [U] at hk
  exact hfind.trans (by omega)

lemma odd_presentation_bound (gen : FeedbackGenerator) (r : ℕ) :
    (adversarialTranscript gen).presentation (2 * r + 1) ≤ 12 * r + 9 := by
  rw [transcript_value, nextPresentationValue, if_neg]
  · have hfresh := freshOrdinary_le
        (prefixes gen (2 * r + 1)).admitted
        (prefixes gen (2 * r + 1)).rejected
    have hUnion := Finset.card_union_le
      (prefixes gen (2 * r + 1)).admitted
      (prefixes gen (2 * r + 1)).rejected
    have hI := admitted_card_le gen (2 * r + 1)
    have hR := rejected_card_le gen (2 * r + 1)
    omega
  · exact Nat.not_even_iff_odd.mpr ⟨r, by omega⟩

lemma target_infinite (gen : FeedbackGenerator) : (adversarialTarget gen).Infinite := by
  apply Set.Infinite.mono _ (Set.infinite_range_of_injective
    (Nat.pow_right_injective (by decide : 1 < 2)))
  intro z hz
  exact Or.inl hz

lemma odd_values_injective (gen : FeedbackGenerator) :
    Function.Injective (fun r => (adversarialTranscript gen).presentation (2 * r + 1)) := by
  intro a b hab
  have htime := presentation_injective gen hab
  omega

lemma target_count_lower (gen : FeedbackGenerator) (n : ℕ) :
    n < Nat.count (fun z => z ∈ adversarialTarget gen) (12 * n + 10) := by
  classical
  let vals := (Finset.range (n + 1)).image
    (fun r => (adversarialTranscript gen).presentation (2 * r + 1))
  have hvalsCard : vals.card = n + 1 := by
    calc
      vals.card = (Finset.range (n + 1)).card :=
        Finset.card_image_of_injective _ (odd_values_injective gen)
      _ = n + 1 := Finset.card_range _
  have hsub : vals ⊆ (Finset.range (12 * n + 10)).filter
      (fun z => z ∈ adversarialTarget gen) := by
    intro z hz
    simp only [vals, Finset.mem_image, Finset.mem_range] at hz
    rcases hz with ⟨r, hr, rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      have hb := odd_presentation_bound gen r
      omega
    · exact presentation_clean gen (2 * r + 1)
  rw [Nat.count_eq_card_filter_range]
  have hc := Finset.card_le_card hsub
  rw [hvalsCard] at hc
  omega

lemma target_nth_lt_linear (gen : FeedbackGenerator) (n : ℕ) :
    Nat.nth (fun z => z ∈ adversarialTarget gen) n < 12 * n + 10 := by
  exact (Nat.lt_nth_iff_count_lt (target_infinite gen)).mp
    (target_count_lower gen n)

noncomputable def orderedTarget (gen : FeedbackGenerator) : Stage3S2B.OrderedLanguage where
  carrier := adversarialTarget gen
  enumeration := Nat.nth (fun z => z ∈ adversarialTarget gen)
  enumeration_injective := Nat.nth_injective (target_infinite gen)
  range_enumeration := Nat.range_nth_of_infinite (target_infinite gen)

lemma orderedTarget_strictMono (gen : FeedbackGenerator) :
    InheritsAmbientOrder (orderedTarget gen) :=
  Nat.nth_strictMono (target_infinite gen)

lemma orderedTarget_core_prefixCount_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).prefixCount core n ≤ Nat.log2 (16 * (n + 1)) + 1 := by
  classical
  let inds := (Finset.range n).filter
    (fun i => (orderedTarget gen).enumeration i ∈ core)
  let logs := inds.image (fun i => Nat.log2 ((orderedTarget gen).enumeration i))
  have hlogInj : Set.InjOn
      (fun i => Nat.log2 ((orderedTarget gen).enumeration i)) inds := by
    intro i hi j hj hij
    have hiCore : (orderedTarget gen).enumeration i ∈ core :=
      (Finset.mem_filter.mp hi).2
    have hjCore : (orderedTarget gen).enumeration j ∈ core :=
      (Finset.mem_filter.mp hj).2
    rcases hiCore with ⟨a, ha⟩
    rcases hjCore with ⟨b, hb⟩
    have hab : a = b := by
      calc
        a = Nat.log2 ((orderedTarget gen).enumeration i) := by rw [← ha, Nat.log2_two_pow]
        _ = Nat.log2 ((orderedTarget gen).enumeration j) := hij
        _ = b := by rw [← hb, Nat.log2_two_pow]
    apply (orderedTarget gen).enumeration_injective
    rw [← ha, ← hb, hab]
  have hlogsCard : logs.card = inds.card := Finset.card_image_iff.mpr hlogInj
  have hsub : logs ⊆ Finset.range (Nat.log2 (16 * (n + 1)) + 1) := by
    intro k hk
    simp only [logs, Finset.mem_image] at hk
    rcases hk with ⟨i, hi, rfl⟩
    apply Finset.mem_range.mpr
    have hiRange : i < n := by simpa using (Finset.mem_filter.mp hi).1
    have hiCore : (orderedTarget gen).enumeration i ∈ core :=
      (Finset.mem_filter.mp hi).2
    rcases hiCore with ⟨a, ha⟩
    have henum : (orderedTarget gen).enumeration i < 16 * (n + 1) := by
      have hmono := (orderedTarget_strictMono gen) hiRange
      have hbound := target_nth_lt_linear gen n
      change Nat.nth (fun z => z ∈ adversarialTarget gen) i < 16 * (n + 1)
      change Nat.nth (fun z => z ∈ adversarialTarget gen) i <
        Nat.nth (fun z => z ∈ adversarialTarget gen) n at hmono
      omega
    rw [← ha] at henum
    have hpow : 2 ^ a ≤ 16 * (n + 1) := Nat.le_of_lt henum
    have hnonzero : 16 * (n + 1) ≠ 0 := by omega
    rw [← ha, Nat.log2_two_pow]
    exact Nat.lt_succ_of_le ((Nat.le_log2 hnonzero).mpr hpow)
  unfold GenLimit.KleinbergWei.OrderedLanguage.prefixCount
  change inds.card ≤ _
  rw [← hlogsCard]
  simpa using Finset.card_le_card hsub

lemma log2_sixteen_succ_le (n : ℕ) (hn : n ≠ 0) :
    Nat.log2 (16 * (n + 1)) + 1 ≤ 6 + Nat.log2 n := by
  have harg : 16 * (n + 1) ≤ 32 * n := by omega
  have hlog := Nat.log_mono_right (b := 2) harg
  have hid : Nat.log2 (32 * n) = Nat.log2 n + 5 := by
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    norm_num [show 32 * n = ((((n * 2) * 2) * 2) * 2) * 2 by ring,
      Nat.log_mul_base, hn, Nat.add_assoc]
  rw [← Nat.log2_eq_log_two, ← Nat.log2_eq_log_two, hid] at hlog
  omega

lemma orderedTarget_core_prefixRatio_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).prefixRatio core n ≤
      ((6 + Nat.log2 n : ℕ) : ℝ) / (n : ℝ) := by
  by_cases hn : n = 0
  · simp [hn]
  · simp only [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, hn, if_false]
    apply div_le_div_of_nonneg_right
    · exact_mod_cast (orderedTarget_core_prefixCount_le gen n).trans
        (log2_sixteen_succ_le n hn)
    · positivity

lemma orderedTarget_core_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity core = 0 := by
  unfold GenLimit.KleinbergWei.OrderedLanguage.upperDensity
  have htendsto : Tendsto ((orderedTarget gen).prefixRatio core) atTop (nhds 0) := by
    apply squeeze_zero
    · exact fun n => (orderedTarget gen).prefixRatio_nonneg core n
    · exact orderedTarget_core_prefixRatio_le gen
    · exact GenLimit.tendsto_countingError_div 6
  exact htendsto.limsup_eq

lemma valid_fresh_output_mem_core (gen : FeedbackGenerator) (t : ℕ)
    (hvalid : (adversarialTranscript gen).output t ∈ adversarialTarget gen)
    (hfresh : (adversarialTranscript gen).output t ∉
      observedThrough (adversarialTranscript gen).presentation t) :
    (adversarialTranscript gen).output t ∈ core := by
  classical
  let y := (adversarialTranscript gen).output t
  have hyOut : y = nextOutput gen t (prefixes gen t) := by
    simp [y, adversarialTranscript, prefixes, extend]
  have hyNotAdmitted : y ∉ nextAdmitted t (prefixes gen t) := by
    intro hyI
    have hyI' : y ∈ (prefixes gen (t+1)).admitted := by
      simpa [prefixes, extend] using hyI
    obtain ⟨i, hi⟩ := (prefixInv gen (t+1)).admitted_presented y hyI'
    apply hfresh
    refine ⟨i, Nat.le_of_lt_succ i.isLt, ?_⟩
    rw [transcript_prefix_presentation gen (t+1) i]
    exact hi
  have hyNotRq : y ∉ rejectedAfterQuery gen t (prefixes gen t) := by
    intro hyRq
    have hyR : y ∈ (prefixes gen (t+1)).rejected := by
      exact nextRejected_mono_rq gen t _ hyRq
    exact rejected_not_target hyR hvalid
  by_contra hyCore
  have hyR : y ∈ (prefixes gen (t+1)).rejected := by
    rw [prefixes]
    change y ∈ nextRejected gen t (prefixes gen t)
    change y ∈ (if nextOutput gen t (prefixes gen t) ∈ core ∨
        nextOutput gen t (prefixes gen t) ∈ nextAdmitted t (prefixes gen t) ∨
        nextOutput gen t (prefixes gen t) ∈ rejectedAfterQuery gen t (prefixes gen t)
      then rejectedAfterQuery gen t (prefixes gen t)
      else insert (nextOutput gen t (prefixes gen t))
        (rejectedAfterQuery gen t (prefixes gen t)))
    rw [if_neg]
    · simpa [← hyOut]
    · rw [← hyOut]
      exact fun h => h.elim hyCore (fun h => h.elim hyNotAdmitted hyNotRq)
  exact rejected_not_target hyR hvalid

lemma scored_subset_core_union_early (gen : FeedbackGenerator) (T : ℕ)
    (heventual : ∀ t, T ≤ t →
      (adversarialTranscript gen).output t ∈ adversarialTarget gen ∧
      (adversarialTranscript gen).output t ∉
        observedThrough (adversarialTranscript gen).presentation t) :
    scored (adversarialTarget gen) (adversarialTranscript gen).presentation
        (adversarialTranscript gen).output ⊆
      core ∪ Set.range (fun i : Fin T => (adversarialTranscript gen).output i) := by
  rintro z ⟨hzTarget, t, hyt, hzFresh⟩
  by_cases ht : T ≤ t
  · left
    rw [← hyt]
    exact valid_fresh_output_mem_core gen t (heventual t ht).1 (heventual t ht).2
  · right
    refine ⟨⟨t, by omega⟩, hyt⟩

lemma scored_upperDensity_zero (gen : FeedbackGenerator) (T : ℕ)
    (heventual : ∀ t, T ≤ t →
      (adversarialTranscript gen).output t ∈ adversarialTarget gen ∧
      (adversarialTranscript gen).output t ∉
        observedThrough (adversarialTranscript gen).presentation t) :
    (orderedTarget gen).upperDensity
      (scored (adversarialTarget gen) (adversarialTranscript gen).presentation
        (adversarialTranscript gen).output) = 0 := by
  let early : Set ℕ := Set.range
    (fun i : Fin T => (adversarialTranscript gen).output i)
  have hfinite : early.Finite := Set.finite_range _
  have hmono := (orderedTarget gen).upperDensity_mono
    (scored_subset_core_union_early gen T heventual)
  have hunion := (orderedTarget gen).upperDensity_union_le core early
  have hearly := (orderedTarget gen).upperDensity_eq_zero_of_finite hfinite
  have hnonneg := (orderedTarget gen).upperDensity_nonneg
    (scored (adversarialTarget gen) (adversarialTranscript gen).presentation
      (adversarialTranscript gen).output)
  rw [orderedTarget_core_upperDensity_zero gen, hearly, add_zero] at hunion
  exact le_antisymm (hmono.trans hunion) hnonneg

end
end Stage3Proof

open Stage3S2B
open Stage3Proof

theorem stage3_result : Stage3S2B.MainClaim := by
  refine ⟨targetClass_uncountable, uniform_generation, ?_⟩
  intro gen hgen
  let K := adversarialTarget gen
  let presenter := adversarialPresenter gen
  let tr := adversarialTranscript gen
  let orderedK := orderedTarget gen
  have hclass : K ∈ targetClass := adversarialTarget_mem_class gen
  have hprotocol : FollowsProtocol gen K tr := followsProtocol gen
  have hclean : Clean tr.presentation K := presentation_clean gen
  have hinjective : Function.Injective tr.presentation := presentation_injective gen
  have hcomplete : Complete tr.presentation K := presentation_complete gen
  obtain ⟨T, hT⟩ := hgen K hclass tr hprotocol hclean hinjective hcomplete
  refine ⟨K, hclass, presenter, tr, orderedK, ?_⟩
  refine ⟨rfl, orderedTarget_strictMono gen, presentedBy gen, hprotocol,
    hclean, hinjective, hcomplete, ?_⟩
  exact scored_upperDensity_zero gen T hT
