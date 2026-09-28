import Stage3Model
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import GenLimit.Paper39_DenseGeneration.Abstract.Density
import Mathlib.Data.Nat.Nth
import Mathlib.Tactic

open Set Filter
open scoped Topology
open GenLimit.KleinbergWei

namespace Stage3S2BFormalization

open Stage3S2B

private theorem oddCode_mem_ordinary (n : ℕ) : 2 * n + 3 ∈ ordinary := by
  intro hcore
  obtain ⟨k, hk⟩ := hcore
  by_cases hk0 : k = 0
  · subst k
    simp at hk
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have heven : Even (2 ^ k) := Nat.even_pow.mpr ⟨by norm_num, hk0⟩
    have hodd : Odd (2 * n + 3) := ⟨n + 1, by omega⟩
    exact (Nat.not_even_iff_odd.mpr hodd) (hk ▸ heven)

private theorem oddCode_injective : Function.Injective (fun n : ℕ => 2 * n + 3) := by
  intro a b h
  have hmul : 2 * a = 2 * b := Nat.add_right_cancel h
  exact Nat.mul_left_cancel (by norm_num) hmul

private theorem targetClass_not_countable : ¬ targetClass.Countable := by
  intro hcount
  let f : Set ℕ → targetClass := fun A =>
    ⟨core ∪ ((fun n : ℕ => 2 * n + 3) '' A),
      ⟨(fun n : ℕ => 2 * n + 3) '' A,
        by rintro _ ⟨n, _, rfl⟩; exact oddCode_mem_ordinary n,
        rfl⟩⟩
  have hf : Function.Injective f := by
    intro A B hAB
    apply Set.ext
    intro n
    have hmem := Set.ext_iff.mp (congrArg Subtype.val hAB) (2 * n + 3)
    change
      ((2 * n + 3 ∈ core) ∨ ∃ a ∈ A, 2 * a + 3 = 2 * n + 3) ↔
      ((2 * n + 3 ∈ core) ∨ ∃ b ∈ B, 2 * b + 3 = 2 * n + 3) at hmem
    have hnotcore : 2 * n + 3 ∉ core := oddCode_mem_ordinary n
    simp only [hnotcore, false_or] at hmem
    constructor
    · intro hn
      have : ∃ a ∈ B, 2 * a + 3 = 2 * n + 3 := hmem.mp ⟨n, hn, rfl⟩
      obtain ⟨a, ha, han⟩ := this
      exact oddCode_injective han ▸ ha
    · intro hn
      have : ∃ a ∈ A, 2 * a + 3 = 2 * n + 3 := hmem.mpr ⟨n, hn, rfl⟩
      obtain ⟨a, ha, han⟩ := this
      exact oddCode_injective han ▸ ha
  letI : Countable targetClass := hcount.to_subtype
  have : Countable (Set ℕ) := hf.countable
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ this

private theorem uniform_positive : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t => 2 ^ t, ?_, 0, ?_⟩
  · exact Nat.pow_right_injective (by norm_num)
  · intro K hK t _
    obtain ⟨A, hA, rfl⟩ := hK
    exact Or.inl ⟨t, rfl⟩


private theorem ordinary_infinite : ordinary.Infinite := by
  apply (Set.infinite_range_of_injective oddCode_injective).mono
  rintro _ ⟨n, rfl⟩
  exact oddCode_mem_ordinary n

private noncomputable def freshOrdinary (I R : Finset ℕ) : ℕ := by
  classical
  exact Nat.find (ordinary_infinite.exists_not_mem_finset (I ∪ R))

private theorem freshOrdinary_spec (I R : Finset ℕ) :
    freshOrdinary I R ∈ ordinary ∧ freshOrdinary I R ∉ I ∪ R := by
  classical
  exact Nat.find_spec (ordinary_infinite.exists_not_mem_finset (I ∪ R))

private theorem freshOrdinary_mem (I R : Finset ℕ) :
    freshOrdinary I R ∈ ordinary :=
  (freshOrdinary_spec I R).1

private theorem freshOrdinary_not_mem (I R : Finset ℕ) :
    freshOrdinary I R ∉ I ∪ R :=
  (freshOrdinary_spec I R).2

private structure RunState (t : ℕ) where
  admitted : Finset ℕ
  rejected : Finset ℕ
  presentation : Fin t → ℕ
  query : Fin t → Option ℕ
  answer : Fin t → Option Bool
  output : Fin t → ℕ

private def initialState : RunState 0 where
  admitted := ∅
  rejected := ∅
  presentation := Fin.elim0
  query := Fin.elim0
  answer := Fin.elim0
  output := Fin.elim0

private noncomputable def roundPresentation {t : ℕ} (s : RunState t) : ℕ :=
  if Even t then 2 ^ (t / 2) else freshOrdinary s.admitted s.rejected

private noncomputable def admittedBefore {t : ℕ} (s : RunState t) : Finset ℕ :=
  if Even t then s.admitted else insert (roundPresentation s) s.admitted

private noncomputable def roundQuery (gen : FeedbackGenerator) {t : ℕ} (s : RunState t) : Option ℕ :=
  gen.query t (Fin.snoc s.presentation (roundPresentation s)) s.answer

private noncomputable def roundAnswer (gen : FeedbackGenerator) {t : ℕ}
    (s : RunState t) : Option Bool := by
  classical
  exact (roundQuery gen s).map fun z => decide (z ∈ core ∨ z ∈ admittedBefore s)

private noncomputable def rejectedAfterQuery (gen : FeedbackGenerator) {t : ℕ}
    (s : RunState t) : Finset ℕ := by
  classical
  exact match roundQuery gen s with
  | none => s.rejected
  | some z =>
      if z ∈ ordinary ∧ z ∉ admittedBefore s ∧ z ∉ s.rejected then
        insert z s.rejected
      else s.rejected

private noncomputable def roundOutput (gen : FeedbackGenerator) {t : ℕ}
    (s : RunState t) : ℕ :=
  gen.output t (Fin.snoc s.presentation (roundPresentation s))
    (Fin.snoc s.answer (roundAnswer gen s))

private noncomputable def rejectedNext (gen : FeedbackGenerator) {t : ℕ}
    (s : RunState t) : Finset ℕ := by
  classical
  let Rq := rejectedAfterQuery gen s
  let y := roundOutput gen s
  exact if y ∈ ordinary ∧ y ∉ admittedBefore s ∧ y ∉ Rq then insert y Rq else Rq

private noncomputable def nextState (gen : FeedbackGenerator) (t : ℕ)
    (s : RunState t) : RunState (t + 1) where
  admitted := admittedBefore s
  rejected := rejectedNext gen s
  presentation := Fin.snoc s.presentation (roundPresentation s)
  query := Fin.snoc s.query (roundQuery gen s)
  answer := Fin.snoc s.answer (roundAnswer gen s)
  output := Fin.snoc s.output (roundOutput gen s)

private noncomputable def runState (gen : FeedbackGenerator) :
    (t : ℕ) → RunState t :=
  fun t => Nat.rec initialState (fun n s => nextState gen n s) t

private theorem runState_succ (gen : FeedbackGenerator) (t : ℕ) :
    runState gen (t + 1) = nextState gen t (runState gen t) := by
  rfl

private noncomputable def adversarialTranscript (gen : FeedbackGenerator) : Transcript where
  presentation := fun t => roundPresentation (runState gen t)
  query := fun t => roundQuery gen (runState gen t)
  answer := fun t => roundAnswer gen (runState gen t)
  output := fun t => roundOutput gen (runState gen t)

private theorem runState_presentation (gen : FeedbackGenerator) (t : ℕ)
    (i : Fin t) :
    (runState gen t).presentation i =
      (adversarialTranscript gen).presentation i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      rw [runState_succ]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [nextState, adversarialTranscript]
      · simpa [nextState, adversarialTranscript] using ih j

private theorem runState_answer (gen : FeedbackGenerator) (t : ℕ)
    (i : Fin t) :
    (runState gen t).answer i = (adversarialTranscript gen).answer i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      rw [runState_succ]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [nextState, adversarialTranscript]
      · simpa [nextState, adversarialTranscript] using ih j

private theorem runState_query (gen : FeedbackGenerator) (t : ℕ)
    (i : Fin t) :
    (runState gen t).query i = (adversarialTranscript gen).query i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      rw [runState_succ]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [nextState, adversarialTranscript]
      · simpa [nextState, adversarialTranscript] using ih j

private theorem runState_output (gen : FeedbackGenerator) (t : ℕ)
    (i : Fin t) :
    (runState gen t).output i = (adversarialTranscript gen).output i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      rw [runState_succ]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [nextState, adversarialTranscript]
      · simpa [nextState, adversarialTranscript] using ih j


private def StateGood (gen : FeedbackGenerator) (t : ℕ) (s : RunState t) : Prop :=
  (∀ z ∈ s.admitted, z ∈ ordinary) ∧
  (∀ z ∈ s.rejected, z ∈ ordinary) ∧
  Disjoint s.admitted s.rejected ∧
  (∀ z ∈ s.admitted, ∃ i : Fin t, s.presentation i = z)

private theorem initialState_good (gen : FeedbackGenerator) : StateGood gen 0 initialState := by
  simp [StateGood, initialState]

private theorem admittedBefore_subset_ordinary {gen : FeedbackGenerator} {t : ℕ}
    {s : RunState t} (hs : StateGood gen t s) :
    ∀ z ∈ admittedBefore s, z ∈ ordinary := by
  intro z hz
  by_cases he : Even t
  · rw [admittedBefore, if_pos he] at hz
    exact hs.1 z hz
  · simp only [admittedBefore, he, if_false, Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · simp [roundPresentation, he, freshOrdinary_mem]
    · exact hs.1 z hz

private theorem admittedBefore_disjoint_rejected {gen : FeedbackGenerator} {t : ℕ}
    {s : RunState t} (hs : StateGood gen t s) :
    Disjoint (admittedBefore s) s.rejected := by
  rw [Finset.disjoint_left]
  intro z hzI hzR
  by_cases he : Even t
  · rw [admittedBefore, if_pos he] at hzI
    exact (Finset.disjoint_left.mp hs.2.2.1) hzI hzR
  · simp only [admittedBefore, he, if_false, Finset.mem_insert] at hzI
    rcases hzI with rfl | hzI
    · rw [roundPresentation, if_neg he] at hzR
      exact (freshOrdinary_not_mem s.admitted s.rejected)
        (Finset.mem_union_right _ hzR)
    · exact (Finset.disjoint_left.mp hs.2.2.1) hzI hzR

private theorem rejectedAfterQuery_subset_ordinary {gen : FeedbackGenerator} {t : ℕ}
    {s : RunState t} (hs : StateGood gen t s) :
    ∀ z ∈ rejectedAfterQuery gen s, z ∈ ordinary := by
  classical
  intro z hz
  unfold rejectedAfterQuery at hz
  split at hz
  · exact hs.2.1 z hz
  · split at hz
    · rcases Finset.mem_insert.mp hz with rfl | hz
      · exact ‹z ∈ ordinary ∧ z ∉ admittedBefore s ∧ z ∉ s.rejected›.1
      · exact hs.2.1 z hz
    · exact hs.2.1 z hz

private theorem admittedBefore_disjoint_rejectedAfterQuery
    {gen : FeedbackGenerator} {t : ℕ} {s : RunState t}
    (hs : StateGood gen t s) :
    Disjoint (admittedBefore s) (rejectedAfterQuery gen s) := by
  classical
  rw [Finset.disjoint_left]
  intro z hzI hzR
  unfold rejectedAfterQuery at hzR
  split at hzR
  · exact (Finset.disjoint_left.mp (admittedBefore_disjoint_rejected hs)) hzI hzR
  · split at hzR
    · rcases Finset.mem_insert.mp hzR with rfl | hzR
      · simp_all
      · exact (Finset.disjoint_left.mp (admittedBefore_disjoint_rejected hs)) hzI hzR
    · exact (Finset.disjoint_left.mp (admittedBefore_disjoint_rejected hs)) hzI hzR

private theorem rejectedNext_subset_ordinary {gen : FeedbackGenerator} {t : ℕ}
    {s : RunState t} (hs : StateGood gen t s) :
    ∀ z ∈ rejectedNext gen s, z ∈ ordinary := by
  classical
  intro z hz
  simp only [rejectedNext] at hz
  split at hz
  · rcases Finset.mem_insert.mp hz with rfl | hz
    · exact ‹roundOutput gen s ∈ ordinary ∧ _›.1
    · exact rejectedAfterQuery_subset_ordinary hs z hz
  · exact rejectedAfterQuery_subset_ordinary hs z hz

private theorem admittedBefore_disjoint_rejectedNext
    {gen : FeedbackGenerator} {t : ℕ} {s : RunState t}
    (hs : StateGood gen t s) :
    Disjoint (admittedBefore s) (rejectedNext gen s) := by
  classical
  rw [Finset.disjoint_left]
  intro z hzI hzR
  simp only [rejectedNext] at hzR
  split at hzR
  · rcases Finset.mem_insert.mp hzR with rfl | hzR
    · simp_all
    · exact (Finset.disjoint_left.mp
        (admittedBefore_disjoint_rejectedAfterQuery hs)) hzI hzR
  · exact (Finset.disjoint_left.mp
      (admittedBefore_disjoint_rejectedAfterQuery hs)) hzI hzR

private theorem stateGood_next {gen : FeedbackGenerator} {t : ℕ}
    {s : RunState t} (hs : StateGood gen t s) :
    StateGood gen (t + 1) (nextState gen t s) := by
  unfold StateGood nextState
  dsimp only
  refine ⟨admittedBefore_subset_ordinary hs,
    rejectedNext_subset_ordinary hs,
    admittedBefore_disjoint_rejectedNext hs, ?_⟩
  intro z hz
  by_cases he : Even t
  · have hzold : z ∈ s.admitted := by simpa [admittedBefore, he] using hz
    obtain ⟨i, hi⟩ := hs.2.2.2 z hzold
    exact ⟨i.castSucc, by simpa [nextState] using hi⟩
  · simp only [admittedBefore, he, if_false, Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · exact ⟨Fin.last t, by simp [nextState]⟩
    · obtain ⟨i, hi⟩ := hs.2.2.2 z hz
      exact ⟨i.castSucc, by simpa [nextState] using hi⟩

private theorem runState_good (gen : FeedbackGenerator) (t : ℕ) :
    StateGood gen t (runState gen t) := by
  induction t with
  | zero => exact initialState_good gen
  | succ t ih =>
      rw [runState_succ]
      exact stateGood_next ih

private theorem admitted_mono_step (gen : FeedbackGenerator) (t : ℕ) :
    (runState gen t).admitted ⊆ (runState gen (t + 1)).admitted := by
  rw [runState_succ]
  intro z hz
  by_cases he : Even t
  · simpa [nextState, admittedBefore, he] using hz
  · simp [nextState, admittedBefore, he, hz]

private theorem rejected_mono_step (gen : FeedbackGenerator) (t : ℕ) :
    (runState gen t).rejected ⊆ (runState gen (t + 1)).rejected := by
  classical
  rw [runState_succ]
  intro z hz
  have hq : z ∈ rejectedAfterQuery gen (runState gen t) := by
    simp only [rejectedAfterQuery]
    split
    · exact hz
    · split
      · exact Finset.mem_insert_of_mem hz
      · exact hz
  change z ∈ rejectedNext gen (runState gen t)
  simp only [rejectedNext]
  split <;> simp_all

private theorem admitted_mono (gen : FeedbackGenerator) {a b : ℕ} (hab : a ≤ b) :
    (runState gen a).admitted ⊆ (runState gen b).admitted := by
  induction b, hab using Nat.le_induction with
  | base => exact fun _ h => h
  | succ b hab ih => exact fun z hz => admitted_mono_step gen b (ih hz)

private theorem rejected_mono (gen : FeedbackGenerator) {a b : ℕ} (hab : a ≤ b) :
    (runState gen a).rejected ⊆ (runState gen b).rejected := by
  induction b, hab using Nat.le_induction with
  | base => exact fun _ h => h
  | succ b hab ih => exact fun z hz => rejected_mono_step gen b (ih hz)

private noncomputable def admittedLimit (gen : FeedbackGenerator) : Language :=
  {z | ∃ t, z ∈ (runState gen t).admitted}

private noncomputable def adversarialTarget (gen : FeedbackGenerator) : Language :=
  core ∪ admittedLimit gen


private theorem admittedLimit_subset_ordinary (gen : FeedbackGenerator) :
    admittedLimit gen ⊆ ordinary := by
  rintro z ⟨t, hz⟩
  exact (runState_good gen t).1 z hz

private theorem rejected_not_admittedLimit (gen : FeedbackGenerator) {t z : ℕ}
    (hz : z ∈ (runState gen t).rejected) : z ∉ admittedLimit gen := by
  rintro ⟨u, hu⟩
  let m := max t u
  have hz' : z ∈ (runState gen m).rejected := rejected_mono gen (le_max_left _ _) hz
  have hu' : z ∈ (runState gen m).admitted := admitted_mono gen (le_max_right _ _) hu
  exact (Finset.disjoint_left.mp (runState_good gen m).2.2.1) hu' hz'

private theorem admittedBefore_subset_limit (gen : FeedbackGenerator) (t : ℕ) :
    ∀ z ∈ admittedBefore (runState gen t), z ∈ admittedLimit gen := by
  intro z hz
  exact ⟨t + 1, by simpa [runState_succ, nextState] using hz⟩

private theorem targetClass_adversarial (gen : FeedbackGenerator) :
    adversarialTarget gen ∈ targetClass := by
  exact ⟨admittedLimit gen, admittedLimit_subset_ordinary gen, rfl⟩

private theorem query_negative_rejected (gen : FeedbackGenerator) (t z : ℕ)
    (hq : roundQuery gen (runState gen t) = some z)
    (hzcore : z ∉ core)
    (hzI : z ∉ admittedBefore (runState gen t)) :
    z ∈ (runState gen (t + 1)).rejected := by
  classical
  rw [runState_succ]
  change z ∈ rejectedNext gen (runState gen t)
  have hzordinary : z ∈ ordinary := hzcore
  have hqrej : z ∈ rejectedAfterQuery gen (runState gen t) := by
    simp only [rejectedAfterQuery, hq]
    by_cases hzR : z ∈ (runState gen t).rejected
    · split
      · exact Finset.mem_insert_of_mem hzR
      · exact hzR
    · simp [hzordinary, hzI, hzR]
  simp only [rejectedNext]
  split
  · exact Finset.mem_insert_of_mem hqrej
  · exact hqrej

private theorem followsProtocol_adversarial (gen : FeedbackGenerator) :
    FollowsProtocol gen (adversarialTarget gen) (adversarialTranscript gen) := by
  intro t
  have hp : (fun i : Fin (t + 1) => (adversarialTranscript gen).presentation i) =
      Fin.snoc (runState gen t).presentation (roundPresentation (runState gen t)) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [adversarialTranscript]
    · simpa using (runState_presentation gen t j).symm
  have ha : (fun i : Fin t => (adversarialTranscript gen).answer i) =
      (runState gen t).answer := by
    funext i
    exact (runState_answer gen t i).symm
  have haa : (fun i : Fin (t + 1) => (adversarialTranscript gen).answer i) =
      Fin.snoc (runState gen t).answer (roundAnswer gen (runState gen t)) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [adversarialTranscript]
    · simpa using (runState_answer gen t j).symm
  refine ⟨?_, ?_, ?_⟩
  · simp only [adversarialTranscript, roundQuery]
    congr 1
    · exact hp.symm
    · exact ha.symm
  · simp only [adversarialTranscript, roundAnswer]
    cases hq : roundQuery gen (runState gen t) with
    | none => simp [hq]
    | some z =>
        simp only [hq, Option.map_some, membershipAnswer]
        congr 2
        apply propext
        constructor
        · intro hz
          rcases hz with hz | hz
          · exact Or.inl hz
          · exact Or.inr (admittedBefore_subset_limit gen t z hz)
        · intro hz
          rcases hz with hz | hz
          · exact Or.inl hz
          · by_contra hbefore
            have hzcore : z ∉ core := fun hc => hbefore (Or.inl hc)
            have hzI : z ∉ admittedBefore (runState gen t) :=
              fun hi => hbefore (Or.inr hi)
            have hzrej := query_negative_rejected gen t z hq hzcore hzI
            exact rejected_not_admittedLimit gen hzrej hz
  · simp only [adversarialTranscript, roundOutput]
    congr 1
    · exact hp.symm
    · exact haa.symm


private theorem presentation_even (gen : FeedbackGenerator) {t : ℕ} (ht : Even t) :
    (adversarialTranscript gen).presentation t = 2 ^ (t / 2) := by
  simp [adversarialTranscript, roundPresentation, ht]

private theorem presentation_odd_ordinary (gen : FeedbackGenerator) {t : ℕ}
    (ht : ¬ Even t) : (adversarialTranscript gen).presentation t ∈ ordinary := by
  simp [adversarialTranscript, roundPresentation, ht, freshOrdinary_mem]

private theorem presentation_odd_not_admitted (gen : FeedbackGenerator) {t : ℕ}
    (ht : ¬ Even t) :
    (adversarialTranscript gen).presentation t ∉ (runState gen t).admitted := by
  simp only [adversarialTranscript, roundPresentation, ht, if_false]
  intro h
  exact freshOrdinary_not_mem (runState gen t).admitted (runState gen t).rejected
    (Finset.mem_union_left _ h)

private theorem presentation_odd_admitted_next (gen : FeedbackGenerator) {t : ℕ}
    (ht : ¬ Even t) :
    (adversarialTranscript gen).presentation t ∈ (runState gen (t + 1)).admitted := by
  rw [runState_succ]
  simp [nextState, admittedBefore, adversarialTranscript, roundPresentation, ht]

private theorem clean_adversarial (gen : FeedbackGenerator) :
    Clean (adversarialTranscript gen).presentation (adversarialTarget gen) := by
  intro t
  by_cases ht : Even t
  · exact Or.inl ⟨t / 2, (presentation_even gen ht).symm⟩
  · exact Or.inr ⟨t + 1, presentation_odd_admitted_next gen ht⟩

private theorem complete_adversarial (gen : FeedbackGenerator) :
    Complete (adversarialTranscript gen).presentation (adversarialTarget gen) := by
  intro z hz
  rcases hz with hz | hz
  · obtain ⟨k, rfl⟩ := hz
    refine ⟨2 * k, ?_⟩
    have he : Even (2 * k) := ⟨k, by omega⟩
    rw [presentation_even gen he]
    congr 1
    omega
  · obtain ⟨t, ht⟩ := hz
    obtain ⟨i, hi⟩ := (runState_good gen t).2.2.2 z ht
    exact ⟨i, (runState_presentation gen t i).symm.trans hi⟩

private theorem presentation_injective (gen : FeedbackGenerator) :
    Function.Injective (adversarialTranscript gen).presentation := by
  intro a b hab
  rcases lt_trichotomy a b with hablt | rfl | hblt
  · exfalso
    by_cases hb : Even b
    · by_cases ha : Even a
      · have hp := hab
        rw [presentation_even gen ha, presentation_even gen hb] at hp
        have hdiv : a / 2 = b / 2 := Nat.pow_right_injective (by norm_num) hp
        obtain ⟨ra, hra⟩ := even_iff_exists_two_mul.mp ha
        obtain ⟨rb, hrb⟩ := even_iff_exists_two_mul.mp hb
        omega
      · have haOrd := presentation_odd_ordinary gen ha
        have hbCore : (adversarialTranscript gen).presentation b ∈ core :=
          ⟨b / 2, (presentation_even gen hb).symm⟩
        exact haOrd (hab ▸ hbCore)
    · have hbnot := presentation_odd_not_admitted gen hb
      by_cases ha : Even a
      · have haCore : (adversarialTranscript gen).presentation a ∈ core :=
          ⟨a / 2, (presentation_even gen ha).symm⟩
        have hbOrd := presentation_odd_ordinary gen hb
        exact hbOrd (hab ▸ haCore)
      · have haAdm := presentation_odd_admitted_next gen ha
        have haAdmB := admitted_mono gen (by omega : a + 1 ≤ b) haAdm
        exact hbnot (hab ▸ haAdmB)
  · rfl
  · exact (presentation_injective gen hab.symm).symm

private noncomputable def adversarialPresenter (gen : FeedbackGenerator) : CausalPresenter where
  next := fun t _ _ _ _ => (adversarialTranscript gen).presentation t

private theorem presentedBy_adversarial (gen : FeedbackGenerator) :
    PresentedBy (adversarialPresenter gen) (adversarialTranscript gen) := by
  intro t
  rfl

private theorem admittedBefore_observed (gen : FeedbackGenerator) (t z : ℕ)
    (hz : z ∈ admittedBefore (runState gen t)) :
    z ∈ observedThrough (adversarialTranscript gen).presentation t := by
  by_cases he : Even t
  · have hzold : z ∈ (runState gen t).admitted := by
      simpa [admittedBefore, he] using hz
    obtain ⟨i, hi⟩ := (runState_good gen t).2.2.2 z hzold
    exact ⟨i, i.isLt.le, (runState_presentation gen t i).symm.trans hi⟩
  · simp only [admittedBefore, he, if_false, Finset.mem_insert] at hz
    rcases hz with rfl | hzold
    · exact ⟨t, le_rfl, rfl⟩
    · obtain ⟨i, hi⟩ := (runState_good gen t).2.2.2 z hzold
      exact ⟨i, i.isLt.le, (runState_presentation gen t i).symm.trans hi⟩

private theorem output_ordinary_rejected (gen : FeedbackGenerator) (t : ℕ)
    (hordinary : roundOutput gen (runState gen t) ∈ ordinary)
    (hnot : roundOutput gen (runState gen t) ∉ admittedBefore (runState gen t)) :
    roundOutput gen (runState gen t) ∈ (runState gen (t + 1)).rejected := by
  classical
  rw [runState_succ]
  change roundOutput gen (runState gen t) ∈ rejectedNext gen (runState gen t)
  simp only [rejectedNext]
  by_cases hq : roundOutput gen (runState gen t) ∈
      rejectedAfterQuery gen (runState gen t)
  · split
    · exact Finset.mem_insert_of_mem hq
    · exact hq
  · simp [hordinary, hnot, hq]

private theorem scored_subset_core (gen : FeedbackGenerator) :
    scored (adversarialTarget gen)
      (adversarialTranscript gen).presentation
      (adversarialTranscript gen).output ⊆ core := by
  intro z hz
  rcases hz with ⟨hzK, t, hyt, hnotobs⟩
  by_contra hzcore
  have hzordinary : z ∈ ordinary := hzcore
  have hzlimit : z ∈ admittedLimit gen := by
    rcases hzK with hzK | hzK
    · exact (hzcore hzK).elim
    · exact hzK
  have hnotbefore : z ∉ admittedBefore (runState gen t) := by
    intro hbefore
    exact hnotobs (admittedBefore_observed gen t z hbefore)
  have hyround : roundOutput gen (runState gen t) = z := by
    simpa [adversarialTranscript] using hyt
  have hzrej : z ∈ (runState gen (t + 1)).rejected := by
    rw [← hyround]
    exact output_ordinary_rejected gen t (hyround ▸ hzordinary) (hyround ▸ hnotbefore)
  exact rejected_not_admittedLimit gen hzrej hzlimit

private theorem admitted_card_le (gen : FeedbackGenerator) (t : ℕ) :
    (runState gen t).admitted.card ≤ t := by
  induction t with
  | zero => simp [runState, initialState]
  | succ t ih =>
      rw [runState_succ]
      change (admittedBefore (runState gen t)).card ≤ t + 1
      by_cases he : Even t
      · simpa [admittedBefore, he] using ih.trans (Nat.le_succ t)
      · simpa [admittedBefore, he] using
          (Finset.card_insert_le (roundPresentation (runState gen t))
            (runState gen t).admitted).trans (Nat.add_le_add_right ih 1)

private theorem rejectedAfterQuery_card_le (gen : FeedbackGenerator) {t : ℕ}
    (s : RunState t) :
    (rejectedAfterQuery gen s).card ≤ s.rejected.card + 1 := by
  classical
  unfold rejectedAfterQuery
  split
  · omega
  · split
    · exact Finset.card_insert_le _ _
    · omega

private theorem rejectedNext_card_le (gen : FeedbackGenerator) {t : ℕ}
    (s : RunState t) :
    (rejectedNext gen s).card ≤ s.rejected.card + 2 := by
  classical
  let Rq := rejectedAfterQuery gen s
  let y := roundOutput gen s
  change (if y ∈ ordinary ∧ y ∉ admittedBefore s ∧ y ∉ Rq then
    insert y Rq else Rq).card ≤ s.rejected.card + 2
  split
  · exact (Finset.card_insert_le _ _).trans
      (Nat.add_le_add_right (rejectedAfterQuery_card_le gen s) 1)
  · exact (rejectedAfterQuery_card_le gen s).trans (by omega)

private theorem rejected_card_le (gen : FeedbackGenerator) (t : ℕ) :
    (runState gen t).rejected.card ≤ 2 * t := by
  induction t with
  | zero => simp [runState, initialState]
  | succ t ih =>
      rw [runState_succ]
      exact (rejectedNext_card_le gen (runState gen t)).trans (by omega)

private theorem assigned_card_le (gen : FeedbackGenerator) (t : ℕ) :
    ((runState gen t).admitted ∪ (runState gen t).rejected).card ≤ 3 * t := by
  exact (Finset.card_union_le _ _).trans (by
    have hi := admitted_card_le gen t
    have hr := rejected_card_le gen t
    omega)

private theorem freshOrdinary_le_assigned (I R : Finset ℕ) :
    freshOrdinary I R ≤ 2 * (I ∪ R).card + 3 := by
  classical
  let candidates := (Finset.range ((I ∪ R).card + 1)).image (fun n : ℕ => 2 * n + 3)
  have hcard : candidates.card = (I ∪ R).card + 1 := by
    simp [candidates, Finset.card_image_of_injective _ oddCode_injective]
  have hex : ∃ z ∈ candidates, z ∉ I ∪ R := by
    by_contra h
    push_neg at h
    have hsub : candidates ⊆ I ∪ R := by
      intro z hz
      exact h z hz
    have := Finset.card_le_card hsub
    omega
  obtain ⟨z, hzC, hznot⟩ := hex
  rcases Finset.mem_image.mp hzC with ⟨j, hj, rfl⟩
  have hjlt : j < (I ∪ R).card + 1 := Finset.mem_range.mp hj
  have hjle : j ≤ (I ∪ R).card := by omega
  calc
    freshOrdinary I R ≤ 2 * j + 3 := by
      unfold freshOrdinary
      exact Nat.find_min' (ordinary_infinite.exists_not_mem_finset (I ∪ R))
        ⟨oddCode_mem_ordinary j, hznot⟩
    _ ≤ 2 * (I ∪ R).card + 3 := by omega

private theorem odd_admission_bound (gen : FeedbackGenerator) (r : ℕ) :
    (adversarialTranscript gen).presentation (2 * r + 1) ≤ 12 * r + 9 := by
  have hodd : ¬ Even (2 * r + 1) :=
    Nat.not_even_iff_odd.mpr ⟨r, rfl⟩
  simp only [adversarialTranscript, roundPresentation, hodd, if_false]
  calc
    freshOrdinary (runState gen (2 * r + 1)).admitted
        (runState gen (2 * r + 1)).rejected
        ≤ 2 * ((runState gen (2 * r + 1)).admitted ∪
          (runState gen (2 * r + 1)).rejected).card + 3 :=
      freshOrdinary_le_assigned _ _
    _ ≤ 12 * r + 9 := by
      have h := assigned_card_le gen (2 * r + 1)
      omega

private theorem adversarialTarget_infinite (gen : FeedbackGenerator) :
    (adversarialTarget gen).Infinite := by
  have hpow : Function.Injective (fun k : ℕ => 2 ^ k) :=
    Nat.pow_right_injective (by norm_num)
  apply (Set.infinite_range_of_injective hpow).mono
  exact Set.subset_union_left

private noncomputable def orderedAdversarialTarget
    (gen : FeedbackGenerator) : Stage3S2B.OrderedLanguage := by
  classical
  exact {
    carrier := adversarialTarget gen
    enumeration := Nat.nth (fun z => z ∈ adversarialTarget gen)
    enumeration_injective := Nat.nth_injective (adversarialTarget_infinite gen)
    range_enumeration := Nat.range_nth_of_infinite (adversarialTarget_infinite gen) }

private theorem orderedAdversarialTarget_strictMono (gen : FeedbackGenerator) :
    InheritsAmbientOrder (orderedAdversarialTarget gen) := by
  exact Nat.nth_strictMono (adversarialTarget_infinite gen)

private theorem oddPresentation_injective (gen : FeedbackGenerator) :
    Function.Injective (fun r : ℕ =>
      (adversarialTranscript gen).presentation (2 * r + 1)) := by
  intro a b hab
  have := presentation_injective gen hab
  omega

private noncomputable def adversarialCount (gen : FeedbackGenerator) (n : ℕ) : ℕ := by
  classical
  exact Nat.count (fun z => z ∈ adversarialTarget gen) n

private theorem target_count_lower (gen : FeedbackGenerator) (n : ℕ) :
    n + 1 ≤ adversarialCount gen (12 * n + 10) := by
  classical
  let admissions := (Finset.range (n + 1)).image fun r : ℕ =>
    (adversarialTranscript gen).presentation (2 * r + 1)
  have hcard : admissions.card = n + 1 := by
    simp [admissions, Finset.card_image_of_injective _ (oddPresentation_injective gen)]
  have hsub : admissions ⊆
      (Finset.range (12 * n + 10)).filter
        (fun z => z ∈ adversarialTarget gen) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨r, hr, rfl⟩
    have hrle : r ≤ n := by
      have : r < n + 1 := Finset.mem_range.mp hr
      omega
    have hbound := odd_admission_bound gen r
    have htarget := clean_adversarial gen (2 * r + 1)
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · omega
    · exact htarget
  unfold adversarialCount
  rw [Nat.count_eq_card_filter_range]
  rw [← hcard]
  exact Finset.card_le_card hsub

private theorem ordered_enumeration_bound (gen : FeedbackGenerator) (n : ℕ) :
    (orderedAdversarialTarget gen).enumeration n ≤ 12 * n + 9 := by
  classical
  have hcount := target_count_lower gen n
  have hlt : n < adversarialCount gen (12 * n + 10) := by
    omega
  have hnth : Nat.nth (fun z => z ∈ adversarialTarget gen) n < 12 * n + 10 := by
    apply (Nat.lt_nth_iff_count_lt (adversarialTarget_infinite gen)).mp
    simpa [adversarialCount] using hlt
  exact Nat.le_of_lt_succ (by simpa only [Nat.add_assoc] using hnth)

private theorem log2_linear_bound (n : ℕ) (hn : n ≠ 0) :
    Nat.log2 (12 * n + 9) + 1 ≤ Nat.log2 n + 6 := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hnext : n < 2 ^ (Nat.log2 n + 1) := by
    exact (Nat.log2_lt hn).mp (Nat.lt_succ_self (Nat.log2 n))
  have hB : 12 * n + 9 ≠ 0 := by omega
  have hlt : Nat.log2 (12 * n + 9) < Nat.log2 n + 6 := by
    apply (Nat.log2_lt hB).mpr
    rw [show Nat.log2 n + 6 = (Nat.log2 n + 1) + 5 by omega, pow_add]
    norm_num
    have hp : 0 < 2 ^ (Nat.log2 n + 1) := pow_pos (by norm_num) _
    omega
  omega

private theorem core_prefixCount_le (gen : FeedbackGenerator) (n : ℕ) (hn : n ≠ 0) :
    (orderedAdversarialTarget gen).prefixCount core n ≤ Nat.log2 n + 6 := by
  classical
  let indices := (Finset.range n).filter fun i =>
    (orderedAdversarialTarget gen).enumeration i ∈ core
  let exponent := fun i : ℕ => Nat.log2 ((orderedAdversarialTarget gen).enumeration i)
  have hinj : Set.InjOn exponent (↑indices : Set ℕ) := by
    intro i hi j hj hij
    have hicore : (orderedAdversarialTarget gen).enumeration i ∈ core :=
      (Finset.mem_filter.mp hi).2
    have hjcore : (orderedAdversarialTarget gen).enumeration j ∈ core :=
      (Finset.mem_filter.mp hj).2
    obtain ⟨ki, hki⟩ := hicore
    obtain ⟨kj, hkj⟩ := hjcore
    have hkiLog : exponent i = ki := by simp [exponent, ← hki, Nat.log2_two_pow]
    have hkjLog : exponent j = kj := by simp [exponent, ← hkj, Nat.log2_two_pow]
    have hk : ki = kj := by omega
    exact (orderedAdversarialTarget gen).enumeration_injective (by
      calc
        (orderedAdversarialTarget gen).enumeration i = 2 ^ ki := hki.symm
        _ = 2 ^ kj := by rw [hk]
        _ = (orderedAdversarialTarget gen).enumeration j := hkj)
  have himage : indices.image exponent ⊆ Finset.range (Nat.log2 n + 6) := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨i, hi, rfl⟩
    have hilt : i < n := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hicore : (orderedAdversarialTarget gen).enumeration i ∈ core :=
      (Finset.mem_filter.mp hi).2
    obtain ⟨ki, hki⟩ := hicore
    have henum : (orderedAdversarialTarget gen).enumeration i ≤ 12 * n + 9 := by
      calc
        (orderedAdversarialTarget gen).enumeration i ≤ 12 * i + 9 :=
          ordered_enumeration_bound gen i
        _ ≤ 12 * n + 9 := by omega
    have hB : 12 * n + 9 ≠ 0 := by omega
    have hklog : ki ≤ Nat.log2 (12 * n + 9) := by
      apply (Nat.le_log2 hB).mpr
      simpa [hki] using henum
    have hlin := log2_linear_bound n hn
    have hexp : exponent i = ki := by simp [exponent, ← hki, Nat.log2_two_pow]
    rw [hexp]
    simp only [Finset.mem_range]
    omega
  change indices.card ≤ Nat.log2 n + 6
  rw [← Finset.card_image_of_injOn hinj]
  exact (Finset.card_le_card himage).trans_eq (Finset.card_range _)

private theorem tendsto_core_prefixRatio_zero (gen : FeedbackGenerator) :
    Tendsto ((orderedAdversarialTarget gen).prefixRatio core) atTop (𝓝 0) := by
  have hbound : ∀ n : ℕ, (orderedAdversarialTarget gen).prefixRatio core n ≤
      ((Nat.log2 n + 6 : ℕ) : ℝ) / (n : ℝ) := by
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · simp only [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, hn, if_false]
      exact div_le_div_of_nonneg_right
        (by exact_mod_cast core_prefixCount_le gen n hn) (Nat.cast_nonneg n)
  have herror : Tendsto (fun n : ℕ => ((Nat.log2 n + 6 : ℕ) : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
    have hconst : Tendsto (fun n : ℕ => (6 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa only [Nat.cast_add, add_div, zero_add] using
      GenLimit.tendsto_natLog2_div.add hconst
  exact squeeze_zero
    (fun n => (orderedAdversarialTarget gen).prefixRatio_nonneg core n)
    hbound herror

private theorem core_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedAdversarialTarget gen).upperDensity core = 0 := by
  exact (tendsto_core_prefixRatio_zero gen).limsup_eq

private theorem scored_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedAdversarialTarget gen).upperDensity
      (scored (adversarialTarget gen)
        (adversarialTranscript gen).presentation
        (adversarialTranscript gen).output) = 0 := by
  apply le_antisymm
  · calc
      (orderedAdversarialTarget gen).upperDensity
          (scored (adversarialTarget gen)
            (adversarialTranscript gen).presentation
            (adversarialTranscript gen).output)
          ≤ (orderedAdversarialTarget gen).upperDensity core :=
        (orderedAdversarialTarget gen).upperDensity_mono (scored_subset_core gen)
      _ = 0 := core_upperDensity_zero gen
  · exact (orderedAdversarialTarget gen).upperDensity_nonneg _

end Stage3S2BFormalization

theorem stage3_result : Stage3S2B.MainClaim := by
  refine ⟨Stage3S2BFormalization.targetClass_not_countable,
    Stage3S2BFormalization.uniform_positive, ?_⟩
  intro gen _hgen
  refine ⟨Stage3S2BFormalization.adversarialTarget gen,
    Stage3S2BFormalization.targetClass_adversarial gen, ?_⟩
  refine ⟨Stage3S2BFormalization.adversarialPresenter gen,
    Stage3S2BFormalization.adversarialTranscript gen,
    Stage3S2BFormalization.orderedAdversarialTarget gen, ?_⟩
  exact ⟨rfl,
    Stage3S2BFormalization.orderedAdversarialTarget_strictMono gen,
    Stage3S2BFormalization.presentedBy_adversarial gen,
    Stage3S2BFormalization.followsProtocol_adversarial gen,
    Stage3S2BFormalization.clean_adversarial gen,
    Stage3S2BFormalization.presentation_injective gen,
    Stage3S2BFormalization.complete_adversarial gen,
    Stage3S2BFormalization.scored_upperDensity_zero gen⟩
