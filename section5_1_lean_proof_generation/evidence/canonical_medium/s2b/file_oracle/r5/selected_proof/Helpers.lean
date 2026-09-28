import Stage3Model
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import Mathlib.Data.Nat.Nth
import Mathlib.Tactic
import GenLimit.Paper39_DenseGeneration.Abstract.Density

open Set Filter
open GenLimit.KleinbergWei

namespace Stage3Proof

open Stage3S2B

theorem core_injective : Function.Injective (fun k : ℕ => 2 ^ k) := by
  intro a b h
  exact Nat.pow_right_injective (by omega) h

theorem core_infinite : core.Infinite := by
  rw [core]
  exact Set.infinite_range_of_injective core_injective

theorem positive : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t => 2 ^ t, core_injective, 0, ?_⟩
  intro K hK t _
  rcases hK with ⟨A, hA, rfl⟩
  exact Or.inl ⟨t, rfl⟩

def encodeOrdinary (A : Set ℕ) : Language :=
  core ∪ {n | n ∈ ordinary ∧ Nat.div2 n ∈ A}

theorem encodeOrdinary_mem (A : Set ℕ) : encodeOrdinary A ∈ targetClass := by
  exact ⟨{n | n ∈ ordinary ∧ Nat.div2 n ∈ A}, by aesop, rfl⟩

theorem odd_not_core (n : ℕ) : 2 * n + 3 ∈ ordinary := by
  intro h
  rcases h with ⟨k, hk⟩
  cases k with
  | zero => simp at hk
  | succ k =>
      have heven : Even (2 ^ (k + 1)) := ⟨2 ^ k, by ring⟩
      have hodd : Odd (2 * n + 3) := ⟨n + 1, by omega⟩
      rw [← hk] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) heven

theorem encodeOrdinary_injective : Function.Injective encodeOrdinary := by
  intro A B h
  ext n
  by_cases hn : n = 0
  · subst n
    have hzero := Set.ext_iff.mp h 0
    have ho0 : 0 ∈ ordinary := by
      intro hc
      rcases hc with ⟨k, hk⟩
      simp at hk
    have hc0 : 0 ∉ core := ho0
    simpa [encodeOrdinary, hc0, ho0] using hzero
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have ho : 2 * m + 3 ∈ ordinary := odd_not_core m
    have heq := Set.ext_iff.mp h (2 * m + 3)
    have hc : 2 * m + 3 ∉ core := ho
    simpa [encodeOrdinary, hc, ho] using heq

theorem targetClass_not_countable : ¬ targetClass.Countable := by
  intro hcount
  have hpre : encodeOrdinary ⁻¹' targetClass = (Set.univ : Set (Set ℕ)) := by
    ext A
    simp [encodeOrdinary_mem]
  have huniv : (Set.univ : Set (Set ℕ)).Countable := by
    rw [← hpre]
    exact hcount.preimage encodeOrdinary_injective
  have hsets : Countable (Set ℕ) := Set.countable_univ_iff.mp huniv
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ hsets

end Stage3Proof

namespace Stage3Proof

open Stage3S2B

 theorem ordinary_infinite : ordinary.Infinite := by
  let f : ℕ → ℕ := fun n => 2 * n + 3
  have hf : Function.Injective f := by
    intro a b h
    simp [f] at h
    omega
  have hr : Set.range f ⊆ ordinary := by
    intro z hz
    rcases hz with ⟨n, rfl⟩
    exact odd_not_core n
  exact (Set.infinite_range_of_injective hf).mono hr

noncomputable def freshOrdinary (F : Finset ℕ) : ℕ := by
  classical
  exact Nat.find (ordinary_infinite.exists_notMem_finset F)

theorem freshOrdinary_spec (F : Finset ℕ) :
    freshOrdinary F ∈ ordinary ∧ freshOrdinary F ∉ F :=
by
  classical
  exact Nat.find_spec (ordinary_infinite.exists_notMem_finset F)

structure RunState (t : ℕ) where
  presentation : Fin t → ℕ
  query : Fin t → Option ℕ
  answer : Fin t → Option Bool
  output : Fin t → ℕ
  admitted : Finset ℕ
  rejected : Finset ℕ

noncomputable def nextPresentation {t : ℕ} (s : RunState t) : ℕ :=
  if Even t then 2 ^ (t / 2) else freshOrdinary (s.admitted ∪ s.rejected)

def admittedAfter {t : ℕ} (s : RunState t) (x : ℕ) : Finset ℕ :=
  if Even t then s.admitted else insert x s.admitted

noncomputable def rejectOne (I R : Finset ℕ) (z : ℕ) : Finset ℕ := by
  classical
  exact if z ∈ ordinary ∧ z ∉ I ∧ z ∉ R then insert z R else R

noncomputable def step (gen : FeedbackGenerator) {t : ℕ} (s : RunState t) : RunState (t + 1) := by
  classical
  let x := nextPresentation s
  let admitted' := admittedAfter s x
  let pres' : Fin (t + 1) → ℕ := Fin.lastCases x s.presentation
  let q := gen.query t pres' s.answer
  let b : Option Bool := match q with
    | none => none
    | some z => some (decide (z ∈ core ∨ z ∈ admitted'))
  let rejectedQ := match q with
    | none => s.rejected
    | some z => rejectOne admitted' s.rejected z
  let ans' : Fin (t + 1) → Option Bool := Fin.lastCases b s.answer
  let y := gen.output t pres' ans'
  exact {
    presentation := pres'
    query := Fin.lastCases q s.query
    answer := ans'
    output := Fin.lastCases y s.output
    admitted := admitted'
    rejected := rejectOne admitted' rejectedQ y
  }

noncomputable def run (gen : FeedbackGenerator) : (t : ℕ) → RunState t
  | 0 => ⟨Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, ∅, ∅⟩
  | t + 1 => step gen (run gen t)

noncomputable def runPresentation (gen : FeedbackGenerator) (t : ℕ) : ℕ :=
  nextPresentation (run gen t)

noncomputable def runQuery (gen : FeedbackGenerator) (t : ℕ) : Option ℕ :=
  gen.query t (Fin.lastCases (runPresentation gen t) (run gen t).presentation)
    (run gen t).answer

noncomputable def runAnswer (gen : FeedbackGenerator) (t : ℕ) : Option Bool := by
  classical
  exact match runQuery gen t with
  | none => none
  | some z => some (decide (z ∈ core ∨ z ∈
      admittedAfter (run gen t) (runPresentation gen t)))

noncomputable def runOutput (gen : FeedbackGenerator) (t : ℕ) : ℕ :=
  gen.output t
    (Fin.lastCases (runPresentation gen t) (run gen t).presentation)
    (Fin.lastCases (runAnswer gen t) (run gen t).answer)

noncomputable def runTranscript (gen : FeedbackGenerator) : Transcript where
  presentation := runPresentation gen
  query := runQuery gen
  answer := runAnswer gen
  output := runOutput gen

noncomputable def runPresenter (gen : FeedbackGenerator) : CausalPresenter where
  next t _ _ _ _ := runPresentation gen t

@[simp] theorem run_succ_presentation_last (gen : FeedbackGenerator) (t : ℕ) :
    (run gen (t + 1)).presentation (Fin.last t) = runPresentation gen t := by
  simp [run, step, runPresentation]

@[simp] theorem run_succ_query_last (gen : FeedbackGenerator) (t : ℕ) :
    (run gen (t + 1)).query (Fin.last t) = runQuery gen t := by
  simp [run, step, runQuery, runPresentation]

@[simp] theorem run_succ_answer_last (gen : FeedbackGenerator) (t : ℕ) :
    (run gen (t + 1)).answer (Fin.last t) = runAnswer gen t := by
  simp [run, step, runAnswer, runQuery, runPresentation]

@[simp] theorem run_succ_output_last (gen : FeedbackGenerator) (t : ℕ) :
    (run gen (t + 1)).output (Fin.last t) = runOutput gen t := by
  simp [run, step, runOutput, runAnswer, runQuery, runPresentation]

end Stage3Proof

namespace Stage3Proof

open Stage3S2B

@[simp] theorem run_presentation_eq (gen : FeedbackGenerator) (t : ℕ)
    (i : Fin t) : (run gen t).presentation i = runPresentation gen i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp
      · simpa [run, step] using ih j

@[simp] theorem run_query_eq (gen : FeedbackGenerator) (t : ℕ)
    (i : Fin t) : (run gen t).query i = runQuery gen i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp
      · simpa [run, step] using ih j

@[simp] theorem run_answer_eq (gen : FeedbackGenerator) (t : ℕ)
    (i : Fin t) : (run gen t).answer i = runAnswer gen i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp
      · simpa [run, step] using ih j

@[simp] theorem run_output_eq (gen : FeedbackGenerator) (t : ℕ)
    (i : Fin t) : (run gen t).output i = runOutput gen i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp
      · simpa [run, step] using ih j

 theorem presentedBy_run (gen : FeedbackGenerator) :
    PresentedBy (runPresenter gen) (runTranscript gen) := by
  intro t
  rfl

 theorem protocol_query_output (gen : FeedbackGenerator) (t : ℕ) :
    (runTranscript gen).query t = gen.query t
      (fun i => (runTranscript gen).presentation i)
      (fun i => (runTranscript gen).answer i) ∧
    (runTranscript gen).output t = gen.output t
      (fun i => (runTranscript gen).presentation i)
      (fun i => (runTranscript gen).answer i) := by
  constructor
  · simp only [runTranscript, runQuery]
    apply congrArg₂ (gen.query t)
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [runTranscript]
      · simp [runTranscript]
    · funext i
      simp [runTranscript]
  · simp only [runTranscript, runOutput]
    apply congrArg₂ (gen.output t)
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [runTranscript]
      · simp [runTranscript]
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [runTranscript]
      · simp [runTranscript]

end Stage3Proof

namespace Stage3Proof

open Stage3S2B

 theorem rejectOne_subset (I R : Finset ℕ) (z : ℕ) : R ⊆ rejectOne I R z := by
  classical
  simp [rejectOne]
  split <;> simp_all

 theorem rejectOne_ordinary (I R : Finset ℕ) (z : ℕ)
    (hR : ∀ w ∈ R, w ∈ ordinary) :
    ∀ w ∈ rejectOne I R z, w ∈ ordinary := by
  classical
  simp only [rejectOne]
  split_ifs with h
  · intro w hw
    simp at hw
    rcases hw with rfl | hw
    · exact h.1
    · exact hR w hw
  · exact hR

 theorem rejectOne_disjoint (I R : Finset ℕ) (z : ℕ)
    (h : Disjoint I R) : Disjoint I (rejectOne I R z) := by
  classical
  rw [Finset.disjoint_left] at h ⊢
  intro w hwI hwR
  simp only [rejectOne] at hwR
  split_ifs at hwR with hz
  · simp at hwR
    rcases hwR with rfl | hwR
    · exact hz.2.1 hwI
    · exact h hwI hwR
  · exact h hwI hwR

structure GoodState {t : ℕ} (s : RunState t) : Prop where
  admitted_ordinary : ∀ z ∈ s.admitted, z ∈ ordinary
  rejected_ordinary : ∀ z ∈ s.rejected, z ∈ ordinary
  disjoint : Disjoint s.admitted s.rejected

 theorem good_run (gen : FeedbackGenerator) (t : ℕ) : GoodState (run gen t) := by
  induction t with
  | zero =>
      constructor <;> simp [run]
  | succ t ih =>
      classical
      let s := run gen t
      let x := nextPresentation s
      let I := admittedAfter s x
      have hx : ¬ Even t → x ∈ ordinary ∧ x ∉ s.admitted ∧ x ∉ s.rejected := by
        intro he
        have hf := freshOrdinary_spec (s.admitted ∪ s.rejected)
        simpa [x, nextPresentation, he] using hf
      have hIord : ∀ z ∈ I, z ∈ ordinary := by
        intro z hz
        by_cases he : Even t
        · have hz' : z ∈ s.admitted := by
            simpa [I, admittedAfter, he] using hz
          exact ih.admitted_ordinary z hz'
        · simp [I, admittedAfter, he] at hz
          rcases hz with rfl | hz
          · exact (hx he).1
          · exact ih.admitted_ordinary z hz
      have hIR : Disjoint I s.rejected := by
        rw [Finset.disjoint_left]
        intro z hzI hzR
        by_cases he : Even t
        · exact (Finset.disjoint_left.mp ih.disjoint)
            (by simpa [I, admittedAfter, he] using hzI) hzR
        · simp [I, admittedAfter, he] at hzI
          rcases hzI with rfl | hzI
          · exact (hx he).2.2 hzR
          · exact (Finset.disjoint_left.mp ih.disjoint) hzI hzR
      let q := gen.query t (Fin.lastCases x s.presentation) s.answer
      let Rq := match q with
        | none => s.rejected
        | some z => rejectOne I s.rejected z
      have hRqOrd : ∀ z ∈ Rq, z ∈ ordinary := by
        cases hq : q with
        | none => simpa [Rq, hq] using ih.rejected_ordinary
        | some z =>
            simpa [Rq, hq] using rejectOne_ordinary I s.rejected z ih.rejected_ordinary
      have hIRq : Disjoint I Rq := by
        cases hq : q with
        | none => simpa [Rq, hq] using hIR
        | some z => simpa [Rq, hq] using rejectOne_disjoint I s.rejected z hIR
      rw [run, step]
      change GoodState {
        presentation := Fin.lastCases x s.presentation
        query := Fin.lastCases q s.query
        answer := Fin.lastCases
          (match q with | none => none | some z => some (decide (z ∈ core ∨ z ∈ I))) s.answer
        output := Fin.lastCases
          (gen.output t (Fin.lastCases x s.presentation)
            (Fin.lastCases
              (match q with | none => none | some z => some (decide (z ∈ core ∨ z ∈ I))) s.answer)) s.output
        admitted := I
        rejected := rejectOne I Rq
          (gen.output t (Fin.lastCases x s.presentation)
            (Fin.lastCases
              (match q with | none => none | some z => some (decide (z ∈ core ∨ z ∈ I))) s.answer)) }
      exact ⟨hIord,
        rejectOne_ordinary I Rq _ hRqOrd,
        rejectOne_disjoint I Rq _ hIRq⟩

 theorem admitted_mono_step (gen : FeedbackGenerator) (t : ℕ) :
    (run gen t).admitted ⊆ (run gen (t + 1)).admitted := by
  classical
  simp [run, step, admittedAfter]
  split <;> simp_all

 theorem rejected_mono_step (gen : FeedbackGenerator) (t : ℕ) :
    (run gen t).rejected ⊆ (run gen (t + 1)).rejected := by
  classical
  simp only [run, step]
  exact fun z hz => rejectOne_subset _ _ _
    (by
      split
      · exact hz
      · exact rejectOne_subset _ _ _ hz)

 theorem admitted_mono (gen : FeedbackGenerator) {s t : ℕ} (hst : s ≤ t) :
    (run gen s).admitted ⊆ (run gen t).admitted := by
  induction t, hst using Nat.le_induction with
  | base => exact fun _ h => h
  | succ t hst ih => exact fun z hz => admitted_mono_step gen t (ih hz)

 theorem rejected_mono (gen : FeedbackGenerator) {s t : ℕ} (hst : s ≤ t) :
    (run gen s).rejected ⊆ (run gen t).rejected := by
  induction t, hst using Nat.le_induction with
  | base => exact fun _ h => h
  | succ t hst ih => exact fun z hz => rejected_mono_step gen t (ih hz)

noncomputable def runTarget (gen : FeedbackGenerator) : Language :=
  core ∪ {z | ∃ t, z ∈ (run gen t).admitted}

 theorem rejected_not_target (gen : FeedbackGenerator) {t z : ℕ}
    (hz : z ∈ (run gen t).rejected) : z ∉ runTarget gen := by
  intro hK
  rcases hK with hc | ⟨u, hu⟩
  · exact (good_run gen t).rejected_ordinary z hz hc
  · have hR : z ∈ (run gen (max t u)).rejected :=
      rejected_mono gen (Nat.le_max_left _ _) hz
    have hI : z ∈ (run gen (max t u)).admitted :=
      admitted_mono gen (Nat.le_max_right _ _) hu
    exact (Finset.disjoint_left.mp (good_run gen _).disjoint) hI hR

end Stage3Proof

namespace Stage3Proof

open Stage3S2B

 theorem runTarget_mem_class (gen : FeedbackGenerator) : runTarget gen ∈ targetClass := by
  refine ⟨{z | ∃ t, z ∈ (run gen t).admitted}, ?_, rfl⟩
  intro z hz
  rcases hz with ⟨t, ht⟩
  exact (good_run gen t).admitted_ordinary z ht

 theorem presentation_even (gen : FeedbackGenerator) {t : ℕ} (ht : Even t) :
    runPresentation gen t = 2 ^ (t / 2) := by
  simp [runPresentation, nextPresentation, ht]

 theorem presentation_odd (gen : FeedbackGenerator) {t : ℕ} (ht : ¬ Even t) :
    runPresentation gen t = freshOrdinary
      ((run gen t).admitted ∪ (run gen t).rejected) := by
  simp [runPresentation, nextPresentation, ht]

 theorem presentation_odd_spec (gen : FeedbackGenerator) {t : ℕ} (ht : ¬ Even t) :
    runPresentation gen t ∈ ordinary ∧
    runPresentation gen t ∉ (run gen t).admitted ∧
    runPresentation gen t ∉ (run gen t).rejected := by
  have h := freshOrdinary_spec ((run gen t).admitted ∪ (run gen t).rejected)
  simpa [presentation_odd gen ht] using h

 theorem presentation_admitted (gen : FeedbackGenerator) {t : ℕ} (ht : ¬ Even t) :
    runPresentation gen t ∈ (run gen (t + 1)).admitted := by
  classical
  rw [run]
  change runPresentation gen t ∈ admittedAfter (run gen t) (runPresentation gen t)
  simp [admittedAfter, ht]

 theorem admitted_has_presentation (gen : FeedbackGenerator) {t z : ℕ}
    (hz : z ∈ (run gen t).admitted) : ∃ i, i < t ∧ runPresentation gen i = z := by
  induction t with
  | zero => simp [run] at hz
  | succ t ih =>
      classical
      by_cases he : Even t
      · have hz' : z ∈ (run gen t).admitted := by
          simpa [run, step, admittedAfter, he] using hz
        rcases ih hz' with ⟨i, hi, rfl⟩
        exact ⟨i, Nat.lt.step hi, rfl⟩
      · simp [run, step, admittedAfter, he] at hz
        rcases hz with rfl | hz
        · exact ⟨t, Nat.lt_add_one _, rfl⟩
        · rcases ih hz with ⟨i, hi, rfl⟩
          exact ⟨i, Nat.lt.step hi, rfl⟩

 theorem run_clean (gen : FeedbackGenerator) :
    Clean (runPresentation gen) (runTarget gen) := by
  intro t
  by_cases ht : Even t
  · left
    exact ⟨t / 2, (presentation_even gen ht).symm⟩
  · right
    exact ⟨t + 1, presentation_admitted gen ht⟩

 theorem run_complete (gen : FeedbackGenerator) :
    Complete (runPresentation gen) (runTarget gen) := by
  intro z hz
  rcases hz with ⟨k, rfl⟩ | ⟨t, ht⟩
  · refine ⟨2 * k, ?_⟩
    have he : Even (2 * k) := ⟨k, by omega⟩
    rw [presentation_even gen he]
    congr 1
    omega
  · rcases admitted_has_presentation gen ht with ⟨i, -, hi⟩
    exact ⟨i, hi⟩

 theorem run_injective (gen : FeedbackGenerator) : Function.Injective (runPresentation gen) := by
  intro a b hab
  wlog hle : a ≤ b generalizing a b
  · exact (this hab.symm (Nat.le_of_not_ge hle)).symm
  rcases Nat.eq_or_lt_of_le hle with rfl | hlt
  · rfl
  by_cases ha : Even a <;> by_cases hb : Even b
  · rw [presentation_even gen ha, presentation_even gen hb] at hab
    have hd : a / 2 = b / 2 := core_injective hab
    rcases ha with ⟨i, rfl⟩
    rcases hb with ⟨j, rfl⟩
    simp at hd
    omega
  · have hcore : runPresentation gen a ∈ core :=
      ⟨a / 2, (presentation_even gen ha).symm⟩
    have hord := (presentation_odd_spec gen hb).1
    exact (hord (hab ▸ hcore)).elim
  · have hord := (presentation_odd_spec gen ha).1
    have hcore : runPresentation gen b ∈ core :=
      ⟨b / 2, (presentation_even gen hb).symm⟩
    exact (hord (hab ▸ hcore)).elim
  · have hIa : runPresentation gen a ∈ (run gen (a + 1)).admitted :=
      presentation_admitted gen ha
    have hIb : runPresentation gen a ∈ (run gen b).admitted :=
      admitted_mono gen (by omega) hIa
    have hfresh := (presentation_odd_spec gen hb).2.1
    exact (hfresh (hab ▸ hIb)).elim

end Stage3Proof

namespace Stage3Proof

open Stage3S2B

 theorem run_succ_admitted (gen : FeedbackGenerator) (t : ℕ) :
    (run gen (t + 1)).admitted =
      admittedAfter (run gen t) (runPresentation gen t) := by
  simp [run, step, runPresentation]

 theorem current_decision_iff (gen : FeedbackGenerator) (t z : ℕ)
    (hqz : runQuery gen t = some z) :
    z ∈ core ∨ z ∈ admittedAfter (run gen t) (runPresentation gen t) ↔
      z ∈ runTarget gen := by
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr ⟨t + 1, by simpa [run_succ_admitted] using h⟩
  · intro hK
    by_contra hnow
    have hnc : z ∉ core := fun h => hnow (Or.inl h)
    have hord : z ∈ ordinary := hnc
    have hnI : z ∉ admittedAfter (run gen t) (runPresentation gen t) :=
      fun h => hnow (Or.inr h)
    by_cases hR : z ∈ (run gen t).rejected
    · exact rejected_not_target gen hR hK
    · have hqR : z ∈ match runQuery gen t with
          | none => (run gen t).rejected
          | some q => rejectOne
              (admittedAfter (run gen t) (runPresentation gen t))
              (run gen t).rejected q := by
        cases hq : runQuery gen t with
        | none =>
            rw [hq] at hqz
            contradiction
        | some q =>
            have hqeq : q = z := Option.some.inj (hq.symm.trans hqz)
            subst q
            simp [rejectOne, hord, hnI, hR]
      have hnextR : z ∈ (run gen (t + 1)).rejected := by
        rw [run]
        simp only [step]
        exact rejectOne_subset _ _ _ hqR
      exact rejected_not_target gen hnextR hK

 theorem run_follows_protocol (gen : FeedbackGenerator) :
    FollowsProtocol gen (runTarget gen) (runTranscript gen) := by
  intro t
  have hqo := protocol_query_output gen t
  refine ⟨hqo.1, ?_, hqo.2⟩
  simp only [runTranscript, runAnswer]
  cases hq : runQuery gen t with
  | none => simp [hq]
  | some z =>
      simp only [hq]
      congr 2
      exact propext (current_decision_iff gen t z hq)

end Stage3Proof

namespace Stage3Proof

open Stage3S2B

 theorem scored_subset_core (gen : FeedbackGenerator) :
    scored (runTarget gen) (runPresentation gen) (runOutput gen) ⊆ core := by
  intro z hz
  rcases hz with ⟨hzK, t, hyt, hzobs⟩
  by_contra hzcore
  have hzord : z ∈ ordinary := hzcore
  let I := admittedAfter (run gen t) (runPresentation gen t)
  let Rq := match runQuery gen t with
    | none => (run gen t).rejected
    | some q => rejectOne I (run gen t).rejected q
  by_cases hzI : z ∈ I
  · have hzInext : z ∈ (run gen (t + 1)).admitted := by
      simpa [I, run_succ_admitted] using hzI
    rcases admitted_has_presentation gen hzInext with ⟨i, hi, hip⟩
    exact hzobs ⟨i, by omega, hip⟩
  · by_cases hzRq : z ∈ Rq
    · have hzRnext : z ∈ (run gen (t + 1)).rejected := by
        rw [run]
        simp only [step]
        exact rejectOne_subset _ _ _ hzRq
      exact rejected_not_target gen hzRnext hzK
    · have hzRnext : z ∈ (run gen (t + 1)).rejected := by
        rw [run]
        simp only [step]
        change z ∈ rejectOne I Rq (runOutput gen t)
        rw [hyt]
        simp [rejectOne, hzord, hzI, hzRq]
      exact rejected_not_target gen hzRnext hzK

 theorem admitted_card_le (gen : FeedbackGenerator) (t : ℕ) :
    (run gen t).admitted.card ≤ t := by
  induction t with
  | zero => simp [run]
  | succ t ih =>
      classical
      rw [run_succ_admitted]
      simp only [admittedAfter]
      split_ifs
      · omega
      · exact (Finset.card_insert_le _ _).trans (by omega)

 theorem rejectOne_card_le (I R : Finset ℕ) (z : ℕ) :
    (rejectOne I R z).card ≤ R.card + 1 := by
  classical
  simp only [rejectOne]
  split_ifs
  · exact Finset.card_insert_le _ _
  · omega

 theorem doubleReject_card_le (I R : Finset ℕ) (q : Option ℕ) (y : ℕ) :
    (rejectOne I (match q with
      | none => R
      | some z => rejectOne I R z) y).card ≤ R.card + 2 := by
  cases q with
  | none =>
      change (rejectOne I R y).card ≤ R.card + 2
      exact (rejectOne_card_le I R y).trans (by omega)
  | some z =>
      change (rejectOne I (rejectOne I R z) y).card ≤ R.card + 2
      have h₁ := rejectOne_card_le I R z
      have h₂ := rejectOne_card_le I (rejectOne I R z) y
      omega

 theorem rejected_card_le (gen : FeedbackGenerator) (t : ℕ) :
    (run gen t).rejected.card ≤ 2 * t := by
  induction t with
  | zero => simp [run]
  | succ t ih =>
      rw [run]
      simp only [step]
      exact (doubleReject_card_le _ _ _ _).trans (by omega)

 theorem state_union_card_le (gen : FeedbackGenerator) (t : ℕ) :
    ((run gen t).admitted ∪ (run gen t).rejected).card ≤ 3 * t := by
  calc
    ((run gen t).admitted ∪ (run gen t).rejected).card
        ≤ (run gen t).admitted.card + (run gen t).rejected.card := Finset.card_union_le _ _
    _ ≤ t + 2 * t := Nat.add_le_add (admitted_card_le gen t) (rejected_card_le gen t)
    _ = 3 * t := by omega

end Stage3Proof

namespace Stage3Proof

open Stage3S2B

 theorem freshOrdinary_le (F : Finset ℕ) :
    freshOrdinary F ≤ 2 * F.card + 3 := by
  classical
  let f : ℕ → ℕ := fun j => 2 * j + 3
  let pool := (Finset.range (F.card + 1)).image f
  have hf : Function.Injective f := by
    intro a b h
    simp [f] at h
    omega
  have hpoolcard : pool.card = F.card + 1 := by
    simp [pool, Finset.card_image_of_injective _ hf]
  obtain ⟨z, hzpool, hzF⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := F) (t := pool) (by omega)
  rcases Finset.mem_image.mp hzpool with ⟨j, hj, rfl⟩
  have hjlt : j < F.card + 1 := Finset.mem_range.mp hj
  have hwitness : f j ∈ ordinary ∧ f j ∉ F := by
    exact ⟨odd_not_core j, hzF⟩
  calc
    freshOrdinary F ≤ f j := Nat.find_min' _ hwitness
    _ ≤ 2 * F.card + 3 := by simp [f]; omega

 theorem odd_presentation_le (gen : FeedbackGenerator) (r : ℕ) :
    runPresentation gen (2 * r + 1) ≤ 12 * r + 9 := by
  have hodd : ¬ Even (2 * r + 1) := Nat.not_even_iff_odd.mpr ⟨r, by omega⟩
  rw [presentation_odd gen hodd]
  calc
    freshOrdinary ((run gen (2 * r + 1)).admitted ∪
        (run gen (2 * r + 1)).rejected)
      ≤ 2 * ((run gen (2 * r + 1)).admitted ∪
          (run gen (2 * r + 1)).rejected).card + 3 := freshOrdinary_le _
    _ ≤ 2 * (3 * (2 * r + 1)) + 3 := by
      have hcard := state_union_card_le gen (2 * r + 1)
      omega
    _ = 12 * r + 9 := by ring

 theorem runTarget_infinite (gen : FeedbackGenerator) : (runTarget gen).Infinite := by
  exact core_infinite.mono (fun _ hz => Or.inl hz)

noncomputable def orderedRunTarget (gen : FeedbackGenerator) : Stage3S2B.OrderedLanguage where
  carrier := runTarget gen
  enumeration := Nat.nth (fun z => z ∈ runTarget gen)
  enumeration_injective := Nat.nth_injective (runTarget_infinite gen)
  range_enumeration := Nat.range_nth_of_infinite (runTarget_infinite gen)

 theorem orderedRunTarget_strictMono (gen : FeedbackGenerator) :
    StrictMono (orderedRunTarget gen).enumeration :=
  Nat.nth_strictMono (runTarget_infinite gen)

 theorem orderedRunTarget_nth_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedRunTarget gen).enumeration n ≤ 12 * n + 9 := by
  classical
  let f : ℕ → ℕ := fun r => runPresentation gen (2 * r + 1)
  let source := Finset.range (n + 1)
  let target := (Finset.range (12 * n + 10)).filter
    (fun z => z ∈ runTarget gen)
  have hf : Function.Injective f := by
    intro a b h
    change runPresentation gen (2 * a + 1) = runPresentation gen (2 * b + 1) at h
    have hab := run_injective gen h
    omega
  have hcardSource : (source.image f).card = n + 1 := by
    simp [source, Finset.card_image_of_injective _ hf]
  have hsub : source.image f ⊆ target := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨r, hr, rfl⟩
    have hrlt : r < n + 1 := by simpa [source] using hr
    have hrle : r ≤ n := Nat.le_of_lt_succ hrlt
    have hbound := odd_presentation_le gen r
    have hK := run_clean gen (2 * r + 1)
    change f r ∈ target
    simp only [target, Finset.mem_filter, Finset.mem_range]
    change f r < 12 * n + 10 ∧ f r ∈ runTarget gen
    constructor
    · change runPresentation gen (2 * r + 1) < 12 * n + 10
      omega
    · exact hK
  have hcount : n + 1 ≤ Nat.count (fun z => z ∈ runTarget gen) (12 * n + 10) := by
    rw [Nat.count_eq_card_filter_range]
    exact hcardSource ▸ Finset.card_le_card hsub
  have hnth : Nat.nth (fun z => z ∈ runTarget gen) n < 12 * n + 10 := by
    apply Nat.nth_lt_of_lt_count
    omega
  simpa [orderedRunTarget] using (Nat.le_pred_of_lt hnth)

end Stage3Proof

namespace Stage3Proof

open Stage3S2B

noncomputable def coreExponent (z : ℕ) : ℕ := by
  classical
  exact if h : z ∈ core then Nat.find h else 0

 theorem pow_coreExponent {z : ℕ} (hz : z ∈ core) : 2 ^ coreExponent z = z := by
  classical
  simp only [coreExponent, dif_pos hz]
  exact Nat.find_spec hz

 theorem core_prefixCount_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedRunTarget gen).prefixCount core n ≤ Nat.log2 (12 * n + 10) + 1 := by
  classical
  let source := (Finset.range n).filter
    (fun i => (orderedRunTarget gen).enumeration i ∈ core)
  let target := Finset.range (Nat.log2 (12 * n + 10) + 1)
  have hmaps : Set.MapsTo
      (fun i => coreExponent ((orderedRunTarget gen).enumeration i))
      (source : Set ℕ) (target : Set ℕ) := by
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    have hil : i < n := Finset.mem_range.mp hi'.1
    have hpow := pow_coreExponent hi'.2
    have henum := orderedRunTarget_nth_le gen i
    have hleB : (orderedRunTarget gen).enumeration i ≤ 12 * n + 10 := by omega
    have hexp : coreExponent ((orderedRunTarget gen).enumeration i) ≤
        Nat.log2 (12 * n + 10) := by
      rw [Nat.le_log2 (by omega)]
      simpa [hpow] using hleB
    simpa [target] using Nat.lt_succ_of_le hexp
  have hinj : Set.InjOn
      (fun i => coreExponent ((orderedRunTarget gen).enumeration i))
      (source : Set ℕ) := by
    intro i hi j hj hij
    apply (orderedRunTarget gen).enumeration_injective
    change coreExponent ((orderedRunTarget gen).enumeration i) =
      coreExponent ((orderedRunTarget gen).enumeration j) at hij
    have hicore := (Finset.mem_filter.mp hi).2
    have hjcore := (Finset.mem_filter.mp hj).2
    calc
      (orderedRunTarget gen).enumeration i
          = 2 ^ coreExponent ((orderedRunTarget gen).enumeration i) :=
            (pow_coreExponent hicore).symm
      _ = 2 ^ coreExponent ((orderedRunTarget gen).enumeration j) := congrArg (fun k => 2 ^ k) hij
      _ = (orderedRunTarget gen).enumeration j := pow_coreExponent hjcore
  have hcard := Finset.card_le_card_of_injOn
    (fun i => coreExponent ((orderedRunTarget gen).enumeration i)) hmaps hinj
  simpa [GenLimit.KleinbergWei.OrderedLanguage.prefixCount, source, target] using hcard

 theorem log_linear_le (n : ℕ) (hn : 3 ≤ n) :
    Nat.log2 (12 * n + 10) ≤ Nat.log2 n + 4 := by
  rw [Nat.log2_eq_log_two]
  calc
    Nat.log 2 (12 * n + 10) ≤ Nat.log 2 (n * 16) := Nat.log_mono_right (by omega)
    _ = Nat.log 2 n + 4 := by
      have hn0 : n ≠ 0 := by omega
      rw [show n * 16 = (((n * 2) * 2) * 2) * 2 by ring]
      rw [Nat.log_mul_base Nat.one_lt_two]
      · rw [Nat.log_mul_base Nat.one_lt_two]
        · rw [Nat.log_mul_base Nat.one_lt_two]
          · rw [Nat.log_mul_base Nat.one_lt_two hn0]
          · omega
        · omega
      · omega
    _ = Nat.log2 n + 4 := by rw [Nat.log2_eq_log_two]

 theorem core_prefixRatio_le (gen : FeedbackGenerator) :
    ∀ᶠ n : ℕ in atTop,
      (orderedRunTarget gen).prefixRatio core n ≤
        ((5 + Nat.log2 n : ℕ) : ℝ) / (n : ℝ) := by
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hn0 : n ≠ 0 := by omega
  rw [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio]
  simp only [hn0, if_false]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  exact_mod_cast (core_prefixCount_le gen n).trans (by
    have := log_linear_le n hn
    omega)

 theorem core_prefixRatio_tendsto_zero (gen : FeedbackGenerator) :
    Tendsto ((orderedRunTarget gen).prefixRatio core) atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall (fun n => (orderedRunTarget gen).prefixRatio_nonneg core n)
  · exact core_prefixRatio_le gen
  · exact GenLimit.tendsto_countingError_div 5

 theorem core_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedRunTarget gen).upperDensity core = 0 := by
  exact (core_prefixRatio_tendsto_zero gen).limsup_eq

 theorem scored_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedRunTarget gen).upperDensity
      (scored (runTarget gen) (runPresentation gen) (runOutput gen)) = 0 := by
  apply le_antisymm
  · calc
      (orderedRunTarget gen).upperDensity
          (scored (runTarget gen) (runPresentation gen) (runOutput gen))
        ≤ (orderedRunTarget gen).upperDensity core :=
          (orderedRunTarget gen).upperDensity_mono (scored_subset_core gen)
      _ = 0 := core_upperDensity_zero gen
  · exact (orderedRunTarget gen).upperDensity_nonneg _

end Stage3Proof

namespace Stage3Proof

open Stage3S2B

 theorem negative : NegativeClaim := by
  intro gen _
  refine ⟨runTarget gen, runTarget_mem_class gen,
    runPresenter gen, runTranscript gen, orderedRunTarget gen, ?_⟩
  refine ⟨rfl, orderedRunTarget_strictMono gen, presentedBy_run gen,
    run_follows_protocol gen, ?_, ?_, ?_, ?_⟩
  · simpa [runTranscript] using run_clean gen
  · simpa [runTranscript] using run_injective gen
  · simpa [runTranscript] using run_complete gen
  · simpa [runTranscript] using scored_upperDensity_zero gen

end Stage3Proof
