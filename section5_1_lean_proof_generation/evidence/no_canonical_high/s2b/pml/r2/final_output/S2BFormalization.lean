import Stage3Model
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Set.Countable
import Mathlib.Tactic
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation

open Filter
open GenLimit.KleinbergWei

namespace Stage3Proof

open Stage3S2B

structure Round where
  presentation : ℕ
  query : Option ℕ
  answer : Option Bool
  output : ℕ

def oddCandidate (k : ℕ) : ℕ := 2 * k + 3

theorem oddCandidate_injective : Function.Injective oddCandidate := by
  intro a b h
  simp only [oddCandidate] at h
  omega

theorem oddCandidate_ordinary (k : ℕ) : oddCandidate k ∈ ordinary := by
  intro hcore
  rcases hcore with ⟨j, hj⟩
  cases j with
  | zero => simp [oddCandidate] at hj
  | succ j =>
      have heven : Even (2 ^ (j + 1)) := by
        refine ⟨2 ^ j, ?_⟩
        rw [pow_succ]
        omega
      rcases heven with ⟨r, hr⟩
      change 2 ^ (j + 1) = 2 * k + 3 at hj
      have hodd : Odd (2 * k + 3) := by
        refine ⟨k + 1, ?_⟩
        omega
      have hev : Even (2 * k + 3) := ⟨r, (hr.symm.trans hj).symm⟩
      exact (Nat.not_even_iff_odd.mpr hodd) hev

def pastForbidden (t : ℕ)
    (x : Fin t → ℕ) (q : Fin t → Option ℕ) (y : Fin t → ℕ) : Finset ℕ :=
  (Finset.univ.image x) ∪
    (Finset.univ.image y) ∪
      (Finset.univ.image fun i => (q i).getD 0)

theorem exists_freshOddIndex (t : ℕ)
    (x : Fin t → ℕ) (q : Fin t → Option ℕ) (y : Fin t → ℕ) :
    ∃ k, oddCandidate k ∉ pastForbidden t x q y := by
  classical
  have hinfinite : (Set.range oddCandidate).Infinite :=
    Set.infinite_range_of_injective oddCandidate_injective
  obtain ⟨z, ⟨k, rfl⟩, hk⟩ :=
    hinfinite.exists_notMem_finset (pastForbidden t x q y)
  exact ⟨k, hk⟩

noncomputable def freshOddIndex (t : ℕ)
    (x : Fin t → ℕ) (q : Fin t → Option ℕ) (y : Fin t → ℕ) : ℕ := by
  classical
  exact Nat.find (exists_freshOddIndex t x q y)

theorem freshOddIndex_avoids (t : ℕ)
    (x : Fin t → ℕ) (q : Fin t → Option ℕ) (y : Fin t → ℕ) :
    let k := freshOddIndex t x q y
    (∀ i, x i ≠ oddCandidate k) ∧
      (∀ i z, q i = some z → z ≠ oddCandidate k) ∧
      (∀ i, y i ≠ oddCandidate k) := by
  classical
  have hk := Nat.find_spec (exists_freshOddIndex t x q y)
  change oddCandidate (freshOddIndex t x q y) ∉ pastForbidden t x q y at hk
  simp only [pastForbidden, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
    true_and, not_or] at hk
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    exact hk.1.1 ⟨i, hi⟩
  · intro i z hq hz
    apply hk.2
    refine ⟨i, ?_⟩
    simp [hq, hz]
  · intro i hi
    exact hk.1.2 ⟨i, hi⟩

theorem freshOddIndex_le_card (t : ℕ)
    (x : Fin t → ℕ) (q : Fin t → Option ℕ) (y : Fin t → ℕ) :
    freshOddIndex t x q y ≤ (pastForbidden t x q y).card := by
  classical
  let forbidden := pastForbidden t x q y
  let witness := exists_freshOddIndex t x q y
  by_contra hle
  have hlt : forbidden.card < freshOddIndex t x q y := Nat.lt_of_not_ge hle
  let candidates := (Finset.range (forbidden.card + 1)).image oddCandidate
  have hsubset : candidates ⊆ forbidden := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨k, hk, rfl⟩
    have hklt : k < freshOddIndex t x q y := by
      have hkcard : k ≤ forbidden.card := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      exact hkcard.trans_lt hlt
    have hnot := Nat.find_min witness hklt
    change ¬ oddCandidate k ∉ forbidden at hnot
    simpa using hnot
  have hcard : candidates.card = forbidden.card + 1 := by
    simp [candidates, Finset.card_image_of_injective _ oddCandidate_injective]
  have := Finset.card_le_card hsubset
  rw [hcard] at this
  omega

theorem pastForbidden_card_le (t : ℕ)
    (x : Fin t → ℕ) (q : Fin t → Option ℕ) (y : Fin t → ℕ) :
    (pastForbidden t x q y).card ≤ 3 * t := by
  classical
  have hx : (Finset.univ.image x).card ≤ t := by
    simpa using (Finset.card_image_le (s := Finset.univ) (f := x))
  have hy : (Finset.univ.image y).card ≤ t := by
    simpa using (Finset.card_image_le (s := Finset.univ) (f := y))
  have hq : (Finset.univ.image fun i => (q i).getD 0).card ≤ t := by
    simpa using (Finset.card_image_le (s := Finset.univ)
      (f := fun i => (q i).getD 0))
  have hxy := Finset.card_union_le (Finset.univ.image x) (Finset.univ.image y)
  have htotal := Finset.card_union_le
    ((Finset.univ.image x) ∪ (Finset.univ.image y))
    (Finset.univ.image fun i => (q i).getD 0)
  unfold pastForbidden
  omega

theorem freshOddIndex_le (t : ℕ)
    (x : Fin t → ℕ) (q : Fin t → Option ℕ) (y : Fin t → ℕ) :
    freshOddIndex t x q y ≤ 3 * t :=
  (freshOddIndex_le_card t x q y).trans (pastForbidden_card_le t x q y)

noncomputable def presenterValue (t : ℕ)
    (x : Fin t → ℕ) (q : Fin t → Option ℕ)
    (y : Fin t → ℕ) : ℕ :=
  if Even t then 2 ^ (t / 2)
  else oddCandidate (freshOddIndex t x q y)

noncomputable local instance : DecidablePred (· ∈ core) := Classical.decPred _

noncomputable def run (gen : FeedbackGenerator) :
    (t : ℕ) → Fin t → Round
  | 0 => Fin.elim0
  | t + 1 =>
      let prev := run gen t
      let xv := presenterValue t
        (fun i => (prev i).presentation)
        (fun i => (prev i).query)
        (fun i => (prev i).output)
      let xp : Fin (t + 1) → ℕ := Fin.lastCases xv (fun i => (prev i).presentation)
      let ap : Fin t → Option Bool := fun i => (prev i).answer
      let qv := gen.query t xp ap
      let av := match qv with
        | none => none
        | some z => some (decide (z ∈ core ∨ ∃ i, xp i = z))
      let af : Fin (t + 1) → Option Bool := Fin.lastCases av ap
      let yv := gen.output t xp af
      Fin.lastCases ⟨xv, qv, av, yv⟩ prev

noncomputable def runTranscript (gen : FeedbackGenerator) : Transcript where
  presentation t := (run gen (t + 1) (Fin.last t)).presentation
  query t := (run gen (t + 1) (Fin.last t)).query
  answer t := (run gen (t + 1) (Fin.last t)).answer
  output t := (run gen (t + 1) (Fin.last t)).output

noncomputable def diagonalPresenter : CausalPresenter where
  next t x q _a y := presenterValue t x q y

def diagonalTarget (gen : FeedbackGenerator) : Language :=
  Set.range (runTranscript gen).presentation

@[simp] theorem run_castSucc (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    run gen (t + 1) i.castSucc = run gen t i := by
  simp [run]

@[simp] theorem run_last_presentation (gen : FeedbackGenerator) (t : ℕ) :
    (run gen (t + 1) (Fin.last t)).presentation =
      presenterValue t
        (fun i => (run gen t i).presentation)
        (fun i => (run gen t i).query)
        (fun i => (run gen t i).output) := by
  simp [run]

@[simp] theorem run_last_query (gen : FeedbackGenerator) (t : ℕ) :
    (run gen (t + 1) (Fin.last t)).query =
      gen.query t
        (Fin.lastCases
          (presenterValue t
            (fun i => (run gen t i).presentation)
            (fun i => (run gen t i).query)
            (fun i => (run gen t i).output))
          (fun i => (run gen t i).presentation))
        (fun i => (run gen t i).answer) := by
  simp [run]


theorem transcript_prefix_round (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (run gen t i).presentation = (runTranscript gen).presentation i ∧
    (run gen t i).query = (runTranscript gen).query i ∧
    (run gen t i).answer = (runTranscript gen).answer i ∧
    (run gen t i).output = (runTranscript gen).output i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [runTranscript]
      · simpa using ih j

 theorem presented_by_diagonal (gen : FeedbackGenerator) :
    PresentedBy diagonalPresenter (runTranscript gen) := by
  intro t
  change (run gen (t + 1) (Fin.last t)).presentation = _
  rw [run_last_presentation]
  congr 1 <;> funext i
  · exact (transcript_prefix_round gen t i).1
  · exact (transcript_prefix_round gen t i).2.1
  · exact (transcript_prefix_round gen t i).2.2.2

theorem presentation_even (gen : FeedbackGenerator) (k : ℕ) :
    (runTranscript gen).presentation (2 * k) = 2 ^ k := by
  change (run gen (2 * k + 1) (Fin.last (2 * k))).presentation = _
  rw [run_last_presentation]
  simp [presenterValue]

theorem presentation_odd (gen : FeedbackGenerator) (k : ℕ) :
    ∃ j, (runTranscript gen).presentation (2 * k + 1) = oddCandidate j := by
  change ∃ j, (run gen (2 * k + 1 + 1) (Fin.last (2 * k + 1))).presentation = oddCandidate j
  rw [run_last_presentation]
  simp only [presenterValue, Nat.not_even_iff_odd.mpr (odd_two_mul_add_one k),
    if_false]
  exact ⟨_, rfl⟩

theorem presentation_of_even (gen : FeedbackGenerator) {t : ℕ} (ht : Even t) :
    (runTranscript gen).presentation t = 2 ^ (t / 2) := by
  change (run gen (t + 1) (Fin.last t)).presentation = _
  rw [run_last_presentation]
  simp [presenterValue, ht]

theorem presentation_of_odd_ordinary (gen : FeedbackGenerator) {t : ℕ} (ht : Odd t) :
    (runTranscript gen).presentation t ∈ ordinary := by
  change (run gen (t + 1) (Fin.last t)).presentation ∈ ordinary
  rw [run_last_presentation]
  simp only [presenterValue, Nat.not_even_iff_odd.mpr ht, if_false]
  exact oddCandidate_ordinary _

theorem odd_presentation_ne_past (gen : FeedbackGenerator) {t : ℕ} (ht : Odd t)
    (i : Fin t) :
    (runTranscript gen).presentation i ≠ (runTranscript gen).presentation t := by
  change (runTranscript gen).presentation i ≠
    (run gen (t + 1) (Fin.last t)).presentation
  rw [run_last_presentation]
  simp only [presenterValue, Nat.not_even_iff_odd.mpr ht, if_false]
  rw [← (transcript_prefix_round gen t i).1]
  exact (freshOddIndex_avoids t
    (fun j => (run gen t j).presentation)
    (fun j => (run gen t j).query)
    (fun j => (run gen t j).output)).1 i

theorem presentation_ne_of_lt (gen : FeedbackGenerator) {m n : ℕ} (hmn : m < n) :
    (runTranscript gen).presentation m ≠ (runTranscript gen).presentation n := by
  rcases Nat.even_or_odd n with hn | hn
  · rcases Nat.even_or_odd m with hm | hm
    · intro h
      rw [presentation_of_even gen hm, presentation_of_even gen hn] at h
      have hp := Nat.pow_right_injective (by omega) h
      rcases hm with ⟨a, rfl⟩
      rcases hn with ⟨b, rfl⟩
      omega
    · intro h
      have hord := presentation_of_odd_ordinary gen hm
      have hcore : (runTranscript gen).presentation n ∈ core := by
        rw [presentation_of_even gen hn]
        exact ⟨n / 2, rfl⟩
      exact hord (h ▸ hcore)
  · exact odd_presentation_ne_past gen hn ⟨m, hmn⟩

theorem presentation_injective (gen : FeedbackGenerator) :
    Function.Injective (runTranscript gen).presentation := by
  intro m n hmn
  rcases lt_trichotomy m n with hlt | heq | hgt
  · exact (presentation_ne_of_lt gen hlt hmn).elim
  · exact heq
  · exact (presentation_ne_of_lt gen hgt hmn.symm).elim
theorem scored_subset_core (gen : FeedbackGenerator) :
    scored (diagonalTarget gen) (runTranscript gen).presentation
      (runTranscript gen).output ⊆ core := by
  intro z hz
  rcases hz with ⟨hzK, t, hyt, hnotobs⟩
  by_contra hzcore
  rcases hzK with ⟨s, hxs⟩
  have hsodd : Odd s := by
    rcases Nat.even_or_odd s with hseven | hsodd
    · have hc : z ∈ core := by
        rw [← hxs, presentation_of_even gen hseven]
        exact ⟨s / 2, rfl⟩
      exact (hzcore hc).elim
    · exact hsodd
  have hts : t < s := by
    by_contra hst
    apply hnotobs
    exact ⟨s, Nat.le_of_not_gt hst, hxs⟩
  have hav := (freshOddIndex_avoids s
    (fun j => (run gen s j).presentation)
    (fun j => (run gen s j).query)
    (fun j => (run gen s j).output)).2.2 ⟨t, hts⟩
  apply hav
  rw [(transcript_prefix_round gen s ⟨t, hts⟩).2.2.2, hyt, ← hxs]
  change (runTranscript gen).presentation s = _
  change (run gen (s + 1) (Fin.last s)).presentation = _
  rw [run_last_presentation]
  simp [presenterValue, Nat.not_even_iff_odd.mpr hsodd]

theorem core_subset_target (gen : FeedbackGenerator) :
    core ⊆ diagonalTarget gen := by
  rintro z ⟨k, rfl⟩
  exact ⟨2 * k, presentation_even gen k⟩

theorem diagonalTarget_mem_class (gen : FeedbackGenerator) :
    diagonalTarget gen ∈ targetClass := by
  let A : Language := diagonalTarget gen ∩ ordinary
  refine ⟨A, Set.inter_subset_right, ?_⟩
  apply Set.Subset.antisymm
  · intro z hz
    by_cases hc : z ∈ core
    · exact Set.mem_union_left A hc
    · exact Set.mem_union_right core ⟨hz, hc⟩
  · intro z hz
    rcases hz with hc | hA
    · exact core_subset_target gen hc
    · exact hA.1
theorem queried_unseen_ordinary_not_target (gen : FeedbackGenerator)
    {t z : ℕ} (hq : (runTranscript gen).query t = some z)
    (hzordinary : z ∈ ordinary)
    (hunseen : z ∉ observedThrough (runTranscript gen).presentation t) :
    z ∉ diagonalTarget gen := by
  rintro ⟨s, hxs⟩
  by_cases hst : s ≤ t
  · exact hunseen ⟨s, hst, hxs⟩
  · have hts : t < s := Nat.lt_of_not_ge hst
    rcases Nat.even_or_odd s with hseven | hsodd
    · have hzcore : z ∈ core := by
        rw [← hxs, presentation_of_even gen hseven]
        exact ⟨s / 2, rfl⟩
      exact hzordinary hzcore
    · have hav := (freshOddIndex_avoids s
        (fun j => (run gen s j).presentation)
        (fun j => (run gen s j).query)
        (fun j => (run gen s j).output)).2.1 ⟨t, hts⟩ z
      apply hav
      · rw [(transcript_prefix_round gen s ⟨t, hts⟩).2.1]
        exact hq
      · rw [← hxs]
        change (runTranscript gen).presentation s = _
        change (run gen (s + 1) (Fin.last s)).presentation = _
        rw [run_last_presentation]
        simp [presenterValue, Nat.not_even_iff_odd.mpr hsodd]

theorem answer_condition_iff (gen : FeedbackGenerator) (t z : ℕ)
    (hq : (runTranscript gen).query t = some z) :
    (z ∈ core ∨ z ∈ observedThrough (runTranscript gen).presentation t) ↔
      z ∈ diagonalTarget gen := by
  constructor
  · rintro (hz | hz)
    · exact core_subset_target gen hz
    · rcases hz with ⟨s, hs, hxs⟩
      exact ⟨s, hxs⟩
  · intro hz
    by_cases hc : z ∈ core
    · exact Or.inl hc
    · refine Or.inr (by_contra fun ho => ?_)
      exact queried_unseen_ordinary_not_target gen hq hc ho hz

theorem finite_prefix_iff_observed (gen : FeedbackGenerator) (t z : ℕ) :
    (∃ i : Fin (t + 1), (run gen (t + 1) i).presentation = z) ↔
      z ∈ observedThrough (runTranscript gen).presentation t := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, Nat.le_of_lt_succ i.isLt,
      (transcript_prefix_round gen (t + 1) i).1.symm.trans hi⟩
  · rintro ⟨s, hs, hxs⟩
    let i : Fin (t + 1) := ⟨s, Nat.lt_succ_of_le hs⟩
    exact ⟨i, (transcript_prefix_round gen (t + 1) i).1.trans hxs⟩

theorem follows_protocol (gen : FeedbackGenerator) :
    FollowsProtocol gen (diagonalTarget gen) (runTranscript gen) := by
  intro t
  have hquery :
      (runTranscript gen).query t = gen.query t
        (fun i => (runTranscript gen).presentation i)
        (fun i => (runTranscript gen).answer i) := by
    change (run gen (t + 1) (Fin.last t)).query = _
    rw [run_last_query]
    congr 1 <;> funext i
    · refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [runTranscript, run]
      · simpa using (transcript_prefix_round gen t j).1
    · exact (transcript_prefix_round gen t i).2.2.1
  refine ⟨hquery, ?_, ?_⟩
  · change (run gen (t + 1) (Fin.last t)).answer = _
    simp only [run, Fin.lastCases_last]
    let prev := run gen t
    let xv := presenterValue t
      (fun i => (prev i).presentation)
      (fun i => (prev i).query)
      (fun i => (prev i).output)
    let xp : Fin (t + 1) → ℕ := Fin.lastCases xv (fun i => (prev i).presentation)
    let ap : Fin t → Option Bool := fun i => (prev i).answer
    let qv := gen.query t xp ap
    change (match qv with
      | none => none
      | some z => some (decide (z ∈ core ∨ ∃ i, xp i = z))) = _
    have hxp (i : Fin (t + 1)) :
        xp i = (run gen (t + 1) i).presentation := by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [xp, xv, prev, run]
      · simp [xp, xv, prev, run]
    have hap (i : Fin t) : ap i = (runTranscript gen).answer i := by
      exact (transcript_prefix_round gen t i).2.2.1
    have hqv : qv = (runTranscript gen).query t := by
      change gen.query t xp ap = _
      rw [hquery]
      congr 1 <;> funext i
      · exact (hxp i).trans (transcript_prefix_round gen (t + 1) i).1
      · exact hap i
    rw [hqv]
    cases hq : (runTranscript gen).query t with
    | none => rfl
    | some z =>
        have hprefix : (∃ i, xp i = z) ↔
            z ∈ observedThrough (runTranscript gen).presentation t := by
          rw [show (∃ i, xp i = z) ↔
              ∃ i, (run gen (t + 1) i).presentation = z by
            apply exists_congr
            intro i
            rw [hxp i]]
          exact finite_prefix_iff_observed gen t z
        have hiff : (z ∈ core ∨ ∃ i, xp i = z) ↔
            z ∈ diagonalTarget gen :=
          (or_congr Iff.rfl hprefix).trans (answer_condition_iff gen t z hq)
        by_cases hz : z ∈ core ∨ ∃ i, xp i = z
        · have hzK := hiff.mp hz
          simp [membershipAnswer, hz, hzK]
        · have hzK : z ∉ diagonalTarget gen := fun h => hz (hiff.mpr h)
          simp [membershipAnswer, hz, hzK]
  · change (run gen (t + 1) (Fin.last t)).output = _
    simp only [run, Fin.lastCases_last]
    congr 1 <;> funext i
    · refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [runTranscript, run]
      · simpa using (transcript_prefix_round gen t j).1
    · refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [runTranscript, run]
      · simpa using (transcript_prefix_round gen t j).2.2.1

theorem presentation_clean (gen : FeedbackGenerator) :
    Clean (runTranscript gen).presentation (diagonalTarget gen) := by
  intro t
  exact ⟨t, rfl⟩

theorem presentation_complete (gen : FeedbackGenerator) :
    Complete (runTranscript gen).presentation (diagonalTarget gen) := by
  intro z hz
  exact hz

theorem presentation_odd_le (gen : FeedbackGenerator) (k : ℕ) :
    (runTranscript gen).presentation (2 * k + 1) ≤ 12 * k + 9 := by
  change (run gen (2 * k + 1 + 1) (Fin.last (2 * k + 1))).presentation ≤ _
  rw [run_last_presentation]
  simp only [presenterValue, Nat.not_even_iff_odd.mpr (odd_two_mul_add_one k),
    if_false, oddCandidate]
  have h := freshOddIndex_le (2 * k + 1)
    (fun i => (run gen (2 * k + 1) i).presentation)
    (fun i => (run gen (2 * k + 1) i).query)
    (fun i => (run gen (2 * k + 1) i).output)
  omega

theorem diagonalTarget_infinite (gen : FeedbackGenerator) :
    (diagonalTarget gen).Infinite := by
  exact (Set.infinite_range_of_injective (Nat.pow_right_injective (by omega))).mono
    (core_subset_target gen)

noncomputable def orderedTarget (gen : FeedbackGenerator) : Stage3S2B.OrderedLanguage where
  carrier := diagonalTarget gen
  enumeration := Nat.nth (· ∈ diagonalTarget gen)
  enumeration_injective := Nat.nth_injective (diagonalTarget_infinite gen)
  range_enumeration := Nat.range_nth_of_infinite (diagonalTarget_infinite gen)

theorem orderedTarget_inherits (gen : FeedbackGenerator) :
    InheritsAmbientOrder (orderedTarget gen) :=
  Nat.nth_strictMono (diagonalTarget_infinite gen)

theorem orderedTarget_enumeration_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).enumeration n ≤ 12 * n + 9 := by
  classical
  let bound := 12 * n + 9
  let fillers : Fin (n + 1) → ℕ := fun k =>
    (runTranscript gen).presentation (2 * (k : ℕ) + 1)
  have hfillers : Function.Injective fillers := by
    intro a b hab
    have hround := presentation_injective gen hab
    apply Fin.ext
    omega
  have hsubset : Finset.univ.image fillers ⊆
      (Finset.range (bound + 1)).filter (· ∈ diagonalTarget gen) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨k, _, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, ⟨2 * (k : ℕ) + 1, rfl⟩⟩
    have hk : (k : ℕ) ≤ n := Nat.le_of_lt_succ k.isLt
    have hvalue := presentation_odd_le gen (k : ℕ)
    change (runTranscript gen).presentation (2 * (k : ℕ) + 1) < bound + 1
    dsimp [bound]
    omega
  have hcount : n < Nat.count (· ∈ diagonalTarget gen) (bound + 1) := by
    rw [Nat.count_eq_card_filter_range]
    have hcard := Finset.card_le_card hsubset
    have himage : (Finset.univ.image fillers).card = n + 1 := by
      rw [Finset.card_image_of_injective _ hfillers, Finset.card_univ,
        Fintype.card_fin]
    rw [himage] at hcard
    omega
  have hnth := Nat.nth_lt_of_lt_count hcount
  change Nat.nth (· ∈ diagonalTarget gen) n ≤ bound
  exact Nat.le_of_lt_succ hnth

noncomputable def coreExponent (z : ℕ) : ℕ := by
  classical
  exact if hz : z ∈ core then Classical.choose hz else 0

theorem pow_coreExponent {z : ℕ} (hz : z ∈ core) :
    2 ^ coreExponent z = z := by
  classical
  simp only [coreExponent, dif_pos hz]
  exact Classical.choose_spec hz

theorem square_le_two_pow {k : ℕ} (hk : 4 ≤ k) : k * k ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      rw [pow_succ]
      nlinarith

theorem orderedTarget_prefixCount_core_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).prefixCount core n ≤ Nat.sqrt (12 * n + 9) + 4 := by
  classical
  let indices := (Finset.range n).filter fun i =>
    (orderedTarget gen).enumeration i ∈ core
  let exponentAt := fun i => coreExponent ((orderedTarget gen).enumeration i)
  have hinj : Set.InjOn exponentAt (indices : Set ℕ) := by
    intro a ha b hb hab
    have haCore : (orderedTarget gen).enumeration a ∈ core :=
      (Finset.mem_filter.mp ha).2
    have hbCore : (orderedTarget gen).enumeration b ∈ core :=
      (Finset.mem_filter.mp hb).2
    apply (orderedTarget gen).enumeration_injective
    calc
      (orderedTarget gen).enumeration a = 2 ^ exponentAt a :=
        (pow_coreExponent haCore).symm
      _ = 2 ^ exponentAt b := by rw [hab]
      _ = (orderedTarget gen).enumeration b := pow_coreExponent hbCore
  have hcard : (indices.image exponentAt).card = indices.card := by
    rw [Finset.card_image_iff.mpr]
    intro a ha b hb hab
    exact hinj ha hb hab
  have hsubset : indices.image exponentAt ⊆
      Finset.range (Nat.sqrt (12 * n + 9) + 4) := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨i, hi, rfl⟩
    rw [Finset.mem_range]
    have hiRange : i < n := (Finset.mem_filter.mp hi).1 |> Finset.mem_range.mp
    have hiCore : (orderedTarget gen).enumeration i ∈ core :=
      (Finset.mem_filter.mp hi).2
    have henum : (orderedTarget gen).enumeration i ≤ 12 * n + 9 := by
      exact (orderedTarget_enumeration_le gen i).trans (by omega)
    by_cases hsmall : exponentAt i < 4
    · omega
    · have hsquare := square_le_two_pow (Nat.le_of_not_gt hsmall)
      change exponentAt i * exponentAt i ≤ 2 ^ exponentAt i at hsquare
      rw [show 2 ^ exponentAt i = (orderedTarget gen).enumeration i by
        exact pow_coreExponent hiCore] at hsquare
      have hsqrt : exponentAt i ≤ Nat.sqrt (12 * n + 9) :=
        Nat.le_sqrt.mpr (hsquare.trans henum)
      omega
  unfold GenLimit.KleinbergWei.OrderedLanguage.prefixCount
  change indices.card ≤ _
  rw [← hcard]
  exact (Finset.card_le_card hsubset).trans_eq (Finset.card_range _)


theorem sqrt_scaled_le (n : ℕ) :
    Nat.sqrt (12 * n + 9) + 4 ≤ 4 * (Nat.sqrt n + 1) + 4 := by
  have hn : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := by
    exact Nat.sqrt_lt.mp (Nat.lt_succ_self (Nat.sqrt n))
  have hroot : Nat.sqrt (12 * n + 9) < 4 * (Nat.sqrt n + 1) + 1 := by
    apply Nat.sqrt_lt.mpr
    nlinarith
  omega

theorem orderedTarget_prefixRatio_core_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).prefixRatio core n ≤
      ((4 : ℝ) * ((Nat.sqrt n : ℝ) + 1) + 4) / n := by
  by_cases hn : n = 0
  · simp [hn]
  · simp only [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, hn, if_false]
    apply div_le_div_of_nonneg_right
    · exact_mod_cast (orderedTarget_prefixCount_core_le gen n |>.trans (sqrt_scaled_le n))
    · positivity

theorem tendsto_scaled_sqrt_bound :
    Tendsto (fun n : ℕ =>
      ((4 : ℝ) * ((Nat.sqrt n : ℝ) + 1) + 4) / n) atTop (nhds 0) := by
  have h₁ :=
    GenLimit.InfiniteContamination.tendsto_sparseSqrt_add_one_div.const_mul (4 : ℝ)
  have h₂ := tendsto_inverse_atTop_nhds_zero_nat.const_mul (4 : ℝ)
  have hadd := h₁.add h₂
  convert hadd using 1
  · funext n
    simp only [div_eq_mul_inv]
    ring
  · norm_num

theorem orderedTarget_core_density_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity core = 0 := by
  unfold GenLimit.KleinbergWei.OrderedLanguage.upperDensity
  apply Filter.Tendsto.limsup_eq
  apply squeeze_zero
    (fun n => (orderedTarget gen).prefixRatio_nonneg core n)
    (orderedTarget_prefixRatio_core_le gen)
    tendsto_scaled_sqrt_bound

theorem orderedTarget_scored_density_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity
      (scored (diagonalTarget gen) (runTranscript gen).presentation
        (runTranscript gen).output) = 0 := by
  apply le_antisymm
  · exact ((orderedTarget gen).upperDensity_mono (scored_subset_core gen)).trans_eq
      (orderedTarget_core_density_zero gen)
  · exact (orderedTarget gen).upperDensity_nonneg _

def decodeTarget (K : Language) : Set ordinary :=
  {z | z.1 ∈ K}

theorem ordinary_infinite : ordinary.Infinite := by
  apply (Set.infinite_range_of_injective oddCandidate_injective).mono
  rintro _ ⟨k, rfl⟩
  exact oddCandidate_ordinary k

theorem targetClass_not_countable : ¬ targetClass.Countable := by
  intro hcount
  have himage : (decodeTarget '' targetClass).Countable := hcount.image decodeTarget
  have huniv : (Set.univ : Set (Set ordinary)).Countable := by
    apply himage.mono
    intro B _
    let A : Language := {n | ∃ hn : n ∈ ordinary, (⟨n, hn⟩ : ordinary) ∈ B}
    let K : Language := core ∪ A
    have hK : K ∈ targetClass := by
      refine ⟨A, ?_, rfl⟩
      rintro n ⟨hn, _⟩
      exact hn
    refine ⟨K, hK, ?_⟩
    ext z
    constructor
    · intro hz
      rcases hz with hzCore | hzA
      · exact (z.property hzCore).elim
      · exact hzA.choose_spec
    · intro hz
      exact Or.inr ⟨z.property, hz⟩
  haveI : Infinite ordinary := ordinary_infinite.to_subtype
  haveI : Countable (Set ordinary) := Set.countable_univ_iff.mp huniv
  exact GenLimit.UnionClosedness.powerSet_not_countable ordinary inferInstance

theorem uniformly_generatable : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t => 2 ^ t, Nat.pow_right_injective (by omega), 0, ?_⟩
  intro K hK t _
  rcases hK with ⟨A, hA, rfl⟩
  exact Set.mem_union_left A ⟨t, rfl⟩

end Stage3Proof

theorem stage3_result : Stage3S2B.MainClaim := by
  refine ⟨Stage3Proof.targetClass_not_countable,
    Stage3Proof.uniformly_generatable, ?_⟩
  intro gen _hvalid
  refine ⟨Stage3Proof.diagonalTarget gen,
    Stage3Proof.diagonalTarget_mem_class gen,
    Stage3Proof.diagonalPresenter,
    Stage3Proof.runTranscript gen,
    Stage3Proof.orderedTarget gen, ?_⟩
  exact ⟨rfl,
    Stage3Proof.orderedTarget_inherits gen,
    Stage3Proof.presented_by_diagonal gen,
    Stage3Proof.follows_protocol gen,
    Stage3Proof.presentation_clean gen,
    Stage3Proof.presentation_injective gen,
    Stage3Proof.presentation_complete gen,
    Stage3Proof.orderedTarget_scored_density_zero gen⟩
