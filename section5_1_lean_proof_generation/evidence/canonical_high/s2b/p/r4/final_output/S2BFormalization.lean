import Stage3Model
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic

open Set Filter

namespace Stage3Proof

open Stage3S2B

def extend {α : Type*} {t : ℕ} (f : Fin t → α) (a : α) : Fin (t + 1) → α :=
  Fin.lastCases a f

@[simp] theorem extend_last {α : Type*} {t : ℕ} (f : Fin t → α) (a : α) :
    extend f a (Fin.last t) = a := by simp [extend]

@[simp] theorem extend_castSucc {α : Type*} {t : ℕ} (f : Fin t → α) (a : α)
    (i : Fin t) : extend f a i.castSucc = f i := by simp [extend]

theorem candidate_not_core (n : ℕ) : 2 * n + 3 ∉ core := by
  rintro ⟨k, hk⟩
  cases k with
  | zero => simp at hk
  | succ k =>
      simp [pow_succ] at hk
      omega

theorem exists_candidate_not_mem (s : Finset ℕ) : ∃ n, 2 * n + 3 ∉ s := by
  by_cases hs : s.Nonempty
  · refine ⟨s.max' hs + 1, ?_⟩
    intro h
    have := Finset.le_max' s (2 * (s.max' hs + 1) + 3) h
    omega
  · exact ⟨0, by simpa [Finset.not_nonempty_iff_eq_empty.mp hs]⟩

noncomputable def pick (s : Finset ℕ) : ℕ :=
  2 * Nat.find (exists_candidate_not_mem s) + 3

theorem pick_not_mem (s : Finset ℕ) : pick s ∉ s :=
  Nat.find_spec (exists_candidate_not_mem s)

theorem pick_not_core (s : Finset ℕ) : pick s ∉ core :=
  candidate_not_core _

theorem pick_le (s : Finset ℕ) : pick s ≤ 2 * s.card + 3 := by
  classical
  let candidates := (Finset.range (s.card + 1)).image (fun n => 2 * n + 3)
  have hcard : candidates.card = s.card + 1 := by
    dsimp [candidates]
    rw [Finset.card_image_of_injective]
    · simp
    · intro a b h
      change 2 * a + 3 = 2 * b + 3 at h
      omega
  obtain ⟨z, hz, hzs⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := s) (t := candidates) (by omega : s.card < candidates.card)
  rw [Finset.mem_image] at hz
  obtain ⟨n, hn, rfl⟩ := hz
  have hnlt : n < s.card + 1 := by
    simpa [candidates] using hn
  have hnle : n ≤ s.card := Nat.lt_succ_iff.mp (by simpa using hnlt)
  unfold pick
  have hfind : Nat.find (exists_candidate_not_mem s) ≤ n :=
    Nat.find_min' (exists_candidate_not_mem s) hzs
  omega

structure State (t : ℕ) where
  presentation : Fin t → ℕ
  query : Fin t → Option ℕ
  answer : Fin t → Option Bool
  output : Fin t → ℕ
  admitted : Finset ℕ
  rejected : Finset ℕ

def State.empty : State 0 where
  presentation := Fin.elim0
  query := Fin.elim0
  answer := Fin.elim0
  output := Fin.elim0
  admitted := ∅
  rejected := ∅

noncomputable def presentedValue {t : ℕ} (s : State t) : ℕ :=
  if Even t then 2 ^ (t / 2) else pick (s.admitted ∪ s.rejected)

noncomputable def queryValue (gen : FeedbackGenerator) {t : ℕ} (s : State t) : Option ℕ :=
  gen.query t (extend s.presentation (presentedValue s)) s.answer

noncomputable def preAdmitted {t : ℕ} (s : State t) : Finset ℕ :=
  if Even t then s.admitted else insert (presentedValue s) s.admitted

noncomputable def answerValue (gen : FeedbackGenerator) {t : ℕ} (s : State t) : Option Bool := by
  classical
  exact match queryValue gen s with
  | none => none
  | some z => some (decide (z ∈ core ∨ z ∈ preAdmitted s))

noncomputable def queryRejected (gen : FeedbackGenerator) {t : ℕ} (s : State t) : Finset ℕ := by
  classical
  exact match queryValue gen s with
  | some z => if z ∈ core ∨ z ∈ preAdmitted s then s.rejected else insert z s.rejected
  | none => s.rejected

noncomputable def outputValue (gen : FeedbackGenerator) {t : ℕ} (s : State t) : ℕ :=
  gen.output t (extend s.presentation (presentedValue s))
    (extend s.answer (answerValue gen s))

noncomputable def nextRejected (gen : FeedbackGenerator) {t : ℕ} (s : State t) : Finset ℕ := by
  classical
  exact
  let r := queryRejected gen s
  let y := outputValue gen s
  if y ∈ core ∨ y ∈ preAdmitted s ∨ y ∈ r then r else insert y r

noncomputable def step (gen : FeedbackGenerator) {t : ℕ} (s : State t) : State (t + 1) where
  presentation := extend s.presentation (presentedValue s)
  query := extend s.query (queryValue gen s)
  answer := extend s.answer (answerValue gen s)
  output := extend s.output (outputValue gen s)
  admitted := preAdmitted s
  rejected := nextRejected gen s

noncomputable def states (gen : FeedbackGenerator) : (t : ℕ) → State t
  | 0 => State.empty
  | t + 1 => step gen (states gen t)

noncomputable def presentation (gen : FeedbackGenerator) (t : ℕ) : ℕ :=
  presentedValue (states gen t)

noncomputable def queries (gen : FeedbackGenerator) (t : ℕ) : Option ℕ :=
  queryValue gen (states gen t)

noncomputable def answers (gen : FeedbackGenerator) (t : ℕ) : Option Bool :=
  answerValue gen (states gen t)

noncomputable def outputs (gen : FeedbackGenerator) (t : ℕ) : ℕ :=
  outputValue gen (states gen t)

noncomputable def admittedLimit (gen : FeedbackGenerator) : Set ℕ :=
  {z | ∃ t, z ∈ (states gen t).admitted}

noncomputable def target (gen : FeedbackGenerator) : Set ℕ :=
  core ∪ admittedLimit gen

noncomputable def transcript (gen : FeedbackGenerator) : Transcript where
  presentation := presentation gen
  query := queries gen
  answer := answers gen
  output := outputs gen

noncomputable def presenter (gen : FeedbackGenerator) : CausalPresenter where
  next := fun t _ _ _ _ => presentation gen t


theorem states_presentation (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (states gen t).presentation i = presentation gen i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [states, step, presentation]
      · simpa [states, step] using ih j

theorem states_query (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (states gen t).query i = queries gen i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [states, step, queries]
      · simpa [states, step] using ih j

theorem states_answer (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (states gen t).answer i = answers gen i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [states, step, answers]
      · simpa [states, step] using ih j

theorem states_output (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (states gen t).output i = outputs gen i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [states, step, outputs]
      · simpa [states, step] using ih j

theorem admitted_subset_preAdmitted {t : ℕ} (s : State t) :
    s.admitted ⊆ preAdmitted s := by
  intro z hz
  simp only [preAdmitted]
  split <;> simp_all

theorem rejected_subset_queryRejected (gen : FeedbackGenerator) {t : ℕ} (s : State t) :
    s.rejected ⊆ queryRejected gen s := by
  classical
  intro z hz
  unfold queryRejected
  cases hq : queryValue gen s with
  | none => simpa [hq] using hz
  | some q =>
      by_cases hpos : q ∈ core ∨ q ∈ preAdmitted s
      · simpa [hq, hpos] using hz
      · simpa [hq, hpos] using Finset.mem_insert_of_mem hz

theorem queryRejected_subset_nextRejected (gen : FeedbackGenerator) {t : ℕ} (s : State t) :
    queryRejected gen s ⊆ nextRejected gen s := by
  classical
  intro z hz
  simp only [nextRejected]
  split <;> simp_all

theorem preAdmitted_card_le {t : ℕ} (s : State t) :
    (preAdmitted s).card ≤ s.admitted.card + 1 := by
  simp only [preAdmitted]
  split
  · omega
  · exact Finset.card_insert_le _ _

theorem queryRejected_card_le (gen : FeedbackGenerator) {t : ℕ} (s : State t) :
    (queryRejected gen s).card ≤ s.rejected.card + 1 := by
  classical
  unfold queryRejected
  split
  · split
    · omega
    · exact Finset.card_insert_le _ _
  · omega

theorem nextRejected_card_le (gen : FeedbackGenerator) {t : ℕ} (s : State t) :
    (nextRejected gen s).card ≤ s.rejected.card + 2 := by
  classical
  simp only [nextRejected]
  split
  · exact (queryRejected_card_le gen s).trans (by omega)
  · exact (Finset.card_insert_le _ _).trans
      (Nat.add_le_add_right (queryRejected_card_le gen s) 1)

theorem admitted_card_le (gen : FeedbackGenerator) (t : ℕ) :
    (states gen t).admitted.card ≤ t := by
  induction t with
  | zero => simp [states, State.empty]
  | succ t ih =>
      simpa [states, step] using (preAdmitted_card_le (states gen t)).trans (by omega)

theorem rejected_card_le (gen : FeedbackGenerator) (t : ℕ) :
    (states gen t).rejected.card ≤ 2 * t := by
  induction t with
  | zero => simp [states, State.empty]
  | succ t ih =>
      simpa [states, step] using (nextRejected_card_le gen (states gen t)).trans (by omega)

theorem union_card_le (gen : FeedbackGenerator) (t : ℕ) :
    ((states gen t).admitted ∪ (states gen t).rejected).card ≤ 3 * t := by
  exact (Finset.card_union_le _ _).trans (by
    have ha := admitted_card_le gen t
    have hr := rejected_card_le gen t
    omega)

theorem admitted_mono (gen : FeedbackGenerator) (t u : ℕ) (htu : t ≤ u) :
    (states gen t).admitted ⊆ (states gen u).admitted := by
  induction u with
  | zero =>
      have : t = 0 := Nat.eq_zero_of_le_zero htu
      subst t
      exact fun _ h => h
  | succ u ih =>
      rcases Nat.eq_or_lt_of_le htu with rfl | hlt
      · exact fun _ h => h
      · exact (ih (Nat.le_of_lt_succ hlt)).trans (by
          simpa [states, step] using admitted_subset_preAdmitted (states gen u))

theorem rejected_mono (gen : FeedbackGenerator) (t u : ℕ) (htu : t ≤ u) :
    (states gen t).rejected ⊆ (states gen u).rejected := by
  induction u with
  | zero =>
      have : t = 0 := Nat.eq_zero_of_le_zero htu
      subst t
      exact fun _ h => h
  | succ u ih =>
      rcases Nat.eq_or_lt_of_le htu with rfl | hlt
      · exact fun _ h => h
      · refine (ih (Nat.le_of_lt_succ hlt)).trans ?_
        simpa [states, step] using
          (rejected_subset_queryRejected gen (states gen u)).trans
            (queryRejected_subset_nextRejected gen (states gen u))

def Good {t : ℕ} (s : State t) : Prop :=
  Disjoint (s.admitted : Set ℕ) s.rejected ∧
  (s.admitted : Set ℕ) ⊆ ordinary ∧ (s.rejected : Set ℕ) ⊆ ordinary

theorem preAdmitted_good {t : ℕ} (s : State t) (hs : Good s) :
    Disjoint (preAdmitted s : Set ℕ) s.rejected ∧
      (preAdmitted s : Set ℕ) ⊆ ordinary := by
  classical
  rcases hs with ⟨hdis, hadm, hrej⟩
  simp only [preAdmitted]
  split
  · exact ⟨hdis, hadm⟩
  · have hpick : presentedValue s = pick (s.admitted ∪ s.rejected) := by
      simp [presentedValue, *]
    constructor
    · rw [Finset.coe_insert, Set.disjoint_insert_left]
      exact ⟨by
        rw [hpick]
        exact fun h => pick_not_mem (s.admitted ∪ s.rejected) (Finset.mem_union_right _ h), hdis⟩
    · intro z hz
      rw [Finset.mem_coe, Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · rw [hpick]
        exact pick_not_core _
      · exact hadm hz

theorem queryRejected_good (gen : FeedbackGenerator) {t : ℕ} (s : State t)
    (hs : Good s) :
    Disjoint (preAdmitted s : Set ℕ) (queryRejected gen s) ∧
      (queryRejected gen s : Set ℕ) ⊆ ordinary := by
  classical
  rcases preAdmitted_good s hs with ⟨hdis, hadm⟩
  rcases hs with ⟨_, _, hrej⟩
  cases hq : queryValue gen s with
  | none => simpa [queryRejected, hq] using And.intro hdis hrej
  | some z =>
      by_cases hpos : z ∈ core ∨ z ∈ preAdmitted s
      · simpa [queryRejected, hq, hpos] using And.intro hdis hrej
      · simp only [queryRejected, hq, hpos, ↓reduceIte]
        constructor
        · rw [Finset.coe_insert, Set.disjoint_insert_right]
          exact ⟨by aesop, hdis⟩
        · intro w hw
          rw [Finset.mem_coe, Finset.mem_insert] at hw
          rcases hw with rfl | hw
          · exact fun hc => hpos (Or.inl hc)
          · exact hrej hw

theorem step_good (gen : FeedbackGenerator) {t : ℕ} (s : State t) (hs : Good s) :
    Good (step gen s) := by
  classical
  rcases queryRejected_good gen s hs with ⟨hdis, hrej⟩
  rcases preAdmitted_good s hs with ⟨_, hadm⟩
  simp only [Good, step]
  simp only [nextRejected]
  split
  · exact ⟨hdis, hadm, hrej⟩
  · constructor
    · rw [Finset.coe_insert, Set.disjoint_insert_right]
      exact ⟨by aesop, hdis⟩
    · exact ⟨hadm, by
        intro z hz
        rw [Finset.mem_coe, Finset.mem_insert] at hz
        rcases hz with rfl | hz
        · aesop
        · exact hrej hz⟩

theorem states_good (gen : FeedbackGenerator) (t : ℕ) : Good (states gen t) := by
  induction t with
  | zero => simp [states, State.empty, Good]
  | succ t ih => simpa [states] using step_good gen (states gen t) ih

theorem target_mem_class (gen : FeedbackGenerator) : target gen ∈ targetClass := by
  refine ⟨admittedLimit gen, ?_, rfl⟩
  intro z hz
  rcases hz with ⟨t, ht⟩
  exact (states_good gen t).2.1 ht

theorem presented_by (gen : FeedbackGenerator) :
    PresentedBy (presenter gen) (transcript gen) := by
  intro t
  rfl


theorem disjoint_across (gen : FeedbackGenerator) {t u z : ℕ}
    (ha : z ∈ (states gen t).admitted) (hr : z ∈ (states gen u).rejected) : False := by
  let v := max t u
  have hat : z ∈ (states gen v).admitted := admitted_mono gen t v (le_max_left _ _) ha
  have hrt : z ∈ (states gen v).rejected := rejected_mono gen u v (le_max_right _ _) hr
  exact (states_good gen v).1.le_bot ⟨hat, hrt⟩

theorem preAdmitted_subset_limit (gen : FeedbackGenerator) (t : ℕ) :
    (preAdmitted (states gen t) : Set ℕ) ⊆ admittedLimit gen := by
  intro z hz
  exact ⟨t + 1, by simpa [states, step] using hz⟩

theorem query_negative_rejected (gen : FeedbackGenerator) (t z : ℕ)
    (hq : queries gen t = some z)
    (hn : answers gen t = some false) :
    z ∈ (states gen (t + 1)).rejected := by
  classical
  have hq' : queryValue gen (states gen t) = some z := hq
  have hn' : answerValue gen (states gen t) = some false := hn
  simp only [answerValue, hq'] at hn'
  have hneg : ¬(z ∈ core ∨ z ∈ preAdmitted (states gen t)) := by
    simpa using hn'
  simp only [states, step]
  apply queryRejected_subset_nextRejected gen
  simp [queryRejected, hq', hneg]

theorem answer_truthful (gen : FeedbackGenerator) (t : ℕ) :
    answers gen t = match queries gen t with
      | none => none
      | some z => some (membershipAnswer (target gen) z) := by
  classical
  unfold answers queries answerValue
  cases hq : queryValue gen (states gen t) with
  | none => simp [hq]
  | some z =>
      simp only [hq]
      congr 1
      apply Bool.eq_iff_iff.mpr
      simp only [membershipAnswer, decide_eq_true_eq]
      constructor
      · intro hz
        rcases hz with hz | hz
        · exact Or.inl hz
        · exact Or.inr (preAdmitted_subset_limit gen t hz)
      · intro hz
        rcases hz with hz | hz
        · exact Or.inl hz
        · by_contra hpre
          have hr : z ∈ (states gen (t + 1)).rejected := by
            apply query_negative_rejected gen t z
            · exact hq
            · simp [answers, answerValue, hq, hpre, hz]
          rcases hz with ⟨u, hu⟩
          exact disjoint_across gen hu hr

theorem follows_protocol (gen : FeedbackGenerator) :
    FollowsProtocol gen (target gen) (transcript gen) := by
  intro t
  constructor
  · change queryValue gen (states gen t) = gen.query t _ _
    unfold queryValue
    congr 1
    · funext i
      simpa using states_presentation gen (t + 1) i
    · funext i
      exact states_answer gen t i
  constructor
  · exact answer_truthful gen t
  · change outputValue gen (states gen t) = gen.output t _ _
    unfold outputValue
    congr 1
    · funext i
      simpa using states_presentation gen (t + 1) i
    · funext i
      simpa using states_answer gen (t + 1) i

theorem presentation_mem_target (gen : FeedbackGenerator) (t : ℕ) :
    presentation gen t ∈ target gen := by
  by_cases he : Even t
  · left
    simp [presentation, presentedValue, he, core]
  · right
    apply preAdmitted_subset_limit gen t
    change presentation gen t ∈ preAdmitted (states gen t)
    simp [presentation, preAdmitted, he]

theorem clean (gen : FeedbackGenerator) :
    Clean (presentation gen) (target gen) := presentation_mem_target gen

theorem admitted_origin (gen : FeedbackGenerator) {t z : ℕ}
    (hz : z ∈ (states gen t).admitted) :
    ∃ s < t, ¬ Even s ∧ presentation gen s = z := by
  induction t with
  | zero => simp [states, State.empty] at hz
  | succ t ih =>
      simp only [states, step] at hz
      simp only [preAdmitted] at hz
      split at hz
      · rcases ih hz with ⟨s, hs, ho, hp⟩
        exact ⟨s, hs.trans_le (Nat.le_succ _), ho, hp⟩
      · rw [Finset.mem_insert] at hz
        rcases hz with hz | hz
        · exact ⟨t, Nat.lt_succ_self _, by assumption, by simpa [presentation] using hz.symm⟩
        · rcases ih hz with ⟨s, hs, ho, hp⟩
          exact ⟨s, hs.trans_le (Nat.le_succ _), ho, hp⟩

theorem presentation_ne_of_lt (gen : FeedbackGenerator) {t u : ℕ} (htu : t < u) :
    presentation gen t ≠ presentation gen u := by
  by_cases ht : Even t
  · by_cases hu : Even u
    · obtain ⟨a, rfl⟩ := ht
      obtain ⟨b, rfl⟩ := hu
      have hab : a < b := by omega
      have hada : a + a = a * 2 := by omega
      have hadb : b + b = b * 2 := by omega
      have hpa : presentation gen (a + a) = 2 ^ a := by
        simp [presentation, presentedValue, show Even (a + a) from ⟨a, by omega⟩,
          hada, Nat.mul_div_left]
      have hpb : presentation gen (b + b) = 2 ^ b := by
        simp [presentation, presentedValue, show Even (b + b) from ⟨b, by omega⟩,
          hadb, Nat.mul_div_left]
      rw [hpa, hpb]
      exact ne_of_lt (Nat.pow_lt_pow_right (a := 2) (by norm_num) hab)
    · intro h
      have hc : presentation gen t ∈ core := by
        simp [presentation, presentedValue, ht, core]
      have hnc : presentation gen u ∉ core := by
        simp [presentation, presentedValue, hu, pick_not_core]
      exact hnc (h ▸ hc)
  · by_cases hu : Even u
    · intro h
      have hnc : presentation gen t ∉ core := by
        simp [presentation, presentedValue, ht, pick_not_core]
      have hc : presentation gen u ∈ core := by
        simp [presentation, presentedValue, hu, core]
      exact hnc (h ▸ hc)
    · intro h
      have hmem : presentation gen t ∈ (states gen u).admitted := by
        have htmem : presentation gen t ∈ (states gen (t + 1)).admitted := by
          change presentation gen t ∈ preAdmitted (states gen t)
          simp [presentation, preAdmitted, ht]
        exact admitted_mono gen (t + 1) u htu htmem
      have hnot : presentation gen u ∉ (states gen u).admitted := by
        simp only [presentation, presentedValue, hu, if_false]
        intro hz
        exact pick_not_mem ((states gen u).admitted ∪ (states gen u).rejected)
          (Finset.mem_union_left _ hz)
      exact hnot (h ▸ hmem)

theorem presentation_injective (gen : FeedbackGenerator) :
    Function.Injective (presentation gen) := by
  intro t u h
  rcases lt_trichotomy t u with hlt | rfl | hgt
  · exact False.elim (presentation_ne_of_lt gen hlt h)
  · rfl
  · exact False.elim (presentation_ne_of_lt gen hgt h.symm)

theorem complete (gen : FeedbackGenerator) :
    Complete (presentation gen) (target gen) := by
  intro z hz
  rcases hz with hz | hz
  · rcases hz with ⟨k, rfl⟩
    refine ⟨2 * k, ?_⟩
    simp [presentation, presentedValue, show Even (2 * k) from ⟨k, by omega⟩]
  · rcases hz with ⟨t, ht⟩
    rcases admitted_origin gen ht with ⟨s, _, _, hs⟩
    exact ⟨s, hs⟩


theorem preAdmitted_observed (gen : FeedbackGenerator) {t z : ℕ}
    (hz : z ∈ preAdmitted (states gen t)) : z ∈ observedThrough (presentation gen) t := by
  simp only [preAdmitted] at hz
  split at hz
  · rcases admitted_origin gen hz with ⟨s, hs, _, hsz⟩
    exact ⟨s, Nat.le_of_lt hs, hsz⟩
  · rw [Finset.mem_insert] at hz
    rcases hz with hz | hz
    · exact ⟨t, le_rfl, by simpa [presentation] using hz.symm⟩
    · rcases admitted_origin gen hz with ⟨s, hs, _, hsz⟩
      exact ⟨s, Nat.le_of_lt hs, hsz⟩

theorem output_reserved (gen : FeedbackGenerator) {t z : ℕ}
    (hy : outputs gen t = z) (hc : z ∉ core)
    (ha : z ∉ preAdmitted (states gen t)) :
    z ∈ (states gen (t + 1)).rejected := by
  classical
  simp only [states, step]
  have hy' : outputValue gen (states gen t) = z := hy
  simp only [nextRejected, hy', hc, ha, false_or]
  split
  · assumption
  · exact Finset.mem_insert_self _ _

theorem scored_subset_core (gen : FeedbackGenerator) :
    scored (target gen) (presentation gen) (outputs gen) ⊆ core := by
  intro z hz
  rcases hz with ⟨hzt, t, hy, hfresh⟩
  by_contra hc
  have ha : z ∉ preAdmitted (states gen t) := fun ha => hfresh (preAdmitted_observed gen ha)
  have hr := output_reserved gen hy hc ha
  rcases hzt with hcore | hadm
  · exact hc hcore
  · rcases hadm with ⟨u, hu⟩
    exact disjoint_across gen hu hr

theorem odd_presentation_le (gen : FeedbackGenerator) (r : ℕ) :
    presentation gen (2 * r + 1) ≤ 12 * r + 9 := by
  have hodd : ¬Even (2 * r + 1) := by
    rintro ⟨k, hk⟩
    omega
  rw [presentation, presentedValue, if_neg hodd]
  refine (pick_le _).trans ?_
  have hcard := union_card_le gen (2 * r + 1)
  omega

theorem target_infinite (gen : FeedbackGenerator) : (target gen).Infinite := by
  have hinj : Function.Injective (fun k : ℕ => 2 ^ k) := by
    intro a b h
    rcases lt_trichotomy a b with hab | rfl | hba
    · exact False.elim ((Nat.pow_lt_pow_right (a := 2) (by norm_num) hab).ne h)
    · rfl
    · exact False.elim ((Nat.pow_lt_pow_right (a := 2) (by norm_num) hba).ne h.symm)
  exact (Set.infinite_range_of_injective hinj).mono (fun _ hz => Or.inl hz)

noncomputable def orderedTarget (gen : FeedbackGenerator) : OrderedLanguage where
  carrier := target gen
  enumeration := Nat.nth (fun z => z ∈ target gen)
  enumeration_injective := (Nat.nth_strictMono (target_infinite gen)).injective
  range_enumeration := Nat.range_nth_of_infinite (target_infinite gen)

theorem orderedTarget_strictMono (gen : FeedbackGenerator) :
    StrictMono (orderedTarget gen).enumeration :=
  Nat.nth_strictMono (target_infinite gen)

noncomputable def targetPrefix (gen : FeedbackGenerator) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter (fun z => z ∈ target gen)

theorem target_prefix_lower (gen : FeedbackGenerator) (n : ℕ) :
    n + 1 ≤ (targetPrefix gen (12 * n + 10)).card := by
  classical
  let samples := (Finset.range (n + 1)).image (fun r => presentation gen (2 * r + 1))
  have hcard : samples.card = n + 1 := by
    dsimp [samples]
    rw [Finset.card_image_of_injective]
    · simp
    · exact (presentation_injective gen).comp (fun _ _ h => by omega)
  have hsub : samples ⊆ targetPrefix gen (12 * n + 10) := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    rw [targetPrefix, Finset.mem_filter, Finset.mem_range]
    have hrlt : r < n + 1 := by simpa using hr
    have hrle : r ≤ n := by omega
    exact ⟨(odd_presentation_le gen r).trans_lt (by omega), presentation_mem_target gen _⟩
  exact hcard ▸ Finset.card_le_card hsub

theorem orderedTarget_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).enumeration n ≤ 12 * n + 9 := by
  classical
  change Nat.nth (fun z => z ∈ target gen) n ≤ _
  have hcount := target_prefix_lower gen n
  rw [targetPrefix, ← Nat.count_eq_card_filter_range] at hcount
  have hlt : n < Nat.count (Membership.mem (target gen)) (12 * n + 10) := by omega
  exact Nat.le_of_lt_succ (by
    simpa only [Nat.add_comm 1 (12 * n + 9)] using
      (Nat.nth_lt_of_lt_count hlt))

theorem sq_le_two_pow_succ (k : ℕ) : k * k ≤ 2 ^ (k + 1) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      by_cases hk : k < 4
      · have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
        rcases hk' with rfl | rfl | rfl | rfl <;> norm_num
      · let j := k - 1
        have hj : 3 ≤ j := by omega
        have hkj : k = j + 1 := by omega
        have hprev := ih j (by omega)
        have hsq : k * k ≤ 2 * (j * j) := by rw [hkj]; nlinarith
        calc
          k * k ≤ 2 * (j * j) := hsq
          _ ≤ 2 * 2 ^ (j + 1) := Nat.mul_le_mul_left 2 hprev
          _ = 2 ^ (k + 1) := by
            rw [hkj, pow_succ, pow_succ]
            ring

noncomputable def coreExponent (gen : FeedbackGenerator) (i : ℕ) : ℕ := by
  classical
  exact if h : (orderedTarget gen).enumeration i ∈ core then Nat.find h else 0

theorem coreExponent_spec (gen : FeedbackGenerator) {i : ℕ}
    (hi : (orderedTarget gen).enumeration i ∈ core) :
    2 ^ coreExponent gen i = (orderedTarget gen).enumeration i := by
  classical
  simp only [coreExponent, dif_pos hi]
  exact Nat.find_spec hi

noncomputable def coreIndices (gen : FeedbackGenerator) (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter (fun i => (orderedTarget gen).enumeration i ∈ core)

theorem core_prefix_count_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).prefixCount core n ≤ Nat.sqrt (42 * n) + 1 := by
  classical
  change (coreIndices gen n).card ≤ _
  have hcard := Finset.card_le_card_of_injOn (s := coreIndices gen n)
    (t := Finset.range (Nat.sqrt (42 * n) + 1)) (coreExponent gen)
  apply (hcard ?_ ?_).trans_eq
  · simp
  · intro i hi
    change i ∈ coreIndices gen n at hi
    rw [coreIndices, Finset.mem_filter, Finset.mem_range] at hi
    change coreExponent gen i ∈ Finset.range (Nat.sqrt (42 * n) + 1)
    rw [Finset.mem_range]
    rcases hi with ⟨hin, hicore⟩
    have hnpos : 0 < n := by omega
    have hvalue : (orderedTarget gen).enumeration i ≤ 21 * n := by
      exact (orderedTarget_le gen i).trans (by omega)
    have hpow := sq_le_two_pow_succ (coreExponent gen i)
    have hspec := coreExponent_spec gen hicore
    have hsquare : coreExponent gen i * coreExponent gen i ≤ 42 * n := by
      rw [pow_succ, hspec] at hpow
      omega
    exact Nat.lt_succ_iff.mpr (Nat.le_sqrt.mpr hsquare)
  · intro i hi j hj hij
    change i ∈ coreIndices gen n at hi
    change j ∈ coreIndices gen n at hj
    rw [coreIndices, Finset.mem_filter] at hi hj
    apply (orderedTarget gen).enumeration_injective
    rw [← coreExponent_spec gen hi.2, ← coreExponent_spec gen hj.2, hij]

theorem sqrt_ratio_tendsto :
    Tendsto (fun n : ℕ => ((Nat.sqrt (42 * n) + 1 : ℕ) : ℝ) / n) atTop (nhds 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_gt (2 / ε)
  have hmpos : 0 < m := by
    have : 0 < (2 / ε : ℝ) := div_pos (by norm_num) hε
    exact_mod_cast this.trans hm
  have htwo : (2 : ℝ) / m < ε := by
    have hmreal : (2 : ℝ) / ε < m := hm
    have hmul : (2 : ℝ) < m * ε := by
      exact (div_lt_iff₀ hε).mp hmreal
    rw [div_lt_iff₀ (show (0 : ℝ) < m by positivity)]
    nlinarith
  refine ⟨max (42 * m * m) m, ?_⟩
  intro n hn
  have hlarge : 42 * m * m ≤ n := (le_max_left _ _).trans hn
  have hmn : m ≤ n := (le_max_right _ _).trans hn
  have hnpos : 0 < n := lt_of_lt_of_le hmpos hmn
  let s := Nat.sqrt (42 * n)
  have hsquare : s * s ≤ 42 * n := by
    exact Nat.sqrt_le _
  have hms : m * s ≤ n := by nlinarith
  have hnat : m * (s + 1) ≤ 2 * n := by
    simpa [Nat.mul_add, two_mul] using Nat.add_le_add hms hmn
  have hbound : (((s + 1 : ℕ) : ℝ) / n) ≤ (2 : ℝ) / m := by
    rw [div_le_div_iff₀ (show (0 : ℝ) < n by exact_mod_cast hnpos)
      (show (0 : ℝ) < m by exact_mod_cast hmpos)]
    exact_mod_cast (show (s + 1) * m ≤ 2 * n by simpa [mul_comm] using hnat)
  rw [Real.dist_eq]
  have hnonneg : 0 ≤ (((s + 1 : ℕ) : ℝ) / n) := by positivity
  rw [sub_zero, abs_of_nonneg hnonneg]
  exact hbound.trans_lt htwo

theorem core_prefixRatio_tendsto (gen : FeedbackGenerator) :
    Tendsto ((orderedTarget gen).prefixRatio core) atTop (nhds 0) := by
  refine squeeze_zero'
    (f := (orderedTarget gen).prefixRatio core)
    (g := fun n : ℕ => ((Nat.sqrt (42 * n) + 1 : ℕ) : ℝ) / n) ?_ ?_ sqrt_ratio_tendsto
  · filter_upwards [] with n
    by_cases hn : n = 0
    · simp [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, hn]
    · simp [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, hn]
      positivity
  · filter_upwards [] with n
    by_cases hn : n = 0
    · simp [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, hn]
    · simp only [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, hn, if_false]
      gcongr
      exact core_prefix_count_le gen n

theorem prefixRatio_mono (K : OrderedLanguage) {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    K.prefixRatio A n ≤ K.prefixRatio B n := by
  classical
  by_cases hn : n = 0
  · simp [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, hn]
  · simp only [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, hn, if_false]
    gcongr
    apply Finset.card_le_card
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hAB hi.2⟩

theorem scored_prefixRatio_tendsto (gen : FeedbackGenerator) :
    Tendsto ((orderedTarget gen).prefixRatio
      (scored (target gen) (presentation gen) (outputs gen))) atTop (nhds 0) := by
  refine squeeze_zero'
    (f := (orderedTarget gen).prefixRatio
      (scored (target gen) (presentation gen) (outputs gen)))
    (g := (orderedTarget gen).prefixRatio core) ?_ ?_ (core_prefixRatio_tendsto gen)
  · filter_upwards [] with n
    by_cases hn : n = 0
    · simp [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, hn]
    · simp [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, hn]
      positivity
  · filter_upwards [] with n
    exact prefixRatio_mono _ (scored_subset_core gen) n

theorem scored_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity
      (scored (target gen) (presentation gen) (outputs gen)) = 0 := by
  exact (scored_prefixRatio_tendsto gen).limsup_eq

def codedOrdinary (A : Set ℕ) : Set ℕ :=
  {z | ∃ n ∈ A, z = 2 * n + 3}

def codedTarget (A : Set ℕ) : Set ℕ :=
  core ∪ codedOrdinary A

theorem codedOrdinary_subset_ordinary (A : Set ℕ) : codedOrdinary A ⊆ ordinary := by
  rintro z ⟨n, _, rfl⟩
  exact candidate_not_core n

theorem codedTarget_mem_class (A : Set ℕ) : codedTarget A ∈ targetClass := by
  exact ⟨codedOrdinary A, codedOrdinary_subset_ordinary A, rfl⟩

theorem codedTarget_code_mem (A : Set ℕ) (n : ℕ) :
    2 * n + 3 ∈ codedTarget A ↔ n ∈ A := by
  constructor
  · rintro (hcore | ⟨m, hm, heq⟩)
    · exact False.elim (candidate_not_core n hcore)
    · have : m = n := by omega
      simpa [this] using hm
  · intro hn
    exact Or.inr ⟨n, hn, rfl⟩

theorem codedTarget_injective : Function.Injective codedTarget := by
  intro A B hAB
  ext n
  rw [← codedTarget_code_mem A n, hAB, codedTarget_code_mem B n]

theorem sets_not_countable : ¬ Countable (Set ℕ) := by
  intro h
  letI : Countable (Set ℕ) := h
  obtain ⟨f, hf⟩ := (countable_iff_exists_surjective (α := Set ℕ)).mp inferInstance
  let D : Set ℕ := {n | n ∉ f n}
  obtain ⟨n, hn⟩ := hf D
  have hmem : n ∈ D ↔ n ∉ D := by
    change (n ∉ f n) ↔ n ∉ D
    rw [hn]
  exact iff_not_self hmem

theorem targetClass_not_countable : ¬ targetClass.Countable := by
  intro hclass
  have hrange : (Set.range codedTarget).Countable := by
    apply hclass.mono
    rintro K ⟨A, rfl⟩
    exact codedTarget_mem_class A
  apply sets_not_countable
  letI : Countable (Set.range codedTarget) := hrange.to_subtype
  let embedding : Set ℕ → Set.range codedTarget :=
    fun A => ⟨codedTarget A, Set.mem_range_self A⟩
  exact (show Function.Injective embedding by
    intro A B hAB
    apply codedTarget_injective
    exact congrArg Subtype.val hAB).countable

theorem uniformly_generatable : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t => 2 ^ t, Nat.pow_right_injective (by omega), 0, ?_⟩
  intro K hK t _
  rcases hK with ⟨A, _, rfl⟩
  exact Or.inl ⟨t, rfl⟩

theorem negative_claim : NegativeClaim := by
  intro gen _
  refine ⟨target gen, target_mem_class gen, presenter gen, transcript gen,
    orderedTarget gen, ?_⟩
  exact ⟨rfl, orderedTarget_strictMono gen, presented_by gen, follows_protocol gen,
    clean gen, presentation_injective gen, complete gen, scored_upperDensity_zero gen⟩

end Stage3Proof

theorem stage3_result : Stage3S2B.MainClaim := by
  exact ⟨Stage3Proof.targetClass_not_countable, Stage3Proof.uniformly_generatable,
    Stage3Proof.negative_claim⟩
