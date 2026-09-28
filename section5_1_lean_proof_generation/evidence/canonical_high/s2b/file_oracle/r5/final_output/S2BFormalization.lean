import Stage3Model
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import GenLimit.Paper39_DenseGeneration.Abstract.Density
import Mathlib.Data.Nat.Nth

open Set Filter

namespace Stage3Proof

open Stage3S2B

def oddValue (k : ℕ) : ℕ := 2 * k + 3

theorem oddValue_injective : Function.Injective oddValue := by
  intro a b h
  simp [oddValue] at h
  omega

theorem oddValue_not_core (k : ℕ) : oddValue k ∉ core := by
  rintro ⟨e, he⟩
  cases e with
  | zero => simp [oddValue] at he
  | succ e =>
      have hEven : Even (2 ^ (Nat.succ e)) := by
        refine ⟨2 ^ e, by simp [pow_succ, Nat.mul_two]⟩
      have hOdd : ¬ Even (oddValue k) := by
        simp [oddValue, even_iff_two_dvd]
      exact hOdd (he ▸ hEven)

structure Prefix (gen : FeedbackGenerator) (t : ℕ) where
  presentation : Fin t → ℕ
  query : Fin t → Option ℕ
  answer : Fin t → Option Bool
  output : Fin t → ℕ
  rejected : Finset ℕ

def append {α : Type*} {t : ℕ} (f : Fin t → α) (a : α) : Fin (t + 1) → α :=
  Fin.lastCases a f

@[simp] theorem append_last {α : Type*} {t : ℕ} (f : Fin t → α) (a : α) :
    append f a (Fin.last t) = a := by
  simp [append]

@[simp] theorem append_castSucc {α : Type*} {t : ℕ} (f : Fin t → α) (a : α)
    (i : Fin t) : append f a i.castSucc = f i := by
  simp [append]

def seen {gen : FeedbackGenerator} {t : ℕ} (s : Prefix gen t) : Finset ℕ :=
  Finset.univ.image s.presentation

def assigned {gen : FeedbackGenerator} {t : ℕ} (s : Prefix gen t) : Finset ℕ :=
  s.rejected ∪ seen s

theorem exists_unused_odd {gen : FeedbackGenerator} {t : ℕ} (s : Prefix gen t) :
    ∃ k, oddValue k ∉ assigned s := by
  have hinf : (Set.range oddValue).Infinite := Set.infinite_range_of_injective oddValue_injective
  obtain ⟨z, ⟨k, rfl⟩, hk⟩ := hinf.exists_notMem_finset (assigned s)
  exact ⟨k, hk⟩

noncomputable def unusedIndex {gen : FeedbackGenerator} {t : ℕ} (s : Prefix gen t) : ℕ :=
  Nat.find (exists_unused_odd s)

theorem unusedIndex_spec {gen : FeedbackGenerator} {t : ℕ} (s : Prefix gen t) :
    oddValue (unusedIndex s) ∉ assigned s :=
  Nat.find_spec (exists_unused_odd s)

noncomputable def nextPresentation {gen : FeedbackGenerator} {t : ℕ}
    (s : Prefix gen t) : ℕ :=
  if Even t then 2 ^ (t / 2) else oddValue (unusedIndex s)

noncomputable def addUnlessSeen (currentSeen : Finset ℕ) (s : Finset ℕ) (z : ℕ) : Finset ℕ := by
  classical
  exact if z ∈ core ∨ z ∈ currentSeen then s else insert z s

noncomputable def addQueryUnlessSeen (currentSeen : Finset ℕ) (s : Finset ℕ)
    (q : Option ℕ) : Finset ℕ := by
  classical
  exact match q with
  | none => s
  | some z => addUnlessSeen currentSeen s z

theorem card_addUnlessSeen (currentSeen s : Finset ℕ) (z : ℕ) :
    (addUnlessSeen currentSeen s z).card ≤ s.card + 1 := by
  classical
  unfold addUnlessSeen
  split
  · omega
  · exact Finset.card_insert_le _ _

theorem card_addQueryUnlessSeen (currentSeen s : Finset ℕ) (q : Option ℕ) :
    (addQueryUnlessSeen currentSeen s q).card ≤ s.card + 1 := by
  cases q with
  | none => simp [addQueryUnlessSeen]
  | some z => simpa [addQueryUnlessSeen] using card_addUnlessSeen currentSeen s z

noncomputable def step {gen : FeedbackGenerator} {t : ℕ}
    (s : Prefix gen t) : Prefix gen (t + 1) := by
  classical
  let x := nextPresentation s
  let xhist := append s.presentation x
  let q := gen.query t xhist s.answer
  let currentSeen := insert x (seen s)
  let a : Option Bool := q.map fun z => decide (z ∈ core ∨ z ∈ currentSeen)
  let ahist := append s.answer a
  let y := gen.output t xhist ahist
  let r1 := addQueryUnlessSeen currentSeen s.rejected q
  let r2 := addUnlessSeen currentSeen r1 y
  exact {
    presentation := xhist
    query := append s.query q
    answer := ahist
    output := append s.output y
    rejected := r2
  }

noncomputable def prefixes (gen : FeedbackGenerator) : (t : ℕ) → Prefix gen t
  | 0 => {
      presentation := Fin.elim0
      query := Fin.elim0
      answer := Fin.elim0
      output := Fin.elim0
      rejected := ∅
    }
  | t + 1 => step (prefixes gen t)

noncomputable def builtPresentation (gen : FeedbackGenerator) : Stream := fun t =>
  (prefixes gen (t + 1)).presentation (Fin.last t)

noncomputable def builtQuery (gen : FeedbackGenerator) : ℕ → Option ℕ := fun t =>
  (prefixes gen (t + 1)).query (Fin.last t)

noncomputable def builtAnswer (gen : FeedbackGenerator) : ℕ → Option Bool := fun t =>
  (prefixes gen (t + 1)).answer (Fin.last t)

noncomputable def builtOutput (gen : FeedbackGenerator) : Stream := fun t =>
  (prefixes gen (t + 1)).output (Fin.last t)

noncomputable def builtTranscript (gen : FeedbackGenerator) : Transcript := {
  presentation := builtPresentation gen
  query := builtQuery gen
  answer := builtAnswer gen
  output := builtOutput gen
}

theorem prefix_presentation (gen : FeedbackGenerator) : ∀ {t : ℕ} (i : Fin t),
    (prefixes gen t).presentation i = builtPresentation gen i := by
  intro t
  induction t with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ t ih =>
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · simpa [prefixes, step] using ih j

theorem prefix_query (gen : FeedbackGenerator) : ∀ {t : ℕ} (i : Fin t),
    (prefixes gen t).query i = builtQuery gen i := by
  intro t
  induction t with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ t ih =>
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · simpa [prefixes, step] using ih j

theorem prefix_answer (gen : FeedbackGenerator) : ∀ {t : ℕ} (i : Fin t),
    (prefixes gen t).answer i = builtAnswer gen i := by
  intro t
  induction t with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ t ih =>
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · simpa [prefixes, step] using ih j

theorem prefix_output (gen : FeedbackGenerator) : ∀ {t : ℕ} (i : Fin t),
    (prefixes gen t).output i = builtOutput gen i := by
  intro t
  induction t with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ t ih =>
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · simpa [prefixes, step] using ih j

theorem unusedIndex_le_card {gen : FeedbackGenerator} {t : ℕ} (s : Prefix gen t) :
    unusedIndex s ≤ (assigned s).card := by
  classical
  by_contra hle
  have hlt : (assigned s).card < unusedIndex s := Nat.lt_of_not_ge hle
  have hsub : (Finset.range ((assigned s).card + 1)).image oddValue ⊆ assigned s := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    have hi' : i < unusedIndex s := by
      simp only [Finset.mem_range] at hi
      omega
    have hnot := Nat.find_min (exists_unused_odd s) hi'
    simpa using hnot
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ oddValue_injective, Finset.card_range] at hcard
  omega

theorem seen_card_le {gen : FeedbackGenerator} {t : ℕ} (s : Prefix gen t) :
    (seen s).card ≤ t := by
  simpa [seen] using (Finset.card_image_le :
    (Finset.univ.image s.presentation).card ≤ Finset.univ.card)

theorem rejected_card_step {gen : FeedbackGenerator} {t : ℕ} (s : Prefix gen t) :
    (step s).rejected.card ≤ s.rejected.card + 2 := by
  classical
  unfold step
  dsimp only
  apply le_trans (card_addUnlessSeen _ _ _)
  have hq := card_addQueryUnlessSeen
    (insert (nextPresentation s) (seen s)) s.rejected
    (gen.query t (append s.presentation (nextPresentation s)) s.answer)
  omega

theorem rejected_card_le (gen : FeedbackGenerator) : ∀ t,
    (prefixes gen t).rejected.card ≤ 2 * t := by
  intro t
  induction t with
  | zero => simp [prefixes]
  | succ t ih =>
      rw [prefixes]
      have hs := rejected_card_step (prefixes gen t)
      omega

theorem assigned_card_le (gen : FeedbackGenerator) (t : ℕ) :
    (assigned (prefixes gen t)).card ≤ 3 * t := by
  calc
    (assigned (prefixes gen t)).card ≤
        (prefixes gen t).rejected.card + (seen (prefixes gen t)).card :=
      Finset.card_union_le _ _
    _ ≤ 2 * t + t := Nat.add_le_add (rejected_card_le gen t) (seen_card_le _)
    _ = 3 * t := by omega

theorem builtPresentation_eq_next (gen : FeedbackGenerator) (t : ℕ) :
    builtPresentation gen t = nextPresentation (prefixes gen t) := by
  simp [builtPresentation, prefixes, step]

theorem builtPresentation_even (gen : FeedbackGenerator) (r : ℕ) :
    builtPresentation gen (2 * r) = 2 ^ r := by
  rw [builtPresentation_eq_next]
  simp [nextPresentation]

theorem builtPresentation_odd (gen : FeedbackGenerator) (r : ℕ) :
    builtPresentation gen (2 * r + 1) = oddValue (unusedIndex (prefixes gen (2 * r + 1))) := by
  rw [builtPresentation_eq_next]
  simp [nextPresentation]

theorem builtPresentation_odd_bound (gen : FeedbackGenerator) (r : ℕ) :
    builtPresentation gen (2 * r + 1) ≤ 12 * r + 9 := by
  rw [builtPresentation_odd, oddValue]
  have h := unusedIndex_le_card (prefixes gen (2 * r + 1))
  have hc := assigned_card_le gen (2 * r + 1)
  omega

theorem rejected_subset_addUnlessSeen (currentSeen s : Finset ℕ) (z : ℕ) :
    s ⊆ addUnlessSeen currentSeen s z := by
  classical
  unfold addUnlessSeen
  split <;> simp_all

theorem rejected_subset_addQueryUnlessSeen (currentSeen s : Finset ℕ) (q : Option ℕ) :
    s ⊆ addQueryUnlessSeen currentSeen s q := by
  cases q with
  | none => simp [addQueryUnlessSeen]
  | some z => simpa [addQueryUnlessSeen] using rejected_subset_addUnlessSeen currentSeen s z

theorem rejected_subset_step {gen : FeedbackGenerator} {t : ℕ} (s : Prefix gen t) :
    s.rejected ⊆ (step s).rejected := by
  classical
  unfold step
  dsimp only
  exact (rejected_subset_addQueryUnlessSeen _ _ _).trans
    (rejected_subset_addUnlessSeen _ _ _)

theorem rejected_mono (gen : FeedbackGenerator) {s t : ℕ} (hst : s ≤ t) :
    (prefixes gen s).rejected ⊆ (prefixes gen t).rejected := by
  induction t with
  | zero =>
      have hs : s = 0 := by omega
      subst s
      exact fun _ h => h
  | succ t ih =>
      by_cases h : s = t + 1
      · subst s
        exact fun _ h => h
      · have hst' : s ≤ t := by omega
        exact (ih hst').trans (by simpa [prefixes] using rejected_subset_step (prefixes gen t))

theorem presentation_mem_seen_of_lt (gen : FeedbackGenerator) {s t : ℕ} (hst : s < t) :
    builtPresentation gen s ∈ seen (prefixes gen t) := by
  classical
  rw [seen, Finset.mem_image]
  let i : Fin t := ⟨s, hst⟩
  exact ⟨i, Finset.mem_univ _, by simpa [i] using (prefix_presentation gen i)⟩

theorem odd_not_seen_before (gen : FeedbackGenerator) (r : ℕ) :
    builtPresentation gen (2 * r + 1) ∉ seen (prefixes gen (2 * r + 1)) := by
  rw [builtPresentation_odd]
  exact fun h => unusedIndex_spec (prefixes gen (2 * r + 1)) (Finset.mem_union_right _ h)

theorem odd_not_rejected_before (gen : FeedbackGenerator) (r : ℕ) :
    builtPresentation gen (2 * r + 1) ∉ (prefixes gen (2 * r + 1)).rejected := by
  rw [builtPresentation_odd]
  exact fun h => unusedIndex_spec (prefixes gen (2 * r + 1)) (Finset.mem_union_left _ h)

noncomputable def builtTarget (gen : FeedbackGenerator) : Language :=
  core ∪ Set.range (fun r => builtPresentation gen (2 * r + 1))

theorem odd_presentation_not_core (gen : FeedbackGenerator) (r : ℕ) :
    builtPresentation gen (2 * r + 1) ∉ core := by
  rw [builtPresentation_odd]
  exact oddValue_not_core _

theorem builtTarget_mem_class (gen : FeedbackGenerator) : builtTarget gen ∈ targetClass := by
  refine ⟨Set.range (fun r => builtPresentation gen (2 * r + 1)), ?_, rfl⟩
  rintro z ⟨r, rfl⟩
  exact odd_presentation_not_core gen r

theorem presentation_mem_target (gen : FeedbackGenerator) (t : ℕ) :
    builtPresentation gen t ∈ builtTarget gen := by
  rcases Nat.even_or_odd' t with ⟨r, rfl | rfl⟩
  · left
    exact ⟨r, (builtPresentation_even gen r).symm⟩
  · right
    exact ⟨r, rfl⟩

theorem seen_subset_target (gen : FeedbackGenerator) (t : ℕ) :
    ↑(seen (prefixes gen t)) ⊆ builtTarget gen := by
  intro z hz
  rw [seen, Finset.mem_coe, Finset.mem_image] at hz
  obtain ⟨i, _, rfl⟩ := hz
  rw [prefix_presentation gen i]
  exact presentation_mem_target gen i

theorem builtPresentation_injective (gen : FeedbackGenerator) :
    Function.Injective (builtPresentation gen) := by
  intro s t hst
  by_contra hne
  wlog hlt : s < t generalizing s t
  · have hts : t < s := by omega
    exact this hst.symm (Ne.symm hne) hts
  rcases Nat.even_or_odd' s with ⟨r, rfl | rfl⟩ <;>
    rcases Nat.even_or_odd' t with ⟨u, rfl | rfl⟩
  · rw [builtPresentation_even, builtPresentation_even] at hst
    have : r = u := Nat.pow_right_injective (by omega : 1 < (2 : ℕ)) hst
    omega
  · exact odd_presentation_not_core gen u (hst ▸ ⟨r, (builtPresentation_even gen r).symm⟩)
  · exact odd_presentation_not_core gen r (hst.symm ▸ ⟨u, (builtPresentation_even gen u).symm⟩)
  · exact odd_not_seen_before gen u (hst ▸ presentation_mem_seen_of_lt gen hlt)

theorem builtPresentation_complete (gen : FeedbackGenerator) :
    Complete (builtPresentation gen) (builtTarget gen) := by
  intro z hz
  rcases hz with ⟨r, hr⟩ | ⟨r, rfl⟩
  · exact ⟨2 * r, (builtPresentation_even gen r).trans hr⟩
  · exact ⟨2 * r + 1, rfl⟩

theorem observed_iff_seen (gen : FeedbackGenerator) (t z : ℕ) :
    z ∈ observedThrough (builtPresentation gen) t ↔
      z ∈ insert (builtPresentation gen t) (seen (prefixes gen t)) := by
  classical
  constructor
  · rintro ⟨s, hst, rfl⟩
    rcases hst.eq_or_lt with rfl | hlt
    · simp
    · exact Finset.mem_insert_of_mem (presentation_mem_seen_of_lt gen hlt)
  · intro hz
    rw [Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · exact ⟨t, le_rfl, rfl⟩
    · rw [seen, Finset.mem_image] at hz
      obtain ⟨i, _, hi⟩ := hz
      exact ⟨i, Nat.le_of_lt i.isLt, (prefix_presentation gen i).symm.trans hi⟩

theorem builtOutput_eq_early (gen : FeedbackGenerator) (t : ℕ) :
    builtOutput gen t = gen.output t
      (fun i => builtPresentation gen i) (fun i => builtAnswer gen i) := by
  rw [builtOutput, prefixes]
  simp only [step, append_last]
  congr 1
  · funext i
    exact prefix_presentation gen i
  · funext i
    exact prefix_answer gen i

theorem builtQuery_eq_early (gen : FeedbackGenerator) (t : ℕ) :
    builtQuery gen t = gen.query t
      (fun i => builtPresentation gen i) (fun i => builtAnswer gen i) := by
  rw [builtQuery, prefixes]
  simp only [step, append_last]
  congr 1
  · funext i
    exact prefix_presentation gen i
  · funext i
    exact prefix_answer gen i

theorem query_rejected_if_unknown (gen : FeedbackGenerator) (t z : ℕ)
    (hq : builtQuery gen t = some z) (hzcore : z ∉ core)
    (hzseen : z ∉ insert (builtPresentation gen t) (seen (prefixes gen t))) :
    z ∈ (prefixes gen (t + 1)).rejected := by
  classical
  rw [prefixes]
  unfold step
  dsimp only
  have hq' : gen.query t
      (append (prefixes gen t).presentation (nextPresentation (prefixes gen t)))
      (prefixes gen t).answer = some z := by
    calc
      _ = gen.query t (fun i => builtPresentation gen i) (fun i => builtAnswer gen i) := by
        congr 1
        · funext i
          simpa [prefixes, step] using prefix_presentation gen i
        · funext i
          exact prefix_answer gen i
      _ = some z := (builtQuery_eq_early gen t).symm.trans hq
  apply rejected_subset_addUnlessSeen
  unfold addQueryUnlessSeen
  rw [hq']
  unfold addUnlessSeen
  have hzseen' : z ∉ insert (nextPresentation (prefixes gen t)) (seen (prefixes gen t)) := by
    simpa [builtPresentation_eq_next] using hzseen
  simp [hzcore, hzseen']

theorem rejected_ne_future_odd_early (gen : FeedbackGenerator) {t r : ℕ}
    (htr : t ≤ 2 * r + 1) {z : ℕ} (hz : z ∈ (prefixes gen t).rejected) :
    z ≠ builtPresentation gen (2 * r + 1) := by
  intro heq
  have hz' := rejected_mono gen htr hz
  exact odd_not_rejected_before gen r (heq ▸ hz')

theorem query_local_iff_target (gen : FeedbackGenerator) (t z : ℕ)
    (hq : builtQuery gen t = some z) :
    (z ∈ core ∨ z ∈ insert (builtPresentation gen t) (seen (prefixes gen t))) ↔
      z ∈ builtTarget gen := by
  constructor
  · rintro (hz | hz)
    · exact Or.inl hz
    · rw [← observed_iff_seen] at hz
      obtain ⟨s, _, hs⟩ := hz
      exact hs ▸ presentation_mem_target gen s
  · intro hzK
    rcases hzK with hzcore | ⟨r, hr⟩
    · exact Or.inl hzcore
    · right
      by_contra hzseen
      have ht : t < 2 * r + 1 := by
        by_contra hnot
        apply hzseen
        rw [← observed_iff_seen]
        exact ⟨2 * r + 1, Nat.le_of_not_gt hnot, hr⟩
      have hznotcore : z ∉ core := by
        intro hzcore
        apply odd_presentation_not_core gen r
        change builtPresentation gen (2 * r + 1) = z at hr
        rw [hr]
        exact hzcore
      have hzrej := query_rejected_if_unknown gen t z hq hznotcore hzseen
      exact rejected_ne_future_odd_early gen (Nat.succ_le_iff.mp ht) hzrej hr.symm

theorem builtAnswer_eq (gen : FeedbackGenerator) (t : ℕ) :
    builtAnswer gen t = match builtQuery gen t with
      | none => none
      | some z => some (membershipAnswer (builtTarget gen) z) := by
  classical
  cases hq : builtQuery gen t with
  | none =>
      rw [builtAnswer, prefixes]
      simp only [step, append_last]
      have hq' : gen.query t
          (append (prefixes gen t).presentation (nextPresentation (prefixes gen t)))
          (prefixes gen t).answer = none := by
        calc
          _ = gen.query t (fun i => builtPresentation gen i) (fun i => builtAnswer gen i) := by
            congr 1
            · funext i
              simpa [prefixes, step] using prefix_presentation gen i
            · funext i
              exact prefix_answer gen i
          _ = none := (builtQuery_eq_early gen t).symm.trans hq
      simp [hq, hq']
  | some z =>
      rw [builtAnswer, prefixes]
      simp only [step, append_last]
      have hq' : gen.query t
          (append (prefixes gen t).presentation (nextPresentation (prefixes gen t)))
          (prefixes gen t).answer = some z := by
        calc
          _ = gen.query t (fun i => builtPresentation gen i) (fun i => builtAnswer gen i) := by
            congr 1
            · funext i
              simpa [prefixes, step] using prefix_presentation gen i
            · funext i
              exact prefix_answer gen i
          _ = some z := (builtQuery_eq_early gen t).symm.trans hq
      rw [hq']
      simp only [Option.map_some, hq]
      unfold membershipAnswer
      apply congrArg some
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      rw [← builtPresentation_eq_next]
      exact query_local_iff_target gen t z hq

theorem followsProtocol_built (gen : FeedbackGenerator) :
    FollowsProtocol gen (builtTarget gen) (builtTranscript gen) := by
  intro t
  exact ⟨builtQuery_eq_early gen t, builtAnswer_eq gen t, builtOutput_eq_early gen t⟩

theorem output_rejected_if_fresh_ordinary (gen : FeedbackGenerator) (t z : ℕ)
    (hy : builtOutput gen t = z) (hzcore : z ∉ core)
    (hzfresh : z ∉ observedThrough (builtPresentation gen) t) :
    z ∈ (prefixes gen (t + 1)).rejected := by
  classical
  rw [prefixes]
  unfold step
  dsimp only
  have hzseen : z ∉ insert (nextPresentation (prefixes gen t)) (seen (prefixes gen t)) := by
    rw [← builtPresentation_eq_next]
    simpa [observed_iff_seen] using hzfresh
  have hy' : gen.output t
      (append (prefixes gen t).presentation (nextPresentation (prefixes gen t)))
      (append (prefixes gen t).answer
        (Option.map (fun z => decide (z ∈ core ∨
          z ∈ insert (nextPresentation (prefixes gen t)) (seen (prefixes gen t))))
          (gen.query t
            (append (prefixes gen t).presentation (nextPresentation (prefixes gen t)))
            (prefixes gen t).answer))) = z := by
    calc
      _ = gen.output t (fun i => builtPresentation gen i) (fun i => builtAnswer gen i) := by
        congr 1
        · funext i
          simpa [prefixes, step] using prefix_presentation gen i
        · funext i
          simpa [prefixes, step] using prefix_answer gen i
      _ = z := (builtOutput_eq_early gen t).symm.trans hy
  rw [hy']
  unfold addUnlessSeen
  simp [hzcore, hzseen]

theorem rejected_ne_future_odd (gen : FeedbackGenerator) {t r : ℕ}
    (htr : t ≤ 2 * r + 1) {z : ℕ} (hz : z ∈ (prefixes gen t).rejected) :
    z ≠ builtPresentation gen (2 * r + 1) := by
  intro heq
  have hz' := rejected_mono gen htr hz
  exact odd_not_rejected_before gen r (heq ▸ hz')

theorem scored_subset_core (gen : FeedbackGenerator) :
    scored (builtTarget gen) (builtPresentation gen) (builtOutput gen) ⊆ core := by
  intro z hz
  rcases hz with ⟨hzK, t, hyt, hzfresh⟩
  by_contra hzcore
  rcases hzK with hzcore' | ⟨r, hr⟩
  · exact hzcore hzcore'
  · have ht : t < 2 * r + 1 := by
      by_contra hnot
      apply hzfresh
      exact ⟨2 * r + 1, Nat.le_of_not_gt hnot, hr⟩
    have hzrej := output_rejected_if_fresh_ordinary gen t z hyt hzcore hzfresh
    exact rejected_ne_future_odd gen (Nat.succ_le_iff.mp ht) hzrej hr.symm

theorem core_infinite : core.Infinite := by
  unfold core
  exact Set.infinite_range_of_injective
    (Nat.pow_right_injective (by omega : 1 < (2 : ℕ)))

theorem builtTarget_infinite (gen : FeedbackGenerator) : (builtTarget gen).Infinite :=
  core_infinite.mono Set.subset_union_left

noncomputable def orderedTarget (gen : FeedbackGenerator) : OrderedLanguage := {
  carrier := builtTarget gen
  enumeration := Nat.nth (fun z => z ∈ builtTarget gen)
  enumeration_injective := Nat.nth_injective (builtTarget_infinite gen)
  range_enumeration := Nat.range_nth_of_infinite (builtTarget_infinite gen)
}

theorem orderedTarget_strictMono (gen : FeedbackGenerator) :
    InheritsAmbientOrder (orderedTarget gen) :=
  Nat.nth_strictMono (builtTarget_infinite gen)

theorem odd_stream_injective (gen : FeedbackGenerator) :
    Function.Injective (fun r => builtPresentation gen (2 * r + 1)) := by
  intro r u h
  have := builtPresentation_injective gen h
  omega

theorem target_nth_bound (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).enumeration n ≤ 12 * n + 9 := by
  classical
  let f : ℕ → ℕ := fun r => builtPresentation gen (2 * r + 1)
  let B := 12 * n + 10
  have hsub : (Finset.range (n + 1)).image f ⊆
      (Finset.range B).filter (fun z => z ∈ builtTarget gen) := by
    intro z hz
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hz
    simp only [Finset.mem_range] at hr
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · dsimp [f, B]
      have hb := builtPresentation_odd_bound gen r
      omega
    · exact Or.inr ⟨r, rfl⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (odd_stream_injective gen), Finset.card_range,
    ← Nat.count_eq_card_filter_range] at hcard
  have hnth := Nat.nth_lt_of_lt_count hcard
  change Nat.nth (fun z => z ∈ builtTarget gen) n ≤ 12 * n + 9
  change Nat.nth (fun z => z ∈ builtTarget gen) n < B at hnth
  dsimp [B] at hnth
  omega

theorem builtQuery_eq (gen : FeedbackGenerator) (t : ℕ) :
    builtQuery gen t = gen.query t
      (fun i => builtPresentation gen i) (fun i => builtAnswer gen i) := by
  rw [builtQuery, prefixes]
  simp only [step, append_last]
  congr 1
  · funext i
    exact prefix_presentation gen i
  · funext i
    exact prefix_answer gen i

theorem builtOutput_eq (gen : FeedbackGenerator) (t : ℕ) :
    builtOutput gen t = gen.output t
      (fun i => builtPresentation gen i) (fun i => builtAnswer gen i) := by
  rw [builtOutput, prefixes]
  simp only [step, append_last]
  congr 1
  · funext i
    exact prefix_presentation gen i
  · funext i
    exact prefix_answer gen i

theorem core_prefixCount_bound (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).prefixCount core n ≤ Nat.log2 (12 * n + 10) + 1 := by
  classical
  let s := (Finset.range n).filter fun i => (orderedTarget gen).enumeration i ∈ core
  let e : ℕ → ℕ := fun i => Nat.log2 ((orderedTarget gen).enumeration i)
  have heinj : Set.InjOn e (s : Set ℕ) := by
    intro i hi j hj hij
    simp only [s, Finset.mem_coe, Finset.mem_filter] at hi hj
    rcases hi.2 with ⟨a, ha⟩
    rcases hj.2 with ⟨b, hb⟩
    have hab : a = b := by
      have hla : Nat.log2 ((orderedTarget gen).enumeration i) = a := by
        rw [← ha, Nat.log2_eq_log_two, Nat.log_pow (by omega : 1 < (2 : ℕ))]
      have hlb : Nat.log2 ((orderedTarget gen).enumeration j) = b := by
        rw [← hb, Nat.log2_eq_log_two, Nat.log_pow (by omega : 1 < (2 : ℕ))]
      calc
        a = e i := by simpa [e] using hla.symm
        _ = e j := hij
        _ = b := by simpa [e] using hlb
    apply (orderedTarget gen).enumeration_injective
    rw [← ha, ← hb, hab]
  have herange : s.image e ⊆ Finset.range (Nat.log2 (12 * n + 10) + 1) := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    simp only [s, Finset.mem_filter, Finset.mem_range] at hi
    have hbound := target_nth_bound gen i
    have hmono : Nat.log2 ((orderedTarget gen).enumeration i) ≤
        Nat.log2 (12 * n + 10) := by
      rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
      apply Nat.log_mono_right
      omega
    simp only [Finset.mem_range]
    dsimp only [e]
    exact Nat.lt_succ_of_le hmono
  change s.card ≤ _
  rw [← Finset.card_image_iff.mpr heinj]
  simpa using Finset.card_le_card herange

theorem core_prefixRatio_tendsto_zero (gen : FeedbackGenerator) :
    Tendsto ((orderedTarget gen).prefixRatio core) atTop (nhds 0) := by
  let error : ℕ → ℝ := fun n => ((6 + Nat.log2 n : ℕ) : ℝ) / (n : ℝ)
  have herror : Tendsto error atTop (nhds 0) := by
    simpa [error] using GenLimit.tendsto_countingError_div 6
  apply squeeze_zero (fun n => (orderedTarget gen).prefixRatio_nonneg core n) _ herror
  intro n
  by_cases hn : n = 0
  · simp [hn, error]
  · have hcount := core_prefixCount_bound gen n
    have hlinear : 12 * n + 10 ≤ 32 * n := by omega
    have hmul : ∀ m : ℕ, Nat.log 2 (n * 2 ^ m) = Nat.log 2 n + m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
          rw [pow_succ, ← mul_assoc,
            Nat.log_mul_base (by omega : 1 < (2 : ℕ))
              (mul_ne_zero hn (pow_ne_zero m (by omega : (2 : ℕ) ≠ 0))), ih]
          omega
    have hlog : Nat.log2 (12 * n + 10) ≤ Nat.log2 n + 5 := by
      rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
      calc
        Nat.log 2 (12 * n + 10) ≤ Nat.log 2 (32 * n) := Nat.log_mono_right hlinear
        _ = Nat.log 2 (n * 2 ^ 5) := by congr 1 <;> omega
        _ = Nat.log 2 n + 5 := hmul 5
    simp only [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, hn, if_false]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    exact_mod_cast hcount.trans (by omega : Nat.log2 (12 * n + 10) + 1 ≤ 6 + Nat.log2 n)

theorem core_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity core = 0 := by
  exact (core_prefixRatio_tendsto_zero gen).limsup_eq

noncomputable def encodedTarget (A : Set ℕ) : Language :=
  core ∪ oddValue '' A

theorem encodedTarget_mem_class (A : Set ℕ) : encodedTarget A ∈ targetClass := by
  refine ⟨oddValue '' A, ?_, rfl⟩
  rintro z ⟨k, _, rfl⟩
  exact oddValue_not_core k

theorem oddValue_mem_encodedTarget (A : Set ℕ) (k : ℕ) :
    oddValue k ∈ encodedTarget A ↔ k ∈ A := by
  constructor
  · rintro (hkcore | ⟨j, hj, heq⟩)
    · exact (oddValue_not_core k hkcore).elim
    · exact (oddValue_injective heq).symm ▸ hj
  · intro hk
    exact Or.inr ⟨k, hk, rfl⟩

theorem encodedTarget_injective : Function.Injective encodedTarget := by
  intro A B hAB
  ext k
  rw [← oddValue_mem_encodedTarget A k, ← oddValue_mem_encodedTarget B k, hAB]

theorem targetClass_not_countable : ¬ targetClass.Countable := by
  intro hclass
  have hrange : (Set.range encodedTarget).Countable := by
    apply hclass.mono
    rintro K ⟨A, rfl⟩
    exact encodedTarget_mem_class A
  have hpreimage := hrange.preimage encodedTarget_injective
  have huniv : (Set.univ : Set (Set ℕ)).Countable := by
    simpa using hpreimage
  letI : Countable (Set ℕ) := Set.countable_univ_iff.mp huniv
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ inferInstance

theorem uniformly_generatable : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t => 2 ^ t, Nat.pow_right_injective (by omega : 1 < (2 : ℕ)), 0, ?_⟩
  intro K hK t _
  rcases hK with ⟨A, hA, rfl⟩
  exact Or.inl ⟨t, rfl⟩

noncomputable def builtPresenter (gen : FeedbackGenerator) : CausalPresenter := {
  next := fun t _ _ _ _ => builtPresentation gen t
}

theorem presentedBy_built (gen : FeedbackGenerator) :
    PresentedBy (builtPresenter gen) (builtTranscript gen) := by
  intro t
  rfl

theorem scored_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity
      (scored (builtTarget gen) (builtPresentation gen) (builtOutput gen)) = 0 := by
  apply le_antisymm
  · calc
      (orderedTarget gen).upperDensity
          (scored (builtTarget gen) (builtPresentation gen) (builtOutput gen)) ≤
          (orderedTarget gen).upperDensity core :=
        (orderedTarget gen).upperDensity_mono (scored_subset_core gen)
      _ = 0 := core_upperDensity_zero gen
  · exact (orderedTarget gen).upperDensity_nonneg _

theorem faithful_built (gen : FeedbackGenerator) :
    FaithfulNegativeWitness gen (builtTarget gen) (builtPresenter gen)
      (builtTranscript gen) (orderedTarget gen) := by
  refine ⟨rfl, orderedTarget_strictMono gen, presentedBy_built gen,
    followsProtocol_built gen, ?_, builtPresentation_injective gen,
    builtPresentation_complete gen, scored_upperDensity_zero gen⟩
  exact presentation_mem_target gen

theorem negative_claim : NegativeClaim := by
  intro gen _
  exact ⟨builtTarget gen, builtTarget_mem_class gen, builtPresenter gen,
    builtTranscript gen, orderedTarget gen, faithful_built gen⟩

end Stage3Proof

theorem stage3_result : Stage3S2B.MainClaim := by
  exact ⟨Stage3Proof.targetClass_not_countable,
    Stage3Proof.uniformly_generatable, Stage3Proof.negative_claim⟩
