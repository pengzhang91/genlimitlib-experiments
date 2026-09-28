import Stage3Model
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import Mathlib.Data.Nat.Nth
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Set Filter
open GenLimit.KleinbergWei

namespace Stage3Proof

open Stage3S2B

lemma odd_large_ordinary (n : ℕ) : 2 * n + 3 ∈ ordinary := by
  rw [ordinary, Set.mem_compl_iff]
  rintro ⟨k, hk⟩
  have hodd : Odd (2 * n + 3) := by
    exact ⟨n + 1, by omega⟩
  have hk0 : k ≠ 0 := by
    intro h
    subst k
    simp at hk
  have heven : Even (2 ^ k) := Nat.even_pow.2 ⟨by simp, hk0⟩
  change 2 ^ k = 2 * n + 3 at hk
  rw [hk] at heven
  exact (Nat.not_even_iff_odd.mpr hodd) heven

lemma ordinary_infinite : ordinary.Infinite := by
  let f : ℕ → ℕ := fun n => 2 * n + 3
  have hf : Function.Injective f := by
    intro a b h
    dsimp [f] at h
    omega
  apply (Set.infinite_range_of_injective hf).mono
  rintro _ ⟨n, rfl⟩
  exact odd_large_ordinary n

noncomputable def pickOrdinary (I R : Finset ℕ) : ℕ := by
  classical
  exact Nat.find (ordinary_infinite.exists_not_mem_finset (I ∪ R))

lemma pickOrdinary_spec (I R : Finset ℕ) :
    pickOrdinary I R ∈ ordinary ∧ pickOrdinary I R ∉ I ∪ R := by
  classical
  exact Nat.find_spec (ordinary_infinite.exists_not_mem_finset (I ∪ R))

structure BuildState (t : ℕ) where
  presentation : Fin t → ℕ
  query : Fin t → Option ℕ
  answer : Fin t → Option Bool
  output : Fin t → ℕ
  admitted : Finset ℕ
  rejected : Finset ℕ

noncomputable def initialState : BuildState 0 where
  presentation := Fin.elim0
  query := Fin.elim0
  answer := Fin.elim0
  output := Fin.elim0
  admitted := ∅
  rejected := ∅

noncomputable def step (gen : FeedbackGenerator) (t : ℕ)
    (s : BuildState t) : BuildState (t + 1) := by
  classical
  let x : ℕ := if Even t then 2 ^ (t / 2) else pickOrdinary s.admitted s.rejected
  let admitted' : Finset ℕ := if Even t then s.admitted else insert x s.admitted
  let xs : Fin (t + 1) → ℕ := Fin.snoc s.presentation x
  let q : Option ℕ := gen.query t xs s.answer
  let b : Option Bool := match q with
    | none => none
    | some z => some (decide (z ∈ core ∨ z ∈ admitted'))
  let rejectedQ : Finset ℕ := match q with
    | none => s.rejected
    | some z => if z ∈ core ∨ z ∈ admitted' then s.rejected else insert z s.rejected
  let bs : Fin (t + 1) → Option Bool := Fin.snoc s.answer b
  let y : ℕ := gen.output t xs bs
  let rejected' : Finset ℕ :=
    if y ∈ core ∨ y ∈ admitted' then rejectedQ else insert y rejectedQ
  exact {
    presentation := xs
    query := Fin.snoc s.query q
    answer := bs
    output := Fin.snoc s.output y
    admitted := admitted'
    rejected := rejected'
  }

noncomputable def build (gen : FeedbackGenerator) : (t : ℕ) → BuildState t
  | 0 => initialState
  | t + 1 => step gen t (build gen t)


lemma admitted_subset_ordinary (gen : FeedbackGenerator) (t : ℕ) :
    ∀ z ∈ (build gen t).admitted, z ∈ ordinary := by
  induction t with
  | zero => simp [build, initialState]
  | succ t ih =>
      classical
      intro z hz
      simp only [build] at hz
      simp only [step] at hz
      split at hz
      · exact ih z hz
      · simp only [Finset.mem_insert] at hz
        rcases hz with rfl | hz
        · exact (pickOrdinary_spec _ _).1
        · exact ih z hz

lemma rejected_subset_ordinary (gen : FeedbackGenerator) (t : ℕ) :
    ∀ z ∈ (build gen t).rejected, z ∈ ordinary := by
  induction t with
  | zero => simp [build, initialState]
  | succ t ih =>
      classical
      intro z hz
      simp only [build] at hz
      simp only [step] at hz
      repeat' first | split at hz | simp only [Finset.mem_insert] at hz
      all_goals aesop

lemma admitted_mono (gen : FeedbackGenerator) (t : ℕ) :
    (build gen t).admitted ⊆ (build gen (t + 1)).admitted := by
  classical
  simp only [build, step]
  split <;> simp

lemma rejected_mono (gen : FeedbackGenerator) (t : ℕ) :
    (build gen t).rejected ⊆ (build gen (t + 1)).rejected := by
  classical
  simp only [build, step]
  repeat' first | split | simp
  all_goals intro z hz; simp [hz]

lemma admitted_rejected_disjoint (gen : FeedbackGenerator) (t : ℕ) :
    Disjoint (build gen t).admitted (build gen t).rejected := by
  induction t with
  | zero => simp [build, initialState]
  | succ t ih =>
      classical
      simp only [build, step]
      have hp := pickOrdinary_spec (build gen t).admitted (build gen t).rejected
      repeat' first | split | simp only [Finset.disjoint_insert_left,
          Finset.disjoint_insert_right, Finset.mem_union, not_or]
      all_goals aesop

noncomputable def builtTranscript (gen : FeedbackGenerator) : Transcript where
  presentation t := (build gen (t + 1)).presentation (Fin.last t)
  query t := (build gen (t + 1)).query (Fin.last t)
  answer t := (build gen (t + 1)).answer (Fin.last t)
  output t := (build gen (t + 1)).output (Fin.last t)

lemma build_presentation_eq (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (build gen t).presentation i = (builtTranscript gen).presentation i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [builtTranscript, build, step]
      · simpa [build, step] using ih j

lemma build_query_eq (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (build gen t).query i = (builtTranscript gen).query i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [builtTranscript, build, step]
      · simpa [build, step] using ih j

lemma build_answer_eq (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (build gen t).answer i = (builtTranscript gen).answer i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [builtTranscript, build, step]
      · simpa [build, step] using ih j

lemma build_output_eq (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (build gen t).output i = (builtTranscript gen).output i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [builtTranscript, build, step]
      · simpa [build, step] using ih j

lemma admitted_mono_le (gen : FeedbackGenerator) {s t : ℕ} (h : s ≤ t) :
    (build gen s).admitted ⊆ (build gen t).admitted := by
  induction h with
  | refl => exact fun _ hz => hz
  | @step t h ih => exact Finset.Subset.trans ih (admitted_mono gen t)

lemma rejected_mono_le (gen : FeedbackGenerator) {s t : ℕ} (h : s ≤ t) :
    (build gen s).rejected ⊆ (build gen t).rejected := by
  induction h with
  | refl => exact fun _ hz => hz
  | @step t h ih => exact Finset.Subset.trans ih (rejected_mono gen t)

lemma presentation_even (gen : FeedbackGenerator) (t : ℕ) (ht : Even t) :
    (builtTranscript gen).presentation t = 2 ^ (t / 2) := by
  simp [builtTranscript, build, step, ht]

lemma presentation_odd (gen : FeedbackGenerator) (t : ℕ) (ht : ¬ Even t) :
    (builtTranscript gen).presentation t =
      pickOrdinary (build gen t).admitted (build gen t).rejected := by
  simp [builtTranscript, build, step, ht]

lemma odd_presentation_admitted (gen : FeedbackGenerator) (t : ℕ) (ht : ¬ Even t) :
    (builtTranscript gen).presentation t ∈ (build gen (t + 1)).admitted := by
  simp [build, step, presentation_odd gen t ht, ht]

lemma admitted_has_presentation (gen : FeedbackGenerator) (t : ℕ) {z : ℕ}
    (hz : z ∈ (build gen t).admitted) :
    ∃ s < t, ¬ Even s ∧ (builtTranscript gen).presentation s = z := by
  induction t with
  | zero => simp [build, initialState] at hz
  | succ t ih =>
      classical
      by_cases ht : Even t
      · simp [build, step, ht] at hz
        obtain ⟨s, hs, hso, hsz⟩ := ih hz
        exact ⟨s, hs.trans (Nat.lt_succ_self t), hso, hsz⟩
      · simp [build, step, ht] at hz
        rcases hz with rfl | hz
        · exact ⟨t, Nat.lt_succ_self t, ht, presentation_odd gen t ht⟩
        · obtain ⟨s, hs, hso, hsz⟩ := ih hz
          exact ⟨s, hs.trans (Nat.lt_succ_self t), hso, hsz⟩

lemma rejected_not_admitted_later (gen : FeedbackGenerator) {s t z : ℕ}
    (hst : s ≤ t) (hz : z ∈ (build gen s).rejected) :
    z ∉ (build gen t).admitted := by
  intro hza
  have hzr := rejected_mono_le gen hst hz
  exact Finset.disjoint_left.1 (admitted_rejected_disjoint gen t) hza hzr

noncomputable def builtTarget (gen : FeedbackGenerator) : Language :=
  core ∪ {z | ∃ t, z ∈ (build gen t).admitted}

noncomputable def builtPresenter (gen : FeedbackGenerator) : CausalPresenter where
  next t _ _ _ _ := (builtTranscript gen).presentation t

noncomputable def ambientOrder (K : Language) (hK : K.Infinite) :
    GenLimit.KleinbergWei.OrderedLanguage where
  carrier := K
  enumeration := Nat.nth (fun n => n ∈ K)
  enumeration_injective := (Nat.nth_strictMono hK).injective
  range_enumeration := Nat.range_nth_of_infinite hK



lemma builtTarget_mem_class (gen : FeedbackGenerator) :
    builtTarget gen ∈ targetClass := by
  refine ⟨{z | ∃ t, z ∈ (build gen t).admitted}, ?_, rfl⟩
  rintro z ⟨t, hz⟩
  exact admitted_subset_ordinary gen t z hz

lemma builtTarget_infinite (gen : FeedbackGenerator) : (builtTarget gen).Infinite := by
  have hc : core.Infinite := by
    apply (Set.infinite_range_of_injective (Nat.pow_right_injective (by omega : 2 ≤ 2)))
  exact hc.mono (Set.subset_union_left)

lemma built_clean (gen : FeedbackGenerator) :
    Clean (builtTranscript gen).presentation (builtTarget gen) := by
  intro t
  by_cases ht : Even t
  · left
    rw [presentation_even gen t ht]
    exact ⟨t / 2, rfl⟩
  · right
    exact ⟨t + 1, odd_presentation_admitted gen t ht⟩

lemma built_complete (gen : FeedbackGenerator) :
    Complete (builtTranscript gen).presentation (builtTarget gen) := by
  intro z hz
  rcases hz with hz | ⟨t, hz⟩
  · rcases hz with ⟨k, rfl⟩
    refine ⟨2 * k, ?_⟩
    have he : Even (2 * k) := ⟨k, by omega⟩
    simpa using presentation_even gen (2 * k) he
  · obtain ⟨s, hs, hso, hsz⟩ := admitted_has_presentation gen t hz
    exact ⟨s, hsz⟩

lemma built_distinct_of_lt (gen : FeedbackGenerator) {s t : ℕ} (hlt : s < t) :
    (builtTranscript gen).presentation s ≠ (builtTranscript gen).presentation t := by
  by_cases hs : Even s
  · by_cases ht : Even t
    · rcases hs with ⟨a, rfl⟩
      rcases ht with ⟨b, rfl⟩
      have hpa := presentation_even gen (a + a) ⟨a, rfl⟩
      have hpb := presentation_even gen (b + b) ⟨b, rfl⟩
      simp at hpa hpb
      rw [hpa, hpb]
      intro hp
      have hab := Nat.pow_right_injective (by omega : 2 ≤ 2) hp
      omega
    · have hcore : (builtTranscript gen).presentation s ∈ core := by
        rw [presentation_even gen s hs]
        exact ⟨s / 2, rfl⟩
      have hord : (builtTranscript gen).presentation t ∈ ordinary := by
        rw [presentation_odd gen t ht]
        exact (pickOrdinary_spec _ _).1
      intro h
      exact hord (h ▸ hcore)
  · by_cases ht : Even t
    · have hord : (builtTranscript gen).presentation s ∈ ordinary := by
        rw [presentation_odd gen s hs]
        exact (pickOrdinary_spec _ _).1
      have hcore : (builtTranscript gen).presentation t ∈ core := by
        rw [presentation_even gen t ht]
        exact ⟨t / 2, rfl⟩
      intro h
      exact hord (h.symm ▸ hcore)
    · have hsa := odd_presentation_admitted gen s hs
      have hle : s + 1 ≤ t := by omega
      have hsat := admitted_mono_le gen hle hsa
      have hnot := (pickOrdinary_spec (build gen t).admitted
        (build gen t).rejected).2
      rw [presentation_odd gen t ht]
      intro h
      apply hnot
      exact Finset.mem_union.mpr (Or.inl (h ▸ hsat))

lemma built_injective (gen : FeedbackGenerator) :
    Function.Injective (builtTranscript gen).presentation := by
  intro s t h
  apply le_antisymm
  · exact not_lt.mp (fun hts => built_distinct_of_lt gen hts h.symm)
  · exact not_lt.mp (fun hst => built_distinct_of_lt gen hst h)

lemma built_presentedBy (gen : FeedbackGenerator) :
    PresentedBy (builtPresenter gen) (builtTranscript gen) := by
  intro t
  rfl


lemma built_query_state (gen : FeedbackGenerator) (t : ℕ) :
    (builtTranscript gen).query t =
      gen.query t (build gen (t + 1)).presentation (build gen t).answer := by
  simp [builtTranscript, build, step]

lemma built_answer_state (gen : FeedbackGenerator) (t : ℕ) :
    (builtTranscript gen).answer t =
      match (builtTranscript gen).query t with
      | none => none
      | some z => some (membershipAnswer
          (core ∪ {z | z ∈ (build gen (t + 1)).admitted}) z) := by
  classical
  rw [built_query_state]
  simp [builtTranscript, build, step, membershipAnswer]

lemma built_output_state (gen : FeedbackGenerator) (t : ℕ) :
    (builtTranscript gen).output t =
      gen.output t (build gen (t + 1)).presentation (build gen (t + 1)).answer := by
  simp [builtTranscript, build, step]

lemma built_query_eq (gen : FeedbackGenerator) (t : ℕ) :
    (builtTranscript gen).query t = gen.query t
      (fun i => (builtTranscript gen).presentation i)
      (fun i => (builtTranscript gen).answer i) := by
  rw [built_query_state]
  congr 1
  · funext i
    exact build_presentation_eq gen (t + 1) i
  · funext i
    exact build_answer_eq gen t i

lemma query_rejected_if_negative (gen : FeedbackGenerator) (t z : ℕ)
    (hq : (builtTranscript gen).query t = some z)
    (hc : z ∉ core) (ha : z ∉ (build gen (t + 1)).admitted) :
    z ∈ (build gen (t + 1)).rejected := by
  classical
  by_cases ht : Even t
  · simp [builtTranscript, build, step, ht] at hq ha ⊢
    rw [hq]
    simp [hc, ha]
    split <;> simp
  · simp [builtTranscript, build, step, ht] at hq ha ⊢
    rw [hq]
    simp [hc, ha]
    split <;> simp

lemma queried_membership_iff (gen : FeedbackGenerator) (t z : ℕ)
    (hq : (builtTranscript gen).query t = some z) :
    z ∈ builtTarget gen ↔ z ∈ core ∨ z ∈ (build gen (t + 1)).admitted := by
  constructor
  · rintro (hc | ⟨s, hs⟩)
    · exact Or.inl hc
    · right
      by_cases hst : s ≤ t + 1
      · exact admitted_mono_le gen hst hs
      · have hle : t + 1 ≤ s := by omega
        by_contra ha
        have hc : z ∉ core := by
          intro hzc
          exact (admitted_subset_ordinary gen s z hs) hzc
        have hzr := query_rejected_if_negative gen t z hq hc ha
        exact (rejected_not_admitted_later gen hle hzr) hs
  · rintro (hc | ha)
    · exact Or.inl hc
    · exact Or.inr ⟨t + 1, ha⟩

lemma built_answer_eq (gen : FeedbackGenerator) (t : ℕ) :
    (builtTranscript gen).answer t =
      match (builtTranscript gen).query t with
      | none => none
      | some z => some (membershipAnswer (builtTarget gen) z) := by
  classical
  rw [built_answer_state]
  cases hq : (builtTranscript gen).query t with
  | none => simp
  | some z =>
      simp only
      apply congrArg some
      unfold membershipAnswer
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, Set.mem_union, Set.mem_setOf_eq]
      exact (queried_membership_iff gen t z hq).symm

lemma built_output_eq_generator (gen : FeedbackGenerator) (t : ℕ) :
    (builtTranscript gen).output t = gen.output t
      (fun i => (builtTranscript gen).presentation i)
      (fun i => (builtTranscript gen).answer i) := by
  rw [built_output_state]
  congr 1
  · funext i
    exact build_presentation_eq gen (t + 1) i
  · funext i
    exact build_answer_eq gen (t + 1) i

lemma built_followsProtocol (gen : FeedbackGenerator) :
    FollowsProtocol gen (builtTarget gen) (builtTranscript gen) := by
  intro t
  exact ⟨built_query_eq gen t, built_answer_eq gen t, built_output_eq_generator gen t⟩

lemma output_rejected_if_ordinary_unadmitted (gen : FeedbackGenerator) (t : ℕ)
    (hc : (builtTranscript gen).output t ∉ core)
    (ha : (builtTranscript gen).output t ∉ (build gen (t + 1)).admitted) :
    (builtTranscript gen).output t ∈ (build gen (t + 1)).rejected := by
  classical
  by_cases ht : Even t
  · simp [builtTranscript, build, step, ht] at hc ha ⊢
    split <;> simp_all
  · simp [builtTranscript, build, step, ht] at hc ha ⊢
    split <;> simp_all

lemma scored_subset_core (gen : FeedbackGenerator) :
    scored (builtTarget gen) (builtTranscript gen).presentation
      (builtTranscript gen).output ⊆ core := by
  intro z hz
  rcases hz with ⟨hzK, t, hyt, hzobs⟩
  by_contra hc
  have haK : ∃ s, z ∈ (build gen s).admitted := by
    rcases hzK with hzc | ha
    · exact False.elim (hc hzc)
    · exact ha
  have hnotCurrent : z ∉ (build gen (t + 1)).admitted := by
    intro ha
    obtain ⟨s, hs, _hso, hpres⟩ := admitted_has_presentation gen (t + 1) ha
    apply hzobs
    exact ⟨s, by omega, hpres⟩
  have hzr : z ∈ (build gen (t + 1)).rejected := by
    rw [← hyt]
    exact output_rejected_if_ordinary_unadmitted gen t (by simpa [hyt] using hc)
      (by simpa [hyt] using hnotCurrent)
  obtain ⟨s, hs⟩ := haK
  by_cases hle : s ≤ t + 1
  · have hsa := admitted_mono_le gen hle hs
    exact Finset.disjoint_left.1 (admitted_rejected_disjoint gen (t + 1)) hsa hzr
  · have hle' : t + 1 ≤ s := by omega
    exact (rejected_not_admitted_later gen hle' hzr) hs


lemma admitted_card_le (gen : FeedbackGenerator) (t : ℕ) :
    (build gen t).admitted.card ≤ t := by
  induction t with
  | zero => simp [build, initialState]
  | succ t ih =>
      classical
      simp only [build, step]
      split
      · exact ih.trans (Nat.le_succ t)
      · exact (Finset.card_insert_le _ _).trans (by omega)

lemma rejected_card_le (gen : FeedbackGenerator) (t : ℕ) :
    (build gen t).rejected.card ≤ 2 * t := by
  induction t with
  | zero => simp [build, initialState]
  | succ t ih =>
      classical
      simp only [build, step]
      repeat' split
      all_goals grind [Finset.card_insert_le]

lemma assigned_card_le (gen : FeedbackGenerator) (t : ℕ) :
    ((build gen t).admitted ∪ (build gen t).rejected).card ≤ 3 * t := by
  calc
    _ ≤ (build gen t).admitted.card + (build gen t).rejected.card :=
      Finset.card_union_le _ _
    _ ≤ t + 2 * t := Nat.add_le_add (admitted_card_le gen t) (rejected_card_le gen t)
    _ = 3 * t := by omega

lemma exists_odd_not_mem (F : Finset ℕ) :
    ∃ j ≤ F.card, 2 * j + 3 ∉ F := by
  classical
  let f : ℕ → ℕ := fun j => 2 * j + 3
  have hf : Function.Injective f := by
    intro a b h
    dsimp [f] at h
    omega
  let candidates := (Finset.range (F.card + 1)).image f
  have hcard : candidates.card = F.card + 1 := by
    rw [show candidates.card = (Finset.range (F.card + 1)).card by
      exact Finset.card_image_of_injective _ hf]
    simp
  have hlt : F.card < candidates.card := by omega
  obtain ⟨x, hxc, hxF⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  rcases Finset.mem_image.mp hxc with ⟨j, hj, rfl⟩
  refine ⟨j, ?_, hxF⟩
  simp [candidates] at hj
  omega

lemma pickOrdinary_le (I R : Finset ℕ) :
    pickOrdinary I R ≤ 2 * (I ∪ R).card + 3 := by
  classical
  obtain ⟨j, hj, hmem⟩ := exists_odd_not_mem (I ∪ R)
  calc
    pickOrdinary I R ≤ 2 * j + 3 := by
      unfold pickOrdinary
      apply Nat.find_min'
      exact ⟨odd_large_ordinary j, hmem⟩
    _ ≤ 2 * (I ∪ R).card + 3 := by omega

lemma pickOrdinary_build_le (gen : FeedbackGenerator) (t : ℕ) :
    pickOrdinary (build gen t).admitted (build gen t).rejected ≤ 6 * t + 3 := by
  calc
    _ ≤ 2 * ((build gen t).admitted ∪ (build gen t).rejected).card + 3 :=
      pickOrdinary_le _ _
    _ ≤ 6 * t + 3 := by
      have h := assigned_card_le gen t
      omega

lemma odd_presentation_le (gen : FeedbackGenerator) (r : ℕ) :
    (builtTranscript gen).presentation (2 * r + 1) ≤ 12 * r + 9 := by
  have hodd : ¬ Even (2 * r + 1) :=
    Nat.not_even_iff_odd.mpr ⟨r, by omega⟩
  rw [presentation_odd gen (2 * r + 1) hodd]
  have h := pickOrdinary_build_le gen (2 * r + 1)
  omega


lemma ambient_nth_le (gen : FeedbackGenerator) (n : ℕ) :
    Nat.nth (fun z => z ∈ builtTarget gen) n ≤ 12 * n + 9 := by
  classical
  let vals := (Finset.range (n + 1)).image
    (fun r => (builtTranscript gen).presentation (2 * r + 1))
  have hlinj : Function.Injective (fun r : ℕ => 2 * r + 1) := by
    intro a b h
    dsimp at h
    omega
  have hinj : Function.Injective
      (fun r => (builtTranscript gen).presentation (2 * r + 1)) :=
    (built_injective gen).comp hlinj
  have hcard : vals.card = n + 1 := by
    rw [show vals.card = (Finset.range (n + 1)).card by
      exact Finset.card_image_of_injective _ hinj]
    simp
  have hsubset : vals ⊆ (Finset.range (12 * n + 10)).filter
      (fun z => z ∈ builtTarget gen) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨r, hr, rfl⟩
    have hrn : r ≤ n := by simp at hr; omega
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · have h := odd_presentation_le gen r
      omega
    · exact built_clean gen (2 * r + 1)
  have hcount : n + 1 ≤ Nat.count (fun z => z ∈ builtTarget gen) (12 * n + 10) := by
    rw [Nat.count_eq_card_filter_range]
    rw [← hcard]
    exact Finset.card_le_card hsubset
  have hnth := Nat.nth_lt_of_lt_count (p := fun z => z ∈ builtTarget gen)
    (n := 12 * n + 10) (k := n) (by omega)
  omega

noncomputable def inCore (z : ℕ) : Bool := membershipAnswer core z

lemma inCore_eq_true (z : ℕ) : inCore z = true ↔ z ∈ core := by
  classical
  simp [inCore, membershipAnswer]

lemma core_count_le_log (M : ℕ) :
    Nat.count (fun z => inCore z = true) M ≤ Nat.log 2 M + 1 := by
  classical
  rw [Nat.count_eq_card_filter_range]
  let powers := (Finset.range (Nat.log 2 M + 1)).image (fun k => 2 ^ k)
  have hsubset : (Finset.range M).filter (fun z => inCore z = true) ⊆ powers := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_range] at hz
    have hzcore := (inCore_eq_true z).mp hz.2
    rcases hzcore with ⟨k, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨k, ?_, rfl⟩
    simp only [Finset.mem_range]
    have hk : k ≤ Nat.log 2 M :=
      Nat.le_log_of_pow_le (by omega) (Nat.le_of_lt hz.1)
    omega
  calc
    _ ≤ powers.card := Finset.card_le_card hsubset
    _ ≤ (Finset.range (Nat.log 2 M + 1)).card := Finset.card_image_le
    _ = Nat.log 2 M + 1 := by simp

lemma prefixCount_core_le (gen : FeedbackGenerator) (n : ℕ) :
    (ambientOrder (builtTarget gen) (builtTarget_infinite gen)).prefixCount core n ≤
      Nat.log 2 (12 * n + 10) + 1 := by
  classical
  unfold GenLimit.KleinbergWei.OrderedLanguage.prefixCount
  let values := ((Finset.range n).filter fun i =>
    (ambientOrder (builtTarget gen) (builtTarget_infinite gen)).enumeration i ∈ core).image
      (ambientOrder (builtTarget gen) (builtTarget_infinite gen)).enumeration
  have hcard : values.card =
      ((Finset.range n).filter fun i =>
        (ambientOrder (builtTarget gen) (builtTarget_infinite gen)).enumeration i ∈ core).card := by
    exact Finset.card_image_of_injective _
      (ambientOrder (builtTarget gen) (builtTarget_infinite gen)).enumeration_injective
  have hsubset : values ⊆ (Finset.range (12 * n + 10)).filter (fun z => z ∈ core) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    refine ⟨?_, hi.2⟩
    have hin : i ≤ n := by omega
    change Nat.nth (fun z => z ∈ builtTarget gen) i < 12 * n + 10
    have h := ambient_nth_le gen i
    omega
  calc
    _ = values.card := hcard.symm
    _ ≤ ((Finset.range (12 * n + 10)).filter (fun z => z ∈ core)).card :=
      Finset.card_le_card hsubset
    _ = ((Finset.range (12 * n + 10)).filter (fun z => inCore z = true)).card := by
      congr 1
      ext z
      simp only [Finset.mem_filter, Finset.mem_range]
      exact and_congr_right (fun _ => (inCore_eq_true z).symm)
    _ = Nat.count (fun z => inCore z = true) (12 * n + 10) := by
      rw [Nat.count_eq_card_filter_range]
    _ ≤ Nat.log 2 (12 * n + 10) + 1 := core_count_le_log _


lemma tendsto_log_error :
    Tendsto (fun n : ℕ =>
      (Real.logb 2 (12 * (n : ℝ) + 10) + 1) / (n : ℝ)) atTop (nhds 0) := by
  have hargNat : Tendsto (fun n : ℕ => 12 * n + 10) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  have hargReal : Tendsto (fun n : ℕ => ((12 * n + 10 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_iff.mpr hargNat
  have hsmall : Tendsto (fun x : ℝ => Real.logb 2 x / x) atTop (nhds 0) := by
    simpa only [id_eq] using
      (Real.isLittleO_logb_id_atTop (b := (2 : ℝ))).tendsto_div_nhds_zero
  have hA : Tendsto (fun n : ℕ =>
      Real.logb 2 ((12 * n + 10 : ℕ) : ℝ) / ((12 * n + 10 : ℕ) : ℝ))
      atTop (nhds 0) := hsmall.comp hargReal
  have hten : Tendsto (fun n : ℕ => (10 : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hB : Tendsto (fun n : ℕ =>
      ((12 * n + 10 : ℕ) : ℝ) / (n : ℝ)) atTop (nhds 12) := by
    have heq :
        (fun n : ℕ => (12 : ℝ) + 10 / (n : ℝ)) =ᶠ[atTop]
          (fun n : ℕ => ((12 * n + 10 : ℕ) : ℝ) / (n : ℝ)) := by
      filter_upwards [eventually_ne_atTop 0] with n hn
      norm_num [Nat.cast_add, Nat.cast_mul, hn]
      field_simp
    have hconst : Tendsto (fun _ : ℕ => (12 : ℝ)) atTop (nhds 12) :=
      tendsto_const_nhds
    simpa using (hconst.add hten).congr' heq
  have hlog : Tendsto (fun n : ℕ =>
      Real.logb 2 ((12 * n + 10 : ℕ) : ℝ) / (n : ℝ)) atTop (nhds 0) := by
    have heq :
        (fun n : ℕ =>
          (Real.logb 2 ((12 * n + 10 : ℕ) : ℝ) / ((12 * n + 10 : ℕ) : ℝ)) *
            (((12 * n + 10 : ℕ) : ℝ) / (n : ℝ))) =ᶠ[atTop]
          (fun n : ℕ => Real.logb 2 ((12 * n + 10 : ℕ) : ℝ) / (n : ℝ)) := by
      filter_upwards [eventually_ne_atTop 0] with n hn
      have hy : ((12 * n + 10 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
    simpa using (hA.mul hB).congr' heq
  have hone : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  simpa only [add_div, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, zero_add] using
    hlog.add hone

lemma prefixRatio_core_tendsto_zero (gen : FeedbackGenerator) :
    Tendsto
      ((ambientOrder (builtTarget gen) (builtTarget_infinite gen)).prefixRatio core)
      atTop (nhds 0) := by
  let K := ambientOrder (builtTarget gen) (builtTarget_infinite gen)
  let err : ℕ → ℝ := fun n =>
    (Real.logb 2 (12 * (n : ℝ) + 10) + 1) / (n : ℝ)
  have herr : Tendsto err atTop (nhds 0) := tendsto_log_error
  have hbound : ∀ n, K.prefixRatio core n ≤ err n := by
    intro n
    by_cases hn : n = 0
    · simp [hn, K, err]
    · have hcount := prefixCount_core_le gen n
      have hcountR : (K.prefixCount core n : ℝ) ≤
          (Nat.log 2 (12 * n + 10) + 1 : ℕ) := by
        exact_mod_cast hcount
      have hnatlog : (Nat.log 2 (12 * n + 10) : ℝ) ≤
          Real.logb 2 ((12 * n + 10 : ℕ) : ℝ) :=
        Real.natLog_le_logb _ _
      have hnum : (K.prefixCount core n : ℝ) ≤
          Real.logb 2 ((12 * n + 10 : ℕ) : ℝ) + 1 := by
        calc
          _ ≤ (Nat.log 2 (12 * n + 10) : ℝ) + 1 := by
            simpa only [Nat.cast_add, Nat.cast_one] using hcountR
          _ ≤ _ := by linarith
      simp only [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, hn, if_false]
      exact div_le_div_of_nonneg_right (by
        simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hnum)
        (Nat.cast_nonneg n)
  apply squeeze_zero
    (fun n => K.prefixRatio_nonneg core n) hbound herr

lemma ambient_core_upperDensity_zero (gen : FeedbackGenerator) :
    (ambientOrder (builtTarget gen) (builtTarget_infinite gen)).upperDensity core = 0 := by
  unfold GenLimit.KleinbergWei.OrderedLanguage.upperDensity
  exact (prefixRatio_core_tendsto_zero gen).limsup_eq

lemma scored_upperDensity_zero (gen : FeedbackGenerator) :
    (ambientOrder (builtTarget gen) (builtTarget_infinite gen)).upperDensity
      (scored (builtTarget gen) (builtTranscript gen).presentation
        (builtTranscript gen).output) = 0 := by
  apply le_antisymm
  · calc
      _ ≤ (ambientOrder (builtTarget gen) (builtTarget_infinite gen)).upperDensity core :=
        GenLimit.KleinbergWei.OrderedLanguage.upperDensity_mono _ (scored_subset_core gen)
      _ = 0 := ambient_core_upperDensity_zero gen
  · exact GenLimit.KleinbergWei.OrderedLanguage.upperDensity_nonneg _ _

lemma targetClass_not_countable : ¬ targetClass.Countable := by
  intro hc
  let encode : Set ordinary → targetClass := fun A =>
    ⟨core ∪ ((fun a : ordinary => (a : ℕ)) '' A), by
      refine ⟨(fun a : ordinary => (a : ℕ)) '' A, ?_, rfl⟩
      intro z hz
      rcases hz with ⟨a, ha, rfl⟩
      exact a.property⟩
  have hinj : Function.Injective encode := by
    intro A B h
    apply Set.ext
    intro a
    have hu : (encode A : Language) = (encode B : Language) := congrArg Subtype.val h
    have hm := Set.ext_iff.mp hu a.1
    have hnot : a.1 ∉ core := a.2
    simpa [encode, hnot] using hm
  letI : Countable targetClass := hc
  have hsets : Countable (Set ordinary) := hinj.countable
  letI : Infinite ordinary := ordinary_infinite.to_subtype
  exact GenLimit.UnionClosedness.powerSet_not_countable ordinary hsets

lemma uniformly_generatable : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t => 2 ^ t, Nat.pow_right_injective (by omega), 0, ?_⟩
  intro K hK t _
  rcases hK with ⟨A, hA, rfl⟩
  exact Or.inl ⟨t, rfl⟩

lemma negative_claim : NegativeClaim := by
  intro gen _
  refine ⟨builtTarget gen, builtTarget_mem_class gen,
    builtPresenter gen, builtTranscript gen,
    ambientOrder (builtTarget gen) (builtTarget_infinite gen), ?_⟩
  exact ⟨rfl, Nat.nth_strictMono (builtTarget_infinite gen),
    built_presentedBy gen, built_followsProtocol gen,
    built_clean gen, built_injective gen, built_complete gen,
    scored_upperDensity_zero gen⟩

end Stage3Proof

open Stage3S2B
open Stage3Proof

theorem stage3_result : Stage3S2B.MainClaim := by
  exact ⟨targetClass_not_countable, uniformly_generatable, negative_claim⟩
