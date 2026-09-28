import Stage3Model
import Mathlib

open Filter
open scoped Topology

namespace S2BProof

open Stage3S2B

noncomputable section

structure Round where
  presentation : ℕ
  query : Option ℕ
  answer : Option Bool
  output : ℕ

private def candidate (k : ℕ) : ℕ := 4 * k + 3

private theorem candidate_injective : Function.Injective candidate := by
  intro a b h
  dsimp [candidate] at h
  omega

private theorem candidate_not_core (k : ℕ) : candidate k ∉ core := by
  rintro ⟨j, hj⟩
  dsimp [candidate] at hj
  cases j with
  | zero => norm_num at hj
  | succ j =>
      have heven : Even (2 ^ (j + 1)) := by
        refine ⟨2 ^ j, ?_⟩
        simp [pow_succ, Nat.mul_comm, two_mul]
      have hodd : Odd (4 * k + 3) := by omega
      exact (Nat.not_even_iff_odd.mpr hodd) (hj ▸ heven)

private def forbidden {t : ℕ} (h : Fin t → Round) : Finset ℕ :=
  (Finset.univ.image fun i => (h i).presentation) ∪
  (Finset.univ.biUnion fun i => match (h i).query with
    | none => (∅ : Finset ℕ)
    | some z => {z}) ∪
  (Finset.univ.image fun i => (h i).output)

private theorem exists_candidate_not_forbidden {t : ℕ} (h : Fin t → Round) :
    ∃ k, candidate k ∉ forbidden h := by
  have hinf : (Set.range candidate).Infinite := Set.infinite_range_of_injective candidate_injective
  obtain ⟨z, ⟨k, rfl⟩, hz⟩ := hinf.exists_not_mem_finset (forbidden h)
  exact ⟨k, hz⟩

private def pick {t : ℕ} (h : Fin t → Round) : ℕ :=
  candidate (Nat.find (exists_candidate_not_forbidden h))

private theorem pick_not_forbidden {t : ℕ} (h : Fin t → Round) :
    pick h ∉ forbidden h := Nat.find_spec (exists_candidate_not_forbidden h)

private theorem pick_not_core {t : ℕ} (h : Fin t → Round) : pick h ∉ core :=
  candidate_not_core _

private def choosePresentation {t : ℕ} (h : Fin t → Round) : ℕ :=
  if Even t then 2 ^ (t / 2) else pick h

private def makeRound (gen : FeedbackGenerator) {t : ℕ} (h : Fin t → Round) : Round := by
  let x := choosePresentation h
  let xs : Fin (t + 1) → ℕ := Fin.lastCases x (fun i => (h i).presentation)
  let priorAnswers : Fin t → Option Bool := fun i => (h i).answer
  let q := gen.query t xs priorAnswers
  let b := q.map fun z => membershipAnswer
    (core ∪ {z | ∃ i : Fin (t + 1), xs i = z}) z
  let answers : Fin (t + 1) → Option Bool := Fin.lastCases b priorAnswers
  let y := gen.output t xs answers
  exact ⟨x, q, b, y⟩

private def history (gen : FeedbackGenerator) : (t : ℕ) → Fin t → Round
  | 0 => Fin.elim0
  | t + 1 => Fin.lastCases (makeRound gen (history gen t)) (history gen t)

private theorem history_castSucc (gen : FeedbackGenerator) {t : ℕ} (i : Fin t) :
    history gen (t + 1) i.castSucc = history gen t i := by
  simp [history]

private theorem history_last (gen : FeedbackGenerator) (t : ℕ) :
    history gen (t + 1) (Fin.last t) = makeRound gen (history gen t) := by
  simp [history]

private def builtTranscript (gen : FeedbackGenerator) : Transcript where
  presentation t := (makeRound gen (history gen t)).presentation
  query t := (makeRound gen (history gen t)).query
  answer t := (makeRound gen (history gen t)).answer
  output t := (makeRound gen (history gen t)).output

private theorem history_eq_transcript (gen : FeedbackGenerator) {t : ℕ} (i : Fin t) :
    history gen t i =
      { presentation := (builtTranscript gen).presentation i
        query := (builtTranscript gen).query i
        answer := (builtTranscript gen).answer i
        output := (builtTranscript gen).output i } := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [builtTranscript, history_last]
      · rw [history_castSucc]
        exact ih j

private def builtTarget (gen : FeedbackGenerator) : Language :=
  Set.range (builtTranscript gen).presentation

private def builtPresenter (gen : FeedbackGenerator) : CausalPresenter where
  next t _ _ _ _ := (builtTranscript gen).presentation t

private theorem built_presented (gen : FeedbackGenerator) :
    PresentedBy (builtPresenter gen) (builtTranscript gen) := by
  intro t
  rfl

private theorem current_presentation (gen : FeedbackGenerator) (t : ℕ) :
    (builtTranscript gen).presentation t = choosePresentation (history gen t) := by
  simp [builtTranscript, makeRound]

private theorem extended_presentation_eq (gen : FeedbackGenerator) (t : ℕ) :
    Fin.lastCases (choosePresentation (history gen t))
      (fun i => (history gen t i).presentation) =
      (fun i : Fin (t + 1) => (builtTranscript gen).presentation i) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [current_presentation]
  · simpa [Fin.lastCases] using congrArg Round.presentation (history_eq_transcript gen j)

private theorem extended_answer_eq (gen : FeedbackGenerator) (t : ℕ) :
    Fin.lastCases (makeRound gen (history gen t)).answer
      (fun i => (history gen t i).answer) =
      (fun i : Fin (t + 1) => (builtTranscript gen).answer i) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [builtTranscript, Fin.lastCases]
  · simpa [Fin.lastCases] using congrArg Round.answer (history_eq_transcript gen j)

private theorem finite_prefix_set_eq_observed (gen : FeedbackGenerator) (t : ℕ) :
    {z | ∃ i : Fin (t + 1), (builtTranscript gen).presentation i = z} =
      observedThrough (builtTranscript gen).presentation t := by
  ext z
  simp only [Set.mem_setOf_eq, observedThrough]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, Nat.lt_succ_iff.mp i.isLt, hi⟩
  · rintro ⟨s, hs, hz⟩
    exact ⟨⟨s, Nat.lt_succ_iff.mpr hs⟩, hz⟩

private theorem built_protocol_query_output (gen : FeedbackGenerator) (t : ℕ) :
    (builtTranscript gen).query t = gen.query t
      (fun i => (builtTranscript gen).presentation i)
      (fun i => (builtTranscript gen).answer i) ∧
    (builtTranscript gen).answer t =
      ((builtTranscript gen).query t).map (fun z =>
        membershipAnswer (core ∪ observedThrough (builtTranscript gen).presentation t) z) ∧
    (builtTranscript gen).output t = gen.output t
      (fun i => (builtTranscript gen).presentation i)
      (fun i => (builtTranscript gen).answer i) := by
  have hprior : (fun i : Fin t => (history gen t i).answer) =
      (fun i : Fin t => (builtTranscript gen).answer i) := by
    funext i
    simpa only [history_eq_transcript]
  have hxs := extended_presentation_eq gen t
  have hans := extended_answer_eq gen t
  have hset : {z | ∃ i : Fin (t + 1),
      Fin.lastCases (choosePresentation (history gen t))
        (fun i => (history gen t i).presentation) i = z} =
      observedThrough (builtTranscript gen).presentation t := by
    calc
      _ = {z | ∃ i : Fin (t + 1), (builtTranscript gen).presentation i = z} := by
        ext z
        constructor <;> rintro ⟨i, hi⟩ <;> refine ⟨i, ?_⟩
        · simpa only [hxs] using hi
        · simpa only [hxs] using hi
      _ = _ := finite_prefix_set_eq_observed gen t
  have hquery : (builtTranscript gen).query t = gen.query t
      (fun i => (builtTranscript gen).presentation i)
      (fun i => (builtTranscript gen).answer i) := by
    change (makeRound gen (history gen t)).query = _
    simp only [makeRound]
    rw [hxs, hprior]
  have hanswer : (builtTranscript gen).answer t =
      ((builtTranscript gen).query t).map (fun z =>
        membershipAnswer (core ∪ observedThrough (builtTranscript gen).presentation t) z) := by
    change (makeRound gen (history gen t)).answer = _
    simp only [makeRound]
    rw [hxs, hprior, hset, hquery]
  have houtput : (builtTranscript gen).output t = gen.output t
      (fun i => (builtTranscript gen).presentation i)
      (fun i => (builtTranscript gen).answer i) := by
    change (makeRound gen (history gen t)).output = _
    change gen.output t
      (Fin.lastCases (choosePresentation (history gen t))
        (fun i => (history gen t i).presentation))
      (Fin.lastCases (makeRound gen (history gen t)).answer
        (fun i => (history gen t i).answer)) = _
    rw [hxs, hans]
  exact ⟨hquery, hanswer, houtput⟩

private theorem prior_value_forbidden (gen : FeedbackGenerator) {s t : ℕ} (hst : s < t) :
    (builtTranscript gen).presentation s ∈ forbidden (history gen t) ∧
    (builtTranscript gen).output s ∈ forbidden (history gen t) ∧
    ∀ z, (builtTranscript gen).query s = some z → z ∈ forbidden (history gen t) := by
  let i : Fin t := ⟨s, hst⟩
  have hi := history_eq_transcript gen i
  constructor
  · apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by simpa [i] using congrArg Round.presentation hi⟩
  constructor
  · apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by simpa [i] using congrArg Round.output hi⟩
  · intro z hz
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ _, ?_⟩
    have hiq : (history gen t i).query = some z := by
      simpa [i, hz] using congrArg Round.query hi
    simp [hiq]

private theorem odd_pick (gen : FeedbackGenerator) {t : ℕ} (ht : ¬ Even t) :
    (builtTranscript gen).presentation t = pick (history gen t) := by
  simp [current_presentation, choosePresentation, ht]

private theorem even_core (gen : FeedbackGenerator) {t : ℕ} (ht : Even t) :
    (builtTranscript gen).presentation t ∈ core := by
  rw [current_presentation]
  simp [choosePresentation, ht, core]

private theorem odd_not_core (gen : FeedbackGenerator) {t : ℕ} (ht : ¬ Even t) :
    (builtTranscript gen).presentation t ∉ core := by
  rw [odd_pick gen ht]
  exact pick_not_core _

private theorem built_injective (gen : FeedbackGenerator) :
    Function.Injective (builtTranscript gen).presentation := by
  intro s t h
  by_contra hne
  wlog hst : s < t generalizing s t
  · have hts : t < s := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hst) (Ne.symm hne)
    exact this (Eq.symm h) (Ne.symm hne) hts
  by_cases he : Even t
  · have hsCore : (builtTranscript gen).presentation s ∈ core := h ▸ even_core gen he
    by_cases hse : Even s
    · obtain ⟨a, rfl⟩ := hse
      obtain ⟨b, rfl⟩ := he
      have ha : (a + a) / 2 = a := by omega
      have hb : (b + b) / 2 = b := by omega
      have hp : 2 ^ a = 2 ^ b := by
        simpa [current_presentation, choosePresentation, ha, hb] using h
      have : a = b := (pow_right_strictMono₀ (by norm_num : (1:ℕ) < 2)).injective hp
      omega
    · exact odd_not_core gen hse hsCore
  · rw [odd_pick gen he] at h
    have hforb := (prior_value_forbidden gen hst).1
    rw [h] at hforb
    exact pick_not_forbidden (history gen t) hforb

private theorem built_clean (gen : FeedbackGenerator) :
    Clean (builtTranscript gen).presentation (builtTarget gen) := by
  intro t
  exact ⟨t, rfl⟩

private theorem built_complete (gen : FeedbackGenerator) :
    Complete (builtTranscript gen).presentation (builtTarget gen) := by
  rintro z ⟨t, rfl⟩
  exact ⟨t, rfl⟩

private theorem core_subset_target (gen : FeedbackGenerator) : core ⊆ builtTarget gen := by
  rintro z ⟨k, rfl⟩
  refine ⟨2 * k, ?_⟩
  rw [current_presentation]
  simp [choosePresentation, show Even (2 * k) by exact ⟨k, by omega⟩]

private theorem target_mem_class (gen : FeedbackGenerator) : builtTarget gen ∈ targetClass := by
  refine ⟨builtTarget gen ∩ ordinary, Set.inter_subset_right, ?_⟩
  ext z
  constructor
  · intro hz
    by_cases hc : z ∈ core
    · exact Or.inl hc
    · exact Or.inr ⟨hz, hc⟩
  · rintro (hc | ⟨hz, _⟩)
    · exact core_subset_target gen hc
    · exact hz

private theorem future_avoids_query (gen : FeedbackGenerator) {s t z : ℕ}
    (hst : s < t) (hq : (builtTranscript gen).query s = some z)
    (hz : z ∉ core) : (builtTranscript gen).presentation t ≠ z := by
  intro h
  by_cases he : Even t
  · exact hz (h ▸ even_core gen he)
  · rw [odd_pick gen he] at h
    have hf := (prior_value_forbidden gen hst).2.2 z hq
    rw [← h] at hf
    exact pick_not_forbidden (history gen t) hf

private theorem future_avoids_output (gen : FeedbackGenerator) {s t : ℕ}
    (hst : s < t) (hz : (builtTranscript gen).output s ∉ core) :
    (builtTranscript gen).presentation t ≠ (builtTranscript gen).output s := by
  intro h
  by_cases he : Even t
  · exact hz (h ▸ even_core gen he)
  · rw [odd_pick gen he] at h
    have hf := (prior_value_forbidden gen hst).2.1
    rw [← h] at hf
    exact pick_not_forbidden (history gen t) hf

private theorem query_answer_truthful (gen : FeedbackGenerator) (t : ℕ) :
    (builtTranscript gen).answer t = match (builtTranscript gen).query t with
      | none => none
      | some z => some (membershipAnswer (builtTarget gen) z) := by
  obtain ⟨_, hb, _⟩ := built_protocol_query_output gen t
  rw [hb]
  cases hq : (builtTranscript gen).query t with
  | none => simp
  | some z =>
      simp only [Option.map_some]
      congr 1
      apply Bool.eq_iff_iff.mpr
      simp only [membershipAnswer, decide_eq_true_eq]
      constructor
      · rintro (hc | ⟨s, hst, hs⟩)
        · exact core_subset_target gen hc
        · exact ⟨s, hs⟩
      · rintro ⟨s, hs⟩
        by_cases hst : s ≤ t
        · exact Or.inr ⟨s, hst, hs⟩
        · have hts : t < s := Nat.lt_of_not_ge hst
          by_cases hc : z ∈ core
          · exact Or.inl hc
          · exfalso
            exact future_avoids_query gen hts hq hc hs

private theorem built_follows (gen : FeedbackGenerator) :
    FollowsProtocol gen (builtTarget gen) (builtTranscript gen) := by
  intro t
  obtain ⟨hq, _, hy⟩ := built_protocol_query_output gen t
  exact ⟨hq, query_answer_truthful gen t, hy⟩

private theorem scored_subset_core (gen : FeedbackGenerator) :
    scored (builtTarget gen) (builtTranscript gen).presentation
      (builtTranscript gen).output ⊆ core := by
  rintro z ⟨_, t, hyt, hnot⟩
  by_contra hz
  obtain ⟨s, hs⟩ := show z ∈ builtTarget gen by assumption
  have hts : t < s := by
    by_contra hle
    exact hnot ⟨s, Nat.le_of_not_gt hle, hs⟩
  exact future_avoids_output gen hts (by simpa [hyt] using hz) (by simpa [hyt] using hs)


private theorem forbidden_card_le {t : ℕ} (h : Fin t → Round) :
    (forbidden h).card ≤ 3 * t := by
  let A := Finset.univ.image fun i => (h i).presentation
  let B := Finset.univ.biUnion fun i => match (h i).query with
    | none => (∅ : Finset ℕ)
    | some z => {z}
  let C := Finset.univ.image fun i => (h i).output
  have hA : A.card ≤ t := by
    dsimp [A]
    simpa using (Finset.card_image_le :
      (Finset.univ.image fun i : Fin t => (h i).presentation).card ≤ Finset.univ.card)
  have hB : B.card ≤ t := by
    calc
      B.card ≤ ∑ i ∈ (Finset.univ : Finset (Fin t)),
          (match (h i).query with | none => (∅ : Finset ℕ) | some z => {z}).card := by
        exact Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin t)), 1 := by
        apply Finset.sum_le_sum
        intro i hi
        cases (h i).query <;> simp
      _ = t := by simp
  have hC : C.card ≤ t := by
    dsimp [C]
    simpa using (Finset.card_image_le :
      (Finset.univ.image fun i : Fin t => (h i).output).card ≤ Finset.univ.card)
  change ((A ∪ B) ∪ C).card ≤ 3 * t
  calc
    ((A ∪ B) ∪ C).card ≤ (A ∪ B).card + C.card := Finset.card_union_le _ _
    _ ≤ (A.card + B.card) + C.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ (t + t) + t := by omega
    _ = 3 * t := by omega

private theorem pick_le {t : ℕ} (h : Fin t → Round) : pick h ≤ 12 * t + 3 := by
  let F := forbidden h
  let m := F.card
  have hk : Nat.find (exists_candidate_not_forbidden h) ≤ m := by
    by_contra hn
    have hall : ∀ k ∈ Finset.range (m + 1), candidate k ∈ F := by
      intro k hk
      have hlt : k < Nat.find (exists_candidate_not_forbidden h) := by
        have : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        omega
      exact not_not.mp (Nat.find_min (exists_candidate_not_forbidden h) hlt)
    have hsub : Finset.image candidate (Finset.range (m + 1)) ⊆ F := by
      intro z hz
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
      exact hall k hk
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_iff.mpr (candidate_injective.injOn), Finset.card_range] at hc
    omega
  unfold pick candidate
  have hf := forbidden_card_le h
  dsimp [F, m] at hk
  omega

private theorem odd_presentation_bound (gen : FeedbackGenerator) (r : ℕ) :
    (builtTranscript gen).presentation (2 * r + 1) ≤ 24 * r + 15 := by
  rw [odd_pick gen (by exact Nat.not_even_iff_odd.mpr ⟨r, by omega⟩)]
  have h := pick_le (history gen (2 * r + 1))
  omega

private theorem target_infinite (gen : FeedbackGenerator) : (builtTarget gen).Infinite := by
  exact Set.Infinite.mono (core_subset_target gen)
    (Set.infinite_range_of_injective (pow_right_strictMono₀ (by norm_num : (1:ℕ) < 2)).injective)

private theorem target_nth_le (gen : FeedbackGenerator) (n : ℕ) :
    Nat.nth (fun z => z ∈ builtTarget gen) n ≤ 24 * n + 15 := by
  classical
  have hcount : n < Nat.count (fun z => z ∈ builtTarget gen) (24 * n + 16) := by
    rw [Nat.count_eq_card_filter_range]
    let f : Fin (n + 1) → ℕ := fun i => (builtTranscript gen).presentation (2 * i + 1)
    have hfmem : ∀ i, f i ∈ (Finset.range (24 * n + 16)).filter
        (fun z => z ∈ builtTarget gen) := by
      intro i
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · have hb := odd_presentation_bound gen i
        have hi : (i : ℕ) ≤ n := Nat.le_of_lt_succ i.isLt
        change (builtTranscript gen).presentation (2 * (i : ℕ) + 1) < 24 * n + 16
        omega
      · exact ⟨2 * i + 1, rfl⟩
    have hfinj : Function.Injective f := by
      intro i j hij
      have := built_injective gen hij
      ext
      omega
    have himage : Finset.image f Finset.univ ⊆
        (Finset.range (24 * n + 16)).filter (fun z => z ∈ builtTarget gen) := by
      intro z hz
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
      exact hfmem i
    have hc := Finset.card_le_card himage
    rw [Finset.card_image_iff.mpr hfinj.injOn] at hc
    simpa using hc
  exact Nat.le_of_lt_succ (Nat.nth_lt_of_lt_count hcount)


private def orderedTarget (gen : FeedbackGenerator) : OrderedLanguage where
  carrier := builtTarget gen
  enumeration := Nat.nth (fun z => z ∈ builtTarget gen)
  enumeration_injective := Nat.nth_injective (target_infinite gen)
  range_enumeration := Nat.range_nth_of_infinite (target_infinite gen)

private theorem orderedTarget_inherits (gen : FeedbackGenerator) :
    InheritsAmbientOrder (orderedTarget gen) := Nat.nth_strictMono (target_infinite gen)

private noncomputable def coreExponent (z : ℕ) : ℕ := by
  classical
  exact if hz : z ∈ core then Classical.choose hz else 0

private theorem pow_coreExponent {z : ℕ} (hz : z ∈ core) : 2 ^ coreExponent z = z := by
  classical
  simp [coreExponent, hz, Classical.choose_spec hz]

private theorem coreExponent_injective_on : Set.InjOn coreExponent core := by
  intro a ha b hb hab
  calc
    a = 2 ^ coreExponent a := (pow_coreExponent ha).symm
    _ = 2 ^ coreExponent b := by rw [hab]
    _ = b := pow_coreExponent hb

private theorem core_prefixCount_le_log (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).prefixCount core n ≤ Nat.log 2 (24 * n + 15) + 1 := by
  classical
  let S := (Finset.range n).filter fun i => (orderedTarget gen).enumeration i ∈ core
  have hmap : Finset.image (fun i => coreExponent ((orderedTarget gen).enumeration i)) S ⊆
      Finset.range (Nat.log 2 (24 * n + 15) + 1) := by
    intro k hk
    obtain ⟨i, hiS, rfl⟩ := Finset.mem_image.mp hk
    have hi : i < n := Finset.mem_range.mp (Finset.mem_filter.mp hiS).1
    have hcore : (orderedTarget gen).enumeration i ∈ core := (Finset.mem_filter.mp hiS).2
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    apply Nat.le_log_of_pow_le (by norm_num)
    rw [pow_coreExponent hcore]
    have hmono := (orderedTarget_inherits gen).monotone (Nat.le_of_lt hi)
    exact hmono.trans (target_nth_le gen n)
  have hinj : Set.InjOn (fun i => coreExponent ((orderedTarget gen).enumeration i)) (↑S : Set ℕ) := by
    intro i hi j hj hij
    apply (orderedTarget gen).enumeration_injective
    apply coreExponent_injective_on
    · exact (Finset.mem_filter.mp hi).2
    · exact (Finset.mem_filter.mp hj).2
    · exact hij
  have hc := Finset.card_le_card hmap
  rw [Finset.card_image_iff.mpr hinj, Finset.card_range] at hc
  exact hc

private theorem core_prefixRatio_tendsto_zero (gen : FeedbackGenerator) :
    Tendsto ((orderedTarget gen).prefixRatio core) atTop (𝓝 0) := by
  have hbound : ∀ n, (orderedTarget gen).prefixRatio core n ≤
      ((Nat.log 2 (24 * n + 15) + 1 : ℕ) : ℝ) / n := by
    intro n
    unfold GenLimit.KleinbergWei.OrderedLanguage.prefixRatio
    split
    · positivity
    · gcongr
      exact_mod_cast core_prefixCount_le_log gen n
  have hnonneg : ∀ n, 0 ≤ (orderedTarget gen).prefixRatio core n := by
    intro n
    unfold GenLimit.KleinbergWei.OrderedLanguage.prefixRatio
    split <;> positivity
  have hlog : Tendsto (fun n : ℕ =>
      Real.logb 2 (24 * (n : ℝ) + 15) / (n : ℝ)) atTop (𝓝 0) := by
    have hx : Tendsto (fun n : ℕ => 24 * (n : ℝ) + 15) atTop atTop := by
      have hm : Tendsto (fun n : ℕ => (24 : ℝ) * n) atTop atTop :=
        Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
      simpa [add_comm] using (tendsto_const_nhds.add_atTop hm :
        Tendsto (fun n : ℕ => (15 : ℝ) + 24 * n) atTop atTop)
    have ht := (Real.tendsto_pow_logb_div_mul_add_atTop
      (b := (2 : ℝ)) (1 / 24) (-15 / 24) 1 (by norm_num)).comp hx
    convert ht using 1
    · funext n
      simp only [Function.comp_apply, pow_one]
      congr 1
      ring
  have hmajor : Tendsto (fun n : ℕ =>
      ((Nat.log 2 (24 * n + 15) + 1 : ℕ) : ℝ) / n) atTop (𝓝 0) := by
    have hnatlog : ∀ n : ℕ, ((Nat.log 2 (24 * n + 15) : ℕ) : ℝ) ≤
        Real.logb 2 (24 * (n : ℝ) + 15) := by
      intro n
      simpa [Nat.cast_add, Nat.cast_mul] using Real.natLog_le_logb (24 * n + 15) 2
    refine squeeze_zero'
      (f := fun n : ℕ => ((Nat.log 2 (24 * n + 15) + 1 : ℕ) : ℝ) / n)
      (g := fun n : ℕ => Real.logb 2 (24 * (n : ℝ) + 15) / n + 1 / n) ?_ ?_ ?_
    · filter_upwards with n
      positivity
    · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [Nat.cast_add, Nat.cast_one, add_div]
      gcongr
      exact hnatlog n
    · simpa using hlog.add tendsto_one_div_atTop_nhds_zero_nat
  exact squeeze_zero hnonneg hbound hmajor

private theorem core_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity core = 0 :=
  (core_prefixRatio_tendsto_zero gen).limsup_eq

private theorem scored_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity
      (scored (builtTarget gen) (builtTranscript gen).presentation
        (builtTranscript gen).output) = 0 := by
  have hratio : ∀ n, (orderedTarget gen).prefixRatio
      (scored (builtTarget gen) (builtTranscript gen).presentation
        (builtTranscript gen).output) n ≤ (orderedTarget gen).prefixRatio core n := by
    intro n
    unfold GenLimit.KleinbergWei.OrderedLanguage.prefixRatio
    split
    · rfl
    · gcongr
      unfold GenLimit.KleinbergWei.OrderedLanguage.prefixCount
      apply Finset.card_le_card
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
      exact ⟨hi.1, scored_subset_core gen hi.2⟩
  have hnonneg : ∀ n, 0 ≤ (orderedTarget gen).prefixRatio
      (scored (builtTarget gen) (builtTranscript gen).presentation
        (builtTranscript gen).output) n := by
    intro n
    unfold GenLimit.KleinbergWei.OrderedLanguage.prefixRatio
    split <;> positivity
  have ht := squeeze_zero hnonneg hratio (core_prefixRatio_tendsto_zero gen)
  exact ht.limsup_eq


private def classEmbedding (A : Set ℕ) : Language :=
  core ∪ candidate '' A

private theorem classEmbedding_mem (A : Set ℕ) : classEmbedding A ∈ targetClass := by
  refine ⟨candidate '' A, ?_, rfl⟩
  rintro z ⟨k, _, rfl⟩
  exact candidate_not_core k

private theorem classEmbedding_injective : Function.Injective classEmbedding := by
  intro A B h
  ext k
  have hk : candidate k ∉ core := candidate_not_core k
  have hcand : ∀ C : Set ℕ, candidate k ∈ classEmbedding C ↔ k ∈ C := by
    intro C
    simp only [classEmbedding, Set.mem_union, Set.mem_image]
    constructor
    · rintro (hcore | ⟨j, hj, heq⟩)
      · exact False.elim (hk hcore)
      · exact (candidate_injective heq).symm ▸ hj
    · intro hkC
      exact Or.inr ⟨k, hkC, rfl⟩
  rw [← hcand A, h, hcand B]

private theorem targetClass_uncountable : ¬ targetClass.Countable := by
  intro hcount
  have hpre := hcount.preimage classEmbedding_injective
  have hall : classEmbedding ⁻¹' targetClass = (Set.univ : Set (Set ℕ)) := by
    ext A
    simp [classEmbedding_mem]
  rw [hall] at hpre
  obtain ⟨f, hf⟩ := hpre.exists_surjective Set.univ_nonempty
  let diagonal : Set ℕ := {n | n ∉ (f n : Set ℕ)}
  obtain ⟨n, hn⟩ := hf ⟨diagonal, Set.mem_univ diagonal⟩
  have heq : (f n : Set ℕ) = diagonal := congrArg Subtype.val hn
  have hmem : n ∈ (f n : Set ℕ) ↔ n ∈ diagonal := Set.ext_iff.mp heq n
  have hdef : n ∈ diagonal ↔ n ∉ (f n : Set ℕ) := by
    rfl
  have hdiag := hmem.trans hdef
  tauto

private theorem uniformly_generatable : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t => 2 ^ t, (pow_right_strictMono₀ (by norm_num : (1 : ℕ) < 2)).injective, 0, ?_⟩
  intro K hK t ht
  obtain ⟨A, hA, rfl⟩ := hK
  exact Or.inl ⟨t, rfl⟩

private theorem negative_claim : NegativeClaim := by
  intro gen hgen
  refine ⟨builtTarget gen, target_mem_class gen, builtPresenter gen,
    builtTranscript gen, orderedTarget gen, ?_⟩
  refine ⟨rfl, orderedTarget_inherits gen, built_presented gen, built_follows gen,
    built_clean gen, built_injective gen, built_complete gen, ?_⟩
  exact scored_upperDensity_zero gen

end
end S2BProof

open Stage3S2B

theorem stage3_result : Stage3S2B.MainClaim := by
  exact ⟨S2BProof.targetClass_uncountable,
    S2BProof.uniformly_generatable, S2BProof.negative_claim⟩
