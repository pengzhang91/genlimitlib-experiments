import Stage3Model
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation

open Set Filter
open scoped Topology

namespace S2BProof

open Stage3S2B
open GenLimit.KleinbergWei

noncomputable section

 local instance coreDecidable : DecidablePred (fun z => z ∈ core) := Classical.decPred _

 def oddCode (i : ℕ) : ℕ := 2 * i + 3

 theorem oddCode_injective : Function.Injective oddCode := by
  intro i j h
  simp [oddCode] at h
  omega

 theorem oddCode_not_core (i : ℕ) : oddCode i ∉ core := by
  rintro ⟨k, hk⟩
  cases k with
  | zero => simp [oddCode] at hk
  | succ k =>
      change 2 ^ (k + 1) = oddCode i at hk
      rw [Nat.two_pow_succ] at hk
      simp [oddCode] at hk
      omega

 def forbidden {t : ℕ} (xs : Fin t → ℕ) (qs : Fin t → Option ℕ)
    (ys : Fin t → ℕ) : Finset ℕ :=
  (Finset.univ.image xs ∪ Finset.univ.image (fun i => (qs i).getD 0)) ∪
    Finset.univ.image ys

 theorem forbidden_card_le {t : ℕ} (xs : Fin t → ℕ)
    (qs : Fin t → Option ℕ) (ys : Fin t → ℕ) :
    (forbidden xs qs ys).card ≤ 3 * t := by
  unfold forbidden
  calc
    ((Finset.univ.image xs ∪ Finset.univ.image fun i => (qs i).getD 0) ∪
        Finset.univ.image ys).card ≤
        (Finset.univ.image xs ∪ Finset.univ.image fun i => (qs i).getD 0).card +
          (Finset.univ.image ys).card := Finset.card_union_le _ _
    _ ≤ ((Finset.univ.image xs).card +
          (Finset.univ.image fun i => (qs i).getD 0).card) +
          (Finset.univ.image ys).card :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ (t + t) + t := by
      have hx : (Finset.univ.image xs).card ≤ t := by
        simpa using (Finset.card_image_le : (Finset.univ.image xs).card ≤ Finset.univ.card)
      have hq : (Finset.univ.image (fun i => (qs i).getD 0)).card ≤ t := by
        simpa using (Finset.card_image_le :
          (Finset.univ.image (fun i => (qs i).getD 0)).card ≤ Finset.univ.card)
      have hy : (Finset.univ.image ys).card ≤ t := by
        simpa using (Finset.card_image_le : (Finset.univ.image ys).card ≤ Finset.univ.card)
      omega
    _ = 3 * t := by omega

 theorem exists_fresh_oddCode {t : ℕ} (xs : Fin t → ℕ)
    (qs : Fin t → Option ℕ) (ys : Fin t → ℕ) :
    ∃ i < 3 * t + 1, oddCode i ∉ forbidden xs qs ys := by
  let candidates := (Finset.range (3 * t + 1)).image oddCode
  have hcandidates : candidates.card = 3 * t + 1 := by
    dsimp [candidates]
    rw [Finset.card_image_of_injective _ oddCode_injective]
    simp
  have hlt : (forbidden xs qs ys).card < candidates.card := by
    rw [hcandidates]
    exact Nat.lt_succ_of_le (by simpa [Nat.mul_comm] using forbidden_card_le xs qs ys)
  obtain ⟨z, hzCand, hzFresh⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [candidates, Finset.mem_image, Finset.mem_range] at hzCand
  obtain ⟨i, hi, rfl⟩ := hzCand
  exact ⟨i, hi, hzFresh⟩

 def freshOrdIndex {t : ℕ} (xs : Fin t → ℕ) (qs : Fin t → Option ℕ)
    (ys : Fin t → ℕ) : ℕ :=
  Nat.find (exists_fresh_oddCode xs qs ys)

 theorem freshOrdIndex_lt {t : ℕ} (xs : Fin t → ℕ)
    (qs : Fin t → Option ℕ) (ys : Fin t → ℕ) :
    freshOrdIndex xs qs ys < 3 * t + 1 :=
  (Nat.find_spec (exists_fresh_oddCode xs qs ys)).1

 theorem freshOrdIndex_fresh {t : ℕ} (xs : Fin t → ℕ)
    (qs : Fin t → Option ℕ) (ys : Fin t → ℕ) :
    oddCode (freshOrdIndex xs qs ys) ∉ forbidden xs qs ys :=
  (Nat.find_spec (exists_fresh_oddCode xs qs ys)).2

 def adversarialPresenter : CausalPresenter where
  next t xs qs _as ys :=
    if Even t then 2 ^ (t / 2)
    else oddCode (freshOrdIndex xs qs ys)

 structure History (t : ℕ) where
  x : Fin t → ℕ
  q : Fin t → Option ℕ
  a : Fin t → Option Bool
  y : Fin t → ℕ

 def initialHistory : History 0 where
  x := Fin.elim0
  q := Fin.elim0
  a := Fin.elim0
  y := Fin.elim0

 def answerAt (xs : Fin (t + 1) → ℕ) (q : Option ℕ) : Option Bool :=
  match q with
  | none => none
  | some z => by
      classical
      exact some (decide (z ∈ core ∨ ∃ i, xs i = z))

 def snoc {t : ℕ} {α : Type*} (f : Fin t → α) (x : α) : Fin (t + 1) → α :=
  Fin.lastCases x f

 @[simp] theorem snoc_castSucc {t : ℕ} {α : Type*} (f : Fin t → α) (x : α)
    (i : Fin t) : snoc f x i.castSucc = f i := by
  simp [snoc]

 @[simp] theorem snoc_last {t : ℕ} {α : Type*} (f : Fin t → α) (x : α) :
    snoc f x (Fin.last t) = x := by
  simp [snoc]

 def stepHistory (gen : FeedbackGenerator) {t : ℕ}
    (h : History t) : History (t + 1) := by
  let x := adversarialPresenter.next t h.x h.q h.a h.y
  let xs := snoc h.x x
  let q := gen.query t xs h.a
  let a := answerAt xs q
  let as := snoc h.a a
  let y := gen.output t xs as
  exact {
    x := xs
    q := snoc h.q q
    a := as
    y := snoc h.y y
  }

 def histories (gen : FeedbackGenerator) : (t : ℕ) → History t
  | 0 => initialHistory
  | t + 1 => stepHistory gen (histories gen t)

 def runTranscript (gen : FeedbackGenerator) : Transcript where
  presentation t := (histories gen (t + 1)).x (Fin.last t)
  query t := (histories gen (t + 1)).q (Fin.last t)
  answer t := (histories gen (t + 1)).a (Fin.last t)
  output t := (histories gen (t + 1)).y (Fin.last t)

 theorem histories_succ_x_init (gen : FeedbackGenerator) (t : ℕ) :
    Fin.init (histories gen (t + 1)).x = (histories gen t).x := by
  funext i
  simp only [histories, stepHistory, Fin.init, snoc_castSucc]

 theorem histories_succ_q_init (gen : FeedbackGenerator) (t : ℕ) :
    Fin.init (histories gen (t + 1)).q = (histories gen t).q := by
  funext i
  simp only [histories, stepHistory, Fin.init, snoc_castSucc]

 theorem histories_succ_a_init (gen : FeedbackGenerator) (t : ℕ) :
    Fin.init (histories gen (t + 1)).a = (histories gen t).a := by
  funext i
  simp only [histories, stepHistory, Fin.init, snoc_castSucc]

 theorem histories_succ_y_init (gen : FeedbackGenerator) (t : ℕ) :
    Fin.init (histories gen (t + 1)).y = (histories gen t).y := by
  funext i
  simp only [histories, stepHistory, Fin.init, snoc_castSucc]

 theorem history_x_eq_run (gen : FeedbackGenerator) (t : ℕ) :
    (histories gen t).x = fun i => (runTranscript gen).presentation i.val := by
  funext i
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [runTranscript]
      · change (Fin.init (histories gen (t + 1)).x) j =
          (runTranscript gen).presentation j.val
        rw [histories_succ_x_init]
        exact ih j

 theorem history_q_eq_run (gen : FeedbackGenerator) (t : ℕ) :
    (histories gen t).q = fun i => (runTranscript gen).query i.val := by
  funext i
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [runTranscript]
      · change (Fin.init (histories gen (t + 1)).q) j =
          (runTranscript gen).query j.val
        rw [histories_succ_q_init]
        exact ih j

 theorem history_a_eq_run (gen : FeedbackGenerator) (t : ℕ) :
    (histories gen t).a = fun i => (runTranscript gen).answer i.val := by
  funext i
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [runTranscript]
      · change (Fin.init (histories gen (t + 1)).a) j =
          (runTranscript gen).answer j.val
        rw [histories_succ_a_init]
        exact ih j

 theorem history_y_eq_run (gen : FeedbackGenerator) (t : ℕ) :
    (histories gen t).y = fun i => (runTranscript gen).output i.val := by
  funext i
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [runTranscript]
      · change (Fin.init (histories gen (t + 1)).y) j =
          (runTranscript gen).output j.val
        rw [histories_succ_y_init]
        exact ih j

 theorem presentation_eq (gen : FeedbackGenerator) (t : ℕ) :
    (runTranscript gen).presentation t = adversarialPresenter.next t
      (fun i => (runTranscript gen).presentation i)
      (fun i => (runTranscript gen).query i)
      (fun i => (runTranscript gen).answer i)
      (fun i => (runTranscript gen).output i) := by
  change (histories gen (t + 1)).x (Fin.last t) = _
  simp only [histories, stepHistory, snoc_last]
  rw [history_x_eq_run, history_q_eq_run, history_a_eq_run, history_y_eq_run]

 theorem query_eq (gen : FeedbackGenerator) (t : ℕ) :
    (runTranscript gen).query t = gen.query t
      (fun i => (runTranscript gen).presentation i)
      (fun i => (runTranscript gen).answer i) := by
  change (histories gen (t + 1)).q (Fin.last t) = _
  simp only [histories, stepHistory, snoc_last]
  change gen.query t (histories gen (t + 1)).x (histories gen t).a = _
  rw [history_x_eq_run, history_a_eq_run]

 theorem output_eq (gen : FeedbackGenerator) (t : ℕ) :
    (runTranscript gen).output t = gen.output t
      (fun i => (runTranscript gen).presentation i)
      (fun i => (runTranscript gen).answer i) := by
  change (histories gen (t + 1)).y (Fin.last t) = _
  simp only [histories, stepHistory, snoc_last]
  change gen.output t (histories gen (t + 1)).x (histories gen (t + 1)).a = _
  rw [history_x_eq_run, history_a_eq_run]

 theorem answer_eq (gen : FeedbackGenerator) (t : ℕ) :
    (runTranscript gen).answer t = answerAt
      (fun i : Fin (t + 1) => (runTranscript gen).presentation i.val)
      ((runTranscript gen).query t) := by
  change (histories gen (t + 1)).a (Fin.last t) = _
  simp only [histories, stepHistory, snoc_last]
  change answerAt (histories gen (t + 1)).x
    (gen.query t (histories gen (t + 1)).x (histories gen t).a) = _
  rw [history_x_eq_run, history_a_eq_run, ← query_eq]

 theorem presentedBy_run (gen : FeedbackGenerator) :
    PresentedBy adversarialPresenter (runTranscript gen) := presentation_eq gen

 theorem presentation_even (gen : FeedbackGenerator) (k : ℕ) :
    (runTranscript gen).presentation (2 * k) = 2 ^ k := by
  rw [presentation_eq]
  simp [adversarialPresenter]

 theorem presentation_odd_formula (gen : FeedbackGenerator) (t : ℕ)
    (ht : ¬ Even t) :
    (runTranscript gen).presentation t = oddCode
      (freshOrdIndex (histories gen t).x (histories gen t).q (histories gen t).y) := by
  rw [presentation_eq]
  simp only [adversarialPresenter, ht, if_false]
  rw [← history_x_eq_run, ← history_q_eq_run, ← history_y_eq_run]

 theorem presentation_odd_not_core (gen : FeedbackGenerator) {t : ℕ}
    (ht : ¬ Even t) : (runTranscript gen).presentation t ∉ core := by
  rw [presentation_odd_formula gen t ht]
  exact oddCode_not_core _

 theorem presentation_odd_fresh (gen : FeedbackGenerator) {t : ℕ}
    (ht : ¬ Even t) (i : ℕ) (hi : i < t) :
    (runTranscript gen).presentation t ≠ (runTranscript gen).presentation i := by
  rw [presentation_odd_formula gen t ht]
  intro h
  have hf := freshOrdIndex_fresh (histories gen t).x
    (histories gen t).q (histories gen t).y
  apply hf
  unfold forbidden
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  left
  left
  exact ⟨⟨i, hi⟩, by simpa [history_x_eq_run] using h.symm⟩

 theorem presentation_odd_avoids_query (gen : FeedbackGenerator) {t i : ℕ}
    (ht : ¬ Even t) (hi : i < t) (z : ℕ)
    (hq : (runTranscript gen).query i = some z) :
    (runTranscript gen).presentation t ≠ z := by
  rw [presentation_odd_formula gen t ht]
  intro h
  have hf := freshOrdIndex_fresh (histories gen t).x
    (histories gen t).q (histories gen t).y
  apply hf
  unfold forbidden
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  left
  right
  refine ⟨⟨i, hi⟩, ?_⟩
  have hqi : (histories gen t).q ⟨i, hi⟩ = some z := by
    rw [history_q_eq_run]
    exact hq
  rw [hqi]
  simpa using h.symm

 theorem presentation_odd_avoids_output (gen : FeedbackGenerator) {t i : ℕ}
    (ht : ¬ Even t) (hi : i < t) :
    (runTranscript gen).presentation t ≠ (runTranscript gen).output i := by
  rw [presentation_odd_formula gen t ht]
  intro h
  have hf := freshOrdIndex_fresh (histories gen t).x
    (histories gen t).q (histories gen t).y
  apply hf
  unfold forbidden
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  right
  exact ⟨⟨i, hi⟩, by simpa [history_y_eq_run] using h.symm⟩

 theorem presentation_injective (gen : FeedbackGenerator) :
    Function.Injective (runTranscript gen).presentation := by
  intro i j hij
  by_cases hi : Even i
  · by_cases hj : Even j
    · rcases hi with ⟨a, ha⟩
      rcases hj with ⟨b, hb⟩
      have hai : i = 2 * a := by omega
      have hbj : j = 2 * b := by omega
      rw [hai, hbj, presentation_even, presentation_even] at hij
      exact hai.trans ((congrArg (fun n => 2 * n)
        (Nat.pow_right_injective (by norm_num) hij)).trans hbj.symm)
    · rcases hi with ⟨a, ha⟩
      have hai : i = 2 * a := by omega
      have hicore : (runTranscript gen).presentation i ∈ core := by
        exact ⟨a, by rw [hai, presentation_even]⟩
      exact False.elim (presentation_odd_not_core gen hj (hij ▸ hicore))
  · by_cases hj : Even j
    · rcases hj with ⟨b, hb⟩
      have hbj : j = 2 * b := by omega
      have hjcore : (runTranscript gen).presentation j ∈ core := by
        exact ⟨b, by rw [hbj, presentation_even]⟩
      exact False.elim (presentation_odd_not_core gen hi (hij.symm ▸ hjcore))
    · by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact presentation_odd_fresh gen hj i hlt hij.symm
      · exact presentation_odd_fresh gen hi j hgt hij

 def realizedTarget (gen : FeedbackGenerator) : Language :=
  core ∪ Set.range (runTranscript gen).presentation

 theorem realizedTarget_mem_class (gen : FeedbackGenerator) :
    realizedTarget gen ∈ targetClass := by
  refine ⟨Set.range (runTranscript gen).presentation \ core, ?_, ?_⟩
  · intro z hz
    exact hz.2
  · unfold realizedTarget
    ext z
    constructor
    · intro hz
      rcases hz with hz | hz
      · exact Or.inl hz
      · by_cases hc : z ∈ core
        · exact Or.inl hc
        · exact Or.inr ⟨hz, hc⟩
    · rintro (hz | ⟨hz, _⟩)
      · exact Or.inl hz
      · exact Or.inr hz

 theorem run_clean (gen : FeedbackGenerator) :
    Clean (runTranscript gen).presentation (realizedTarget gen) := by
  intro t
  exact Or.inr ⟨t, rfl⟩

 theorem run_complete (gen : FeedbackGenerator) :
    Complete (runTranscript gen).presentation (realizedTarget gen) := by
  intro z hz
  rcases hz with hz | hz
  · obtain ⟨k, rfl⟩ := hz
    exact ⟨2 * k, presentation_even gen k⟩
  · exact hz

 theorem future_not_presented_of_query (gen : FeedbackGenerator) {t : ℕ}
    {z : ℕ} (hq : (runTranscript gen).query t = some z)
    (hcore : z ∉ core) (hobs : ¬ ∃ i : Fin (t + 1),
      (runTranscript gen).presentation i = z) :
    z ∉ Set.range (runTranscript gen).presentation := by
  rintro ⟨s, hs⟩
  by_cases hst : s ≤ t
  · apply hobs
    exact ⟨⟨s, Nat.lt_succ_iff.mpr hst⟩, hs⟩
  · have hts : t < s := Nat.lt_of_not_ge hst
    by_cases heven : Even s
    · obtain ⟨k, hk⟩ := heven
      have hsk : s = 2 * k := by omega
      rw [hsk, presentation_even] at hs
      apply hcore
      exact ⟨k, hs⟩
    · exact presentation_odd_avoids_query gen heven hts z hq hs

 theorem followsProtocol_run (gen : FeedbackGenerator) :
    FollowsProtocol gen (realizedTarget gen) (runTranscript gen) := by
  intro t
  refine ⟨query_eq gen t, ?_, output_eq gen t⟩
  rw [answer_eq]
  cases hq : (runTranscript gen).query t with
  | none => simp [answerAt, hq]
  | some z =>
      simp only [answerAt, hq]
      by_cases hyes : z ∈ core ∨ ∃ i : Fin (t + 1),
          (runTranscript gen).presentation i = z
      · have hmem : z ∈ realizedTarget gen := by
          rcases hyes with hc | ⟨i, hi⟩
          · exact Or.inl hc
          · exact Or.inr ⟨i, hi⟩
        simp [hyes, membershipAnswer, hmem]
      · have hcore : z ∉ core := fun h => hyes (Or.inl h)
        have hobs : ¬ ∃ i : Fin (t + 1),
            (runTranscript gen).presentation i = z := fun h => hyes (Or.inr h)
        have hmem : z ∉ realizedTarget gen := by
          rintro (hc | hr)
          · exact hcore hc
          · exact future_not_presented_of_query gen hq hcore hobs hr
        simp [hyes, membershipAnswer, hmem]

 theorem scored_subset_core (gen : FeedbackGenerator) :
    scored (realizedTarget gen) (runTranscript gen).presentation
      (runTranscript gen).output ⊆ core := by
  intro z hz
  rcases hz with ⟨hzK, t, hyt, hfresh⟩
  rcases hzK with hc | ⟨s, hs⟩
  · exact hc
  · by_contra hc
    have hst : t < s := by
      by_contra hnot
      apply hfresh
      exact ⟨s, Nat.le_of_not_gt hnot, hs⟩
    by_cases heven : Even s
    · obtain ⟨k, hk⟩ := heven
      have hsk : s = 2 * k := by omega
      rw [hsk, presentation_even] at hs
      apply hc
      exact ⟨k, hs⟩
    · exact presentation_odd_avoids_output gen heven hst (hs.trans hyt.symm)

 theorem presentation_odd_bound (gen : FeedbackGenerator) {t : ℕ}
    (ht : ¬ Even t) : (runTranscript gen).presentation t ≤ 6 * t + 3 := by
  rw [presentation_odd_formula gen t ht]
  unfold oddCode
  have h := freshOrdIndex_lt (histories gen t).x
    (histories gen t).q (histories gen t).y
  omega

 theorem realizedTarget_infinite (gen : FeedbackGenerator) :
    (realizedTarget gen).Infinite := by
  apply (Set.infinite_range_of_injective
    (show Function.Injective (fun k : ℕ => 2 ^ k) from
      Nat.pow_right_injective (by norm_num))).mono
  rintro _ ⟨k, rfl⟩
  exact Or.inl ⟨k, rfl⟩

 def orderedTarget (gen : FeedbackGenerator) : Stage3S2B.OrderedLanguage where
  carrier := realizedTarget gen
  enumeration := Nat.nth (fun z => z ∈ realizedTarget gen)
  enumeration_injective := (Nat.nth_strictMono (realizedTarget_infinite gen)).injective
  range_enumeration := Nat.range_nth_of_infinite (realizedTarget_infinite gen)

 theorem orderedTarget_ambient (gen : FeedbackGenerator) :
    InheritsAmbientOrder (orderedTarget gen) :=
  Nat.nth_strictMono (realizedTarget_infinite gen)

 theorem odd_points_below (gen : FeedbackGenerator) (n k : ℕ) (hk : k < n + 1) :
    (runTranscript gen).presentation (2 * k + 1) < 12 * n + 10 := by
  have hb := presentation_odd_bound gen (t := 2 * k + 1) (by simp)
  omega

 theorem orderedTarget_enumeration_lt (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).enumeration n < 12 * n + 10 := by
  classical
  let points := (Finset.range (n + 1)).image
    (fun k => (runTranscript gen).presentation (2 * k + 1))
  let targetPrefix := (Finset.range (12 * n + 10)).filter
    (fun z => z ∈ realizedTarget gen)
  have hpointsCard : points.card = n + 1 := by
    dsimp [points]
    rw [Finset.card_image_of_injective]
    · simp
    · intro a b hab
      have := presentation_injective gen hab
      omega
  have hsub : points ⊆ targetPrefix := by
    intro z hz
    simp only [points, Finset.mem_image, Finset.mem_range] at hz
    obtain ⟨k, hk, rfl⟩ := hz
    simp only [targetPrefix, Finset.mem_filter, Finset.mem_range]
    exact ⟨odd_points_below gen n k hk, Or.inr ⟨2 * k + 1, rfl⟩⟩
  have hcount : n < Nat.count (fun z => z ∈ realizedTarget gen) (12 * n + 10) := by
    rw [Nat.count_eq_card_filter_range]
    change n < targetPrefix.card
    have := Finset.card_le_card hsub
    rw [hpointsCard] at this
    omega
  exact (Nat.lt_nth_iff_count_lt (realizedTarget_infinite gen)).mp hcount

 theorem pow_ge_square {k : ℕ} (hk : 4 ≤ k) : k * k ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      rw [Nat.pow_succ]
      nlinarith

 theorem core_prefix_card_le (B : ℕ) :
    ((Finset.range B).filter (fun z => z ∈ core)).card ≤ Nat.sqrt B + 4 := by
  classical
  let exponents := Finset.range (Nat.sqrt B + 4)
  let powers := exponents.image (fun k => 2 ^ k)
  have hsub : (Finset.range B).filter (fun z => z ∈ core) ⊆ powers := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_range] at hz
    obtain ⟨k, rfl⟩ := hz.2
    simp only [powers, exponents, Finset.mem_image, Finset.mem_range]
    refine ⟨k, ?_, rfl⟩
    by_cases hk : k < 4
    · omega
    · have hsquare : k * k < B := (pow_ge_square (Nat.le_of_not_gt hk)).trans_lt hz.1
      have hksqrt : k ≤ Nat.sqrt B := Nat.le_sqrt.mpr hsquare.le
      omega
  calc
    ((Finset.range B).filter (fun z => z ∈ core)).card ≤ powers.card :=
      Finset.card_le_card hsub
    _ ≤ exponents.card := Finset.card_image_le
    _ = Nat.sqrt B + 4 := by simp [exponents]

 theorem orderedTarget_prefixCount_core_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).prefixCount core n ≤ Nat.sqrt (12 * n + 10) + 4 := by
  classical
  unfold OrderedLanguage.prefixCount
  let source := (Finset.range n).filter
    (fun i => (orderedTarget gen).enumeration i ∈ core)
  let values := source.image (orderedTarget gen).enumeration
  have hcard : values.card = source.card := by
    exact Finset.card_image_of_injective _ (orderedTarget gen).enumeration_injective
  rw [show ((Finset.range n).filter
    (fun i => (orderedTarget gen).enumeration i ∈ core)).card = source.card by rfl,
    ← hcard]
  calc
    values.card ≤ ((Finset.range (12 * n + 10)).filter
        (fun z => z ∈ core)).card := by
      apply Finset.card_le_card
      intro z hz
      simp only [values, Finset.mem_image, source, Finset.mem_filter,
        Finset.mem_range] at hz
      obtain ⟨i, ⟨hi, hicore⟩, rfl⟩ := hz
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr ((orderedTarget_enumeration_lt gen i).trans_le (by omega)), hicore⟩
    _ ≤ Nat.sqrt (12 * n + 10) + 4 := core_prefix_card_le _

 theorem sqrt_linear_bound (n : ℕ) :
    Nat.sqrt (12 * n + 10) + 4 ≤ 4 * Nat.sqrt n + 9 := by
  have hn := Nat.sqrt_le_add n
  have hlt : 12 * n + 10 < (4 * Nat.sqrt n + 5) * (4 * Nat.sqrt n + 5) := by
    nlinarith
  have hs : Nat.sqrt (12 * n + 10) < 4 * Nat.sqrt n + 5 :=
    Nat.sqrt_lt.mpr hlt
  omega

 theorem tendsto_density_bound :
    Tendsto (fun n : ℕ => ((4 * Nat.sqrt n + 9 : ℕ) : ℝ) / n)
      atTop (𝓝 0) := by
  have hbase := GenLimit.InfiniteContamination.tendsto_sparseSqrt_add_one_div
  have hfour : Tendsto
      (fun n : ℕ => (4 : ℝ) * (((Nat.sqrt n : ℝ) + 1) / n))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hbase :
      Tendsto (fun n : ℕ => (4 : ℝ) * (((Nat.sqrt n : ℝ) + 1) / n))
        atTop (𝓝 ((4 : ℝ) * 0)))
  have hinv : Tendsto (fun n : ℕ => (5 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  convert hfour.add hinv using 1
  · funext n
    push_cast
    ring
  · simp

 theorem orderedTarget_core_density_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity core = 0 := by
  have hratio : ∀ n, (orderedTarget gen).prefixRatio core n ≤
      ((4 * Nat.sqrt n + 9 : ℕ) : ℝ) / n := by
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · rw [OrderedLanguage.prefixRatio, if_neg hn]
      apply div_le_div_of_nonneg_right
      · exact_mod_cast (orderedTarget_prefixCount_core_le gen n).trans (sqrt_linear_bound n)
      · positivity
  have ht : Tendsto ((orderedTarget gen).prefixRatio core) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => (orderedTarget gen).prefixRatio_nonneg core n) hratio
    exact tendsto_density_bound
  exact ht.limsup_eq

 theorem scored_density_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity
      (scored (realizedTarget gen) (runTranscript gen).presentation
        (runTranscript gen).output) = 0 := by
  apply le_antisymm
  · calc
      _ ≤ (orderedTarget gen).upperDensity core :=
        (orderedTarget gen).upperDensity_mono (scored_subset_core gen)
      _ = 0 := orderedTarget_core_density_zero gen
  · exact (orderedTarget gen).upperDensity_nonneg _

end
end S2BProof

open S2BProof
open Stage3S2B

theorem stage3_result : Stage3S2B.MainClaim := by
  refine ⟨?_, ?_, ?_⟩
  · intro hcountable
    let encode : Set ℕ → targetClass := fun A =>
      ⟨core ∪ oddCode '' A, by
        refine ⟨oddCode '' A, ?_, rfl⟩
        intro z hz
        obtain ⟨i, _, rfl⟩ := hz
        exact oddCode_not_core i⟩
    have hencode : Function.Injective encode := by
      intro A B hAB
      apply Set.ext
      intro i
      have hprobe := Set.ext_iff.mp (congrArg Subtype.val hAB) (oddCode i)
      simp only [encode, Set.mem_union, Set.mem_image] at hprobe
      simp only [oddCode_not_core, false_or] at hprobe
      constructor
      · intro hi
        have : oddCode i ∈ oddCode '' B := hprobe.mp ⟨i, hi, rfl⟩
        obtain ⟨j, hj, hji⟩ := this
        exact (oddCode_injective hji).symm ▸ hj
      · intro hi
        have : oddCode i ∈ oddCode '' A := hprobe.mpr ⟨i, hi, rfl⟩
        obtain ⟨j, hj, hji⟩ := this
        exact (oddCode_injective hji).symm ▸ hj
    letI : Countable targetClass := hcountable.to_subtype
    have hpower : Countable (Set ℕ) := hencode.countable
    exact GenLimit.UnionClosedness.powerSet_not_countable ℕ hpower
  · refine ⟨fun k => 2 ^ k, ?_, 0, ?_⟩
    · exact Nat.pow_right_injective (by norm_num)
    · intro K hK t _
      obtain ⟨A, hA, rfl⟩ := hK
      exact Or.inl ⟨t, rfl⟩
  · intro gen _
    refine ⟨realizedTarget gen, realizedTarget_mem_class gen,
      adversarialPresenter, runTranscript gen, orderedTarget gen, ?_⟩
    exact ⟨rfl, orderedTarget_ambient gen, presentedBy_run gen,
      followsProtocol_run gen, run_clean gen, presentation_injective gen,
      run_complete gen, scored_density_zero gen⟩
