import Stage3Model
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import GenLimit.Paper39_DenseGeneration.Abstract.Density
import Mathlib.Data.Nat.Nth

open Set

namespace Stage3Work

open Stage3S2B

lemma oddCode_mem_ordinary (n : ℕ) : 2 * n + 3 ∈ ordinary := by
  intro h
  rcases h with ⟨k, hk⟩
  cases k with
  | zero => simp at hk
  | succ k =>
      have hd : 2 ∣ 2 ^ (Nat.succ k) := by
        simp [pow_succ]
      have hk' : 2 ^ (Nat.succ k) = 2 * n + 3 := by simpa using hk
      rw [hk'] at hd
      omega

lemma oddCode_injective : Function.Injective (fun n : ℕ => 2 * n + 3) := by
  intro a b h
  dsimp at h
  omega

noncomputable def encodedTarget (S : Set ℕ) : Set ℕ :=
  core ∪ ((fun n : ℕ => 2 * n + 3) '' S)

lemma encodedTarget_mem (S : Set ℕ) : encodedTarget S ∈ targetClass := by
  refine ⟨(fun n : ℕ => 2 * n + 3) '' S, ?_, rfl⟩
  rintro _ ⟨n, -, rfl⟩
  exact oddCode_mem_ordinary n

lemma encodedTarget_injective : Function.Injective encodedTarget := by
  intro S T h
  ext n
  have hcode := Set.ext_iff.mp h (2 * n + 3)
  have hncore : 2 * n + 3 ∉ core := oddCode_mem_ordinary n
  simpa [encodedTarget, hncore, oddCode_injective.eq_iff] using hcode

lemma targetClass_not_countable : ¬ targetClass.Countable := by
  intro hC
  haveI : Countable targetClass := Set.countable_coe_iff.mpr hC
  let f : Set ℕ → targetClass := fun S => ⟨encodedTarget S, encodedTarget_mem S⟩
  have hf : Function.Injective f := by
    intro S T h
    exact encodedTarget_injective (Subtype.ext_iff.mp h)
  haveI : Countable (Set ℕ) := hf.countable
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ inferInstance

lemma uniform_generation : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun k => 2 ^ k, Nat.pow_right_injective (by omega), 0, ?_⟩
  intro K hK t ht
  rcases hK with ⟨A, hA, rfl⟩
  exact Or.inl ⟨t, rfl⟩



structure Hist (t : ℕ) where
  x : Fin t → ℕ
  q : Fin t → Option ℕ
  a : Fin t → Option Bool
  y : Fin t → ℕ

noncomputable def forbidden {t : ℕ} (h : Hist t) : Finset ℕ :=
  (Finset.univ.image h.x) ∪
    (Finset.univ.image (fun i => (h.q i).getD 0)) ∪
    (Finset.univ.image h.y)

lemma ordinary_infinite : ordinary.Infinite := by
  apply (Set.infinite_range_of_injective oddCode_injective).mono
  rintro _ ⟨n, rfl⟩
  exact oddCode_mem_ordinary n

noncomputable def chooseOrdinary {t : ℕ} (h : Hist t) : ℕ := by
  classical
  exact Nat.find (ordinary_infinite.exists_not_mem_finset (forbidden h))

lemma chooseOrdinary_spec {t : ℕ} (h : Hist t) :
    chooseOrdinary h ∈ ordinary ∧ chooseOrdinary h ∉ forbidden h := by
  classical
  exact Nat.find_spec (ordinary_infinite.exists_not_mem_finset (forbidden h))

noncomputable def choosePresentation {t : ℕ} (h : Hist t) : ℕ :=
  if t % 2 = 0 then 2 ^ (t / 2) else chooseOrdinary h

noncomputable def extendHist (gen : FeedbackGenerator) {t : ℕ} (h : Hist t) : Hist (t + 1) := by
  let xnew := choosePresentation h
  let xext : Fin (t + 1) → ℕ := Fin.lastCases xnew h.x
  let qnew := gen.query t xext h.a
  let qext : Fin (t + 1) → Option ℕ := Fin.lastCases qnew h.q
  let anew := match qnew with
    | none => none
    | some z => some (membershipAnswer (core ∪ Set.range xext) z)
  let aext : Fin (t + 1) → Option Bool := Fin.lastCases anew h.a
  let ynew := gen.output t xext aext
  exact {
    x := xext
    q := qext
    a := aext
    y := Fin.lastCases ynew h.y
  }

noncomputable def runHist (gen : FeedbackGenerator) : (t : ℕ) → Hist t
  | 0 => ⟨Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0⟩
  | t + 1 => extendHist gen (runHist gen t)

noncomputable def adversarialTranscript (gen : FeedbackGenerator) : Transcript where
  presentation t := (runHist gen (t + 1)).x (Fin.last t)
  query t := (runHist gen (t + 1)).q (Fin.last t)
  answer t := (runHist gen (t + 1)).a (Fin.last t)
  output t := (runHist gen (t + 1)).y (Fin.last t)

noncomputable def adversarialTarget (gen : FeedbackGenerator) : Language :=
  core ∪ Set.range (adversarialTranscript gen).presentation

noncomputable def adversarialPresenter (gen : FeedbackGenerator) : CausalPresenter where
  next t x q a y := choosePresentation ⟨x, q, a, y⟩
lemma runHist_x_old (gen : FeedbackGenerator) {t : ℕ} (i : Fin t) :
    (runHist gen (t + 1)).x i.castSucc = (runHist gen t).x i := by
  simp [runHist, extendHist]

lemma runHist_q_old (gen : FeedbackGenerator) {t : ℕ} (i : Fin t) :
    (runHist gen (t + 1)).q i.castSucc = (runHist gen t).q i := by
  simp [runHist, extendHist]

lemma runHist_a_old (gen : FeedbackGenerator) {t : ℕ} (i : Fin t) :
    (runHist gen (t + 1)).a i.castSucc = (runHist gen t).a i := by
  simp [runHist, extendHist]

lemma runHist_y_old (gen : FeedbackGenerator) {t : ℕ} (i : Fin t) :
    (runHist gen (t + 1)).y i.castSucc = (runHist gen t).y i := by
  simp [runHist, extendHist]

lemma transcript_x_new (gen : FeedbackGenerator) (t : ℕ) :
    (adversarialTranscript gen).presentation t = choosePresentation (runHist gen t) := by
  simp [adversarialTranscript, runHist, extendHist]

lemma transcript_x_prefix (gen : FeedbackGenerator) (t : ℕ) :
    (fun i : Fin t => (adversarialTranscript gen).presentation i) = (runHist gen t).x := by
  funext i
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [transcript_x_new]
        simp [runHist, extendHist]
      · simpa [runHist_x_old] using ih j

lemma transcript_q_prefix (gen : FeedbackGenerator) (t : ℕ) :
    (fun i : Fin t => (adversarialTranscript gen).query i) = (runHist gen t).q := by
  funext i
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [adversarialTranscript, runHist, extendHist]
      · simpa [runHist_q_old] using ih j

lemma transcript_a_prefix (gen : FeedbackGenerator) (t : ℕ) :
    (fun i : Fin t => (adversarialTranscript gen).answer i) = (runHist gen t).a := by
  funext i
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [adversarialTranscript, runHist, extendHist]
      · simpa [runHist_a_old] using ih j

lemma transcript_y_prefix (gen : FeedbackGenerator) (t : ℕ) :
    (fun i : Fin t => (adversarialTranscript gen).output i) = (runHist gen t).y := by
  funext i
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [adversarialTranscript, runHist, extendHist]
      · simpa [runHist_y_old] using ih j

lemma adversarial_presented (gen : FeedbackGenerator) :
    PresentedBy (adversarialPresenter gen) (adversarialTranscript gen) := by
  intro t
  rw [transcript_x_new]
  simp only [adversarialPresenter]
  rw [transcript_x_prefix, transcript_q_prefix, transcript_a_prefix, transcript_y_prefix]

lemma target_mem_class (gen : FeedbackGenerator) : adversarialTarget gen ∈ targetClass := by
  refine ⟨Set.range (adversarialTranscript gen).presentation \ core, Set.diff_subset_compl _ _, ?_⟩
  ext z
  simp [adversarialTarget]

lemma adversarial_clean (gen : FeedbackGenerator) :
    Clean (adversarialTranscript gen).presentation (adversarialTarget gen) := by
  intro t
  exact Or.inr ⟨t, rfl⟩

lemma adversarial_complete (gen : FeedbackGenerator) :
    Complete (adversarialTranscript gen).presentation (adversarialTarget gen) := by
  intro z hz
  rcases hz with hz | ⟨t, rfl⟩
  · rcases hz with ⟨k, rfl⟩
    refine ⟨2 * k, ?_⟩
    rw [transcript_x_new]
    simp [choosePresentation]
  · exact ⟨t, rfl⟩

lemma past_presentation_mem_forbidden (gen : FeedbackGenerator) {s t : ℕ} (hst : s < t) :
    (adversarialTranscript gen).presentation s ∈ forbidden (runHist gen t) := by
  classical
  unfold forbidden
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  refine Finset.mem_image.mpr ⟨(⟨s, hst⟩ : Fin t), Finset.mem_univ _, ?_⟩
  exact (congrFun (transcript_x_prefix gen t) ⟨s, hst⟩).symm

lemma presentation_odd_ordinary (gen : FeedbackGenerator) {t : ℕ} (ht : t % 2 ≠ 0) :
    (adversarialTranscript gen).presentation t ∈ ordinary := by
  rw [transcript_x_new]
  simp [choosePresentation, ht, (chooseOrdinary_spec (runHist gen t)).1]

lemma presentation_odd_avoids_past (gen : FeedbackGenerator) {s t : ℕ}
    (hst : s < t) (ht : t % 2 ≠ 0) :
    (adversarialTranscript gen).presentation s ≠
      (adversarialTranscript gen).presentation t := by
  intro h
  have hmem := past_presentation_mem_forbidden gen hst
  have htval : (adversarialTranscript gen).presentation t = chooseOrdinary (runHist gen t) := by
    rw [transcript_x_new]
    simp [choosePresentation, ht]
  rw [h, htval] at hmem
  exact (chooseOrdinary_spec (runHist gen t)).2 hmem

lemma adversarial_injective (gen : FeedbackGenerator) :
    Function.Injective (adversarialTranscript gen).presentation := by
  have hneq : ∀ {s t : ℕ}, s < t →
      (adversarialTranscript gen).presentation s ≠
        (adversarialTranscript gen).presentation t := by
    intro s t hst
    by_cases ht : t % 2 = 0
    · by_cases hs : s % 2 = 0
      · intro h
        rw [transcript_x_new, transcript_x_new] at h
        simp [choosePresentation, hs, ht] at h
        omega
      · intro h
        have hsord := presentation_odd_ordinary gen hs
        apply hsord
        rw [h, transcript_x_new]
        simp [choosePresentation, ht]
        exact ⟨t / 2, rfl⟩
    · exact presentation_odd_avoids_past gen hst ht
  intro s t h
  rcases lt_trichotomy s t with hst | hst | hts
  · exact False.elim (hneq hst h)
  · exact hst
  · exact False.elim (hneq hts h.symm)
lemma past_query_mem_forbidden (gen : FeedbackGenerator) {s t z : ℕ} (hst : s < t)
    (hq : (adversarialTranscript gen).query s = some z) :
    z ∈ forbidden (runHist gen t) := by
  classical
  unfold forbidden
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  refine Finset.mem_image.mpr ⟨(⟨s, hst⟩ : Fin t), Finset.mem_univ _, ?_⟩
  have hp := congrFun (transcript_q_prefix gen t) ⟨s, hst⟩
  rw [← hp, hq]

  simp
lemma past_output_mem_forbidden (gen : FeedbackGenerator) {s t : ℕ} (hst : s < t) :
    (adversarialTranscript gen).output s ∈ forbidden (runHist gen t) := by
  classical
  unfold forbidden
  apply Finset.mem_union_right
  refine Finset.mem_image.mpr ⟨(⟨s, hst⟩ : Fin t), Finset.mem_univ _, ?_⟩
  exact (congrFun (transcript_y_prefix gen t) ⟨s, hst⟩).symm

lemma unseen_ordinary_query_ne_future (gen : FeedbackGenerator) {t u z : ℕ}
    (htu : t < u) (hq : (adversarialTranscript gen).query t = some z)
    (hzord : z ∈ ordinary) :
    (adversarialTranscript gen).presentation u ≠ z := by
  by_cases hu : u % 2 = 0
  · intro h
    exact hzord (by rw [← h, transcript_x_new]; simp [choosePresentation, hu]; exact ⟨u / 2, rfl⟩)
  · intro h
    have hm := past_query_mem_forbidden gen htu hq
    have huval : (adversarialTranscript gen).presentation u = chooseOrdinary (runHist gen u) := by
      rw [transcript_x_new]
      simp [choosePresentation, hu]
    rw [huval] at h
    rw [← h] at hm
    exact (chooseOrdinary_spec (runHist gen u)).2 hm

lemma unseen_ordinary_output_ne_future (gen : FeedbackGenerator) {t u : ℕ}
    (htu : t < u)
    (hzord : (adversarialTranscript gen).output t ∈ ordinary) :
    (adversarialTranscript gen).presentation u ≠ (adversarialTranscript gen).output t := by
  by_cases hu : u % 2 = 0
  · intro h
    exact hzord (by rw [← h, transcript_x_new]; simp [choosePresentation, hu]; exact ⟨u / 2, rfl⟩)
  · intro h
    have hm := past_output_mem_forbidden gen htu
    have huval : (adversarialTranscript gen).presentation u = chooseOrdinary (runHist gen u) := by
      rw [transcript_x_new]
      simp [choosePresentation, hu]
    have heq : chooseOrdinary (runHist gen u) = (adversarialTranscript gen).output t := huval.symm.trans h
    have hm' : chooseOrdinary (runHist gen u) ∈ forbidden (runHist gen u) := heq.symm ▸ hm
    exact (chooseOrdinary_spec (runHist gen u)).2 hm'

lemma query_mem_target_iff_current (gen : FeedbackGenerator) (t z : ℕ)
    (hq : (adversarialTranscript gen).query t = some z) :
    z ∈ adversarialTarget gen ↔
      z ∈ core ∪ Set.range (fun i : Fin (t + 1) =>
        (adversarialTranscript gen).presentation i) := by
  constructor
  · intro hz
    rcases hz with hzcore | ⟨u, hu⟩
    · exact Or.inl hzcore
    · by_cases hut : u ≤ t
      · exact Or.inr ⟨⟨u, Nat.lt_succ_iff.mpr hut⟩, hu⟩
      · have htu : t < u := Nat.lt_of_not_ge hut
        by_cases hzcore : z ∈ core
        · exact Or.inl hzcore
        · have hzord : z ∈ ordinary := hzcore
          exact False.elim ((unseen_ordinary_query_ne_future gen htu hq hzord) hu)
  · intro hz
    rcases hz with hzcore | ⟨i, hi⟩
    · exact Or.inl hzcore
    · exact Or.inr ⟨i, hi⟩

lemma transcript_q_new (gen : FeedbackGenerator) (t : ℕ) :
    (adversarialTranscript gen).query t =
      gen.query t (fun i => (adversarialTranscript gen).presentation i)
        (fun i => (adversarialTranscript gen).answer i) := by
  rw [transcript_x_prefix gen (t + 1), transcript_a_prefix gen t]
  simp [adversarialTranscript, runHist, extendHist]

lemma transcript_a_new (gen : FeedbackGenerator) (t : ℕ) :
    (adversarialTranscript gen).answer t =
      match (adversarialTranscript gen).query t with
      | none => none
      | some z => some (membershipAnswer
          (core ∪ Set.range (fun i : Fin (t + 1) =>
            (adversarialTranscript gen).presentation i)) z) := by
  rw [transcript_x_prefix gen (t + 1)]
  simp [adversarialTranscript, runHist, extendHist]

lemma transcript_y_new (gen : FeedbackGenerator) (t : ℕ) :
    (adversarialTranscript gen).output t =
      gen.output t (fun i => (adversarialTranscript gen).presentation i)
        (fun i => (adversarialTranscript gen).answer i) := by
  rw [transcript_x_prefix gen (t + 1), transcript_a_prefix gen (t + 1)]
  simp [adversarialTranscript, runHist, extendHist]

lemma adversarial_protocol (gen : FeedbackGenerator) :
    FollowsProtocol gen (adversarialTarget gen) (adversarialTranscript gen) := by
  intro t
  refine ⟨transcript_q_new gen t, ?_, transcript_y_new gen t⟩
  rw [transcript_a_new]
  cases hq : (adversarialTranscript gen).query t with
  | none => rfl
  | some z =>
      simp only
      congr 1
      unfold membershipAnswer
      rw [propext (query_mem_target_iff_current gen t z hq)]
lemma forbidden_card_le {t : ℕ} (h : Hist t) : (forbidden h).card ≤ 3 * t := by
  unfold forbidden
  calc
    ((Finset.univ.image h.x ∪ Finset.univ.image fun i => (h.q i).getD 0) ∪
      Finset.univ.image h.y).card
        ≤ (Finset.univ.image h.x ∪ Finset.univ.image fun i => (h.q i).getD 0).card +
          (Finset.univ.image h.y).card := Finset.card_union_le _ _
    _ ≤ ((Finset.univ.image h.x).card +
          (Finset.univ.image fun i => (h.q i).getD 0).card) +
          (Finset.univ.image h.y).card := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ (t + t) + t := by
      gcongr <;> simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin t))))
    _ = 3 * t := by omega

lemma chooseOrdinary_le {t : ℕ} (h : Hist t) : chooseOrdinary h ≤ 6 * t + 3 := by
  classical
  let codes := (Finset.range (3 * t + 1)).image (fun n => 2 * n + 3)
  have hcard : codes.card = 3 * t + 1 := by
    simp [codes, Finset.card_image_of_injective _ oddCode_injective]
  have hlt : (forbidden h).card < codes.card := by
    rw [hcard]
    exact lt_of_le_of_lt (forbidden_card_le h) (Nat.lt_succ_self (3 * t))
  obtain ⟨z, hzcodes, hznot⟩ := Finset.exists_mem_not_mem_of_card_lt_card hlt
  rcases Finset.mem_image.mp hzcodes with ⟨j, hj, rfl⟩
  have hjlt : j < 3 * t + 1 := Finset.mem_range.mp hj
  have hfind := Nat.find_min' (ordinary_infinite.exists_not_mem_finset (forbidden h))
    (show 2 * j + 3 ∈ ordinary ∧ 2 * j + 3 ∉ forbidden h from ⟨oddCode_mem_ordinary j, hznot⟩)
  change chooseOrdinary h ≤ 2 * j + 3 at hfind
  omega


theorem adversarial_legal (gen : FeedbackGenerator) :
    adversarialTarget gen ∈ targetClass ∧
    PresentedBy (adversarialPresenter gen) (adversarialTranscript gen) ∧
    FollowsProtocol gen (adversarialTarget gen) (adversarialTranscript gen) ∧
    Clean (adversarialTranscript gen).presentation (adversarialTarget gen) ∧
    Function.Injective (adversarialTranscript gen).presentation ∧
    Complete (adversarialTranscript gen).presentation (adversarialTarget gen) := by
  exact ⟨target_mem_class gen, adversarial_presented gen, adversarial_protocol gen,
    adversarial_clean gen, adversarial_injective gen, adversarial_complete gen⟩


lemma adversarialTarget_infinite (gen : FeedbackGenerator) : (adversarialTarget gen).Infinite := by
  apply (Set.infinite_range_of_injective (Nat.pow_right_injective (by omega : 1 < 2))).mono
  intro z hz
  exact Or.inl hz

noncomputable def orderedTarget (gen : FeedbackGenerator) : OrderedLanguage where
  carrier := adversarialTarget gen
  enumeration := Nat.nth (fun z => z ∈ adversarialTarget gen)
  enumeration_injective := (Nat.nth_strictMono (adversarialTarget_infinite gen)).injective
  range_enumeration := Nat.range_nth_of_infinite (adversarialTarget_infinite gen)

lemma orderedTarget_ambient (gen : FeedbackGenerator) : InheritsAmbientOrder (orderedTarget gen) :=
  Nat.nth_strictMono (adversarialTarget_infinite gen)

lemma odd_presentation_bound (gen : FeedbackGenerator) (j : ℕ) :
    (adversarialTranscript gen).presentation (2 * j + 1) ≤ 12 * j + 9 := by
  rw [transcript_x_new]
  have hodd : (2 * j + 1) % 2 ≠ 0 := by omega
  simp [choosePresentation, hodd]
  have h := chooseOrdinary_le (runHist gen (2 * j + 1))
  omega

noncomputable def targetCount (gen : FeedbackGenerator) (B : ℕ) : ℕ := by
  classical
  exact Nat.count (fun z => z ∈ adversarialTarget gen) B

lemma target_count_lower (gen : FeedbackGenerator) (n : ℕ) :
    n + 1 ≤ targetCount gen (12 * n + 10) := by
  classical
  let values := (Finset.range (n + 1)).image
    (fun j => (adversarialTranscript gen).presentation (2 * j + 1))
  have hcard : values.card = n + 1 := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro a b hab
      have := adversarial_injective gen hab
      omega
  unfold targetCount
  rw [Nat.count_eq_card_filter_range, ← hcard]
  apply Finset.card_le_card
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨j, hj, rfl⟩
  have hjle : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact lt_of_le_of_lt (odd_presentation_bound gen j) (by omega)
  · exact Or.inr ⟨2 * j + 1, rfl⟩

lemma orderedTarget_bound (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).enumeration n < 12 * n + 10 := by
  classical
  apply Nat.nth_lt_of_lt_count
  exact target_count_lower gen n

noncomputable def coreBelow (B : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range B).filter fun z => z ∈ core

lemma powers_below_card_le (B : ℕ) : (coreBelow B).card ≤ Nat.log2 B + 1 := by
  classical
  let powers := (Finset.range (Nat.log2 B + 1)).image (fun k => 2 ^ k)
  calc
    (coreBelow B).card ≤ powers.card := by
      apply Finset.card_le_card
      intro z hz
      simp only [coreBelow, Finset.mem_filter, Finset.mem_range] at hz
      rcases hz.2 with ⟨k, rfl⟩
      apply Finset.mem_image.mpr
      refine ⟨k, Finset.mem_range.mpr ?_, rfl⟩
      have hk : k ≤ Nat.log 2 B := Nat.le_log_of_pow_le (by omega) (Nat.le_of_lt hz.1)
      simpa [Nat.log2_eq_log_two] using Nat.lt_succ_of_le hk
    _ ≤ Nat.log2 B + 1 := by
      exact (Finset.card_image_le (s := Finset.range (Nat.log2 B + 1))).trans_eq (by simp)

lemma core_prefixCount_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).prefixCount core n ≤ Nat.log2 (12 * n + 10) + 1 := by
  classical
  let indices := (Finset.range n).filter fun i => (orderedTarget gen).enumeration i ∈ core
  let vals := indices.image (orderedTarget gen).enumeration
  have hcard : vals.card = (orderedTarget gen).prefixCount core n := by
    rw [Finset.card_image_of_injective]
    · rfl
    · exact (orderedTarget gen).enumeration_injective
  rw [← hcard]
  calc
    vals.card ≤ (coreBelow (12 * n + 10)).card := by
      apply Finset.card_le_card
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
      change i ∈ indices at hi
      simp only [indices, Finset.mem_filter, Finset.mem_range] at hi
      simp only [coreBelow, Finset.mem_filter, Finset.mem_range]
      exact ⟨(orderedTarget_bound gen i).trans_le (by omega), hi.2⟩
    _ ≤ Nat.log2 (12 * n + 10) + 1 := powers_below_card_le _

lemma tendsto_core_bound :
    Filter.Tendsto
      (fun n : ℕ => ((Nat.log2 (12 * n + 10) + 1 : ℕ) : ℝ) / (n : ℝ))
      Filter.atTop (nhds 0) := by
  have hm : Filter.Tendsto (fun n : ℕ => 12 * n + 10) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 (fun b => ?_)
    filter_upwards [Filter.eventually_ge_atTop b] with a ha
    omega
  have hlog := GenLimit.tendsto_natLog2_div.comp hm
  have hc : Filter.Tendsto (fun n : ℕ => (10 : ℝ) / (n : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlin : Filter.Tendsto
      (fun n : ℕ => ((12 * n + 10 : ℕ) : ℝ) / (n : ℝ)) Filter.atTop (nhds 12) := by
    have hbase := (tendsto_const_nhds (x := (12 : ℝ))).add hc
    have heq : (fun n : ℕ => (12 : ℝ) + 10 / (n : ℝ)) =ᶠ[Filter.atTop]
        (fun n : ℕ => ((12 * n + 10 : ℕ) : ℝ) / (n : ℝ)) := by
      filter_upwards [Filter.eventually_ne_atTop 0] with n hn
      push_cast
      rw [add_div]
      simp [hn]
    simpa using hbase.congr' heq
  have hprod := hlog.mul hlin
  have hmain : Filter.Tendsto
      (fun n : ℕ => (Nat.log2 (12 * n + 10) : ℝ) / (n : ℝ)) Filter.atTop (nhds 0) := by
    have heq :
        (fun n : ℕ => ((Nat.log2 (12 * n + 10) : ℝ) / (12 * n + 10 : ℕ)) *
          (((12 * n + 10 : ℕ) : ℝ) / (n : ℝ))) =ᶠ[Filter.atTop]
        (fun n : ℕ => (Nat.log2 (12 * n + 10) : ℝ) / (n : ℝ)) := by
      filter_upwards with n
      push_cast
      have hm0 : (12 * (n : ℝ) + 10) ≠ 0 := by positivity
      field_simp
    simpa only [Function.comp_apply, zero_mul] using hprod.congr' heq
  have hone : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hadd := hmain.add hone
  convert hadd using 1
  · funext n
    push_cast
    rw [add_div]
  · norm_num

lemma orderedTarget_core_density_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity core = 0 := by
  have htendsto : Filter.Tendsto ((orderedTarget gen).prefixRatio core)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero
      (fun n => (orderedTarget gen).prefixRatio_nonneg core n) _ tendsto_core_bound
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · simp only [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, hn, if_false]
      exact div_le_div_of_nonneg_right
        (by exact_mod_cast core_prefixCount_le gen n) (Nat.cast_nonneg n)
  exact htendsto.limsup_eq
lemma eventual_output_core (gen : FeedbackGenerator)
    (hvalid : UniversallyEventuallyValidFresh gen) :
    ∃ T : ℕ, ∀ t, T ≤ t → (adversarialTranscript gen).output t ∈ core := by
  obtain ⟨T, hT⟩ := hvalid (adversarialTarget gen) (target_mem_class gen)
    (adversarialTranscript gen) (adversarial_protocol gen) (adversarial_clean gen)
    (adversarial_injective gen) (adversarial_complete gen)
  refine ⟨T, fun t ht => ?_⟩
  obtain ⟨hyTarget, hyFresh⟩ := hT t ht
  by_contra hyCore
  have hyOrd : (adversarialTranscript gen).output t ∈ ordinary := hyCore
  rcases hyTarget with hyTarget | ⟨u, hu⟩
  · exact hyCore hyTarget
  · have htu : t < u := by
      by_contra hnot
      have hut : u ≤ t := Nat.le_of_not_gt hnot
      apply hyFresh
      exact ⟨u, hut, hu⟩
    exact (unseen_ordinary_output_ne_future gen htu hyOrd) hu

lemma scored_subset_core_union_initial (gen : FeedbackGenerator)
    (hvalid : UniversallyEventuallyValidFresh gen) :
    ∃ T : ℕ, scored (adversarialTarget gen) (adversarialTranscript gen).presentation
        (adversarialTranscript gen).output ⊆
      core ∪ Set.range (fun i : Fin T => (adversarialTranscript gen).output i) := by
  obtain ⟨T, hT⟩ := eventual_output_core gen hvalid
  refine ⟨T, ?_⟩
  intro z hz
  rcases hz with ⟨-, t, rfl, -⟩
  by_cases ht : T ≤ t
  · exact Or.inl (hT t ht)
  · exact Or.inr ⟨⟨t, Nat.lt_of_not_ge ht⟩, rfl⟩

lemma scored_density_zero (gen : FeedbackGenerator)
    (hvalid : UniversallyEventuallyValidFresh gen) :
    (orderedTarget gen).upperDensity
      (scored (adversarialTarget gen) (adversarialTranscript gen).presentation
        (adversarialTranscript gen).output) = 0 := by
  obtain ⟨T, hsub⟩ := scored_subset_core_union_initial gen hvalid
  let F : Set ℕ := Set.range (fun i : Fin T => (adversarialTranscript gen).output i)
  have hF : F.Finite := Set.finite_range _
  apply le_antisymm
  · calc
      (orderedTarget gen).upperDensity
          (scored (adversarialTarget gen) (adversarialTranscript gen).presentation
            (adversarialTranscript gen).output)
          ≤ (orderedTarget gen).upperDensity (core ∪ F) :=
            (orderedTarget gen).upperDensity_mono hsub
      _ ≤ (orderedTarget gen).upperDensity core + (orderedTarget gen).upperDensity F :=
        (orderedTarget gen).upperDensity_union_le core F
      _ = 0 := by
        rw [orderedTarget_core_density_zero,
          (orderedTarget gen).upperDensity_eq_zero_of_finite hF, add_zero]
  · exact (orderedTarget gen).upperDensity_nonneg _

lemma negative_claim : NegativeClaim := by
  intro gen hvalid
  refine ⟨adversarialTarget gen, target_mem_class gen, adversarialPresenter gen,
    adversarialTranscript gen, orderedTarget gen, ?_⟩
  exact ⟨rfl, orderedTarget_ambient gen, adversarial_presented gen,
    adversarial_protocol gen, adversarial_clean gen, adversarial_injective gen,
    adversarial_complete gen, scored_density_zero gen hvalid⟩

end Stage3Work

theorem stage3_result : Stage3S2B.MainClaim := by
  exact ⟨Stage3Work.targetClass_not_countable, Stage3Work.uniform_generation,
    Stage3Work.negative_claim⟩
