import Stage3Model
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Sqrt
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import Mathlib.Analysis.SpecificLimits.Basic

namespace Stage3Work

open Stage3S2B

lemma oddCode_mem_ordinary (n : ℕ) : 2 * n + 3 ∈ ordinary := by
  intro h
  obtain ⟨k, hk⟩ := h
  have hodd : Odd (2 * n + 3) := ⟨n + 1, by omega⟩
  have hpowodd : Odd (2 ^ k) := by simpa [hk] using hodd
  have hk0 : k = 0 := by
    by_contra hk0
    have heven : Even (2 ^ k) :=
      Nat.even_pow.mpr ⟨by norm_num, hk0⟩
    exact (Nat.not_even_iff_odd.mpr hpowodd) heven
  subst k
  norm_num at hk

lemma oddCode_injective : Function.Injective (fun n : ℕ => 2 * n + 3) := by
  intro m n h
  change 2 * m + 3 = 2 * n + 3 at h
  have hmul : 2 * m = 2 * n := by omega
  exact Nat.eq_of_mul_eq_mul_left (by omega) hmul

def encodeTarget (S : Set ℕ) : Language :=
  core ∪ (fun n : ℕ => 2 * n + 3) '' S

lemma encodeTarget_mem (S : Set ℕ) : encodeTarget S ∈ targetClass := by
  refine ⟨(fun n : ℕ => 2 * n + 3) '' S, ?_, rfl⟩
  rintro _ ⟨n, _hn, rfl⟩
  exact oddCode_mem_ordinary n

lemma encodeTarget_injective : Function.Injective encodeTarget := by
  intro S T hST
  ext n
  have hmem := Set.ext_iff.mp hST (2 * n + 3)
  simp only [encodeTarget, Set.mem_union, Set.mem_image] at hmem
  have hncore : 2 * n + 3 ∉ core := oddCode_mem_ordinary n
  have himage (U : Set ℕ) :
      (∃ a, a ∈ U ∧ 2 * a + 3 = 2 * n + 3) ↔ n ∈ U := by
    constructor
    · rintro ⟨a, ha, hcode⟩
      have : a = n := oddCode_injective hcode
      simpa [this] using ha
    · intro hn
      exact ⟨n, hn, rfl⟩
  simpa [hncore, himage] using hmem

lemma targetClass_uncountable : ¬ targetClass.Countable := by
  intro hcountable
  let f : Set ℕ → targetClass :=
    fun S => ⟨encodeTarget S, encodeTarget_mem S⟩
  have hf : Function.Injective f := by
    intro S T h
    apply encodeTarget_injective
    exact congrArg Subtype.val h
  letI : Countable targetClass := hcountable.to_subtype
  have hpower : Countable (Set ℕ) := hf.countable
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ hpower

lemma powTwo_injective : Function.Injective (fun k : ℕ => 2 ^ k) := by
  exact Nat.pow_right_injective (by omega)

lemma uniform_generation : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun k => 2 ^ k, powTwo_injective, 0, ?_⟩
  intro K hK t _ht
  obtain ⟨A, hA, rfl⟩ := hK
  exact Set.mem_union_left _ ⟨t, rfl⟩

end Stage3Work

namespace Stage3Work

noncomputable def unavailable (t : ℕ) (x : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) : Finset ℕ :=
  Finset.univ.image x ∪
    Finset.univ.image (fun i => (q i).getD 0) ∪
      Finset.univ.image y

def candidate (j : ℕ) : ℕ := 2 * j + 3

lemma candidate_injective : Function.Injective candidate := by
  intro m n h
  change 2 * m + 3 = 2 * n + 3 at h
  have hmul : 2 * m = 2 * n := by omega
  exact Nat.eq_of_mul_eq_mul_left (by omega) hmul

lemma card_unavailable_le (t : ℕ) (x : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) :
    (unavailable t x q y).card ≤ 3 * t := by
  classical
  unfold unavailable
  calc
    ((Finset.univ.image x ∪
        Finset.univ.image (fun i => (q i).getD 0)) ∪
        Finset.univ.image y).card ≤
      (Finset.univ.image x ∪
        Finset.univ.image (fun i => (q i).getD 0)).card +
        (Finset.univ.image y).card := Finset.card_union_le _ _
    _ ≤ ((Finset.univ.image x).card +
        (Finset.univ.image (fun i => (q i).getD 0)).card) +
        (Finset.univ.image y).card :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ (Finset.univ : Finset (Fin t)).card +
          (Finset.univ : Finset (Fin t)).card +
          (Finset.univ : Finset (Fin t)).card := by
      gcongr <;> exact Finset.card_image_le
    _ = 3 * t := by simp [Finset.card_fin]; omega

lemma exists_safe_candidate (t : ℕ) (x : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) :
    ∃ j, j < 4 * t + 1 ∧ candidate j ∉ unavailable t x q y := by
  classical
  let candidates := (Finset.range (4 * t + 1)).image candidate
  have hcand : candidates.card = 4 * t + 1 := by
    simp [candidates, Finset.card_image_of_injective _ candidate_injective]
  have hlt : (unavailable t x q y).card < candidates.card := by
    rw [hcand]
    exact (card_unavailable_le t x q y).trans_lt (by omega)
  obtain ⟨z, hzCand, hzNot⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hlt
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hzCand
  exact ⟨j, Finset.mem_range.mp hj, hzNot⟩

noncomputable def safeIndex (t : ℕ) (x : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) : ℕ :=
  Nat.find (exists_safe_candidate t x q y)

noncomputable def safeOrdinary (t : ℕ) (x : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) : ℕ :=
  candidate (safeIndex t x q y)

lemma safeIndex_spec (t : ℕ) (x : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) :
    safeIndex t x q y < 4 * t + 1 ∧
      safeOrdinary t x q y ∉ unavailable t x q y := by
  exact Nat.find_spec (exists_safe_candidate t x q y)

lemma safeOrdinary_le (t : ℕ) (x : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) :
    safeOrdinary t x q y ≤ 8 * t + 3 := by
  unfold safeOrdinary candidate
  have h := (safeIndex_spec t x q y).1
  omega

lemma safeOrdinary_mem_ordinary (t : ℕ) (x : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) :
    safeOrdinary t x q y ∈ Stage3S2B.ordinary := by
  change safeOrdinary t x q y ∉ Stage3S2B.core
  exact oddCode_mem_ordinary (safeIndex t x q y)

lemma safeOrdinary_ne_x (t : ℕ) (x : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) (i : Fin t) :
    safeOrdinary t x q y ≠ x i := by
  intro h
  apply (safeIndex_spec t x q y).2
  unfold unavailable
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inl (Or.inl ⟨i, h.symm⟩)

lemma safeOrdinary_ne_q (t : ℕ) (x : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) (i : Fin t) {z : ℕ}
    (hi : q i = some z) : safeOrdinary t x q y ≠ z := by
  intro h
  apply (safeIndex_spec t x q y).2
  unfold unavailable
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inl (Or.inr ⟨i, by simp [hi, h]⟩)

lemma safeOrdinary_ne_y (t : ℕ) (x : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) (i : Fin t) :
    safeOrdinary t x q y ≠ y i := by
  intro h
  apply (safeIndex_spec t x q y).2
  unfold unavailable
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inr ⟨i, h.symm⟩

end Stage3Work

namespace Stage3Work

open Stage3S2B

 noncomputable def boolOfProp (P : Prop) : Bool := by
  classical
  exact if P then true else false

structure History (t : ℕ) where
  presentation : Fin t → ℕ
  query : Fin t → Option ℕ
  answer : Fin t → Option Bool
  output : Fin t → ℕ

noncomputable def nextPresentation (t : ℕ) (h : History t) : ℕ :=
  if Even t then 2 ^ (t / 2)
  else safeOrdinary t h.presentation h.query h.output

noncomputable def stepHistory (gen : FeedbackGenerator) (t : ℕ)
    (h : History t) : History (t + 1) := by
  classical
  let xt := nextPresentation t h
  let xnext : Fin (t + 1) → ℕ := Fin.lastCases xt h.presentation
  let qt := gen.query t xnext h.answer
  let qnext : Fin (t + 1) → Option ℕ := Fin.lastCases qt h.query
  let ansT := match qt with
    | none => none
    | some z => some (boolOfProp (z ∈ core ∨ ∃ i, xnext i = z))
  let anext : Fin (t + 1) → Option Bool := Fin.lastCases ansT h.answer
  let yt := gen.output t xnext anext
  let ynext : Fin (t + 1) → ℕ := Fin.lastCases yt h.output
  exact ⟨xnext, qnext, anext, ynext⟩

noncomputable def history (gen : FeedbackGenerator) :
    (t : ℕ) → History t
  | 0 => ⟨Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0⟩
  | t + 1 => stepHistory gen t (history gen t)

noncomputable def adversarialTranscript (gen : FeedbackGenerator) : Transcript where
  presentation t := (history gen (t + 1)).presentation (Fin.last t)
  query t := (history gen (t + 1)).query (Fin.last t)
  answer t := (history gen (t + 1)).answer (Fin.last t)
  output t := (history gen (t + 1)).output (Fin.last t)

@[simp] lemma history_succ_presentation_castSucc (gen : FeedbackGenerator)
    (t : ℕ) (i : Fin t) :
    (history gen (t + 1)).presentation i.castSucc =
      (history gen t).presentation i := by
  simp [history, stepHistory]

@[simp] lemma history_succ_query_castSucc (gen : FeedbackGenerator)
    (t : ℕ) (i : Fin t) :
    (history gen (t + 1)).query i.castSucc =
      (history gen t).query i := by
  simp [history, stepHistory]

@[simp] lemma history_succ_answer_castSucc (gen : FeedbackGenerator)
    (t : ℕ) (i : Fin t) :
    (history gen (t + 1)).answer i.castSucc =
      (history gen t).answer i := by
  simp [history, stepHistory]

@[simp] lemma history_succ_output_castSucc (gen : FeedbackGenerator)
    (t : ℕ) (i : Fin t) :
    (history gen (t + 1)).output i.castSucc =
      (history gen t).output i := by
  simp [history, stepHistory]

lemma history_agrees (gen : FeedbackGenerator) (t : ℕ) :
    (∀ i : Fin t, (history gen t).presentation i =
      (adversarialTranscript gen).presentation i.1) ∧
    (∀ i : Fin t, (history gen t).query i =
      (adversarialTranscript gen).query i.1) ∧
    (∀ i : Fin t, (history gen t).answer i =
      (adversarialTranscript gen).answer i.1) ∧
    (∀ i : Fin t, (history gen t).output i =
      (adversarialTranscript gen).output i.1) := by
  induction t with
  | zero => simp
  | succ t ih =>
      constructor
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · rfl
        · simpa using ih.1 j
      constructor
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · rfl
        · simpa using ih.2.1 j
      constructor
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · rfl
        · simpa using ih.2.2.1 j
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · rfl
        · simpa using ih.2.2.2 j

lemma history_presentation_eq (gen : FeedbackGenerator) (t : ℕ) :
    (history gen (t + 1)).presentation =
      fun i => (adversarialTranscript gen).presentation i.1 := by
  funext i
  exact (history_agrees gen (t + 1)).1 i

lemma history_answer_eq (gen : FeedbackGenerator) (t : ℕ) :
    (history gen t).answer =
      fun i => (adversarialTranscript gen).answer i.1 := by
  funext i
  exact (history_agrees gen t).2.2.1 i

end Stage3Work

namespace Stage3Work

open Stage3S2B

lemma transcript_presentation_eq (gen : FeedbackGenerator) (t : ℕ) :
    (adversarialTranscript gen).presentation t =
      nextPresentation t (history gen t) := by
  simp [adversarialTranscript, history, stepHistory]

lemma transcript_presentation_even (gen : FeedbackGenerator) (s : ℕ) :
    (adversarialTranscript gen).presentation (2 * s) = 2 ^ s := by
  rw [transcript_presentation_eq]
  simp [nextPresentation]

lemma transcript_presentation_odd (gen : FeedbackGenerator) (s : ℕ) :
    (adversarialTranscript gen).presentation (2 * s + 1) =
      safeOrdinary (2 * s + 1)
        (history gen (2 * s + 1)).presentation
        (history gen (2 * s + 1)).query
        (history gen (2 * s + 1)).output := by
  rw [transcript_presentation_eq]
  simp [nextPresentation]

lemma transcript_query_eq (gen : FeedbackGenerator) (t : ℕ) :
    (adversarialTranscript gen).query t =
      gen.query t
        (fun i => (adversarialTranscript gen).presentation i.1)
        (fun i => (adversarialTranscript gen).answer i.1) := by
  change (stepHistory gen t (history gen t)).query (Fin.last t) = _
  simp only [stepHistory, Fin.lastCases_last]
  congr 1
  · funext i
    simpa [history] using (history_agrees gen (t + 1)).1 i
  · funext i
    exact (history_agrees gen t).2.2.1 i

lemma transcript_answer_eq (gen : FeedbackGenerator) (t : ℕ) :
    (adversarialTranscript gen).answer t =
      match (adversarialTranscript gen).query t with
      | none => none
      | some z => some (boolOfProp
          (z ∈ core ∨ ∃ i : Fin (t + 1),
            (adversarialTranscript gen).presentation i.1 = z)) := by
  change (stepHistory gen t (history gen t)).answer (Fin.last t) = _
  simp only [stepHistory, Fin.lastCases_last]
  rw [transcript_query_eq]
  have hx :
      (fun i => Fin.lastCases (nextPresentation t (history gen t))
        (history gen t).presentation i) =
      (fun i => (adversarialTranscript gen).presentation i.1) := by
    funext i
    simpa [history] using (history_agrees gen (t + 1)).1 i
  have ha : (history gen t).answer =
      (fun i => (adversarialTranscript gen).answer i.1) := by
    funext i
    exact (history_agrees gen t).2.2.1 i
  rw [hx, ha]
  cases hq : gen.query t
      (fun i => (adversarialTranscript gen).presentation i.1)
      (fun i => (adversarialTranscript gen).answer i.1) with
  | none => simp [hq]
  | some z =>
    simp only [hq]
    congr 2
    apply propext
    constructor
    · rintro (hz | ⟨i, hi⟩)
      · exact Or.inl hz
      · exact Or.inr ⟨i, by
          exact (congrFun hx i).symm.trans hi⟩
    · rintro (hz | ⟨i, hi⟩)
      · exact Or.inl hz
      · exact Or.inr ⟨i, by
          exact (congrFun hx i).trans hi⟩

lemma transcript_output_eq (gen : FeedbackGenerator) (t : ℕ) :
    (adversarialTranscript gen).output t =
      gen.output t
        (fun i => (adversarialTranscript gen).presentation i.1)
        (fun i => (adversarialTranscript gen).answer i.1) := by
  change (stepHistory gen t (history gen t)).output (Fin.last t) = _
  simp only [stepHistory, Fin.lastCases_last]
  congr 1
  · funext i
    simpa [history] using (history_agrees gen (t + 1)).1 i
  · funext i
    simpa [history] using (history_agrees gen (t + 1)).2.2.1 i

noncomputable def adversarialTarget (gen : FeedbackGenerator) : Language :=
  Set.range (adversarialTranscript gen).presentation

lemma core_subset_target (gen : FeedbackGenerator) :
    core ⊆ adversarialTarget gen := by
  rintro z ⟨s, rfl⟩
  exact ⟨2 * s, transcript_presentation_even gen s⟩

lemma odd_presentation_mem_ordinary (gen : FeedbackGenerator) (s : ℕ) :
    (adversarialTranscript gen).presentation (2 * s + 1) ∈ ordinary := by
  rw [transcript_presentation_odd]
  exact safeOrdinary_mem_ordinary _ _ _ _

lemma target_eq_core_union_oddRange (gen : FeedbackGenerator) :
    adversarialTarget gen =
      core ∪ Set.range (fun s =>
        (adversarialTranscript gen).presentation (2 * s + 1)) := by
  apply Set.Subset.antisymm
  · rintro z ⟨t, rfl⟩
    rcases Nat.even_or_odd t with ⟨s, rfl⟩ | ⟨s, rfl⟩
    · exact Set.mem_union_left _ ⟨s, by simpa [two_mul] using (transcript_presentation_even gen s).symm⟩
    · exact Set.mem_union_right _ ⟨s, rfl⟩
  · intro z hz
    rcases hz with hz | ⟨s, rfl⟩
    · exact core_subset_target gen hz
    · exact ⟨2 * s + 1, rfl⟩

lemma adversarialTarget_mem_targetClass (gen : FeedbackGenerator) :
    adversarialTarget gen ∈ targetClass := by
  refine ⟨Set.range (fun s =>
    (adversarialTranscript gen).presentation (2 * s + 1)), ?_, ?_⟩
  · rintro z ⟨s, rfl⟩
    exact odd_presentation_mem_ordinary gen s
  · exact target_eq_core_union_oddRange gen

lemma future_odd_ne_prior_query (gen : FeedbackGenerator)
    {t s z : ℕ} (hts : t < 2 * s + 1)
    (hq : (adversarialTranscript gen).query t = some z) :
    (adversarialTranscript gen).presentation (2 * s + 1) ≠ z := by
  rw [transcript_presentation_odd]
  apply safeOrdinary_ne_q
    (t := 2 * s + 1)
    (x := (history gen (2 * s + 1)).presentation)
    (q := (history gen (2 * s + 1)).query)
    (y := (history gen (2 * s + 1)).output)
    ⟨t, hts⟩
  simpa using (history_agrees gen (2 * s + 1)).2.1 ⟨t, hts⟩ ▸ hq

lemma future_odd_ne_prior_output (gen : FeedbackGenerator)
    {t s : ℕ} (hts : t < 2 * s + 1) :
    (adversarialTranscript gen).presentation (2 * s + 1) ≠
      (adversarialTranscript gen).output t := by
  rw [transcript_presentation_odd]
  intro h
  apply safeOrdinary_ne_y
    (t := 2 * s + 1)
    (x := (history gen (2 * s + 1)).presentation)
    (q := (history gen (2 * s + 1)).query)
    (y := (history gen (2 * s + 1)).output)
    ⟨t, hts⟩
  rw [(history_agrees gen (2 * s + 1)).2.2.2 ⟨t, hts⟩]
  exact h

end Stage3Work

namespace Stage3Work

open Stage3S2B

lemma target_mem_iff_query_history (gen : FeedbackGenerator)
    {t z : ℕ} (hq : (adversarialTranscript gen).query t = some z) :
    z ∈ adversarialTarget gen ↔
      z ∈ core ∨ ∃ i : Fin (t + 1),
        (adversarialTranscript gen).presentation i.1 = z := by
  constructor
  · rintro ⟨s, hs⟩
    by_cases hst : s ≤ t
    · exact Or.inr ⟨⟨s, by omega⟩, hs⟩
    · have hts : t < s := by omega
      rcases Nat.even_or_odd s with ⟨k, hk⟩ | ⟨k, hk⟩
      · subst s
        exact Or.inl ⟨k, (transcript_presentation_even gen k).symm.trans
          (by simpa [two_mul] using hs)⟩
      · subst s
        exact (future_odd_ne_prior_query gen hts hq hs).elim
  · rintro (hz | ⟨i, hi⟩)
    · exact core_subset_target gen hz
    · exact ⟨i.1, hi⟩

lemma adversarial_follows_protocol (gen : FeedbackGenerator) :
    FollowsProtocol gen (adversarialTarget gen) (adversarialTranscript gen) := by
  intro t
  refine ⟨transcript_query_eq gen t, ?_, transcript_output_eq gen t⟩
  rw [transcript_answer_eq]
  cases hq : (adversarialTranscript gen).query t with
  | none => rfl
  | some z =>
    simp only
    rw [← target_mem_iff_query_history gen hq]
    classical
    simp [membershipAnswer, boolOfProp]

noncomputable def adversarialPresenter (gen : FeedbackGenerator) : CausalPresenter where
  next t x q _a y := if Even t then 2 ^ (t / 2) else safeOrdinary t x q y

lemma adversarial_presented_by (gen : FeedbackGenerator) :
    PresentedBy (adversarialPresenter gen) (adversarialTranscript gen) := by
  intro t
  rw [transcript_presentation_eq]
  simp only [nextPresentation, adversarialPresenter]
  by_cases ht : Even t
  · simp [ht]
  · simp only [ht, ↓reduceIte]
    congr 1
    · funext i
      exact (history_agrees gen t).1 i
    · funext i
      exact (history_agrees gen t).2.1 i
    · funext i
      exact (history_agrees gen t).2.2.2 i

lemma future_odd_ne_prior_presentation (gen : FeedbackGenerator)
    {t s : ℕ} (hts : t < 2 * s + 1) :
    (adversarialTranscript gen).presentation (2 * s + 1) ≠
      (adversarialTranscript gen).presentation t := by
  rw [transcript_presentation_odd]
  intro h
  apply safeOrdinary_ne_x
    (t := 2 * s + 1)
    (x := (history gen (2 * s + 1)).presentation)
    (q := (history gen (2 * s + 1)).query)
    (y := (history gen (2 * s + 1)).output)
    ⟨t, hts⟩
  rw [(history_agrees gen (2 * s + 1)).1 ⟨t, hts⟩]
  exact h

lemma adversarial_presentation_ne_of_lt (gen : FeedbackGenerator)
    {m n : ℕ} (hmn : m < n) :
    (adversarialTranscript gen).presentation m ≠
      (adversarialTranscript gen).presentation n := by
  rcases Nat.even_or_odd n with ⟨s, hs⟩ | ⟨s, hs⟩
  · subst n
    rcases Nat.even_or_odd m with ⟨r, hr⟩ | ⟨r, hr⟩
    · subst m
      intro heq
      have hp : 2 ^ r = 2 ^ s := by
        rw [← transcript_presentation_even gen r,
          ← transcript_presentation_even gen s]
        simpa [two_mul] using heq
      have hrs : r = s := powTwo_injective hp
      omega
    · subst m
      intro heq
      have hmOrd := odd_presentation_mem_ordinary gen r
      apply hmOrd
      rw [heq]
      exact ⟨s, by simpa [two_mul] using (transcript_presentation_even gen s).symm⟩
  · subst n
    exact fun heq => future_odd_ne_prior_presentation gen hmn heq.symm

lemma adversarial_presentation_injective (gen : FeedbackGenerator) :
    Function.Injective (adversarialTranscript gen).presentation := by
  intro m n hmn
  apply le_antisymm
  · exact not_lt.mp (fun h => adversarial_presentation_ne_of_lt gen h hmn.symm)
  · exact not_lt.mp (fun h => adversarial_presentation_ne_of_lt gen h hmn)

lemma adversarial_clean (gen : FeedbackGenerator) :
    Clean (adversarialTranscript gen).presentation (adversarialTarget gen) := by
  intro t
  exact ⟨t, rfl⟩

lemma adversarial_complete (gen : FeedbackGenerator) :
    Complete (adversarialTranscript gen).presentation (adversarialTarget gen) := by
  rintro z ⟨t, ht⟩
  exact ⟨t, ht⟩

lemma scored_subset_core (gen : FeedbackGenerator) :
    scored (adversarialTarget gen)
      (adversarialTranscript gen).presentation
      (adversarialTranscript gen).output ⊆ core := by
  rintro z ⟨hzTarget, t, hyt, hzFresh⟩
  obtain ⟨s, hs⟩ := hzTarget
  have hts : t < s := by
    by_contra hnot
    apply hzFresh
    exact ⟨s, by omega, hs⟩
  rcases Nat.even_or_odd s with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst s
    exact ⟨k, (transcript_presentation_even gen k).symm.trans
      (by simpa [two_mul] using hs)⟩
  · subst s
    have hne := future_odd_ne_prior_output gen hts
    exact (hne (hs.trans hyt.symm)).elim

end Stage3Work

namespace Stage3Work

open Stage3S2B
open Filter
open scoped Topology

lemma odd_presentation_le (gen : FeedbackGenerator) (s : ℕ) :
    (adversarialTranscript gen).presentation (2 * s + 1) ≤ 16 * s + 11 := by
  rw [transcript_presentation_odd]
  have h := safeOrdinary_le (2 * s + 1)
    (history gen (2 * s + 1)).presentation
    (history gen (2 * s + 1)).query
    (history gen (2 * s + 1)).output
  omega

lemma target_infinite (gen : FeedbackGenerator) :
    (adversarialTarget gen).Infinite := by
  exact (Set.infinite_range_of_injective powTwo_injective).mono
    (core_subset_target gen)

noncomputable def orderedTarget (gen : FeedbackGenerator) : OrderedLanguage where
  carrier := adversarialTarget gen
  enumeration := Nat.nth (fun z => z ∈ adversarialTarget gen)
  enumeration_injective := Nat.nth_injective (target_infinite gen)
  range_enumeration := Nat.range_nth_of_infinite (target_infinite gen)

lemma orderedTarget_inherits (gen : FeedbackGenerator) :
    InheritsAmbientOrder (orderedTarget gen) := by
  exact Nat.nth_strictMono (target_infinite gen)

lemma target_nth_le (gen : FeedbackGenerator) (n : ℕ) :
    Nat.nth (fun z => z ∈ adversarialTarget gen) n ≤ 16 * n + 11 := by
  classical
  let values := (Finset.range (n + 1)).image
    (fun s => (adversarialTranscript gen).presentation (2 * s + 1))
  have hcard : values.card = n + 1 := by
    rw [Finset.card_image_of_injective]
    · simp [values]
    · intro a b hab
      apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2)
      have hp := adversarial_presentation_injective gen hab
      omega
  have hsub : values ⊆
      (Finset.range (16 * n + 12)).filter
        (fun z => z ∈ adversarialTarget gen) := by
    intro z hz
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz
    have hsn : s ≤ n := by
      have := Finset.mem_range.mp hs
      omega
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, ⟨2 * s + 1, rfl⟩⟩
    exact (odd_presentation_le gen s).trans_lt (by omega)
  have hcount : n < Nat.count
      (fun z => z ∈ adversarialTarget gen) (16 * n + 12) := by
    rw [Nat.count_eq_card_filter_range]
    have := Finset.card_le_card hsub
    rw [hcard] at this
    omega
  exact Nat.le_of_lt_succ (by
    have := Nat.nth_lt_of_lt_count hcount
    omega)

lemma square_le_pow_two {k : ℕ} (hk : 4 ≤ k) : k * k ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk4 ih =>
      calc
        (k + 1) * (k + 1) ≤ 2 * (k * k) := by nlinarith
        _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (k + 1) := by simp [pow_succ, Nat.mul_comm]

noncomputable local instance : DecidablePred (fun z : ℕ => z ∈ core) := Classical.decPred _

lemma count_core_le_sqrt_add_four (B : ℕ) :
    Nat.count (fun z => z ∈ core) B ≤ Nat.sqrt B + 4 := by
  classical
  rw [Nat.count_eq_card_filter_range]
  let powers := (Finset.range (Nat.sqrt B + 4)).image (fun k => 2 ^ k)
  calc
    ((Finset.range B).filter fun z => z ∈ core).card ≤ powers.card := by
      apply Finset.card_le_card
      intro z hz
      have hzlt : z < B := Finset.mem_range.mp (Finset.mem_filter.mp hz).1
      obtain ⟨k, rfl⟩ := (Finset.mem_filter.mp hz).2
      apply Finset.mem_image.mpr
      refine ⟨k, Finset.mem_range.mpr ?_, rfl⟩
      by_cases hk : k < 4
      · omega
      · have hsq : k * k ≤ B :=
          (square_le_pow_two (by omega)).trans hzlt.le
        have hksqrt : k ≤ Nat.sqrt B := Nat.le_sqrt.mpr hsq
        omega
    _ ≤ Nat.sqrt B + 4 := by
      exact (Finset.card_image_le.trans (by simp [powers]))

end Stage3Work

namespace Stage3Work

open Stage3S2B
open Filter
open scoped Topology

lemma orderedTarget_prefixCount_core_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).prefixCount core n ≤ Nat.sqrt (16 * n + 12) + 4 := by
  classical
  let indices := (Finset.range n).filter (fun i =>
    Nat.nth (fun z => z ∈ adversarialTarget gen) i ∈ core)
  have hcard : (orderedTarget gen).prefixCount core n = indices.card := by
    rfl
  rw [hcard, ← Finset.card_image_of_injective indices
    (Nat.nth_injective (target_infinite gen))]
  calc
    (indices.image (Nat.nth fun z => z ∈ adversarialTarget gen)).card ≤
        ((Finset.range (16 * n + 12)).filter fun z => z ∈ core).card := by
      apply Finset.card_le_card
      intro z hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      have hin : i < n := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
      have hicore := (Finset.mem_filter.mp hi).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr ?_, hicore⟩
      have hmono := (Nat.nth_le_nth (target_infinite gen)).2 hin.le
      exact hmono.trans_lt ((target_nth_le gen n).trans_lt (by omega))
    _ = Nat.count (fun z => z ∈ core) (16 * n + 12) := by
      rw [Nat.count_eq_card_filter_range]
    _ ≤ Nat.sqrt (16 * n + 12) + 4 := count_core_le_sqrt_add_four _

lemma sqrt_affine_le (n : ℕ) :
    Nat.sqrt (16 * n + 12) ≤ 4 * Nat.sqrt n + 4 := by
  rw [← Nat.lt_succ_iff, Nat.sqrt_lt]
  nlinarith [Nat.lt_succ_sqrt n]

noncomputable def coreEnvelope (n : ℕ) : ℝ :=
  if n = 0 then 0 else
    ((Nat.sqrt (16 * n + 12) + 4 : ℕ) : ℝ) / n

lemma coreEnvelope_tendsto_zero :
    Tendsto coreEnvelope atTop (𝓝 0) := by
  have hsparse :=
    GenLimit.InfiniteContamination.tendsto_sparseSqrt_add_one_div
  have hlarge : Tendsto
      (fun n : ℕ => 8 * (((Nat.sqrt n : ℝ) + 1) / (n : ℝ)))
      atTop (𝓝 0) := by
    simpa using hsparse.const_mul 8
  apply squeeze_zero
    (fun n => by simp [coreEnvelope]; positivity)
    (fun n => ?_) hlarge
  by_cases hn : n = 0
  · simp [coreEnvelope, hn]
  · simp only [coreEnvelope, hn, if_false]
    have hnnonneg : (0 : ℝ) ≤ n := by positivity
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hnnonneg
    have hsqrt := sqrt_affine_le n
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    exact_mod_cast (show Nat.sqrt (16 * n + 12) + 4 ≤
      8 * (Nat.sqrt n + 1) by omega)

lemma orderedTarget_prefixRatio_core_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).prefixRatio core n ≤ coreEnvelope n := by
  by_cases hn : n = 0
  · simp [hn, coreEnvelope]
  · simp only [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio,
      coreEnvelope, hn, if_false]
    apply div_le_div_of_nonneg_right
    · exact_mod_cast orderedTarget_prefixCount_core_le gen n
    · positivity

lemma orderedTarget_core_density_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity core = 0 := by
  have htendsto : Tendsto ((orderedTarget gen).prefixRatio core)
      atTop (𝓝 0) :=
    squeeze_zero
      (fun n => (orderedTarget gen).prefixRatio_nonneg core n)
      (orderedTarget_prefixRatio_core_le gen)
      coreEnvelope_tendsto_zero
  exact htendsto.limsup_eq

lemma orderedTarget_scored_density_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity
      (scored (adversarialTarget gen)
        (adversarialTranscript gen).presentation
        (adversarialTranscript gen).output) = 0 := by
  apply le_antisymm
  · exact ((orderedTarget gen).upperDensity_mono (scored_subset_core gen)).trans_eq
      (orderedTarget_core_density_zero gen)
  · exact (orderedTarget gen).upperDensity_nonneg _

end Stage3Work

namespace Stage3Work

open Stage3S2B

lemma adversarial_faithful_witness (gen : FeedbackGenerator) :
    FaithfulNegativeWitness gen (adversarialTarget gen)
      (adversarialPresenter gen) (adversarialTranscript gen)
      (orderedTarget gen) := by
  refine ⟨rfl, orderedTarget_inherits gen, adversarial_presented_by gen,
    adversarial_follows_protocol gen, adversarial_clean gen,
    adversarial_presentation_injective gen, adversarial_complete gen, ?_⟩
  exact orderedTarget_scored_density_zero gen

lemma negative_claim : NegativeClaim := by
  intro gen _hvalid
  exact ⟨adversarialTarget gen, adversarialTarget_mem_targetClass gen,
    adversarialPresenter gen, adversarialTranscript gen, orderedTarget gen,
    adversarial_faithful_witness gen⟩

end Stage3Work
