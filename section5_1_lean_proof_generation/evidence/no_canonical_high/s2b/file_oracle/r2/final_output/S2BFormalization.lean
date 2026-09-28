import Stage3Model
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Log
import GenLimit.Paper39_DenseGeneration.Abstract.Density

open Set Filter

namespace Stage3Proof

open Stage3S2B

theorem core_injective : Function.Injective (fun k : ℕ => 2 ^ k) :=
  Nat.pow_right_injective (by omega)

theorem core_infinite : core.Infinite := by
  rw [core]
  exact Set.infinite_range_of_injective core_injective

theorem core_mem (k : ℕ) : 2 ^ k ∈ core := ⟨k, rfl⟩

def ordinaryEmbed (k : ℕ) : ordinary := by
  refine ⟨2 * k + 3, ?_⟩
  rintro ⟨j, hj⟩
  cases j with
  | zero => simp at hj
  | succ j =>
      have heven : Even (2 ^ (j + 1)) := ⟨2 ^ j, by rw [pow_succ]; omega⟩
      change 2 ^ (j + 1) = 2 * k + 3 at hj
      rw [hj] at heven
      rcases heven with ⟨m, hm⟩
      omega

theorem ordinaryEmbed_injective : Function.Injective ordinaryEmbed := by
  intro a b hab
  have := congrArg Subtype.val hab
  simp [ordinaryEmbed] at this
  omega

instance : Infinite ordinary := Infinite.of_injective ordinaryEmbed ordinaryEmbed_injective

theorem uncountable_targetClass : ¬ targetClass.Countable := by
  intro hcount
  have hpowerset : ¬ Countable (Set ordinary) :=
    GenLimit.UnionClosedness.powerSet_not_countable ordinary
  apply hpowerset
  let encode : Set ordinary → Language := fun A => core ∪ ((fun z : ordinary => (z : ℕ)) '' A)
  have hencode : Function.Injective encode := by
    intro A B hAB
    ext z
    have hzordinary : (z : ℕ) ∈ ordinary := z.property
    have hznotcore : (z : ℕ) ∉ core := hzordinary
    have hzA : (z : ℕ) ∈ encode A ↔ z ∈ A := by
      simp [encode, hznotcore]
    have hzB : (z : ℕ) ∈ encode B ↔ z ∈ B := by
      simp [encode, hznotcore]
    rw [← hzA, ← hzB]
    exact Set.ext_iff.mp hAB (z : ℕ)
  have hrange : Set.range encode ⊆ targetClass := by
    rintro K ⟨A, rfl⟩
    refine ⟨(fun z : ordinary => (z : ℕ)) '' A, ?_, rfl⟩
    rintro _ ⟨z, _, rfl⟩
    exact z.property
  letI : Countable targetClass := hcount
  let f : Set ordinary → targetClass := fun A => ⟨encode A, hrange ⟨A, rfl⟩⟩
  exact (show Function.Injective f by
    intro A B hAB
    exact hencode (Subtype.ext_iff.mp hAB)).countable

theorem uniform_generation : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun k => 2 ^ k, core_injective, 0, ?_⟩
  intro K hK t _
  rcases hK with ⟨A, hA, rfl⟩
  exact Or.inl (core_mem t)

structure History (t : ℕ) where
  presentation : Fin t → ℕ
  query : Fin t → Option ℕ
  answer : Fin t → Option Bool
  output : Fin t → ℕ

def eligible {t : ℕ} (h : History t) (z : ℕ) : Prop :=
  (∀ i, h.presentation i ≠ z) ∧
    (z ∈ core ∨ ((∀ i, h.query i ≠ some z) ∧ ∀ i, h.output i ≠ z))

theorem exists_eligible {t : ℕ} (h : History t) : ∃ z, eligible h z := by
  let B : Finset ℕ :=
    (Finset.univ.image h.presentation) ∪
      (Finset.univ.image fun i => (h.query i).getD 0) ∪
      (Finset.univ.image h.output)
  let z := (∑ x ∈ B, x) + 1
  refine ⟨z, ?_⟩
  have hz : z ∉ B := by
    intro hzB
    have hle : z ≤ ∑ x ∈ B, x :=
      Finset.single_le_sum (f := fun x : ℕ => x) (fun _ _ => Nat.zero_le _) hzB
    simp only [z] at hle
    omega
  constructor
  · intro i hi
    apply hz
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩))
  · right
    constructor
    · intro i hi
      apply hz
      exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by simp [hi]⟩))
    · intro i hi
      apply hz
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)

noncomputable def nextValue {t : ℕ} (h : History t) : ℕ := by
  classical
  exact Nat.find (exists_eligible h)

theorem nextValue_eligible {t : ℕ} (h : History t) : eligible h (nextValue h) := by
  classical
  exact Nat.find_spec (exists_eligible h)

theorem nextValue_le (h : History t) : nextValue h ≤ 3 * t := by
  classical
  let X : Finset ℕ := Finset.univ.image h.presentation
  let Q : Finset ℕ := Finset.univ.image fun i => (h.query i).getD 0
  let Y : Finset ℕ := Finset.univ.image h.output
  let B := X ∪ Q ∪ Y
  have hX : X.card ≤ t := by simpa [X] using Finset.card_image_le (s := Finset.univ) (f := h.presentation)
  have hQ : Q.card ≤ t := by simpa [Q] using Finset.card_image_le (s := Finset.univ) (f := fun i => (h.query i).getD 0)
  have hY : Y.card ≤ t := by simpa [Y] using Finset.card_image_le (s := Finset.univ) (f := h.output)
  have hB : B.card ≤ 3 * t := by
    have hXQ := Finset.card_union_le X Q
    have hXQY := Finset.card_union_le (X ∪ Q) Y
    dsimp [B]
    omega
  obtain ⟨z, hzrange, hzB⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card (s := B) (t := Finset.range (3 * t + 1)) (by simp; omega)
  have helig : eligible h z := by
    constructor
    · intro i hi
      apply hzB
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩))
    · right
      constructor
      · intro i hi
        apply hzB
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by simp [hi]⟩))
      · intro i hi
        apply hzB
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
  have hmin : nextValue h ≤ z := Nat.find_min' (exists_eligible h) helig
  simp only [Finset.mem_range] at hzrange
  omega

def extend {α : Type*} {t : ℕ} (f : Fin t → α) (a : α) : Fin (t + 1) → α :=
  Fin.lastCases a f

noncomputable def step (gen : FeedbackGenerator) {t : ℕ} (h : History t) : History (t + 1) := by
  classical
  let x := nextValue h
  let xp := extend h.presentation x
  let q := gen.query t xp h.answer
  let a := match q with
    | none => none
    | some z => some (decide (z ∈ core ∨ ∃ i, xp i = z))
  let ap := extend h.answer a
  let y := gen.output t xp ap
  exact {
    presentation := xp
    query := extend h.query q
    answer := ap
    output := extend h.output y
  }

noncomputable def run (gen : FeedbackGenerator) : (t : ℕ) → History t
  | 0 => {
      presentation := Fin.elim0
      query := Fin.elim0
      answer := Fin.elim0
      output := Fin.elim0
    }
  | t + 1 => step gen (run gen t)

noncomputable def transcript (gen : FeedbackGenerator) : Transcript where
  presentation t := (run gen (t + 1)).presentation (Fin.last t)
  query t := (run gen (t + 1)).query (Fin.last t)
  answer t := (run gen (t + 1)).answer (Fin.last t)
  output t := (run gen (t + 1)).output (Fin.last t)


@[simp] theorem run_presentation_eq (gen : FeedbackGenerator) {t : ℕ} (i : Fin t) :
    (run gen t).presentation i = (transcript gen).presentation i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      cases i using Fin.lastCases with
      | last => simp [run, step, transcript, extend]
      | cast i => simpa [run, step, transcript, extend] using ih i

@[simp] theorem run_query_eq (gen : FeedbackGenerator) {t : ℕ} (i : Fin t) :
    (run gen t).query i = (transcript gen).query i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      cases i using Fin.lastCases with
      | last => simp [run, step, transcript, extend]
      | cast i => simpa [run, step, transcript, extend] using ih i

@[simp] theorem run_answer_eq (gen : FeedbackGenerator) {t : ℕ} (i : Fin t) :
    (run gen t).answer i = (transcript gen).answer i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      cases i using Fin.lastCases with
      | last => simp [run, step, transcript, extend]
      | cast i => simpa [run, step, transcript, extend] using ih i

@[simp] theorem run_output_eq (gen : FeedbackGenerator) {t : ℕ} (i : Fin t) :
    (run gen t).output i = (transcript gen).output i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      cases i using Fin.lastCases with
      | last => simp [run, step, transcript, extend]
      | cast i => simpa [run, step, transcript, extend] using ih i

@[simp] theorem transcript_presentation_now (gen : FeedbackGenerator) (t : ℕ) :
    (transcript gen).presentation t = nextValue (run gen t) := by
  simp [transcript, run, step, extend]

@[simp] theorem transcript_query_raw (gen : FeedbackGenerator) (t : ℕ) :
    (transcript gen).query t = gen.query t
      (extend (run gen t).presentation (nextValue (run gen t)))
      (run gen t).answer := by
  simp [transcript, run, step, extend]

theorem transcript_query_now (gen : FeedbackGenerator) (t : ℕ) :
    (transcript gen).query t = gen.query t
      (fun i => (transcript gen).presentation i)
      (fun i => (transcript gen).answer i) := by
  rw [transcript_query_raw]
  congr 1
  · funext i
    cases i using Fin.lastCases <;> simp [extend]
  · funext i
    simp

@[simp] theorem transcript_output_raw (gen : FeedbackGenerator) (t : ℕ) :
    (transcript gen).output t = gen.output t
      (extend (run gen t).presentation (nextValue (run gen t)))
      (extend (run gen t).answer ((transcript gen).answer t)) := by
  simp [transcript, run, step, extend]

theorem transcript_output_now (gen : FeedbackGenerator) (t : ℕ) :
    (transcript gen).output t = gen.output t
      (fun i => (transcript gen).presentation i)
      (fun i => (transcript gen).answer i) := by
  rw [transcript_output_raw]
  congr 1
  · funext i
    cases i using Fin.lastCases <;> simp [extend]
  · funext i
    cases i using Fin.lastCases <;> simp [extend]

noncomputable def presenter (gen : FeedbackGenerator) : CausalPresenter where
  next t x q a y := nextValue {
    presentation := x
    query := q
    answer := a
    output := y
  }

theorem presentedBy (gen : FeedbackGenerator) :
    PresentedBy (presenter gen) (transcript gen) := by
  intro t
  rw [transcript_presentation_now]
  apply congrArg nextValue
  cases hrun : run gen t with
  | mk x q a y =>
      simp only [History.mk.injEq]
      constructor
      · funext i
        rw [← run_presentation_eq gen i]
        exact (congrArg (fun h : History t => h.presentation i) hrun).symm
      constructor
      · funext i
        rw [← run_query_eq gen i]
        exact (congrArg (fun h : History t => h.query i) hrun).symm
      constructor
      · funext i
        rw [← run_answer_eq gen i]
        exact (congrArg (fun h : History t => h.answer i) hrun).symm
      · funext i
        rw [← run_output_eq gen i]
        exact (congrArg (fun h : History t => h.output i) hrun).symm

noncomputable def target (gen : FeedbackGenerator) : Language :=
  Set.range (transcript gen).presentation

theorem clean (gen : FeedbackGenerator) :
    Clean (transcript gen).presentation (target gen) := by
  intro t
  exact ⟨t, rfl⟩

theorem complete (gen : FeedbackGenerator) :
    Complete (transcript gen).presentation (target gen) := by
  rintro z ⟨t, rfl⟩
  exact ⟨t, rfl⟩

theorem presentation_injective (gen : FeedbackGenerator) :
    Function.Injective (transcript gen).presentation := by
  intro s t hst
  rcases lt_trichotomy s t with h | h | h
  · exfalso
    have helig := (nextValue_eligible (run gen t)).1 ⟨s, h⟩
    apply helig
    simpa using hst
  · exact h
  · exfalso
    have helig := (nextValue_eligible (run gen s)).1 ⟨t, h⟩
    apply helig
    simpa using hst.symm

theorem presentation_le (gen : FeedbackGenerator) (t : ℕ) :
    (transcript gen).presentation t ≤ 3 * t := by
  simpa using nextValue_le (run gen t)


theorem core_subset_target (gen : FeedbackGenerator) : core ⊆ target gen := by
  classical
  rintro z ⟨k, rfl⟩
  let z := 2 ^ k
  have hzpos : 0 < z := by positivity
  by_contra hzrange
  have hnever : ∀ t, (transcript gen).presentation t ≠ z := by
    intro t ht
    exact hzrange ⟨t, ht⟩
  let f : Fin (z + 1) → Fin z := fun i => ⟨(transcript gen).presentation i, by
    have helig : eligible (run gen i) z := by
      constructor
      · intro j hj
        apply hnever j
        simpa using hj
      · exact Or.inl ⟨k, rfl⟩
    have hle : (transcript gen).presentation i ≤ z := by
      rw [transcript_presentation_now]
      exact Nat.find_min' (exists_eligible (run gen i)) helig
    exact lt_of_le_of_ne hle (hnever i)⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    apply presentation_injective gen
    exact congrArg Fin.val hij
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hcard
  omega

theorem target_mem_class (gen : FeedbackGenerator) : target gen ∈ targetClass := by
  refine ⟨target gen \ core, Set.diff_subset_compl _ _, ?_⟩
  apply Set.Subset.antisymm
  · intro z hz
    by_cases hzc : z ∈ core
    · exact Or.inl hzc
    · exact Or.inr ⟨hz, hzc⟩
  · exact Set.union_subset (core_subset_target gen) Set.diff_subset

theorem future_not_presented_of_query (gen : FeedbackGenerator) {t z : ℕ}
    (hq : (transcript gen).query t = some z) (hzc : z ∉ core)
    (hnot : z ∉ observedThrough (transcript gen).presentation t) :
    z ∉ target gen := by
  rintro ⟨s, hs⟩
  by_cases hst : s ≤ t
  · apply hnot
    exact ⟨s, hst, hs⟩
  · have hts : t < s := Nat.lt_of_not_ge hst
    have helig := (nextValue_eligible (run gen s)).2
    rcases helig with hc | ho
    · apply hzc
      rw [← hs, transcript_presentation_now]
      exact hc
    · have hqne := ho.1 ⟨t, hts⟩
      apply hqne
      rw [run_query_eq]
      rw [show nextValue (run gen s) = (transcript gen).presentation s by
        rw [transcript_presentation_now], hs]
      simpa using hq

theorem target_iff_core_or_prefix (gen : FeedbackGenerator) {t z : ℕ}
    (hq : (transcript gen).query t = some z) :
    z ∈ target gen ↔ z ∈ core ∨ ∃ i : Fin (t + 1), (transcript gen).presentation i = z := by
  constructor
  · intro hz
    by_cases hzc : z ∈ core
    · exact Or.inl hzc
    · right
      by_contra hprefix
      have hnot : z ∉ observedThrough (transcript gen).presentation t := by
        rintro ⟨s, hst, hs⟩
        apply hprefix
        exact ⟨⟨s, Nat.lt_succ_of_le hst⟩, hs⟩
      exact future_not_presented_of_query gen hq hzc hnot hz
  · rintro (hzc | ⟨i, hi⟩)
    · exact core_subset_target gen hzc
    · exact ⟨i, hi⟩


theorem transcript_answer_now (gen : FeedbackGenerator) (t : ℕ) :
    (transcript gen).answer t =
      match (transcript gen).query t with
      | none => none
      | some z => some (membershipAnswer (target gen) z) := by
  classical
  rw [transcript_query_raw]
  change (step gen (run gen t)).answer (Fin.last t) = _
  simp only [step]
  cases hq : gen.query t
      (extend (run gen t).presentation (nextValue (run gen t)))
      (run gen t).answer with
  | none => simp [hq, extend]
  | some z =>
      have hqt : (transcript gen).query t = some z := by
        rw [transcript_query_raw, hq]
      simp only [hq, extend, Fin.lastCases_last]
      congr 2
      apply propext
      rw [target_iff_core_or_prefix gen hqt]
      constructor <;> rintro (h | ⟨i, hi⟩)
      · exact Or.inl h
      · exact Or.inr ⟨i, by cases i using Fin.lastCases <;> simpa [extend] using hi⟩
      · exact Or.inl h
      · exact Or.inr ⟨i, by cases i using Fin.lastCases <;> simpa [extend] using hi⟩
theorem followsProtocol (gen : FeedbackGenerator) :
    FollowsProtocol gen (target gen) (transcript gen) := by
  intro t
  exact ⟨transcript_query_now gen t, transcript_answer_now gen t,
    transcript_output_now gen t⟩


theorem scored_subset_core (gen : FeedbackGenerator) :
    scored (target gen) (transcript gen).presentation (transcript gen).output ⊆ core := by
  rintro z ⟨⟨s, hs⟩, t, hy, hnot⟩
  by_contra hzc
  by_cases hst : s ≤ t
  · exact hnot ⟨s, hst, hs⟩
  · have hts : t < s := Nat.lt_of_not_ge hst
    rcases (nextValue_eligible (run gen s)).2 with hc | ho
    · apply hzc
      rw [← hs, transcript_presentation_now]
      exact hc
    · have hyne := ho.2 ⟨t, hts⟩
      apply hyne
      rw [run_output_eq]
      rw [show nextValue (run gen s) = (transcript gen).presentation s by
        rw [transcript_presentation_now], hs]
      exact hy

theorem target_infinite (gen : FeedbackGenerator) : (target gen).Infinite :=
  core_infinite.mono (core_subset_target gen)

noncomputable def orderedTarget (gen : FeedbackGenerator) : OrderedLanguage where
  carrier := target gen
  enumeration := Nat.nth (· ∈ target gen)
  enumeration_injective := Nat.nth_injective (target_infinite gen)
  range_enumeration := Nat.range_nth_of_infinite (target_infinite gen)

theorem orderedTarget_strictMono (gen : FeedbackGenerator) :
    StrictMono (orderedTarget gen).enumeration :=
  Nat.nth_strictMono (target_infinite gen)

noncomputable def presentationRank (gen : FeedbackGenerator) (i : ℕ) : ℕ := by
  classical
  have hi : (transcript gen).presentation i ∈ target gen := ⟨i, rfl⟩
  have hrange : Set.range (Nat.nth fun z => z ∈ target gen) = target gen :=
    Nat.range_nth_of_infinite (target_infinite gen)
  have hi' : (transcript gen).presentation i ∈
      Set.range (Nat.nth fun z => z ∈ target gen) := hrange.symm ▸ hi
  exact Classical.choose hi'

theorem enumeration_rank (gen : FeedbackGenerator) (i : ℕ) :
    (orderedTarget gen).enumeration (presentationRank gen i) =
      (transcript gen).presentation i := by
  classical
  unfold presentationRank orderedTarget
  exact Classical.choose_spec (show
    (transcript gen).presentation i ∈ Set.range (Nat.nth fun z => z ∈ target gen) by
      have hrange : Set.range (Nat.nth fun z => z ∈ target gen) = target gen :=
        Nat.range_nth_of_infinite (target_infinite gen)
      rw [hrange]
      exact ⟨i, rfl⟩)

theorem presentationRank_injective (gen : FeedbackGenerator) :
    Function.Injective (presentationRank gen) := by
  intro i j hij
  apply presentation_injective gen
  rw [← enumeration_rank gen i, ← enumeration_rank gen j, hij]

theorem exists_large_rank (gen : FeedbackGenerator) (n : ℕ) :
    ∃ i : Fin (n + 1), n ≤ presentationRank gen i := by
  by_contra h
  push_neg at h
  let f : Fin (n + 1) → Fin n := fun i => ⟨presentationRank gen i, h i⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    apply presentationRank_injective gen
    exact congrArg Fin.val hij
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hcard
  omega

theorem orderedTarget_enumeration_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).enumeration n ≤ 3 * n := by
  obtain ⟨i, hi⟩ := exists_large_rank gen n
  calc
    (orderedTarget gen).enumeration n ≤
        (orderedTarget gen).enumeration (presentationRank gen i) :=
      (orderedTarget_strictMono gen).monotone hi
    _ = (transcript gen).presentation i := enumeration_rank gen i
    _ ≤ 3 * (i : ℕ) := presentation_le gen i
    _ ≤ 3 * n := Nat.mul_le_mul_left 3 (Nat.le_of_lt_succ i.isLt)

noncomputable def coreExponent {z : ℕ} (hz : z ∈ core) : ℕ :=
  Nat.find hz

theorem pow_coreExponent {z : ℕ} (hz : z ∈ core) :
    2 ^ coreExponent hz = z :=
  Nat.find_spec hz

theorem prefixCount_core_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).prefixCount core n ≤ Nat.log2 (3 * n) + 1 := by
  classical
  let S : Finset ℕ := (Finset.range n).filter fun i =>
    (orderedTarget gen).enumeration i ∈ core
  let exponent : {i // i ∈ S} → Fin (Nat.log2 (3 * n) + 1) := fun i => by
    have hi : i.1 < n := Finset.mem_range.mp (Finset.mem_filter.mp i.2).1
    have hicore : (orderedTarget gen).enumeration i.1 ∈ core :=
      (Finset.mem_filter.mp i.2).2
    let k := coreExponent hicore
    have hpow : 2 ^ k = (orderedTarget gen).enumeration i.1 := pow_coreExponent hicore
    have hvalue : (orderedTarget gen).enumeration i.1 ≤ 3 * n := by
      calc
        (orderedTarget gen).enumeration i.1 ≤ 3 * i.1 :=
          orderedTarget_enumeration_le gen i.1
        _ ≤ 3 * n := Nat.mul_le_mul_left 3 (Nat.le_of_lt hi)
    have hk : k ≤ Nat.log2 (3 * n) := by
      rw [Nat.log2_eq_log_two]
      exact Nat.le_log_of_pow_le Nat.one_lt_two (hpow.trans_le hvalue)
    exact ⟨k, Nat.lt_succ_of_le hk⟩
  have hexponent : Function.Injective exponent := by
    intro i j hij
    apply Subtype.ext
    apply (orderedTarget gen).enumeration_injective
    have hi : (orderedTarget gen).enumeration i.1 ∈ core :=
      (Finset.mem_filter.mp i.2).2
    have hj : (orderedTarget gen).enumeration j.1 ∈ core :=
      (Finset.mem_filter.mp j.2).2
    have hk : coreExponent hi = coreExponent hj := congrArg Fin.val hij
    rw [← pow_coreExponent hi, ← pow_coreExponent hj, hk]
  have hcard := Fintype.card_le_of_injective exponent hexponent
  change S.card ≤ Nat.log2 (3 * n) + 1
  simpa only [Fintype.card_coe, Fintype.card_fin] using hcard

theorem log2_three_mul_add_one_le (n : ℕ) :
    Nat.log2 (3 * n) + 1 ≤ 3 + Nat.log2 n := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    have hmono : Nat.log 2 (3 * n) ≤ Nat.log 2 (4 * n) :=
      Nat.log_mono_right (Nat.mul_le_mul_right n (by omega : 3 ≤ 4))
    have hlog : Nat.log 2 (4 * n) = Nat.log 2 n + 2 := by
      calc
        Nat.log 2 (4 * n) = Nat.log 2 ((n * 2) * 2) := by
          rw [show 4 * n = (n * 2) * 2 by omega]
        _ = Nat.log 2 (n * 2) + 1 :=
          Nat.log_mul_base Nat.one_lt_two (by positivity)
        _ = Nat.log 2 n + 1 + 1 := by rw [Nat.log_mul_base Nat.one_lt_two hn]
        _ = Nat.log 2 n + 2 := by omega
    omega

theorem prefixRatio_core_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).prefixRatio core n ≤
      ((3 + Nat.log2 n : ℕ) : ℝ) / (n : ℝ) := by
  by_cases hn : n = 0
  · simp [hn]
  · unfold GenLimit.KleinbergWei.OrderedLanguage.prefixRatio
    simp only [hn, if_false]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    exact_mod_cast (prefixCount_core_le gen n).trans (log2_three_mul_add_one_le n)

theorem prefixRatio_core_tendsto (gen : FeedbackGenerator) :
    Tendsto ((orderedTarget gen).prefixRatio core) atTop (nhds 0) := by
  exact squeeze_zero
    (fun n => (orderedTarget gen).prefixRatio_nonneg core n)
    (prefixRatio_core_le gen)
    (GenLimit.tendsto_countingError_div 3)

theorem upperDensity_core (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity core = 0 := by
  unfold GenLimit.KleinbergWei.OrderedLanguage.upperDensity
  exact (prefixRatio_core_tendsto gen).limsup_eq

theorem upperDensity_scored (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity
      (scored (target gen) (transcript gen).presentation (transcript gen).output) = 0 := by
  apply le_antisymm
  · calc
      (orderedTarget gen).upperDensity
          (scored (target gen) (transcript gen).presentation (transcript gen).output) ≤
          (orderedTarget gen).upperDensity core :=
        (orderedTarget gen).upperDensity_mono (scored_subset_core gen)
      _ = 0 := upperDensity_core gen
  · exact (orderedTarget gen).upperDensity_nonneg _

theorem negativeClaim : NegativeClaim := by
  intro gen _
  refine ⟨target gen, target_mem_class gen, presenter gen, transcript gen,
    orderedTarget gen, ?_⟩
  exact ⟨rfl, orderedTarget_strictMono gen, presentedBy gen, followsProtocol gen,
    clean gen, presentation_injective gen, complete gen, upperDensity_scored gen⟩
end Stage3Proof

theorem stage3_result : Stage3S2B.MainClaim := by
  exact ⟨Stage3Proof.uncountable_targetClass, Stage3Proof.uniform_generation,
    Stage3Proof.negativeClaim⟩
