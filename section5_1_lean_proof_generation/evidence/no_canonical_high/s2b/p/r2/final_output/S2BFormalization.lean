import Stage3Model
import Mathlib.Data.Nat.Nth
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

open Set Function Filter

namespace S2BProof

open Stage3S2B

noncomputable section

abbrev encode (n : ℕ) : ℕ := 2 * n + 3

lemma encode_injective : Function.Injective encode := by
  intro a b h
  dsimp [encode] at h
  omega

lemma encode_ordinary (n : ℕ) : encode n ∈ ordinary := by
  intro h
  rcases h with ⟨k, hk⟩
  rcases k with _ | k
  · simp [encode] at hk
  · have he : Even (2 ^ (k + 1)) := (Nat.even_pow).2 ⟨even_two, by omega⟩
    change 2 ^ (k + 1) = encode n at hk
    rw [hk] at he
    rcases he with ⟨m, hm⟩
    simp [encode] at hm
    omega

lemma core_injective : Function.Injective (fun k : ℕ => 2 ^ k) :=
  Nat.pow_right_injective (by omega)

lemma target_uncountable : ¬ targetClass.Countable := by
  intro hcount
  let F : Set ℕ → {K // K ∈ targetClass} := fun B =>
    ⟨core ∪ encode '' B, ⟨encode '' B, by
      rintro z ⟨n, hn, rfl⟩
      exact encode_ordinary n, rfl⟩⟩
  have hF : Function.Injective F := by
    intro A B h
    apply Set.ext
    intro n
    have hs : encode n ∈ core ∪ encode '' A ↔ encode n ∈ core ∪ encode '' B := by
      change encode n ∈ (F A).1 ↔ encode n ∈ (F B).1
      rw [h]
    simp only [mem_union, mem_image] at hs
    have hncore : encode n ∉ core := encode_ordinary n
    simp only [hncore, false_or, encode_injective.eq_iff] at hs
    constructor
    · intro ha
      rcases hs.mp ⟨n, ha, rfl⟩ with ⟨m, hm, hmn⟩
      simpa [hmn] using hm
    · intro hb
      rcases hs.mpr ⟨n, hb, rfl⟩ with ⟨m, hm, hmn⟩
      simpa [hmn] using hm
  letI : Countable {K // K ∈ targetClass} := hcount.to_subtype
  have hsets : Countable (Set ℕ) := hF.countable
  obtain ⟨enum, henum⟩ := countable_iff_exists_surjective.1 hsets
  let D : Set ℕ := {n | n ∉ enum n}
  obtain ⟨n, hn⟩ := henum D
  have hdiag : n ∈ D ↔ n ∉ enum n := Iff.rfl
  rw [hn] at hdiag
  have := hdiag
  tauto

lemma uniform_generation : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t => 2 ^ t, core_injective, 0, ?_⟩
  intro K hK t ht
  rcases hK with ⟨A, hA, rfl⟩
  exact mem_union_left _ ⟨t, rfl⟩

structure Prefix (t : ℕ) where
  presentation : Fin t → ℕ
  query : Fin t → Option ℕ
  answer : Fin t → Option Bool
  output : Fin t → ℕ

def append {α : Type*} {t : ℕ} (f : Fin t → α) (a : α) : Fin (t + 1) → α :=
  Fin.lastCases a f

@[simp] lemma append_last {α : Type*} {t : ℕ} (f : Fin t → α) (a : α) :
    append f a (Fin.last t) = a := by
  simp [append]

@[simp] lemma append_castSucc {α : Type*} {t : ℕ} (f : Fin t → α) (a : α) (i : Fin t) :
    append f a i.castSucc = f i := by
  simp [append]

noncomputable def blocked {t : ℕ} (p : Prefix t) : Finset ℕ := by
  classical
  exact (Finset.univ.image p.presentation) ∪
    (Finset.univ.biUnion fun i => match p.query i with
      | none => ∅
      | some z => {z}) ∪
    (Finset.univ.image p.output)

noncomputable def freshExists {t : ℕ} (p : Prefix t) : ∃ n, encode n ∉ blocked p := by
  classical
  obtain ⟨z, ⟨n, rfl⟩, hz⟩ :=
    (Set.infinite_range_of_injective encode_injective).exists_not_mem_finset (blocked p)
  exact ⟨n, hz⟩

noncomputable def freshIndex {t : ℕ} (p : Prefix t) : ℕ :=
  Nat.find (freshExists p)

noncomputable def freshOrdinary {t : ℕ} (p : Prefix t) : ℕ := encode (freshIndex p)

lemma freshOrdinary_mem_range {t : ℕ} (p : Prefix t) : freshOrdinary p ∈ Set.range encode :=
  ⟨freshIndex p, rfl⟩

lemma freshOrdinary_not_blocked {t : ℕ} (p : Prefix t) : freshOrdinary p ∉ blocked p := by
  exact Nat.find_spec (freshExists p)


lemma blocked_card_le {t : ℕ} (p : Prefix t) : (blocked p).card ≤ 3 * t := by
  classical
  unfold blocked
  let qset : Fin t → Finset ℕ := fun i => match p.query i with
    | none => ∅
    | some z => {z}
  change ((Finset.univ.image p.presentation) ∪ (Finset.univ.biUnion qset) ∪
    (Finset.univ.image p.output)).card ≤ 3 * t
  have h1 : (Finset.univ.image p.presentation).card ≤ t := by
    simpa using (Finset.card_image_le (s := Finset.univ) (f := p.presentation))
  have h2 : (Finset.univ.biUnion qset).card ≤ t := by
    calc
      _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin t)),
          (qset i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin t)), 1 := by
        apply Finset.sum_le_sum
        intro i hi
        rcases hq : p.query i with _ | z <;> simp [qset, hq]
      _ = t := by simp
  have h3 : (Finset.univ.image p.output).card ≤ t := by
    simpa using (Finset.card_image_le (s := Finset.univ) (f := p.output))
  have hu1 := Finset.card_union_le (Finset.univ.image p.presentation)
    (Finset.univ.biUnion qset)
  have hu2 := Finset.card_union_le
    ((Finset.univ.image p.presentation) ∪ (Finset.univ.biUnion qset))
    (Finset.univ.image p.output)
  omega

lemma freshIndex_le_card {t : ℕ} (p : Prefix t) : freshIndex p ≤ (blocked p).card := by
  classical
  let r := Finset.range ((blocked p).card + 1)
  have hcard : (Finset.image encode r).card = (blocked p).card + 1 := by
    rw [Finset.card_image_of_injective _ encode_injective]
    simp [r]
  obtain ⟨z, hzimg, hznot⟩ := Finset.exists_mem_not_mem_of_card_lt_card
    (s := blocked p) (t := Finset.image encode r) (by omega)
  rcases Finset.mem_image.mp hzimg with ⟨n, hn, rfl⟩
  have hnle : n ≤ (blocked p).card := by
    have : n < (blocked p).card + 1 := by simpa [r] using hn
    omega
  exact (Nat.find_min' (freshExists p) hznot).trans hnle

lemma freshOrdinary_le {t : ℕ} (p : Prefix t) : freshOrdinary p ≤ 6 * t + 3 := by
  unfold freshOrdinary encode
  have h := freshIndex_le_card p
  have hb := blocked_card_le p
  omega

noncomputable def nextPresentation {t : ℕ} (p : Prefix t) : ℕ :=
  if Even t then 2 ^ (t / 2) else freshOrdinary p

noncomputable def onlineAnswer {t : ℕ} (x : Fin (t + 1) → ℕ) : Option ℕ → Option Bool
  | none => none
  | some z => some (by classical exact decide (z ∈ core ∨ ∃ i, x i = z))

noncomputable def step (gen : FeedbackGenerator) {t : ℕ} (p : Prefix t) : Prefix (t + 1) := by
  let xnew := nextPresentation p
  let x := append p.presentation xnew
  let qnew := gen.query t x p.answer
  let anew := onlineAnswer x qnew
  let a := append p.answer anew
  let ynew := gen.output t x a
  exact {
    presentation := x
    query := append p.query qnew
    answer := a
    output := append p.output ynew
  }

noncomputable def prefixes (gen : FeedbackGenerator) : (t : ℕ) → Prefix t
  | 0 => ⟨Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0⟩
  | t + 1 => step gen (prefixes gen t)

noncomputable def adversarialTranscript (gen : FeedbackGenerator) : Transcript := {
  presentation := fun t => (prefixes gen (t + 1)).presentation (Fin.last t)
  query := fun t => (prefixes gen (t + 1)).query (Fin.last t)
  answer := fun t => (prefixes gen (t + 1)).answer (Fin.last t)
  output := fun t => (prefixes gen (t + 1)).output (Fin.last t)
}

lemma prefixes_presentation (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (prefixes gen t).presentation i = (adversarialTranscript gen).presentation i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · simpa [prefixes, step, adversarialTranscript] using ih j

lemma prefixes_query (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (prefixes gen t).query i = (adversarialTranscript gen).query i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · simpa [prefixes, step, adversarialTranscript] using ih j

lemma prefixes_answer (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (prefixes gen t).answer i = (adversarialTranscript gen).answer i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · simpa [prefixes, step, adversarialTranscript] using ih j

lemma prefixes_output (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (prefixes gen t).output i = (adversarialTranscript gen).output i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · simpa [prefixes, step, adversarialTranscript] using ih j


lemma presentation_step (gen : FeedbackGenerator) (t : ℕ) :
    (adversarialTranscript gen).presentation t = nextPresentation (prefixes gen t) := by
  change (step gen (prefixes gen t)).presentation (Fin.last t) = _
  simp [step]

lemma query_step (gen : FeedbackGenerator) (t : ℕ) :
    (adversarialTranscript gen).query t = gen.query t
      (fun i => (adversarialTranscript gen).presentation i)
      (fun i => (adversarialTranscript gen).answer i) := by
  change (step gen (prefixes gen t)).query (Fin.last t) = _
  simp only [step, append_last]
  apply congrArg₂ (gen.query t)
  · funext i
    exact prefixes_presentation gen (t + 1) i
  · funext i
    exact prefixes_answer gen t i

lemma answer_step (gen : FeedbackGenerator) (t : ℕ) :
    (adversarialTranscript gen).answer t = onlineAnswer
      (t := t) (fun i => (adversarialTranscript gen).presentation i)
      ((adversarialTranscript gen).query t) := by
  change (step gen (prefixes gen t)).answer (Fin.last t) = _
  simp only [step, append_last]
  have hx : append (prefixes gen t).presentation (nextPresentation (prefixes gen t)) =
      fun i : Fin (t + 1) => (adversarialTranscript gen).presentation i := by
    funext i
    exact prefixes_presentation gen (t + 1) i
  have ha : (prefixes gen t).answer =
      fun i : Fin t => (adversarialTranscript gen).answer i := by
    funext i
    exact prefixes_answer gen t i
  have hq : gen.query t
      (append (prefixes gen t).presentation (nextPresentation (prefixes gen t)))
      (prefixes gen t).answer = (adversarialTranscript gen).query t := by
    calc
      _ = gen.query t (fun i => (adversarialTranscript gen).presentation i)
          (fun i => (adversarialTranscript gen).answer i) := congrArg₂ (gen.query t) hx ha
      _ = _ := (query_step gen t).symm
  exact congrArg₂ onlineAnswer hx hq

lemma output_step (gen : FeedbackGenerator) (t : ℕ) :
    (adversarialTranscript gen).output t = gen.output t
      (fun i => (adversarialTranscript gen).presentation i)
      (fun i => (adversarialTranscript gen).answer i) := by
  change (step gen (prefixes gen t)).output (Fin.last t) = _
  simp only [step, append_last]
  congr 1 <;> funext i
  · exact prefixes_presentation gen (t + 1) i
  · exact prefixes_answer gen (t + 1) i

lemma presentation_mem_blocked {t : ℕ} (p : Prefix t) (i : Fin t) :
    p.presentation i ∈ blocked p := by
  classical
  simp [blocked]

lemma output_mem_blocked {t : ℕ} (p : Prefix t) (i : Fin t) :
    p.output i ∈ blocked p := by
  classical
  simp [blocked]

lemma query_mem_blocked {t : ℕ} (p : Prefix t) (i : Fin t) {z : ℕ}
    (h : p.query i = some z) : z ∈ blocked p := by
  classical
  rw [blocked]
  simp only [Finset.mem_union]
  left
  right
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  refine ⟨i, ?_⟩
  simp [h]

lemma odd_presentation_ordinary (gen : FeedbackGenerator) {t : ℕ} (ht : ¬ Even t) :
    (adversarialTranscript gen).presentation t ∈ ordinary := by
  rw [presentation_step, nextPresentation, if_neg ht]
  rcases freshOrdinary_mem_range (prefixes gen t) with ⟨n, hn⟩
  rw [← hn]
  exact encode_ordinary n

lemma even_presentation_core (gen : FeedbackGenerator) {t : ℕ} (ht : Even t) :
    (adversarialTranscript gen).presentation t ∈ core := by
  rw [presentation_step, nextPresentation, if_pos ht]
  exact ⟨t / 2, rfl⟩

lemma core_presented (gen : FeedbackGenerator) (k : ℕ) :
    (adversarialTranscript gen).presentation (2 * k) = 2 ^ k := by
  rw [presentation_step, nextPresentation, if_pos]
  · simp
  · exact ⟨k, by omega⟩

lemma future_ne_of_output_ordinary (gen : FeedbackGenerator) {t s z : ℕ}
    (hts : t < s) (hy : (adversarialTranscript gen).output t = z)
    (hz : z ∈ ordinary) : (adversarialTranscript gen).presentation s ≠ z := by
  intro hx
  by_cases hs : Even s
  · have hc := even_presentation_core gen hs
    rw [hx] at hc
    exact hz hc
  · rw [presentation_step, nextPresentation, if_neg hs] at hx
    have hnot := freshOrdinary_not_blocked (prefixes gen s)
    apply hnot
    let i : Fin s := ⟨t, hts⟩
    have hm := output_mem_blocked (prefixes gen s) i
    rw [prefixes_output gen s i, hy] at hm
    simpa [hx] using hm

lemma future_ne_of_query_ordinary (gen : FeedbackGenerator) {t s z : ℕ}
    (hts : t < s) (hq : (adversarialTranscript gen).query t = some z)
    (hz : z ∈ ordinary) : (adversarialTranscript gen).presentation s ≠ z := by
  intro hx
  by_cases hs : Even s
  · have hc := even_presentation_core gen hs
    rw [hx] at hc
    exact hz hc
  · rw [presentation_step, nextPresentation, if_neg hs] at hx
    have hnot := freshOrdinary_not_blocked (prefixes gen s)
    apply hnot
    let i : Fin s := ⟨t, hts⟩
    have hqpre : (prefixes gen s).query i = some z := by
      rw [prefixes_query gen s i, hq]
    have hm := query_mem_blocked (prefixes gen s) i hqpre
    simpa [hx] using hm


noncomputable def adversarialTarget (gen : FeedbackGenerator) : Language :=
  Set.range (adversarialTranscript gen).presentation

noncomputable def adversarialPresenter (gen : FeedbackGenerator) : CausalPresenter := {
  next := fun t _ _ _ _ => nextPresentation (prefixes gen t)
}

lemma target_mem_class (gen : FeedbackGenerator) : adversarialTarget gen ∈ targetClass := by
  let A : Language := adversarialTarget gen ∩ ordinary
  refine ⟨A, inter_subset_right, ?_⟩
  apply Set.Subset.antisymm
  · rintro z ⟨t, rfl⟩
    by_cases ht : Even t
    · exact mem_union_left _ (even_presentation_core gen ht)
    · exact mem_union_right _ ⟨⟨t, rfl⟩, odd_presentation_ordinary gen ht⟩
  · rintro z (hz | hz)
    · rcases hz with ⟨k, rfl⟩
      exact ⟨2 * k, core_presented gen k⟩
    · exact hz.1

lemma presentation_later_ne (gen : FeedbackGenerator) {t s : ℕ} (hts : t < s) :
    (adversarialTranscript gen).presentation t ≠
      (adversarialTranscript gen).presentation s := by
  by_cases hs : Even s
  · by_cases ht : Even t
    · rcases ht with ⟨a, ha⟩
      rcases hs with ⟨b, hb⟩
      have hab : a < b := by omega
      have hxa : (adversarialTranscript gen).presentation t = 2 ^ a := by
        rw [ha]
        simpa [two_mul] using core_presented gen a
      have hxb : (adversarialTranscript gen).presentation s = 2 ^ b := by
        rw [hb]
        simpa [two_mul] using core_presented gen b
      rw [hxa, hxb]
      exact ne_of_lt (Nat.pow_lt_pow_right (by omega) hab)
    · intro h
      have ho := odd_presentation_ordinary gen ht
      have hc := even_presentation_core gen hs
      rw [h] at ho
      exact ho hc
  · conv_rhs => rw [presentation_step, nextPresentation, if_neg hs]
    have hnot := freshOrdinary_not_blocked (prefixes gen s)
    intro h
    let i : Fin s := ⟨t, hts⟩
    have hm := presentation_mem_blocked (prefixes gen s) i
    rw [prefixes_presentation gen s i, h] at hm
    exact hnot hm

lemma presentation_injective (gen : FeedbackGenerator) :
    Function.Injective (adversarialTranscript gen).presentation := by
  intro a b h
  rcases lt_trichotomy a b with hab | hab | hab
  · exact (presentation_later_ne gen hab h).elim
  · exact hab
  · exact (presentation_later_ne gen hab h.symm).elim

lemma presented_by (gen : FeedbackGenerator) :
    PresentedBy (adversarialPresenter gen) (adversarialTranscript gen) := by
  intro t
  exact presentation_step gen t

lemma clean (gen : FeedbackGenerator) :
    Clean (adversarialTranscript gen).presentation (adversarialTarget gen) := by
  intro t
  exact ⟨t, rfl⟩

lemma complete (gen : FeedbackGenerator) :
    Complete (adversarialTranscript gen).presentation (adversarialTarget gen) := by
  intro z hz
  exact hz

lemma core_subset_target (gen : FeedbackGenerator) : core ⊆ adversarialTarget gen := by
  rintro z ⟨k, rfl⟩
  exact ⟨2 * k, core_presented gen k⟩

lemma query_target_iff (gen : FeedbackGenerator) {t z : ℕ}
    (hq : (adversarialTranscript gen).query t = some z) :
    (z ∈ core ∨ ∃ i : Fin (t + 1), (adversarialTranscript gen).presentation i = z) ↔
      z ∈ adversarialTarget gen := by
  constructor
  · rintro (hc | ⟨i, hi⟩)
    · exact core_subset_target gen hc
    · exact ⟨i, hi⟩
  · rintro ⟨s, hs⟩
    by_cases hc : z ∈ core
    · exact Or.inl hc
    · right
      have ho : z ∈ ordinary := hc
      have hst : s ≤ t := by
        by_contra hle
        have hts : t < s := Nat.lt_of_not_ge hle
        exact future_ne_of_query_ordinary gen hts hq ho hs
      exact ⟨⟨s, Nat.lt_succ_of_le hst⟩, hs⟩

lemma follows_protocol (gen : FeedbackGenerator) :
    FollowsProtocol gen (adversarialTarget gen) (adversarialTranscript gen) := by
  intro t
  refine ⟨query_step gen t, ?_, output_step gen t⟩
  rw [answer_step]
  cases hq : (adversarialTranscript gen).query t with
  | none => simp [onlineAnswer, hq]
  | some z =>
      simp only [onlineAnswer, hq]
      congr 2
      exact propext (query_target_iff gen hq)

lemma scored_subset_core (gen : FeedbackGenerator) :
    scored (adversarialTarget gen) (adversarialTranscript gen).presentation
      (adversarialTranscript gen).output ⊆ core := by
  intro z hz
  rcases hz with ⟨hzK, t, hyt, hfresh⟩
  by_contra hc
  have ho : z ∈ ordinary := hc
  rcases hzK with ⟨s, hxs⟩
  by_cases hst : s ≤ t
  · apply hfresh
    exact ⟨s, hst, hxs⟩
  · have hts : t < s := Nat.lt_of_not_ge hst
    exact future_ne_of_output_ordinary gen hts hyt ho hxs

lemma target_infinite (gen : FeedbackGenerator) : (adversarialTarget gen).Infinite :=
  (Set.infinite_range_of_injective core_injective).mono (core_subset_target gen)

noncomputable def orderedTarget (gen : FeedbackGenerator) : OrderedLanguage where
  carrier := adversarialTarget gen
  enumeration := Nat.nth (fun z => z ∈ adversarialTarget gen)
  enumeration_injective := Nat.nth_injective (target_infinite gen)
  range_enumeration := Nat.range_nth_of_infinite (target_infinite gen)

lemma orderedTarget_strictMono (gen : FeedbackGenerator) :
    StrictMono (orderedTarget gen).enumeration :=
  Nat.nth_strictMono (target_infinite gen)

lemma odd_presentation_le (gen : FeedbackGenerator) (n : ℕ) :
    (adversarialTranscript gen).presentation (2 * n + 1) ≤ 12 * n + 9 := by
  have hodd : ¬ Even (2 * n + 1) := by
    rintro ⟨k, hk⟩
    omega
  rw [presentation_step, nextPresentation, if_neg hodd]
  have h := freshOrdinary_le (prefixes gen (2 * n + 1))
  omega

lemma nth_target_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).enumeration n ≤ 12 * n + 9 := by
  classical
  let oddPoint : Fin (n + 1) → ℕ := fun i =>
    (adversarialTranscript gen).presentation (2 * (i : ℕ) + 1)
  have hodd_inj : Function.Injective oddPoint := by
    intro i j hij
    have hind : 2 * (i : ℕ) + 1 = 2 * (j : ℕ) + 1 := by
      apply presentation_injective gen
      simpa [oddPoint] using hij
    apply Fin.ext
    omega
  have hodd_mem : ∀ i, oddPoint i ∈ adversarialTarget gen := by
    intro i
    exact ⟨2 * (i : ℕ) + 1, rfl⟩
  have hrange : Set.range (orderedTarget gen).enumeration = adversarialTarget gen :=
    (orderedTarget gen).range_enumeration
  let position : Fin (n + 1) → ℕ := fun i =>
    Classical.choose (hrange.symm ▸ hodd_mem i)
  have hposition : ∀ i, (orderedTarget gen).enumeration (position i) = oddPoint i := by
    intro i
    exact Classical.choose_spec (hrange.symm ▸ hodd_mem i)
  have hpos_inj : Function.Injective position := by
    intro i j hij
    apply hodd_inj
    rw [← hposition i, ← hposition j, hij]
  have hex : ∃ i, n ≤ position i := by
    by_contra h
    push_neg at h
    let smallPosition : Fin (n + 1) → Fin n := fun i => ⟨position i, h i⟩
    have hsmall : Function.Injective smallPosition := by
      intro i j hij
      apply hpos_inj
      exact Fin.ext_iff.mp hij
    have hc := Fintype.card_le_of_injective smallPosition hsmall
    simp at hc
  obtain ⟨i, hi⟩ := hex
  calc
    (orderedTarget gen).enumeration n ≤ (orderedTarget gen).enumeration (position i) :=
      (orderedTarget_strictMono gen).monotone hi
    _ = oddPoint i := hposition i
    _ ≤ 12 * (i : ℕ) + 9 := odd_presentation_le gen i
    _ ≤ 12 * n + 9 := by omega

lemma prefixCount_core_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).prefixCount core n ≤ Nat.log2 (12 * n + 9) + 1 := by
  classical
  let selected := (Finset.range n).filter fun i => (orderedTarget gen).enumeration i ∈ core
  let exponent : {i // i ∈ selected} → ℕ := fun i => Classical.choose (by
    have hi := (Finset.mem_filter.mp i.property).2
    exact hi)
  have hpow : ∀ i, 2 ^ exponent i = (orderedTarget gen).enumeration i := by
    intro i
    exact Classical.choose_spec (by
      have hi := (Finset.mem_filter.mp i.property).2
      exact hi)
  have hexponent_le : ∀ i, exponent i ≤ Nat.log2 (12 * n + 9) := by
    intro i
    apply (Nat.le_log2 (by omega)).2
    rw [hpow i]
    have hin : (i : ℕ) < n := Finset.mem_range.mp (Finset.mem_filter.mp i.property).1
    calc
      (orderedTarget gen).enumeration (i : ℕ) ≤ (orderedTarget gen).enumeration n :=
        (orderedTarget_strictMono gen).monotone hin.le
      _ ≤ 12 * n + 9 := nth_target_le gen n
  let exponentFin : {i // i ∈ selected} → Fin (Nat.log2 (12 * n + 9) + 1) :=
    fun i => ⟨exponent i, Nat.lt_succ_of_le (hexponent_le i)⟩
  have hexponent_inj : Function.Injective exponentFin := by
    intro i j hij
    apply Subtype.ext
    apply (orderedTarget gen).enumeration_injective
    rw [← hpow i, ← hpow j]
    congr 1
    exact congrArg Fin.val hij
  have hcard := Fintype.card_le_of_injective exponentFin hexponent_inj
  simpa [Stage3S2B.OrderedLanguage, GenLimit.KleinbergWei.OrderedLanguage.prefixCount,
    selected] using hcard

lemma log2_ratio_tendsto_zero : Tendsto (fun n : ℕ =>
    ((Nat.log2 (12 * n + 9) + 1 : ℕ) : ℝ) / (n : ℝ)) atTop (nhds 0) := by
  have hx : Tendsto (fun n : ℕ => 12 * (n : ℝ) + 9) atTop atTop := by
    apply tendsto_atTop_add_const_right atTop 9
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 12)
  have hlog : Tendsto (fun n : ℕ =>
      Real.logb 2 (12 * (n : ℝ) + 9) / (n : ℝ)) atTop (nhds 0) := by
    have h := (Real.tendsto_pow_logb_div_mul_add_atTop (b := (2 : ℝ))
      (1 / 12) (-3 / 4) 1 (by norm_num : (1 / 12 : ℝ) ≠ 0)).comp hx
    convert h using 1
    funext n
    simp only [pow_one]
    congr 1
    ring
  have hone : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have hupper : Tendsto (fun n : ℕ =>
      (Real.logb 2 (12 * (n : ℝ) + 9) + 1) / (n : ℝ)) atTop (nhds 0) := by
    have hadd := hlog.add hone
    rw [zero_add] at hadd
    convert hadd using 1
    funext n
    ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
  · intro n
    positivity
  · intro n
    by_cases hn : n = 0
    · simp [hn]
    · apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ (n : ℝ))
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      convert add_le_add_right (Real.log2_le_logb (12 * n + 9)) 1 using 1 <;> norm_num

lemma prefixRatio_core_tendsto_zero (gen : FeedbackGenerator) :
    Tendsto ((orderedTarget gen).prefixRatio core) atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    log2_ratio_tendsto_zero
  · intro n
    unfold GenLimit.KleinbergWei.OrderedLanguage.prefixRatio
    split <;> positivity
  · intro n
    unfold GenLimit.KleinbergWei.OrderedLanguage.prefixRatio
    by_cases hn : n = 0
    · simp [hn]
    · rw [if_neg hn]
      exact div_le_div_of_nonneg_right (by
        exact Nat.cast_le.2 (prefixCount_core_le gen n)) (by positivity)

lemma prefixCount_mono (K : OrderedLanguage) {A B : Language} (hAB : A ⊆ B) (n : ℕ) :
    K.prefixCount A n ≤ K.prefixCount B n := by
  classical
  unfold GenLimit.KleinbergWei.OrderedLanguage.prefixCount
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, hAB hi.2⟩

lemma prefixRatio_mono (K : OrderedLanguage) {A B : Language} (hAB : A ⊆ B) (n : ℕ) :
    K.prefixRatio A n ≤ K.prefixRatio B n := by
  unfold GenLimit.KleinbergWei.OrderedLanguage.prefixRatio
  by_cases hn : n = 0
  · simp [hn]
  · rw [if_neg hn, if_neg hn]
    exact div_le_div_of_nonneg_right (by exact_mod_cast prefixCount_mono K hAB n) (by positivity)

lemma scored_prefixRatio_tendsto_zero (gen : FeedbackGenerator) :
    Tendsto ((orderedTarget gen).prefixRatio
      (scored (adversarialTarget gen) (adversarialTranscript gen).presentation
        (adversarialTranscript gen).output)) atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (prefixRatio_core_tendsto_zero gen)
  · intro n
    unfold GenLimit.KleinbergWei.OrderedLanguage.prefixRatio
    split <;> positivity
  · intro n
    exact prefixRatio_mono (orderedTarget gen) (scored_subset_core gen) n

lemma scored_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity
      (scored (adversarialTarget gen) (adversarialTranscript gen).presentation
        (adversarialTranscript gen).output) = 0 := by
  unfold GenLimit.KleinbergWei.OrderedLanguage.upperDensity
  exact (scored_prefixRatio_tendsto_zero gen).limsup_eq

end
end S2BProof

open Stage3S2B

theorem stage3_result : Stage3S2B.MainClaim := by
  refine ⟨S2BProof.target_uncountable, S2BProof.uniform_generation, ?_⟩
  intro gen _hgen
  refine ⟨S2BProof.adversarialTarget gen, S2BProof.target_mem_class gen,
    S2BProof.adversarialPresenter gen, S2BProof.adversarialTranscript gen,
    S2BProof.orderedTarget gen, ?_⟩
  exact ⟨rfl, S2BProof.orderedTarget_strictMono gen, S2BProof.presented_by gen,
    S2BProof.follows_protocol gen, S2BProof.clean gen, S2BProof.presentation_injective gen,
    S2BProof.complete gen, S2BProof.scored_upperDensity_zero gen⟩
