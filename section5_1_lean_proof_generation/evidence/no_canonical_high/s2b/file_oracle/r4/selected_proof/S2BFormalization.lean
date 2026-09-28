import Stage3Model
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import GenLimit.Paper39_DenseGeneration.Abstract.Density
import Mathlib.Data.Nat.Nth

open Set Function Filter

namespace Stage3S2BProof

open Stage3S2B

lemma core_injective : Function.Injective (fun k : ℕ => 2 ^ k) :=
  Nat.pow_right_injective (by omega)

lemma core_subset_target {K : Language} (hK : K ∈ targetClass) : core ⊆ K := by
  obtain ⟨A, hA, rfl⟩ := hK
  exact Set.subset_union_left

lemma uniform_without_samples : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun k => 2 ^ k, core_injective, 0, ?_⟩
  intro K hK t _
  exact core_subset_target hK ⟨t, rfl⟩

def oddCode (n : ℕ) : ℕ := 2 * n + 3

lemma oddCode_injective : Function.Injective oddCode := by
  intro m n h
  simp [oddCode] at h
  omega

lemma oddCode_not_core (n : ℕ) : oddCode n ∉ core := by
  rintro ⟨k, hk⟩
  have hodd : Odd (oddCode n) := by
    exact ⟨n + 1, by simp [oddCode]; omega⟩
  cases k with
  | zero => simp [oddCode] at hk
  | succ k =>
      have heven : Even (2 ^ (k + 1)) := by
        refine ⟨2 ^ k, ?_⟩
        simp [pow_succ, Nat.mul_comm, two_mul]
      exact (Nat.not_even_iff_odd.mpr hodd) (hk ▸ heven)

def encodeTarget (A : Set ℕ) : Language :=
  core ∪ oddCode '' A

lemma encodeTarget_mem (A : Set ℕ) : encodeTarget A ∈ targetClass := by
  refine ⟨oddCode '' A, ?_, rfl⟩
  intro z hz
  obtain ⟨n, hn, rfl⟩ := hz
  exact oddCode_not_core n

lemma encodeTarget_injective : Function.Injective encodeTarget := by
  intro A B hAB
  ext n
  have hnot : oddCode n ∉ core := oddCode_not_core n
  have hA : oddCode n ∈ encodeTarget A ↔ n ∈ A := by
    simp [encodeTarget, hnot, oddCode_injective.eq_iff]
  have hB : oddCode n ∈ encodeTarget B ↔ n ∈ B := by
    simp [encodeTarget, hnot, oddCode_injective.eq_iff]
  rw [← hA, hAB, hB]

lemma targetClass_not_countable : ¬ targetClass.Countable := by
  intro hcount
  letI : Countable targetClass := hcount
  let f : Set ℕ → targetClass := fun A => ⟨encodeTarget A, encodeTarget_mem A⟩
  have hf : Function.Injective f := by
    intro A B h
    apply encodeTarget_injective
    exact congrArg Subtype.val h
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ hf.countable


@[ext] structure Prefix (t : ℕ) where
  presentation : Fin t → ℕ
  query : Fin t → Option ℕ
  answer : Fin t → Option Bool
  output : Fin t → ℕ

noncomputable def appendFin {t : ℕ} {α : Type*} (f : Fin t → α) (a : α) :
    Fin (t + 1) → α :=
  Fin.lastCases a f

noncomputable def usedValues {t : ℕ} (p : Prefix t) : Finset ℕ := by
  classical
  exact (Finset.univ.image p.presentation) ∪
    (Finset.univ.image fun i => (p.query i).getD 0) ∪
    (Finset.univ.image p.output)

lemma usedValues_card_le {t : ℕ} (p : Prefix t) : (usedValues p).card ≤ 3 * t := by
  classical
  unfold usedValues
  let X := Finset.univ.image p.presentation
  let Q := Finset.univ.image fun i => (p.query i).getD 0
  let Y := Finset.univ.image p.output
  have hX : X.card ≤ t := by
    simpa [X] using Finset.card_image_le (s := (Finset.univ : Finset (Fin t)))
  have hQ : Q.card ≤ t := by
    simpa [Q] using Finset.card_image_le (s := (Finset.univ : Finset (Fin t)))
  have hY : Y.card ≤ t := by
    simpa [Y] using Finset.card_image_le (s := (Finset.univ : Finset (Fin t)))
  calc
    (X ∪ Q ∪ Y).card ≤ (X ∪ Q).card + Y.card := Finset.card_union_le _ _
    _ ≤ (X.card + Q.card) + Y.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ t + t + t := by omega
    _ = 3 * t := by omega

lemma exists_unused_oddCode (U : Finset ℕ) : ∃ n, oddCode n ∉ U := by
  obtain ⟨z, ⟨n, rfl⟩, hn⟩ :=
    (Set.infinite_range_of_injective oddCode_injective).exists_not_mem_finset U
  exact ⟨n, hn⟩

noncomputable def missingIndex (U : Finset ℕ) : ℕ :=
  Nat.find (exists_unused_oddCode U)

lemma missingIndex_spec (U : Finset ℕ) : oddCode (missingIndex U) ∉ U := by
  exact Nat.find_spec (exists_unused_oddCode U)

lemma missingIndex_le_card (U : Finset ℕ) : missingIndex U ≤ U.card := by
  classical
  let candidates := (Finset.range (U.card + 1)).image oddCode
  have hcand : candidates.card = U.card + 1 := by
    simp [candidates, Finset.card_image_of_injective _ oddCode_injective]
  obtain ⟨z, hzCand, hzU⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card (s := U) (t := candidates) (by omega)
  simp only [candidates, Finset.mem_image, Finset.mem_range] at hzCand
  obtain ⟨n, hn, rfl⟩ := hzCand
  exact (Nat.find_min' (exists_unused_oddCode U) hzU).trans (by omega)

noncomputable def nextPresentation {t : ℕ} (p : Prefix t) : ℕ :=
  if h : Even t then 2 ^ (t / 2) else oddCode (missingIndex (usedValues p))

noncomputable def answerNow {t : ℕ} (x : Fin (t + 1) → ℕ)
    (q : Option ℕ) : Option Bool := by
  classical
  exact match q with
    | none => none
    | some z => some (decide (z ∈ core ∨ ∃ i, x i = z))

noncomputable def step (gen : FeedbackGenerator) {t : ℕ} (p : Prefix t) : Prefix (t + 1) := by
  let xval := nextPresentation p
  let x := appendFin p.presentation xval
  let qval := gen.query t x p.answer
  let q := appendFin p.query qval
  let aval := answerNow x qval
  let a := appendFin p.answer aval
  let yval := gen.output t x a
  let y := appendFin p.output yval
  exact ⟨x, q, a, y⟩

noncomputable def runPrefix (gen : FeedbackGenerator) : (t : ℕ) → Prefix t
  | 0 => ⟨Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0⟩
  | t + 1 => step gen (runPrefix gen t)

noncomputable def runPresentation (gen : FeedbackGenerator) (t : ℕ) : ℕ :=
  nextPresentation (runPrefix gen t)

noncomputable def runQuery (gen : FeedbackGenerator) (t : ℕ) : Option ℕ :=
  gen.query t (appendFin (runPrefix gen t).presentation (runPresentation gen t))
    (runPrefix gen t).answer

noncomputable def runAnswer (gen : FeedbackGenerator) (t : ℕ) : Option Bool :=
  answerNow (appendFin (runPrefix gen t).presentation (runPresentation gen t))
    (runQuery gen t)

noncomputable def runOutput (gen : FeedbackGenerator) (t : ℕ) : ℕ :=
  gen.output t (appendFin (runPrefix gen t).presentation (runPresentation gen t))
    (appendFin (runPrefix gen t).answer (runAnswer gen t))

noncomputable def runTranscript (gen : FeedbackGenerator) : Transcript where
  presentation := runPresentation gen
  query := runQuery gen
  answer := runAnswer gen
  output := runOutput gen



@[simp] lemma appendFin_last {t : ℕ} {α : Type*} (f : Fin t → α) (a : α) :
    appendFin f a (Fin.last t) = a := by
  simp [appendFin]

@[simp] lemma appendFin_castSucc {t : ℕ} {α : Type*} (f : Fin t → α) (a : α)
    (i : Fin t) : appendFin f a i.castSucc = f i := by
  simp [appendFin]

lemma runPrefix_presentation (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (runPrefix gen t).presentation i = runPresentation gen i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [runPrefix, step, runPresentation]
      · simpa [runPrefix, step] using ih j

lemma runPrefix_query (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (runPrefix gen t).query i = runQuery gen i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [runPrefix, step, runQuery, runPresentation]
      · simpa [runPrefix, step] using ih j

lemma runPrefix_answer (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (runPrefix gen t).answer i = runAnswer gen i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [runPrefix, step, runAnswer, runQuery, runPresentation]
      · simpa [runPrefix, step] using ih j

lemma runPrefix_output (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (runPrefix gen t).output i = runOutput gen i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [runPrefix, step, runOutput, runAnswer, runQuery, runPresentation]
      · simpa [runPrefix, step] using ih j



noncomputable def runPresenter (gen : FeedbackGenerator) : CausalPresenter where
  next t x q a y := nextPresentation ⟨x, q, a, y⟩

noncomputable def runTarget (gen : FeedbackGenerator) : Language :=
  Set.range (runPresentation gen)

lemma runPresentation_of_even (gen : FeedbackGenerator) {t : ℕ} (ht : Even t) :
    runPresentation gen t = 2 ^ (t / 2) := by
  simp [runPresentation, nextPresentation, ht]

lemma runPresentation_of_not_even (gen : FeedbackGenerator) {t : ℕ} (ht : ¬ Even t) :
    runPresentation gen t = oddCode (missingIndex (usedValues (runPrefix gen t))) := by
  simp [runPresentation, nextPresentation, ht]

lemma runPresentation_not_core_of_not_even (gen : FeedbackGenerator) {t : ℕ}
    (ht : ¬ Even t) : runPresentation gen t ∉ core := by
  rw [runPresentation_of_not_even gen ht]
  exact oddCode_not_core _

lemma runPresentation_not_used_of_not_even (gen : FeedbackGenerator) {t : ℕ}
    (ht : ¬ Even t) : runPresentation gen t ∉ usedValues (runPrefix gen t) := by
  rw [runPresentation_of_not_even gen ht]
  exact missingIndex_spec _

lemma previous_presentation_mem_used (gen : FeedbackGenerator) {t : ℕ} (i : Fin t) :
    runPresentation gen i ∈ usedValues (runPrefix gen t) := by
  classical
  unfold usedValues
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inl (Or.inl ⟨i, runPrefix_presentation gen t i⟩)

lemma previous_query_mem_used (gen : FeedbackGenerator) {t : ℕ} (i : Fin t) {z : ℕ}
    (hi : runQuery gen i = some z) : z ∈ usedValues (runPrefix gen t) := by
  classical
  unfold usedValues
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  refine Or.inl (Or.inr ⟨i, ?_⟩)
  rw [runPrefix_query gen t i, hi]
  rfl

lemma previous_output_mem_used (gen : FeedbackGenerator) {t : ℕ} (i : Fin t) :
    runOutput gen i ∈ usedValues (runPrefix gen t) := by
  classical
  unfold usedValues
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inr ⟨i, runPrefix_output gen t i⟩

lemma core_subset_runTarget (gen : FeedbackGenerator) : core ⊆ runTarget gen := by
  intro z hz
  obtain ⟨k, rfl⟩ := hz
  refine ⟨2 * k, ?_⟩
  rw [runPresentation_of_even gen ⟨k, by omega⟩]
  simp

lemma runTarget_mem_targetClass (gen : FeedbackGenerator) : runTarget gen ∈ targetClass := by
  refine ⟨runTarget gen ∩ ordinary, Set.inter_subset_right, ?_⟩
  apply Set.Subset.antisymm
  · intro z hz
    by_cases hcore : z ∈ core
    · exact Or.inl hcore
    · exact Or.inr ⟨hz, hcore⟩
  · intro z hz
    rcases hz with hz | hz
    · exact core_subset_runTarget gen hz
    · exact hz.1

lemma future_presentation_ne_query (gen : FeedbackGenerator) {t s z : ℕ}
    (hts : t < s) (hq : runQuery gen t = some z) (hz : z ∈ ordinary) :
    runPresentation gen s ≠ z := by
  by_cases hs : Even s
  · intro h
    apply hz
    rw [← h]
    rw [runPresentation_of_even gen hs]
    exact ⟨s / 2, rfl⟩
  · intro h
    apply runPresentation_not_used_of_not_even gen hs
    rw [h]
    exact previous_query_mem_used gen ⟨t, hts⟩ hq

lemma future_presentation_ne_output (gen : FeedbackGenerator) {t s : ℕ}
    (hts : t < s) (hz : runOutput gen t ∈ ordinary) :
    runPresentation gen s ≠ runOutput gen t := by
  by_cases hs : Even s
  · intro h
    apply hz
    rw [← h]
    rw [runPresentation_of_even gen hs]
    exact ⟨s / 2, rfl⟩
  · intro h
    apply runPresentation_not_used_of_not_even gen hs
    rw [h]
    exact previous_output_mem_used gen ⟨t, hts⟩

lemma runPresentation_ne_of_lt (gen : FeedbackGenerator) {s t : ℕ} (hst : s < t) :
    runPresentation gen s ≠ runPresentation gen t := by
  by_cases ht : Even t
  · rw [runPresentation_of_even gen ht]
    by_cases hs : Even s
    · intro heq
      rw [runPresentation_of_even gen hs] at heq
      have hdiv : s / 2 = t / 2 := core_injective heq
      obtain ⟨a, ha⟩ := hs
      obtain ⟨b, hb⟩ := ht
      omega
    · intro heq
      apply runPresentation_not_core_of_not_even gen hs
      rw [heq]
      exact ⟨t / 2, rfl⟩
  · intro heq
    apply runPresentation_not_used_of_not_even gen ht
    rw [← heq]
    exact previous_presentation_mem_used gen ⟨s, hst⟩

lemma runPresentation_injective (gen : FeedbackGenerator) :
    Function.Injective (runPresentation gen) := by
  intro s t hEq
  rcases lt_trichotomy s t with hst | hst | hst
  · exact (runPresentation_ne_of_lt gen hst hEq).elim
  · exact hst
  · exact (runPresentation_ne_of_lt gen hst hEq.symm).elim


noncomputable def currentPresentation (gen : FeedbackGenerator) (t : ℕ) : Fin (t + 1) → ℕ :=
  appendFin (runPrefix gen t).presentation (runPresentation gen t)

noncomputable def currentAnswer (gen : FeedbackGenerator) (t : ℕ) :
    Fin (t + 1) → Option Bool :=
  appendFin (runPrefix gen t).answer (runAnswer gen t)

lemma currentPresentation_eq (gen : FeedbackGenerator) (t : ℕ) (i : Fin (t + 1)) :
    currentPresentation gen t i = runPresentation gen i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [currentPresentation]
  · simp [currentPresentation, runPrefix_presentation]

lemma queried_mem_runTarget_iff (gen : FeedbackGenerator) {t z : ℕ}
    (hq : runQuery gen t = some z) :
    z ∈ runTarget gen ↔ z ∈ core ∨ ∃ i : Fin (t + 1), currentPresentation gen t i = z := by
  constructor
  · rintro ⟨s, hs⟩
    by_cases hcore : z ∈ core
    · exact Or.inl hcore
    · right
      by_cases hst : s ≤ t
      · exact ⟨⟨s, by omega⟩, by rw [currentPresentation_eq, hs]⟩
      · exfalso
        exact future_presentation_ne_query gen (lt_of_not_ge hst) hq hcore hs
  · rintro (hcore | ⟨i, hi⟩)
    · exact core_subset_runTarget gen hcore
    · exact ⟨i, by rw [← hi, currentPresentation_eq]⟩

lemma run_answer_truthful (gen : FeedbackGenerator) (t : ℕ) :
    runAnswer gen t = match runQuery gen t with
      | none => none
      | some z => some (membershipAnswer (runTarget gen) z) := by
  unfold runAnswer
  change answerNow (currentPresentation gen t) (runQuery gen t) = _
  cases hq : runQuery gen t with
  | none => simp [answerNow, hq]
  | some z =>
      have hiff := queried_mem_runTarget_iff gen hq
      simp [answerNow, hq, membershipAnswer, hiff]

lemma run_presented (gen : FeedbackGenerator) :
    PresentedBy (runPresenter gen) (runTranscript gen) := by
  intro t
  change runPresentation gen t = nextPresentation
    ⟨(fun i => runPresentation gen i), (fun i => runQuery gen i),
      (fun i => runAnswer gen i), (fun i => runOutput gen i)⟩
  unfold runPresentation
  have hp : runPrefix gen t =
      ⟨(fun i => runPresentation gen i), (fun i => runQuery gen i),
        (fun i => runAnswer gen i), (fun i => runOutput gen i)⟩ := by
    apply Prefix.ext <;> funext i
    · exact runPrefix_presentation gen t i
    · exact runPrefix_query gen t i
    · exact runPrefix_answer gen t i
    · exact runPrefix_output gen t i
  simp [hp, runPresentation]

lemma run_follows_protocol (gen : FeedbackGenerator) :
    FollowsProtocol gen (runTarget gen) (runTranscript gen) := by
  intro t
  refine ⟨?_, run_answer_truthful gen t, ?_⟩
  · change runQuery gen t = gen.query t
      (fun i => runPresentation gen i) (fun i => runAnswer gen i)
    unfold runQuery
    congr 2
    · funext i
      exact currentPresentation_eq gen t i
    · funext i
      exact runPrefix_answer gen t i
  · change runOutput gen t = gen.output t
      (fun i => runPresentation gen i) (fun i => runAnswer gen i)
    unfold runOutput
    congr 2
    · funext i
      exact currentPresentation_eq gen t i
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp
      · simp [runPrefix_answer]

lemma run_clean (gen : FeedbackGenerator) :
    Clean (runTranscript gen).presentation (runTarget gen) := by
  intro t
  exact ⟨t, rfl⟩

lemma run_complete (gen : FeedbackGenerator) :
    Complete (runTranscript gen).presentation (runTarget gen) := by
  intro z hz
  exact hz


lemma odd_round_bound (gen : FeedbackGenerator) (k : ℕ) :
    runPresentation gen (2 * k + 1) ≤ 12 * k + 9 := by
  have hodd : ¬ Even (2 * k + 1) := Nat.not_even_iff_odd.mpr ⟨k, by omega⟩
  rw [runPresentation_of_not_even gen hodd]
  have hmiss := missingIndex_le_card (usedValues (runPrefix gen (2 * k + 1)))
  have hcard := usedValues_card_le (runPrefix gen (2 * k + 1))
  unfold oddCode
  omega

lemma runTarget_infinite (gen : FeedbackGenerator) : (runTarget gen).Infinite := by
  exact (Set.infinite_range_of_injective core_injective).mono (core_subset_runTarget gen)

noncomputable def orderedRunTarget (gen : FeedbackGenerator) : OrderedLanguage where
  carrier := runTarget gen
  enumeration := Nat.nth (fun z => z ∈ runTarget gen)
  enumeration_injective := Nat.nth_injective (runTarget_infinite gen)
  range_enumeration := Nat.range_nth_of_infinite (runTarget_infinite gen)

lemma orderedRunTarget_strictMono (gen : FeedbackGenerator) :
    StrictMono (orderedRunTarget gen).enumeration := by
  exact Nat.nth_strictMono (runTarget_infinite gen)

lemma scored_subset_core (gen : FeedbackGenerator) :
    scored (runTarget gen) (runTranscript gen).presentation (runTranscript gen).output ⊆ core := by
  intro z hz
  rcases hz with ⟨hzK, t, hout, hfresh⟩
  by_contra hcore
  have hord : z ∈ ordinary := hcore
  change runOutput gen t = z at hout
  change z ∉ observedThrough (runPresentation gen) t at hfresh
  obtain ⟨s, hs⟩ := hzK
  by_cases hst : s ≤ t
  · apply hfresh
    exact ⟨s, hst, by simpa [runTranscript] using hs⟩
  · have hordout : runOutput gen t ∈ ordinary := by rw [hout]; exact hord
    exact (future_presentation_ne_output gen (lt_of_not_ge hst) hordout) (hs.trans hout.symm)

noncomputable def ambientCount (A : Set ℕ) (B : ℕ) : ℕ := by
  classical
  exact ((Finset.range B).filter fun z => z ∈ A).card

lemma target_count_lower (gen : FeedbackGenerator) (n : ℕ) :
    n + 1 ≤ ambientCount (runTarget gen) (12 * n + 10) := by
  classical
  unfold ambientCount
  let f : ℕ → ℕ := fun k => runPresentation gen (2 * k + 1)
  let S := (Finset.range (n + 1)).image f
  have hf : Function.Injective f := by
    apply (runPresentation_injective gen).comp
    intro a b h
    simp [f] at h
    omega
  have hcard : S.card = n + 1 := by
    simp [S, Finset.card_image_of_injective _ hf]
  rw [← hcard]
  apply Finset.card_le_card
  intro z hz
  simp only [S, Finset.mem_image, Finset.mem_range] at hz
  obtain ⟨k, hk, rfl⟩ := hz
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact lt_of_le_of_lt (odd_round_bound gen k) (by omega)
  · exact ⟨2 * k + 1, rfl⟩

lemma ordered_nth_bound (gen : FeedbackGenerator) (n : ℕ) :
    (orderedRunTarget gen).enumeration n < 12 * n + 10 := by
  classical
  apply Nat.nth_lt_of_lt_count
  rw [Nat.count_eq_card_filter_range]
  exact lt_of_lt_of_le (Nat.lt_succ_self n) (target_count_lower gen n)

lemma core_count_upper (B : ℕ) :
    ambientCount core B ≤ Nat.log2 B + 1 := by
  classical
  unfold ambientCount
  let S := (Finset.range B).filter (fun z => z ∈ core)
  let T := (Finset.range (Nat.log2 B + 1)).image (fun k : ℕ => 2 ^ k)
  have hsub : S ⊆ T := by
    intro z hz
    simp only [S, Finset.mem_filter, Finset.mem_range] at hz
    obtain ⟨k, rfl⟩ := hz.2
    simp only [T, Finset.mem_image, Finset.mem_range]
    refine ⟨k, ?_, rfl⟩
    rw [Nat.log2_eq_log_two]
    have hklog : k ≤ Nat.log 2 (2 ^ k) := Nat.le_log_of_pow_le (by omega) le_rfl
    have hmono : Nat.log 2 (2 ^ k) ≤ Nat.log 2 B := Nat.log_mono_right (Nat.le_of_lt hz.1)
    omega
  calc
    S.card ≤ T.card := Finset.card_le_card hsub
    _ ≤ (Finset.range (Nat.log2 B + 1)).card := Finset.card_image_le
    _ = Nat.log2 B + 1 := Finset.card_range _

lemma prefixCount_core_upper (gen : FeedbackGenerator) (n : ℕ) :
    (orderedRunTarget gen).prefixCount core n ≤ Nat.log2 (12 * n + 10) + 1 := by
  classical
  unfold GenLimit.KleinbergWei.OrderedLanguage.prefixCount
  let S := (Finset.range n).filter (fun i => (orderedRunTarget gen).enumeration i ∈ core)
  let T := (Finset.range (12 * n + 10)).filter (fun z => z ∈ core)
  have hcardImage : (S.image (orderedRunTarget gen).enumeration).card = S.card := by
    exact Finset.card_image_of_injective _ (orderedRunTarget gen).enumeration_injective
  rw [← hcardImage]
  have hsub : S.image (orderedRunTarget gen).enumeration ⊆ T := by
    intro z hz
    simp only [Finset.mem_image, S, Finset.mem_filter, Finset.mem_range] at hz
    obtain ⟨i, ⟨hi, hicore⟩, rfl⟩ := hz
    simp only [T, Finset.mem_filter, Finset.mem_range]
    exact ⟨lt_of_lt_of_le (ordered_nth_bound gen i) (by omega), hicore⟩
  calc
    (S.image (orderedRunTarget gen).enumeration).card ≤ T.card := Finset.card_le_card hsub
    _ = ambientCount core (12 * n + 10) := by rfl
    _ ≤ Nat.log2 (12 * n + 10) + 1 := core_count_upper _

lemma log_linear_bound {n : ℕ} (hn : n ≠ 0) :
    Nat.log2 (12 * n + 10) ≤ Nat.log2 n + 5 := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  have hnPow : n < 2 ^ (Nat.log 2 n + 1) := by
    simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self (by omega : 1 < 2) n
  have hbound : 12 * n + 10 < 2 ^ (Nat.log 2 n + 6) := by
    calc
      12 * n + 10 ≤ 22 * n := by omega
      _ < 32 * 2 ^ (Nat.log 2 n + 1) := by omega
      _ = 2 ^ (Nat.log 2 n + 6) := by
        rw [show 32 = 2 ^ 5 by norm_num, ← pow_add]
        congr 1
        omega
  have hlog : Nat.log 2 (12 * n + 10) < Nat.log 2 n + 6 :=
    Nat.log_lt_of_lt_pow (by omega) hbound
  omega

lemma prefixRatio_core_tendsto_zero (gen : FeedbackGenerator) :
    Tendsto ((orderedRunTarget gen).prefixRatio core) atTop (nhds 0) := by
  apply squeeze_zero
    (fun n => (orderedRunTarget gen).prefixRatio_nonneg core n)
    (fun n => ?_)
  · simpa [Nat.add_comm] using GenLimit.tendsto_countingError_div 6
  · by_cases hn : n = 0
    · simp [hn]
    · simp only [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, hn, if_false]
      apply div_le_div_of_nonneg_right
      · exact_mod_cast (prefixCount_core_upper gen n).trans (by
          have := log_linear_bound hn
          omega)
      · positivity

lemma upperDensity_core_zero (gen : FeedbackGenerator) :
    (orderedRunTarget gen).upperDensity core = 0 := by
  exact (prefixRatio_core_tendsto_zero gen).limsup_eq

lemma upperDensity_scored_zero (gen : FeedbackGenerator) :
    (orderedRunTarget gen).upperDensity
      (scored (runTarget gen) (runTranscript gen).presentation (runTranscript gen).output) = 0 := by
  apply le_antisymm
  · calc
      (orderedRunTarget gen).upperDensity
          (scored (runTarget gen) (runTranscript gen).presentation (runTranscript gen).output) ≤
          (orderedRunTarget gen).upperDensity core :=
        (orderedRunTarget gen).upperDensity_mono (scored_subset_core gen)
      _ = 0 := upperDensity_core_zero gen
  · exact (orderedRunTarget gen).upperDensity_nonneg _

lemma negative_claim : NegativeClaim := by
  intro gen _hgen
  refine ⟨runTarget gen, runTarget_mem_targetClass gen,
    runPresenter gen, runTranscript gen, orderedRunTarget gen, ?_⟩
  refine ⟨rfl, orderedRunTarget_strictMono gen, run_presented gen,
    run_follows_protocol gen, run_clean gen, runPresentation_injective gen,
    run_complete gen, upperDensity_scored_zero gen⟩


end Stage3S2BProof

theorem stage3_result : Stage3S2B.MainClaim := by
  exact ⟨Stage3S2BProof.targetClass_not_countable,
    Stage3S2BProof.uniform_without_samples, Stage3S2BProof.negative_claim⟩
