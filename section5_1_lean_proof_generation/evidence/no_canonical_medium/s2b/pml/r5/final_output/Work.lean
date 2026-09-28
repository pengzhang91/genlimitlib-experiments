import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Set.Card

open Set

namespace Stage3Work

open Stage3S2B

noncomputable section

/-- Odd numbers above one; these are never powers of two. -/
def padCode (n : ℕ) : ℕ := 2 * n + 3

theorem padCode_injective : Function.Injective padCode := by
  intro a b h
  simp [padCode] at h
  omega

theorem padCode_odd (n : ℕ) : Odd (padCode n) := by
  refine ⟨n + 1, ?_⟩
  simp [padCode]
  omega

theorem padCode_not_core (n : ℕ) : padCode n ∉ core := by
  rintro ⟨k, hk⟩
  have hodd := padCode_odd n
  rcases k with _ | k
  · simp [padCode] at hk
  · have heven : Even (padCode n) := by
      rw [← hk]
      refine ⟨2 ^ k, by simp [pow_succ, Nat.mul_two]⟩
    exact (Nat.not_even_iff_odd.mpr hodd) heven

theorem padCode_mem_ordinary (n : ℕ) : padCode n ∈ ordinary := by
  exact padCode_not_core n

structure Prefix (n : ℕ) where
  x : Fin n → ℕ
  q : Fin n → Option ℕ
  a : Fin n → Option Bool
  y : Fin n → ℕ


def Prefix.empty : Prefix 0 where
  x := Fin.elim0
  q := Fin.elim0
  a := Fin.elim0
  y := Fin.elim0

def forbiddenPad {n : ℕ} (p : Prefix n) : Set ℕ :=
  {m | (∃ i, p.x i = padCode m) ∨ (∃ i, p.q i = some (padCode m)) ∨
    (∃ i, p.y i = padCode m)}

theorem forbiddenPad_finite {n : ℕ} (p : Prefix n) : (forbiddenPad p).Finite := by
  let values : Set ℕ := Set.range p.x ∪ Set.range (fun i => (p.q i).getD 0) ∪ Set.range p.y
  have hvalues : values.Finite :=
    ((Set.finite_range p.x).union (Set.finite_range _)).union (Set.finite_range p.y)
  apply (hvalues.preimage padCode_injective.injOn).subset
  intro m hm
  change padCode m ∈ values
  rcases hm with hm | hm | hm
  · rcases hm with ⟨i, hi⟩
    exact Or.inl (Or.inl ⟨i, hi⟩)
  · rcases hm with ⟨i, hi⟩
    apply Or.inl
    apply Or.inr
    refine ⟨i, ?_⟩
    cases hq : p.q i with
    | none => simp [hq] at hi
    | some z =>
        simp [hq] at hi
        subst z
        simp [hq]
  · rcases hm with ⟨i, hi⟩
    exact Or.inr ⟨i, hi⟩

/-- The least odd code not used in the presentation and not previously queried. -/
noncomputable def nextPadIndex {n : ℕ} (p : Prefix n) : ℕ := by
  classical
  exact Nat.find (forbiddenPad_finite p).exists_notMem

theorem nextPadIndex_fresh_x {n : ℕ} (p : Prefix n) (i : Fin n) :
    p.x i ≠ padCode (nextPadIndex p) := by
  classical
  intro h
  have hnot := Nat.find_spec (forbiddenPad_finite p).exists_notMem
  change Nat.find (forbiddenPad_finite p).exists_notMem ∉ forbiddenPad p at hnot
  unfold nextPadIndex at h
  exact hnot (Or.inl ⟨i, h⟩)

theorem nextPadIndex_fresh_q {n : ℕ} (p : Prefix n) (i : Fin n) (z : ℕ)
    (hqi : p.q i = some z) : z ≠ padCode (nextPadIndex p) := by
  classical
  intro h
  subst z
  have hnot := Nat.find_spec (forbiddenPad_finite p).exists_notMem
  change Nat.find (forbiddenPad_finite p).exists_notMem ∉ forbiddenPad p at hnot
  unfold nextPadIndex at hqi
  exact hnot (Or.inr (Or.inl ⟨i, hqi⟩))

noncomputable def nextX {n : ℕ} (p : Prefix n) : ℕ := by
  classical
  exact if GenLimit.InfiniteContamination.SparseSquare n then 2 ^ Nat.sqrt n
    else padCode (nextPadIndex p)

noncomputable def extend (gen : FeedbackGenerator) {n : ℕ} (p : Prefix n) : Prefix (n+1) := by
  let xn := nextX p
  let xs : Fin (n+1) → ℕ := Fin.lastCases xn p.x
  let qn := gen.query n xs p.a
  let an := match qn with
    | none => none
    | some z => some (membershipAnswer (core ∪ Set.range xs) z)
  let as : Fin (n+1) → Option Bool := Fin.lastCases an p.a
  let yn := gen.output n xs as
  exact {
    x := xs
    q := Fin.lastCases qn p.q
    a := as
    y := Fin.lastCases yn p.y
  }

noncomputable def runPrefix (gen : FeedbackGenerator) : (n : ℕ) → Prefix n
  | 0 => Prefix.empty
  | n+1 => extend gen (runPrefix gen n)

noncomputable def runTranscript (gen : FeedbackGenerator) : Transcript where
  presentation t := (runPrefix gen (t+1)).x (Fin.last t)
  query t := (runPrefix gen (t+1)).q (Fin.last t)
  answer t := (runPrefix gen (t+1)).a (Fin.last t)
  output t := (runPrefix gen (t+1)).y (Fin.last t)

def encodeTarget (S : Set ℕ) : Language := core ∪ padCode '' S

theorem encodeTarget_mem (S : Set ℕ) : encodeTarget S ∈ targetClass := by
  refine ⟨padCode '' S, ?_, rfl⟩
  rintro z ⟨n, hn, rfl⟩
  exact padCode_mem_ordinary n

theorem encodeTarget_injective : Function.Injective encodeTarget := by
  intro S T hST
  ext n
  have hpadS : padCode n ∈ encodeTarget S ↔ n ∈ S := by
    constructor
    · intro h
      rcases h with hcore | ⟨m, hm, hmn⟩
      · exact False.elim (padCode_not_core n hcore)
      · exact padCode_injective hmn ▸ hm
    · intro hn
      exact Or.inr ⟨n, hn, rfl⟩
  have hpadT : padCode n ∈ encodeTarget T ↔ n ∈ T := by
    constructor
    · intro h
      rcases h with hcore | ⟨m, hm, hmn⟩
      · exact False.elim (padCode_not_core n hcore)
      · exact padCode_injective hmn ▸ hm
    · intro hn
      exact Or.inr ⟨n, hn, rfl⟩
  rw [← hpadS, ← hpadT, hST]

theorem targetClass_not_countable : ¬ targetClass.Countable := by
  intro hcount
  have hpre := hcount.preimage encodeTarget_injective
  have hpreUniv : encodeTarget ⁻¹' targetClass = Set.univ := by
    ext S
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    exact encodeTarget_mem S
  rw [hpreUniv] at hpre
  haveI : Countable (Set ℕ) := Set.countable_univ_iff.mp hpre
  obtain ⟨f, hf⟩ := exists_surjective_nat (Set ℕ)
  exact Function.cantor_surjective f hf

theorem uniform_without_samples : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun n => 2 ^ n, (Nat.pow_right_injective (by omega)), 0, ?_⟩
  intro K hK t _ht
  rcases hK with ⟨A, hA, rfl⟩
  exact Or.inl ⟨t, rfl⟩


theorem extend_x_castSucc (gen : FeedbackGenerator) {n : ℕ} (p : Prefix n) (i : Fin n) :
    (extend gen p).x i.castSucc = p.x i := by
  simp [extend]

theorem extend_q_castSucc (gen : FeedbackGenerator) {n : ℕ} (p : Prefix n) (i : Fin n) :
    (extend gen p).q i.castSucc = p.q i := by
  simp [extend]

theorem extend_a_castSucc (gen : FeedbackGenerator) {n : ℕ} (p : Prefix n) (i : Fin n) :
    (extend gen p).a i.castSucc = p.a i := by
  simp [extend]

theorem extend_y_castSucc (gen : FeedbackGenerator) {n : ℕ} (p : Prefix n) (i : Fin n) :
    (extend gen p).y i.castSucc = p.y i := by
  simp [extend]

theorem runPrefix_x (gen : FeedbackGenerator) {n : ℕ} (i : Fin n) :
    (runPrefix gen n).x i = (runTranscript gen).presentation i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · rw [runPrefix, extend_x_castSucc]
        exact ih j

theorem runPrefix_q (gen : FeedbackGenerator) {n : ℕ} (i : Fin n) :
    (runPrefix gen n).q i = (runTranscript gen).query i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · rw [runPrefix, extend_q_castSucc]
        exact ih j

theorem runPrefix_a (gen : FeedbackGenerator) {n : ℕ} (i : Fin n) :
    (runPrefix gen n).a i = (runTranscript gen).answer i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · rw [runPrefix, extend_a_castSucc]
        exact ih j

theorem runPrefix_y (gen : FeedbackGenerator) {n : ℕ} (i : Fin n) :
    (runPrefix gen n).y i = (runTranscript gen).output i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · rw [runPrefix, extend_y_castSucc]
        exact ih j


theorem nextPadIndex_fresh_y {n : ℕ} (p : Prefix n) (i : Fin n) :
    p.y i ≠ padCode (nextPadIndex p) := by
  classical
  intro h
  have hnot := Nat.find_spec (forbiddenPad_finite p).exists_notMem
  change Nat.find (forbiddenPad_finite p).exists_notMem ∉ forbiddenPad p at hnot
  unfold nextPadIndex at h
  exact hnot (Or.inr (Or.inr ⟨i, h⟩))

theorem presentation_eq_nextX (gen : FeedbackGenerator) (t : ℕ) :
    (runTranscript gen).presentation t = nextX (runPrefix gen t) := by
  simp [runTranscript, runPrefix, extend]

theorem presentation_of_square (gen : FeedbackGenerator) {t : ℕ}
    (ht : GenLimit.InfiniteContamination.SparseSquare t) :
    (runTranscript gen).presentation t = 2 ^ Nat.sqrt t := by
  rw [presentation_eq_nextX]
  simp [nextX, ht]

theorem presentation_of_nonsquare (gen : FeedbackGenerator) {t : ℕ}
    (ht : ¬ GenLimit.InfiniteContamination.SparseSquare t) :
    (runTranscript gen).presentation t = padCode (nextPadIndex (runPrefix gen t)) := by
  rw [presentation_eq_nextX]
  simp [nextX, ht]

theorem core_subset_target (gen : FeedbackGenerator) :
    core ⊆ Set.range (runTranscript gen).presentation := by
  rintro z ⟨k, rfl⟩
  refine ⟨k * k, ?_⟩
  rw [presentation_of_square gen (GenLimit.InfiniteContamination.sparseSquare_mul_self k)]
  rw [Nat.sqrt_eq]

theorem runTranscript_presentation_injective (gen : FeedbackGenerator) :
    Function.Injective (runTranscript gen).presentation := by
  suffices hne : ∀ {m n : ℕ}, m < n →
      (runTranscript gen).presentation m ≠ (runTranscript gen).presentation n by
    intro m n hmn
    rcases lt_trichotomy m n with hlt | heq | hgt
    · exact False.elim (hne hlt hmn)
    · exact heq
    · exact False.elim (hne hgt hmn.symm)
  intro m n hlt
  by_cases hn : GenLimit.InfiniteContamination.SparseSquare n
  · by_cases hm : GenLimit.InfiniteContamination.SparseSquare m
    · rw [presentation_of_square gen hm, presentation_of_square gen hn]
      intro hpow
      have hsqrt : Nat.sqrt m = Nat.sqrt n := Nat.pow_right_injective (by omega) hpow
      have hmEq := (GenLimit.InfiniteContamination.sparseSquare_iff_sqrt m).mp hm
      have hnEq := (GenLimit.InfiniteContamination.sparseSquare_iff_sqrt n).mp hn
      apply Nat.ne_of_lt hlt
      calc
        m = Nat.sqrt m * Nat.sqrt m := hmEq.symm
        _ = Nat.sqrt n * Nat.sqrt n := by rw [hsqrt]
        _ = n := hnEq
    · rw [presentation_of_nonsquare gen hm, presentation_of_square gen hn]
      intro h
      exact padCode_not_core _ ⟨Nat.sqrt n, h.symm⟩
  · rw [presentation_of_nonsquare gen hn]
    have hfresh := nextPadIndex_fresh_x (runPrefix gen n) ⟨m, hlt⟩
    intro h
    apply hfresh
    rw [runPrefix_x]
    exact h

def diagonalTarget (gen : FeedbackGenerator) : Language :=
  Set.range (runTranscript gen).presentation

theorem diagonalTarget_mem (gen : FeedbackGenerator) : diagonalTarget gen ∈ targetClass := by
  refine ⟨diagonalTarget gen \ core, ?_, ?_⟩
  · intro z hz
    exact hz.2
  · ext z
    constructor
    · intro hz
      by_cases hc : z ∈ core
      · exact Or.inl hc
      · exact Or.inr ⟨hz, hc⟩
    · intro hz
      rcases hz with hz | hz
      · exact core_subset_target gen hz
      · exact hz.1

theorem no_future_query_presentation (gen : FeedbackGenerator) {t s z : ℕ}
    (hts : t < s) (hq : (runTranscript gen).query t = some z)
    (hz : z ∉ core) : (runTranscript gen).presentation s ≠ z := by
  by_cases hs : GenLimit.InfiniteContamination.SparseSquare s
  · intro heq
    apply hz
    rw [presentation_of_square gen hs] at heq
    exact ⟨Nat.sqrt s, heq⟩
  · rw [presentation_of_nonsquare gen hs]
    have hfresh := nextPadIndex_fresh_q (runPrefix gen s) ⟨t, hts⟩ z
    intro heq
    apply (hfresh (by rw [runPrefix_q]; exact hq))
    exact heq.symm

theorem no_future_output_presentation (gen : FeedbackGenerator) {t s : ℕ}
    (hts : t < s) (hz : (runTranscript gen).output t ∉ core) :
    (runTranscript gen).presentation s ≠ (runTranscript gen).output t := by
  by_cases hs : GenLimit.InfiniteContamination.SparseSquare s
  · intro heq
    apply hz
    rw [presentation_of_square gen hs] at heq
    exact ⟨Nat.sqrt s, heq⟩
  · rw [presentation_of_nonsquare gen hs]
    have hfresh := nextPadIndex_fresh_y (runPrefix gen s) ⟨t, hts⟩
    rw [runPrefix_y] at hfresh
    exact hfresh.symm

theorem query_membership_equiv (gen : FeedbackGenerator) (t z : ℕ)
    (hq : (runTranscript gen).query t = some z) :
    z ∈ diagonalTarget gen ↔ z ∈ core ∪ Set.range (runPrefix gen (t+1)).x := by
  constructor
  · rintro ⟨s, hs⟩
    by_cases hst : s ≤ t
    · exact Or.inr ⟨⟨s, Nat.lt_succ_iff.mpr hst⟩, by rw [runPrefix_x]; exact hs⟩
    · by_cases hz : z ∈ core
      · exact Or.inl hz
      · exact False.elim (no_future_query_presentation gen (Nat.lt_of_not_ge hst) hq hz hs)
  · intro hz
    rcases hz with hz | ⟨i, hi⟩
    · exact core_subset_target gen hz
    · refine ⟨i, ?_⟩
      rw [← runPrefix_x]
      exact hi


theorem transcript_query_eq (gen : FeedbackGenerator) (t : ℕ) :
    (runTranscript gen).query t = gen.query t (runPrefix gen (t+1)).x (runPrefix gen t).a := by
  simp [runTranscript, runPrefix, extend]

theorem transcript_answer_eq (gen : FeedbackGenerator) (t : ℕ) :
    (runTranscript gen).answer t =
      match (runTranscript gen).query t with
      | none => none
      | some z => some (membershipAnswer (core ∪ Set.range (runPrefix gen (t+1)).x) z) := by
  rw [transcript_query_eq]
  simp [runTranscript, runPrefix, extend]

theorem transcript_output_eq (gen : FeedbackGenerator) (t : ℕ) :
    (runTranscript gen).output t = gen.output t (runPrefix gen (t+1)).x
      (runPrefix gen (t+1)).a := by
  simp [runTranscript, runPrefix, extend]

theorem membershipAnswer_congr {K L : Language} {z : ℕ} (h : z ∈ K ↔ z ∈ L) :
    membershipAnswer K z = membershipAnswer L z := by
  unfold membershipAnswer
  rw [propext h]

theorem runTranscript_follows (gen : FeedbackGenerator) :
    FollowsProtocol gen (diagonalTarget gen) (runTranscript gen) := by
  intro t
  constructor
  · rw [transcript_query_eq]
    congr 2
    · funext i
      exact runPrefix_x gen i
    · funext i
      exact runPrefix_a gen i
  constructor
  · rw [transcript_answer_eq]
    cases hq : (runTranscript gen).query t with
    | none => rfl
    | some z =>
        simp only
        apply congrArg some
        exact membershipAnswer_congr (query_membership_equiv gen t z hq).symm
  · rw [transcript_output_eq]
    congr 2
    · funext i
      exact runPrefix_x gen i
    · funext i
      exact runPrefix_a gen i

def replayPresenter (gen : FeedbackGenerator) : CausalPresenter where
  next t _ _ _ _ := (runTranscript gen).presentation t

theorem replay_presented (gen : FeedbackGenerator) :
    PresentedBy (replayPresenter gen) (runTranscript gen) := by
  intro t
  rfl

theorem diagonal_clean (gen : FeedbackGenerator) :
    Clean (runTranscript gen).presentation (diagonalTarget gen) := by
  intro t
  exact ⟨t, rfl⟩

theorem diagonal_complete (gen : FeedbackGenerator) :
    Complete (runTranscript gen).presentation (diagonalTarget gen) := by
  intro z hz
  exact hz

theorem eventual_output_core (gen : FeedbackGenerator)
    (hgen : UniversallyEventuallyValidFresh gen) :
    ∃ T, ∀ t, T ≤ t → (runTranscript gen).output t ∈ core := by
  obtain ⟨T, hT⟩ := hgen (diagonalTarget gen) (diagonalTarget_mem gen)
    (runTranscript gen) (runTranscript_follows gen) (diagonal_clean gen)
    (runTranscript_presentation_injective gen) (diagonal_complete gen)
  refine ⟨T, fun t ht => ?_⟩
  obtain ⟨hout, hfresh⟩ := hT t ht
  by_contra hcore
  rcases hout with ⟨s, hs⟩
  have hts : t < s := by
    by_contra hnot
    apply hfresh
    exact ⟨s, Nat.le_of_not_gt hnot, hs⟩
  exact no_future_output_presentation gen hts hcore hs

def earlyOutputs (gen : FeedbackGenerator) (T : ℕ) : Set ℕ :=
  Set.range (fun i : Fin T => (runTranscript gen).output i)

theorem earlyOutputs_finite (gen : FeedbackGenerator) (T : ℕ) :
    (earlyOutputs gen T).Finite := Set.finite_range _

theorem scored_subset_core_union_early (gen : FeedbackGenerator) (T : ℕ)
    (hT : ∀ t, T ≤ t → (runTranscript gen).output t ∈ core) :
    scored (diagonalTarget gen) (runTranscript gen).presentation
      (runTranscript gen).output ⊆ core ∪ earlyOutputs gen T := by
  intro z hz
  rcases hz.2 with ⟨t, ht, _⟩
  by_cases hlarge : T ≤ t
  · exact Or.inl (ht ▸ hT t hlarge)
  · exact Or.inr ⟨⟨t, Nat.lt_of_not_ge hlarge⟩, ht⟩


theorem diagonal_legal_and_sparse (gen : FeedbackGenerator)
    (hgen : UniversallyEventuallyValidFresh gen) :
    ∃ K : Language, K ∈ targetClass ∧ ∃ presenter : CausalPresenter, ∃ tr : Transcript,
      PresentedBy presenter tr ∧ FollowsProtocol gen K tr ∧
      Clean tr.presentation K ∧ Function.Injective tr.presentation ∧
      Complete tr.presentation K ∧
      ∃ F : Language, F.Finite ∧ scored K tr.presentation tr.output ⊆ core ∪ F := by
  obtain ⟨T, hT⟩ := eventual_output_core gen hgen
  refine ⟨diagonalTarget gen, diagonalTarget_mem gen, replayPresenter gen,
    runTranscript gen, replay_presented gen, runTranscript_follows gen,
    diagonal_clean gen, runTranscript_presentation_injective gen,
    diagonal_complete gen, earlyOutputs gen T, earlyOutputs_finite gen T, ?_⟩
  exact scored_subset_core_union_early gen T hT

-- The remaining proof develops the coherence, truthfulness, and density lemmas.

end

end Stage3Work

open Stage3Work

theorem stage3_result : Stage3S2B.MainClaim := by
  refine ⟨targetClass_not_countable, uniform_without_samples, ?_⟩
  sorry
