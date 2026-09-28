import Stage3Model
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import GenLimit.Paper39_DenseGeneration.Abstract.Density
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

open Set Filter
open scoped Topology

namespace Stage3Work

open Stage3S2B

structure Round where
  x : ℕ
  q : Option ℕ
  a : Option Bool
  y : ℕ

noncomputable def blocked {t : ℕ} (x : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) : Finset ℕ := by
  classical
  exact (Finset.univ.image x) ∪
    (Finset.univ.biUnion (fun i => match q i with | none => (∅ : Finset ℕ) | some z => {z})) ∪
    (Finset.univ.image y)

lemma exists_multiple_three_not_mem (B : Finset ℕ) : ∃ n, 3 * n ∉ B := by
  by_contra h
  push_neg at h
  have hsub : (Finset.range (B.card + 1)).image (fun n => 3 * n) ⊆ B := by
    intro z hz
    simp only [Finset.mem_image, Finset.mem_range] at hz
    obtain ⟨n, hn, rfl⟩ := hz
    exact h n
  have hinj : Function.Injective (fun n : ℕ => 3 * n) := by
    intro a b hab
    exact Nat.mul_left_cancel (by omega) hab
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_range] at hc
  omega

noncomputable def freshMultiple (B : Finset ℕ) : ℕ :=
  3 * Nat.find (exists_multiple_three_not_mem B)

lemma freshMultiple_not_mem (B : Finset ℕ) : freshMultiple B ∉ B := by
  exact Nat.find_spec (exists_multiple_three_not_mem B)

lemma freshMultiple_bound (B : Finset ℕ) : freshMultiple B ≤ 3 * B.card := by
  obtain ⟨n, hnle, hn⟩ : ∃ n ≤ B.card, 3 * n ∉ B := by
    by_contra h
    push_neg at h
    have hsub : (Finset.range (B.card + 1)).image (fun n => 3 * n) ⊆ B := by
      intro z hz
      simp only [Finset.mem_image, Finset.mem_range] at hz
      obtain ⟨m, hm, rfl⟩ := hz
      exact h m (by omega)
    have hinj : Function.Injective (fun n : ℕ => 3 * n) := by
      intro a b hab
      exact Nat.mul_left_cancel (by omega) hab
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hinj, Finset.card_range] at hc
    omega
  unfold freshMultiple
  exact Nat.mul_le_mul_left 3 ((Nat.find_min' _ hn).trans hnle)

lemma three_mul_not_core (n : ℕ) : 3 * n ∉ core := by
  rintro ⟨k, hk⟩
  have hd : 3 ∣ 2 ^ k := by
    use n
  have hp : Nat.Prime 3 := by norm_num
  have := hp.dvd_of_dvd_pow hd
  norm_num at this

noncomputable def chooseX {t : ℕ} (x : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) : ℕ :=
  if t % 2 = 0 then 2 ^ (t / 2) else freshMultiple (blocked x q y)

noncomputable def runRound (gen : FeedbackGenerator) (t : ℕ) : Round := by
  classical
  let prev : Fin t → Round := fun i => runRound gen i.1
  let xprev : Fin t → ℕ := fun i => (prev i).x
  let qprev : Fin t → Option ℕ := fun i => (prev i).q
  let aprev : Fin t → Option Bool := fun i => (prev i).a
  let yprev : Fin t → ℕ := fun i => (prev i).y
  let xt := chooseX xprev qprev yprev
  let xnow : Fin (t + 1) → ℕ := Fin.lastCases xt xprev
  let qt := gen.query t xnow aprev
  let admitted : ℕ → Prop := fun z =>
    z ∈ core ∨ (t % 2 = 1 ∧ z = xt) ∨ ∃ i : Fin t, i.1 % 2 = 1 ∧ z = xprev i
  let ans : Option Bool := qt.map fun z => decide (admitted z)
  let anow : Fin (t + 1) → Option Bool := Fin.lastCases ans aprev
  exact ⟨xt, qt, ans, gen.output t xnow anow⟩
termination_by t

noncomputable def diagonalTranscript (gen : FeedbackGenerator) : Transcript where
  presentation t := (runRound gen t).x
  query t := (runRound gen t).q
  answer t := (runRound gen t).a
  output t := (runRound gen t).y

noncomputable def diagonalPresenter : CausalPresenter where
  next t x q _a y := chooseX x q y

end Stage3Work

namespace Stage3Work

open Stage3S2B

lemma encode_injective : Function.Injective
    (fun A : Set ℕ => core ∪ ((fun n : ℕ => 3 * n) '' A)) := by
  intro A B hAB
  change core ∪ ((fun n : ℕ => 3 * n) '' A) = core ∪ ((fun n : ℕ => 3 * n) '' B) at hAB
  ext n
  have hnot : 3 * n ∉ core := three_mul_not_core n
  have hmul : Function.Injective (fun m : ℕ => 3 * m) := by
    intro a b hab
    exact Nat.mul_left_cancel (by omega) hab
  have hmemA : 3 * n ∈ core ∪ ((fun m : ℕ => 3 * m) '' A) ↔ n ∈ A := by
    simp only [Set.mem_union, Set.mem_image]
    constructor
    · rintro (hc | ⟨m, hm, heq⟩)
      · exact (hnot hc).elim
      · simpa [hmul heq] using hm
    · intro hn
      exact Or.inr ⟨n, hn, rfl⟩
  have hmemB : 3 * n ∈ core ∪ ((fun m : ℕ => 3 * m) '' B) ↔ n ∈ B := by
    simp only [Set.mem_union, Set.mem_image]
    constructor
    · rintro (hc | ⟨m, hm, heq⟩)
      · exact (hnot hc).elim
      · simpa [hmul heq] using hm
    · intro hn
      exact Or.inr ⟨n, hn, rfl⟩
  constructor
  · intro hnA
    have hz : 3 * n ∈ core ∪ ((fun m : ℕ => 3 * m) '' A) := hmemA.mpr hnA
    have hz' : 3 * n ∈ core ∪ ((fun m : ℕ => 3 * m) '' B) := by
      exact hAB ▸ hz
    exact hmemB.mp hz'
  · intro hnB
    have hz : 3 * n ∈ core ∪ ((fun m : ℕ => 3 * m) '' B) := hmemB.mpr hnB
    have hz' : 3 * n ∈ core ∪ ((fun m : ℕ => 3 * m) '' A) := by
      exact hAB.symm ▸ hz
    exact hmemA.mp hz'

lemma encoded_mem_targetClass (A : Set ℕ) :
    core ∪ ((fun n : ℕ => 3 * n) '' A) ∈ targetClass := by
  refine ⟨(fun n : ℕ => 3 * n) '' A, ?_, rfl⟩
  rintro z ⟨n, hn, rfl⟩
  exact three_mul_not_core n

lemma targetClass_not_countable : ¬ targetClass.Countable := by
  intro hcount
  have hrange : Set.range (fun A : Set ℕ => core ∪ ((fun n : ℕ => 3 * n) '' A)) ⊆
      targetClass := by
    rintro K ⟨A, rfl⟩
    exact encoded_mem_targetClass A
  have hpre : (Set.univ : Set (Set ℕ)).Countable := by
    have hcRange := hcount.mono hrange
    have hcPre := hcRange.preimage encode_injective
    simpa using hcPre
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ
    (by simpa [Set.countable_univ_iff] using hpre)

lemma uniform_generation : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t => 2 ^ t, ?_, 0, ?_⟩
  · intro a b hab
    exact (Nat.pow_right_injective (by omega : 1 < 2)) hab
  · intro K hK t _ht
    obtain ⟨A, hA, rfl⟩ := hK
    exact Or.inl ⟨t, rfl⟩

end Stage3Work

namespace Stage3Work

open Stage3S2B

lemma presentation_eq (gen : FeedbackGenerator) (t : ℕ) :
    (diagonalTranscript gen).presentation t = chooseX
      (fun i : Fin t => (diagonalTranscript gen).presentation i)
      (fun i : Fin t => (diagonalTranscript gen).query i)
      (fun i : Fin t => (diagonalTranscript gen).output i) := by
  change (runRound gen t).x = chooseX
    (fun i : Fin t => (runRound gen i).x)
    (fun i : Fin t => (runRound gen i).q)
    (fun i : Fin t => (runRound gen i).y)
  rw [runRound.eq_1]

lemma query_eq (gen : FeedbackGenerator) (t : ℕ) :
    (diagonalTranscript gen).query t = gen.query t
      (fun i : Fin (t + 1) => (diagonalTranscript gen).presentation i)
      (fun i : Fin t => (diagonalTranscript gen).answer i) := by
  change (runRound gen t).q = gen.query t
    (fun i : Fin (t + 1) => (runRound gen i).x)
    (fun i : Fin t => (runRound gen i).a)
  rw [runRound.eq_1]
  change gen.query t (Fin.lastCases _ _) _ = _
  congr 2
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.lastCases_last]
    exact (congrArg Round.x (runRound.eq_1 gen t)).symm
  · rw [Fin.lastCases_castSucc]
    congr

lemma output_eq (gen : FeedbackGenerator) (t : ℕ) :
    (diagonalTranscript gen).output t = gen.output t
      (fun i : Fin (t + 1) => (diagonalTranscript gen).presentation i)
      (fun i : Fin (t + 1) => (diagonalTranscript gen).answer i) := by
  change (runRound gen t).y = gen.output t
    (fun i : Fin (t + 1) => (runRound gen i).x)
    (fun i : Fin (t + 1) => (runRound gen i).a)
  rw [runRound.eq_1]
  change gen.output t (Fin.lastCases _ _) (Fin.lastCases _ _) = _
  congr 2 <;> funext i
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.lastCases_last]
      exact (congrArg Round.x (runRound.eq_1 gen t)).symm
    · rw [Fin.lastCases_castSucc]
      congr
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.lastCases_last]
      exact (congrArg Round.a (runRound.eq_1 gen t)).symm
    · rw [Fin.lastCases_castSucc]
      congr

lemma presented_by_diagonal (gen : FeedbackGenerator) :
    PresentedBy diagonalPresenter (diagonalTranscript gen) := by
  intro t
  exact presentation_eq gen t

lemma blocked_presentation_mem {t : ℕ} (x : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) (i : Fin t) :
    x i ∈ blocked x q y := by
  classical
  simp [blocked]

lemma blocked_query_mem {t : ℕ} (x : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) (i : Fin t) {z : ℕ}
    (hi : q i = some z) : z ∈ blocked x q y := by
  classical
  simp only [blocked, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion,
    Finset.mem_univ, true_and]
  left
  right
  exact ⟨i, by simp [hi]⟩

lemma blocked_output_mem {t : ℕ} (x : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) (i : Fin t) :
    y i ∈ blocked x q y := by
  classical
  simp [blocked]

lemma odd_presentation_fresh (gen : FeedbackGenerator) {t : ℕ}
    (ht : t % 2 = 1) :
    (diagonalTranscript gen).presentation t ∉ blocked
      (fun i : Fin t => (diagonalTranscript gen).presentation i)
      (fun i : Fin t => (diagonalTranscript gen).query i)
      (fun i : Fin t => (diagonalTranscript gen).output i) := by
  rw [presentation_eq, chooseX, if_neg (by omega)]
  exact freshMultiple_not_mem _

lemma odd_presentation_not_core (gen : FeedbackGenerator) {t : ℕ}
    (ht : t % 2 = 1) : (diagonalTranscript gen).presentation t ∉ core := by
  rw [presentation_eq, chooseX, if_neg (by omega)]
  exact three_mul_not_core _

lemma even_presentation (gen : FeedbackGenerator) {t : ℕ}
    (ht : t % 2 = 0) :
    (diagonalTranscript gen).presentation t = 2 ^ (t / 2) := by
  rw [presentation_eq, chooseX, if_pos ht]

lemma presentation_ne_of_lt (gen : FeedbackGenerator) {s t : ℕ} (hlt : s < t) :
    (diagonalTranscript gen).presentation s ≠
      (diagonalTranscript gen).presentation t := by
  intro hst
  by_cases hs : s % 2 = 0
  · by_cases ht : t % 2 = 0
    · rw [even_presentation gen hs, even_presentation gen ht] at hst
      have hp := Nat.pow_right_injective (by omega : 1 < 2) hst
      have hsform : s = 2 * (s / 2) := by omega
      have htform : t = 2 * (t / 2) := by omega
      omega
    · have ht1 : t % 2 = 1 := by omega
      have hcore : (diagonalTranscript gen).presentation s ∈ core := by
        rw [even_presentation gen hs]
        exact ⟨s / 2, rfl⟩
      rw [hst] at hcore
      exact odd_presentation_not_core gen ht1 hcore
  · have hs1 : s % 2 = 1 := by omega
    by_cases ht : t % 2 = 0
    · have hcore : (diagonalTranscript gen).presentation t ∈ core := by
        rw [even_presentation gen ht]
        exact ⟨t / 2, rfl⟩
      rw [← hst] at hcore
      exact odd_presentation_not_core gen hs1 hcore
    · have ht1 : t % 2 = 1 := by omega
      have hmem : (diagonalTranscript gen).presentation s ∈ blocked
          (fun i : Fin t => (diagonalTranscript gen).presentation i)
          (fun i : Fin t => (diagonalTranscript gen).query i)
          (fun i : Fin t => (diagonalTranscript gen).output i) := by
        exact blocked_presentation_mem
          (fun i : Fin t => (diagonalTranscript gen).presentation i)
          (fun i : Fin t => (diagonalTranscript gen).query i)
          (fun i : Fin t => (diagonalTranscript gen).output i) ⟨s, hlt⟩
      have hfresh := odd_presentation_fresh gen ht1
      exact hfresh (hst ▸ hmem)

lemma presentation_injective (gen : FeedbackGenerator) :
    Function.Injective (diagonalTranscript gen).presentation := by
  intro s t hst
  rcases lt_trichotomy s t with hlt | heq | hgt
  · exact (presentation_ne_of_lt gen hlt hst).elim
  · exact heq
  · exact (presentation_ne_of_lt gen hgt hst.symm).elim

noncomputable def admitted (gen : FeedbackGenerator) : Set ℕ :=
  {z | ∃ t, t % 2 = 1 ∧ (diagonalTranscript gen).presentation t = z}

noncomputable def diagonalTarget (gen : FeedbackGenerator) : Language :=
  core ∪ admitted gen

lemma diagonalTarget_mem (gen : FeedbackGenerator) :
    diagonalTarget gen ∈ targetClass := by
  refine ⟨admitted gen, ?_, rfl⟩
  rintro z ⟨t, ht, rfl⟩
  exact odd_presentation_not_core gen ht

lemma diagonal_clean (gen : FeedbackGenerator) :
    Clean (diagonalTranscript gen).presentation (diagonalTarget gen) := by
  intro t
  by_cases ht : t % 2 = 0
  · left
    rw [even_presentation gen ht]
    exact ⟨t / 2, rfl⟩
  · right
    exact ⟨t, by omega, rfl⟩

lemma diagonal_complete (gen : FeedbackGenerator) :
    Complete (diagonalTranscript gen).presentation (diagonalTarget gen) := by
  intro z hz
  rcases hz with ⟨k, rfl⟩ | ⟨t, ht, rfl⟩
  · refine ⟨2 * k, ?_⟩
    rw [even_presentation gen (by omega)]
    congr
    omega
  · exact ⟨t, rfl⟩

end Stage3Work

namespace Stage3Work

open Stage3S2B

lemma query_blocks_future (gen : FeedbackGenerator) {s t z : ℕ}
    (hst : s < t) (hq : (diagonalTranscript gen).query s = some z)
    (ht : t % 2 = 1) : (diagonalTranscript gen).presentation t ≠ z := by
  intro hx
  have hmem : z ∈ blocked
      (fun i : Fin t => (diagonalTranscript gen).presentation i)
      (fun i : Fin t => (diagonalTranscript gen).query i)
      (fun i : Fin t => (diagonalTranscript gen).output i) := by
    exact blocked_query_mem
      (fun i : Fin t => (diagonalTranscript gen).presentation i)
      (fun i : Fin t => (diagonalTranscript gen).query i)
      (fun i : Fin t => (diagonalTranscript gen).output i) ⟨s, hst⟩ hq
  exact odd_presentation_fresh gen ht (hx ▸ hmem)

lemma output_blocks_future (gen : FeedbackGenerator) {s t : ℕ}
    (hst : s < t) (ht : t % 2 = 1) :
    (diagonalTranscript gen).presentation t ≠
      (diagonalTranscript gen).output s := by
  intro hx
  have hmem : (diagonalTranscript gen).output s ∈ blocked
      (fun i : Fin t => (diagonalTranscript gen).presentation i)
      (fun i : Fin t => (diagonalTranscript gen).query i)
      (fun i : Fin t => (diagonalTranscript gen).output i) := by
    exact blocked_output_mem
      (fun i : Fin t => (diagonalTranscript gen).presentation i)
      (fun i : Fin t => (diagonalTranscript gen).query i)
      (fun i : Fin t => (diagonalTranscript gen).output i) ⟨s, hst⟩
  exact odd_presentation_fresh gen ht (hx ▸ hmem)

def locallyAdmitted (gen : FeedbackGenerator) (t z : ℕ) : Prop :=
  z ∈ core ∨
  (t % 2 = 1 ∧ z = (diagonalTranscript gen).presentation t) ∨
  ∃ s, s < t ∧ s % 2 = 1 ∧ z = (diagonalTranscript gen).presentation s

lemma answer_formula (gen : FeedbackGenerator) (t : ℕ) :
    (diagonalTranscript gen).answer t =
      Option.map (fun z => @decide (locallyAdmitted gen t z) (Classical.propDecidable _))
        ((diagonalTranscript gen).query t) := by
  classical
  change (runRound gen t).a =
    Option.map (fun z => @decide (locallyAdmitted gen t z) (Classical.propDecidable _))
      (runRound gen t).q
  rw [runRound.eq_1]
  dsimp only
  congr 2
  funext z
  congr 1
  apply propext
  simp only [locallyAdmitted]
  constructor
  · rintro (hz | ⟨ht, hz⟩ | ⟨i, hi, hz⟩)
    · exact Or.inl hz
    · exact Or.inr (Or.inl ⟨ht, hz.trans (presentation_eq gen t).symm⟩)
    · exact Or.inr (Or.inr ⟨i.1, i.2, hi, hz⟩)
  · rintro (hz | ⟨ht, hz⟩ | ⟨i, hit, hi, hz⟩)
    · exact Or.inl hz
    · exact Or.inr (Or.inl ⟨ht, hz.trans (presentation_eq gen t)⟩)
    · exact Or.inr (Or.inr ⟨⟨i, hit⟩, hi, hz⟩)

lemma locallyAdmitted_iff_target_of_query (gen : FeedbackGenerator) {t z : ℕ}
    (hq : (diagonalTranscript gen).query t = some z) :
    locallyAdmitted gen t z ↔ z ∈ diagonalTarget gen := by
  constructor
  · rintro (hz | ⟨ht, hz⟩ | ⟨s, hst, hs, hz⟩)
    · exact Or.inl hz
    · exact Or.inr ⟨t, ht, hz.symm⟩
    · exact Or.inr ⟨s, hs, hz.symm⟩
  · rintro (hz | ⟨s, hs, hz⟩)
    · exact Or.inl hz
    · rcases lt_trichotomy s t with hst | rfl | hts
      · exact Or.inr (Or.inr ⟨s, hst, hs, hz.symm⟩)
      · exact Or.inr (Or.inl ⟨hs, hz.symm⟩)
      · exact (query_blocks_future gen hts hq hs hz).elim

lemma answer_correct (gen : FeedbackGenerator) (t : ℕ) :
    (diagonalTranscript gen).answer t =
      match (diagonalTranscript gen).query t with
      | none => none
      | some z => some (membershipAnswer (diagonalTarget gen) z) := by
  classical
  rw [answer_formula]
  cases hq : (diagonalTranscript gen).query t with
  | none => simp [hq]
  | some z =>
      simp only [hq, Option.map_some]
      congr 1
      simp only [membershipAnswer]
      congr 1
      apply propext
      exact locallyAdmitted_iff_target_of_query gen hq

lemma follows_diagonal (gen : FeedbackGenerator) :
    FollowsProtocol gen (diagonalTarget gen) (diagonalTranscript gen) := by
  intro t
  exact ⟨query_eq gen t, answer_correct gen t, output_eq gen t⟩

lemma scored_subset_core (gen : FeedbackGenerator) :
    scored (diagonalTarget gen) (diagonalTranscript gen).presentation
      (diagonalTranscript gen).output ⊆ core := by
  intro z hz
  rcases hz with ⟨hzK, t, hyt, hzobs⟩
  rcases hzK with hzcore | ⟨s, hs, hxs⟩
  · exact hzcore
  · exfalso
    have hts : t < s := by
      by_contra hnot
      have hst : s ≤ t := by omega
      apply hzobs
      exact ⟨s, hst, hxs⟩
    have hblock := output_blocks_future gen hts hs
    exact hblock (hxs.trans hyt.symm)

end Stage3Work


namespace Stage3Work

open Stage3S2B

lemma blocked_card_le {t : ℕ} (x : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) :
    (blocked x q y).card ≤ 3 * t := by
  classical
  have hx : (Finset.univ.image x).card ≤ t := by
    simpa using (Finset.card_image_le : (Finset.univ.image x).card ≤ Finset.univ.card)
  have hq : (Finset.univ.biUnion
      (fun i => match q i with | none => (∅ : Finset ℕ) | some z => {z})).card ≤ t := by
    calc
      _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin t)),
          (match q i with | none => (∅ : Finset ℕ) | some z => {z}).card := Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin t)), 1 := by
        apply Finset.sum_le_sum
        intro i _hi
        cases hqi : q i <;> simp
      _ = t := by simp
  have hy : (Finset.univ.image y).card ≤ t := by
    simpa using (Finset.card_image_le : (Finset.univ.image y).card ≤ Finset.univ.card)
  unfold blocked
  calc
    ((Finset.univ.image x) ∪
        (Finset.univ.biUnion (fun i => match q i with | none => (∅ : Finset ℕ) | some z => {z})) ∪
        (Finset.univ.image y)).card
        ≤ ((Finset.univ.image x) ∪
            (Finset.univ.biUnion (fun i => match q i with | none => (∅ : Finset ℕ) | some z => {z}))).card +
          (Finset.univ.image y).card := Finset.card_union_le _ _
    _ ≤ ((Finset.univ.image x).card +
          (Finset.univ.biUnion (fun i => match q i with | none => (∅ : Finset ℕ) | some z => {z})).card) +
          (Finset.univ.image y).card := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ 3 * t := by omega

lemma odd_presentation_bound (gen : FeedbackGenerator) {t : ℕ}
    (ht : t % 2 = 1) :
    (diagonalTranscript gen).presentation t ≤ 9 * t := by
  rw [presentation_eq, chooseX, if_neg (by omega)]
  calc
    freshMultiple _ ≤ 3 * (blocked
      (fun i : Fin t => (diagonalTranscript gen).presentation i)
      (fun i : Fin t => (diagonalTranscript gen).query i)
      (fun i : Fin t => (diagonalTranscript gen).output i)).card := freshMultiple_bound _
    _ ≤ 9 * t := by
      have h := blocked_card_le
        (fun i : Fin t => (diagonalTranscript gen).presentation i)
        (fun i : Fin t => (diagonalTranscript gen).query i)
        (fun i : Fin t => (diagonalTranscript gen).output i)
      omega

lemma admitted_round_bound (gen : FeedbackGenerator) (r : ℕ) :
    (diagonalTranscript gen).presentation (2 * r + 1) ≤ 18 * r + 9 := by
  have h := odd_presentation_bound gen (t := 2 * r + 1) (by omega)
  omega

end Stage3Work

namespace Stage3Work

open Stage3S2B

lemma diagonalTarget_infinite (gen : FeedbackGenerator) :
    (diagonalTarget gen).Infinite := by
  have hcore : core.Infinite := by
    exact Set.infinite_range_of_injective
      (Nat.pow_right_injective (by omega : 1 < 2))
  exact hcore.mono (by
    intro z hz
    exact Or.inl hz)

noncomputable def orderedDiagonal (gen : FeedbackGenerator) : OrderedLanguage where
  carrier := diagonalTarget gen
  enumeration := Nat.nth (fun z => z ∈ diagonalTarget gen)
  enumeration_injective := Nat.nth_injective (diagonalTarget_infinite gen)
  range_enumeration := by
    simpa only [Set.setOf_mem_eq] using
      Nat.range_nth_of_infinite (diagonalTarget_infinite gen)

lemma orderedDiagonal_strictMono (gen : FeedbackGenerator) :
    InheritsAmbientOrder (orderedDiagonal gen) := by
  exact Nat.nth_strictMono (diagonalTarget_infinite gen)

lemma orderedDiagonal_enumeration_bound (gen : FeedbackGenerator) (n : ℕ) :
    (orderedDiagonal gen).enumeration n ≤ 18 * n + 9 := by
  classical
  let values : Finset ℕ :=
    (Finset.range (n + 1)).image
      (fun r => (diagonalTranscript gen).presentation (2 * r + 1))
  have hvalues_card : values.card = n + 1 := by
    dsimp only [values]
    rw [Finset.card_image_of_injective]
    · simp
    · intro a b hab
      have hround : 2 * a + 1 = 2 * b + 1 := presentation_injective gen hab
      omega
  have hsubset : values ⊆
      (Finset.range (18 * n + 10)).filter
        (fun z => z ∈ diagonalTarget gen) := by
    intro z hz
    simp only [values, Finset.mem_image, Finset.mem_range] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · have hb := admitted_round_bound gen r
      omega
    · exact Or.inr ⟨2 * r + 1, by omega, rfl⟩
  have hcount : n < Nat.count (fun z => z ∈ diagonalTarget gen) (18 * n + 10) := by
    rw [Nat.count_eq_card_filter_range]
    have hc := Finset.card_le_card hsubset
    rw [hvalues_card] at hc
    omega
  have hnth := Nat.nth_lt_of_lt_count hcount
  change Nat.nth (fun z => z ∈ diagonalTarget gen) n ≤ 18 * n + 9
  omega

end Stage3Work

namespace Stage3Work

open Stage3S2B

lemma core_count_le_log2_add_one (M : ℕ) :
    @Nat.count (fun z => z ∈ core) (Classical.decPred _) M ≤ Nat.log2 M + 1 := by
  classical
  rw [Nat.count_eq_card_filter_range]
  calc
    ((Finset.range M).filter (fun z => z ∈ core)).card
        ≤ ((Finset.range (Nat.log2 M + 1)).image (fun k => 2 ^ k)).card := by
      apply Finset.card_le_card
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_range] at hz
      rcases hz.2 with ⟨k, rfl⟩
      simp only [Finset.mem_image, Finset.mem_range]
      refine ⟨k, ?_, rfl⟩
      have hM : M ≠ 0 := by
        intro hzero
        simp [hzero] at hz
      have hk : k ≤ Nat.log2 M := (Nat.le_log2 hM).2 (Nat.le_of_lt hz.1)
      omega
    _ ≤ (Finset.range (Nat.log2 M + 1)).card := Finset.card_image_le
    _ = Nat.log2 M + 1 := Finset.card_range _

lemma prefixCount_core_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedDiagonal gen).prefixCount core n ≤ Nat.log2 (18 * n + 10) + 1 := by
  classical
  let indices : Finset ℕ :=
    (Finset.range n).filter (fun i => (orderedDiagonal gen).enumeration i ∈ core)
  have himage : (indices.image (orderedDiagonal gen).enumeration).card = indices.card := by
    rw [Finset.card_image_of_injective]
    exact (orderedDiagonal gen).enumeration_injective
  have hsubset : indices.image (orderedDiagonal gen).enumeration ⊆
      (Finset.range (18 * n + 10)).filter (fun z => z ∈ core) := by
    intro z hz
    simp only [Finset.mem_image] at hz
    obtain ⟨i, hi, rfl⟩ := hz
    simp only [indices, Finset.mem_filter, Finset.mem_range] at hi
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · have hb := orderedDiagonal_enumeration_bound gen i
      omega
    · exact hi.2
  calc
    (orderedDiagonal gen).prefixCount core n = indices.card := by
      rfl
    _ = (indices.image (orderedDiagonal gen).enumeration).card := himage.symm
    _ ≤ ((Finset.range (18 * n + 10)).filter (fun z => z ∈ core)).card :=
      Finset.card_le_card hsubset
    _ = Nat.count (fun z => z ∈ core) (18 * n + 10) := by
      rw [Nat.count_eq_card_filter_range]
    _ ≤ Nat.log2 (18 * n + 10) + 1 := core_count_le_log2_add_one _

end Stage3Work

namespace Stage3Work

open Stage3S2B

lemma log2_linear_bound (n : ℕ) (hn : 0 < n) :
    Nat.log2 (18 * n + 10) + 1 ≤ 6 + Nat.log2 n := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  have hmono : Nat.log 2 (18 * n + 10) ≤ Nat.log 2 (32 * n) := by
    apply Nat.log_mono Nat.one_lt_two le_rfl
    omega
  calc
    Nat.log 2 (18 * n + 10) + 1 ≤ Nat.log 2 (32 * n) + 1 :=
      Nat.add_le_add_right hmono 1
    _ = Nat.log 2 n + 6 := by
      have heq : 32 * n = (((((n * 2) * 2) * 2) * 2) * 2) := by omega
      rw [heq]
      repeat' rw [Nat.log_mul_base Nat.one_lt_two (by positivity)]
    _ = 6 + Nat.log 2 n := by omega

lemma prefixRatio_core_le_error (gen : FeedbackGenerator) {n : ℕ} (hn : n ≠ 0) :
    (orderedDiagonal gen).prefixRatio core n ≤
      (((6 + Nat.log2 n : ℕ) : ℝ) / (n : ℝ)) := by
  rw [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, if_neg hn]
  apply div_le_div_of_nonneg_right
  · exact_mod_cast (prefixCount_core_le gen n).trans
      (log2_linear_bound n (Nat.pos_of_ne_zero hn))
  · exact Nat.cast_nonneg n

lemma ordered_core_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedDiagonal gen).upperDensity core = 0 := by
  let error : ℕ → ℝ := fun n => ((6 + Nat.log2 n : ℕ) : ℝ) / (n : ℝ)
  have herror : Tendsto error atTop (𝓝 0) := by
    simpa only [error] using GenLimit.tendsto_countingError_div 6
  have hcompare : ∀ᶠ n : ℕ in atTop,
      (orderedDiagonal gen).prefixRatio core n ≤ error n := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    exact prefixRatio_core_le_error gen hn
  have hnonneg := (orderedDiagonal gen).upperDensity_nonneg core
  apply le_antisymm
  · unfold GenLimit.KleinbergWei.OrderedLanguage.upperDensity
    calc
      limsup ((orderedDiagonal gen).prefixRatio core) atTop
          ≤ limsup error atTop := by
        exact Filter.limsup_le_limsup hcompare
          (isCoboundedUnder_le_of_le atTop
            (fun n => (orderedDiagonal gen).prefixRatio_nonneg core n))
          herror.isBoundedUnder_le
      _ = 0 := herror.limsup_eq
  · exact hnonneg

lemma scored_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedDiagonal gen).upperDensity
      (scored (diagonalTarget gen) (diagonalTranscript gen).presentation
        (diagonalTranscript gen).output) = 0 := by
  have hmono := (orderedDiagonal gen).upperDensity_mono (scored_subset_core gen)
  have hcore := ordered_core_upperDensity_zero gen
  have hnonneg := (orderedDiagonal gen).upperDensity_nonneg
    (scored (diagonalTarget gen) (diagonalTranscript gen).presentation
      (diagonalTranscript gen).output)
  linarith

lemma negative_claim : NegativeClaim := by
  intro gen _hgen
  refine ⟨diagonalTarget gen, diagonalTarget_mem gen,
    diagonalPresenter, diagonalTranscript gen, orderedDiagonal gen, ?_⟩
  exact ⟨rfl, orderedDiagonal_strictMono gen, presented_by_diagonal gen,
    follows_diagonal gen, diagonal_clean gen, presentation_injective gen,
    diagonal_complete gen, scored_upperDensity_zero gen⟩

end Stage3Work

theorem stage3_result : Stage3S2B.MainClaim := by
  exact ⟨Stage3Work.targetClass_not_countable,
    Stage3Work.uniform_generation, Stage3Work.negative_claim⟩
