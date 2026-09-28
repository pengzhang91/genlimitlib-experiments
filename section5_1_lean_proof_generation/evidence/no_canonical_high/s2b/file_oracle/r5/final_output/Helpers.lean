import Stage3Model
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import GenLimit.Paper39_DenseGeneration.Abstract.Density
import Mathlib.Data.Nat.Nth

namespace Stage3Proof

open Stage3S2B
open GenLimit.KleinbergWei
open Filter

lemma oddEncoding_not_core (n : ℕ) : 2 * n + 3 ∉ core := by
  rintro ⟨k, hk⟩
  cases k with
  | zero => simp at hk
  | succ k =>
      have heven : Even (2 ^ (k + 1)) := by
        refine ⟨2 ^ k, ?_⟩
        rw [pow_succ]
        omega
      have hodd : Odd (2 * n + 3) := by
        refine ⟨n + 1, ?_⟩
        omega
      change 2 ^ (k + 1) = 2 * n + 3 at hk
      rw [hk] at heven
      exact (Nat.not_even_iff_odd.mpr hodd) heven

lemma oddEncoding_injective : Function.Injective (fun n : ℕ => 2 * n + 3) := by
  intro a b h
  change 2 * a + 3 = 2 * b + 3 at h
  have hab : 2 * a = 2 * b := Nat.add_right_cancel h
  exact Nat.eq_of_mul_eq_mul_left (by omega) hab

noncomputable def encode (A : Set ℕ) : Language :=
  core ∪ (fun n : ℕ => 2 * n + 3) '' A

lemma encode_mem (A : Set ℕ) : encode A ∈ targetClass := by
  refine ⟨(fun n : ℕ => 2 * n + 3) '' A, ?_, rfl⟩
  rintro z ⟨n, -, rfl⟩
  exact oddEncoding_not_core n

lemma encode_injective : Function.Injective encode := by
  intro A B h
  ext n
  have hn : 2 * n + 3 ∉ core := oddEncoding_not_core n
  have := Set.ext_iff.mp h (2 * n + 3)
  simpa [encode, hn, oddEncoding_injective.eq_iff] using this

lemma targetClass_not_countable : ¬ targetClass.Countable := by
  intro hcount
  let f : Set ℕ → targetClass := fun A => ⟨encode A, encode_mem A⟩
  have hf : Function.Injective f := by
    intro A B h
    exact encode_injective (Subtype.ext_iff.mp h)
  letI : Countable targetClass := hcount.to_subtype
  letI : Countable (Set ℕ) := hf.countable
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ inferInstance

lemma uniform_without_samples : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t => 2 ^ t, ?_, 0, ?_⟩
  · exact Nat.pow_right_injective (by omega)
  · intro K hK t _
    obtain ⟨A, hA, rfl⟩ := hK
    exact Or.inl ⟨t, rfl⟩

end Stage3Proof

namespace Stage3Proof

open Stage3S2B
open GenLimit.KleinbergWei
open Filter

structure FreshOddChoice (blocked : Finset ℕ) where
  value : ℕ
  not_mem : value ∉ blocked
  ordinary_mem : value ∈ ordinary
  bound : value ≤ 2 * blocked.card + 3

lemma exists_freshOddChoice (blocked : Finset ℕ) : Nonempty (FreshOddChoice blocked) := by
  let candidates := (Finset.range (blocked.card + 1)).image (fun n : ℕ => 2 * n + 3)
  have hcandidates : candidates.card = blocked.card + 1 := by
    simpa [candidates] using
      Finset.card_image_of_injective (Finset.range (blocked.card + 1)) oddEncoding_injective
  have hcard : blocked.card < candidates.card := by omega
  obtain ⟨z, hzc, hzb⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  rw [Finset.mem_image] at hzc
  obtain ⟨n, hn, rfl⟩ := hzc
  refine ⟨⟨2 * n + 3, hzb, oddEncoding_not_core n, ?_⟩⟩
  simp only [Finset.mem_range] at hn
  omega

noncomputable def freshOddChoice (blocked : Finset ℕ) : FreshOddChoice blocked :=
  Classical.choice (exists_freshOddChoice blocked)

noncomputable def runRound (gen : FeedbackGenerator) (t : ℕ) :
    ℕ × Option ℕ × Option Bool × ℕ := by
  let prevX : Fin t → ℕ := fun i => (runRound gen i).1
  let prevQ : Fin t → Option ℕ := fun i => (runRound gen i).2.1
  let prevA : Fin t → Option Bool := fun i => (runRound gen i).2.2.1
  let prevY : Fin t → ℕ := fun i => (runRound gen i).2.2.2
  let blocked : Finset ℕ :=
    Finset.univ.image prevX ∪
      Finset.univ.image (fun i => (prevQ i).getD 0) ∪
        Finset.univ.image prevY
  let x := if Even t then 2 ^ (t / 2) else (freshOddChoice blocked).value
  let currentX : Fin (t + 1) → ℕ := Fin.lastCases x prevX
  let q := gen.query t currentX prevA
  let partialK : Language := core ∪ Set.range prevX ∪ {x}
  let a := q.map fun z => membershipAnswer partialK z
  let currentA : Fin (t + 1) → Option Bool := Fin.lastCases a prevA
  let y := gen.output t currentX currentA
  exact (x, q, a, y)
termination_by t

noncomputable def adversarialTranscript (gen : FeedbackGenerator) : Transcript where
  presentation t := (runRound gen t).1
  query t := (runRound gen t).2.1
  answer t := (runRound gen t).2.2.1
  output t := (runRound gen t).2.2.2

noncomputable def adversarialTarget (gen : FeedbackGenerator) : Language :=
  Set.range (adversarialTranscript gen).presentation

end Stage3Proof

namespace Stage3Proof

open Stage3S2B

lemma membershipAnswer_eq_true_iff (K : Language) (z : ℕ) :
    membershipAnswer K z = true ↔ z ∈ K := by
  classical
  simp [membershipAnswer]

lemma presentation_even (gen : FeedbackGenerator) (k : ℕ) :
    (adversarialTranscript gen).presentation (2 * k) = 2 ^ k := by
  change (runRound gen (2 * k)).1 = 2 ^ k
  rw [runRound.eq_def]
  simp [show Even (2 * k) by exact ⟨k, by omega⟩]

lemma presentation_odd_not_core (gen : FeedbackGenerator) (t : ℕ) (ht : ¬ Even t) :
    (adversarialTranscript gen).presentation t ∈ ordinary := by
  change (runRound gen t).1 ∈ ordinary
  rw [runRound.eq_def]
  simp only [ht, if_false]
  exact (freshOddChoice _).ordinary_mem

end Stage3Proof

namespace Stage3Proof

open Stage3S2B

lemma presentation_odd_ne_prior_presentation (gen : FeedbackGenerator) (t i : ℕ)
    (ht : ¬ Even t) (hi : i < t) :
    (adversarialTranscript gen).presentation t ≠
      (adversarialTranscript gen).presentation i := by
  change (runRound gen t).1 ≠ (runRound gen i).1
  rw [runRound.eq_def]
  simp only [ht, if_false]
  let B : Finset ℕ :=
    Finset.univ.image (fun j : Fin t => (runRound gen j).1) ∪
      Finset.univ.image (fun j : Fin t => ((runRound gen j).2.1).getD 0) ∪
        Finset.univ.image (fun j : Fin t => (runRound gen j).2.2.2)
  change (freshOddChoice B).value ≠ (runRound gen i).1
  intro h
  apply (freshOddChoice B).not_mem
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [Finset.mem_image]
  exact ⟨⟨i, hi⟩, Finset.mem_univ _, h.symm⟩

lemma presentation_odd_ne_prior_query (gen : FeedbackGenerator) (t i z : ℕ)
    (ht : ¬ Even t) (hi : i < t)
    (hq : (adversarialTranscript gen).query i = some z) :
    (adversarialTranscript gen).presentation t ≠ z := by
  change (runRound gen t).1 ≠ z
  change (runRound gen i).2.1 = some z at hq
  rw [runRound.eq_def]
  simp only [ht, if_false]
  let B : Finset ℕ :=
    Finset.univ.image (fun j : Fin t => (runRound gen j).1) ∪
      Finset.univ.image (fun j : Fin t => ((runRound gen j).2.1).getD 0) ∪
        Finset.univ.image (fun j : Fin t => (runRound gen j).2.2.2)
  change (freshOddChoice B).value ≠ z
  intro h
  apply (freshOddChoice B).not_mem
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  rw [Finset.mem_image]
  refine ⟨⟨i, hi⟩, Finset.mem_univ _, ?_⟩
  simp [hq, h]

lemma presentation_odd_ne_prior_output (gen : FeedbackGenerator) (t i : ℕ)
    (ht : ¬ Even t) (hi : i < t) :
    (adversarialTranscript gen).presentation t ≠
      (adversarialTranscript gen).output i := by
  change (runRound gen t).1 ≠ (runRound gen i).2.2.2
  rw [runRound.eq_def]
  simp only [ht, if_false]
  let B : Finset ℕ :=
    Finset.univ.image (fun j : Fin t => (runRound gen j).1) ∪
      Finset.univ.image (fun j : Fin t => ((runRound gen j).2.1).getD 0) ∪
        Finset.univ.image (fun j : Fin t => (runRound gen j).2.2.2)
  change (freshOddChoice B).value ≠ (runRound gen i).2.2.2
  intro h
  apply (freshOddChoice B).not_mem
  apply Finset.mem_union_right
  rw [Finset.mem_image]
  exact ⟨⟨i, hi⟩, Finset.mem_univ _, h.symm⟩

end Stage3Proof

namespace Stage3Proof

open Stage3S2B

lemma run_x_eq (gen : FeedbackGenerator) (t : ℕ) :
    (runRound gen t).1 =
      if Even t then 2 ^ (t / 2) else
        (freshOddChoice
          (Finset.univ.image (fun i : Fin t => (runRound gen i).1) ∪
            Finset.univ.image (fun i : Fin t => ((runRound gen i).2.1).getD 0) ∪
              Finset.univ.image (fun i : Fin t => (runRound gen i).2.2.2))).value := by
  rw [runRound.eq_def]

lemma run_answer_value_eq (gen : FeedbackGenerator) (t : ℕ) :
    (runRound gen t).2.2.1 =
      (runRound gen t).2.1.map (fun z => membershipAnswer
        (core ∪ Set.range (fun i : Fin t => (runRound gen i).1) ∪ {(runRound gen t).1}) z) := by
  rw [runRound.eq_def]

lemma current_presentation_eq (gen : FeedbackGenerator) (t : ℕ) :
    (fun i : Fin (t + 1) => (adversarialTranscript gen).presentation i) =
      Fin.lastCases ((runRound gen t).1) (fun i : Fin t => (runRound gen i).1) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change (runRound gen t).1 = _
    simp
  · change (runRound gen j).1 = _
    simp

lemma prior_answer_eq (gen : FeedbackGenerator) (t : ℕ) :
    (fun i : Fin t => (adversarialTranscript gen).answer i) =
      (fun i : Fin t => (runRound gen i).2.2.1) := by
  rfl

lemma current_answer_eq (gen : FeedbackGenerator) (t : ℕ) :
    (fun i : Fin (t + 1) => (adversarialTranscript gen).answer i) =
      Fin.lastCases ((runRound gen t).2.2.1)
        (fun i : Fin t => (runRound gen i).2.2.1) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change (runRound gen t).2.2.1 = _
    simp
  · change (runRound gen j).2.2.1 = _
    simp

lemma transcript_query_eq (gen : FeedbackGenerator) (t : ℕ) :
    (adversarialTranscript gen).query t = gen.query t
      (fun i => (adversarialTranscript gen).presentation i)
      (fun i => (adversarialTranscript gen).answer i) := by
  change (runRound gen t).2.1 = gen.query t
    (fun i => (runRound gen i).1) (fun i => (runRound gen i).2.2.1)
  rw [runRound.eq_def]
  dsimp only
  rw [← run_x_eq]
  rw [← current_presentation_eq]
  simpa [adversarialTranscript]

lemma transcript_output_eq (gen : FeedbackGenerator) (t : ℕ) :
    (adversarialTranscript gen).output t = gen.output t
      (fun i => (adversarialTranscript gen).presentation i)
      (fun i => (adversarialTranscript gen).answer i) := by
  change (runRound gen t).2.2.2 = gen.output t
    (fun i => (runRound gen i).1) (fun i => (runRound gen i).2.2.1)
  rw [runRound.eq_def]
  dsimp only
  rw [← run_x_eq]
  rw [← current_presentation_eq]
  rw [← prior_answer_eq]
  rw [← transcript_query_eq]
  have ha : Option.map (fun z => membershipAnswer
      (core ∪ Set.range (fun i : Fin t => (runRound gen i).1) ∪ {(runRound gen t).1}) z)
      ((adversarialTranscript gen).query t) = (runRound gen t).2.2.1 := by
    change Option.map (fun z => membershipAnswer
      (core ∪ Set.range (fun i : Fin t => (runRound gen i).1) ∪ {(runRound gen t).1}) z)
      ((runRound gen t).2.1) = (runRound gen t).2.2.1
    exact (run_answer_value_eq gen t).symm
  rw [ha]
  rw [prior_answer_eq]
  rw [← current_answer_eq]
  simpa [adversarialTranscript]

lemma core_subset_adversarialTarget (gen : FeedbackGenerator) :
    core ⊆ adversarialTarget gen := by
  rintro z ⟨k, rfl⟩
  exact ⟨2 * k, presentation_even gen k⟩

lemma partial_target_subset (gen : FeedbackGenerator) (t : ℕ) :
    core ∪ Set.range (fun i : Fin t => (runRound gen i).1) ∪ {(runRound gen t).1} ⊆
      adversarialTarget gen := by
  intro z hz
  rcases hz with (hz | rfl)
  · rcases hz with (hz | hz)
    · exact core_subset_adversarialTarget gen hz
    · obtain ⟨i, rfl⟩ := hz
      exact ⟨i, rfl⟩
  · exact ⟨t, rfl⟩

lemma queried_mem_target_iff_partial (gen : FeedbackGenerator) (t z : ℕ)
    (hq : (adversarialTranscript gen).query t = some z) :
    z ∈ adversarialTarget gen ↔
      z ∈ core ∪ Set.range (fun i : Fin t => (runRound gen i).1) ∪ {(runRound gen t).1} := by
  constructor
  · rintro ⟨s, hs⟩
    by_cases hcore : z ∈ core
    · exact Or.inl (Or.inl hcore)
    by_cases hst : s < t
    · exact Or.inl (Or.inr ⟨⟨s, hst⟩, hs⟩)
    by_cases hts : t < s
    · have hsodd : ¬ Even s := by
        intro hseven
        exact hcore (by
          obtain ⟨k, hk⟩ := hseven
          have hx := presentation_even gen k
          have hsk : s = 2 * k := by omega
          rw [hsk] at hs
          exact ⟨k, by exact hx.symm.trans hs⟩)
      exact False.elim ((presentation_odd_ne_prior_query gen s t z hsodd hts hq) hs)
    · have hst_eq : s = t := by omega
      subst s
      exact Or.inr (by exact hs.symm)
  · intro hz
    exact partial_target_subset gen t hz

lemma transcript_answer_eq (gen : FeedbackGenerator) (t : ℕ) :
    (adversarialTranscript gen).answer t =
      match (adversarialTranscript gen).query t with
      | none => none
      | some z => some (membershipAnswer (adversarialTarget gen) z) := by
  change (runRound gen t).2.2.1 = _
  rw [run_answer_value_eq]
  change Option.map (fun z => membershipAnswer
      (core ∪ Set.range (fun i : Fin t => (runRound gen i).1) ∪ {(runRound gen t).1}) z)
      ((adversarialTranscript gen).query t) = _
  cases hq : (adversarialTranscript gen).query t with
  | none => simp [hq]
  | some z =>
      simp only [hq, Option.map_some]
      congr 1
      apply Bool.eq_iff_iff.mpr
      simp only [membershipAnswer_eq_true_iff]
      exact (queried_mem_target_iff_partial gen t z hq).symm

lemma followsProtocol_adversarial (gen : FeedbackGenerator) :
    FollowsProtocol gen (adversarialTarget gen) (adversarialTranscript gen) := by
  intro t
  exact ⟨transcript_query_eq gen t, transcript_answer_eq gen t,
    transcript_output_eq gen t⟩

end Stage3Proof

namespace Stage3Proof

open Stage3S2B
open GenLimit.KleinbergWei

lemma presentation_injective (gen : FeedbackGenerator) :
    Function.Injective (adversarialTranscript gen).presentation := by
  intro t s h
  by_cases ht : Even t
  · obtain ⟨a, ha⟩ := ht
    have hta : t = 2 * a := by omega
    by_cases hs : Even s
    · obtain ⟨b, hb⟩ := hs
      have hsb : s = 2 * b := by omega
      have hp : 2 ^ a = 2 ^ b := by
        rw [← presentation_even gen a, ← presentation_even gen b]
        simpa [hta, hsb] using h
      have hab : a = b := Nat.pow_right_injective (by omega) hp
      omega
    · have hcore : (adversarialTranscript gen).presentation t ∈ core := by
        rw [hta, presentation_even]
        exact ⟨a, rfl⟩
      have hord := presentation_odd_not_core gen s hs
      rw [h] at hcore
      exact False.elim (hord hcore)
  · by_cases hs : Even s
    · have hcore : (adversarialTranscript gen).presentation s ∈ core := by
        obtain ⟨b, hb⟩ := hs
        have hsb : s = 2 * b := by omega
        rw [hsb, presentation_even]
        exact ⟨b, rfl⟩
      have hord := presentation_odd_not_core gen t ht
      rw [h] at hord
      exact False.elim (hord hcore)
    · rcases lt_trichotomy t s with hts | rfl | hst
      · exact False.elim ((presentation_odd_ne_prior_presentation gen s t hs hts) h.symm)
      · rfl
      · exact False.elim ((presentation_odd_ne_prior_presentation gen t s ht hst) h)

lemma adversarialTarget_mem_class (gen : FeedbackGenerator) :
    adversarialTarget gen ∈ targetClass := by
  let A : Language := adversarialTarget gen ∩ ordinary
  refine ⟨A, Set.inter_subset_right, ?_⟩
  apply Set.Subset.antisymm
  · intro z hz
    by_cases hc : z ∈ core
    · exact Or.inl hc
    · exact Or.inr ⟨hz, hc⟩
  · intro z hz
    rcases hz with hz | hz
    · exact core_subset_adversarialTarget gen hz
    · exact hz.1

lemma clean_adversarial (gen : FeedbackGenerator) :
    Clean (adversarialTranscript gen).presentation (adversarialTarget gen) := by
  intro t
  exact ⟨t, rfl⟩

lemma complete_adversarial (gen : FeedbackGenerator) :
    Complete (adversarialTranscript gen).presentation (adversarialTarget gen) := by
  intro z hz
  exact hz

noncomputable def hardcodedPresenter (gen : FeedbackGenerator) : CausalPresenter where
  next t _ _ _ _ := (adversarialTranscript gen).presentation t

lemma presentedBy_adversarial (gen : FeedbackGenerator) :
    PresentedBy (hardcodedPresenter gen) (adversarialTranscript gen) := by
  intro t
  rfl

lemma eventual_output_core (gen : FeedbackGenerator)
    (hvalid : UniversallyEventuallyValidFresh gen) :
    ∃ T, ∀ t, T ≤ t → (adversarialTranscript gen).output t ∈ core := by
  obtain ⟨T, hT⟩ := hvalid (adversarialTarget gen) (adversarialTarget_mem_class gen)
    (adversarialTranscript gen) (followsProtocol_adversarial gen)
    (clean_adversarial gen) (presentation_injective gen) (complete_adversarial gen)
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hyK, hyfresh⟩ := hT t ht
  by_contra hycore
  obtain ⟨s, hs⟩ := hyK
  by_cases hst : s ≤ t
  · exact hyfresh ⟨s, hst, hs⟩
  · have hsodd : ¬ Even s := by
      intro hseven
      obtain ⟨k, hk⟩ := hseven
      have hsk : s = 2 * k := by omega
      have hp := presentation_even gen k
      rw [hsk] at hs
      apply hycore
      exact ⟨k, hp.symm.trans hs⟩
    exact (presentation_odd_ne_prior_output gen s t hsodd (by omega)) hs

lemma scored_subset_core_union_initial (gen : FeedbackGenerator)
    (hvalid : UniversallyEventuallyValidFresh gen) :
    ∃ T, scored (adversarialTarget gen) (adversarialTranscript gen).presentation
      (adversarialTranscript gen).output ⊆
      core ∪ Set.range (fun i : Fin T => (adversarialTranscript gen).output i) := by
  obtain ⟨T, hT⟩ := eventual_output_core gen hvalid
  refine ⟨T, ?_⟩
  intro z hz
  obtain ⟨-, t, hyt, -⟩ := hz
  by_cases ht : T ≤ t
  · exact Or.inl (by rw [← hyt]; exact hT t ht)
  · exact Or.inr ⟨⟨t, by omega⟩, hyt⟩

end Stage3Proof

namespace Stage3Proof

open Stage3S2B
open GenLimit.KleinbergWei
open Filter

lemma blocked_card_le (gen : FeedbackGenerator) (t : ℕ) :
    (Finset.univ.image (fun i : Fin t => (runRound gen i).1) ∪
      Finset.univ.image (fun i : Fin t => ((runRound gen i).2.1).getD 0) ∪
        Finset.univ.image (fun i : Fin t => (runRound gen i).2.2.2)).card ≤ 3 * t := by
  calc
    _ ≤ (Finset.univ.image (fun i : Fin t => (runRound gen i).1)).card +
        (Finset.univ.image (fun i : Fin t => ((runRound gen i).2.1).getD 0)).card +
        (Finset.univ.image (fun i : Fin t => (runRound gen i).2.2.2)).card := by
          exact (Finset.card_union_le _ _).trans
            (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    _ ≤ t + t + t := by
      have hx : (Finset.univ.image (fun i : Fin t => (runRound gen i).1)).card ≤ t := by
        simpa using (Finset.card_image_le :
          (Finset.univ.image (fun i : Fin t => (runRound gen i).1)).card ≤ Finset.univ.card)
      have hq : (Finset.univ.image (fun i : Fin t => ((runRound gen i).2.1).getD 0)).card ≤ t := by
        simpa using (Finset.card_image_le :
          (Finset.univ.image (fun i : Fin t => ((runRound gen i).2.1).getD 0)).card ≤ Finset.univ.card)
      have hy : (Finset.univ.image (fun i : Fin t => (runRound gen i).2.2.2)).card ≤ t := by
        simpa using (Finset.card_image_le :
          (Finset.univ.image (fun i : Fin t => (runRound gen i).2.2.2)).card ≤ Finset.univ.card)
      omega
    _ = 3 * t := by omega

lemma presentation_odd_bound (gen : FeedbackGenerator) (t : ℕ) (ht : ¬ Even t) :
    (adversarialTranscript gen).presentation t ≤ 6 * t + 3 := by
  change (runRound gen t).1 ≤ 6 * t + 3
  rw [run_x_eq, if_neg ht]
  let B : Finset ℕ :=
    Finset.univ.image (fun i : Fin t => (runRound gen i).1) ∪
      Finset.univ.image (fun i : Fin t => ((runRound gen i).2.1).getD 0) ∪
        Finset.univ.image (fun i : Fin t => (runRound gen i).2.2.2)
  change (freshOddChoice B).value ≤ 6 * t + 3
  calc
    (freshOddChoice B).value ≤ 2 * B.card + 3 := (freshOddChoice B).bound
    _ ≤ 6 * t + 3 := by have := blocked_card_le gen t; change B.card ≤ 3 * t at this; omega

lemma adversarialTarget_infinite (gen : FeedbackGenerator) :
    (adversarialTarget gen).Infinite := by
  exact Set.Infinite.mono (core_subset_adversarialTarget gen)
    (Set.infinite_range_of_injective (Nat.pow_right_injective (by omega)))

noncomputable def orderedAdversarialTarget (gen : FeedbackGenerator) : Stage3S2B.OrderedLanguage where
  carrier := adversarialTarget gen
  enumeration := Nat.nth (fun z => z ∈ adversarialTarget gen)
  enumeration_injective := (Nat.nth_strictMono (adversarialTarget_infinite gen)).injective
  range_enumeration := Nat.range_nth_of_infinite (adversarialTarget_infinite gen)

lemma odd_presentations_bounded (gen : FeedbackGenerator) (n k : ℕ) (hk : k ≤ n) :
    (adversarialTranscript gen).presentation (2 * k + 1) < 12 * n + 10 := by
  have hodd : ¬ Even (2 * k + 1) :=
    Nat.not_even_iff_odd.mpr ⟨k, by omega⟩
  have hb := presentation_odd_bound gen (2 * k + 1) hodd
  simp only [Nat.mul_add, Nat.mul_one] at hb ⊢
  omega

lemma ordered_enumeration_bound (gen : FeedbackGenerator) (n : ℕ) :
    (orderedAdversarialTarget gen).enumeration n < 12 * n + 10 := by
  classical
  let values : Finset ℕ := (Finset.range (n + 1)).image
    (fun k => (adversarialTranscript gen).presentation (2 * k + 1))
  have hcard : values.card = n + 1 := by
    rw [Finset.card_image_of_injective]
    · simp [values]
    · intro a b hab
      have htimes : 2 * a + 1 = 2 * b + 1 := presentation_injective gen hab
      have hmul : 2 * a = 2 * b := Nat.add_right_cancel htimes
      exact Nat.eq_of_mul_eq_mul_left (by omega) hmul
  have hsubset : values ⊆ (Finset.range (12 * n + 10)).filter
      (fun z => z ∈ adversarialTarget gen) := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨k, hk, rfl⟩ := hz
    simp only [Finset.mem_range, Finset.mem_filter] at hk ⊢
    exact ⟨odd_presentations_bounded gen n k (by omega), ⟨2 * k + 1, rfl⟩⟩
  have hcount : n < Nat.count (fun z => z ∈ adversarialTarget gen) (12 * n + 10) := by
    rw [Nat.count_eq_card_filter_range]
    have := Finset.card_le_card hsubset
    omega
  exact Nat.nth_lt_of_lt_count hcount

end Stage3Proof

namespace Stage3Proof

open Stage3S2B
open GenLimit.KleinbergWei
open Filter

lemma prefixCount_core_le_log2 (gen : FeedbackGenerator) (n : ℕ) :
    (orderedAdversarialTarget gen).prefixCount core n ≤
      Nat.log2 (12 * n + 10) + 1 := by
  classical
  let indices : Finset ℕ := (Finset.range n).filter
    (fun i => (orderedAdversarialTarget gen).enumeration i ∈ core)
  let values : Finset ℕ := indices.image (orderedAdversarialTarget gen).enumeration
  let powers : Finset ℕ := (Finset.range (Nat.log2 (12 * n + 10) + 1)).image
    (fun k => 2 ^ k)
  have hcard : values.card = (orderedAdversarialTarget gen).prefixCount core n := by
    rw [Finset.card_image_of_injective]
    · rfl
    · exact (orderedAdversarialTarget gen).enumeration_injective
  have hsubset : values ⊆ powers := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨i, hi, rfl⟩ := hz
    have hi' : i < n ∧ (orderedAdversarialTarget gen).enumeration i ∈ core := by
      simpa [indices] using hi
    obtain ⟨k, hk⟩ := hi'.2
    rw [Finset.mem_image]
    refine ⟨k, ?_, hk⟩
    simp only [Finset.mem_range]
    change 2 ^ k = (orderedAdversarialTarget gen).enumeration i at hk
    have hibound := ordered_enumeration_bound gen i
    have hkpow : 2 ^ k ≤ 12 * n + 10 := by
      rw [hk]
      omega
    exact Nat.lt_succ_iff.mpr ((Nat.le_log2 (by omega)).mpr hkpow)
  calc
    (orderedAdversarialTarget gen).prefixCount core n = values.card := hcard.symm
    _ ≤ powers.card := Finset.card_le_card hsubset
    _ ≤ Nat.log2 (12 * n + 10) + 1 := by
      simpa [powers] using (Finset.card_image_le :
        ((Finset.range (Nat.log2 (12 * n + 10) + 1)).image
          (fun k => 2 ^ k)).card ≤
        (Finset.range (Nat.log2 (12 * n + 10) + 1)).card)

lemma log2_linear_bound (n : ℕ) (hn : 1 ≤ n) :
    Nat.log2 (12 * n + 10) + 1 ≤ 6 + Nat.log2 n := by
  have harg : 12 * n + 10 ≤ 32 * n := by omega
  have hlog : Nat.log2 (12 * n + 10) ≤ Nat.log2 (32 * n) := by
    simpa only [Nat.log2_eq_log_two] using Nat.log_monotone harg
  have hn0 : n ≠ 0 := by omega
  have h1 : n * 2 ≠ 0 := by omega
  have h2 : (n * 2) * 2 ≠ 0 := by omega
  have h3 : ((n * 2) * 2) * 2 ≠ 0 := by omega
  have h4 : (((n * 2) * 2) * 2) * 2 ≠ 0 := by omega
  have hlogmul : Nat.log2 (32 * n) = Nat.log2 n + 5 := by
    simp only [Nat.log2_eq_log_two]
    rw [show 32 * n = (((((n * 2) * 2) * 2) * 2) * 2) by omega]
    rw [Nat.log_mul_base Nat.one_lt_two h4,
      Nat.log_mul_base Nat.one_lt_two h3,
      Nat.log_mul_base Nat.one_lt_two h2,
      Nat.log_mul_base Nat.one_lt_two h1,
      Nat.log_mul_base Nat.one_lt_two hn0]
  rw [hlogmul] at hlog
  omega

lemma core_prefixRatio_tendsto_zero (gen : FeedbackGenerator) :
    Tendsto ((orderedAdversarialTarget gen).prefixRatio core) atTop (nhds 0) := by
  apply squeeze_zero
    (fun n => (orderedAdversarialTarget gen).prefixRatio_nonneg core n)
    (fun n => ?_)
    (GenLimit.tendsto_countingError_div 6)
  cases n with
  | zero => simp
  | succ n =>
      simp only [OrderedLanguage.prefixRatio, Nat.succ_ne_zero, if_false]
      apply div_le_div_of_nonneg_right
      · exact_mod_cast (prefixCount_core_le_log2 gen (n + 1)).trans
          (log2_linear_bound (n + 1) (by omega))
      · positivity

lemma core_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedAdversarialTarget gen).upperDensity core = 0 := by
  exact (core_prefixRatio_tendsto_zero gen).limsup_eq

lemma scored_upperDensity_zero (gen : FeedbackGenerator)
    (hvalid : UniversallyEventuallyValidFresh gen) :
    (orderedAdversarialTarget gen).upperDensity
      (scored (adversarialTarget gen) (adversarialTranscript gen).presentation
        (adversarialTranscript gen).output) = 0 := by
  obtain ⟨T, hsubset⟩ := scored_subset_core_union_initial gen hvalid
  let initial : Language := Set.range
    (fun i : Fin T => (adversarialTranscript gen).output i)
  have hinitial : initial.Finite := Set.finite_range _
  apply le_antisymm
  · calc
      (orderedAdversarialTarget gen).upperDensity
          (scored (adversarialTarget gen) (adversarialTranscript gen).presentation
            (adversarialTranscript gen).output) ≤
          (orderedAdversarialTarget gen).upperDensity (core ∪ initial) :=
        (orderedAdversarialTarget gen).upperDensity_mono hsubset
      _ ≤ (orderedAdversarialTarget gen).upperDensity core +
          (orderedAdversarialTarget gen).upperDensity initial :=
        (orderedAdversarialTarget gen).upperDensity_union_le core initial
      _ = 0 := by
        rw [core_upperDensity_zero gen,
          (orderedAdversarialTarget gen).upperDensity_eq_zero_of_finite hinitial]
        norm_num
  · exact (orderedAdversarialTarget gen).upperDensity_nonneg _

lemma negative_claim : NegativeClaim := by
  intro gen hvalid
  refine ⟨adversarialTarget gen, adversarialTarget_mem_class gen,
    hardcodedPresenter gen, adversarialTranscript gen,
    orderedAdversarialTarget gen, ?_⟩
  refine ⟨rfl, ?_, presentedBy_adversarial gen,
    followsProtocol_adversarial gen, clean_adversarial gen,
    presentation_injective gen, complete_adversarial gen,
    scored_upperDensity_zero gen hvalid⟩
  exact Nat.nth_strictMono (adversarialTarget_infinite gen)

end Stage3Proof
