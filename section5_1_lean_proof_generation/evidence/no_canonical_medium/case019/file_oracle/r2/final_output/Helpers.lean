import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Set

namespace Stage3Case019Proof

private theorem basic_sample_eq {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    GenLimit.sample a t = GenLimit.sample b t := by
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor <;> rintro ⟨k, hk, rfl⟩
  · exact ⟨k, hk, (h k hk).symm⟩
  · exact ⟨k, hk, h k hk⟩

private theorem consistent_iff {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {t i : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    GenLimit.Consistent C a t i ↔ GenLimit.Consistent C b t i := by
  unfold GenLimit.Consistent
  rw [basic_sample_eq h]

private theorem recursiveCritical_iff {C : GenLimit.LanguageFamily}
    {a b : ℕ → ℕ} {t i : ℕ} (h : ∀ k, k < t → a k = b k) :
    GenLimit.RecursiveCritical C a t i ↔ GenLimit.RecursiveCritical C b t i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    cases i with
    | zero => simpa [GenLimit.RecursiveCritical] using consistent_iff (i := 0) h
    | succ i =>
      simp only [GenLimit.RecursiveCritical]
      constructor
      · rintro ⟨hc, hr⟩
        refine ⟨(consistent_iff h).mp hc, ?_⟩
        intro j hj hjc
        exact hr j hj ((ih j (Nat.lt_succ_of_le hj)).mpr hjc)
      · rintro ⟨hc, hr⟩
        refine ⟨(consistent_iff h).mpr hc, ?_⟩
        intro j hj hjc
        exact hr j hj ((ih j (Nat.lt_succ_of_le hj)).mp hjc)

private theorem consistentIndices_eq {C : GenLimit.LanguageFamily}
    {a b : ℕ → ℕ} {t scope : ℕ} (h : ∀ k, k < t → a k = b k) :
    GenLimit.PatientMachine.consistentIndices C a t scope =
      GenLimit.PatientMachine.consistentIndices C b t scope := by
  ext i
  simp only [GenLimit.PatientMachine.mem_consistentIndices]
  exact and_congr_right (fun _ => consistent_iff h)

private theorem criticalIndices_eq {C : GenLimit.LanguageFamily}
    {a b : ℕ → ℕ} {t scope : ℕ} (h : ∀ k, k < t → a k = b k) :
    GenLimit.PatientMachine.criticalIndices C a t scope =
      GenLimit.PatientMachine.criticalIndices C b t scope := by
  ext i
  simp only [GenLimit.PatientMachine.mem_criticalIndices]
  exact and_congr_right (fun _ => recursiveCritical_iff h)

private theorem survivingCriticalIndices_eq {C : GenLimit.LanguageFamily}
    {a b : ℕ → ℕ} {t scope : ℕ} (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.survivingCriticalIndices C a t scope =
      GenLimit.PatientMachine.survivingCriticalIndices C b t scope := by
  ext i
  simp only [GenLimit.PatientMachine.mem_survivingCriticalIndices]
  have ht : ∀ k, k < t → a k = b k := fun k hk => h k (Nat.lt.step hk)
  exact and_congr_right fun _ =>
    and_congr (recursiveCritical_iff ht) (recursiveCritical_iff h)

private theorem highestCritical_eq (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ}
    {t scope fallback : ℕ} (h : ∀ k, k < t → a k = b k) :
    GenLimit.PatientMachine.highestCritical C a t scope fallback =
      GenLimit.PatientMachine.highestCritical C b t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.highestCritical
  rw [criticalIndices_eq h]

private theorem highestSurvivor_eq (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ}
    {t scope fallback : ℕ} (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.highestSurvivor C a t scope fallback =
      GenLimit.PatientMachine.highestSurvivor C b t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.highestSurvivor
  rw [survivingCriticalIndices_eq h]

private theorem lowestConsistentInScope_eq (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ}
    {t scope fallback : ℕ} (h : ∀ k, k < t → a k = b k) :
    GenLimit.PatientMachine.lowestConsistentInScope C a t scope fallback =
      GenLimit.PatientMachine.lowestConsistentInScope C b t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.lowestConsistentInScope
  rw [consistentIndices_eq h]

private theorem lowestConsistent_eq (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ}
    {t fallback : ℕ} (h : ∀ k, k < t → a k = b k) :
    GenLimit.PatientMachine.lowestConsistent C a t fallback =
      GenLimit.PatientMachine.lowestConsistent C b t fallback := by
  classical
  unfold GenLimit.PatientMachine.lowestConsistent
  by_cases ha : ∃ i, GenLimit.Consistent C a t i
  · have hb : ∃ i, GenLimit.Consistent C b t i := by
      simpa only [consistent_iff h] using ha
    rw [dif_pos ha, dif_pos hb]
    apply Nat.find_congr (Nat.find_spec ha)
    intro n _hn
    exact consistent_iff h
  · have hb : ¬∃ i, GenLimit.Consistent C b t i := by
      simpa only [consistent_iff h] using ha
    rw [dif_neg ha, dif_neg hb]

private theorem backtrackDecision_eq (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ}
    {t : ℕ} {old : GenLimit.PatientMachine.State}
    (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.backtrackDecision C a t old =
      GenLimit.PatientMachine.backtrackDecision C b t old := by
  classical
  unfold GenLimit.PatientMachine.backtrackDecision
  rw [consistentIndices_eq h, survivingCriticalIndices_eq h]
  rw [highestSurvivor_eq C h, lowestConsistentInScope_eq C h]
  rw [lowestConsistent_eq C h]
  simp_rw [consistent_iff h]

private theorem stableDecision_eq (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ}
    {t : ℕ} {old : GenLimit.PatientMachine.State}
    (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.stableDecision C a t old =
      GenLimit.PatientMachine.stableDecision C b t old := by
  classical
  unfold GenLimit.PatientMachine.stableDecision
  by_cases hw : 2 ^ old.tau ≤ old.age
  · simp only [dif_pos hw]
    rw [highestCritical_eq C h]
  · simp only [dif_neg hw]

private theorem decide_eq (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ}
    {t : ℕ} {old : GenLimit.PatientMachine.State}
    (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.decide C a t old =
      GenLimit.PatientMachine.decide C b t old := by
  classical
  unfold GenLimit.PatientMachine.decide
  rw [propext (consistent_iff h)]
  by_cases hc : GenLimit.Consistent C b (t + 1) old.focus
  · rw [if_pos hc, if_pos hc]
    exact stableDecision_eq C h
  · rw [if_neg hc, if_neg hc]
    exact backtrackDecision_eq C h

private theorem leastAvailable_eq (O : GenLimit.OracleFamily)
    {a b : ℕ → ℕ} {t : ℕ} {used : Finset ℕ} {focus : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    GenLimit.PatientMachine.leastAvailable O.language O.infinite' a t used focus =
      GenLimit.PatientMachine.leastAvailable O.language O.infinite' b t used focus := by
  classical
  unfold GenLimit.PatientMachine.leastAvailable
  apply Nat.find_congr (GenLimit.PatientMachine.leastAvailable_spec
    O.language O.infinite' a t used focus)
  intro n _hn
  unfold GenLimit.PatientMachine.Available
  rw [basic_sample_eq h]

private theorem processRound_congr (O : GenLimit.OracleFamily)
    {a b : ℕ → ℕ} {t : ℕ} {old : GenLimit.PatientMachine.State}
    (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.processRound O a t old =
      GenLimit.PatientMachine.processRound O b t old := by
  classical
  have hd := decide_eq O.language (old := old) h
  have hx := leastAvailable_eq O (used := old.used)
    (focus := (GenLimit.PatientMachine.decide O.language b t old).focus) h
  unfold GenLimit.PatientMachine.processRound
  simp only [hd]
  rw [hx]

private theorem run_congr (O : GenLimit.OracleFamily)
    {a b : ℕ → ℕ} {t : ℕ} (h : ∀ k, k < t → a k = b k) :
    GenLimit.PatientMachine.run O a t = GenLimit.PatientMachine.run O b t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [GenLimit.PatientMachine.run_succ, GenLimit.PatientMachine.run_succ]
      rw [ih (fun k hk => h k (Nat.lt.step hk))]
      exact processRound_congr O h


def prefixCompletion {α : Type*} {t : ℕ} (xs : Fin t → α) (fallback : α) : ℕ → α :=
  fun k => if hk : k < t then xs ⟨k, hk⟩ else fallback

noncomputable def patientGenerator (O : GenLimit.OracleFamily) :
    GenLimit.Generic.Generator ℕ :=
  fun t xs => match t with
    | 0 => 0
    | n + 1 => GenLimit.PatientMachine.output O (prefixCompletion xs 0) n

theorem outputAfterInput_patientGenerator (O : GenLimit.OracleFamily)
    (input : ℕ → ℕ) (t : ℕ) :
    Stage3Case019.outputAfterInput (patientGenerator O) input t =
      GenLimit.PatientMachine.output O input t := by
  unfold Stage3Case019.outputAfterInput GenLimit.Generic.output patientGenerator
  simp only
  unfold GenLimit.PatientMachine.output
  rw [run_congr O]
  intro k hk
  simp [prefixCompletion, hk]


private def omissionEncoding (i : ℕ) (A : Set ℕ) : Set ℤ :=
  GenLimit.UnionClosedness.negativeIntegers ∪
    {z | ∃ n ∈ A, z = GenLimit.UnionClosedness.positiveCode (i + 1 + n)}

private theorem omissionEncoding_mem_second (i : ℕ) (A : Set ℕ) :
    omissionEncoding i A ∈
      GenLimit.NoiseLossFeedback.finiteOmissionSecondClass i := by
  constructor
  · exact Set.subset_union_left
  · rw [Set.disjoint_left]
    intro z hz hmarker
    rcases hz with hzneg | ⟨n, _hnA, rfl⟩
    · exact (Int.not_lt_of_ge
        (GenLimit.NoiseLossFeedback.omissionMarker_nonnegative hmarker)) hzneg
    · obtain ⟨k, hk, heq⟩ :=
        GenLimit.NoiseLossFeedback.mem_omissionMarkerFinset_iff.mp hmarker
      simp [GenLimit.UnionClosedness.positiveCode] at heq
      omega

private theorem omissionEncoding_injective (i : ℕ) :
    Function.Injective (omissionEncoding i) := by
  intro A B hAB
  ext n
  have hpositive :
      GenLimit.UnionClosedness.positiveCode (i + 1 + n) ∉
        GenLimit.UnionClosedness.negativeIntegers := by
    intro hz
    have hp := GenLimit.UnionClosedness.positiveCode_mem (i + 1 + n)
    simp only [GenLimit.UnionClosedness.negativeIntegers, Set.mem_setOf_eq] at hz
    simp only [GenLimit.UnionClosedness.positiveIntegers, Set.mem_setOf_eq] at hp
    omega
  have hmem (C : Set ℕ) :
      GenLimit.UnionClosedness.positiveCode (i + 1 + n) ∈
        omissionEncoding i C ↔ n ∈ C := by
    simp only [omissionEncoding, Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro (hneg | ⟨m, hm, heq⟩)
      · exact False.elim (hpositive hneg)
      · have hadd : i + 1 + m = i + 1 + n :=
          GenLimit.UnionClosedness.positiveCode_injective heq.symm
        have : m = n := by omega
        simpa [this] using hm
    · intro hn
      exact Or.inr ⟨n, hn, rfl⟩
  rw [← hmem A, ← hmem B, hAB]

theorem finiteOmissionClass_not_countable (i : ℕ) :
    ¬(GenLimit.NoiseLossFeedback.finiteOmissionClass i).Countable := by
  intro hcount
  have hrange : (Set.range (omissionEncoding i)).Countable := by
    apply Set.Countable.mono _ hcount
    rintro L ⟨A, rfl⟩
    exact Or.inr (omissionEncoding_mem_second i A)
  have huniv : (Set.univ : Set (Set ℕ)).Countable := by
    rw [← Set.preimage_range (omissionEncoding i)]
    exact hrange.preimage (omissionEncoding_injective i)
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ
    (Set.countable_univ_iff.mp huniv)

theorem finiteNoiseLevel_sampleFresh_failure (i : ℕ)
    (gen : Stage3Case019.Generator ℤ) :
    ∃ K ∈ GenLimit.NoiseLossFeedback.finiteOmissionClass i,
      ∃ input : Stage3Case019.Stream ℤ,
        GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
            input K (i + 1) ∧
          ¬Stage3Case019.SampleFreshGeneratesAfterInput
            input (Stage3Case019.outputAfterInput gen input) K := by
  by_contra h
  push_neg at h
  apply GenLimit.NoiseLossFeedback.finiteNoiseLevel_lower i
  refine ⟨gen, ?_⟩
  intro K hK input hinput
  have hg := h K hK input hinput
  simpa [Stage3Case019.SampleFreshGeneratesAfterInput,
    Stage3Case019.outputAfterInput,
    GenLimit.NoiseLossFeedback.CorrectAt,
    GenLimit.NoiseLossFeedback.outputAt,
    GenLimit.NoiseLossFeedback.observedThrough] using hg

end Stage3Case019Proof
