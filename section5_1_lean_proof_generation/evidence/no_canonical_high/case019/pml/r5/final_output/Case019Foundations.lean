import Stage3Model
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.SignedIntegers

open Filter
open scoped Topology

namespace Stage3Case019Proof

open Stage3Case019
open GenLimit.Generic
open GenLimit.NoiseLossFeedback
open GenLimit.UnionClosedness

private def richFirstLanguage (q : ℕ) (A : Set ℕ) : Set ℤ :=
  (omissionMarkerFinset q : Set ℤ) ∪ positiveIntegers ∪ negativeCode '' A

private theorem richFirstLanguage_mem (q : ℕ) (A : Set ℕ) :
    richFirstLanguage q A ∈ finiteOmissionClass q := by
  left
  refine ⟨?_, 0, ?_⟩
  · intro z hz
    exact Or.inl (Or.inl hz)
  · rintro z ⟨k, rfl⟩
    simpa using (show positiveCode k ∈ richFirstLanguage q A from Or.inl (Or.inr (positiveCode_mem k)))

private theorem richFirstLanguage_injective (q : ℕ) :
    Function.Injective (richFirstLanguage q) := by
  intro A B hAB
  ext k
  have hmem := Set.ext_iff.mp hAB (negativeCode k)
  have hnotMarker : negativeCode k ∉ omissionMarkerFinset q :=
    negativeCode_not_marker q k
  have hnotPositive : negativeCode k ∉ positiveIntegers := by
    exact Int.not_lt_of_ge (Int.le_of_lt (negativeCode_mem k))
  simpa [richFirstLanguage, hnotMarker, hnotPositive,
    negativeCode_injective.eq_iff] using hmem

private theorem finiteOmissionClass_uncountable (q : ℕ) :
    ¬(finiteOmissionClass q).Countable := by
  intro hcountable
  let f : Set ℕ → {L // L ∈ finiteOmissionClass q} :=
    fun A => ⟨richFirstLanguage q A, richFirstLanguage_mem q A⟩
  have hf : Function.Injective f := by
    intro A B h
    apply richFirstLanguage_injective q
    exact congrArg Subtype.val h
  letI : Countable {L // L ∈ finiteOmissionClass q} := hcountable.to_subtype
  have hpower : Countable (Set ℕ) := hf.countable
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ hpower

private theorem finiteNoiseLevel_lower_stage3 (q : ℕ) :
    ∀ gen : Stage3Case019.Generator ℤ,
      ∃ K ∈ finiteOmissionClass q, ∃ input : Stage3Case019.Stream ℤ,
        InjectiveValueContaminatedPresentationAtMost input K (q + 1) ∧
          ¬SampleFreshGeneratesAfterInput
            input (outputAfterInput gen input) K := by
  intro gen
  by_contra hnone
  push_neg at hnone
  apply finiteNoiseLevel_lower q
  refine ⟨gen, ?_⟩
  intro K hK input hinput
  obtain ⟨T, hT⟩ := hnone K hK input hinput
  refine ⟨T, ?_⟩
  intro t ht
  exact hT t ht

/-- Checked structural part of the separating witness. -/
theorem separation_witness_structure (q : ℕ) :
    ¬(finiteOmissionClass q).Countable ∧
      (∀ K ∈ finiteOmissionClass q, K.Infinite) ∧
      (∀ gen : Stage3Case019.Generator ℤ,
        ∃ K ∈ finiteOmissionClass q, ∃ input : Stage3Case019.Stream ℤ,
          InjectiveValueContaminatedPresentationAtMost input K (q + 1) ∧
            ¬SampleFreshGeneratesAfterInput
              input (outputAfterInput gen input) K) := by
  exact ⟨finiteOmissionClass_uncountable q,
    finiteOmissionClass_uus q, finiteNoiseLevel_lower_stage3 q⟩


noncomputable def familyOracle
    (family : Stage3Case019.LanguageFamily ℕ)
    (hinf : ∀ i, (family i).Infinite) : GenLimit.OracleFamily := by
  classical
  exact
    { language := family
      infinite' := hinf
      query := fun i x => if x ∈ family i then true else false
      query_spec := by simp }

private def prefixExtension {α : Type*} {n : ℕ}
    (xs : Fin n → α) (fallback : α) : ℕ → α :=
  fun k => if h : k < n then xs ⟨k, h⟩ else fallback

private theorem processRound_eq_of_prefix
    (O : GenLimit.OracleFamily) (a b : ℕ → ℕ) (t : ℕ)
    (old : GenLimit.PatientMachine.State)
    (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.processRound O a t old =
      GenLimit.PatientMachine.processRound O b t old := by
  classical
  have hs : ∀ u, u ≤ t + 1 →
      GenLimit.sample a u = GenLimit.sample b u := by
    intro u hu
    ext x
    simp only [GenLimit.mem_sample_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k, hk, (h k (lt_of_lt_of_le hk hu)).symm⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k, hk, h k (lt_of_lt_of_le hk hu)⟩
  have hcrit : ∀ u, u ≤ t + 1 →
      GenLimit.RecursiveCritical O.language a u =
        GenLimit.RecursiveCritical O.language b u := by
    intro u hu
    funext i
    apply propext
    induction i using Nat.strong_induction_on with
    | h i ih =>
        cases i with
        | zero =>
            simp [GenLimit.RecursiveCritical, GenLimit.Consistent, hs u hu]
        | succ i =>
            simp only [GenLimit.RecursiveCritical]
            rw [show GenLimit.Consistent O.language a u (i + 1) ↔
                GenLimit.Consistent O.language b u (i + 1) by
              simp [GenLimit.Consistent, hs u hu]]
            constructor
            · rintro ⟨hc, hsub⟩
              refine ⟨hc, fun j hj hjc => hsub j hj ?_⟩
              exact (ih j (by omega)).mpr hjc
            · rintro ⟨hc, hsub⟩
              refine ⟨hc, fun j hj hjc => hsub j hj ?_⟩
              exact (ih j (by omega)).mp hjc
  have hs_t := hs t (by omega)
  have hs_succ := hs (t + 1) (by omega)
  have hcrit_t := hcrit t (by omega)
  have hcrit_succ := hcrit (t + 1) (by omega)
  have hdecision :
      GenLimit.PatientMachine.decide O.language a t old =
        GenLimit.PatientMachine.decide O.language b t old := by
    unfold GenLimit.PatientMachine.decide
      GenLimit.PatientMachine.stableDecision
      GenLimit.PatientMachine.backtrackDecision
      GenLimit.PatientMachine.highestCritical
      GenLimit.PatientMachine.highestSurvivor
      GenLimit.PatientMachine.lowestConsistentInScope
      GenLimit.PatientMachine.lowestConsistent
      GenLimit.PatientMachine.criticalIndices
      GenLimit.PatientMachine.survivingCriticalIndices
      GenLimit.PatientMachine.consistentIndices
      GenLimit.Consistent
    simp only [hs_t, hs_succ, hcrit_t, hcrit_succ]
  have hleast :
      GenLimit.PatientMachine.leastAvailable O.language O.infinite' a (t + 1)
          old.used (GenLimit.PatientMachine.decide O.language b t old).focus =
        GenLimit.PatientMachine.leastAvailable O.language O.infinite' b (t + 1)
          old.used (GenLimit.PatientMachine.decide O.language b t old).focus := by
    unfold GenLimit.PatientMachine.leastAvailable
    congr 1
    funext x
    apply propext
    simp only [GenLimit.PatientMachine.Available, hs_succ]
  unfold GenLimit.PatientMachine.processRound
  simp only [hdecision, hleast]

private theorem patient_run_eq_of_prefix
    (O : GenLimit.OracleFamily) (a b : ℕ → ℕ) :
    ∀ n, (∀ k, k < n → a k = b k) →
      GenLimit.PatientMachine.run O a n =
        GenLimit.PatientMachine.run O b n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro h
      rw [GenLimit.PatientMachine.run_succ,
        GenLimit.PatientMachine.run_succ, ih (fun k hk => h k (by omega))]
      exact processRound_eq_of_prefix O a b n _
        (fun k hk => h k (by omega))

private theorem patient_output_eq_of_prefix
    (O : GenLimit.OracleFamily) (a b : ℕ → ℕ) (t : ℕ)
    (h : ∀ k, k ≤ t → a k = b k) :
    GenLimit.PatientMachine.output O a t =
      GenLimit.PatientMachine.output O b t := by
  unfold GenLimit.PatientMachine.output
  rw [patient_run_eq_of_prefix O a b (t + 1)
    (fun k hk => h k (by omega))]

noncomputable def patientGenerator (O : GenLimit.OracleFamily) :
    Stage3Case019.Generator ℕ :=
  fun n xs => match n with
    | 0 => GenLimit.PatientMachine.output O (fun _ => 0) 0
    | m + 1 =>
        GenLimit.PatientMachine.output O (prefixExtension xs 0) m

theorem outputAfterInput_patientGenerator
    (O : GenLimit.OracleFamily) (input : ℕ → ℕ) (t : ℕ) :
    outputAfterInput (patientGenerator O) input t =
      GenLimit.PatientMachine.output O input t := by
  unfold outputAfterInput GenLimit.Generic.output patientGenerator
  apply patient_output_eq_of_prefix
  intro k hk
  simp [prefixExtension, show k < t + 1 by omega]

end Stage3Case019Proof
