import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.SweepGenerators

open Set Filter
open scoped Topology

namespace Case019

noncomputable def oracleOfFamily
    (family : GenLimit.Generic.LanguageFamily ℕ)
    (hinf : ∀ i, (family i).Infinite) : GenLimit.OracleFamily where
  language := family
  infinite' := hinf
  query i x := by
    classical
    exact if x ∈ family i then true else false
  query_spec i x := by
    classical
    simp

private theorem sample_eq_of_eqOn_lt
    {a b : ℕ → ℕ} {t : ℕ} (h : ∀ k, k < t → a k = b k) :
    GenLimit.sample a t = GenLimit.sample b t := by
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor <;> rintro ⟨k, hk, rfl⟩
  · exact ⟨k, hk, (h k hk).symm⟩
  · exact ⟨k, hk, h k hk⟩

private theorem consistent_iff_of_eqOn_lt
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {t i : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    GenLimit.Consistent C a t i ↔ GenLimit.Consistent C b t i := by
  unfold GenLimit.Consistent
  rw [sample_eq_of_eqOn_lt h]

private theorem recursiveCritical_iff_of_eqOn_lt
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    ∀ i, GenLimit.RecursiveCritical C a t i ↔
      GenLimit.RecursiveCritical C b t i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero => simpa [GenLimit.RecursiveCritical] using
          consistent_iff_of_eqOn_lt (C := C) (i := 0) h
      | succ n =>
          rw [GenLimit.RecursiveCritical, GenLimit.RecursiveCritical,
            consistent_iff_of_eqOn_lt h]
          constructor
          · rintro ⟨hc, hsub⟩
            exact ⟨hc, fun j hj hjc => hsub j hj ((ih j (by omega)).mpr hjc)⟩
          · rintro ⟨hc, hsub⟩
            exact ⟨hc, fun j hj hjc => hsub j hj ((ih j (by omega)).mp hjc)⟩

private theorem consistentIndices_eq_of_eqOn_lt
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {t scope : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    GenLimit.PatientMachine.consistentIndices C a t scope =
      GenLimit.PatientMachine.consistentIndices C b t scope := by
  ext i
  simp [GenLimit.PatientMachine.mem_consistentIndices,
    consistent_iff_of_eqOn_lt h]

private theorem criticalIndices_eq_of_eqOn_lt
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {t scope : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    GenLimit.PatientMachine.criticalIndices C a t scope =
      GenLimit.PatientMachine.criticalIndices C b t scope := by
  ext i
  simp [GenLimit.PatientMachine.mem_criticalIndices,
    recursiveCritical_iff_of_eqOn_lt h]

private theorem survivingCriticalIndices_eq_of_eqOn_lt
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {t scope : ℕ}
    (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.survivingCriticalIndices C a t scope =
      GenLimit.PatientMachine.survivingCriticalIndices C b t scope := by
  have hprev : ∀ k, k < t → a k = b k := fun k hk => h k (by omega)
  ext i
  simp [GenLimit.PatientMachine.mem_survivingCriticalIndices,
    recursiveCritical_iff_of_eqOn_lt h,
    recursiveCritical_iff_of_eqOn_lt hprev]

private theorem highestCritical_eq_of_eqOn_lt
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {t scope fallback : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    GenLimit.PatientMachine.highestCritical C a t scope fallback =
      GenLimit.PatientMachine.highestCritical C b t scope fallback := by
  unfold GenLimit.PatientMachine.highestCritical
  rw [criticalIndices_eq_of_eqOn_lt h]

private theorem highestSurvivor_eq_of_eqOn_lt
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {t scope fallback : ℕ}
    (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.highestSurvivor C a t scope fallback =
      GenLimit.PatientMachine.highestSurvivor C b t scope fallback := by
  unfold GenLimit.PatientMachine.highestSurvivor
  rw [survivingCriticalIndices_eq_of_eqOn_lt h]

private theorem lowestConsistentInScope_eq_of_eqOn_lt
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {t scope fallback : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    GenLimit.PatientMachine.lowestConsistentInScope C a t scope fallback =
      GenLimit.PatientMachine.lowestConsistentInScope C b t scope fallback := by
  unfold GenLimit.PatientMachine.lowestConsistentInScope
  rw [consistentIndices_eq_of_eqOn_lt h]

private theorem lowestConsistent_eq_of_eqOn_lt
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {t fallback : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    GenLimit.PatientMachine.lowestConsistent C a t fallback =
      GenLimit.PatientMachine.lowestConsistent C b t fallback := by
  classical
  unfold GenLimit.PatientMachine.lowestConsistent
  by_cases ha : ∃ i, GenLimit.Consistent C a t i
  · have hb : ∃ i, GenLimit.Consistent C b t i := by
      simpa only [consistent_iff_of_eqOn_lt h] using ha
    rw [dif_pos ha, dif_pos hb]
    exact Nat.find_congr (Nat.find_spec ha)
      (fun n _ => consistent_iff_of_eqOn_lt h)
  · have hb : ¬∃ i, GenLimit.Consistent C b t i := by
      simpa only [← consistent_iff_of_eqOn_lt h] using ha
    rw [dif_neg ha, dif_neg hb]

private theorem backtrackDecision_eq_of_eqOn_lt
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.backtrackDecision C a t old =
      GenLimit.PatientMachine.backtrackDecision C b t old := by
  have hconsistent := consistentIndices_eq_of_eqOn_lt
    (C := C) (scope := old.scope) h
  have hsurvivors := survivingCriticalIndices_eq_of_eqOn_lt
    (C := C) (scope := old.scope) h
  have hhighest := highestSurvivor_eq_of_eqOn_lt
    (C := C) (scope := old.scope) (fallback := old.focus) h
  have hscope := lowestConsistentInScope_eq_of_eqOn_lt
    (C := C) (scope := old.scope) (fallback := old.focus) h
  have hglobal := lowestConsistent_eq_of_eqOn_lt
    (C := C) (fallback := old.focus) h
  simp only [GenLimit.PatientMachine.backtrackDecision]
  rw [hconsistent, hsurvivors, hhighest, hscope, hglobal]
  by_cases hb : ∃ j, GenLimit.Consistent C b (t + 1) j
  · have ha : ∃ j, GenLimit.Consistent C a (t + 1) j := by
      simpa only [consistent_iff_of_eqOn_lt h] using hb
    simp [ha, hb]
  · have ha : ¬∃ j, GenLimit.Consistent C a (t + 1) j := by
      simpa only [consistent_iff_of_eqOn_lt h] using hb
    simp [ha, hb]

private theorem stableDecision_eq_of_eqOn_lt
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.stableDecision C a t old =
      GenLimit.PatientMachine.stableDecision C b t old := by
  have hf := highestCritical_eq_of_eqOn_lt
    (C := C) (scope := old.scope + 1) (fallback := old.focus) h
  simp only [GenLimit.PatientMachine.stableDecision]
  split <;> simp [hf]

private theorem decide_eq_of_eqOn_lt
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.decide C a t old =
      GenLimit.PatientMachine.decide C b t old := by
  have hc := consistent_iff_of_eqOn_lt
    (C := C) (i := old.focus) h
  simp only [GenLimit.PatientMachine.decide]
  by_cases ha : GenLimit.Consistent C a (t + 1) old.focus
  · have hb := hc.mp ha
    simp [ha, hb, stableDecision_eq_of_eqOn_lt old h]
  · have hb : ¬GenLimit.Consistent C b (t + 1) old.focus :=
      fun hh => ha (hc.mpr hh)
    simp [ha, hb, backtrackDecision_eq_of_eqOn_lt old h]

private theorem leastAvailable_eq_of_eqOn_lt
    {C : GenLimit.LanguageFamily} (hinf : ∀ i, (C i).Infinite)
    {a b : ℕ → ℕ} {t used focus}
    (h : ∀ k, k < t → a k = b k) :
    GenLimit.PatientMachine.leastAvailable C hinf a t used focus =
      GenLimit.PatientMachine.leastAvailable C hinf b t used focus := by
  classical
  unfold GenLimit.PatientMachine.leastAvailable
  apply Nat.find_congr (Nat.find_spec
    (GenLimit.PatientMachine.available_exists C hinf a t used focus))
  intro x hx
  unfold GenLimit.PatientMachine.Available
  rw [sample_eq_of_eqOn_lt h]

private theorem processRound_eq_of_eqOn_lt
    (O : GenLimit.OracleFamily) {a b : ℕ → ℕ} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.processRound O a t old =
      GenLimit.PatientMachine.processRound O b t old := by
  have hd := decide_eq_of_eqOn_lt (C := O.language) old h
  simp only [GenLimit.PatientMachine.processRound]
  rw [hd]
  have hl := leastAvailable_eq_of_eqOn_lt O.infinite'
    (used := old.used)
    (focus := (GenLimit.PatientMachine.decide O.language b t old).focus) h
  rw [hl]

private theorem run_eq_of_eqOn_lt
    (O : GenLimit.OracleFamily) {a b : ℕ → ℕ} :
    ∀ t, (∀ k, k < t → a k = b k) →
      GenLimit.PatientMachine.run O a t = GenLimit.PatientMachine.run O b t := by
  intro t
  induction t with
  | zero => intro h; rfl
  | succ t ih =>
      intro h
      rw [GenLimit.PatientMachine.run_succ, GenLimit.PatientMachine.run_succ,
        ih (fun k hk => h k (by omega))]
      exact processRound_eq_of_eqOn_lt O _ h

private def prefixCompletion {t : ℕ} (xs : Fin t → ℕ) : ℕ → ℕ :=
  fun n => if hn : n < t then xs ⟨n, hn⟩ else 0

private theorem prefixCompletion_eq {t : ℕ} (xs : Fin t → ℕ)
    {k : ℕ} (hk : k < t) : prefixCompletion xs k = xs ⟨k, hk⟩ := by
  simp [prefixCompletion, hk]

noncomputable def patientGenerator (O : GenLimit.OracleFamily) :
    GenLimit.Generic.Generator ℕ :=
  fun t xs => match t with
    | 0 => 0
    | s + 1 => GenLimit.PatientMachine.output O (prefixCompletion xs) s

private theorem patientGenerator_output
    (O : GenLimit.OracleFamily) (input : ℕ → ℕ) (t : ℕ) :
    Stage3Case019.outputAfterInput (patientGenerator O) input t =
      GenLimit.PatientMachine.output O input t := by
  unfold Stage3Case019.outputAfterInput GenLimit.Generic.output patientGenerator
  simp only
  have hrun :
      GenLimit.PatientMachine.run O
          (prefixCompletion (fun i : Fin (t + 1) => input i)) (t + 1) =
        GenLimit.PatientMachine.run O input (t + 1) := by
    apply run_eq_of_eqOn_lt O (t + 1)
    intro k hk
    exact prefixCompletion_eq _ hk
  unfold GenLimit.PatientMachine.output
  rw [hrun]

private theorem contamination_of_level
    {input : ℕ → ℕ} {L : Set ℕ} {q : ℕ}
    (h : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input L q) :
    GenLimit.InfiniteContamination.FiniteNoiseFiniteOmissionEnumeration input L := by
  refine ⟨h.1, ?_, ?_⟩
  · exact (GenLimit.InfiniteContamination.finiteNoise_iff_valuesOutside_finite_of_injective h.1).2
      ((GenLimit.Generic.setDifferenceAtMost_iff_finite_ncard_le
        (Set.range input) L q).1 h.2.2).1
  · unfold GenLimit.InfiniteContamination.FiniteOmissions
    rw [Set.diff_eq_empty.mpr h.2.1]
    exact Set.finite_empty


private theorem separation_negative (q : ℕ) (gen : GenLimit.Generic.Generator ℤ) :
    ∃ K ∈ GenLimit.NoiseLossFeedback.finiteOmissionClass q,
      ∃ input : GenLimit.Generic.Stream ℤ,
        GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
            input K (q + 1) ∧
          ¬Stage3Case019.SampleFreshGeneratesAfterInput
            input (Stage3Case019.outputAfterInput gen input) K := by
  have hn := GenLimit.NoiseLossFeedback.finiteNoiseLevel_lower q
  unfold GenLimit.NoiseLossFeedback.GeneratableInLimitWithNoiseLevel at hn
  unfold GenLimit.NoiseLossFeedback.IsLimitGeneratorWithNoiseLevel at hn
  push_neg at hn
  obtain ⟨K, hK, input, hinput, hfail⟩ := hn gen
  refine ⟨K, hK, input, hinput, ?_⟩
  intro hgood
  obtain ⟨T, hT⟩ := hgood
  obtain ⟨t, ht, hbad⟩ := hfail T
  exact hbad (by
    simpa [Stage3Case019.outputAfterInput,
      GenLimit.NoiseLossFeedback.CorrectAt,
      GenLimit.NoiseLossFeedback.outputAt,
      GenLimit.NoiseLossFeedback.observedThrough] using hT t ht)

end Case019

open Stage3Case019

theorem stage3_result : Stage3Case019.MainClaim := by
  sorry
