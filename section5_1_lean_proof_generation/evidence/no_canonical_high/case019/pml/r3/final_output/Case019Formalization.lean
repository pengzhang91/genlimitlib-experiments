import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import GenLimit.Paper17_InfiniteContamination.EvenDensity

open Stage3Case019

namespace Case019

open GenLimit

theorem sample_eq_of_eq_below
    {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.sample a t = GenLimit.sample b t := by
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor <;> rintro ⟨n, hn, rfl⟩
  · exact ⟨n, hn, (h n hn).symm⟩
  · exact ⟨n, hn, h n hn⟩

theorem consistent_iff_of_eq_below
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {t i : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.Consistent C a t i ↔ GenLimit.Consistent C b t i := by
  change (↑(GenLimit.sample a t) : Set ℕ) ⊆ C i ↔
    (↑(GenLimit.sample b t) : Set ℕ) ⊆ C i
  rw [sample_eq_of_eq_below h]

theorem recursiveCritical_iff_of_eq_below
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {t i : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.RecursiveCritical C a t i ↔
      GenLimit.RecursiveCritical C b t i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero =>
          simpa [GenLimit.RecursiveCritical] using
            consistent_iff_of_eq_below (C := C) (i := 0) h
      | succ i =>
          simp only [GenLimit.RecursiveCritical]
          rw [consistent_iff_of_eq_below h]
          constructor
          · rintro ⟨hcon, hsub⟩
            refine ⟨hcon, ?_⟩
            intro j hj hjcrit
            exact hsub j hj ((ih j (by omega)).2 hjcrit)
          · rintro ⟨hcon, hsub⟩
            refine ⟨hcon, ?_⟩
            intro j hj hjcrit
            exact hsub j hj ((ih j (by omega)).1 hjcrit)

theorem processRound_eq_of_eq_below
    (O : GenLimit.OracleFamily) {a b : ℕ → ℕ} (t : ℕ)
    (old : GenLimit.PatientMachine.State)
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.processRound O a t old =
      GenLimit.PatientMachine.processRound O b t old := by
  classical
  have hs : ∀ u, u ≤ t + 1 →
      GenLimit.sample a u = GenLimit.sample b u := by
    intro u hu
    exact sample_eq_of_eq_below (fun n hn => h n (lt_of_lt_of_le hn hu))
  have hc : ∀ u, u ≤ t + 1 → ∀ i,
      GenLimit.Consistent O.language a u i ↔
        GenLimit.Consistent O.language b u i := by
    intro u hu i
    exact consistent_iff_of_eq_below
      (fun n hn => h n (lt_of_lt_of_le hn hu))
  have hr : ∀ u, u ≤ t + 1 → ∀ i,
      GenLimit.RecursiveCritical O.language a u i ↔
        GenLimit.RecursiveCritical O.language b u i := by
    intro u hu i
    exact recursiveCritical_iff_of_eq_below
      (fun n hn => h n (lt_of_lt_of_le hn hu))
  have hc1 : ∀ i,
      GenLimit.Consistent O.language a (t + 1) i ↔
        GenLimit.Consistent O.language b (t + 1) i :=
    hc (t + 1) (by omega)
  have hr0 : ∀ i,
      GenLimit.RecursiveCritical O.language a t i ↔
        GenLimit.RecursiveCritical O.language b t i :=
    hr t (by omega)
  have hr1 : ∀ i,
      GenLimit.RecursiveCritical O.language a (t + 1) i ↔
        GenLimit.RecursiveCritical O.language b (t + 1) i :=
    hr (t + 1) (by omega)
  have hs1 : GenLimit.sample a (t + 1) =
      GenLimit.sample b (t + 1) := hs (t + 1) (by omega)
  have hc1_eq :
      GenLimit.Consistent O.language a (t + 1) =
        GenLimit.Consistent O.language b (t + 1) := by
    funext i
    exact propext (hc1 i)
  have hr0_eq :
      GenLimit.RecursiveCritical O.language a t =
        GenLimit.RecursiveCritical O.language b t := by
    funext i
    exact propext (hr0 i)
  have hr1_eq :
      GenLimit.RecursiveCritical O.language a (t + 1) =
        GenLimit.RecursiveCritical O.language b (t + 1) := by
    funext i
    exact propext (hr1 i)
  have hd :
      GenLimit.PatientMachine.decide O.language a t old =
        GenLimit.PatientMachine.decide O.language b t old := by
    unfold GenLimit.PatientMachine.decide
    unfold GenLimit.PatientMachine.stableDecision
    unfold GenLimit.PatientMachine.backtrackDecision
    unfold GenLimit.PatientMachine.highestCritical
    unfold GenLimit.PatientMachine.highestSurvivor
    unfold GenLimit.PatientMachine.lowestConsistentInScope
    unfold GenLimit.PatientMachine.lowestConsistent
    unfold GenLimit.PatientMachine.criticalIndices
    unfold GenLimit.PatientMachine.survivingCriticalIndices
    unfold GenLimit.PatientMachine.consistentIndices
    rw [hc1_eq, hr0_eq, hr1_eq]
  have havail : ∀ focus x,
      GenLimit.PatientMachine.Available O.language a (t + 1)
          old.used focus x ↔
        GenLimit.PatientMachine.Available O.language b (t + 1)
          old.used focus x := by
    intro focus x
    unfold GenLimit.PatientMachine.Available
    rw [hs1]
  have hx : ∀ focus,
      GenLimit.PatientMachine.leastAvailable O.language O.infinite'
          a (t + 1) old.used focus =
        GenLimit.PatientMachine.leastAvailable O.language O.infinite'
          b (t + 1) old.used focus := by
    intro focus
    apply Nat.le_antisymm
    · apply GenLimit.PatientMachine.leastAvailable_minimal
      exact (havail focus _).2
        (GenLimit.PatientMachine.leastAvailable_spec
          O.language O.infinite' b (t + 1) old.used focus)
    · apply GenLimit.PatientMachine.leastAvailable_minimal
      exact (havail focus _).1
        (GenLimit.PatientMachine.leastAvailable_spec
          O.language O.infinite' a (t + 1) old.used focus)
  unfold GenLimit.PatientMachine.processRound
  rw [hd]
  simp only [hx]


theorem run_eq_of_eq_below
    (O : GenLimit.OracleFamily) {a b : ℕ → ℕ} :
    ∀ t, (∀ n, n < t → a n = b n) →
      GenLimit.PatientMachine.run O a t =
        GenLimit.PatientMachine.run O b t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
      intro h
      rw [GenLimit.PatientMachine.run_succ,
        GenLimit.PatientMachine.run_succ, ih (fun n hn => h n (by omega))]
      exact processRound_eq_of_eq_below O t _ h

theorem patient_output_eq_of_eq_below
    (O : GenLimit.OracleFamily) {a b : ℕ → ℕ} (t : ℕ)
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.output O a t =
      GenLimit.PatientMachine.output O b t := by
  unfold GenLimit.PatientMachine.output
  rw [run_eq_of_eq_below O (t + 1) h]

noncomputable def patientGenerator
    (O : GenLimit.OracleFamily) : Stage3Case019.Generator ℕ :=
  fun t history =>
    if _ht : 0 < t then
      GenLimit.PatientMachine.output O
        (fun n => if hn : n < t then history ⟨n, hn⟩ else 0) (t - 1)
    else 0

theorem outputAfterInput_patientGenerator
    (O : GenLimit.OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    Stage3Case019.outputAfterInput (patientGenerator O) stream t =
      GenLimit.PatientMachine.output O stream t := by
  unfold Stage3Case019.outputAfterInput GenLimit.Generic.output
  simp only [patientGenerator, Nat.zero_lt_succ, dite_true, Nat.add_sub_cancel]
  apply patient_output_eq_of_eq_below
  intro n hn
  rw [dif_pos (by omega)]

/-- The exact eventual validity-and-novelty part of the countable clause. -/
theorem countable_eventual_novelty
    (q : ℕ) (family : Stage3Case019.LanguageFamily ℕ)
    (hinfinite : ∀ i, (family i).Infinite) :
    ∃ gen : Stage3Case019.Generator ℕ,
      ∀ i (input : Stage3Case019.Stream ℕ),
        GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
            input (family i) q →
          GenLimit.NovelGeneratesInLimit
            input (Stage3Case019.outputAfterInput gen input) (family i) := by
  classical
  let O : GenLimit.OracleFamily :=
    { language := family
      infinite' := hinfinite
      query := fun i x => if x ∈ family i then true else false
      query_spec := by simp }
  let expanded := GenLimit.InfiniteContamination.finiteExpansionOracleFamily O
  refine ⟨patientGenerator expanded, ?_⟩
  intro i input hinput
  have houtside : (Set.range input \ family i).Finite := by
    obtain ⟨F, hF, _⟩ := hinput.2.2
    rw [← hF]
    exact F.finite_toSet
  have hcontam :
      GenLimit.InfiniteContamination.FiniteNoiseFiniteOmissionEnumeration
        input (O.language i) := by
    refine ⟨hinput.1, ?_, ?_⟩
    · exact
        (GenLimit.InfiniteContamination.finiteNoise_iff_valuesOutside_finite_of_injective
          hinput.1).2 houtside
    · unfold GenLimit.InfiniteContamination.FiniteOmissions
      change (family i \ Set.range input).Finite
      rw [Set.diff_eq_empty.mpr hinput.2.1]
      exact Set.finite_empty
  obtain ⟨j, _hjBase, hjPresents⟩ :=
    GenLimit.InfiniteContamination.exists_finiteExpansion_index_for_stream
      O hcontam
  have hrun :=
    GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
      expanded input hjPresents
  obtain ⟨Tvalid, hvalid⟩ := hrun.1
  have hextraneous : (expanded.language j \ family i).Finite := by
    rw [← hjPresents]
    exact houtside
  obtain ⟨Tseen, hseen⟩ :=
    GenLimit.Generic.finset_eventually_subset_sample
      hjPresents hextraneous.toFinset (by
        intro x hx
        exact ((Set.Finite.mem_toFinset hextraneous).mp hx).1)
  refine ⟨max Tvalid Tseen, ?_⟩
  intro t ht
  have htValid : Tvalid ≤ t := (Nat.le_max_left _ _).trans ht
  have htSeen : Tseen ≤ t := (Nat.le_max_right _ _).trans ht
  have hv := hvalid t htValid
  have hfresh :
      GenLimit.PatientMachine.output expanded input t ∉
        GenLimit.sample input (t + 1) := by
    intro hmem
    obtain ⟨s, hs, heq⟩ := GenLimit.mem_sample_iff.mp hmem
    exact hv.2.1 s (by omega) heq
  have htarget : GenLimit.PatientMachine.output expanded input t ∈ family i := by
    by_contra houtside
    have hbad :
        GenLimit.PatientMachine.output expanded input t ∈
          hextraneous.toFinset :=
      (Set.Finite.mem_toFinset hextraneous).2 ⟨hv.1, houtside⟩
    have hsample :
        GenLimit.PatientMachine.output expanded input t ∈
          GenLimit.sample input t :=
      by
        simpa [GenLimit.Generic.sample, GenLimit.sample] using
          (GenLimit.Generic.sample_mono htSeen (hseen hbad))
    exact hfresh (GenLimit.sample_mono (by omega) hsample)
  rw [outputAfterInput_patientGenerator]
  refine ⟨htarget, hfresh, ?_⟩
  intro s hs
  rw [outputAfterInput_patientGenerator]
  exact hv.2.2 s hs

end Case019

/-- Checked partial milestone: every countable family has one generator with
exact eventual validity and novelty at every finite distinct-noise level. -/
theorem stage3_countable_eventual_novelty :
    ∀ (q : ℕ) (family : Stage3Case019.LanguageFamily ℕ),
      (∀ i, (family i).Infinite) →
        ∃ gen : Stage3Case019.Generator ℕ,
          ∀ i (input : Stage3Case019.Stream ℕ),
            GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
                input (family i) q →
              GenLimit.NovelGeneratesInLimit
                input (Stage3Case019.outputAfterInput gen input) (family i) := by
  intro q family hinfinite
  exact Case019.countable_eventual_novelty q family hinfinite
