import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency

open Filter
open scoped Topology

namespace Stage3Case025

noncomputable def oracleOf
    (family : ℕ → Language) (hInfinite : ∀ i, (family i).Infinite) :
    GenLimit.OracleFamily where
  language := family
  infinite' := hInfinite
  query i x := by
    classical
    exact if x ∈ family i then true else false
  query_spec i x := by
    classical
    simp

def extendCurrent {t : ℕ} (xs : Fin (t + 1) → ℕ) : Stream :=
  fun n => if h : n < t + 1 then xs ⟨n, h⟩ else 0

theorem extendCurrent_eq {t : ℕ} (xs : Fin (t + 1) → ℕ) (n : ℕ)
    (hn : n < t + 1) :
    extendCurrent xs n = xs ⟨n, hn⟩ := by
  simp [extendCurrent, hn]

private theorem patient_run_congr
    (O : GenLimit.OracleFamily) (stream₁ stream₂ : Stream) :
    ∀ t, (∀ n, n < t → stream₁ n = stream₂ n) →
      GenLimit.PatientMachine.run O stream₁ t =
        GenLimit.PatientMachine.run O stream₂ t := by
  intro t
  induction t with
  | zero =>
      intro _
      rfl
  | succ t ih =>
      intro hprefix
      have hrun := ih (fun n hn => hprefix n (Nat.lt_succ_of_lt hn))
      have hsample_t : GenLimit.sample stream₁ t = GenLimit.sample stream₂ t := by
        ext x
        simp only [GenLimit.mem_sample_iff]
        constructor
        · rintro ⟨n, hn, rfl⟩
          exact ⟨n, hn, (hprefix n (Nat.lt_succ_of_lt hn)).symm⟩
        · rintro ⟨n, hn, rfl⟩
          exact ⟨n, hn, hprefix n (Nat.lt_succ_of_lt hn)⟩
      have hsample_succ :
          GenLimit.sample stream₁ (t + 1) =
            GenLimit.sample stream₂ (t + 1) := by
        ext x
        simp only [GenLimit.mem_sample_iff]
        constructor
        · rintro ⟨n, hn, rfl⟩
          exact ⟨n, hn, (hprefix n hn).symm⟩
        · rintro ⟨n, hn, rfl⟩
          exact ⟨n, hn, hprefix n hn⟩
      have hconsistent_t (i : ℕ) :
          GenLimit.Consistent O.language stream₁ t i ↔
            GenLimit.Consistent O.language stream₂ t i := by
        simp only [GenLimit.Consistent, hsample_t]
      have hconsistent_succ (i : ℕ) :
          GenLimit.Consistent O.language stream₁ (t + 1) i ↔
            GenLimit.Consistent O.language stream₂ (t + 1) i := by
        simp only [GenLimit.Consistent, hsample_succ]
      have hcritical_t (i : ℕ) :
          GenLimit.RecursiveCritical O.language stream₁ t i ↔
            GenLimit.RecursiveCritical O.language stream₂ t i := by
        induction i using Nat.strong_induction_on with
        | h i ih =>
            cases i with
            | zero => simpa [GenLimit.RecursiveCritical] using hconsistent_t 0
            | succ i =>
                simp only [GenLimit.RecursiveCritical, hconsistent_t]
                constructor
                · rintro ⟨hcon, hrest⟩
                  refine ⟨hcon, ?_⟩
                  intro j hj hjcrit
                  exact hrest j hj ((ih j (Nat.lt_succ_of_le hj)).mpr hjcrit)
                · rintro ⟨hcon, hrest⟩
                  refine ⟨hcon, ?_⟩
                  intro j hj hjcrit
                  exact hrest j hj ((ih j (Nat.lt_succ_of_le hj)).mp hjcrit)
      have hcritical_succ (i : ℕ) :
          GenLimit.RecursiveCritical O.language stream₁ (t + 1) i ↔
            GenLimit.RecursiveCritical O.language stream₂ (t + 1) i := by
        induction i using Nat.strong_induction_on with
        | h i ih =>
            cases i with
            | zero => simpa [GenLimit.RecursiveCritical] using hconsistent_succ 0
            | succ i =>
                simp only [GenLimit.RecursiveCritical, hconsistent_succ]
                constructor
                · rintro ⟨hcon, hrest⟩
                  refine ⟨hcon, ?_⟩
                  intro j hj hjcrit
                  exact hrest j hj ((ih j (Nat.lt_succ_of_le hj)).mpr hjcrit)
                · rintro ⟨hcon, hrest⟩
                  refine ⟨hcon, ?_⟩
                  intro j hj hjcrit
                  exact hrest j hj ((ih j (Nat.lt_succ_of_le hj)).mp hjcrit)
      have hconsistent_t_fun :
          GenLimit.Consistent O.language stream₁ t =
            GenLimit.Consistent O.language stream₂ t := by
        funext i
        exact propext (hconsistent_t i)
      have hconsistent_succ_fun :
          GenLimit.Consistent O.language stream₁ (t + 1) =
            GenLimit.Consistent O.language stream₂ (t + 1) := by
        funext i
        exact propext (hconsistent_succ i)
      have hcritical_t_fun :
          GenLimit.RecursiveCritical O.language stream₁ t =
            GenLimit.RecursiveCritical O.language stream₂ t := by
        funext i
        exact propext (hcritical_t i)
      have hcritical_succ_fun :
          GenLimit.RecursiveCritical O.language stream₁ (t + 1) =
            GenLimit.RecursiveCritical O.language stream₂ (t + 1) := by
        funext i
        exact propext (hcritical_succ i)
      rw [GenLimit.PatientMachine.run_succ,
        GenLimit.PatientMachine.run_succ, hrun]
      simp only [GenLimit.PatientMachine.processRound,
        GenLimit.PatientMachine.decide,
        GenLimit.PatientMachine.stableDecision,
        GenLimit.PatientMachine.backtrackDecision,
        GenLimit.PatientMachine.consistentIndices,
        GenLimit.PatientMachine.criticalIndices,
        GenLimit.PatientMachine.survivingCriticalIndices,
        GenLimit.PatientMachine.highestCritical,
        GenLimit.PatientMachine.highestSurvivor,
        GenLimit.PatientMachine.lowestConsistentInScope,
        GenLimit.PatientMachine.lowestConsistent,
        GenLimit.PatientMachine.leastAvailable,
        GenLimit.PatientMachine.Available]
      rfl

private theorem patient_output_congr
    (O : GenLimit.OracleFamily) (stream₁ stream₂ : Stream) (t : ℕ)
    (hprefix : ∀ n, n < t + 1 → stream₁ n = stream₂ n) :
    GenLimit.PatientMachine.output O stream₁ t =
      GenLimit.PatientMachine.output O stream₂ t := by
  unfold GenLimit.PatientMachine.output
  rw [patient_run_congr O stream₁ stream₂ (t + 1) hprefix]

noncomputable def patientOnline (O : GenLimit.OracleFamily) : OnlineGenerator :=
  fun t xs _ => GenLimit.PatientMachine.output O (extendCurrent xs) t

theorem patientOnline_follows (O : GenLimit.OracleFamily) (input : Stream) :
    Follows (patientOnline O) input (GenLimit.PatientMachine.output O input) := by
  intro t
  apply patient_output_congr
  intro n hn
  symm
  exact extendCurrent_eq (fun i : Fin (t + 1) => input i) n hn

theorem stage3_positive_engine : PositivePresentationHalfDensity := by
  intro family hInfinite
  let O := oracleOf family hInfinite
  refine ⟨patientOnline O, ?_⟩
  intro i input hP
  let output := GenLimit.PatientMachine.output O input
  refine ⟨output, patientOnline_follows O input, ?_, ?_⟩
  · obtain ⟨⟨T, hNovel⟩, _⟩ :=
      GenLimit.PatientMachine.patientScope_generation_and_lowerDensity O input hP
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨hmem, hfresh, hdistinct⟩ := hNovel t ht
    refine ⟨hmem, ?_, hdistinct⟩
    intro hseen
    rw [GenLimit.mem_sample_iff] at hseen
    obtain ⟨s, hs, heq⟩ := hseen
    exact hfresh s (Nat.lt_succ_iff.mp hs) heq
  · simpa [output, O] using
      GenLimit.PatientMachine.patientScope_lowerDensity_half O input hP

end Stage3Case025

theorem stage3_result : Stage3Case025.MainClaim := by
  sorry
