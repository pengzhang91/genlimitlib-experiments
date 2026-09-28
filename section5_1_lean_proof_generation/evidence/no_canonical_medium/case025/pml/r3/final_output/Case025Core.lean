import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency
import «output».Causality

open GenLimit
open Stage3Case025

namespace Case025Helpers

noncomputable def oracleOfFamily
    (family : ℕ → Stage3Case025.Language)
    (hInfinite : ∀ i, (family i).Infinite) : OracleFamily where
  language := family
  infinite' := hInfinite
  query i x := by
    classical
    exact if x ∈ family i then true else false
  query_spec i x := by
    classical
    simp

private def prefixCompletion
    (t : ℕ) (input : Fin (t + 1) → ℕ) : ℕ → ℕ :=
  fun n => if h : n < t + 1 then input ⟨n, h⟩ else 0

noncomputable def patientOnline (O : OracleFamily) : OnlineGenerator :=
  fun t input _ => PatientMachine.output O (prefixCompletion t input) t

private theorem prefixCompletion_eq
    (input : Stage3Case025.Stream) (t : ℕ) (n : ℕ) (hn : n < t + 1) :
    prefixCompletion t (fun i => input i) n = input n := by
  simp [prefixCompletion, hn]

 theorem patientOnline_follows
    (O : OracleFamily) (input : Stage3Case025.Stream) :
    Follows (patientOnline O) input (PatientMachine.output O input) := by
  intro t
  unfold patientOnline
  apply output_congr O
  intro n hn
  exact (prefixCompletion_eq input t n hn).symm

 theorem positiveEngine : PositivePresentationHalfDensity := by
  intro family hInfinite
  let O := oracleOfFamily family hInfinite
  refine ⟨patientOnline O, ?_⟩
  intro i input hP
  refine ⟨PatientMachine.output O input, patientOnline_follows O input, ?_, ?_⟩
  · obtain ⟨hNovel, _⟩ :=
      PatientMachine.patientScope_generation_and_lowerDensity O input hP
    obtain ⟨T, hT⟩ := hNovel
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨hmem, hinput, houtput⟩ := hT t ht
    refine ⟨hmem, ?_, houtput⟩
    intro hsample
    rw [mem_sample_iff] at hsample
    obtain ⟨s, hs, heq⟩ := hsample
    exact hinput s (Nat.lt_succ_iff.mp hs) heq
  · obtain ⟨_, hDensity⟩ :=
      PatientMachine.patientScope_generation_and_lowerDensity O input hP
    exact hDensity

end Case025Helpers
