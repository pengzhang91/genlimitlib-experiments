import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency

open Set Filter
open scoped Topology

namespace Stage3Case025

noncomputable def oracleOfFamily (family : ℕ → Language)
    (hinf : ∀ i, (family i).Infinite) : GenLimit.OracleFamily where
  language := family
  infinite' := hinf
  query i x := by
    classical
    exact if x ∈ family i then true else false
  query_spec i x := by
    classical
    simp

noncomputable def extendInput {t : ℕ} (input : Fin (t + 1) → ℕ) : Stream :=
  fun n => if h : n < t + 1 then input ⟨n, h⟩ else 0

noncomputable def patientOnlineGenerator (O : GenLimit.OracleFamily) : OnlineGenerator :=
  fun t input _ => GenLimit.PatientMachine.output O (extendInput input) t

private theorem sample_eq_of_prefix_eq
    {stream₁ stream₂ : Stream} {t : ℕ}
    (h : ∀ n, n < t → stream₁ n = stream₂ n) :
    GenLimit.sample stream₁ t = GenLimit.sample stream₂ t := by
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, (h n hn).symm⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, h n hn⟩

private theorem consistent_eq_of_sample_eq
    {family : GenLimit.LanguageFamily} {stream₁ stream₂ : Stream} {t i : ℕ}
    (h : GenLimit.sample stream₁ t = GenLimit.sample stream₂ t) :
    GenLimit.Consistent family stream₁ t i =
      GenLimit.Consistent family stream₂ t i := by
  apply propext
  simp only [GenLimit.Consistent, h]

private theorem recursiveCritical_eq_of_sample_eq
    {family : GenLimit.LanguageFamily} {stream₁ stream₂ : Stream} {t : ℕ}
    (h : GenLimit.sample stream₁ t = GenLimit.sample stream₂ t) :
    GenLimit.RecursiveCritical family stream₁ t =
      GenLimit.RecursiveCritical family stream₂ t := by
  funext i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero =>
          simp only [GenLimit.RecursiveCritical]
          exact consistent_eq_of_sample_eq h
      | succ n =>
          rw [GenLimit.RecursiveCritical, GenLimit.RecursiveCritical]
          apply propext
          constructor
          · rintro ⟨hcon, hall⟩
            refine ⟨?_, ?_⟩
            · rwa [← consistent_eq_of_sample_eq h]
            · intro j hj hcrit
              apply hall j hj
              rwa [ih j (Nat.lt_succ_of_le hj)]
          · rintro ⟨hcon, hall⟩
            refine ⟨?_, ?_⟩
            · rwa [consistent_eq_of_sample_eq h]
            · intro j hj hcrit
              apply hall j hj
              rwa [← ih j (Nat.lt_succ_of_le hj)]

private theorem leastAvailable_eq_of_sample_eq
    (family : GenLimit.LanguageFamily) (hinf : ∀ i, (family i).Infinite)
    {stream₁ stream₂ : Stream} {t : ℕ} (used : Finset ℕ) (focus : ℕ)
    (h : GenLimit.sample stream₁ t = GenLimit.sample stream₂ t) :
    GenLimit.PatientMachine.leastAvailable family hinf stream₁ t used focus =
      GenLimit.PatientMachine.leastAvailable family hinf stream₂ t used focus := by
  classical
  unfold GenLimit.PatientMachine.leastAvailable
  congr 1
  funext n
  apply propext
  simp only [GenLimit.PatientMachine.Available, h]

private theorem decide_eq_of_samples
    (O : GenLimit.OracleFamily) {stream₁ stream₂ : Stream} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (ht : GenLimit.sample stream₁ t = GenLimit.sample stream₂ t)
    (hs : GenLimit.sample stream₁ (t + 1) = GenLimit.sample stream₂ (t + 1)) :
    GenLimit.PatientMachine.decide O.language stream₁ t old =
      GenLimit.PatientMachine.decide O.language stream₂ t old := by
  classical
  have hconsT : GenLimit.Consistent O.language stream₁ t =
      GenLimit.Consistent O.language stream₂ t := by
    funext i
    exact consistent_eq_of_sample_eq ht
  have hconsS : GenLimit.Consistent O.language stream₁ (t + 1) =
      GenLimit.Consistent O.language stream₂ (t + 1) := by
    funext i
    exact consistent_eq_of_sample_eq hs
  have hcritT : GenLimit.RecursiveCritical O.language stream₁ t =
      GenLimit.RecursiveCritical O.language stream₂ t :=
    recursiveCritical_eq_of_sample_eq ht
  have hcritS : GenLimit.RecursiveCritical O.language stream₁ (t + 1) =
      GenLimit.RecursiveCritical O.language stream₂ (t + 1) :=
    recursiveCritical_eq_of_sample_eq hs
  simp only [GenLimit.PatientMachine.decide,
    GenLimit.PatientMachine.stableDecision,
    GenLimit.PatientMachine.backtrackDecision,
    GenLimit.PatientMachine.consistentIndices,
    GenLimit.PatientMachine.criticalIndices,
    GenLimit.PatientMachine.survivingCriticalIndices,
    GenLimit.PatientMachine.highestCritical,
    GenLimit.PatientMachine.highestSurvivor,
    GenLimit.PatientMachine.lowestConsistentInScope,
    GenLimit.PatientMachine.lowestConsistent,
    hconsT, hconsS, hcritT, hcritS]

private theorem run_eq_of_prefix_eq
    (O : GenLimit.OracleFamily) {stream₁ stream₂ : Stream} :
    ∀ t, (∀ n, n < t → stream₁ n = stream₂ n) →
      GenLimit.PatientMachine.run O stream₁ t =
        GenLimit.PatientMachine.run O stream₂ t := by
  intro t
  induction t with
  | zero => intro; rfl
  | succ t ih =>
      intro hprefix
      have hprefix' : ∀ n, n < t → stream₁ n = stream₂ n :=
        fun n hn => hprefix n (Nat.lt.step hn)
      have hrun := ih hprefix'
      have hsampT := sample_eq_of_prefix_eq hprefix'
      have hsampS := sample_eq_of_prefix_eq hprefix
      rw [GenLimit.PatientMachine.run_succ,
        GenLimit.PatientMachine.run_succ, hrun]
      have hdec := decide_eq_of_samples O
        (GenLimit.PatientMachine.run O stream₂ t) hsampT hsampS
      have hleast :
          GenLimit.PatientMachine.leastAvailable O.language O.infinite'
              stream₁ (t + 1) (GenLimit.PatientMachine.run O stream₂ t).used
                (GenLimit.PatientMachine.decide O.language stream₂ t
                  (GenLimit.PatientMachine.run O stream₂ t)).focus =
            GenLimit.PatientMachine.leastAvailable O.language O.infinite'
              stream₂ (t + 1) (GenLimit.PatientMachine.run O stream₂ t).used
                (GenLimit.PatientMachine.decide O.language stream₂ t
                  (GenLimit.PatientMachine.run O stream₂ t)).focus :=
        leastAvailable_eq_of_sample_eq O.language O.infinite'
          (GenLimit.PatientMachine.run O stream₂ t).used
          (GenLimit.PatientMachine.decide O.language stream₂ t
            (GenLimit.PatientMachine.run O stream₂ t)).focus hsampS
      unfold GenLimit.PatientMachine.processRound
      simp only [hdec, hleast]


private theorem output_eq_of_prefix_eq
    (O : GenLimit.OracleFamily) {stream₁ stream₂ : Stream} {t : ℕ}
    (h : ∀ n, n < t + 1 → stream₁ n = stream₂ n) :
    GenLimit.PatientMachine.output O stream₁ t =
      GenLimit.PatientMachine.output O stream₂ t := by
  simp only [GenLimit.PatientMachine.output]
  rw [run_eq_of_prefix_eq O (t + 1) h]

private theorem extendInput_agrees (input : Stream) (t n : ℕ) (hn : n < t + 1) :
    extendInput (fun i : Fin (t + 1) => input i) n = input n := by
  simp [extendInput, hn]

theorem patientOnlineGenerator_follows
    (O : GenLimit.OracleFamily) (input : Stream) :
    Follows (patientOnlineGenerator O) input
      (GenLimit.PatientMachine.output O input) := by
  intro t
  symm
  apply output_eq_of_prefix_eq O
  intro n hn
  exact extendInput_agrees input t n hn


theorem positivePresentationHalfDensity : PositivePresentationHalfDensity := by
  intro family hinf
  let O := oracleOfFamily family hinf
  refine ⟨patientOnlineGenerator O, ?_⟩
  intro i input hpresents
  let output := GenLimit.PatientMachine.output O input
  have hmain := GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
    O input (z := i) hpresents
  refine ⟨output, patientOnlineGenerator_follows O input, ?_, ?_⟩
  · obtain ⟨T, hT⟩ := hmain.1
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨hmem, hinput, houtput⟩ := hT t ht
    refine ⟨hmem, ?_, houtput⟩
    intro hsample
    rw [GenLimit.mem_sample_iff] at hsample
    obtain ⟨s, hs, heq⟩ := hsample
    exact hinput s (Nat.le_of_lt_succ hs) heq
  · simpa [GenLimit.PatientMachine.patientLowerDensity, O, output,
      oracleOfFamily] using hmain.2

end Stage3Case025
