import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency

open Set Filter

namespace Stage3Case025Formalization

noncomputable def oracleOfFamily
    (family : ℕ → Stage3Case025.Language)
    (hInfinite : ∀ i, (family i).Infinite) : GenLimit.OracleFamily where
  language := family
  infinite' := hInfinite
  query i x := by
    classical
    exact if x ∈ family i then true else false
  query_spec i x := by
    classical
    simp

def prefixExtension (t : ℕ) (xs : Fin (t + 1) → ℕ) : ℕ → ℕ :=
  fun n => if h : n < t + 1 then xs ⟨n, h⟩ else 0

theorem prefixExtension_eq
    (t : ℕ) (xs : Fin (t + 1) → ℕ) {n : ℕ} (hn : n < t + 1) :
    prefixExtension t xs n = xs ⟨n, hn⟩ := by
  simp [prefixExtension, hn]

theorem basicSample_eq_of_eqOn
    {stream₁ stream₂ : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t → stream₁ n = stream₂ n) :
    GenLimit.sample stream₁ t = GenLimit.sample stream₂ t := by
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor <;> rintro ⟨n, hn, rfl⟩
  · exact ⟨n, hn, (h n hn).symm⟩
  · exact ⟨n, hn, h n hn⟩

theorem recursiveCritical_congr
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : ℕ → ℕ} {t : ℕ}
    (hcon : ∀ i,
      GenLimit.Consistent C stream₁ t i ↔
        GenLimit.Consistent C stream₂ t i) :
    ∀ i,
      GenLimit.RecursiveCritical C stream₁ t i ↔
        GenLimit.RecursiveCritical C stream₂ t i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero => simpa only [GenLimit.RecursiveCritical] using hcon 0
      | succ n =>
          simp only [GenLimit.RecursiveCritical, hcon]
          constructor
          · rintro ⟨hconsistent, hcritical⟩
            refine ⟨hconsistent, ?_⟩
            intro j hj hjcritical
            exact hcritical j hj ((ih j (by omega)).mpr hjcritical)
          · rintro ⟨hconsistent, hcritical⟩
            refine ⟨hconsistent, ?_⟩
            intro j hj hjcritical
            exact hcritical j hj ((ih j (by omega)).mp hjcritical)

theorem patientRun_eq_of_eqOn
    (O : GenLimit.OracleFamily)
    {stream₁ stream₂ : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t → stream₁ n = stream₂ n) :
    GenLimit.PatientMachine.run O stream₁ t =
      GenLimit.PatientMachine.run O stream₂ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [GenLimit.PatientMachine.run_succ,
        GenLimit.PatientMachine.run_succ]
      have hprev : ∀ n, n < t → stream₁ n = stream₂ n :=
        fun n hn => h n (Nat.lt.step hn)
      rw [ih hprev]
      let old := GenLimit.PatientMachine.run O stream₂ t
      have hsamplePrev :
          GenLimit.sample stream₁ t = GenLimit.sample stream₂ t :=
        basicSample_eq_of_eqOn hprev
      have hsampleNow :
          GenLimit.sample stream₁ (t + 1) =
            GenLimit.sample stream₂ (t + 1) :=
        basicSample_eq_of_eqOn h
      have hconPrev (i : ℕ) :
          GenLimit.Consistent O.language stream₁ t i ↔
            GenLimit.Consistent O.language stream₂ t i := by
        simp only [GenLimit.Consistent, hsamplePrev]
      have hconNow (i : ℕ) :
          GenLimit.Consistent O.language stream₁ (t + 1) i ↔
            GenLimit.Consistent O.language stream₂ (t + 1) i := by
        simp only [GenLimit.Consistent, hsampleNow]
      have hpredNow :
          GenLimit.Consistent O.language stream₁ (t + 1) =
            GenLimit.Consistent O.language stream₂ (t + 1) := by
        funext i
        exact propext (hconNow i)
      have hcriticalPrev (i : ℕ) :
          GenLimit.RecursiveCritical O.language stream₁ t i ↔
            GenLimit.RecursiveCritical O.language stream₂ t i :=
        recursiveCritical_congr O.language hconPrev i
      have hcriticalNow (i : ℕ) :
          GenLimit.RecursiveCritical O.language stream₁ (t + 1) i ↔
            GenLimit.RecursiveCritical O.language stream₂ (t + 1) i :=
        recursiveCritical_congr O.language hconNow i
      have hconsistentIndices (scope : ℕ) :
          GenLimit.PatientMachine.consistentIndices O.language stream₁
              (t + 1) scope =
            GenLimit.PatientMachine.consistentIndices O.language stream₂
              (t + 1) scope := by
        ext i
        simp only [GenLimit.PatientMachine.mem_consistentIndices]
        rw [hconNow i]
      have hcriticalIndices (scope : ℕ) :
          GenLimit.PatientMachine.criticalIndices O.language stream₁
              (t + 1) scope =
            GenLimit.PatientMachine.criticalIndices O.language stream₂
              (t + 1) scope := by
        ext i
        simp only [GenLimit.PatientMachine.mem_criticalIndices]
        rw [hcriticalNow i]
      have hsurvivingIndices (scope : ℕ) :
          GenLimit.PatientMachine.survivingCriticalIndices O.language stream₁
              t scope =
            GenLimit.PatientMachine.survivingCriticalIndices O.language stream₂
              t scope := by
        ext i
        simp only [GenLimit.PatientMachine.mem_survivingCriticalIndices]
        rw [hcriticalPrev i, hcriticalNow i]
      have hhighestCritical (scope fallback : ℕ) :
          GenLimit.PatientMachine.highestCritical O.language stream₁
              (t + 1) scope fallback =
            GenLimit.PatientMachine.highestCritical O.language stream₂
              (t + 1) scope fallback := by
        simp only [GenLimit.PatientMachine.highestCritical]
        rw [hcriticalIndices scope]
      have hhighestSurvivor (scope fallback : ℕ) :
          GenLimit.PatientMachine.highestSurvivor O.language stream₁
              t scope fallback =
            GenLimit.PatientMachine.highestSurvivor O.language stream₂
              t scope fallback := by
        simp only [GenLimit.PatientMachine.highestSurvivor]
        rw [hsurvivingIndices scope]
      have hlowestInScope (scope fallback : ℕ) :
          GenLimit.PatientMachine.lowestConsistentInScope O.language stream₁
              (t + 1) scope fallback =
            GenLimit.PatientMachine.lowestConsistentInScope O.language stream₂
              (t + 1) scope fallback := by
        simp only [GenLimit.PatientMachine.lowestConsistentInScope]
        rw [hconsistentIndices scope]
      have hlowest (fallback : ℕ) :
          GenLimit.PatientMachine.lowestConsistent O.language stream₁
              (t + 1) fallback =
            GenLimit.PatientMachine.lowestConsistent O.language stream₂
              (t + 1) fallback := by
        simp only [GenLimit.PatientMachine.lowestConsistent]
        rw [hpredNow]
      have hstable :
          GenLimit.PatientMachine.stableDecision O.language stream₁ t old =
            GenLimit.PatientMachine.stableDecision O.language stream₂ t old := by
        simp only [GenLimit.PatientMachine.stableDecision]
        rw [hhighestCritical]
      have hbacktrack :
          GenLimit.PatientMachine.backtrackDecision O.language stream₁ t old =
            GenLimit.PatientMachine.backtrackDecision O.language stream₂ t old := by
        simp only [GenLimit.PatientMachine.backtrackDecision]
        rw [hconsistentIndices, hsurvivingIndices, hhighestSurvivor,
          hlowestInScope, hpredNow, hlowest]
      have hdecide :
          GenLimit.PatientMachine.decide O.language stream₁ t old =
            GenLimit.PatientMachine.decide O.language stream₂ t old := by
        simp only [GenLimit.PatientMachine.decide]
        rw [propext (hconNow old.focus), hstable, hbacktrack]
      have hleast (used : Finset ℕ) (focus : ℕ) :
          GenLimit.PatientMachine.leastAvailable O.language O.infinite'
              stream₁ (t + 1) used focus =
            GenLimit.PatientMachine.leastAvailable O.language O.infinite'
              stream₂ (t + 1) used focus := by
        apply Nat.le_antisymm
        · apply GenLimit.PatientMachine.leastAvailable_minimal
          have hspec := GenLimit.PatientMachine.leastAvailable_spec
            O.language O.infinite' stream₂ (t + 1) used focus
          simpa only [GenLimit.PatientMachine.Available, hsampleNow] using hspec
        · apply GenLimit.PatientMachine.leastAvailable_minimal
          have hspec := GenLimit.PatientMachine.leastAvailable_spec
            O.language O.infinite' stream₁ (t + 1) used focus
          simpa only [GenLimit.PatientMachine.Available, hsampleNow] using hspec
      simp only [old, GenLimit.PatientMachine.processRound]
      rw [hdecide, hleast]

theorem patientOutput_eq_of_eqOn
    (O : GenLimit.OracleFamily)
    {stream₁ stream₂ : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t + 1 → stream₁ n = stream₂ n) :
    GenLimit.PatientMachine.output O stream₁ t =
      GenLimit.PatientMachine.output O stream₂ t := by
  unfold GenLimit.PatientMachine.output
  rw [patientRun_eq_of_eqOn O h]

noncomputable def patientOnline (O : GenLimit.OracleFamily) :
    Stage3Case025.OnlineGenerator :=
  fun t xs _ => GenLimit.PatientMachine.output O (prefixExtension t xs) t

theorem patientOnline_follows
    (O : GenLimit.OracleFamily) (input : Stage3Case025.Stream) :
    Stage3Case025.Follows (patientOnline O) input
      (GenLimit.PatientMachine.output O input) := by
  intro t
  apply patientOutput_eq_of_eqOn O
  intro n hn
  exact (prefixExtension_eq t (fun i => input i) hn).symm

theorem positiveEngine : Stage3Case025.PositivePresentationHalfDensity := by
  intro family hInfinite
  let O := oracleOfFamily family hInfinite
  refine ⟨patientOnline O, ?_⟩
  intro i input hPresents
  let output := GenLimit.PatientMachine.output O input
  refine ⟨output, patientOnline_follows O input, ?_, ?_⟩
  · obtain ⟨hNovel, _⟩ :=
      GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
        O input hPresents
    obtain ⟨T, hT⟩ := hNovel
    refine ⟨T, ?_⟩
    intro t ht
    have hAt := hT t ht
    refine ⟨hAt.1, ?_, hAt.2.2⟩
    intro hmem
    obtain ⟨s, hs, heq⟩ := GenLimit.mem_sample_iff.mp hmem
    exact hAt.2.1 s (Nat.lt_succ_iff.mp hs) heq
  · exact
      GenLimit.PatientMachine.patientScope_lowerDensity_half O input hPresents

end Stage3Case025Formalization
