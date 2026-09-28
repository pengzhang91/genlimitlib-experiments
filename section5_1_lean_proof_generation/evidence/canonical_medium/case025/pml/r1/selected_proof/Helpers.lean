import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main

open Stage3Case025

namespace Stage3Case025Local

open GenLimit
open GenLimit.PatientMachine

noncomputable def oracleFamily
    (family : ℕ → GenLimit.Language)
    (hInfinite : ∀ i, (family i).Infinite) : OracleFamily where
  language := family
  infinite' := hInfinite
  query i x := by
    classical
    exact if x ∈ family i then true else false
  query_spec i x := by
    classical
    simp

theorem sample_eq_of_prefix_eq
    (stream₁ stream₂ : ℕ → ℕ) (t : ℕ)
    (hprefix : ∀ n, n < t → stream₁ n = stream₂ n) :
    sample stream₁ t = sample stream₂ t := by
  classical
  ext x
  simp only [mem_sample_iff]
  constructor <;> rintro ⟨n, hn, rfl⟩
  · exact ⟨n, hn, (hprefix n hn).symm⟩
  · exact ⟨n, hn, hprefix n hn⟩

theorem recursiveCritical_eq_of_sample_eq
    (C : LanguageFamily) (stream₁ stream₂ : ℕ → ℕ) (t : ℕ)
    (hsample : sample stream₁ t = sample stream₂ t) (i : ℕ) :
    RecursiveCritical C stream₁ t i ↔ RecursiveCritical C stream₂ t i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero => simp [RecursiveCritical, Consistent, hsample]
      | succ i =>
          simp only [RecursiveCritical]
          have hcon : Consistent C stream₁ t (i + 1) ↔
              Consistent C stream₂ t (i + 1) := by
            simp [Consistent, hsample]
          constructor
          · rintro ⟨hci, hcrit⟩
            refine ⟨hcon.mp hci, ?_⟩
            intro j hj hjcrit
            exact hcrit j hj ((ih j (Nat.lt_succ_of_le hj)).mpr hjcrit)
          · rintro ⟨hci, hcrit⟩
            refine ⟨hcon.mpr hci, ?_⟩
            intro j hj hjcrit
            exact hcrit j hj ((ih j (Nat.lt_succ_of_le hj)).mp hjcrit)


theorem natFind_eq_of_iff
    {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q]
    (hp : ∃ n, p n) (hq : ∃ n, q n)
    (hiff : ∀ n, p n ↔ q n) : Nat.find hp = Nat.find hq := by
  apply Nat.le_antisymm
  · exact Nat.find_min' hp ((hiff _).mpr (Nat.find_spec hq))
  · exact Nat.find_min' hq ((hiff _).mp (Nat.find_spec hp))

theorem decision_eq_of_prefix_eq
    (O : OracleFamily) (stream₁ stream₂ : ℕ → ℕ) (t : ℕ)
    (old : State)
    (hprefix : ∀ n, n < t + 1 → stream₁ n = stream₂ n) :
    decide O.language stream₁ t old = decide O.language stream₂ t old := by
  classical
  have hsampleT : sample stream₁ t = sample stream₂ t :=
    sample_eq_of_prefix_eq stream₁ stream₂ t
      (fun n hn => hprefix n (lt_trans hn (Nat.lt_succ_self t)))
  have hsampleS : sample stream₁ (t + 1) = sample stream₂ (t + 1) :=
    sample_eq_of_prefix_eq stream₁ stream₂ (t + 1) hprefix
  have hconsistentS : ∀ i,
      Consistent O.language stream₁ (t + 1) i ↔
        Consistent O.language stream₂ (t + 1) i := by
    intro i
    simp [Consistent, hsampleS]
  have hexistsConsistent :
      (∃ i, Consistent O.language stream₁ (t + 1) i) ↔
        ∃ i, Consistent O.language stream₂ (t + 1) i := by
    constructor <;> rintro ⟨i, hi⟩
    · exact ⟨i, (hconsistentS i).mp hi⟩
    · exact ⟨i, (hconsistentS i).mpr hi⟩
  have hcriticalT : ∀ i,
      RecursiveCritical O.language stream₁ t i ↔
        RecursiveCritical O.language stream₂ t i :=
    fun i => recursiveCritical_eq_of_sample_eq O.language stream₁ stream₂ t hsampleT i
  have hcriticalS : ∀ i,
      RecursiveCritical O.language stream₁ (t + 1) i ↔
        RecursiveCritical O.language stream₂ (t + 1) i :=
    fun i => recursiveCritical_eq_of_sample_eq O.language stream₁ stream₂ (t + 1) hsampleS i
  have hconsistentIndices : consistentIndices O.language stream₁ (t + 1) old.scope =
      consistentIndices O.language stream₂ (t + 1) old.scope := by
    ext i
    simp [hconsistentS]
  have hcriticalIndices : ∀ scope,
      criticalIndices O.language stream₁ (t + 1) scope =
        criticalIndices O.language stream₂ (t + 1) scope := by
    intro scope
    ext i
    simp [hcriticalS]
  have hsurviving : survivingCriticalIndices O.language stream₁ t old.scope =
      survivingCriticalIndices O.language stream₂ t old.scope := by
    ext i
    simp [hcriticalT, hcriticalS]
  have hhighestCritical : ∀ scope fallback,
      highestCritical O.language stream₁ (t + 1) scope fallback =
        highestCritical O.language stream₂ (t + 1) scope fallback := by
    intro scope fallback
    unfold highestCritical
    rw [hcriticalIndices scope]
  have hhighestSurvivor :
      highestSurvivor O.language stream₁ t old.scope old.focus =
        highestSurvivor O.language stream₂ t old.scope old.focus := by
    unfold highestSurvivor
    rw [hsurviving]
  have hlowestInScope :
      lowestConsistentInScope O.language stream₁ (t + 1) old.scope old.focus =
        lowestConsistentInScope O.language stream₂ (t + 1) old.scope old.focus := by
    unfold lowestConsistentInScope
    rw [hconsistentIndices]
  have hlowest :
      lowestConsistent O.language stream₁ (t + 1) old.focus =
        lowestConsistent O.language stream₂ (t + 1) old.focus := by
    classical
    unfold lowestConsistent
    by_cases h₁ : ∃ i, Consistent O.language stream₁ (t + 1) i
    · have h₂ : ∃ i, Consistent O.language stream₂ (t + 1) i := by
        obtain ⟨i, hi⟩ := h₁
        exact ⟨i, (hconsistentS i).mp hi⟩
      rw [dif_pos h₁, dif_pos h₂]
      exact natFind_eq_of_iff h₁ h₂ hconsistentS
    · have h₂ : ¬∃ i, Consistent O.language stream₂ (t + 1) i := by
        intro h
        obtain ⟨i, hi⟩ := h
        exact h₁ ⟨i, (hconsistentS i).mpr hi⟩
      rw [dif_neg h₁, dif_neg h₂]
  by_cases hc₁ : Consistent O.language stream₁ (t + 1) old.focus
  · have hc₂ : Consistent O.language stream₂ (t + 1) old.focus :=
      (hconsistentS old.focus).mp hc₁
    simp [GenLimit.PatientMachine.decide, hc₁, hc₂, stableDecision,
      hhighestCritical]
  · have hc₂ : ¬Consistent O.language stream₂ (t + 1) old.focus := by
      exact fun h => hc₁ ((hconsistentS old.focus).mpr h)
    simp [GenLimit.PatientMachine.decide, hc₁, hc₂, backtrackDecision,
      hconsistentIndices, hsurviving, hhighestSurvivor, hlowestInScope, hlowest,
      hexistsConsistent]

theorem leastAvailable_eq_of_prefix_eq
    (O : OracleFamily) (stream₁ stream₂ : ℕ → ℕ) (t : ℕ)
    (used : Finset ℕ) (focus : ℕ)
    (hprefix : ∀ n, n < t → stream₁ n = stream₂ n) :
    leastAvailable O.language O.infinite' stream₁ t used focus =
      leastAvailable O.language O.infinite' stream₂ t used focus := by
  classical
  have hsample := sample_eq_of_prefix_eq stream₁ stream₂ t hprefix
  unfold leastAvailable
  apply natFind_eq_of_iff
  intro x
  simp [Available, hsample]

theorem processRound_eq_of_prefix_eq
    (O : OracleFamily) (stream₁ stream₂ : ℕ → ℕ) (t : ℕ)
    (old : State)
    (hprefix : ∀ n, n < t + 1 → stream₁ n = stream₂ n) :
    processRound O stream₁ t old = processRound O stream₂ t old := by
  classical
  have hdecision := decision_eq_of_prefix_eq O stream₁ stream₂ t old hprefix
  unfold processRound
  dsimp only
  rw [hdecision]
  rw [leastAvailable_eq_of_prefix_eq O stream₁ stream₂ (t + 1) old.used
    (GenLimit.PatientMachine.decide O.language stream₂ t old).focus hprefix]

theorem run_eq_of_prefix_eq
    (O : OracleFamily) (stream₁ stream₂ : ℕ → ℕ) :
    ∀ t, (∀ n, n < t → stream₁ n = stream₂ n) →
      run O stream₁ t = run O stream₂ t := by
  intro t
  induction t with
  | zero => intro; rfl
  | succ t ih =>
      intro hprefix
      rw [run_succ, run_succ,
        ih (fun n hn => hprefix n (lt_trans hn (Nat.lt_succ_self t)))]
      exact processRound_eq_of_prefix_eq O stream₁ stream₂ t _ hprefix

theorem patient_output_eq_of_prefix_eq
    (O : OracleFamily) (stream₁ stream₂ : ℕ → ℕ) (t : ℕ)
    (hprefix : ∀ n, n < t + 1 → stream₁ n = stream₂ n) :
    output O stream₁ t = output O stream₂ t := by
  unfold output
  rw [run_eq_of_prefix_eq O stream₁ stream₂ (t + 1) hprefix]

noncomputable def extendPrefix {t : ℕ} (xs : Fin (t + 1) → ℕ) : Stream :=
  fun n => if h : n < t + 1 then xs ⟨n, h⟩ else 0

noncomputable def onlinePatient (O : OracleFamily) : OnlineGenerator :=
  fun t xs _ => output O (extendPrefix xs) t

theorem onlinePatient_follows (O : OracleFamily) (input : Stream) :
    Follows (onlinePatient O) input (output O input) := by
  intro t
  apply patient_output_eq_of_prefix_eq
  intro n hn
  simp [extendPrefix, hn]

theorem positive_engine : PositivePresentationHalfDensity := by
  intro family hInfinite
  let O : OracleFamily := oracleFamily family hInfinite
  have hlang : O.language = family := rfl
  refine ⟨onlinePatient O, ?_⟩
  intro i input hP
  have hPO : Presents input (O.language i) := by simpa [hlang] using hP
  let generated := output O input
  refine ⟨generated, onlinePatient_follows O input, ?_, ?_⟩
  · obtain ⟨T, hT⟩ :=
      (patientScope_generation_and_lowerDensity O input (z := i) hPO).1
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨hmem, hinput, hprevious⟩ := hT t ht
    refine ⟨?_, ?_, hprevious⟩
    · simpa [generated, hlang] using hmem
    · intro hsample
      rw [GenLimit.mem_sample_iff] at hsample
      obtain ⟨s, hs, heq⟩ := hsample
      exact hinput s (Nat.lt_succ_iff.mp hs) (by simpa [generated] using heq)
  · simpa [generated, patientLowerDensity, hlang] using
      (patientScope_generation_and_lowerDensity O input (z := i) hPO).2

end Stage3Case025Local
