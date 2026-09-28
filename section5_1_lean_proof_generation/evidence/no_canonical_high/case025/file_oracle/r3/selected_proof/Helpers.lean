import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency

open Filter
open Stage3Case025

namespace Stage3Case025

noncomputable def oracleOfFamily
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

lemma sample_eq_of_eq_on_prefix
    {input₁ input₂ : Stream} {t : ℕ}
    (h : ∀ n, n < t → input₁ n = input₂ n) :
    GenLimit.sample input₁ t = GenLimit.sample input₂ t := by
  classical
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, (h n hn).symm⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, h n hn⟩

lemma consistent_iff_of_eq_on_prefix
    {family : ℕ → Language} {input₁ input₂ : Stream} {t i : ℕ}
    (h : ∀ n, n < t → input₁ n = input₂ n) :
    GenLimit.Consistent family input₁ t i ↔
      GenLimit.Consistent family input₂ t i := by
  unfold GenLimit.Consistent
  rw [sample_eq_of_eq_on_prefix h]

lemma recursiveCritical_iff_of_eq_on_prefix
    {family : ℕ → Language} {input₁ input₂ : Stream} {t i : ℕ}
    (h : ∀ n, n < t → input₁ n = input₂ n) :
    GenLimit.RecursiveCritical family input₁ t i ↔
      GenLimit.RecursiveCritical family input₂ t i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero =>
          simpa [GenLimit.RecursiveCritical] using
            (consistent_iff_of_eq_on_prefix (i := 0) h)
      | succ i =>
          simp only [GenLimit.RecursiveCritical]
          constructor
          · rintro ⟨hcon, hcrit⟩
            refine ⟨(consistent_iff_of_eq_on_prefix h).mp hcon, ?_⟩
            intro j hj hjcrit
            exact hcrit j hj ((ih j (by omega)).mpr hjcrit)
          · rintro ⟨hcon, hcrit⟩
            refine ⟨(consistent_iff_of_eq_on_prefix h).mpr hcon, ?_⟩
            intro j hj hjcrit
            exact hcrit j hj ((ih j (by omega)).mp hjcrit)

lemma decide_eq_of_eq_on_prefix
    (C : GenLimit.LanguageFamily) {input₁ input₂ : Stream} {t : ℕ}
    (h : ∀ n, n < t + 1 → input₁ n = input₂ n)
    (old : GenLimit.PatientMachine.State) :
    GenLimit.PatientMachine.decide C input₁ t old =
      GenLimit.PatientMachine.decide C input₂ t old := by
  classical
  have hcon : ∀ i,
      GenLimit.Consistent C input₁ (t + 1) i ↔
        GenLimit.Consistent C input₂ (t + 1) i :=
    fun i => consistent_iff_of_eq_on_prefix h
  have hcritNow : ∀ i,
      GenLimit.RecursiveCritical C input₁ (t + 1) i ↔
        GenLimit.RecursiveCritical C input₂ (t + 1) i :=
    fun i => recursiveCritical_iff_of_eq_on_prefix h
  have hshort : ∀ n, n < t → input₁ n = input₂ n := by
    intro n hn
    exact h n (by omega)
  have hcritOld : ∀ i,
      GenLimit.RecursiveCritical C input₁ t i ↔
        GenLimit.RecursiveCritical C input₂ t i :=
    fun i => recursiveCritical_iff_of_eq_on_prefix hshort
  have hConPred :
      (fun i => GenLimit.Consistent C input₁ (t + 1) i) =
        (fun i => GenLimit.Consistent C input₂ (t + 1) i) := by
    funext i
    exact propext (hcon i)
  have hConsistentIndices :
      GenLimit.PatientMachine.consistentIndices C input₁ (t + 1) old.scope =
        GenLimit.PatientMachine.consistentIndices C input₂ (t + 1) old.scope := by
    ext i
    simp [hcon i]
  have hCriticalFinset : ∀ scope,
      GenLimit.PatientMachine.criticalIndices C input₁ (t + 1) scope =
        GenLimit.PatientMachine.criticalIndices C input₂ (t + 1) scope := by
    intro scope
    ext i
    simp [hcritNow i]
  have hHighestCritical : ∀ scope fallback,
      GenLimit.PatientMachine.highestCritical C input₁ (t + 1) scope fallback =
        GenLimit.PatientMachine.highestCritical C input₂ (t + 1) scope fallback := by
    intro scope fallback
    unfold GenLimit.PatientMachine.highestCritical
    rw [hCriticalFinset]
  have hSurviving :
      GenLimit.PatientMachine.survivingCriticalIndices C input₁ t old.scope =
        GenLimit.PatientMachine.survivingCriticalIndices C input₂ t old.scope := by
    ext i
    simp [hcritOld i, hcritNow i]
  have hHighestSurvivor :
      GenLimit.PatientMachine.highestSurvivor C input₁ t old.scope old.focus =
        GenLimit.PatientMachine.highestSurvivor C input₂ t old.scope old.focus := by
    unfold GenLimit.PatientMachine.highestSurvivor
    rw [hSurviving]
  have hLowestScope :
      GenLimit.PatientMachine.lowestConsistentInScope C input₁ (t + 1)
          old.scope old.focus =
        GenLimit.PatientMachine.lowestConsistentInScope C input₂ (t + 1)
          old.scope old.focus := by
    unfold GenLimit.PatientMachine.lowestConsistentInScope
    rw [hConsistentIndices]
  have hLowest :
      GenLimit.PatientMachine.lowestConsistent C input₁ (t + 1) old.focus =
        GenLimit.PatientMachine.lowestConsistent C input₂ (t + 1) old.focus := by
    classical
    unfold GenLimit.PatientMachine.lowestConsistent
    by_cases h₁ : ∃ i, GenLimit.Consistent C input₁ (t + 1) i
    · have h₂ : ∃ i, GenLimit.Consistent C input₂ (t + 1) i := by
        simpa only [hConPred] using h₁
      rw [dif_pos h₁, dif_pos h₂]
      exact Nat.find_congr' (fun {n} => hcon n)
    · have h₂ : ¬∃ i, GenLimit.Consistent C input₂ (t + 1) i := by
        simpa only [hConPred] using h₁
      rw [dif_neg h₁, dif_neg h₂]
  have hStable :
      GenLimit.PatientMachine.stableDecision C input₁ t old =
        GenLimit.PatientMachine.stableDecision C input₂ t old := by
    unfold GenLimit.PatientMachine.stableDecision
    split
    · dsimp
      rw [hHighestCritical]
    · rfl
  have hBacktrack :
      GenLimit.PatientMachine.backtrackDecision C input₁ t old =
        GenLimit.PatientMachine.backtrackDecision C input₂ t old := by
    simp only [GenLimit.PatientMachine.backtrackDecision]
    rw [hConsistentIndices, hSurviving, hHighestSurvivor, hLowestScope,
      hLowest, hConPred]
  unfold GenLimit.PatientMachine.decide
  split <;> rename_i hfocus
  · rw [if_pos ((hcon old.focus).mp hfocus), hStable]
  · rw [if_neg (fun hc => hfocus ((hcon old.focus).mpr hc)), hBacktrack]

lemma leastAvailable_eq_of_sample_eq
    (C : GenLimit.LanguageFamily) (hInfinite : ∀ i, (C i).Infinite)
    {input₁ input₂ : Stream} {t : ℕ} (hsample :
      GenLimit.sample input₁ t = GenLimit.sample input₂ t)
    (used : Finset ℕ) (focus : ℕ) :
    GenLimit.PatientMachine.leastAvailable C hInfinite input₁ t used focus =
      GenLimit.PatientMachine.leastAvailable C hInfinite input₂ t used focus := by
  classical
  unfold GenLimit.PatientMachine.leastAvailable
  apply Nat.find_congr'
  intro n
  simp [GenLimit.PatientMachine.Available, hsample]

lemma processRound_eq_of_eq_on_prefix
    (O : GenLimit.OracleFamily) {input₁ input₂ : Stream} {t : ℕ}
    (h : ∀ n, n < t + 1 → input₁ n = input₂ n)
    (old : GenLimit.PatientMachine.State) :
    GenLimit.PatientMachine.processRound O input₁ t old =
      GenLimit.PatientMachine.processRound O input₂ t old := by
  classical
  have hsample : GenLimit.sample input₁ (t + 1) =
      GenLimit.sample input₂ (t + 1) := sample_eq_of_eq_on_prefix h
  have hdecide := decide_eq_of_eq_on_prefix O.language h old
  have hleast := leastAvailable_eq_of_sample_eq O.language O.infinite'
    hsample old.used (GenLimit.PatientMachine.decide O.language input₁ t old).focus
  rw [hdecide] at hleast
  simp only [GenLimit.PatientMachine.processRound]
  rw [hdecide, hleast]

lemma run_eq_of_eq_on_prefix
    (O : GenLimit.OracleFamily) {input₁ input₂ : Stream} {t : ℕ}
    (h : ∀ n, n < t → input₁ n = input₂ n) :
    GenLimit.PatientMachine.run O input₁ t =
      GenLimit.PatientMachine.run O input₂ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [GenLimit.PatientMachine.run_succ,
        GenLimit.PatientMachine.run_succ]
      rw [ih (fun n hn => h n (by omega))]
      exact processRound_eq_of_eq_on_prefix O h _

lemma patientOutput_eq_of_eq_on_prefix
    (O : GenLimit.OracleFamily) {input₁ input₂ : Stream} {t : ℕ}
    (h : ∀ n, n < t + 1 → input₁ n = input₂ n) :
    GenLimit.PatientMachine.output O input₁ t =
      GenLimit.PatientMachine.output O input₂ t := by
  unfold GenLimit.PatientMachine.output
  rw [run_eq_of_eq_on_prefix O h]

noncomputable def prefixExtension
    (t : ℕ) (xs : Fin (t + 1) → ℕ) : Stream :=
  fun n => if hn : n < t + 1 then xs ⟨n, hn⟩ else 0

noncomputable def patientOnlineGenerator (O : GenLimit.OracleFamily) :
    OnlineGenerator :=
  fun t xs _ => GenLimit.PatientMachine.output O (prefixExtension t xs) t

lemma patientOnlineGenerator_follows
    (O : GenLimit.OracleFamily) (input : Stream) :
    Follows (patientOnlineGenerator O) input
      (GenLimit.PatientMachine.output O input) := by
  intro t
  apply patientOutput_eq_of_eq_on_prefix O
  intro n hn
  simp [prefixExtension, hn]

end Stage3Case025
