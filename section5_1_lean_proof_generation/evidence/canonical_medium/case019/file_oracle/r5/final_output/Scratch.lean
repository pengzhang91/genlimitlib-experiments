import GenLimit.Paper39_DenseGeneration.Patient.Main

open Set
namespace Test
open GenLimit GenLimit.PatientMachine

lemma sample_eq_of_eq_lt {a b : ℕ → ℕ} {n : ℕ}
    (h : ∀ k, k < n → a k = b k) : sample a n = sample b n := by
  classical
  unfold sample
  apply Finset.image_congr
  intro k hk
  exact h k (Finset.mem_range.mp hk)

lemma consistent_congr {C : LanguageFamily} {a b : ℕ → ℕ} {n i : ℕ}
    (hs : sample a n = sample b n) :
    Consistent C a n i ↔ Consistent C b n i := by
  simp [Consistent, hs]

lemma recursiveCritical_congr {C : LanguageFamily} {a b : ℕ → ℕ} {n : ℕ}
    (hs : sample a n = sample b n) :
    ∀ i, RecursiveCritical C a n i ↔ RecursiveCritical C b n i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    cases i with
    | zero => simpa [RecursiveCritical] using (consistent_congr (i := 0) hs)
    | succ i =>
      simp only [RecursiveCritical]
      constructor
      · rintro ⟨hc, hsub⟩
        refine ⟨(consistent_congr hs).mp hc, ?_⟩
        intro j hj hcrit
        exact hsub j hj ((ih j (by omega)).mpr hcrit)
      · rintro ⟨hc, hsub⟩
        refine ⟨(consistent_congr hs).mpr hc, ?_⟩
        intro j hj hcrit
        exact hsub j hj ((ih j (by omega)).mp hcrit)

lemma decision_congr (O : OracleFamily) {a b : ℕ → ℕ} {t : ℕ} {old : State}
    (h : ∀ k, k < t + 1 → a k = b k) :
    PatientMachine.decide O.language a t old =
      PatientMachine.decide O.language b t old := by
  classical
  have hs : sample a (t+1) = sample b (t+1) := sample_eq_of_eq_lt h
  have hs0 : sample a t = sample b t :=
    sample_eq_of_eq_lt (fun k hk => h k (lt_trans hk (Nat.lt_succ_self t)))
  have hc : ∀ i, Consistent O.language a (t+1) i ↔
      Consistent O.language b (t+1) i := fun i => consistent_congr hs
  have hr : ∀ i, RecursiveCritical O.language a (t+1) i ↔
      RecursiveCritical O.language b (t+1) i := recursiveCritical_congr hs
  have hr0 : ∀ i, RecursiveCritical O.language a t i ↔
      RecursiveCritical O.language b t i := recursiveCritical_congr hs0
  have hcf : (fun i => Consistent O.language a (t+1) i) =
      (fun i => Consistent O.language b (t+1) i) := funext (fun i => propext (hc i))
  have hrf : (fun i => RecursiveCritical O.language a (t+1) i) =
      (fun i => RecursiveCritical O.language b (t+1) i) := funext (fun i => propext (hr i))
  have hr0f : (fun i => RecursiveCritical O.language a t i) =
      (fun i => RecursiveCritical O.language b t i) := funext (fun i => propext (hr0 i))
  simp only [PatientMachine.decide, stableDecision, backtrackDecision,
    highestCritical, highestSurvivor, lowestConsistentInScope,
    lowestConsistent, consistentIndices, survivingCriticalIndices,
    criticalIndices, hcf, hrf, hr0f, hc]

lemma leastAvailable_congr (O : OracleFamily) {a b : ℕ → ℕ} {n : ℕ}
    (hs : sample a n = sample b n) (used : Finset ℕ) (focus : ℕ) :
    leastAvailable O.language O.infinite' a n used focus =
      leastAvailable O.language O.infinite' b n used focus := by
  classical
  unfold leastAvailable
  apply Nat.find_congr (Nat.find_spec (available_exists O.language O.infinite' a n used focus))
  intro x _
  simp [Available, hs]

lemma processRound_congr (O : OracleFamily) {a b : ℕ → ℕ} {t : ℕ} {old : State}
    (h : ∀ k, k < t + 1 → a k = b k) :
    processRound O a t old = processRound O b t old := by
  classical
  have hs : sample a (t+1) = sample b (t+1) := sample_eq_of_eq_lt h
  have hd := decision_congr (old := old) O h
  simp only [processRound]
  rw [hd]
  rw [leastAvailable_congr O hs]

lemma run_congr (O : OracleFamily) {a b : ℕ → ℕ} :
    ∀ n, (∀ k, k < n → a k = b k) → run O a n = run O b n := by
  intro n
  induction n with
  | zero => intro; rfl
  | succ n ih =>
      intro h
      rw [run_succ, run_succ, ih (fun k hk => h k (Nat.lt.step hk))]
      exact processRound_congr O h

end Test
