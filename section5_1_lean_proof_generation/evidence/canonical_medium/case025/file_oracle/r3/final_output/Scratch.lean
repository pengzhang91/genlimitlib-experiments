import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency

open Stage3Case025
open Set

noncomputable def oracleOf (family : ℕ → Language)
    (hinf : ∀ i, (family i).Infinite) : GenLimit.OracleFamily where
  language := family
  infinite' := hinf
  query i x := by
    classical
    exact if x ∈ family i then true else false
  query_spec i x := by
    classical
    simp

private theorem sample_congr {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.sample a t = GenLimit.sample b t := by
  classical
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor <;> rintro ⟨n, hn, rfl⟩
  · exact ⟨n, hn, (h n hn).symm⟩
  · exact ⟨n, hn, h n hn⟩

private theorem recursiveCritical_congr (C : GenLimit.LanguageFamily)
    {a b : ℕ → ℕ} {t : ℕ}
    (hs : GenLimit.sample a t = GenLimit.sample b t) :
    ∀ i, GenLimit.RecursiveCritical C a t i ↔
      GenLimit.RecursiveCritical C b t i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero => simp [GenLimit.RecursiveCritical, GenLimit.Consistent, hs]
      | succ i =>
          rw [GenLimit.RecursiveCritical, GenLimit.RecursiveCritical]
          constructor
          · rintro ⟨hcon, hprev⟩
            refine ⟨?_, ?_⟩
            · simpa [GenLimit.Consistent, hs] using hcon
            · intro j hj hjcrit
              apply hprev j hj
              exact (ih j (Nat.lt_succ_of_le hj)).2 hjcrit
          · rintro ⟨hcon, hprev⟩
            refine ⟨?_, ?_⟩
            · simpa [GenLimit.Consistent, hs] using hcon
            · intro j hj hjcrit
              apply hprev j hj
              exact (ih j (Nat.lt_succ_of_le hj)).1 hjcrit

private theorem decide_congr (O : GenLimit.OracleFamily) {a b : ℕ → ℕ}
    (t : ℕ) (old : GenLimit.PatientMachine.State)
    (hs0 : GenLimit.sample a t = GenLimit.sample b t)
    (hs1 : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1)) :
    GenLimit.PatientMachine.decide O.language a t old =
      GenLimit.PatientMachine.decide O.language b t old := by
  classical
  have hc : ∀ i, GenLimit.Consistent O.language a (t + 1) i ↔
      GenLimit.Consistent O.language b (t + 1) i := by
    intro i
    simp [GenLimit.Consistent, hs1]
  have hr : ∀ i, GenLimit.RecursiveCritical O.language a (t + 1) i ↔
      GenLimit.RecursiveCritical O.language b (t + 1) i :=
    recursiveCritical_congr O.language hs1
  have hr0 : ∀ i, GenLimit.RecursiveCritical O.language a t i ↔
      GenLimit.RecursiveCritical O.language b t i :=
    recursiveCritical_congr O.language hs0
  have hconsistent : ∀ scope,
      GenLimit.PatientMachine.consistentIndices O.language a (t + 1) scope =
        GenLimit.PatientMachine.consistentIndices O.language b (t + 1) scope := by
    intro scope
    ext i
    simp [hc]
  have hcritical : ∀ scope,
      GenLimit.PatientMachine.criticalIndices O.language a (t + 1) scope =
        GenLimit.PatientMachine.criticalIndices O.language b (t + 1) scope := by
    intro scope
    ext i
    simp [hr]
  have hsurviving : ∀ scope,
      GenLimit.PatientMachine.survivingCriticalIndices O.language a t scope =
        GenLimit.PatientMachine.survivingCriticalIndices O.language b t scope := by
    intro scope
    ext i
    simp [hr0, hr]
  have hhighestCritical : ∀ scope fallback,
      GenLimit.PatientMachine.highestCritical O.language a (t + 1) scope fallback =
        GenLimit.PatientMachine.highestCritical O.language b (t + 1) scope fallback := by
    intro scope fallback
    unfold GenLimit.PatientMachine.highestCritical
    rw [hcritical]
  have hhighestSurvivor : ∀ scope fallback,
      GenLimit.PatientMachine.highestSurvivor O.language a t scope fallback =
        GenLimit.PatientMachine.highestSurvivor O.language b t scope fallback := by
    intro scope fallback
    unfold GenLimit.PatientMachine.highestSurvivor
    rw [hsurviving]
  have hlowestScope : ∀ scope fallback,
      GenLimit.PatientMachine.lowestConsistentInScope O.language a (t + 1) scope fallback =
        GenLimit.PatientMachine.lowestConsistentInScope O.language b (t + 1) scope fallback := by
    intro scope fallback
    unfold GenLimit.PatientMachine.lowestConsistentInScope
    rw [hconsistent]
  have hlowest : ∀ fallback,
      GenLimit.PatientMachine.lowestConsistent O.language a (t + 1) fallback =
        GenLimit.PatientMachine.lowestConsistent O.language b (t + 1) fallback := by
    intro fallback
    unfold GenLimit.PatientMachine.lowestConsistent
    by_cases ha : ∃ i, GenLimit.Consistent O.language a (t + 1) i
    · have hb : ∃ i, GenLimit.Consistent O.language b (t + 1) i := by
        obtain ⟨i, hi⟩ := ha
        exact ⟨i, (hc i).1 hi⟩
      simp only [ha, hb, dif_pos]
      exact Nat.find_congr' (fun {n} => hc n)
    · have hb : ¬ ∃ i, GenLimit.Consistent O.language b (t + 1) i := by
        rintro ⟨i, hi⟩
        exact ha ⟨i, (hc i).2 hi⟩
      simp [ha, hb]
  unfold GenLimit.PatientMachine.decide
  rw [propext (hc old.focus)]
  by_cases hfocus : GenLimit.Consistent O.language b (t + 1) old.focus
  · simp only [hfocus, if_true]
    unfold GenLimit.PatientMachine.stableDecision
    by_cases hwait : 2 ^ old.tau ≤ old.age
    · simp only [hwait, if_pos]
      rw [hhighestCritical]
    · simp [hwait]
  · simp only [hfocus, if_false]
    unfold GenLimit.PatientMachine.backtrackDecision
    rw [hconsistent]
    by_cases hcon :
        (GenLimit.PatientMachine.consistentIndices O.language b (t + 1) old.scope).Nonempty
    · simp only [hcon, dif_pos]
      rw [hsurviving, hhighestSurvivor, hlowestScope]
    · simp only [hcon, dif_neg, if_false]
      rw [hlowest]
      have hexists : (∃ i, GenLimit.Consistent O.language a (t + 1) i) ↔
          ∃ i, GenLimit.Consistent O.language b (t + 1) i := by
        constructor <;> rintro ⟨i, hi⟩
        · exact ⟨i, (hc i).1 hi⟩
        · exact ⟨i, (hc i).2 hi⟩
      rw [propext hexists]
      split <;> simp_all

private theorem leastAvailable_congr (O : GenLimit.OracleFamily) {a b : ℕ → ℕ}
    (t : ℕ) (used : Finset ℕ) (focus : ℕ)
    (hs : GenLimit.sample a t = GenLimit.sample b t) :
    GenLimit.PatientMachine.leastAvailable O.language O.infinite' a t used focus =
      GenLimit.PatientMachine.leastAvailable O.language O.infinite' b t used focus := by
  unfold GenLimit.PatientMachine.leastAvailable
  congr 1
  funext x
  apply propext
  simp only [GenLimit.PatientMachine.Available]
  rw [hs]

private theorem run_congr (O : GenLimit.OracleFamily) {a b : ℕ → ℕ} :
    ∀ t, (∀ n, n < t → a n = b n) →
      GenLimit.PatientMachine.run O a t = GenLimit.PatientMachine.run O b t := by
  intro t
  induction t with
  | zero => intro h; rfl
  | succ t ih =>
      intro h
      have hab : GenLimit.PatientMachine.run O a t =
          GenLimit.PatientMachine.run O b t :=
        ih (fun n hn => h n (Nat.lt.step hn))
      rw [GenLimit.PatientMachine.run_succ,
        GenLimit.PatientMachine.run_succ, hab]
      have hs0 : GenLimit.sample a t = GenLimit.sample b t :=
        sample_congr (fun n hn => h n (Nat.lt.step hn))
      have hs1 : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1) :=
        sample_congr h
      have hd := decide_congr O t (GenLimit.PatientMachine.run O b t) hs0 hs1
      simp only [GenLimit.PatientMachine.processRound]
      rw [hd]
      have hx := leastAvailable_congr O (t + 1)
        (GenLimit.PatientMachine.run O b t).used
        (GenLimit.PatientMachine.decide O.language b t
          (GenLimit.PatientMachine.run O b t)).focus hs1
      rw [hx]

private theorem output_congr (O : GenLimit.OracleFamily) {a b : ℕ → ℕ} (t : ℕ)
    (h : ∀ n, n ≤ t → a n = b n) :
    GenLimit.PatientMachine.output O a t =
      GenLimit.PatientMachine.output O b t := by
  unfold GenLimit.PatientMachine.output
  have hrun := run_congr O (t + 1) (fun n hn => h n (Nat.lt_succ_iff.mp hn))
  rw [hrun]

noncomputable def extendHistory (t : ℕ) (xs : Fin (t+1) → ℕ) : ℕ → ℕ :=
  fun n => if h : n ≤ t then xs ⟨n, Nat.lt_succ_iff.mpr h⟩ else 0

noncomputable def onlineOf (O : GenLimit.OracleFamily) : OnlineGenerator :=
  fun t xs _ => GenLimit.PatientMachine.output O (extendHistory t xs) t

private theorem follows_onlineOf (O : GenLimit.OracleFamily) (input : Stream) :
    Follows (onlineOf O) input (GenLimit.PatientMachine.output O input) := by
  intro t
  apply output_congr
  intro n hn
  simp [extendHistory, hn]

example : PositivePresentationHalfDensity := by
  intro family hinf
  let O := oracleOf family hinf
  refine ⟨onlineOf O, ?_⟩
  intro i input hP
  refine ⟨GenLimit.PatientMachine.output O input, follows_onlineOf O input, ?_, ?_⟩
  · obtain ⟨hgen, hdens⟩ :=
      GenLimit.PatientMachine.patientScope_generation_and_lowerDensity O input hP
    obtain ⟨T, hT⟩ := hgen
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
    refine ⟨hmem, ?_, hnovel⟩
    intro hx
    rw [GenLimit.mem_sample_iff] at hx
    obtain ⟨s, hs, heq⟩ := hx
    exact hfresh s (Nat.lt_succ_iff.mp hs) heq
  · exact GenLimit.PatientMachine.patientScope_lowerDensity_half O input hP
