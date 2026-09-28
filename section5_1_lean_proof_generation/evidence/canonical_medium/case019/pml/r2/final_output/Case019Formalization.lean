import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Stage3Case019

namespace Case019

noncomputable def oracleOfFamily
    (family : LanguageFamily ℕ)
    (hinfinite : ∀ i, (family i).Infinite) : GenLimit.OracleFamily where
  language := family
  infinite' := hinfinite
  query i x := by
    classical
    exact if x ∈ family i then true else false
  query_spec i x := by classical simp

def extendHistory {α : Type*} [Inhabited α]
    {n : ℕ} (history : Fin n → α) : Stream α :=
  fun k => if hk : k < n then history ⟨k, hk⟩ else default

theorem extendHistory_eq {α : Type*} [Inhabited α]
    {n : ℕ} (history : Fin n → α) {k : ℕ} (hk : k < n) :
    extendHistory history k = history ⟨k, hk⟩ := by
  simp [extendHistory, hk]

theorem sample_congr
    {a b : Stream ℕ} {n : ℕ}
    (h : ∀ k, k < n → a k = b k) :
    GenLimit.sample a n = GenLimit.sample b n := by
  ext x
  rw [GenLimit.mem_sample_iff, GenLimit.mem_sample_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, (h k hk).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, h k hk⟩

theorem consistent_congr
    (C : GenLimit.LanguageFamily) {a b : Stream ℕ} {n i : ℕ}
    (h : ∀ k, k < n → a k = b k) :
    GenLimit.Consistent C a n i ↔ GenLimit.Consistent C b n i := by
  unfold GenLimit.Consistent
  rw [sample_congr h]

theorem recursiveCritical_congr
    (C : GenLimit.LanguageFamily) {a b : Stream ℕ} {n : ℕ}
    (h : ∀ k, k < n → a k = b k) :
    ∀ i, GenLimit.RecursiveCritical C a n i ↔
      GenLimit.RecursiveCritical C b n i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero =>
          simpa [GenLimit.RecursiveCritical] using
            consistent_congr C h (i := 0)
      | succ i =>
          simp only [GenLimit.RecursiveCritical]
          rw [consistent_congr C h]
          constructor
          · rintro ⟨hc, hs⟩
            refine ⟨hc, ?_⟩
            intro j hj hjc
            exact hs j hj ((ih j (Nat.lt_succ_of_le hj)).mpr hjc)
          · rintro ⟨hc, hs⟩
            refine ⟨hc, ?_⟩
            intro j hj hjc
            exact hs j hj ((ih j (Nat.lt_succ_of_le hj)).mp hjc)

noncomputable def patientGenerator
    (O : GenLimit.OracleFamily) : Generator ℕ :=
  fun n history =>
    match n with
    | 0 => 0
    | t + 1 => GenLimit.PatientMachine.output O (extendHistory history) t

theorem finiteContamination_is_finiteNoiseFiniteOmission
    {input : Stream ℕ} {K : Language ℕ} {q : ℕ}
    (h : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
      input K q) :
    GenLimit.InfiniteContamination.FiniteNoiseFiniteOmissionEnumeration
      input K := by
  refine ⟨h.1, ?_, ?_⟩
  · rw [GenLimit.InfiniteContamination.finiteNoise_iff_valuesOutside_finite_of_injective
      h.1]
    exact (GenLimit.Generic.setDifferenceAtMost_iff_finite_ncard_le _ _ _).mp h.2.2 |>.1
  · unfold GenLimit.InfiniteContamination.FiniteOmissions
    simpa [GenLimit.InfiniteContamination.displayedOmissions] using
      by
        rw [Set.diff_eq_empty.mpr h.2.1]
        exact Set.finite_empty

end Case019

-- The checked helpers above establish the finite-prefix and contamination
-- reductions needed by the countable construction.  The exact combined
-- theorem remains unfinished in this partial artifact.
theorem stage3_result : Stage3Case019.MainClaim := by
  sorry
