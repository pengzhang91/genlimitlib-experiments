import Case019Helpers
open GenLimit GenLimit.Generic
open GenLimit.NoiseLossFeedback GenLimit.UnionClosedness
open Stage3Case019 Case019Helpers

example (k : ℕ) : balanced (2*k+1) = negativeCode k := by
  simp [balanced, negativeCode, Int.negSucc_eq]

example (k : ℕ) : balanced (2*k+2) = positiveCode k := by
  simp [balanced, positiveCode]
  omega

example (q : ℕ) (input : ℕ → ℤ) (t : ℕ) :
    ∃ k < 2 * (t+1) + 1,
      outputAfterInput (freshSweepGenerator q) input t =
        sweepCode (decide (omissionMarkerFinset q ⊆ sample input (t+1))) k ∧
      outputAfterInput (freshSweepGenerator q) input t ∉ sample input (t+1) ∧
      ∀ s < t, outputAfterInput (freshSweepGenerator q) input s ≠
        outputAfterInput (freshSweepGenerator q) input t := by
  obtain ⟨k, hk, hout, hfresh, hnew⟩ :=
    freshSweepOutput_spec q (fun j : Fin (t+1) => input j)
  refine ⟨k, hk, ?_, ?_, ?_⟩
  · simpa [outputAfterInput, freshSweepGenerator,
      Generic.sequenceSample_prefix] using hout
  · simpa [outputAfterInput, freshSweepGenerator,
      Generic.sequenceSample_prefix] using hfresh
  · intro s hs
    have h := hnew ⟨s+1, by omega⟩
    simpa [outputAfterInput, freshSweepGenerator] using h.symm
