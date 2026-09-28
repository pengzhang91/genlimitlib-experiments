import Stage3Model
open Set Filter
example (input : ℕ → ℕ) (t : ℕ) : GenLimit.sample input t = GenLimit.Generic.sample input t := by
  classical
  ext z
  simp [GenLimit.sample, GenLimit.Generic.sample]
example (input : ℕ → ℕ) (t z : ℕ) (h : z ∉ GenLimit.Generic.sample input t) :
    z ∉ GenLimit.sample input t := by
  classical
  simpa only [GenLimit.sample, GenLimit.Generic.sample] using h
