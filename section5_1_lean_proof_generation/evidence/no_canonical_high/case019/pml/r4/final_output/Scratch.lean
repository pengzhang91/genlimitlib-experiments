import Stage3Model
import GenLimit.Paper39_DenseGeneration.Partial.Main
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation

open Set Filter
open scoped Topology
open GenLimit GenLimit.Generic
open GenLimit.UnionClosedness

example (n : ℕ) : Stage3Case019.balanced (2*n+1) = negativeCode n := by
  simp [Stage3Case019.balanced, negativeCode]

example (n : ℕ) : Stage3Case019.balanced (2*n+2) = positiveCode n := by
  simp [Stage3Case019.balanced, positiveCode]

example : Tendsto (fun N : ℕ => N / 2 - 1) atTop atTop := by
  apply tendsto_atTop_mono' (f := fun N : ℕ => N / 2)
  · exact tendsto_nat_div_atTop_atTop (by omega)
  · filter_upwards [eventually_ge_atTop 4] with N hN
    omega

example : Tendsto (fun N : ℕ => ((N / 2 - 1 : ℕ) : ℝ) / N) atTop (𝓝 (1/2 : ℝ)) := by
  sorry
