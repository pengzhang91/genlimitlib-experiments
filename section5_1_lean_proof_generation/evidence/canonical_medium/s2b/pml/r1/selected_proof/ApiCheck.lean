import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.Density
example (n : ℕ) : Nat.log2 (16 * (n+1)) = Nat.log2 (n+1) + 4 := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  norm_num [show 16 * (n + 1) = (((n+1) * 2) * 2) * 2 * 2 by ring,
    Nat.log_mul_base, Nat.add_assoc]

example : Filter.Tendsto (fun n : ℕ => ((Nat.log2 (n+1) + 5 : ℕ) : ℝ) / (n : ℝ)) Filter.atTop (nhds 0) := by
  have hshift : Filter.Tendsto (fun n : ℕ => (Nat.log2 (n+1) : ℝ) / (n+1 : ℝ)) Filter.atTop (nhds 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using GenLimit.tendsto_natLog2_div.comp (Filter.tendsto_add_atTop_nat 1)
  sorry
