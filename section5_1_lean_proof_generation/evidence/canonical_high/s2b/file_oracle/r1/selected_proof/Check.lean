import GenLimit.Paper39_DenseGeneration.Abstract.Density
import Mathlib.Tactic

lemma test_log (n : ℕ) (hn : 0 < n) :
    Nat.log2 (18 * n + 10) + 1 ≤ 6 + Nat.log2 n := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  have hmono : Nat.log 2 (18 * n + 10) ≤ Nat.log 2 (32 * n) := by
    apply Nat.log_mono Nat.one_lt_two le_rfl
    omega
  calc
    Nat.log 2 (18 * n + 10) + 1 ≤ Nat.log 2 (32 * n) + 1 := Nat.add_le_add_right hmono 1
    _ = Nat.log 2 n + 6 := by
      have hn0 : n ≠ 0 := Nat.ne_of_gt hn
      have heq : 32 * n = (((((n * 2) * 2) * 2) * 2) * 2) := by omega
      rw [heq]
      repeat' rw [Nat.log_mul_base Nat.one_lt_two (by positivity)]
    _ = 6 + Nat.log 2 n := by omega
