import Stage3Model
import Mathlib.Data.Nat.Log
example (n : ℕ) : Nat.log 2 ((n+1)*32) = Nat.log 2 (n+1)+5 := by
  rw [show (n + 1) * 32 = (((((n + 1) * 2) * 2) * 2) * 2) * 2 by ring]
  rw [Nat.log_mul_base (by norm_num : 1 < 2) (by positivity)]
  rw [Nat.log_mul_base (by norm_num : 1 < 2) (by positivity)]
  rw [Nat.log_mul_base (by norm_num : 1 < 2) (by positivity)]
  rw [Nat.log_mul_base (by norm_num : 1 < 2) (by positivity)]
  rw [Nat.log_mul_base (by norm_num : 1 < 2) (by positivity)]
  omega
