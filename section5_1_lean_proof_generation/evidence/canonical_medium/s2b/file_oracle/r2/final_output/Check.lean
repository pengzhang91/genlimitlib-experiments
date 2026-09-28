import Mathlib.Tactic
#check Nat.eq_of_mul_eq_mul_left
#check Nat.mul_left_cancel
#check Nat.add_right_cancel
example (a b:ℕ) (h:2*a+3=2*b+3) : a=b := by
  apply Nat.mul_left_cancel (n := 2)
  omega
