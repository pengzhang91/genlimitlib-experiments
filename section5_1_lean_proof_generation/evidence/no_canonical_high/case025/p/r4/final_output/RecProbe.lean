import Mathlib

def foo (n : Nat) : Prop := (n = 0 ∨ ∀ k, k < n → foo k)
termination_by n

#check foo.eq_def
#check foo.eq_1
#print foo
