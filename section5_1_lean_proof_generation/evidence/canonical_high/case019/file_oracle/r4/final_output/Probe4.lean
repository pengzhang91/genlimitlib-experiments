import output.Helpers
import Mathlib
#check Finset.card_image_of_injective
#check Int.negSucc_eq
#check Int.negSucc_eq_neg_succ
#check Int.negSucc_coe
#check Int.ofNat_eq_coe
example (n : ℕ) : (2*n+1)/2=n := by omega
example (n : ℕ) : (-1 : ℤ) + -(n:ℤ) = Int.negSucc n := by omega
