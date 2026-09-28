import Stage3Model
import Mathlib.Data.Set.Countable
open Set
#check Countable.of_injective
#check Countable.of_surjective
#check Function.Injective.countable
#check Set.countable_coe_iff
#check Set.to_countable
#check Set.Countable.to_countable
#check Set.Countable.toEncodable
#check Set.univ_countable_iff
#check Set.not_countable_univ
#check not_countable_iff
#check uncountable_iff_not_countable
#synth Uncountable (Set ℕ)
