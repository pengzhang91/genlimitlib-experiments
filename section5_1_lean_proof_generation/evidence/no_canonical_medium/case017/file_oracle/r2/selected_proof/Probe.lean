import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity
#check Set.Finite.exists_not_mem
#check Set.Infinite.exists_not_mem_finset
#check Finset.exists_nat_subset_range
#check Nat.find_min'
#check Finset.max'
#check Finset.max'_mem
#check Finset.le_max'
#check Set.toFinite
#check Set.Finite.toFinset
#check Function.Injective.infinite_range
#check Set.infinite_range_of_injective
#check Set.Finite.subset
#check Filter.liminf_le_liminf

namespace X
abbrev OnlineGenerator := Stage3Case017.OnlineGenerator
noncomputable def run (gen : OnlineGenerator) (input : ℕ → ℕ) (t : ℕ) : ℕ :=
  gen t (fun i => input i) (fun i => run gen input i)
termination_by t

theorem run_eq (gen : OnlineGenerator) (input : ℕ → ℕ) (t : ℕ) :
    run gen input t = gen t (fun i => input i) (fun i => run gen input i) := by
  rw [run]
end X
