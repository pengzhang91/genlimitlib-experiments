import output.PackagingScratch

open Stage3Case019

theorem stage3_countable_half_density : CountableClause := by
  intro q
  exact Case019.countable_half_density_fixed q

theorem stage3_uncountable_separation : SeparationClause := by
  intro q
  exact Case019.uncountable_separation_fixed q

theorem stage3_result : MainClaim := by
  exact ⟨stage3_countable_half_density, stage3_uncountable_separation⟩
