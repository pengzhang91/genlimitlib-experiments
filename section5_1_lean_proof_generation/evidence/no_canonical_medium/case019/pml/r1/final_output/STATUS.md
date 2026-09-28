Overall outcome: PARTIAL

The exact `stage3_result : Stage3Case019.MainClaim` was not completed.

Checked accomplishments:

- `stage3_countable_half_density : Stage3Case019.CountableClause` proves the entire countable-family half-density component for every finite distinct-noise level. It adapts the supplied patient generator to semantic finite histories, codes each contaminated presentation as a finite expansion, transfers eventual novelty back across the finite extraneous set, and proves that finite extension cannot increase target-relative lower density.
- `stage3_uncountable_separation_core` packages the supplied `finiteOmissionClass q` and proves its extensional uncountability, infinitude of every member, level-`q` eventual target validity and sample freshness, and the exact level-`q+1` impossibility required by the target.
- The remaining gap is the positive strengthening for `finiteOmissionClass q`: one semantic generator must additionally avoid all earlier outputs and its generator-first target set must have balanced relative lower density at least `1/4`. The supplied finite-noise sweep proves eventual validity/freshness but may repeat outputs, so it does not establish these two requirements.

The root file compiles as a partial artifact and intentionally does not declare or fake `stage3_result`.
