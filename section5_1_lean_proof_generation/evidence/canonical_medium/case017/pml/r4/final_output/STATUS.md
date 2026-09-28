Overall outcome: COMPLETE

- Implemented `stage3_result : Stage3Case017.MainClaim` in `Case017Formalization.lean`.
- Constructed a deterministic least-fresh online generator from the stabilized finite-family information core.
- Proved eventual novel generation for every compatible target.
- Proved the half-core density bound using `PartialDensity.partialDensity_of_counting` and the target-prefix machinery from `TargetDensity`.
- Proved the omitted-core density bound by showing every never-presented core point is generator-first announced.
- The complete entry-point check passes using only `propext`, `Classical.choice`, and `Quot.sound`.
