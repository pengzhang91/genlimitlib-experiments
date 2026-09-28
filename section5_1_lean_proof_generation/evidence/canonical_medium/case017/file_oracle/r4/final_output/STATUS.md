Overall outcome: COMPLETE

The exact declaration `stage3_result : Stage3Case017.MainClaim` is implemented in `Case017Formalization.lean`. The checked construction uses a family-tailored online generator that selects the least fresh point in the current finite-family information core when available, together with a total fallback. The proof establishes finite-family stabilization, eventual novel generation for every compatible target, coverage of every never-presented core point, a finite-prefix half-density counting bound, and both required target-relative lower-density inequalities.

Materially used sources and declarations: `Stage3Model.lean`; `GenLimit.GeneratorFirst`; `GenLimit.range_subset_first_announcements`; `GenLimit.PatientScope.prefixCount`; `GenLimit.PatientScope.partialDensity_of_counting`; `GenLimit.PatientScope.tendsto_prefixCount_atTop`; and `GenLimit.PatientScope.relativeLowerDensity`.

The targeted checker passes without `sorryAx` or any prohibited mechanism. Reported axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
