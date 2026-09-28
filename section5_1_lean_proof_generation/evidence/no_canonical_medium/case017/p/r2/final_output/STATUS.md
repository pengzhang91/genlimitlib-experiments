Overall outcome: COMPLETE

The exact declaration `stage3_result : Stage3Case017.MainClaim` is proved in `Case017Formalization.lean`. The proof constructs a deterministic family-tailored generator from stabilized compatible-family intersections, proves eventual novel generation for every compatible target, establishes finite-prefix lower bounds for both the missing information core and half of the full information core, and transfers those bounds to target-relative lower densities through liminf estimates.

The complete entry-point check passed. Its axiom audit reports only the permitted standard axioms `propext`, `Classical.choice`, and `Quot.sound`, with no prohibited mechanisms or inadmissible axioms.

Material declarations used include `Stage3Case017.MainClaim`, `Stage3Case017.SucceedsFor`, `Stage3Case017.informationCore`, `GenLimit.GeneratorFirst`, and `GenLimit.PatientScope.relativeLowerDensity` from the supplied shared model and its imports.
