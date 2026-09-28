Overall outcome: COMPLETE

Proved the exact declaration `stage3_result : Stage3Case017.MainClaim` in `Case017Formalization.lean`.

The checked construction defines one family-dependent online generator, proves finite stabilization of the version core to the information core, establishes eventual target-valid fresh nonrepeating output, proves that all unpresented core points are generator-first, and formalizes the charging argument yielding the one-half relative lower-density bound. The two density estimates are combined for every compatible family member on the same output trajectory.

Material sources and declarations used: `Stage3Model.lean`, `Stage3Case017.MainClaim`, the supplied canonical proof, `GenLimit.NovelGeneratesInLimit`, `GenLimit.GeneratorFirst`, and `GenLimit.PatientScope.relativeLowerDensity`.

Validation: the complete entry point passes the supplied Lean checker and final target/axiom gate. Its dependencies are limited to the permitted standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
