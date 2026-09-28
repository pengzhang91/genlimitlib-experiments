Overall outcome: COMPLETE

The exact declaration `stage3_result : Stage3Case017.MainClaim` is proved in `Case017Formalization.lean` and passes the supplied entry-point checker.

The proof constructs one family-dependent online generator, establishes finite-prefix version-space stabilization to `informationCore`, proves eventual fresh target-valid generation for every compatible language, identifies the output first-announcement range, and derives both required relative lower-density bounds. The half-core bound uses the finite-prefix pairing/counting argument followed by a liminf transfer; the unpresented-core bound follows from inclusion in `GeneratorFirst`. These are combined with `max_le` to establish the target inequality.

Materially used sources and declarations include `Stage3Model.lean`, the fixed theorem statement and canonical proof, `GenLimit.Generic.StreamIn`, `GenLimit.NovelGeneratesInLimit`, `GenLimit.GeneratorFirst`, and `GenLimit.PatientScope.relativeLowerDensity`, together with the model's within-round announcement semantics and target-density definitions.

No gaps remain. The proof contains no `sorry`, `admit`, new axioms, unsafe code, or prohibited kernel-bypass mechanisms. Its audited dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.
