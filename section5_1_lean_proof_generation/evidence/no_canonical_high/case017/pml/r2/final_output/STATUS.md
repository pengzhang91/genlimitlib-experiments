Overall outcome: COMPLETE

The exact declaration `stage3_result : Stage3Case017.MainClaim` is proved in `Case017Formalization.lean`. Both the direct entry-point check and the frozen final gate completed successfully. The checker reports only the permitted standard axioms `propext`, `Classical.choice`, and `Quot.sound`, with no prohibited mechanisms or inadmissible axioms.

The proof constructs a deterministic least-fresh online generator from stabilized finite-family compatibility. Its trajectory is eventually novel and valid for every compatible target. A partial-enumeration game trace and certificate apply `GenLimit.PatientScope.PartialEnumerationCertificate.theorem_3_17` for the half-core density bound; monotonicity of relative lower density and coverage of never-presented core elements establish the second bound.

Materially used supplied declarations include `Stage3Case017.MainClaim`, `Stage3Case017.informationCore`, `GenLimit.GeneratorFirst`, `GenLimit.NovelGeneratesInLimit`, `GenLimit.PatientScope.relativeLowerDensity`, `GenLimit.PartialEnumeration.PartialGameTrace`, and `GenLimit.PatientScope.PartialEnumerationCertificate.theorem_3_17`.
