Overall outcome: COMPLETE

`output/Case017Formalization.lean` proves the exact declaration `stage3_result : Stage3Case017.MainClaim`.

The checked construction uses a family-tailored least-fresh generator. Its finite-prefix information core stabilizes to `Stage3Case017.informationCore`; after stabilization, outputs are fresh, nonrepeating, and valid for every compatible target. A finite-prefix predecessor injection is packaged as `GenLimit.PatientScope.PartialEnumerationCertificate` to obtain the half-core relative lower-density bound. Eventual announcement of every core point gives the never-presented-core inclusion and the second density bound.

Material declarations include `GenLimit.GeneratorFirst`, `GenLimit.AdversaryFirst`, `GenLimit.NovelGeneratesInLimit`, `GenLimit.PatientScope.relativeLowerDensity`, and `GenLimit.PatientScope.PartialEnumerationCertificate.theorem_3_17`.

The entry-point checker passed. Its axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
