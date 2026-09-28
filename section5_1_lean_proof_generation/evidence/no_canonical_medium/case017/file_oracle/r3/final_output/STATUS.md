Overall outcome: COMPLETE

The exact declaration `stage3_result : Stage3Case017.MainClaim` is proved and passes the supplied root checker. The proof constructs a deterministic family-specific greedy online generator. Its empirical finite-family core stabilizes to `informationCore`; the resulting trajectory is globally nonrepeating, avoids the current input sample, eventually lies in every compatible target, and eventually enumerates every core element not presented by the input.

For the density bound, adversary-first core elements after a finite prefix are injectively paired with strictly smaller preceding generator outputs. This is packaged through `GenLimit.PatientScope.PartialEnumerationCertificate` to obtain the finite counting inequality, then discharged by `partialDensity_of_counting`. Monotonicity of relative lower density supplies the never-presented-core term.

Materially used supplied declarations include `Stage3Case017.informationCore`, `Stage3Case017.SucceedsFor`, `GenLimit.GeneratorFirst`, `GenLimit.AdversaryFirst`, `GenLimit.adversaryFirst_disjoint_generatorFirst`, `GenLimit.PatientScope.PartialEnumerationCertificate.enumeratedCount_le_two_mul_defender`, `GenLimit.PatientScope.partialDensity_of_counting`, and `GenLimit.PatientScope.tendsto_prefixCount_atTop`.
