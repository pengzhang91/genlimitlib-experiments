Overall outcome: COMPLETE

Implemented and kernel-checked `stage3_result : Stage3Case017.MainClaim` in `Case017Formalization.lean`.

The proof constructs an online least-available generator, establishes finite version-space stabilization, and uses the stabilized tail to partition the information core into attacker and defender sets. For each compatible target it builds a `PartialEnumerationCertificate`, applies `PartialEnumerationCertificate.theorem_3_17`, and proves the additional never-presented-core bound using monotonicity of `relativeLowerDensity`.

The complete entry-point check passes using only the permitted standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
