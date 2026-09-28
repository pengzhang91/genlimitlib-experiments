Overall outcome: COMPLETE

The exact root theorem `stage3_result : Stage3Case025.MainClaim` is proved in
`Case025Formalization.lean`. Both the direct entry-point check and the final
controller check pass. The final axiom audit reports only the permitted axioms
`propext`, `Classical.choice`, and `Quot.sound`, with no inadmissible axioms or
prohibited mechanisms.

The proof wraps the supplied patient-scope machine as the required
current-round online generator, proves output extensionality from finite input
prefixes, closes the indexed family under finite additions, and transfers
novel generation and ambient-prefix relative lower density from the input
range back to the original target.

Materially used sources and declarations include `Stage3Model.lean`,
`CANONICAL_FULL_PROOF.md`, `GenLimit.Paper39_DenseGeneration.Patient`,
`GenLimit.Core.FiniteContamination`, and `GenLimit.Core.GenericGeneration`.
