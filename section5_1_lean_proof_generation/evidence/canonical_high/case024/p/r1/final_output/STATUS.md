Overall outcome: COMPLETE

The exact theorem `stage3_result : Stage3Case024.MainClaim` is proved in `Case024Formalization.lean`, supported by `Helpers.lean`.

The construction uses the square numbers as the sparse lower target, the universal language as the upper target, and a bijective stream that swaps square and nonsquare indices. The helper proof establishes legality, vanishing square density, the pathwise generator-first obstruction, the expectation bound, strictly nested finite families, and a target-independent deterministic fresh-square generator witnessing global feasibility.

Checks completed successfully:
- `bash LEAN_CHECK.sh output/Case024Formalization.lean`
- `bash LEAN_CHECK.sh --final`

The final gate reports kernel success, exact-target success, no prohibited mechanisms, no inadmissible axioms, and only the permitted axioms `propext`, `Classical.choice`, and `Quot.sound`.

Material declarations used include `GenLimit.NovelGeneratesInLimit`, `GenLimit.GeneratorFirst`, `GenLimit.InfiniteContamination.VanishingNoiseEnumeration`, `GenLimit.PatientScope.prefixCount`, and `Stage3Case024.MainClaim`.
