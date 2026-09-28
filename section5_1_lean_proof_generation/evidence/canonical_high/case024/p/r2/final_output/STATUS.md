Overall outcome: COMPLETE

The exact theorem `stage3_result : Stage3Case024.MainClaim` is proved in `Case024Formalization.lean`, with checked supporting lemmas in `Case024Helpers.lean`.

The construction uses the square numbers as an infinite zero-density common core and a noncomputable bijective input stream that swaps the core with its infinite complement. It proves common legality, the pathwise zero-density obstruction on the universal target, the expectation inequality, and the strict-half consequence. For every finite size `r ≥ 2`, it also constructs a strictly nested family ending in the universal target, proves common legality and the many-target zero obstruction, and supplies a target-independent globally feasible generator that always emits a fresh square above the observed input prefix.

Material declarations used include `NovelGeneratesInLimit`, `VanishingNoiseEnumeration`, `GeneratorFirst`, `PatientScope.prefixCount`, measure-theoretic integral comparison, and standard limsup/tendsto results. The canonical proof and shared model guided the construction.

The complete entry-point check passed and reported only the permitted axioms `propext`, `Classical.choice`, and `Quot.sound`, with no prohibited mechanisms or inadmissible axioms.
