Overall outcome: COMPLETE

The exact theorem `stage3_result : Stage3Case024.MainClaim` is implemented and checked. The construction uses the infinite set of perfect squares as the sparse common core, a square-sparse injective full presentation of the universe, finite initial segments of a fixed injective nonsquare sequence for the intermediate strictly nested targets, and `Set.univ` as the final target.

The pathwise argument proves that eventual validity for the square core leaves only finitely many nonsquare outputs, so the generator-first set has ambient-prefix upper density zero on `Set.univ`. General relative upper densities are proved to lie in `[0,1]`, yielding the pair expectation inequality. The same zero-density final target proves the many-target obstruction. Global feasibility is witnessed by a target-independent online generator choosing a fresh square outside the current input and prior-output finite sets.

Materially used declarations include `GenLimit.InfiniteContamination.sparseMergePresentation`, its injectivity/range/vanishing-noise theorems, square-count bounds from `SharedVanishingPresentation`, `GenLimit.NovelGeneratesInLimit`, `GenLimit.GeneratorFirst`, and `GenLimit.PatientScope.prefixCount`.

Both the complete entry point and final checker pass without `sorryAx` or prohibited mechanisms; dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.
