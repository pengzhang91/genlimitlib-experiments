Overall outcome: COMPLETE

The exact declaration `stage3_result : Stage3Case024.MainClaim` is proved in `Case024Formalization.lean`. The checked construction uses the perfect squares as the sparse base language, the full natural-number universe as the large target, and the supplied sparse-merge presentation to obtain one injective, surjective stream with vanishing contamination for every target containing the square core.

The pathwise argument proves that eventual validity for the square language leaves only finitely many nonsquare outputs. Therefore the generator-first set has ambient-prefix upper density zero in `Set.univ`; its density in any target is at most one. Integration yields the required pair inequality and strict-half consequence.

For every finite `r ≥ 2`, the family consists of the square core, successive finite additions of canonical nonsquares, and `Set.univ` as the final member. It is strictly nested, shares the same legal stream, has a globally feasible target-independent square generator, and forces expected density zero on the final target.

Materially used supplied declarations include `sparseMergePresentation`, its injectivity/range/vanishing-noise lemmas, `count_sparseSquare_le_sqrt_add_one`, `tendsto_sparseSqrt_add_one_div`, `NovelGeneratesInLimit`, `GeneratorFirst`, and `PatientScope.prefixCount`.

The exact root check passed with only `propext`, `Classical.choice`, and `Quot.sound`.
