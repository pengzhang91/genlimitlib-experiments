Overall outcome: COMPLETE

The exact theorem `stage3_result : Stage3Case024.MainClaim` is proved and checked. The construction uses the infinite set of perfect squares as the sparse common core, the supplied square-sparse merge presentation as one injective universal-range stream, finite initial extensions for intermediate targets, and `Set.univ` as the final target. A target-independent online generator always selects a fresh square outside the finite input/output history, establishing global feasibility.

The pathwise obstruction shows that eventual validity for the square core leaves only finitely many non-square outputs. Generator-first announcements therefore have ambient-prefix upper density zero on `Set.univ`; integrability and the probability-measure hypothesis yield the required expectation statements. The pair inequality and strict-half consequence follow, and every finite nested family has a zero-density final member.

Material declarations include `SparseSquare`, `squareSparseMerge`, its injectivity/range/vanishing-noise lemmas, `NovelGeneratesInLimit`, `GeneratorFirst`, `PatientScope.prefixCount`, and standard limsup and Bochner-integral lemmas.
