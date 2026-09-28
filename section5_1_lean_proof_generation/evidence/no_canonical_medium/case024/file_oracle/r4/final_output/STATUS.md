Overall outcome: COMPLETE

The exact declaration `stage3_result : Stage3Case024.MainClaim` is proved and checked. The construction uses the infinite set of perfect squares as a zero ambient-density common core, finite nested nonsquare extensions, and `Set.univ` as the final target. A single sparse-merge stream is legal for every target. A causal generator selecting an unseen square proves global feasibility. Eventual validity for the square core implies that generator-first announcements lie in the core up to a seed-dependent finite set, yielding zero relative upper density against `Set.univ`; the general density bound by one gives the pair inequality and strict-half consequence.

Materially used declarations include `GenLimit.InfiniteContamination.sparseMergePresentation`, its injectivity/range/vanishing-noise theorems, `count_sparseSquare_le_sqrt_add_one`, `tendsto_sparseSqrt_add_one_div`, `GenLimit.NovelGeneratesInLimit`, `GenLimit.GeneratorFirst`, and `GenLimit.PatientScope.prefixCount`.

The targeted entry-point check passed with only `propext`, `Classical.choice`, and `Quot.sound`.
