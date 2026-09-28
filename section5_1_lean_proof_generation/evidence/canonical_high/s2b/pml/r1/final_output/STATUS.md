Overall outcome: COMPLETE

The exact declaration `stage3_result : Stage3S2B.MainClaim` is proved in `S2BFormalization.lean`. The construction defines a causal alternating presentation, proves truthful replay against one fixed target, clean/injective/complete presentation legality, scored-set containment in the power-of-two core, and zero ordered upper density via a linear admission bound and a square-root core-count estimate.

The uncountability clause uses `GenLimit.UnionClosedness.powerSet_not_countable`; the density limit uses `GenLimit.InfiniteContamination.tendsto_sparseSqrt_add_one_div`. Material standard APIs include `Nat.nth`, `Nat.count`, `Nat.find`, and ordered-density monotonicity.

Both required checks passed:
- `bash LEAN_CHECK.sh output/S2BFormalization.lean`
- `bash LEAN_CHECK.sh --final`

The final axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`, with no prohibited mechanisms or inadmissible axioms.
