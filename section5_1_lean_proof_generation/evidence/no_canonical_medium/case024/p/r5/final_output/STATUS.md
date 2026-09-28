Overall outcome: PARTIAL

`output/Case024Formalization.lean` checks successfully as a standalone entry point and contains an explicit pair of strictly nested infinite languages together with a common injective stream covering both. It also proves that the larger range language is fully `Stage3Case024.Legal` (including vanishing noise), and reduces legality of the smaller core language to the remaining square-time noise estimate.

The exact declaration `stage3_result : Stage3Case024.MainClaim` is not present, so the final target gate fails. The main unresolved work is: (1) prove square rounds have vanishing empirical frequency for the smaller language; (2) replace or refine the current square construction with the ambient-density-separated family needed for `PairObstruction` and `ManyTargetWitness`; and (3) formalize the pathwise density bounds and their almost-everywhere integral consequences.

Materially used declarations include `Stage3Case024.Legal`, `GenLimit.InfiniteContamination.VanishingNoise`, `VanishingNoiseEnumeration`, `Set.range`, `Nat.sqrt`, and standard mathlib finiteness/arithmetic facts. No prohibited mechanism, new axiom, `sorry`, or `admit` is used in the checked source.
