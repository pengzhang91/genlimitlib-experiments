Overall outcome: COMPLETE

The exact declaration `stage3_result : Stage3Case024.MainClaim` is proved and passes the entry-point checker. The construction uses the square-sparse core, its complement, and the supplied square-sparse merge stream to establish the mandatory pair obstruction. For every finite rank at least two, it builds a strictly nested family by adjoining nonsquare markers, proves common-input legality and global feasibility using an online square-output generator, and derives the many-target obstruction from the first and last targets.

No proof gap remains. The proof materially uses `Stage3Model`, `GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation`, its sparse-square stream and density declarations, and standard mathlib measure/integral, finite-sum, set, and arithmetic results.
