Overall outcome: COMPLETE

The exact declaration `stage3_result : Stage3Case024.MainClaim` is proved in `Case024Formalization.lean`. The construction uses the infinite square language, the ambient language `Set.univ`, and a single injective sparse enumeration whose contamination rate vanishes for every target containing the squares. Eventual square-validity forces the generator-first set to differ from the squares only finitely, so its ambient upper density and expectation are zero; the remaining expected relative density is at most one.

For every `r ≥ 2`, `targetFamily r` is a strictly nested family formed from the squares, finite initial segments of an injective nonsquare sequence, and final target `Set.univ`. The same sparse stream is legal for every member. A target-independent online generator outputs a square exceeding every observed input and prior output, proving global feasibility. Simultaneous validity on the first member yields zero expected density on the final member.

Material declarations used include `GenLimit.NovelGeneratesInLimit`, `GenLimit.GeneratorFirst`, `GenLimit.InfiniteContamination.VanishingNoiseEnumeration`, `Stage3Case024.relativeUpperDensity`, and the supplied `Stage3Case024.MainClaim` model. The checked sources are `Helpers.lean`, `MainDraft.lean`, and `Case024Formalization.lean`.
