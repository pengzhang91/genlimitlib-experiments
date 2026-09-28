Overall outcome: COMPLETE

`output/Case024Formalization.lean` proves the exact declaration
`stage3_result : Stage3Case024.MainClaim`.

The construction uses the sparse language of doubled squares, a bijective common
stream swapping that language with its complement, and a direct square-root
prefix bound to prove vanishing contamination. Eventual validity in the sparse
core forces the generator-first set to have zero ambient upper density, yielding
the two-target expectation obstruction. For every `r ≥ 2`, finite odd markers
produce a strictly nested family ending in `Set.univ`; a deterministic choice
generator always selects a fresh sparse-core element, establishing global
feasibility, while validity for the first target forces zero expected density on
the final target.

Material declarations used include `Stage3Case024.MainClaim`,
`GenLimit.InfiniteContamination.VanishingNoiseEnumeration`,
`GenLimit.NovelGeneratesInLimit`, `GenLimit.GeneratorFirst`, and
`GenLimit.PatientScope.prefixCount`. The proof depends only on the permitted
standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
