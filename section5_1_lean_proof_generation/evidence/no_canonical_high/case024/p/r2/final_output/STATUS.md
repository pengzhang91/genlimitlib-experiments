Overall outcome: COMPLETE

The exact declaration `stage3_result : Stage3Case024.MainClaim` is proved in `Case024Formalization.lean`. The construction uses natural squares as the sparse core, a bijective square/nonsquare-swapping common stream, the pair `Kcore ⊂ Set.univ`, and finite strictly nested enlargements ending in `Set.univ` for every requested family size. A fresh-history generator supplies global feasibility. Eventual validity for the sparse core forces the generator-first set to lie in the core up to finitely many exceptions, yielding zero ambient upper density for the universal target.

The complete entry point passed `LEAN_CHECK.sh`; its axiom audit reported only `propext`, `Classical.choice`, and `Quot.sound`, with no prohibited mechanisms or inadmissible axioms. Material declarations used include `Nat.nth`, `Nat.count`, `Nat.sqrt`, `GenLimit.NovelGeneratesInLimit`, `GenLimit.GeneratorFirst`, and `GenLimit.PatientScope.prefixCount`.
