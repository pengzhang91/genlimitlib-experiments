Overall outcome: COMPLETE

The exact declaration `stage3_result : Stage3Case017.MainClaim` is implemented and passes both the targeted entry-point check and the final controller gate. The proof constructs a deterministic finite-family generator that eventually stabilizes to the information core, chooses the least currently unannounced core element, and follows its recursively defined output trajectory.

The checked proof establishes eventual target validity and novelty for every compatible target, covers every never-presented core element by a generator-first announcement, and proves the half-core bound through a finite-prefix attacker/defender counting injection followed by the supplied `partialDensity_of_counting` theorem. Monotonicity of target-relative lower density yields the never-presented-core bound.

Material declarations used include `InfinitePartialPresentation`, `StreamIn`, `NovelGeneratesInLimit`, `GeneratorFirst`, `range_subset_first_announcements`, `relativeLowerDensity`, `prefixCount_mono`, `tendsto_prefixCount_atTop`, and `partialDensity_of_counting`. The final axiom audit reports only the permitted `propext`, `Classical.choice`, and `Quot.sound`.
