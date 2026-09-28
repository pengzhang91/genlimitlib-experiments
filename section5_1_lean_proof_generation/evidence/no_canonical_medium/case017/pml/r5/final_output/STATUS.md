Overall outcome: COMPLETE

The exact declaration `stage3_result : Stage3Case017.MainClaim` is proved and checked. The construction uses one family-tailored online generator that tracks the currently compatible family members and announces the least point in their current intersection that is fresh from both finite histories. Finite-family compatibility stabilizes to the information core.

The proof establishes eventual target validity and novelty, proves every core point is eventually announced, and charges each sufficiently late adversary-first core point to a distinct no-larger predecessor output. This gives the half-core prefix-count inequality and hence the first lower-density bound. Every never-presented core point is generator-first, yielding the second bound by lower-density monotonicity.

Materially used declarations include `Stage3Case017.informationCore`, `Stage3Case017.SucceedsFor`, `GenLimit.GeneratorFirst`, `GenLimit.NovelGeneratesInLimit`, `GenLimit.PatientScope.relativeLowerDensity`, `GenLimit.PatientScope.partialDensity_of_counting`, and `GenLimit.PatientScope.tendsto_prefixCount_atTop`.
