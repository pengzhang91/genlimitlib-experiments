Overall outcome: COMPLETE

The exact theorem `stage3_result : Stage3Case017.MainClaim` is proved in `Case017Formalization.lean`. The proof constructs a deterministic within-round online generator from the finite family, proves that its active finite-evidence intersection stabilizes to `informationCore`, and uses least fresh outputs thereafter.

The checked result establishes eventual target-valid novelty for every compatible family member. A finite-exception predecessor injection gives the half-core relative lower-density bound, while a finite pigeonhole argument shows every never-presented core element is eventually first announced by the generator, giving the second density bound. Monotonicity transports both bounds to each compatible target and combines them with `max_le`.

Materially used declarations include `Stage3Case017.informationCore`, `Stage3Case017.SucceedsFor`, `GenLimit.GeneratorFirst`, `GenLimit.NovelGeneratesInLimit`, `GenLimit.PatientScope.relativeLowerDensity`, `prefixCount_mono`, `tendsto_prefixCount_atTop`, and `partialDensity_of_counting` from the supplied P39 development.

Checks completed successfully:
- `bash LEAN_CHECK.sh output/Case017Formalization.lean`
- `bash LEAN_CHECK.sh --final`

The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
