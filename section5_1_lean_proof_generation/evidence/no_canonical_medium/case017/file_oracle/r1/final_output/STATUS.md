Overall outcome: COMPLETE

The exact theorem `stage3_result : Stage3Case017.MainClaim` is proved and checked. The construction uses a family-tailored causal greedy generator: after finite stabilization of the candidates consistent with the observed prefix, it repeatedly chooses the least core element not yet announced by either side.

The proof establishes eventual target-valid novelty for every compatible family member. For density, it proves that every never-presented core element is eventually generator-first, and injects each sufficiently late input-first core element into the preceding, strictly smaller generator-first output. The resulting finite-prefix inequality is discharged through `GenLimit.PatientScope.partialDensity_of_counting`; a separate liminf monotonicity lemma gives the never-presented-core term.

Materially used declarations include `GenLimit.NovelGeneratesInLimit`, `GenLimit.GeneratorFirst`, `GenLimit.PatientScope.relativeLowerDensity`, `GenLimit.PatientScope.partialDensity_of_counting`, prefix-count lemmas from `TargetDensity`, and the finite-sample interfaces from `GenericGeneration`.
