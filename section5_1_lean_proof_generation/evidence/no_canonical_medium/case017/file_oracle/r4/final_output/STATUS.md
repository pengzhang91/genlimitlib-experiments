Overall outcome: COMPLETE

`output/Case017Formalization.lean` proves the exact declaration
`stage3_result : Stage3Case017.MainClaim` and passes both the targeted entry-point
check and the final controller gate.

The proof constructs one family-tailored online generator. After the finite
set of incompatible family indices is eliminated, it greedily announces the
least information-core element absent from the current input prefix and prior
outputs. The formalization proves stabilization, eventual target validity,
input freshness, output nonrepetition, and simultaneous success for every
compatible target.

For density, it proves that every never-presented core element is generator
first, and injects each sufficiently late input-first core element into a
strictly smaller generator-first element. This yields the finite-prefix
half-density inequality. The supplied
`GenLimit.PatientScope.partialDensity_of_counting` theorem converts that
inequality to the required relative lower-density bound; a monotonicity lemma
supplies the never-presented-core bound.

Material declarations used include `Stage3Case017.informationCore`,
`Stage3Case017.SucceedsFor`, `GenLimit.GeneratorFirst`,
`GenLimit.NovelGeneratesInLimit`, `GenLimit.PatientScope.prefixCount`,
`GenLimit.PatientScope.tendsto_prefixCount_atTop`, and
`GenLimit.PatientScope.partialDensity_of_counting`.

Final axiom audit: `propext`, `Classical.choice`, and `Quot.sound` only; no
inadmissible axioms or prohibited mechanisms.
