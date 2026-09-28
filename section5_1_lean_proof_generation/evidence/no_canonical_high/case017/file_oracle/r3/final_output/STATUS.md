Overall outcome: COMPLETE

The exact theorem `stage3_result : Stage3Case017.MainClaim` is proved and checked. The construction uses a family-tailored greedy online generator. From each observed prefix it intersects the currently compatible family members and announces the least element not used by the input through the current round or by earlier outputs. Because the family is finite, this empirical core stabilizes to `informationCore family input`.

After stabilization, outputs are core-valid, avoid the current input sample, and never repeat. A finite counting argument pairs every stable adversary-first core element except a final boundary element with the generator output from the same round; pre-stabilization adversary wins contribute only a fixed finite error. `GenLimit.PatientScope.partialDensity_of_counting` then gives the half-core lower-density bound. A finite pigeonhole argument shows every core element never presented by the input is eventually generator-first, and monotonicity of relative lower density gives the second bound.

Material declarations used include `GenLimit.range_subset_first_announcements`, `GenLimit.adversaryFirst_disjoint_generatorFirst`, `GenLimit.PatientScope.partialDensity_of_counting`, `GenLimit.PatientScope.tendsto_prefixCount_atTop`, and `GenLimit.PatientScope.prefixCount_mono`.
