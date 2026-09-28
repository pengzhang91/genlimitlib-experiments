Overall outcome: COMPLETE

The exact declaration `stage3_result : Stage3Case017.MainClaim` is proved and passes the supplied entry-point checker. The construction uses a family-tailored causal generator that selects the least element consistent with the current finite observations and unused by either stream. Finite-family stabilization identifies this candidate set with the information core.

The checked proof establishes eventual novel generation for every compatible target, coverage of every never-presented core element by `GenLimit.GeneratorFirst`, and a prefix injection from late adversary-first core elements to smaller generator-first elements. The resulting finite-prefix inequality yields the half-core relative lower-density bound; set monotonicity yields the never-presented-core bound.

Material declarations include `Stage3Case017.informationCore`, `Stage3Case017.SucceedsFor`, `GenLimit.NovelGeneratesInLimit`, `GenLimit.GeneratorFirst`, `GenLimit.PatientScope.prefixCount`, and `GenLimit.PatientScope.relativeLowerDensity`, together with standard mathlib results for finite sets, `liminf`, and indicator counts. The proof depends only on the permitted axioms `propext`, `Classical.choice`, and `Quot.sound`.
