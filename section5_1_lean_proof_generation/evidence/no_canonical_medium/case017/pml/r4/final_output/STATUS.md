Overall outcome: COMPLETE

The exact declaration `stage3_result : Stage3Case017.MainClaim` is implemented in `Case017Formalization.lean` and passes the supplied entry-point checker.

The proof uses a family-tailored online rule that intersects the family members consistent with the observed finite prefix and chooses the least value fresh from both the input prefix and prior outputs. Since the family is finite, the current intersection eventually stabilizes to `informationCore`. The checked helpers prove eventual target validity, global output non-repetition, coverage of every core element by an input or output announcement, and inclusion of every never-presented core element in `GeneratorFirst`.

For the half-core term, the proof constructs a `GenLimit.PatientScope.PartialEnumerationCertificate` with empty switch loss. Late adversary-first core elements are injectively paired with a smaller preceding generator output. The supplied Paper 39 partial-density theorem then yields the factor-`1/2` bound. A monotonicity lemma for `relativeLowerDensity` yields the never-presented-core bound.

Materially used declarations include `Stage3Case017.informationCore`, `GenLimit.GeneratorFirst`, `GenLimit.PatientScope.PartialEnumerationCertificate.theorem_3_17`, and the supplied first-announcement and target-density lemmas. The checker reports only `propext`, `Classical.choice`, and `Quot.sound`.
