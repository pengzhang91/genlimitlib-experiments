Overall outcome: PARTIAL

`output/Case019Formalization.lean` compiles successfully as an entry-point source without `sorry`, new axioms, unsafe code, or kernel-bypass mechanisms.

Strongest checked result: for every `q`, the supplied marker-and-tail class `finiteOmissionClass q` is proved uncountable, all of its languages are infinite, it has a semantic generator satisfying eventual target validity and same-round sample freshness at noise level `q`, and every semantic generator is defeated at level `q + 1`.  The last statement is translated exactly to `Stage3Case019.SampleFreshGeneratesAfterInput`.  These facts are combined in `Stage3Case019Proof.separation_core`.

Remaining gap: the exact `stage3_result : Stage3Case019.MainClaim` is not present.  The missing work is the two density-sensitive positive constructions: (1) exposing the stream-level patient-scope machine as a causal finite-history `Generic.Generator` and transferring its half-density guarantee through finite contamination while preserving the target-relative numerator; and (2) formalizing the fresh-output sweep and balanced-order quarter-density counting argument for the separation class.  The existing finite-noise sweep theorem proves eventual sample freshness but not output novelty or the required density.

Materially used declarations include `finiteNoiseLevel_upper`, `finiteNoiseLevel_lower`, `finiteOmissionClass_uus`, the marker/tail class definitions, signed-integer encodings, and `powerSet_not_countable`.
