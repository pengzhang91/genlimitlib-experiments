Overall outcome: COMPLETE

`output/Case017Formalization.lean` proves the exact declaration
`stage3_result : Stage3Case017.MainClaim`.

The checked construction is a family-tailored total online generator. It uses
the least fresh point in the intersection of family members consistent with
the current input prefix whenever that set has an available point, and a total
fresh fallback otherwise. The proof establishes finite-family stabilization,
eventual target-valid novelty for every compatible target on the same output
trajectory, coverage of every information-core point, the never-presented-core
inclusion in `GeneratorFirst`, and the finite-prefix pairing inequality needed
for the half-core density bound. The analytic endgame uses
`GenLimit.PatientScope.partialDensity_of_counting` and target-relative density
monotonicity.

Material inputs were `Stage3Model.lean`, `CANONICAL_FULL_PROOF.md`, and the
supplied modules for announcements, target density, and partial density.

Both the entry-point check and `bash LEAN_CHECK.sh --final` passed. The final
axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`, with no
inadmissible axioms or prohibited mechanisms.
