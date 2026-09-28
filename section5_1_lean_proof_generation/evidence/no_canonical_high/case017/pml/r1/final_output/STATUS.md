Overall outcome: COMPLETE

The exact declaration `stage3_result : Stage3Case017.MainClaim` is proved and
passes the supplied entry-point checker. The proof constructs a deterministic
least-fresh online generator from the finite prefix-compatible version space,
proves stabilization to the information core, eventual target validity and
novelty, coverage of every never-presented core point, and both required
relative lower-density bounds.

The half-density bound materially uses
`GenLimit.PatientScope.PartialEnumerationCertificate.theorem_3_17`; the second
bound uses prefix-count monotonicity after proving the never-presented core is
contained in the generator-first target set. The construction also uses the
first-announcement definitions and disjointness from `Announcements.lean` and
the relative-density definitions from `TargetDensity.lean`.

Checked artifacts: `output/Case017Formalization.lean` and
`output/Case017Helpers.lean`. No proof gap remains.
