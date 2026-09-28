Overall outcome: COMPLETE

The exact declaration `stage3_result : Stage3Case017.MainClaim` is proved in
`Case017Formalization.lean`. The family-tailored generator greedily chooses the
least unseen element of the finite-family approximate information core (or of
the universe while that core is finite). Finite-family compatibility
stabilizes, yielding eventual core membership, input freshness, and output
injectivity.

For each compatible target, `Case017Helpers.lean` constructs a
`GenLimit.PatientScope.PartialEnumerationCertificate` whose enumerated set is
the information core and whose attacker ownership is restricted to
core-owned adversary-first announcements. The supplied Theorem 3.17 gives the
half-core density bound. A separate monotonicity argument gives the
never-presented-core bound, and `max_le` combines them. Eventual novelty follows
from stabilized core membership and the generator's global freshness.

Both requested checks succeeded:

- `bash LEAN_CHECK.sh output/Case017Formalization.lean`
- `bash LEAN_CHECK.sh --final`

The final gate reports kernel success, no prohibited mechanisms, no
inadmissible axioms, and only the permitted axioms `propext`,
`Classical.choice`, and `Quot.sound`.

Material supplied declarations include `Stage3Case017.MainClaim`, first
announcement ownership, target-relative lower density, and
`PartialEnumerationCertificate.theorem_3_17`.
