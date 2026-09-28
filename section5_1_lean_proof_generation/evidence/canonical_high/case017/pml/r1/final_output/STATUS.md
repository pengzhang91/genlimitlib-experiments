Overall outcome: COMPLETE

Implemented `stage3_result : Stage3Case017.MainClaim` in
`Case017Formalization.lean`. The proof stabilizes finite version cores to the
information core, constructs a fresh online output stream, obtains a
`PartialEnumerationCertificate` through `PartialGameTrace.toCertificate`, and
applies `PartialEnumerationCertificate.theorem_3_17` for the half-density
bound. The targeted entry-point check passes using only the permitted axioms.
