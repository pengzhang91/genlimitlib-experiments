# Status

Complete.

- `Case017Formalization.lean` proves the exact theorem `stage3_result : Stage3Case017.MainClaim`.
- `Helpers.lean` supplies the prefix-congruence argument needed to package the patient machine as the required within-round online generator.
- The proof uses the filtered finite-intersection closure, establishes eventual novel generation, proves the half-density bound for the information core via a modified partial-enumeration certificate, and proves the missing-core bound by eventual first announcement.
- Targeted checking passes without `sorry`, new axioms, unsafe definitions, or kernel-bypass mechanisms.
- Final axiom dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.
