# Reproducible verification records

Run `bash scripts/verify_section4.sh --fetch-cache` from the module root to
regenerate the records in this directory.

- `STATUS.md`: verification result and evidence boundary;
- `environment-and-sources.txt`: tool versions and hashes of the Section 4
  source files and Lake configuration;
- `static-scan.log`: comment-aware scan for admissions, custom axioms, unsafe
  declarations, and `native_decide`;
- `build.log`: complete focused `lake build Section4` output from the verified
  source snapshot;
- `axioms.log`: Lean's axiom reports for the declared endpoints;
- `axiom-check.log`: validation that all expected reports are present and use
  only `propext`, `Classical.choice`, and `Quot.sound`.
- `final-consistency.json`: confirmation that the delivered proof sources match
  the sources covered by the final verification record.

The recorded checks concern kernel compilation and declared logical
dependencies. They are not a substitute for mathematical peer review.
