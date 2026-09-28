# Verification status: passed

The Section 4 Lean formalization has passed its recorded verification:

- `build.log` ends with `Build completed successfully (3130 jobs)`;
- the comment-aware static scan passed on all 22 checked Lean files
  (`Section4.lean`, 20 modules under `Section4/`, and the axiom-audit driver);
- all 18 declared theorem endpoints produced exactly one axiom report;
- every reported axiom belongs to the permitted set `propext`,
  `Classical.choice`, and `Quot.sound`;
- `final-consistency.json` records a successful final build and confirms that
  all delivered proof sources match the verified working sources;
- a byte-for-byte comparison performed while preparing the anonymous snapshot
  confirmed that its `GenLimitLean/Section4/`, `Section4.lean`, bundled
  `GenLimit/`, and `Examples/` sources match those verified sources.

These records come from the source repository's completed verification and
contain no author-identifying repository coordinates. The release-preparation
session did not need to repeat the full Lean build. Reviewers may independently
reproduce the focused verification from the module root with:

```bash
bash scripts/verify_section4.sh --fetch-cache
```

The command regenerates `build.log`, `axioms.log`, and `axiom-check.log`.
