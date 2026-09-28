Overall outcome: PARTIAL

The checked Lean source proves the full positive half: `targetClass` is not countable, via an injective encoding of all subsets of the ordinary numbers, and the powers-of-two stream is an injective uniform sample-free generator with threshold zero. This is exposed as `stage3_positive`.

For the negative half, the source contains a checked dependent recursion for the adaptive transcript. It presents powers of two on even rounds, chooses fresh odd ordinary candidates on odd rounds, answers each query against the currently admitted target, and permanently reserves every query and output. Checked supporting results include finite-history coherence, ordinary-candidate injectivity, a bounded fresh-index lemma, and linear cardinality bounds for admitted and reserved sets.

Remaining gap: the replay/legality invariants, construction of the ambient-order `OrderedLanguage`, scored-set containment, and the final ordered upper-density-zero estimate have not been completed. Consequently the exact `stage3_result : Stage3S2B.MainClaim` is not certified and is intentionally not asserted with a placeholder.

Material sources: `Stage3Model.lean`, `CANONICAL_FULL_PROOF.md`, `GenLimit.Core.OrderedDensity`, and `GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality`.
