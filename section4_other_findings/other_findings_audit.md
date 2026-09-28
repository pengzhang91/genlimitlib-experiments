# Mathematical audit of Other Findings

**Verdict:** A fresh, independent, proof-by-proof review found no material mathematical error in the five results under their stated assumptions. The revision improves precision and exposition; it does not retract or weaken a substantive theorem. This is an AI-assisted written mathematical audit with supplementary finite checks, not a new Lean certification or human peer review.

The current document, *Other Findings*, uses a simple research-note structure: contents, Findings 1–5, comparison tables, and references. The paper-style abstract, introduction, and discussion have been removed. Mathematical typography and the audit corrections are retained. This structural revision does not change any theorem or proof.

## What was checked

| Finding | Main proof obligations | Supplementary checks |
|---|---|---|
| Overlapping representative groups | Completion preserves dual VC dimension; functional separation; measurable finite approximation; integral tree costs including empty vertices; exact bottleneck and positive dual attainment; sharp constant and matching fixed-target example | 160 finite primal-LP/bottleneck comparisons, including empty tree vertices and forbidden zero-mass points; largest numerical residual 3.33e-16 |
| Exact logarithmic coefficient | Rational attainment; tangent primal/dual; binary no-cancellation mass bound; adaptive upper bound; fixed-target common-prefix lower bound; exact examples; MaxCut reduction and NP certificates | 3,450 LP solves across 30 joint signatures, 86 infinite subfamilies, 432 tangent count/anchor cases, exact families, and small MaxCut gadgets |
| Metric generation | Legal covering centers; bounded non-totally-bounded obstruction; finite/countable all-scale scheduler; completion equivalence; empty and repeated-history cases | Direct theorem-by-theorem proof and edge-case review |
| Contrastive ambiguity | Exact realization; complete-presentation versus finite-prefix lower bounds; exact widths; finite regular-language realization; hypergraph decomposition | Exhaustive finite checks on all 126 complexes with one to four vertices; 9,310 realization/subclass checks |
| Sparse holes | Tape independence; measurable quantile cutoffs; infinitely many residue hits; Fubini extraction of a fixed dense target; error-frequency convergence; locking/inner-cover argument; known-envelope separation | Direct probability and quantifier review; explicit boundary cases |

The finite calculations use floating-point LPs or finite combinatorial enumeration. They are diagnostics, not formal proofs of the infinite theorems.

## Corrections incorporated

1. The two-block attainment statement now says: **if the supremum is positive, it is attained**. This is the dual bottleneck; it does not assert an optimal fresh distribution exists.
2. The tangent lemma explicitly quantifies over **integer sample-count vectors**. The hardness discussion specifies that one known target already suffices.
3. The contrastive model explicitly uses deterministic learners, permits an empty fallback list, and identifies the sharpness construction's vertex set as the union of its two facets.
4. The sparse-hole locking proof includes the empty extension and makes the enumeration step precede each bad extension. The square-time concentration and interpolation argument is written out.
5. The scope review confirmed the necessary qualifiers: finite dual VC dimension; countable classes of unbounded metric targets; all positive scales; fixed streams in the vanishing-frequency theorem; and mistakes charged for observed **input** points, not merely repeated prior outputs.

## Essential limits retained

- The sharp overlap rate assumes two blocks of dual VC dimension at most one and linear completed-cell capacity growth. A bound of two on the overall dual VC dimension alone is not the stated hypothesis.
- The minimax asymptotic fixes a finite target family and finite group family. Its algorithms use semantic profile access; the hardness result concerns an explicit finite signature.
- Metric generation concerns countable classes of unbounded targets and all positive input/output scales, with ambient covering centers.
- Exact contrastive width formulas concern the constructed classes. Eventual correctness on complete presentations differs from a finite-prefix threshold guarantee.
- The sparse-hole adversarial target and increasing text are fixed before the algorithm tape. Known-envelope almost-sure success events may depend on the target. The deterministic lower bound requires success on every full text.
- No comprehensive literature-priority or conference-acceptance conclusion follows from this audit.

## Detailed review records

- [Overlap audit](other_findings_audit/overlap_audit.md)
- [Minimax coefficient audit](other_findings_audit/gamma_audit.md)
- [Metric, contrastive, and sparse-hole audit](other_findings_audit/metric_contrastive_sparse_audit.md)
- [Overlap finite checks](other_findings_audit/overlap_finite_lp_check.py) and [results](other_findings_audit/overlap_finite_lp_check.json)
- [Minimax finite checks](other_findings_audit/gamma_lp_checks.py) and [results](other_findings_audit/gamma_lp_checks.json)
- [Revision integrity and source hashes](other_findings_audit/revision_integrity.json)

The detailed proof audits refer to the preserved first-edition sources; their mathematical content is retained in the revision with the clarifications above. The original report remains in `archive_v1/`; the subsequent paper-style edition is preserved in `archive_v2_academic/`. The present update restores the research-note structure while retaining the audited mathematics.
