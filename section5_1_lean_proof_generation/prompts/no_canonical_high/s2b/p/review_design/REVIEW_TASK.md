# Conditional anonymous review of incomplete formalizations

Model: gpt-5.6-sol / ultra. At most one fresh 90-minute session.
Only the incomplete submissions listed in SUBMISSIONS.json are supplied.
Complete submissions have already passed the fixed root gate and are not
reviewed or reranked. This review cannot change that primary success decision.

Read the common theorem statement, full natural-language proof,
Stage3Model.lean, and the private OBLIGATIONS.md rubric. Authors did NOT see this rubric or
write an obligation ledger. Do not penalize a different valid architecture.

For each anonymous submission, describe:
- the strongest actually checked result, citing precise declarations;
- the constructed objects and established dependency chain;
- the first substantive gap;
- whether the missing work is core construction, proof, interface bridging,
  or final technical cleanup;
- how O1–O7 / C1 are covered or bypassed by an alternative route.

Use PROVED / PARTIAL / BLOCKED / UNCERTAIN per rubric item. PROVED requires
appropriate compiler/axiom evidence and established assumptions, not only a
claim in a report. A conditional theorem assuming the hard invariant does
not construct that invariant. If supplied logs cannot certify a declaration,
mark its verification UNCERTAIN rather than inventing a kernel result.
Unimported scratch is not part of the root proof; its separate merits, if any,
must be explicitly identified and independently supported.

DECLARATION_INVENTORY.json, when present, lists the actually imported author
declarations and their transitive axioms from an independent compiler pass.
It does not assert that a conditional theorem's assumptions have been built;
that semantic dependency check remains your task. Missing inventory is not
permission to label an unverified declaration PROVED.

Report compilation defects separately from mathematical gaps. Do not infer
a substantive failure from an infrastructure interruption alone. Exact Lean
names and frozen source references remain visible for mathematical inspection;
do not infer source conditions from those names.

Write output/PARTIAL_REVIEW.md (at most 4,500 words) and
output/PARTIAL_PROGRESS.tsv with this tab-separated header:

submission\tobligation_id\tstatus\tsupporting_declarations\tverification_evidence\tremaining_gap

Write one row per supplied submission and rubric item. Explain dependency
structure in the prose report; do NOT rank by a raw count such as 5/8 vs 4/8.
Ties and unresolved comparisons are acceptable. This is descriptive analysis
of incomplete artifacts, not another correctness gate or a proof-repair round.
