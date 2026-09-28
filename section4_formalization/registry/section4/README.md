# Section 4: statements, proofs, and Lean correspondence

This record maps the manuscript's mathematical claims to the added Lean declarations. All paths below are relative to this repository. The original paper maps remain under `GenLimitLean/PaperMaps/`; the additions below are new manuscript results, not claims that the source papers already proved them.

| Manuscript result | Written proof | Main Lean entry point |
|---|---|---|
| Section 4.1: proof gap and repair | [Appendix A.2](../../manuscript/section4/appendix_proof_guide.tex) | [InvariantRepair.lean](../../GenLimitLean/Section4/InvariantRepair.lean), together with P13's existing `GlobalInvariant.lean` and `ArbitraryScheduler.lean` |
| Section 4.2: three-language impossibility, Theorem 1, finite-state consequences | [Appendix A.3](../../manuscript/section4/appendix_replay.tex) | [Replay.lean](../../GenLimitLean/Section4/Replay.lean) |
| Section 4.3: Theorem 2 and its two extreme examples | [Appendix A.4](../../manuscript/section4/appendix_p29_frontier.tex) | [StaircaseAbstract.lean](../../GenLimitLean/Section4/StaircaseAbstract.lean), [StaircaseTransportProfiles.lean](../../GenLimitLean/Section4/StaircaseTransportProfiles.lean), [StaircaseExtremes.lean](../../GenLimitLean/Section4/StaircaseExtremes.lean) |

## Proof repair

The upstream P13 declarations `literal_claim_3_2_counterexample`, `maxScoreBound_persists_insert`, `InsertionSplit.orderMaxScoreBounds`, and `target_selected_in_greedyListScan` cover the counterexample, preservation of the numerical score bound, its induction through insertions, and retention of the target. The source paper's published Claim 7 and Theorem 8 have older arXiv numbers in these existing identifiers.

The new `Section4.InvariantRepair.published_theorem_8_with_repetitions` checks the appendix's repeated-observation argument. The scheduler uses the total number of rounds, while the convergence threshold uses the number of distinct observations. It retains the original scheduler and generator. Oracle-access implementation and running-time claims are outside this theorem's scope.

## Proper generation under replay

The final module `Section4.Replay` exposes:

- `triangle_transfer`: impossibility for an arbitrary infinite common core and three distinct markers, using the original P22 replay semantics.
- `finite_replay_characterization`: the first-observation version of Theorem 1.
- `finite_replay_characterization_profiles`: the equivalent version phrased using realized membership profiles.
- `finite_state_replay_corollary`: one generator satisfying the semantic success condition, stabilization, inclusion-minimal outputs, contamination containment, at most N output changes, and an explicit Mealy-machine realization with `1 + N * 2^N` states.

The family is finite and nonempty; duplicate languages are allowed. Necessity uses a countable universe. The characterization actually proves a stronger statement without requiring every language to be infinite; the manuscript imposes infinitude because this is its generation setting. No computability restriction is imposed. The machine reads the current point's membership profile; its fixed transition/output tables depend on the family.

Only outputs after nonempty input prefixes count as replay material or toward the output-change bound. This agrees with the paper's input-then-output order and avoids an extra change caused by the arbitrary empty-history value.

## Mistake and convergence guarantees

`Family.exact_staircase_frontier` proves the three conclusions for the concrete normal form. `Realization.exact_staircase_frontier` transports them to arbitrary ambient sets, including generators that output points outside the union of all target languages. `StaircaseRepresentation.lean` constructs the representation from the manuscript's disjoint finite nonempty common blocks and countably infinite private sets; `Section4.Staircase.abstract_exact_staircase_frontier` in `StaircaseAbstract.lean` combines it with the full numerical characterization. Only the private sets need be countable; the ambient universe may be arbitrary.

The formal profile uses extended naturals. `worstMistakes` is the supremum of actual error counts over legal ordered histories; `worstDeadline` is the supremum of one plus the length of every history causing an error. The `*_le_iff` lemmas connect these definitions to uniform mistake and convergence bounds, including infinite values. These are defined from the actual generator, not assumed bounds.

`StaircaseStreams.lean` proves that every legal finite history extends to an infinite injective stream and to a complete injective enumeration. It proves that the finite-history bounds equal the stream and complete-text bounds. `Realization.every_history_completes` supplies the same continuation in the arbitrary ambient universe.

`StaircasePareto.lean` proves that distinct binary sequences have incomparable mistake vectors. The frontier theorem combines this with the arbitrary-generator lower bound to obtain Pareto minimality and completeness. `Family.extreme_profiles` checks the two constant choices, including the first-target zero-mistake and zero-convergence-time exception.

### Notation and conventions

- Lean indices start at zero: Lean target `i` corresponds to manuscript target `L_(i+1)`.
- `Family.ofBlocks` uses cumulative sums of arbitrary positive block sizes. The concrete common points are natural numbers, and each private part is an indexed copy of the naturals.
- Histories are ordered lists of distinct observations. An output must be absent from the observed inputs; outputs may repeat each other.
- Time is the number of observations already received, including zero. A mistake after s observations forces convergence time at least s+1.
- Generators are deterministic functions of their full ordered histories, without effectiveness or running-time restrictions.
- “Deadline” in Lean identifiers denotes precisely the worst-case convergence time defined in the TeX. The prose uses “convergence time”, matching the source literature.

## Reproduction and evidence

Run `bash scripts/verify_section4.sh --fetch-cache` from the repository root on a fresh checkout. This builds `Section4` and its transitive dependencies, then checks the listed endpoint axioms. The permitted logical axioms are the usual `propext`, `Classical.choice`, and `Quot.sound`. See [verification records](verification/) for source hashes, compiler versions, and the recorded output.

The Lean verification status is **passed**. The included source-repository
record reports a complete 3130-job `Section4` build, and the delivered Lean
sources match the verified sources. See
[`verification/STATUS.md`](verification/STATUS.md) for the evidence boundary.

This verification is specific to the Section 4 statements and their dependencies. It is not a claim that every historical or unrelated upstream result has been re-audited. The [source list](SOURCES.md) and this map make the paper-to-code interpretation explicit.
