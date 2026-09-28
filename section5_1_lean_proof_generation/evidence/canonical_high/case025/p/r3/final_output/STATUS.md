Overall outcome: PARTIAL

The checked artifact implements a concrete deterministic patient-stack online generator and its recursively defined trajectory. `output/Helpers.lean` proves that every stack focus used by the machine is infinite, the generated trajectory follows the online rule, every output avoids all presenter observations through the current round, outputs never repeat, and every output is generator-first. `output/Case025Formalization.lean` exposes this as `stage3_checked_global_fresh` and proves that eventual containment of the machine focus in a target implies `GenLimit.NovelGeneratesInLimit`.

The exact declaration `stage3_result : Stage3Case025.MainClaim` is not completed. The remaining gaps are the full eventual-focus stabilization proof for every exact positive presentation, the charging/counting argument yielding relative lower density at least `1/2`, and the finite-addition transfer from positive presentations to finite occurrence noise.

Materially used sources: `Stage3Model.lean`, `THEOREM_STATEMENT.md`, `CANONICAL_FULL_PROOF.md`, the supplied abstract announcement/density vocabulary, and standard Lean/mathlib list, finset, set, and recursion facilities.
