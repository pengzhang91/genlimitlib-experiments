# Formalize the supplied complete mathematical proof

Read `THEOREM_STATEMENT.md`, `CANONICAL_FULL_PROOF.md`, and
`Stage3Model.lean`. The mathematical claim and exact Lean target are fixed.
Consult any additional supplied source material selectively.

Create `output/Case024Formalization.lean` with this root declaration:

```lean
import Stage3Model

theorem stage3_result : Stage3Case024.MainClaim := by
  sorry
```

Replace the placeholder. Do not change shared definitions, weaken the
conclusion, or add assumptions. Local helper files and alternative valid proof
architectures are allowed. The supplied prose proof is guidance, not an axiom.

## Deliverables

1. `output/Case024Formalization.lean` and any local Lean helpers it imports.
2. `output/STATUS.md`, at most 500 words. Begin with exactly one of
   `Overall outcome: COMPLETE`, `Overall outcome: PARTIAL`, or
   `Overall outcome: BLOCKED`. Briefly state the strongest checked result,
   remaining gap, and sources or declarations materially used.

## Budget and success

You have 90 minutes including tools and compilation. Save checked progress.
Check a complete entry point before any optional refactoring:

```bash
bash LEAN_CHECK.sh output/Case024Formalization.lean
bash LEAN_CHECK.sh --final
```

Success means that a correct proof of the exact target is present in a frozen
artifact by the author cutoff, with no `sorryAx` or unapproved transitive
axiom. A placeholder never counts. The controller may preserve a successful
intermediate checkpoint; independent validation occurs later and may verify
but not repair it. If incomplete, leave the
strongest checked partial sources. Do not stop at a plan or ask questions.
