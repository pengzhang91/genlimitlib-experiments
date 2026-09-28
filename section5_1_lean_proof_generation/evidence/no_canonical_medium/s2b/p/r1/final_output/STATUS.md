Overall outcome: PARTIAL

The checked source proves the first two required components: `targetClass` is not countable, and the common powers-of-two core gives uniform generation without samples using one injective stream and threshold zero. These are packaged as `stage3_positive`.

It also contains a checked recursive diagonal construction for an arbitrary feedback generator. The constructed target belongs to `targetClass`; its presentation is clean, injective, and complete; every core element is presented; future ordinary presentations avoid all prior presentations, queries, and outputs; queried membership is characterized by the finite transcript prefix plus the core; and a causal presenter realizing the stream is supplied.

Remaining gap: the exact `stage3_result : Stage3S2B.MainClaim` is not declared because the oracle/protocol bridge and the final ordered upper-density-zero calculation were not completed. No placeholder, new axiom, unsafe feature, or kernel bypass remains in the delivered Lean source.

Materially used sources: `Stage3Model.lean`, `THEOREM_STATEMENT.md`, `TASK_STAGE3.md`, and the ordered-density definitions imported by the shared model.
