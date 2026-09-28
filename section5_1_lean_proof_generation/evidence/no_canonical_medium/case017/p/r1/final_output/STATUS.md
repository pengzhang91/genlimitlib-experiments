Overall outcome: COMPLETE

Implemented and checked the exact declaration `stage3_result : Stage3Case017.MainClaim` in `Case017Formalization.lean`.

The proof constructs a deterministic least-available online generator for each finite family, proves stabilization of the current compatible-family core to `informationCore`, and establishes eventual target membership, input freshness, and output nonrepetition. For the density clauses, it proves that never-presented core elements are announced first and uses an injective first-input-time predecessor pairing to derive the finite-prefix half-core estimate, then passes both estimates to relative lower densities.

Materially used `Stage3Model` and its imported GenLimit declarations for partial presentations, novelty, first announcements, and relative lower density. The complete entry-point check and final controller gate pass using only the permitted axioms `propext`, `Classical.choice`, and `Quot.sound`.
