Overall outcome: COMPLETE

- Implemented `stage3_result : Stage3Case017.MainClaim` in `Case017Formalization.lean`.
- Constructed one family-dependent online generator and its recursive output trajectory.
- Proved eventual target validity, sample freshness, and output nonrepetition for every compatible target.
- Proved both required target-relative lower-density bounds, including the half-core finite-prefix pairing argument and the never-presented-core inclusion.
- The targeted Lean check passes with only the permitted axioms `propext`, `Classical.choice`, and `Quot.sound`.
