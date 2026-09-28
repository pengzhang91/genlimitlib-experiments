Overall outcome: COMPLETE

The exact declaration `stage3_result : Stage3Case025.MainClaim` is implemented and passes both the complete entry-point check and the final controller gate. The checker reports only the permitted standard axioms `propext`, `Classical.choice`, and `Quot.sound`, with no inadmissible axioms or prohibited mechanisms.

The proof applies `GenLimit.PatientMachine.patientScope_generation_and_lowerDensity` to a family closed under finite additions, realizes the patient machine as the required presenter-first online generator, transfers eventual novelty from the finite expansion back to the original target, and proves that finite expansion does not reduce ambient-prefix relative lower density below one half.

Materially used supplied declarations include the patient machine and its density theorem from Paper 39, the core presentation/sample lemmas, and the finite-expansion transfer pattern from Paper 17.
