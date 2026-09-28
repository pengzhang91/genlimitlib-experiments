Overall outcome: PARTIAL

The exact declaration `stage3_result : Stage3Case025.MainClaim` is not completed.

Strongest checked result: `stage3_finite_noise_transfer : Stage3Case025.FiniteNoiseTransferPrinciple`. The checked source constructs the fixed countable closure under finite additions, proves that every complete finite-occurrence-noise stream exactly presents one member of that closure, transfers eventual novel generation by eventual injectivity against a finite exceptional set, and proves invariance of the required relative lower-density lower bound under finite target extension. `stage3_result_reduced` therefore derives the exact main claim from `PositivePresentationHalfDensity` without changing the shared model.

Remaining gap: formalize the Section 4 patient-stack online generator for repeated positive presentations, including its state invariants, eventual target focus, ordinary-point partner injection, and charging bound for deletion points. No axiom, `sorry`, `admit`, unsafe feature, or kernel bypass is used.

Material sources/declarations: `Stage3Model.lean`, `CANONICAL_FULL_PROOF.md`, `GenLimit.Presents`, `GenLimit.NovelGeneratesInLimit`, `GenLimit.GeneratorFirst`, `GenLimit.PatientScope.prefixCount`, and `GenLimit.PatientScope.relativeLowerDensity`.
