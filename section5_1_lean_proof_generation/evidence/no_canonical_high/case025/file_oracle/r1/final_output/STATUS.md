Overall outcome: COMPLETE

The exact declaration `stage3_result : Stage3Case025.MainClaim` is proved and passes the supplied entry-point checker and final axiom audit. The proof constructs a semantic online patient-scope generator for exact positive presentations, enumerates all finite expansions of the indexed family, converts each complete finite-occurrence presentation into an exact presentation of a coded expansion, transfers eventual novelty after the finite extraneous values have appeared, and proves that ambient-prefix relative lower density cannot decrease when the finite extraneous part is removed from the target.

Materially used declarations include `PatientMachine.patientScope_lowerDensity_half`, `finiteExpansionOracleFamily`, `finiteExpansion_displayedNoise_displayedOmissions`, `displayedNoise_finite`, `Generic.finset_eventually_subset_sample`, and `PatientScope.tendsto_prefixCount_atTop`.

The checked result uses only the permitted standard axioms `propext`, `Classical.choice`, and `Quot.sound`; no placeholders or prohibited mechanisms remain.
