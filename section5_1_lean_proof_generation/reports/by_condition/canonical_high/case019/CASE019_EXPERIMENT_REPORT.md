# Case 019 five-replicate experiment report

Generated from frozen evidence at `2026-09-21T02:25:33.164552+00:00`.

## Executive summary

The campaign contains exactly 15 official independent author runs, five per arm. The exact-target Lean-kernel endpoint was **8/15** (53.3%; Wilson 95% interval [30.1%, 75.2%]). All **1465** audited model calls were served by OpenAI with no fallback or unverifiable call. Official upstream API cost was **$45.9802** for **91,570,790** input and **930,532** output tokens.

| Arm | Lean-valid / runs | Author time | Calls | Input | Output | Total tokens | Cost | Mean first valid* |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| P | 0 / 5 | 1h 41m 17s | 267 | 16,311,569 | 178,201 | 16,489,770 | $6.8074 | — |
| PML | 3 / 5 | 2h 20m 40s | 559 | 36,070,724 | 355,266 | 36,425,990 | $18.7988 | 31m 20s |
| PML-FileOracle | 5 / 5 | 3h 04m 26s | 639 | 39,188,497 | 397,065 | 39,585,562 | $20.3739 | 35m 48s |
| **Overall** | **8 / 15** | **7h 06m 24s** | **1465** | **91,570,790** | **930,532** | **92,501,322** | **$45.9802** | **34m 08s** |

\* Successful runs only. Queue time and non-generative setup/verification are excluded.

## Task and protocol

Case 019 asks for two statements under injective, distinct-value finite contamination: a countable-family generator attaining target-relative lower density at least one half, and an uncountable integer-language family with a level-`q` quarter-density generator but no eventually valid semantic generator at level `q+1`. The exact Lean root is `Stage3Case019.MainClaim`, submitted as `stage3_result` in `Case019Formalization.lean`.

Every arm received the same theorem, complete prose proof, exact Lean statement, papers, 5,400-second author budget, `openai/gpt-5.6-sol` model alias, high reasoning effort, and controller. P received an eight-file definition-only vocabulary and no research theorem library; PML received the full 161-file research tree; PML-FileOracle received the exact 59-file post-hoc source/import closure and no declaration shortlist or prior proof. Primary success is independent exact-target Lean validation, not reviewer judgment; no reviewer was run.

Preparation compiled one seed packet per arm and copied its hash-verified Lean environment and compiled artifacts to the other four byte-identical replicates. Author outputs, conversations, model responses, and proxy streams were never reused. The three arms ran in parallel within each wave, while waves were sequential.

| Arm | Compiled seed packets | Replicates | Distinct frozen manifests | Lean sources / compiled artifacts per packet | Shared cache |
|---|---:|---:|---:|---:|---|
| P | 1 | 5 | 1 | 11 / 10 | not a 161-source PML tree |
| PML | 1 | 5 | 1 | 164 / 163 | validated content-addressed cache |
| PML-FileOracle | 1 | 5 | 1 | 62 / 61 | not a 161-source PML tree |

The preparation record reports `PREPARED` with 0 model calls. The frozen manifests and their evidence hashes are included in the machine-readable report.

## Run-level results

| Arm | Run | Result | First valid | Author elapsed | Calls | Input / output | Cost |
|---|---:|---:|---:|---:|---:|---:|---:|
| P | r1 | FAIL | — | 13m 57s | 42 | 2,524,166 / 31,367 | $1.0131 |
| P | r2 | FAIL | — | 8m 00s | 23 | 1,109,587 / 17,517 | $0.5596 |
| P | r3 | FAIL | — | 32m 25s | 86 | 5,775,593 / 52,323 | $2.3042 |
| P | r4 | FAIL | — | 12m 46s | 36 | 2,059,971 / 26,756 | $0.8914 |
| P | r5 | FAIL | — | 34m 08s | 80 | 4,842,252 / 50,238 | $2.0391 |
| PML | r1 | FAIL | — | 33m 19s | 124 | 8,283,460 / 86,188 | $4.7455 |
| PML | r2 | PASS | 24m 52s | 25m 37s | 111 | 6,757,903 / 59,373 | $3.2461 |
| PML | r3 | PASS | 27m 25s | 28m 53s | 111 | 6,978,090 / 79,952 | $3.9187 |
| PML | r4 | PASS | 41m 44s | 42m 35s | 159 | 10,356,107 / 102,812 | $5.2490 |
| PML | r5 | FAIL | — | 10m 16s | 54 | 3,695,164 / 26,941 | $1.6394 |
| PML-FileOracle | r1 | PASS | 34m 06s | 35m 04s | 118 | 7,714,385 / 69,448 | $3.6022 |
| PML-FileOracle | r2 | PASS | 36m 15s | 37m 16s | 130 | 7,538,976 / 75,489 | $3.9126 |
| PML-FileOracle | r3 | PASS | 31m 02s | 31m 45s | 107 | 6,647,797 / 72,461 | $3.7110 |
| PML-FileOracle | r4 | PASS | 42m 48s | 44m 23s | 151 | 9,250,103 / 88,976 | $4.8584 |
| PML-FileOracle | r5 | PASS | 34m 49s | 35m 58s | 133 | 8,037,236 / 90,691 | $4.2897 |

`input_tokens` already includes cached input; reasoning output is a subset of output. Neither is added twice. Author time excludes scheduler queue time.

## Library reuse in valid proofs

Reuse is a dependency-closure measure, not text copying. Starting from each selected kernel-checked `stage3_result`, the audit counts proof-relevant `theorem`, `definition`, and `opaque` declarations from frozen research modules and from author root modules. Mathlib/Lean runtime, `Stage3Model`, and type/constructor-only nodes are excluded. Failed runs have no authoritative reuse percentage.

| Arm | r1 | r2 | r3 | r4 | r5 | Pooled reuse | Mean root LOC |
|---|---:|---:|---:|---:|---:|---:|---:|
| P | N/A | N/A | N/A | N/A | N/A | **N/A** (0 / 0) | N/A |
| PML | N/A | 85.6% | 86.5% | 84.5% | N/A | **85.5%** (1631 / 1907) | 1142.3 |
| PML-FileOracle | 87.0% | 84.6% | 86.3% | 84.9% | 85.2% | **85.6%** (2711 / 3168) | 1068.4 |

## Failed official runs

- `p_case019_delta_v1_r1`: author ended `FINISHED` after 13m 57s; 42 audited calls; The submitted entry sources compile, but they do not define the required `stage3_result`; the exact-target check therefore fails. Checker evidence: `lean2paper_case019_delta_v1/cohort/arms/p/logs/p_case019_delta_v1_r1/checkpoints/final/root_check.log` (SHA-256 `7695d067384a090241c3e9be928992d29ea6b4370d1564b5084cfff37c717a8b`).
- `p_case019_delta_v1_r2`: author ended `FINISHED` after 8m 00s; 23 audited calls; The submitted entry sources compile, but they do not define the required `stage3_result`; the exact-target check therefore fails. Checker evidence: `lean2paper_case019_delta_v1/cohort/arms/p/logs/p_case019_delta_v1_r2/checkpoints/final/root_check.log` (SHA-256 `ddea34e53c71b04ab2730a9ec4fd228af45dac7e343aac14584c4e44ac3faada`).
- `p_case019_delta_v1_r3`: author ended `FINISHED` after 32m 25s; 86 audited calls; The submitted entry sources compile, but they do not define the required `stage3_result`; the exact-target check therefore fails. Checker evidence: `lean2paper_case019_delta_v1/cohort/arms/p/logs/p_case019_delta_v1_r3/checkpoints/final/root_check.log` (SHA-256 `10043966c8f17ec1ce893e496279d7f5cdc56df4047bfb7b3b995b4cd0523d72`).
- `p_case019_delta_v1_r4`: author ended `FINISHED` after 12m 46s; 36 audited calls; The submitted entry sources compile, but they do not define the required `stage3_result`; the exact-target check therefore fails. Checker evidence: `lean2paper_case019_delta_v1/cohort/arms/p/logs/p_case019_delta_v1_r4/checkpoints/final/root_check.log` (SHA-256 `1b0cfa1f8c3d60ccffa2cfe32aa28f78fc3a4e4eb8b2e5714b69be29baf828ab`).
- `p_case019_delta_v1_r5`: author ended `FINISHED` after 34m 08s; 80 audited calls; The submitted entry sources compile, but they do not define the required `stage3_result`; the exact-target check therefore fails. Checker evidence: `lean2paper_case019_delta_v1/cohort/arms/p/logs/p_case019_delta_v1_r5/checkpoints/final/root_check.log` (SHA-256 `3cf22591fe02bce386f7532c3903bc9a65e8ca9261b0f13da7912934ff1cfa79`).
- `pml_case019_delta_v1_r1`: author ended `FINISHED` after 33m 19s; 124 audited calls; The submitted entry sources compile, but they do not define the required `stage3_result`; the exact-target check therefore fails. Checker evidence: `lean2paper_case019_delta_v1/cohort/arms/pml/logs/pml_case019_delta_v1_r1/checkpoints/final/root_check.log` (SHA-256 `b0ffceca6fb864a7dddbf835828a26aaa9c47188086552aeeb97660d48fe8a6c`).
- `pml_case019_delta_v1_r5`: author ended `FINISHED` after 10m 16s; 54 audited calls; The submitted entry sources compile, but they do not define the required `stage3_result`; the exact-target check therefore fails. Checker evidence: `lean2paper_case019_delta_v1/cohort/arms/pml/logs/pml_case019_delta_v1_r5/checkpoints/final/root_check.log` (SHA-256 `93bef82dfac8d6cd213ef5e986e0ad62cb6176ff6bee9e7f32be510dbf1853f8`).

These are retained in the official denominator. A model run that ends normally without an independently valid exact-target checkpoint is a scientific failure, not repaired after the cutoff.

## Infrastructure-censored attempt

The first PML r3 attempt (`SLURM_JOB_025_1`) was killed by a one-hour Slurm allocation even though the frozen controller allowed 5,400 author seconds. It made 186 OpenAI-routed calls, consumed $6.4681, and had no valid checkpoint. It is preserved at `${REPO_ROOT}/case019_aborted_attempts/pml_case019_delta_v1_r3_jobSLURM_JOB_025` but excluded from the official sample because the external scheduler censored the run before the protocol cutoff. Only PML r3 was replaced; the already completed P and FileOracle r3 outcomes were retained. Replacement r3 and r4-r5 received 95-minute allocations (90-minute author budget plus five minutes of controller overhead). This incidental $6.4681 is project spend but is not included in the official table or treatment totals.

Three earlier preparation attempts made zero model calls and are documented in `case019_delta_v1_logs/SUBMISSION.json`: a stale Case 025 preflight name, a runtime-probe source-immutability issue, and an operator-cancelled redundant cold compile. None produced an author outcome or entered the sample.

The primary final verification/package job `SLURM_JOB_032` completed successfully. Conditional safeguard job `SLURM_JOB_033` was queued because Delta would not extend the running job's time limit; it found the completed archive checksum valid and exited as `COMPLETED_NO_OP` with 0 model calls. It did not alter or duplicate any experimental outcome. Concrete Slurm identifiers use the same stable anonymous labels as the accompanying metrics file.

## Integrity checks

The generator refuses to emit this report unless all 15 declared IDs are present and terminal; each validation identity matches its run; each author exits normally; every routing audit passes and contains only OpenAI with zero unverifiable calls; success agrees with a first independently revalidated checkpoint; selected dependency evidence exists; and no reviewer output is present. Successful checkpoints may use only the controller-recorded permitted standard axioms; per-run axiom lists and evidence hashes are in the CSV/JSON.

## Limitations

- Five runs per arm are descriptive pilot evidence, not a powered treatment comparison; the Wilson intervals remain wide.
- Replicates are stochastic fresh model trajectories, not seeded deterministic replays.
- FileOracle is a post-hoc navigation ceiling validated against a private proof and should not be interpreted as a prospectively selected treatment.
- P/PML/FileOracle change bundled resources and navigation together, so outcome differences do not identify the effect of a single file or theorem.
- First-valid time is the controller receipt time of a captured, independently revalidated gate and is an observed upper bound.
- Parallel waves make campaign makespan unsuitable for arm-efficiency comparisons.

## Reproducibility artifacts

The machine-readable aggregate is `reports/case019_delta_v1/CASE019_FIVE_RUN_METRICS.json`; run-level evidence is `reports/case019_delta_v1/CASE019_RUN_LEVEL_RESULTS.csv`.

- `lean2paper_case019_delta_v1/SOURCE_MANIFEST.json` — 76,124 bytes; SHA-256 `7d2a58e1775a838ba6d7a8c184d80f4564460dae45699853bd0b4eb17645ede1`
- `lean2paper_case019_delta_v1.tar.zst` — 5,764,888 bytes; SHA-256 `7f676e7659f02dd39e411555e583b7f23e630a90e461ec6d78c851e7f922b817`
- `case019_delta_v1_logs/SUBMISSION.json` — 6,271 bytes; SHA-256 `f25668de0850e86f850d6e9909f5e40941bc903e6c23ab3605d8c24a52a7eee6`
- `lean2paper_case019_delta_v1/cohort/PREPARATION.json` — 887 bytes; SHA-256 `f06de9582d97566a6a7fa162e505d1a9f52a67ad72b3213ec2765814fcd0aefa`
- `lean2paper_case019_delta_v1/cohort/arms/p/control/design_freeze.json` — 39,305 bytes; SHA-256 `e889bac89fe1ebddd8eaa576f8f3b60eb6d43fde5270ebaea81ff70e75882312`
- `lean2paper_case019_delta_v1/cohort/arms/pml/control/design_freeze.json` — 354,278 bytes; SHA-256 `18677fddff267783a103200521715d5d509f3609ab28183939c487d9bd6f88d0`
- `lean2paper_case019_delta_v1/cohort/arms/file_oracle/control/design_freeze.json` — 151,057 bytes; SHA-256 `3bf7d11a719c8f24bb13d60e8d4abe595f8cb910d670b14f33d4639c34dab623`
- `lean2paper_case019_delta_v1/result_archives/case019_delta_v1_results_20260921T021543Z.tar.zst` — 24,197,404 bytes; SHA-256 `6602ff7422688c809d92e6e8e10030d2871d45eb3642caea83f2d55328d4ff7b`
- `case019_aborted_attempts/pml_case019_delta_v1_r3_jobSLURM_JOB_025/ATTEMPT.json` — 1,403 bytes; SHA-256 `e8655f5f1e30f9b38283d98bd54e4b5717fc4a65abfd3f1b1c6b2697b17d0c74`
