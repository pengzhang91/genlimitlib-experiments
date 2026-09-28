# S2B five-replicate experiment report

> Anonymous-release note: concrete Slurm scheduler identifiers were replaced by stable file-local labels; scheduling relationships are preserved.


Generated from frozen run evidence at `2026-09-20T14:04:14.786397+00:00`. Packaging status: **complete and archived**.

## Executive summary

Across 15 independent author runs (five per arm), 14 produced a Lean-kernel-valid proof of the exact target within the 5,400-second budget. P and PML-FileOracle each succeeded in 5/5 runs; PML succeeded in 4/5. Total measured OpenRouter upstream cost was **$28.3353** for **1,004** model calls, **58,830,427** input tokens, and **638,354** output tokens. The only failure, `pml_delta_v1_r4`, was a genuine incomplete model attempt rather than an infrastructure or routing failure.

These five-run samples are adequate for a pilot/descriptive comparison, but too small to establish arm superiority. The overall success proportion was 14/15 (93.3%; Wilson 95% interval [70.2%, 98.8%]).

| Arm | Lean-valid / runs | Success | 95% Wilson CI | Input tokens | Output tokens | Calls | Cost | Mean author time | Mean first valid* |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| P | 5 / 5 | 100.0% | [56.6%, 100.0%] | 21,113,740 | 229,143 | 362 | $10.4658 | 22m 12s | 21m 30s |
| PML | 4 / 5 | 80.0% | [37.6%, 96.4%] | 16,100,389 | 196,521 | 265 | $8.2120 | 18m 45s | 20m 03s |
| PML-FileOracle | 5 / 5 | 100.0% | [56.6%, 100.0%] | 21,616,298 | 212,690 | 377 | $9.6576 | 24m 38s | 23m 49s |

\* Mean over successful runs only. Queue time is excluded.

## Research question and exact target

The experiment asks whether different author-visible formal resources help an agent formalize the supplied complete proof of the “feedback-resistant density boundary.” With `E = {2^k : k ≥ 0}`, `O = ℕ \ E`, and `𝒰 = {E ∪ A : A ⊆ O}`, the fixed Lean target `Stage3S2B.MainClaim` packages two claims: the extensional class `𝒰` is uncountable yet uniformly generatable without samples, and every deterministic eventually valid/fresh feedback generator has a target and causal clean complete presentation for which the target-relative upper density of first-announced target points is zero.

Every arm received the same theorem statement, canonical complete prose proof, fixed `Stage3Model.lean`, task instructions, checker, and five papers. The treatment was the extra Lean/navigation material:

- **P:** papers plus six deliberately stripped vocabulary files; no research closure or supplements.
- **PML:** papers, supplements/navigation cards, and the full 161-file Lean research closure.
- **PML-FileOracle:** the PML-style packet with the research library reduced to four source files: `GenLimit.Core.Basic`, `GenLimit.Core.OrderedDensity`, `GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality`, and `GenLimit.Paper39_DenseGeneration.Abstract.Density`. This is explicitly a post-hoc file-oracle ceiling derived from an earlier successful proof, not an independently selected treatment.

Consequently, P versus PML estimates the effect of the **bundled resource package**, not the isolated causal effect of proved declarations. FileOracle is a targeted navigation ceiling and must be interpreted separately.

## Protocol

- Model alias: `openai/gpt-5.6-sol`; every audited response reports served model `openai/gpt-5.6-sol-20260709`.
- Reasoning effort: `high`; context window: 1,050,000 tokens.
- Author budget: 5,400 seconds per run.
- Agent: Codex CLI 0.155.1.
- Formal environment: Lean 4.24.0 with the locked Lake/mathlib dependency tree.
- Transport: OpenRouter through a local pinning proxy, with `provider.only=["openai"]` and fallbacks disabled.
- Primary endpoint: independently reverified exact-target kernel pass from a stable frozen checkpoint before the author cutoff, with no `sorryAx`, prohibited mechanism, or unapproved transitive axiom.
- Reviewer: not run and not used in the success decision.
- Resources: r3-r5 used 1 CPU / 8 GiB per job. The r1-r2 jobs had a larger scheduler memory reservation, but observed MaxRSS was only about 2.3–3.5 GiB; this resource-request change did not alter the scientific packet or author budget.

Preparation was non-generative (`model_calls = 0`). Runs were organized in waves, one run per arm in parallel, and waves were sequential so two replicates of the same arm did not overlap. No seed was available; independence here means fresh work directories, conversations, proxy audit streams, and model trajectories under the same fixed protocol.

## Replication plan and execution audit

The initial batch ran r1-r2. `CONTINUATION.json` records that the five-replicate target—and the plan to run r1-r2 first followed by r3-r5—was discussed before formal r1-r2 outcomes were observed. Thus the extension was not chosen in response to the initial success pattern, although it was executed as a second batch.

Slurm records:

- r1-r2: preparation `SLURM_JOB_001`; wave jobs `SLURM_JOB_002` and `SLURM_JOB_003`; final corrected verifier/package job `SLURM_JOB_004`.
- r3-r5: setup `SLURM_JOB_005`; wave jobs `SLURM_JOB_006`, `SLURM_JOB_007`, and `SLURM_JOB_008`.
- The original r3-r5 verifier `SLURM_JOB_009` became stale in a pending state after its dependency cleared. It was cancelled without starting, and the identical non-generative verifier/package job was resubmitted as `SLURM_JOB_010`. No author run was repeated.
- After checking the official Delta partition policy, pending job `SLURM_JOB_010` was moved in place from `cpu` to the non-preemptive `cpu-interactive` partition. Its job ID, script, 1-CPU/8-GiB/15-minute resources, inputs, and outputs were unchanged; it added no model calls and completed in 4m52s.

The initial r1-r2 post-run verifier had one packaging-only bug: it counted author-created `.olean` files as frozen input artifacts. The amended verifier restricted that check to the frozen vocabulary/research input tree. The amendment added no model calls and changed no packets, transcripts, checkpoints, routing audits, or per-run validations.

## Aggregate results

| Arm | Lean-valid / runs | Success | 95% Wilson CI | Input tokens | Output tokens | Calls | Cost | Mean author time | Mean first valid* |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| P | 5 / 5 | 100.0% | [56.6%, 100.0%] | 21,113,740 | 229,143 | 362 | $10.4658 | 22m 12s | 21m 30s |
| PML | 4 / 5 | 80.0% | [37.6%, 96.4%] | 16,100,389 | 196,521 | 265 | $8.2120 | 18m 45s | 20m 03s |
| PML-FileOracle | 5 / 5 | 100.0% | [56.6%, 100.0%] | 21,616,298 | 212,690 | 377 | $9.6576 | 24m 38s | 23m 49s |

The point estimates differ by only one outcome. With n=5 per arm, Wilson intervals are very wide: a 5/5 result has an approximate 95% interval of 56.6%–100%, while 4/5 has an interval of 37.6%–96.4%. These data do not support a statistically credible ranking among arms.

## Run-level results

| Arm | Run | Result | First valid | Author elapsed | Calls | Input | Cached | Output | Reasoning† | Cost |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| P | r1 | PASS | 19m 38s | 19m 51s | 78 | 4,816,207 | 4,404,023 | 49,547 | 16,530 | $2.4041 |
| P | r2 | PASS | 21m 08s | 21m 55s | 60 | 3,583,482 | 3,306,653 | 40,942 | 12,923 | $1.7608 |
| P | r3 | PASS | 23m 56s | 24m 43s | 73 | 4,310,483 | 3,923,252 | 45,992 | 13,722 | $2.2102 |
| P | r4 | PASS | 25m 09s | 25m 59s | 86 | 4,871,018 | 4,472,011 | 53,042 | 15,567 | $2.4195 |
| P | r5 | PASS | 17m 41s | 18m 33s | 65 | 3,532,550 | 3,284,469 | 39,620 | 11,863 | $1.6711 |
| PML | r1 | PASS | 19m 07s | 20m 30s | 63 | 3,810,023 | 3,444,440 | 56,515 | 14,007 | $2.1659 |
| PML | r2 | PASS | 32m 19s | 33m 30s | 80 | 4,836,033 | 4,442,799 | 48,842 | 14,961 | $2.3574 |
| PML | r3 | PASS | 18m 22s | 19m 08s | 57 | 3,797,062 | 3,529,916 | 40,669 | 11,458 | $1.7786 |
| PML | r4 | FAIL | — | 9m 27s | 28 | 1,386,122 | 1,313,123 | 17,797 | 5,385 | $0.6221 |
| PML | r5 | PASS | 10m 25s | 11m 11s | 37 | 2,271,149 | 2,050,325 | 32,698 | 8,443 | $1.2879 |
| PML-FileOracle | r1 | PASS | 19m 23s | 20m 03s | 64 | 3,617,997 | 3,359,616 | 38,133 | 12,760 | $1.6971 |
| PML-FileOracle | r2 | PASS | 22m 31s | 23m 30s | 72 | 3,680,896 | 3,439,297 | 40,589 | 14,609 | $1.6953 |
| PML-FileOracle | r3 | PASS | 32m 48s | 33m 27s | 94 | 5,687,036 | 5,425,517 | 43,033 | 12,454 | $2.1661 |
| PML-FileOracle | r4 | PASS | 29m 07s | 30m 12s | 92 | 5,216,620 | 4,831,976 | 50,780 | 16,827 | $2.4327 |
| PML-FileOracle | r5 | PASS | 15m 16s | 15m 59s | 55 | 3,413,749 | 3,159,875 | 40,155 | 12,593 | $1.6664 |

† Reasoning tokens are a subset of output tokens and must not be added to them.

## Token use and API cost

| Arm | Input | Cached input | Cache-write input | Output | Reasoning† | Cache/input | Total cost | Cost to first valid‡ |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| P | 21,113,740 | 19,390,408 | 1,699,236 | 229,143 | 70,605 | 91.8% | $10.4658 | $10.1348 |
| PML | 16,100,389 | 14,780,603 | 1,302,156 | 196,521 | 54,254 | 91.8% | $8.2120 | $7.0521 |
| PML-FileOracle | 21,616,298 | 20,216,281 | 1,374,771 | 212,690 | 69,243 | 93.5% | $9.6576 | $9.2768 |
| **Overall** | **58,830,427** | **54,387,292** | **4,376,163** | **638,354** | **194,102** | **92.4%** | **$28.3353** | **$26.4638** |

‡ Cost-to-first-valid sums audited calls whose timestamps are no later than the first independently reverified successful checker event. It is reported only for successful runs. The controller does not claim exact within-turn token telemetry, so full-run tokens are not relabeled as tokens-to-proof.

Cached-input counts describe provider cache use; cache-write counts are reported separately and are not added to input tokens as if they were a disjoint traffic class. All **1,004** audited calls were served by OpenAI, with zero unverifiable calls and no fallback provider.

## Time results and interpretation

The sum of author elapsed times was **5h 27m 58s** and the per-run mean was **21m 52s**. The mean first-valid time over 14 successful runs was **21m 55s**. Per-arm means were 22m 12s for P, 18m 45s for PML (including its early failed run), and 24m 38s for FileOracle.

The earliest author start through latest author end spanned **8h 54m 02s**, but that interval includes inter-wave queue/batch gaps and parallel execution. It is not a measure of total compute demand or a fair arm-efficiency endpoint. Slurm queue time is excluded from every author elapsed measurement.

FileOracle's mean was modestly longer than P's in this sample, driven mainly by r3 and r4 (respectively 33m 27s and 30m 12s). Since n=5 and model paths are stochastic, the data do not identify a causal reason for that difference.

## The PML r4 failure

`pml_delta_v1_r4` ended normally with exit code 0 after **9m 27s**, well before the 90-minute cutoff. It made 28 audited OpenAI calls, used 1,386,122 input and 17,797 output tokens, and cost $0.6221. Its status described substantial checked partial progress: the positive/uncountability and sample-free-generation portion plus part of the adaptive construction. The negative-clause assembly remained incomplete, including truthful fixed-target replay, clean/injective/complete presentation, quantitative density bounds, and final `FaithfulNegativeWitness` packaging.

Independent validation found no successful observed checkpoint. The final artifact compiled only with an inadmissible `sorryAx`; exact-target checking failed, `selected_checkpoint` was null, and the run was therefore counted as a failure. There was no timeout, proxy failure, non-OpenAI routing, controller crash, or post-cutoff repair. Rerunning it would erase observed model variance, so it remains in the denominator.

## Library reuse in kernel-valid proofs

Lean imports library declarations rather than copying their source text, so this is not a
line-copy percentage. Starting at each selected, kernel-checked `stage3_result`, the audit
traverses its transitive type/value dependencies and counts proof-relevant logical
declarations (`theorem`, `definition`, and `opaque`) from two sources: frozen research
modules and author-written output modules. Mathlib/Lean runtime declarations, the
`Stage3Model` scaffold, and pure type/constructor nodes are excluded. The reuse share is
`research / (research + author)`. A failed run with no kernel-valid selected checkpoint has
no authoritative percentage.

| Arm | r1 | r2 | r3 | r4 | r5 | Pooled reuse among valid runs | Mean author root LOC |
|---|---:|---:|---:|---:|---:|---:|---:|
| P | 0.0% | 0.0% | 0.0% | 0.0% | 0.0% | **0.0%** (0 / 585) | 754.4 |
| PML | 13.9% | 15.1% | 12.6% | N/A (failed) | 14.9% | **14.0%** (73 / 520) | 751.5† |
| PML-FileOracle | 14.3% | 14.3% | 14.7% | 12.1% | 13.0% | **13.6%** (94 / 689) | 730.8 |

† PML author LOC is descriptive for all five generated outputs; its reuse denominator uses
only the four kernel-valid proofs. The P arm deliberately has no research library, hence
0% research-library reuse even though it still imports Mathlib. PML and FileOracle both
reuse about 14% of their task-specific logical dependency mass; FileOracle improves
navigation, but it does not mechanically increase the fraction of dependencies supplied by
the research library. Counts come from the controller-preserved `DEPENDENCIES.json` and
`REUSE.json` records for the selected checkpoints.

## Integrity and treatment-fidelity checks

The report generator enforces the following before emitting results:

1. Exactly the 15 declared run IDs are present, five per arm and no duplicates.
2. Both batches agree on model, reasoning effort, budget, context window, Lean toolchain, Codex version, transport, and provider pin.
3. Every run has a terminal author status with exit code 0 and no deadline overshoot.
4. Every routing audit passes, names only OpenAI, has zero unverifiable calls, and agrees with the validation call count.
5. Success agrees with the presence of an independently reverified first-valid checkpoint.
6. No `REVIEW.json` is present; reviewer output is not silently incorporated.
7. Every source validation and routing audit is recorded in the CSV with its SHA-256 digest.

Successful selected checkpoints list only standard permitted axioms (`propext`, `Classical.choice`, and `Quot.sound`). The failed PML r4 final artifact explicitly records `sorryAx` as inadmissible.

## Limitations

- Five runs per arm provide a useful reproducibility/pilot view, not precise success probabilities or a powered treatment comparison.
- Runs are stochastic but not seeded; “replicate” means an independent sampled agent trajectory, not deterministic replay.
- r1-r2 and r3-r5 are temporally separated batches. Protocol equality is checked, but time-varying service behavior cannot be ruled out.
- FileOracle was selected post hoc from a previous successful proof and should not be treated as a prospectively chosen arm.
- Token and cost totals are descriptive workload measures. Larger input counts can reflect longer tool-mediated trajectories rather than worse proof efficiency.
- First-valid time is the controller receipt time of a successful checker event whose exact sources were captured and reverified; it is an observed upper bound, not proof of the earliest moment a valid proof existed.
- Parallel wave execution makes campaign makespan unsuitable for arm comparisons.

## Reproducibility artifacts

The machine-readable aggregate is `reports/s2b_delta_v1/S2B_FIVE_RUN_METRICS.json`; the full row-level table is `reports/s2b_delta_v1/S2B_RUN_LEVEL_RESULTS.csv`. This report can be regenerated with `python3 reports/s2b_delta_v1/generate_report.py`.

- `lean2paper_delta_v1/SOURCE_MANIFEST.json` — 63,921 bytes; SHA-256 `139551762db209fd41d32382d0d9178c3a99be83f2ac63d9c8606d01796f213b`
- `lean2paper_delta_v1_r3r5/SOURCE_MANIFEST.json` — 64,058 bytes; SHA-256 `0f7443d3da0333866d7bee4caff40fc83b9c6c70f9d755fe40618cfaed479ef7`
- `lean2paper_delta_v1.tar.zst` — 2,269,861 bytes; SHA-256 `c6e4e7217357feb32a81711c713de5ea800744fe72280953fdc93342d738b427`
- `lean2paper_delta_v1/result_archives/delta_v1_results_20260920T061059Z.tar.zst` — 15,777,185 bytes; SHA-256 `ee8daa92b48906d86066b8e20625342e45ea93d64ebab005a1fcf309527b8c0b`
- `lean2paper_delta_v1_r3r5/result_archives/delta_v1_r3r5_results_20260920T135951Z.tar.zst` — 19,705,888 bytes; SHA-256 `c098c519c6c786ccb2065ff07938d548f57e93f1dcea58ed5596aa654fa859fc`

The continuation disclosure has SHA-256 `95c7b83876efc79de0351e7752da4de2bbe43915158a0604b5eb23b84cb0d4b0`. The verifier amendment, verifier-recovery, and interactive-acceleration records have SHA-256 `c6180b136263aebb6e3e28413bd308977769cb069d1ef4d50c8bc811faeab74f`, `2c152cb1bb02c7a6855a7097c2f3fa9faf8f55c69e3ef0ad719bc07e4de4069e`, and `8b7314f842bdedce00126b68fada1ff5a0a29aacaf68a9e27642af2e7c4b5a68`, respectively.

## Conclusion

Under the fixed S2B protocol, all three information conditions were highly capable of producing the exact Lean proof: P 5/5, PML 4/5, and PML-FileOracle 5/5. The experiment demonstrates reproducibility across independent agent trajectories but does **not** establish that one arm is superior. The most defensible next step is to evaluate more distinct theorem tasks under the same balanced design rather than infer a strong arm ordering from one task with five repetitions.
