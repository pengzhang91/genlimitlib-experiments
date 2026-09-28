# Canonical-proof reasoning-effort experiment

> Anonymous-release note: concrete Slurm scheduler identifiers were replaced by stable file-local labels; scheduling relationships are preserved.


## Status

This is the living preregistration and final-report target for the canonical-proof
`high` versus `medium` Codex reasoning comparison. The medium cohort is in
progress; result tables remain intentionally empty until independent post-run
Lean verification finishes. The fail-closed post-run aggregator is
`reports/generate_reasoning_medium_report.py`; it currently validates the full
75-run high baseline and refuses to emit medium statistics until all 75 medium
runs have terminal status, routing audit, and independent Lean-validation
artifacts.

## Question and design

The experiment measures the effect of changing only Codex reasoning effort from
`high` to `medium` while retaining the canonical natural-language proof. It uses
five theorem tasks (S2-B and Cases 017, 019, 024, and 025), three information
conditions (`P`, `PML`, and `PML-FileOracle`), and five independent replicates per
task-condition cell. The medium cohort therefore contains 75 author runs.

The primary endpoint is an independently Lean-checked proof of the exact target
within the fixed 5,400-second author budget. Efficiency outcomes are API tokens,
audited OpenRouter cost to first valid proof, total audited API cost, API calls,
and author elapsed time. Wall time is secondary and is compared only for runs on
the same Delta execution environment.

## Frozen invariants

- Model: `openai/gpt-5.6-sol`.
- Provider routing: OpenAI only, fallbacks disabled.
- Model verbosity: `medium` in both cohorts.
- Author budget: 5,400 seconds; Slurm wrapper: 5,700 seconds, with the final 300
  seconds reserved for artifact capture and deterministic validation.
- Canonical proof, exact Lean statement, `Stage3Model.lean`, papers, supplements,
  research/vocabulary trees, author prompt, and validation protocol are
  byte-identical to the corresponding canonical/high source bundle.
- The only scientific setting changed is reasoning effort (`high` to `medium`).
  Fresh cohort/run identifiers, loopback ports, timestamps, and receipt hashes
  are operational metadata.
- Each task retains the established five-wave schedule: the three arms run in
  parallel within a wave, and R2 through R5 depend successively on the preceding
  wave.
- Each Slurm author task requests 1 CPU and 8 GiB. Setup and final validation make
  zero model calls.

## Source audit ledger

| Task | Medium source manifest SHA-256 | Frozen archive SHA-256 | Source-audit SHA-256 | Source gate |
|---|---|---|---|---|
| S2-B | `94e9bce43fda45774153d1bb474e48258b6fb68a66b97c750932ee7a60ad419e` | `84d5dd807353ca5b5120cda4f7c69315d56af33b2a5429b3b3230208fe7ee8f6` | `b156603889c2a6ca114db1df505a7657c4c7f2b2c9f76aab707f6fed01fc3231` | PASS (350 files) |
| Case 017 | `f9c2b2e2a7742035a87f3b9680b970d0b8c11c70402c07e11a94d6d17300c199` | `b896a87cf4276522591dfeb3b56a52fb6cd884e15014eba258caf066cd9eb0d5` | `42de5fa98c28b8db78e28f3892dfafc757f40324c9a186fd0708fafd4d9cd4ef` | PASS (356 files) |
| Case 019 | `e4b6525d9f22dcc2fa27bd8156672165b066c805234d039e4205f34e6bbdbcee` | `fbf53a3c54ec7d53359842622ef26759ba0e6c41494a97c78b31669d4adb2db9` | `558cb18698ec89cdb0fd198955a146abbad0a475b1877f58cf43dc325a66a478` | PASS (405 files) |
| Case 024 | `92e080bb69df8e7f0018aa08717d474c43b55145d97364623984ea53f438bd24` | `5f4421299aebc4b93d57e74ef654c1660db04c8dae9b5730a58ceed63ecd9fbd` | `069e99f2ed8645a2900dd1a5800fe791b644a0725870079b4f27ec713858cdb1` | PASS (357 files) |
| Case 025 | `0c0285f9fa3099a0654e66f2932a0e88abec2f96760914f299c92159e516ec16` | `9fae5dec83adfab1dd0953b6ed00667acb80ff3e70d44f4b2aa6d810f969cce5` | `42feddbfaac44e4f240887d1c74f17f8bcd9ff0b89e9ed42a4df08a2b2b59c64` | PASS (390 files) |

Every archive in the ledger was extracted into a fresh temporary directory and
passed its bundled exact source verifier. The separate source-audit receipt also
checks byte identity against the canonical/high author-visible packet, design,
and author prompt for all three arms.

## Execution ledger

| Task | Setup | R1 | R2 | R3 | R4 | R5 | Final verification |
|---|---|---|---|---|---|---|---|
| S2-B | `SLURM_JOB_008` PASS, 39m34s, 0 calls | `SLURM_JOB_009` | `SLURM_JOB_010` | `SLURM_JOB_011` | `SLURM_JOB_012` | `SLURM_JOB_013` | `SLURM_JOB_014` |
| Case 017 | `SLURM_JOB_015` PASS, 42m08s, 0 calls | `SLURM_JOB_016` | `SLURM_JOB_017` | `SLURM_JOB_018` | `SLURM_JOB_019` | `SLURM_JOB_020` | `SLURM_JOB_021` |
| Case 019 | `SLURM_JOB_001` PASS, 31m58s, 0 calls | `SLURM_JOB_002` | `SLURM_JOB_003` | `SLURM_JOB_004` | `SLURM_JOB_005` | `SLURM_JOB_006` | `SLURM_JOB_007` |
| Case 024 | replacement `SLURM_JOB_032` PASS, 16m26s, 0 calls; setups `SLURM_JOB_022`, `SLURM_JOB_024` censored | `SLURM_JOB_033` | `SLURM_JOB_034` | `SLURM_JOB_035` | `SLURM_JOB_036` | `SLURM_JOB_037` | `SLURM_JOB_038` |
| Case 025 | replacement `SLURM_JOB_025` PASS, 22m31s, 0 calls; setup `SLURM_JOB_023` censored | `SLURM_JOB_026` | `SLURM_JOB_027` | `SLURM_JOB_028` | `SLURM_JOB_029` | `SLURM_JOB_030` | `SLURM_JOB_031` |

All five active setups have completed the strict source gate, frozen-packet gate,
three-arm regression/preflight gate, and zero-model-call audit. The initial Case
024 and Case 025 setup failures occurred before packet preparation or any model
call: their Slurm environments omitted the external Lean sysroot. A second Case
024 attempt was rejected by the strict source gate because the preceding failed
network probe had left a generated receipt in the bundle root. The receipts were
preserved outside the bundles, the frozen manifests were reverified, and the
active replacement chains were submitted with the verified Lean 4.24/mathlib
paths. These attempts are infrastructure-censored setup events, not author runs.
Case 024 and Case 025 then validated and reused the content-addressed 161-module
PML cache, reducing their successful setup times to 16m26s and 22m31s.

## Results

Final post-run aggregation generated at `2026-09-23T20:32:25.968543+00:00` from 75 independently validated medium runs.
The high cohort contains the corresponding 75 canonical-proof runs. No reviewer stage is used.

### Overall comparison

| Reasoning | Lean success | API calls | API cost | Input tokens | Output tokens | Reasoning output¹ | Non-reasoning output¹ | Mean author time |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| High | 62/75 (82.7%) | 4,483 | $130.2957 | 270,032,181 | 2,905,973 | 932,793 | 1,973,180 | 18m 30s |
| Medium | 43/75 (57.3%) | 3,997 | $93.0074 | 232,613,129 | 1,886,695 | 512,204 | 1,374,491 | 19m 01s |

¹ Provider telemetry reports reasoning output as a subset of output tokens. Non-reasoning output is `output_tokens − reasoning_output_tokens`; neither subset is added again to total tokens.

### Task-level high versus medium

| Task | High Lean | Medium Lean | High cost | Medium cost | Cost change | High calls | Medium calls | High mean time | Medium mean time |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| S2-B | 14/15 | 6/15 | $28.3353 | $15.9202 | -43.8% | 1,004 | 683 | 21m 52s | 16m 17s |
| Case 017 | 15/15 | 13/15 | $17.0476 | $20.7329 | +21.6% | 630 | 1,008 | 13m 27s | 27m 01s |
| Case 019 | 8/15 | 0/15 | $45.9802 | $20.0321 | -56.4% | 1,465 | 784 | 28m 26s | 15m 45s |
| Case 024 | 15/15 | 14/15 | $18.2745 | $19.7767 | +8.2% | 671 | 903 | 14m 25s | 23m 00s |
| Case 025 | 10/15 | 10/15 | $20.6581 | $16.5456 | -19.9% | 713 | 619 | 14m 20s | 13m 03s |

### Task × arm comparison

| Task | Arm | High Lean | Medium Lean | High cost | Medium cost | Cost Δ | High input | Medium input | High reasoning | Medium reasoning | High mean time | Medium mean time |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| S2-B | P | 5/5 | 2/5 | $10.4658 | $5.2281 | -50.0% | 21,113,740 | 12,803,384 | 70,605 | 35,829 | 22m 12s | 16m 03s |
| S2-B | PML | 4/5 | 2/5 | $8.2120 | $5.7215 | -30.3% | 16,100,389 | 13,629,253 | 54,254 | 37,739 | 18m 45s | 17m 56s |
| S2-B | PML-FileOracle | 5/5 | 2/5 | $9.6576 | $4.9706 | -48.5% | 21,616,298 | 11,358,507 | 69,243 | 33,147 | 24m 38s | 14m 53s |
| Case 017 | P | 5/5 | 4/5 | $7.4453 | $8.4709 | +13.8% | 17,424,944 | 24,526,964 | 59,216 | 45,034 | 17m 57s | 33m 59s |
| Case 017 | PML | 5/5 | 5/5 | $5.7322 | $5.6291 | -1.8% | 10,693,636 | 14,952,506 | 46,668 | 33,838 | 11m 48s | 19m 29s |
| Case 017 | PML-FileOracle | 5/5 | 4/5 | $3.8701 | $6.6329 | +71.4% | 8,617,167 | 20,745,585 | 39,192 | 37,273 | 10m 38s | 27m 34s |
| Case 019 | P | 0/5 | 0/5 | $6.8074 | $2.1159 | -68.9% | 16,311,569 | 4,444,418 | 81,893 | 20,636 | 20m 15s | 6m 32s |
| Case 019 | PML | 3/5 | 0/5 | $18.7988 | $9.7502 | -48.1% | 36,070,724 | 20,395,409 | 104,788 | 38,756 | 28m 08s | 15m 39s |
| Case 019 | PML-FileOracle | 5/5 | 0/5 | $20.3739 | $8.1661 | -59.9% | 39,188,497 | 23,803,258 | 125,163 | 35,484 | 36m 53s | 25m 03s |
| Case 024 | P | 5/5 | 4/5 | $8.7983 | $10.9752 | +24.7% | 19,263,635 | 29,387,790 | 60,908 | 52,839 | 21m 57s | 34m 05s |
| Case 024 | PML | 5/5 | 5/5 | $4.2787 | $4.8345 | +13.0% | 9,635,474 | 13,247,028 | 28,012 | 24,266 | 9m 38s | 16m 56s |
| Case 024 | PML-FileOracle | 5/5 | 5/5 | $5.1976 | $3.9670 | -23.7% | 12,187,306 | 9,705,401 | 35,821 | 24,037 | 11m 41s | 17m 58s |
| Case 025 | P | 0/5 | 0/5 | $5.7743 | $2.9664 | -48.6% | 12,831,355 | 7,258,400 | 76,044 | 29,414 | 18m 23s | 11m 56s |
| Case 025 | PML | 5/5 | 5/5 | $7.9850 | $6.2446 | -21.8% | 15,220,841 | 11,369,806 | 41,021 | 27,348 | 12m 14s | 11m 56s |
| Case 025 | PML-FileOracle | 5/5 | 5/5 | $6.8988 | $7.3346 | +6.3% | 13,756,606 | 14,985,420 | 39,965 | 36,564 | 12m 24s | 15m 18s |

### Medium token, cost, and time detail

| Task | Cached input | Cache-write input | Output | Reasoning output | Non-reasoning output | Cost to first valid² | Mean first valid² | Total author time³ |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| S2-B | 35,743,742 | 2,001,348 | 367,596 | 106,715 | 260,881 | $9.8917 | 21m 18s | 4h 04m 19s |
| Case 017 | 58,293,091 | 1,863,745 | 427,845 | 116,145 | 311,700 | $14.0253 | 16m 04s | 6h 45m 11s |
| Case 019 | 45,589,424 | 3,001,064 | 330,640 | 94,876 | 235,764 | $0.0000 | — | 3h 56m 09s |
| Case 024 | 50,040,358 | 2,238,912 | 404,942 | 101,142 | 303,800 | $13.5600 | 16m 25s | 5h 44m 57s |
| Case 025 | 30,880,210 | 2,691,974 | 355,672 | 93,326 | 262,346 | $12.5281 | 12m 22s | 3h 15m 50s |

² Defined only for successful runs and measured at the first independently observed valid Lean gate. Full-run cost includes failed runs. ³ Sum across independent author runs, not campaign makespan or queue time.

### Medium library-code reuse

The reuse metric follows the earlier case reports: within the transitive dependency closure of the kernel-checked `stage3_result`, it counts research-tree theorem/definition/opaque declarations over research plus author declarations. It excludes Mathlib/Lean runtime and is not a textual-copy rate.

| Task | Arm | Successful runs | Research declarations | Author declarations | Pooled research share | Mean author root LOC |
|---|---|---:|---:|---:|---:|---:|
| S2-B | P | 2 | 0 | 216 | 0.0% | 769 |
| S2-B | PML | 2 | 46 | 244 | 15.9% | 909 |
| S2-B | PML-FileOracle | 2 | 37 | 265 | 12.3% | 833 |
| Case 017 | P | 4 | 0 | 286 | 0.0% | 661 |
| Case 017 | PML | 5 | 171 | 257 | 40.0% | 554 |
| Case 017 | PML-FileOracle | 4 | 84 | 178 | 32.1% | 560 |
| Case 019 | P | 0 | 0 | 0 | N/A | — |
| Case 019 | PML | 0 | 0 | 0 | N/A | — |
| Case 019 | PML-FileOracle | 0 | 0 | 0 | N/A | — |
| Case 024 | P | 4 | 0 | 319 | 0.0% | 531 |
| Case 024 | PML | 5 | 274 | 271 | 50.3% | 387 |
| Case 024 | PML-FileOracle | 5 | 265 | 252 | 51.3% | 400 |
| Case 025 | P | 0 | 0 | 0 | N/A | — |
| Case 025 | PML | 5 | 1,837 | 167 | 91.7% | 464 |
| Case 025 | PML-FileOracle | 5 | 1,880 | 146 | 92.8% | 472 |

### Interpretation and limitations

- The comparison changes reasoning effort from high to medium while retaining the canonical natural-language proof and all other audited scientific inputs. Sampling remains stochastic, so the five replicates per cell are independent rather than seed-paired.
- Success is the independent exact-target Lean endpoint, not author self-report. A run that writes plausible code but fails the frozen kernel gate is a failure.
- A controller-enforced `TIMEOUT` is retained when the author received the full 5,400-second budget; it is not rerun as infrastructure censoring. It can still succeed if an independently reverified checkpoint was captured within budget. Because SIGKILL prevents Codex from emitting its final cumulative usage event, token totals for such runs are summed from the controller-owned per-call proxy log; normally finished runs require exact agreement between that sum and the Codex cumulative event.
- API cost and token counts are directly comparable under the pinned model/provider protocol. Author wall time is compared only because both cohorts ran on Delta; scheduler queue time is excluded.
- Five runs give 20-percentage-point observed-success resolution per task/arm cell. Wilson intervals are retained in the machine-readable metrics; 5/5 does not imply a true 100% success probability.
- PML-FileOracle is an oracle-ceiling condition, not a realistic retrieval-system estimate. Reuse shares describe successful proof dependency closures and are not causal estimates of assistance quality.

### Reproducible evidence

- `reports/reasoning_medium_v1/REASONING_MEDIUM_RUN_LEVEL_RESULTS.csv`: all 75 medium runs.
- `reports/reasoning_medium_v1/REASONING_HIGH_VS_MEDIUM_METRICS.json`: normalized high/medium aggregates plus run-level hashes.
- `reports/reasoning_medium_v1/REPORT_CHECKSUMS.sha256`: report-artifact checksums.
- `reports/generate_reasoning_medium_report.py`: deterministic post-run aggregator.
- Each medium bundle also contains its independently produced `cohort/DELTA_RESULTS_SUMMARY.json` and timestamped verified result archive.
