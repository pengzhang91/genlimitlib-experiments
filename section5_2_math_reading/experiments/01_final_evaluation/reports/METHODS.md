# E24 — methods for the reported mathematical-reading results

The saved evaluation was run on 2026-09-19. This note describes the current point-estimate reconstruction used in Section 5.2 and the shortened Appendix C. Source exclusions are a post hoc sensitivity check; the saved inference inputs and responses have not been rerun.

## Question bank

The historical audit records describe two separate Codex audit passes over model-written five-option questions:

| Audit | Reviewed | Correct | Incorrect | Unverifiable |
| --- | ---: | ---: | ---: | ---: |
| First pass: initial bank and batch 2 | 1,071 | 915 | 154 | 2 |
| Second pass: batches 3 and 4 | 330 | 278 | 52 | 0 |
| Total | 1,401 | 1,193 | 206 | 2 |

The 208 items not judged correct were excluded. The retained bank contains 825 individual-paper questions and 368 map-study questions. Its authoring tags aggregate to 786 Opus, 304 GPT, and 103 Fable items. These are recorded tag families, not independently verified model-version identifiers. Auditing was a separate pass; it was not uniformly performed by a different vendor from the question authors. No human expert validation is documented in these records.

The individual-paper bank covers P01, P02, P03, P04, P05, P06, P08, P09, P10, P12, P17, P19, P23, P28, P31, and P39. The map study uses P02, P06, P12, P17, and P19. The full authoring and rejected-question audit workspaces are not included in the anonymous release.

## Reader and scoring

The documented reader is `Qwen/Qwen3.6-27B`, revision `6a9e13bd6fc8f0983b9b99948120bc37f49c13e9`, in BF16 with vLLM 0.19.0 on one H100 80 GB. The recorded server settings are a 16,384-token context, maximum 16 sequences, and seed 20260919. Thinking is disabled; request settings are temperature 0, top-p 1, one generated token, seed 20260915, and first-token top-20 log probabilities.

The selected answer is the option A–E with the highest recorded first-token log probability. All 10,894 calls completed. Of these, 10,891 contain scores for all five option letters; the other three retain their historical choice from the recorded scores. The reader receives a fixed text packet without tools, a Lean compiler, or conversational memory. Chance accuracy is 20%.

## Evidence conditions

| Individual-paper condition | Supplied evidence |
| --- | --- |
| `CLOSED` | Question only |
| `PAPER` | Relevance-ranked paper excerpts |
| `PAPER_SHAM` | The same excerpts plus unrelated Lean statements |
| `PAPER_LEAN_OLD` | The same excerpts plus Lean statements in source-file order |
| `PAPER_LEAN_NEW` | The same excerpts plus relevant Lean statements |

The Lean blocks target 6,000 characters. Relevant Lean begins with the declaration identified by the question's recorded source information, when available, followed by declarations ranked by token overlap with the question. Thus selection uses recorded source metadata as well as question text. The unrelated block is approximately length matched. The source audit records cases in which the selected declaration lies outside the designated paper module and Core; the current sensitivity result excludes those 15 questions.

| Map-study condition | Supplied evidence |
| --- | --- |
| `CLOSED` | Question only |
| `PAPERS` | Excerpts from the five-paper collection |
| `PAPERS_MAP` | The same excerpts plus `MAP5.txt` |
| `PAPERS_SHAMMAP` | The same excerpts plus `SHAMMAP5.txt` |

The relevant map summarizes theorems and relationships from library imports and dependencies. The sham contains Lean statements from outside the five-paper collection with the same heading and length, not the same relationship structure. Both map blocks are 19,102 characters. Historical character budgets describe the original run; anonymous-release prompt counts were refreshed after identity redaction.

## Screening and evaluation

Every question is first scored without supporting material under two cyclic answer-order rotations (0–1). Questions with mean correctness at most one half are retained: 404 individual-paper questions and 204 map-study questions. Evaluation uses three different rotations (2–4) for all evidence conditions. Each question has the same option-order schedule across conditions, and the five rotations collectively place the correct option in every position once.

| Stage | Individual-paper calls | Map-study calls | Total |
| --- | ---: | ---: | ---: |
| Screening: two rotations, question only | 1,650 | 736 | 2,386 |
| Evaluation: three rotations, all conditions | 6,060 | 2,448 | 8,508 |
| Total | 7,710 | 3,184 | 10,894 |

## Accuracy calculation

For each question, average correctness over its three evaluation rotations. Group questions sharing the same recorded paper identifiers and source label, such as a theorem or definition number; a question with no source label forms its own group. Average question scores within each group, then average groups equally. This limits the extra weight given to repeated questions about the same recorded source result. It is a metadata-based grouping, not a separate semantic audit of paraphrases. The same questions, rotations, and groups are used across evidence conditions.

The 404 individual-paper questions form 372 groups; the 204 map questions form 203 groups. The map-study caveat uses 51 questions labeled `multiple_source_candidate` by the auditor. The source-exclusion sensitivity removes 15 individual-paper questions whose selected evidence falls outside the designated source module and Core, leaving 389 questions and 357 groups; relevant Lean accuracy is 78.40%. The classification and exclusions remain documented in the retained bank and reconstruction records.

The current portable analysis reports point estimates without confidence intervals. Historical analyses and their interval fields remain archived for integrity checks and are not the current reporting interface.

## Reproduction and provenance

From the release root, run `python3 scripts/reproduce_appendix_c.py`. The filename is retained for compatibility. It verifies released prompt contents and hashes, raw records, screening decisions, frozen source hashes, and historical point estimates, then writes `results/section5_2_results.md`, `results/section5_2_results.json`, and `results/recount.json`.

The three scripts in this directory's sibling `scripts/` folder are historical authoring/analysis records. In particular, `build_bank.py` depends on earlier workspaces excluded from this release, and `analyze.py` implements older supplemental analyses. Use the root-level portable command for the current results.

Identity strings were redacted after inference; released prompts are not byte-identical to the original model inputs. See [runtime and provenance notes](../../../docs/RUNTIME_AND_PROVENANCE.md), and [licensing notes](../../../LICENSES.md).
