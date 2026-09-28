# Section 5.2: reproduced results

Generated from frozen response records by `python3 scripts/reproduce_appendix_c.py`.

For each question, correctness is averaged over three evaluation rotations. Questions with the same recorded paper identifiers and source label form a group; a question without a source label forms its own group. Question scores are averaged within each group, then groups receive equal weight. The same questions, rotations, and groups are used in every condition within a study.

## Main results

| Study | Information supplied | Questions | Accuracy (%) |
| --- | --- | ---: | ---: |
| Individual papers | Question only | 404 | 41.20 |
| Individual papers | Paper excerpts | 404 | 70.09 |
| Individual papers | Paper + unrelated Lean | 404 | 71.12 |
| Individual papers | Paper + Lean in file order | 404 | 73.45 |
| Individual papers | Paper + relevant Lean | 404 | 78.55 |
| Five-paper collection | No map | 204 | 60.26 |
| Five-paper collection | Relevant map | 204 | 70.61 |
| Five-paper collection | Sham map | 204 | 60.51 |

## Checks supporting the main-text qualifications

Excluding 15 questions with relevant-Lean signatures outside the source module and Core leaves 389 questions and relevant-Lean accuracy of **78.40%**. This is an exact textual-signature check; it does not establish the absence of mathematically equivalent statements elsewhere.

The category point estimates below support the main-text observation that map gains occur mainly outside questions requiring two papers.

| Category | Questions | No map (%) | Relevant map (%) | Sham map (%) | Map minus sham (pp) |
| --- | ---: | ---: | ---: | ---: | ---: |
| Two-paper | 51 | 60.13 | 59.48 | 58.17 | 1.31 |
| One-paper | 116 | 56.81 | 68.99 | 58.41 | 10.58 |
| Stem-only | 19 | 85.96 | 87.72 | 85.96 | 1.75 |
| Repository | 18 | 55.56 | 94.44 | 53.70 | 40.74 |

## Reproduction checks

- Prompt, answer-key, and response IDs and complete condition/rotation schedules verified.
- Released questions, options, Lean/map blocks, and excerpt locators checked for internal consistency.
- Omitted original excerpt text is not verified in this public-only run; use --private-excerpts for full input verification.
- Screening independently recomputed from raw responses and matched to the retained set.
- Unchanged input/source hashes and all reported point estimates checked against historical records.
- Public derivative input hashes checked against PUBLIC_RELEASE.json; original hashes retained separately.
- Saved responses were not regenerated after review-time redactions or public excerpt omission.

Bank: 825 single-paper and 368 map-study questions.
Source files verified: 573.
Responses with fewer than five recorded option scores: 3; these records are preserved and scored using the archived argmax.

The historical reference inputs retain the original analysis fields. This release reproduces point estimates and does not calculate or report confidence intervals.
