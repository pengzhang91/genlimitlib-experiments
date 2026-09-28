# The question bank: how it was built and what the items look like

> Historical question-development note. The current protocol and aggregation are documented in [METHODS.md](METHODS.md). References below to a fourth authoring/auditing system describe separate workflow roles; the records do not establish that the audit uniformly used a different model family or vendor from all question authors.

## 1. Authoring and audit pipeline

Questions were written by three model families against the printed statements of 16
formalized papers, then audited by a fourth (Codex) that did not author any of them.
Three rounds of audit shaped the bank:

1. **First audit (1,017 items).** Found 248 defective. Three failure modes recurred and
   were written into an authoring rules file: *weaker-but-also-true distractors*
   ("at most t" also means "at most 2t"), *unverified dependency claims* (an item
   asserted Paper 19 reuses Paper 06's noise machinery; they define it separately), and
   *strict versus non-strict* ("fewer" where "a subset, possibly equal" is correct,
   since a singleton class gives equality).
2. **Second audit (1,071 items, 2026-09-19).** 154 WRONG, 2 UNVERIFIABLE. It also raised
   a separate, sharper problem: **350 of 425 Test-2 items (82.4%) were answerable from
   one paper (287) or from the stem alone (63)**. A mathematically correct key does not
   make an item a two-paper test.
3. **Third audit (330 items, batches 3–4).** 278 CORRECT, 52 WRONG. On construct
   validity: **132 of 259 Test-2 items (51.0%) still answerable from one paper or the
   stem** — an improvement on 82.4%, not a solution.

Batch 4 (286 items) was written specifically against the second audit's finding. Two
changes:

* **Stems stopped reciting the definitions they ask about.** 132 stems that stated both
  papers' definitions and then asked the reader to compare them were rewritten to cite
  results *by label only* (`Paper 12 Definition 2.8`), leaving the content to the papers.
* **103 items were built on concrete objects.** Fix a collection, cite two papers by
  label, ask for a tuple of verdicts whose components come from different papers. The
  arithmetic for the five recurring collections was verified independently by the
  auditor, which confirmed all five rows, including three counter-intuitive values:
  `NC₁({ℕ}∪{ℕ∖{n}}) = ∞` (the level-1 closure is *empty*, hence finite, so witnesses
  exist at every size), `NC₁({K_k}) = 1` exactly, and `NC₁({evens,odds}) = 2`.

## 2. What entered this run

| | items |
|---|--:|
| Test 1 (within-paper) | 825 |
| Test 2 (cross-paper) | 368 |
| **total** | **1,193** |

Test 1 spans all 16 papers, unevenly: P02 164 items, P10 12. Test 2 covers the ten
ordered pairs inside the five-paper cluster {P02, P06, P12, P17, P19}:

| edge | items | edge | items |
|---|--:|---|--:|
| P02+P06 | 76 | P02+P12 | 32 |
| P12+P19 | 59 | P02+P19 | 20 |
| P12+P17 | 51 | P06+P12 | 16 |
| P17+P19 | 49 | P02+P17 | 14 |
| P06+P19 | 40 | P06+P17 | 11 |

Batch 4 deliberately added nothing to P02+P06, which previously held 41% of Test 2; it
now holds 21%. The three edges internal to P12/P17/P19 went from 58 items to 159.

Each Test-2 item also carries the auditor's construct classification, which is kept
**separate from answer correctness**: `multiple_source_candidate` 89,
`single_paper` 194, `stem_only` 54, `repository_only` 31.

## 3. Example items

### Test 1, from the subset where the Lean manipulation bites

> **`H-A-P02-14`** (Paper 02)
> Under the bare intersection definition, an inconsistent sample has closure equal to:
> **A. the whole domain.** ✓
> B. the empty set.
> C. the sample itself.
> D. the union of all supports.
> E. the bottom symbol by definition.

The declaration that settles this is

```lean
theorem commonCore_eq_univ_of_empty (H : LanguageClass α) (S : Finset α)
    (h : versionSpace H S = ∅) : commonCore H S = Set.univ
```

It is **absent** from the `LEAN_OLD` block, whose first entries are
`IsClosureWitness` and `ClosureDimensionAtMost` — the declarations that happen to sort
first in Paper 02's module. It is the **first line** of the `LEAN_NEW` block.

### Test 2, composed, classified `multiple_source_candidate`

> **`B4C-04`** (Papers 12 + 17)
> A stream lists every element of an infinite target exactly once and, in addition,
> exactly seven distinct strings that lie outside it, each once. Classify it under
> Paper 12 Definition 2.8 and under Paper 17's o(1)-noise regime of Definition 7.
> **A. It qualifies under both, the seven spurious entries being finite in number.** ✓
> B. It qualifies under Paper 12's only; Paper 17 requires the noise rate to be exactly zero.
> C. It qualifies under Paper 17's only; Paper 12 requires the spurious entries to be absent.
> D. It qualifies under neither; both require the spurious entries to be absent.
> E. It qualifies under Paper 12's only; Paper 17 requires infinitely many spurious entries.

Paper 12 supplies "the set of listed values outside K must be finite"; Paper 17 supplies
"the empirical noise rate must tend to zero". Neither clause appears in the stem, and
neither paper alone settles both halves.

> **`B4B-04`** (Papers 12 + 19)
> Paper 12 Theorem 1.6 and Paper 19 Theorem 2.18 both concern what quantifying over all
> finite noise levels buys. Which notion fails to be captured by taking all finite levels
> together?
> **A. Generation in the limit, where quantifying over all levels is strictly weaker.** ✓

Paper 19 collapses the finite noise hierarchy for *uniform* and *non-uniform* generation;
Paper 12 shows it is strict for generation *in the limit*. Neither paper states the
other's half.

## 4. What the audit rejected, and why it matters

52 of the 330 newest items were rejected. Representative reasons, in the auditor's words:

* `B4H-38` — "P19 Lemma 3.2 has a floor around the square root; the tail class disproves
  the unrounded bound." The key stated the bound without the floor.
* `B4F-37`, `B4G-21` — "P06 non-uniform noise-dependent generation is not P12 non-uniform
  noisy generation; the requested transfer is invalid." Two different notions with
  similar names.
* `B4B-32` — "a literal intersection over an empty family is the universe, not an
  automatically finite set."
* `W2-15` — "Finite NC₁ is the stated criterion, but finiteness at every noise level is
  equivalent by P19 Theorems 3.4–3.5, so the second distractor is also correct."

The last is the recurring failure: a *true* key does not make an item sound if a
distractor is also true.
