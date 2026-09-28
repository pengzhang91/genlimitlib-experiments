# Historical anonymization record

The original review artifact was generated as a fresh snapshot. This record documents that preparation; the public README now identifies the authors. It does not contain the source repository's Git history, remotes, branches, reflogs, or commit identities.

## Transformations

The release process applied the following identity-only transformations:

- personal GitHub handles and repository URLs were replaced with anonymous placeholders;
- direct artifact-author names and institutional contact strings were replaced
  with neutral placeholders;
- local macOS usernames and absolute paths were normalized to `/ANONYMIZED/...`;
- prompt `chars` and `prompt_sha256` fields were recomputed after redaction;
- the archived expected hash for the released question bank was refreshed;
- `bank24.json`, `t1_confirm.jsonl`, and `t2_confirm.jsonl` were stored as
  deterministic gzip so every release file remains below the hosting service's
  8 MB per-file limit; decompression restores the exact released bytes.

The frozen Lean source snapshots were not rewritten. Their historical hashes remain independently checked by the reproduction script.

Public scholarly citations and the names of cited authors embedded in frozen
paper excerpts are retained for scientific fidelity. They are part of the
experimental source material and are not artifact-authorship metadata.

## Excluded material

The following historical material was intentionally left out because it is not used by the final offline reproduction and contains extensive authoring or machine provenance:

- the original repository's `.git` directory and remote metadata;
- original handoff ZIP archives;
- early prompt batches and responses;
- intermediate E22/E23 candidate pools and audit workspaces;
- recovered model-assisted question-authoring records;
- duplicate historical source packages and figures.

The final evaluation bank, all final prompts and answer keys, all final raw responses, the map inputs required by verification, and all Lean sources required by the provenance analysis remain included.

## Interpretation

The released statistical analysis exactly reuses the archived response records. Because identity strings were redacted after inference, this release is not a byte-for-byte copy of the text originally sent to the reader model. No mathematical question, answer option, Lean statement, map relation, score, response, screening decision, or estimator was intentionally changed.

For offline reconstruction, the portable script verifies the released prompt-bank consistency and reproduces the archived numerical results. This describes the earlier review snapshot. The subsequent public export also abbreviates selected paper excerpts; see [PUBLIC_RELEASE.md](../PUBLIC_RELEASE.md). Restoring the review-snapshot excerpt bytes does not recover original unredacted inference requests. Historical anonymity audits apply to the review snapshot.
