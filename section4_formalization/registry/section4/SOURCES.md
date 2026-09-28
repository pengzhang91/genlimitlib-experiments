# Source papers and versions

- **P13:** Moses Charikar and Chirag Pabbaraju, *Pareto-optimal Non-uniform Language Generation*, ALT 2026. [Published paper](https://proceedings.mlr.press/v313/charikar26a.html), [PDF](https://proceedings.mlr.press/v313/charikar26a/charikar26a.pdf). Procedure 1, Claim 7, Theorem 8. Existing Lean declarations retain earlier arXiv numbering.
- **P22:** Giorgio Racca, Michal Valko, and Amartya Sanyal, *Language Generation with Replay: A Learning-Theoretic View of Model Collapse*, [arXiv v2](https://arxiv.org/html/2603.11784v2). Definition 3.5 and Theorem 7.3.
- **P31:** Jon Kleinberg, Anay Mehrotra, Amin Saberi, and Grigoris Velegkas, *On Language Generation in the Limit with Bounded Memory*, [arXiv v1](https://arxiv.org/html/2605.30324v1). Definition 13 and Appendix Proposition A.2. The transferred example concerns incremental index-based generation.
- **P29:** Jon Kleinberg, Charlotte Peale, and Omer Reingold, *Mistake-Bounded Language Generation*, [arXiv v1](https://arxiv.org/html/2605.10809v1). Remark 1, Theorem 6.4, and Section 8, Open Direction (2).

“Staircase family” is the manuscript's name for the generalized block construction; it is not terminology attributed to P29. The theorem resolves the tradeoff question for that family with arbitrary positive finite block sizes, not for arbitrary language families.

## Repository provenance

- The bundled Lean dependency snapshot is distributed under the included
  Apache-2.0 license. Author-identifying repository coordinates and revision
  identifiers are withheld during double-blind review and will be restored in
  the archival release.
- Lean: `leanprover/lean4:v4.24.0`.
- Mathlib: `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` (v4.24.0); all transitive pins remain in `GenLimitLean/lake-manifest.json`.
- The replay proof is compiled directly from the sources in this module; no
  external saved certificate is required.

The original manuscripts used to develop the written arguments are historical material. The maintained statements and proofs for this artifact are the TeX files in `manuscript/section4/` and the mapped Lean endpoints.
