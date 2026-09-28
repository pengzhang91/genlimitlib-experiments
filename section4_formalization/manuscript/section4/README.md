# Section 4 and Appendix A proof sources

`proofs.tex` compiles the Section 4 findings and their complete written proofs as a standalone document. The numbering retains Section 4 and Appendix A, with the research workflow first.

```sh
cd manuscript/section4
latexmk -pdf -interaction=nonstopmode -halt-on-error proofs.tex
```

Files `results_connections.tex` and `results_math.tex` contain Sections 4.1–4.3. `appendix_proof_guide.tex` contains the verification guide and the proof repair; `appendix_replay.tex` contains the replay proofs; `appendix_p29_frontier.tex` contains the staircase proof. The four primary citations are in `section4-references.bib`.

The accompanying [Lean map](../../registry/section4/README.md) identifies exact theorem names, indexing conventions, assumptions, and verification commands.

These files contain the Section 4 revision used for this artifact. Private manuscript-synchronization records and unrelated sections of the collaborative manuscript are intentionally excluded from the public release.

## Other Findings

The separate [Other Findings](../../../section4_other_findings/) module collects five additional theoretical results with motivations, source papers, statements, and proofs. Read the [PDF](../../../section4_other_findings/other_findings.pdf) or [text edition](../../../section4_other_findings/other_findings.txt), or download the [complete LaTeX source](../../../section4_other_findings/other_findings_latex.zip). Its [mathematical audit](../../../section4_other_findings/other_findings_audit.md) records the review scope; these written findings are not claimed to be fully Lean-certified.
