# Other Findings

Five additional theoretical findings developed from the language-generation library, accompanying the examples in Section 4. Each finding includes its motivation, source papers, precise results, and proofs. The notes begin with a table of contents and conclude with comparison tables and references.

- **Read:** [PDF](other_findings.pdf) · [plain text](other_findings.txt)
- **Edit:** [complete LaTeX ZIP](other_findings_latex.zip) · [main TeX file](latex/other_findings.tex) · [source directory and build instructions](latex/)
- **Review:** [mathematical audit](other_findings_audit.md) · [detailed review records and finite checks](other_findings_audit/)

## Findings

1. **Overlapping representative groups:** a completed-cell characterization, an exact two-block discrepancy formula, and a sharp square-root bound.
2. **Representative mistakes:** the exact logarithmic minimax coefficient, examples, and evaluation complexity.
3. **Metric generation:** a finite-intersection characterization and its connection to properness of the metric completion.
4. **Contrastive ambiguity:** realization of ambiguity complexes, exact list widths, and hypergraph decomposition.
5. **Sparse holes:** dense-target impossibility, vanishing errors, and a randomization advantage under a known sparsity envelope.

The statements specify their own observation and success models. A fresh written mathematical audit found no material error under those assumptions; supplementary finite checks support the review. These additional notes are not claimed to be fully Lean-certified. The existing Section 4 formalizations and their verification records remain documented in the [Section 4 guide](../section4_formalization/manuscript/section4/README.md).

[SHA-256 checksums](SHA256SUMS) identify the published PDF, text, and source ZIP.
