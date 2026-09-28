# Other Findings

Five research notes from the language-generation library. The file begins with a table of contents, followed by the five findings, comparison tables, and references. Each finding includes motivation, source papers, precise results, and proofs. The latest mathematical audit corrections are retained.

## Compile

Main file: `other_findings.tex`. Use pdfLaTeX with a recent TeX Live distribution:

```sh
pdflatex -interaction=nonstopmode -halt-on-error other_findings.tex
pdflatex -interaction=nonstopmode -halt-on-error other_findings.tex
pdflatex -interaction=nonstopmode -halt-on-error other_findings.tex
```

Repeated passes resolve the contents, citations, theorem references, and list of tables. All required inputs are included. The bibliography is embedded in `07_references.tex`; no BibTeX or external figures are needed. For Overleaf, upload this ZIP and select `other_findings.tex` as the main document, with pdfLaTeX.

The five sources `01_overlap.tex` through `05_sparse_holes.tex` correspond to Findings 1–5. `06_tables.tex` contains comparison and verification tables; `07_references.tex` contains the references. The text edition follows the same numbering. The audit records distinguish written proofs from archived formalization evidence.
