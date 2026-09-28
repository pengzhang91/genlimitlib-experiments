# Run-level data dictionary

`RUN_LEVEL_RESULTS_300.csv` has one row for every task x condition x arm x
replicate. `lean_success` is the independent Lean gate result. Reasoning output
tokens are a subset of output tokens and must not be added to output tokens.
`api_cost_usd` is upstream model API cost only; it excludes Delta CPU and
storage. Reuse fields are populated only when dependency evidence was available
for a successful proof; blank is not equivalent to zero.
