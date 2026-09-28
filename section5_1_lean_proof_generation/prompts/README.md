# Experiment-controlled prompts

This directory preserves all experiment-controlled prompt material used by the
formal author runs. There are 60 prompt sets: 5 tasks x 4 conditions x 3 arms.
Each set is stored once because R1-R5 used byte-identical prompt-facing files;
`PROMPT_MANIFEST.json` maps all 300 formal run IDs to the corresponding set and
records the original source hashes and source bundle.

The preserved material includes `AUTHOR_PROMPT.txt`, author-scope and design-
scope `AGENTS.md`, task/design Markdown and Lean files, the canonical proof when
present, reviewer prompt files retained for protocol provenance, per-batch
campaign/arm/freeze/packet configuration, and representative prompt assembly
code. Absolute private host paths in copied configuration receipts are replaced
with symbolic placeholders; both original and exported hashes are recorded in
`SOURCE_INVENTORY.json`.

OpenAI/Codex service-internal system prompts are not observable experiment
assets and therefore cannot be exported. The repository records every prompt,
instruction, input file, model setting, reasoning level, provider restriction,
and time budget controlled by this experiment.
