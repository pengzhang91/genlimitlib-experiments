# Stage 3 controlled formalization rules

- Treat every supplied input as read-only. Write all source and scratch work
  below `output/`.
- Use only files supplied in this workspace, the paths allowed by
  `SOURCE_CONFIG.md`, and the standard Lean/mathlib environment. Do not access
  files outside these boundaries, prior conversations, or external sources.
- Network, apps, plugins, skills, memories, and subagents are disabled.
- Use `rg` first when searching supplied sources. Consult source materials
  selectively; their volume does not require exhaustive reading.
- Do not redeclare, shadow, replace, or weaken `Stage3Case025.MainClaim` or the
  shared model.
- Certified results may not depend on new axioms, `admit`, `sorry`, `unsafe`,
  `native_decide`, `Lean.ofReduceBool`, custom elaborators, or kernel-bypass
  mechanisms. The standard axioms propext, Classical.choice, and Quot.sound
  are permitted.
- This is a noninteractive 90-minute run. Work autonomously, save checked
  progress, and leave an honest partial result if the exact target is not
  completed.
- Do not alter or fabricate checker output, timing records, or compiler
  artifacts. Do not include private absolute host paths in author output.
