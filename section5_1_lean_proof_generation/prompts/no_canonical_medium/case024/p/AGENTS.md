# Stage 3 experiment controller scope

This directory implements a Lean formalization experiment, not Stage 1
ideation. Stage 1's no-compiler/no-Lean-output rules do not apply here.
Controller preparation may compile the shared specification and run
non-generative sandbox probes. Never build or modify the original research
checkout. Author sessions obey the AGENTS.md copied into their own packet.

Current user instruction: prepare the experiment only; do not launch author
or reviewer model sessions until the user explicitly authorizes execution.
Do not treat a successful preflight as that authorization.

Preserve existing experiments and pilot outputs. Freeze
inputs before launching models; record any pre-launch correction. Never
change the model, theorem, source boundary, or rubric after observing results
without declaring a separate experiment version.
