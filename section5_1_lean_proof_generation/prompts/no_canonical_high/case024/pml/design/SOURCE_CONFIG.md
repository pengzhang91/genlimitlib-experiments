# Allowed sources and compilation

Scientific inputs are limited to the common theorem/specification files and any
additional source material supplied in this workspace. A supplied
`RESEARCH_MODULES.tsv` indexes frozen research modules.

The Lean toolchain and standard dependencies listed by `LEAN_ENV.sh` are
shared read-only infrastructure. Mathlib may be inspected and imported. A
scientific Lean module may be imported only when it is physically supplied in
this packet; missing modules must not be fetched or recovered elsewhere.

Paper maps do not authorize access to an unavailable Lean module.
`ControllerAudit`, `CHECK_DRIVER`, generated checker modules, and
`TargetTemplate` are verification infrastructure, not proof inputs.

Write all work below `output/` and use the supplied checker.
