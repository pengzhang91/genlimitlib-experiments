# Targeted Lean checking

The checker uses the frozen environment in `LEAN_ENV.sh`; it does not update
Lake or rebuild the research checkout.

```bash
bash LEAN_CHECK.sh output/Helpers.lean
bash LEAN_CHECK.sh output/Case017Formalization.lean
bash LEAN_CHECK.sh --final
```

Local imports are rebuilt from source. Ordinary file checking can succeed for
a partial file even when the root gate is false; `--final` returns nonzero
unless the exact target and axiom audit pass.

A successful root check emits `STAGE3_GATE`; the controller captures the
corresponding sources and independently rechecks them. Generated controller
modules and `ROOT_GATE` data are checker artifacts. Never import or edit them,
and do not use compiled-only local helper modules.
