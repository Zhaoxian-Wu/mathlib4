# Local contribution backup

Backup date: 2026-10-27 (America/New_York).

The active proof is `Mathlib/Analysis/ODE/GlobalExistence.lean` at the repository root. `original-source/` preserves the older prepared copy from the parent `mathlib-contrib` directory. `PROMPT.md`, `SETUP.md`, and `PR_DESCRIPTION.md` are historical preparation documents, preserved unchanged; their commands and claims are not a record of an upstream submission.

## Verified state

- Base mathlib commit: `0c43cd0269ce3f929ed08e196f515ed0dc0133ae`.
- Lean toolchain: `leanprover/lean4:v4.29.0-rc8`.
- `lake build Mathlib.Analysis.ODE.GlobalExistence` succeeded.
- A direct `lake env lean Mathlib/Analysis/ODE/GlobalExistence.lean` check succeeded without warnings or errors.
- The active proof contains no `sorry`, `admit`, or added axiom declarations.
- The source author/copyright header still contains `[Your Name]` placeholders. This backup does not claim upstream contribution readiness or validate against current upstream master.

## Rebuild after cache cleanup

Keep `lean-toolchain` and `lake-manifest.json` unchanged to reproduce this baseline. From the repository root, run:

```bash
lake exe cache get
lake build Mathlib.Analysis.ODE.GlobalExistence
```

The ignored `.lake/` directory contains generated build outputs and pinned dependencies and can be regenerated. Local `.claude/settings.local.json` remains outside this Git repository and is not uploaded.
