# Mathlib Contribution: Global ODE Existence

## Quick Setup

### 1. Fork and clone Mathlib

```bash
# Fork leanprover-community/mathlib4 on GitHub first, then:
gh repo fork leanprover-community/mathlib4 --clone --remote
cd mathlib4

# Or if you already have a fork:
git clone git@github.com:YOUR_USERNAME/mathlib4.git
cd mathlib4
git remote add upstream https://github.com/leanprover-community/mathlib4.git
```

### 2. Create feature branch

```bash
git checkout -b feat/global-ode-existence
```

### 3. Get Mathlib cache (saves hours of compilation)

```bash
lake exe cache get
```

### 4. Copy the prepared file

```bash
cp /home/zw868/Desktop/mathlib-contrib/Mathlib/Analysis/ODE/GlobalExistence.lean \
   Mathlib/Analysis/ODE/GlobalExistence.lean
```

### 5. Register the file in Mathlib

Add to `Mathlib.lean` (alphabetical order):
```
import Mathlib.Analysis.ODE.GlobalExistence
```

### 6. Build and lint

```bash
# Build just the new file
lake build Mathlib.Analysis.ODE.GlobalExistence

# Run linter
lake build Mathlib.Analysis.ODE.GlobalExistence -- --run-linter

# Full Mathlib build (optional, slow)
lake build
```

### 7. Create PR

```bash
git add Mathlib/Analysis/ODE/GlobalExistence.lean Mathlib.lean
git commit -m "feat(Analysis/ODE): global ODE existence for Lipschitz vector fields"
git push -u origin feat/global-ode-existence
gh pr create --title "feat(Analysis/ODE): global ODE existence for Lipschitz vector fields" \
  --body-file /home/zw868/Desktop/mathlib-contrib/PR_DESCRIPTION.md
```

## Before You Submit Checklist

- [ ] `lake build Mathlib.Analysis.ODE.GlobalExistence` passes
- [ ] `#lint` reports no errors
- [ ] Copyright header has your real name
- [ ] All docstrings are in English
- [ ] No `private` declarations
- [ ] No unused variables (check `linter.unusedSectionVars`)
- [ ] Imports are minimal
- [ ] File is registered in `Mathlib.lean`

## Notes

- The original proof is at `/home/zw868/Desktop/auto-lean/formal-verify/FormalVerify/GlobalODE.lean`
- Lean version: 4.29.0-rc7, Mathlib rev: 81059bbf91da
- The `ContDiff ℝ 1 v` hypothesis from the original has been removed (unused)
- All `private` declarations have been made public
- Naming follows Mathlib conventions (`ODE.exists_solution_of_lipschitzWith`)
