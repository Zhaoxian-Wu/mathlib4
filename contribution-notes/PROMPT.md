# Prompt: Submit Global ODE Existence PR to Mathlib

## Context

A cleaned-up Lean 4 file is ready at:
- `Mathlib/Analysis/ODE/GlobalExistence.lean` (in this folder)
- PR description at `PR_DESCRIPTION.md`
- Setup guide at `SETUP.md`

The file **builds with 0 warnings, 0 errors** against Mathlib rev `81059bbf91da` (Lean 4.29.0-rc7). It proves global ODE existence for Lipschitz vector fields on Banach spaces — a gap in current Mathlib.

Original project (for reference only): `/home/zw868/Desktop/auto-lean/formal-verify/`

## Task

### 1. Clone Mathlib and set up environment

```bash
cd /home/zw868/Desktop/mathlib-contrib
git clone https://github.com/leanprover-community/mathlib4.git mathlib4
cd mathlib4
```

- Run `lake exe cache get` to download prebuilt oleans (critical — compiling from scratch takes hours)
- Verify `lake build` works on vanilla Mathlib before making changes

### 2. Create feature branch

```bash
git checkout -b feat/global-ode-existence
```

### 3. Install the prepared file

- Copy `../Mathlib/Analysis/ODE/GlobalExistence.lean` → `Mathlib/Analysis/ODE/GlobalExistence.lean`
- Add `import Mathlib.Analysis.ODE.GlobalExistence` to `Mathlib.lean` in alphabetical order (after `Mathlib.Analysis.ODE.Gronwall` or similar)

### 4. Build and lint

```bash
# Build just the new file first
lake build Mathlib.Analysis.ODE.GlobalExistence

# Check for linter warnings
lake build Mathlib.Analysis.ODE.GlobalExistence 2>&1 | grep -E "warning|error"
```

**If Mathlib master has moved** since rev `81059bbf91da`, the file may need adjustments:
- API renames: grep for the old name in Mathlib's git log and update
- `IsPicardLindelof` interface changes: check `Mathlib/Analysis/ODE/PicardLindelof.lean`
- `simp` lemma changes: if `simp only [...]` fails, try `simp?` to discover new lemma names
- Import path changes: verify `Mathlib.Analysis.ODE.PicardLindelof` and `Mathlib.Topology.Order.Basic` still exist

### 5. Fix any issues

Common Mathlib linter issues to watch for:
- `unusedSectionVars` → add `omit [...] in` before the theorem
- `unusedSimpArgs` → remove the flagged argument from `simp only`
- `docBlame` → every public `theorem`/`def`/`lemma` needs a `/-- ... -/` docstring
- `simpNF` → `simp` lemmas must be in normal form
- Style: line length ≤ 100 chars, no trailing whitespace

### 6. Commit and push

```bash
git add Mathlib/Analysis/ODE/GlobalExistence.lean Mathlib.lean
git commit -m "feat(Analysis/ODE): global ODE existence for Lipschitz vector fields

Prove that globally Lipschitz vector fields on Banach spaces have
solutions on arbitrary time intervals [0, T], extending the local
Picard-Lindelöf theory already in Mathlib."
git push -u origin feat/global-ode-existence
```

### 7. Create PR

Use the PR description from `../PR_DESCRIPTION.md`. Title:

```
feat(Analysis/ODE): global ODE existence for Lipschitz vector fields
```

```bash
gh pr create \
  --repo leanprover-community/mathlib4 \
  --title "feat(Analysis/ODE): global ODE existence for Lipschitz vector fields" \
  --body-file ../PR_DESCRIPTION.md
```

### 8. Post-submission

- Mathlib CI will run — watch for failures
- A maintainer will be auto-assigned; respond to review comments
- Common review requests:
  - **Generalize**: e.g., replace `ℝ` with a general ordered field where possible
  - **Split lemmas**: if a proof is too long, extract intermediate steps
  - **Naming**: Mathlib has strict naming conventions — maintainers may suggest renames
  - **Style**: 100-char line limit, specific `where` vs `by` preferences

## File structure of the PR

```
Mathlib/Analysis/ODE/GlobalExistence.lean   ← NEW file
Mathlib.lean                                 ← add import line
```

## Theorem inventory in GlobalExistence.lean

| Name | Type | Description |
|------|------|-------------|
| `ODE.hasDerivAt_of_hasDerivWithinAt_Iic_Ici` | lemma | Paste left/right one-sided derivatives |
| `ODE.piecewise_eventuallyEq_left` | lemma | Piecewise agrees with f₁ near t < a |
| `ODE.piecewise_eventuallyEq_right` | lemma | Piecewise agrees with f₂ near t > a |
| `ODE.HasDerivAt.comp_sub` | lemma | Chain rule for time shift |
| `ODE.exists_solution_local` | theorem | Local ODE existence (any ε) |
| `ODE.exists_solution_smallInterval` | theorem | ODE on [0,T] for small T |
| `ODE.paste_solutions` | theorem | Concatenate two ODE solutions |
| `ODE.exists_solution_aux` | theorem | Inductive step for global existence |
| `ODE.exists_solution_of_lipschitzWith` | theorem | **Main result**: global ODE existence |

## Potential reviewer concerns and responses

1. **"Does this duplicate existing Mathlib results?"**
   - No. Mathlib has `IsPicardLindelof` for local existence only. There is no global extension.

2. **"Why not use `ContDiff` instead of `LipschitzWith`?"**
   - `LipschitzWith` is the minimal hypothesis. `ContDiff ℝ 1` implies local Lipschitz but not global. The original proof had `ContDiff ℝ 1` as an unused hypothesis — it was removed.

3. **"Should the helper lemmas be in separate files?"**
   - `hasDerivAt_of_hasDerivWithinAt_Iic_Ici` could go in `Mathlib.Analysis.Calculus.Deriv.Basic`. The piecewise lemmas could go in `Mathlib.Order.Filter.EventuallyEq`. Happy to split if maintainers prefer.

4. **"Can this be generalized beyond `ℝ`?"**
   - The time parameter is intrinsically `ℝ` for ODE theory (ordered field + completeness). The space `E` is already a general Banach space.
