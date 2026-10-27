## Summary

This PR adds **global ODE existence** for globally Lipschitz vector fields on Banach spaces,
extending Mathlib's existing local Picard-Lindelöf theory to arbitrary time intervals.

### Main theorem

```lean
theorem ODE.exists_solution_of_lipschitzWith
    (v : E → E) (K : NNReal) (hv_lip : LipschitzWith K v)
    (x₀ : E) (T : ℝ) (hT : 0 < T) :
    ∃ X : ℝ → E, X 0 = x₀ ∧
      ContinuousOn X (Icc 0 T) ∧
      (∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt X (v (X t)) t) ∧
      (∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt X (v (X t)) (Ici t) t)
```

**In words:** Given a globally Lipschitz vector field `v` on a Banach space, for any `T > 0`
and initial condition `x₀`, there exists a solution `X` to `X' = v(X)` on `[0, T]`.

### Motivation

Mathlib currently provides local ODE existence via `IsPicardLindelof` but lacks a global
extension theorem. Global existence for Lipschitz vector fields is a fundamental result in ODE
theory, widely used in:
- Gradient flow analysis (optimization theory)
- Dynamical systems
- Control theory
- Numerical analysis of ODEs

This is the standard textbook result (e.g., Coddington-Levinson) that a globally Lipschitz
right-hand side guarantees a global solution.

### Proof strategy

1. **Local existence** (`ODE.exists_solution_smallInterval`): Construct `IsPicardLindelof`
   with a carefully chosen ball radius to get solutions on `[0, δ]` for `δ < 1/(2K+2)`.
2. **Pasting** (`ODE.paste_solutions`): Concatenate two ODE solutions at a junction point,
   using `Set.piecewise` for continuity and one-sided derivative matching at the junction.
3. **Global existence**: Induction on `n` with `T ≤ (n+1)·δ`, iterating local existence
   and pasting.

### New file

- `Mathlib/Analysis/ODE/GlobalExistence.lean`

### Dependencies

- `Mathlib.Analysis.ODE.PicardLindelof` (existing)
- `Mathlib.Topology.Order.Basic` (existing)

### Related issues / context

This work originated from a formal verification project proving optimization theory results
(PL condition → Quadratic Growth Condition) that required global gradient flow existence as
infrastructure. The full project has 0 sorry across 1387 lines.

---

- [x] depends on: no new dependencies
- [x] modifies: no existing files modified (new file only)
