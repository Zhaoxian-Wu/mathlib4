/-
Copyright (c) 2025 [Your Name]. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Topology.Order.Basic

/-!
# Global ODE Existence for Lipschitz Vector Fields

This file proves the global existence of ODE solutions for globally Lipschitz vector fields
on Banach spaces. Mathlib's existing `IsPicardLindelof` theory provides *local* solutions;
this file extends them to arbitrary time intervals `[0, T]` by iterating the local theorem
and pasting solutions together.

## Main results

* `ODE.exists_solution_of_lipschitzWith`: Given a globally Lipschitz vector field `v : E → E`
  with constant `K`, for any initial condition `x₀` and time horizon `T > 0`, there exists
  a solution `X : ℝ → E` to `X' = v ∘ X` on `[0, T]` with `X 0 = x₀`.

## Strategy

1. **Local existence** (`ODE.exists_solution_smallInterval`): Use `IsPicardLindelof` to get
   a solution on `[0, δ]` for `δ < 1/(2K+2)`.
2. **Pasting** (`ODE.paste_solutions`): Given solutions on `[0, a]` and `[0, b]` with matching
   endpoint, produce a solution on `[0, a + b]`.
3. **Global existence** (`ODE.exists_solution_of_lipschitzWith`): By induction on
   `n` with `T ≤ (n+1)·δ`, iterate local existence and pasting.

## References

* [Coddington, Levinson, *Theory of Ordinary Differential Equations*]
* Mathlib's `Mathlib.Analysis.ODE.PicardLindelof`

## Tags

ODE, ordinary differential equation, global existence, Lipschitz, Picard-Lindelöf
-/

open Set Metric Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace ODE

/-! ### Building blocks for pasting ODE solutions -/

section PastingLemmas

/-- Combine left and right one-sided derivatives into a full derivative at a point.
If `f` has derivative `f'` within `Iic a` and within `Ici a` at `a`,
then `f` has derivative `f'` at `a`. -/
theorem hasDerivAt_of_hasDerivWithinAt_Iic_Ici {f : ℝ → E} {f' : E} {a : ℝ}
    (hl : HasDerivWithinAt f f' (Iic a) a)
    (hr : HasDerivWithinAt f f' (Ici a) a) :
    HasDerivAt f f' a := by
  have h := hl.union hr
  rw [show Iic a ∪ Ici a = (univ : Set ℝ) from Iic_union_Ici] at h
  exact hasDerivWithinAt_univ.mp h

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- A piecewise function `if s ≤ a then f₁ s else f₂ s` agrees with `f₁` in a
neighborhood of any `t < a`. -/
theorem piecewise_eventuallyEq_left {f₁ f₂ : ℝ → E} {a t : ℝ} (ht : t < a) :
    (fun s => if s ≤ a then f₁ s else f₂ s) =ᶠ[nhds t] f₁ := by
  filter_upwards [Iio_mem_nhds ht] with s hs
  simp [le_of_lt (mem_Iio.mp hs)]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- A piecewise function `if s ≤ a then f₁ s else f₂ s` agrees with `f₂` in a
neighborhood of any `t > a`. -/
theorem piecewise_eventuallyEq_right {f₁ f₂ : ℝ → E} {a t : ℝ} (ht : a < t) :
    (fun s => if s ≤ a then f₁ s else f₂ s) =ᶠ[nhds t] f₂ := by
  filter_upwards [Ioi_mem_nhds ht] with s hs
  simp [not_le.mpr (mem_Ioi.mp hs)]

/-- Chain rule for a time-shifted function:
if `g` has derivative `g'` at `t - c`, then `s ↦ g (s - c)` has derivative `g'` at `t`. -/
theorem HasDerivAt.comp_sub {g : ℝ → E} {g' : E} {t c : ℝ}
    (hg : HasDerivAt g g' (t - c)) :
    HasDerivAt (fun s => g (s - c)) g' t := by
  simpa using hg.scomp t ((hasDerivAt_id t).sub_const c)

end PastingLemmas

/-! ### Local ODE existence via Picard-Lindelöf -/

section LocalExistence

variable [CompleteSpace E]

/-- **Local ODE existence** for globally Lipschitz vector fields.
Given a globally Lipschitz vector field `v` with constant `K` and initial value `x₀`,
there exists `ε > 0` and a solution `X` on `[0, ε]` satisfying `X 0 = x₀` and `X' = v ∘ X`. -/
theorem exists_solution_local (v : E → E) (K : NNReal) (hv_lip : LipschitzWith K v) (x₀ : E) :
    ∃ ε > (0 : ℝ), ∃ X : ℝ → E, X 0 = x₀ ∧
      (∀ t ∈ Ioo (0 : ℝ) ε, HasDerivAt X (v (X t)) t) ∧
      ContinuousOn X (Icc 0 ε) ∧
      (∀ t ∈ Icc (0 : ℝ) ε, HasDerivWithinAt X (v (X t)) (Icc 0 ε) t) := by
  set G := ‖v x₀‖ + 1
  set a_val := G / (↑K + 1) + 1
  have ha_pos : (0 : ℝ) < a_val := by positivity
  set M_val := ↑K * a_val + G
  have hM_pos : (0 : ℝ) < M_val := by positivity
  set ε := a_val / (2 * M_val)
  have hε_pos : (0 : ℝ) < ε := by positivity
  have hPL : IsPicardLindelof (fun (_ : ℝ) => v) (tmin := 0) (tmax := ε)
      ⟨(0 : ℝ), le_refl 0, le_of_lt hε_pos⟩ x₀
      ⟨a_val, le_of_lt ha_pos⟩ 0 ⟨M_val, le_of_lt hM_pos⟩ K :=
    { lipschitzOnWith := fun _ _ => hv_lip.lipschitzOnWith
      continuousOn := fun _ _ => continuousOn_const
      norm_le := by
        intro t _ x hx
        have hxa : ‖x - x₀‖ ≤ a_val := by rwa [← dist_eq_norm, ← mem_closedBall]
        calc ‖v x‖ = ‖v x - v x₀ + v x₀‖ := by congr 1; abel
          _ ≤ ‖v x - v x₀‖ + ‖v x₀‖ := norm_add_le _ _
          _ ≤ ↑K * ‖x - x₀‖ + ‖v x₀‖ := by
            gcongr
            calc ‖v x - v x₀‖ = dist (v x) (v x₀) := (dist_eq_norm _ _).symm
              _ ≤ ↑K * dist x x₀ := hv_lip.dist_le_mul x x₀
              _ = ↑K * ‖x - x₀‖ := by rw [dist_eq_norm]
          _ ≤ ↑K * a_val + ‖v x₀‖ := by gcongr
          _ ≤ M_val := by simp only [M_val, G]; linarith
      mul_max_le := by
        simp only [tsub_zero, NNReal.coe_mk, NNReal.coe_zero]
        rw [max_eq_left (le_of_lt hε_pos)]
        calc M_val * ε = M_val * (a_val / (2 * M_val)) := rfl
          _ = a_val / 2 := by field_simp
          _ ≤ a_val := by linarith }
  obtain ⟨α, hα0, hα_deriv⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨ε, hε_pos, α, by exact_mod_cast hα0,
    fun t ht => (hα_deriv t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2),
    fun t ht => (hα_deriv t ht).continuousWithinAt,
    hα_deriv⟩

/-- **ODE existence on `[0, T]`** for `T < 1/(2K+2)`, via a single application of
Picard-Lindelöf with a carefully chosen ball radius. -/
theorem exists_solution_smallInterval
    (v : E → E) (K : NNReal) (hv_lip : LipschitzWith K v) (x₀ : E)
    (T : ℝ) (hT : 0 < T) (hT_small : T < 1 / (2 * ↑K + 2)) :
    ∃ X : ℝ → E, X 0 = x₀ ∧
      ContinuousOn X (Icc 0 T) ∧
      (∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt X (v (X t)) t) ∧
      (∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt X (v (X t)) (Icc 0 T) t) := by
  have hK_nn := K.coe_nonneg
  set G := ‖v x₀‖ + 1
  have hK1_pos : (0 : ℝ) < ↑K + 1 := by linarith
  have hKT : (↑K + 1) * T < 1 := by
    calc (↑K + 1) * T < (↑K + 1) * (1 / (2 * (↑K + 1))) := by
            apply mul_lt_mul_of_pos_left _ hK1_pos
            convert hT_small using 1; ring
        _ = 1 / 2 := by field_simp
        _ < 1 := by norm_num
  have h_denom : 0 < 1 - (↑K + 1) * T := by linarith
  set a_val := G * T / (1 - (↑K + 1) * T) + G
  have ha_pos : (0 : ℝ) < a_val := by positivity
  set M_val := (↑K + 1) * a_val
  have hM_pos : (0 : ℝ) < M_val := by positivity
  have h_constraint : M_val * T ≤ a_val := by
    simp only [M_val, a_val]
    have h_rw : (↑K + 1) * (G * T / (1 - (↑K + 1) * T) + G) * T
         = (↑K + 1) * T * (G * T / (1 - (↑K + 1) * T) + G) := by ring
    rw [h_rw]
    have hKT_le : (↑K + 1) * T ≤ 1 := le_of_lt hKT
    calc (↑K + 1) * T * (G * T / (1 - (↑K + 1) * T) + G)
        ≤ 1 * (G * T / (1 - (↑K + 1) * T) + G) := by gcongr
      _ = G * T / (1 - (↑K + 1) * T) + G := one_mul _
  have hPL : IsPicardLindelof (fun (_ : ℝ) => v) (tmin := 0) (tmax := T)
      ⟨(0 : ℝ), le_refl 0, le_of_lt hT⟩ x₀
      ⟨a_val, le_of_lt ha_pos⟩ 0 ⟨M_val, le_of_lt hM_pos⟩ K :=
    { lipschitzOnWith := fun _ _ => hv_lip.lipschitzOnWith
      continuousOn := fun _ _ => continuousOn_const
      norm_le := by
        intro t _ x hx
        have hxa : ‖x - x₀‖ ≤ a_val := by rwa [← dist_eq_norm, ← mem_closedBall]
        calc ‖v x‖ = ‖v x - v x₀ + v x₀‖ := by congr 1; abel
          _ ≤ ‖v x - v x₀‖ + ‖v x₀‖ := norm_add_le _ _
          _ ≤ ↑K * ‖x - x₀‖ + ‖v x₀‖ := by
            gcongr
            calc ‖v x - v x₀‖ = dist (v x) (v x₀) := (dist_eq_norm _ _).symm
              _ ≤ ↑K * dist x x₀ := hv_lip.dist_le_mul x x₀
              _ = ↑K * ‖x - x₀‖ := by rw [dist_eq_norm]
          _ ≤ ↑K * a_val + ‖v x₀‖ := by gcongr
          _ ≤ ↑K * a_val + G := by linarith [show G = ‖v x₀‖ + 1 from rfl]
          _ ≤ (↑K + 1) * a_val := by
            nlinarith [show a_val ≥ G from le_add_of_nonneg_left (by positivity)]
      mul_max_le := by
        simp only [tsub_zero, NNReal.coe_mk, NNReal.coe_zero]
        rw [max_eq_left (le_of_lt hT)]
        exact_mod_cast h_constraint }
  obtain ⟨α, hα0, hα_deriv⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, by exact_mod_cast hα0,
    fun t ht => (hα_deriv t ht).continuousWithinAt,
    fun t ht => (hα_deriv t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2),
    fun t ht => hα_deriv t ht⟩

end LocalExistence

/-! ### Pasting ODE solutions -/

section Pasting

/-- **Paste two ODE solutions** at a junction point.
Given a solution `X₁` on `[0, a]` and a solution `X₂` on `[0, b]` with `X₂ 0 = X₁ a`,
produces a solution on `[0, a + b]` by defining
`X t = if t ≤ a then X₁ t else X₂ (t - a)`. -/
theorem paste_solutions {v : E → E} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {X₁ X₂ : ℝ → E}
    (hX₁_cont : ContinuousOn X₁ (Icc 0 a))
    (hX₁_deriv : ∀ t ∈ Ioo (0 : ℝ) a, HasDerivAt X₁ (v (X₁ t)) t)
    (hX₁_within : ∀ t ∈ Icc (0 : ℝ) a, HasDerivWithinAt X₁ (v (X₁ t)) (Icc 0 a) t)
    (hX₂_cont : ContinuousOn X₂ (Icc 0 b))
    (hX₂_deriv : ∀ t ∈ Ioo (0 : ℝ) b, HasDerivAt X₂ (v (X₂ t)) t)
    (hX₂_within : ∀ t ∈ Icc (0 : ℝ) b, HasDerivWithinAt X₂ (v (X₂ t)) (Icc 0 b) t)
    (hglue : X₂ 0 = X₁ a) :
    ∃ X : ℝ → E, X 0 = X₁ 0 ∧
      ContinuousOn X (Icc 0 (a + b)) ∧
      (∀ t ∈ Ioo (0 : ℝ) (a + b), HasDerivAt X (v (X t)) t) ∧
      (∀ t ∈ Icc (0 : ℝ) (a + b), HasDerivWithinAt X (v (X t)) (Icc 0 (a + b)) t) := by
  set X := fun t => if t ≤ a then X₁ t else X₂ (t - a) with hX_def
  have hX_hasDerivAt : ∀ t ∈ Ioo (0 : ℝ) (a + b), HasDerivAt X (v (X t)) t := by
    intro t ht
    rcases lt_trichotomy t a with htl | hte | htr
    · have heq : X =ᶠ[nhds t] X₁ := by
        filter_upwards [Iio_mem_nhds htl] with s hs
        exact if_pos (le_of_lt (mem_Iio.mp hs))
      rw [show X t = X₁ t from if_pos (le_of_lt htl)]
      exact heq.hasDerivAt_iff.mpr (hX₁_deriv t ⟨ht.1, htl⟩)
    · rw [show X t = X₁ a from by rw [hte]; exact if_pos le_rfl]
      have hleft : HasDerivWithinAt X (v (X₁ a)) (Iic a) a := by
        have h := (hX₁_within a (right_mem_Icc.mpr (le_of_lt ha))).mono_of_mem_nhdsWithin
          (mem_nhdsWithin.mpr ⟨Ioi 0, isOpen_Ioi, mem_Ioi.mpr ha,
            fun _ ⟨h1, h2⟩ => ⟨le_of_lt (mem_Ioi.mp h1), mem_Iic.mp h2⟩⟩)
        exact h.congr (fun s hs => if_pos (mem_Iic.mp hs)) (if_pos le_rfl)
      have hright : HasDerivWithinAt X (v (X₁ a)) (Ici a) a := by
        have h0 := hX₂_within 0 (left_mem_Icc.mpr (le_of_lt hb))
        rw [hglue] at h0
        have h1 : HasDerivWithinAt X₂ (v (X₁ a)) (Ici (0 : ℝ)) 0 :=
          h0.mono_of_mem_nhdsWithin (mem_nhdsWithin.mpr
            ⟨Iio b, isOpen_Iio, mem_Iio.mpr hb,
              fun s ⟨hs1, hs2⟩ => ⟨mem_Ici.mp hs2, le_of_lt (mem_Iio.mp hs1)⟩⟩)
        have h1' : HasDerivWithinAt X₂ (v (X₁ a)) (Ici (0 : ℝ)) (a - a) := by rwa [sub_self]
        have hda : HasDerivWithinAt (fun s => s - a) (1 : ℝ) (Ici a) a :=
          ((hasDerivAt_id a).sub_const a).hasDerivWithinAt
        have hmaps : MapsTo (fun s => s - a) (Ici a) (Ici (0 : ℝ)) := fun s hs =>
          mem_Ici.mpr (by linarith [mem_Ici.mp hs])
        have h2 : HasDerivWithinAt (fun s => X₂ (s - a)) (v (X₁ a)) (Ici a) a := by
          have := HasDerivWithinAt.scomp (h := fun s => s - a) a h1' hda hmaps
          simpa using this
        exact h2.congr (fun s hs => by
          by_cases hle : s ≤ a
          · simp [X, le_antisymm hle (mem_Ici.mp hs), sub_self, hglue]
          · simp [X, hle]) (by simp [X, sub_self, hglue])
      rw [hte]; exact hasDerivAt_of_hasDerivWithinAt_Iic_Ici hleft hright
    · have heq : X =ᶠ[nhds t] (fun s => X₂ (s - a)) := by
        filter_upwards [Ioi_mem_nhds htr] with s hs
        exact if_neg (not_le.mpr (mem_Ioi.mp hs))
      rw [show X t = X₂ (t - a) from if_neg (not_le.mpr htr)]
      have hta : t - a ∈ Ioo (0 : ℝ) b := ⟨by linarith, by linarith [ht.2]⟩
      exact heq.hasDerivAt_iff.mpr
        (by simpa using (hX₂_deriv (t - a) hta).scomp t ((hasDerivAt_id t).sub_const a))
  refine ⟨X, by simp [X, le_of_lt ha], ?_, hX_hasDerivAt, ?_⟩
  · -- ContinuousOn: piecewise via Set.piecewise + frontier agreement
    have hX_eq : X = (Iic a).piecewise X₁ (fun t => X₂ (t - a)) := by
      ext t; simp [X, Set.piecewise]
    rw [hX_eq]
    apply ContinuousOn.piecewise
    · intro x hx; rw [frontier_Iic] at hx
      rw [hx.2, sub_self, hglue]
    · rw [closure_Iic, show Icc 0 (a + b) ∩ Iic a = Icc 0 a from by
        ext x; simp only [mem_inter_iff, mem_Icc, mem_Iic]
        exact ⟨fun ⟨⟨h1, _⟩, h3⟩ => ⟨h1, h3⟩,
               fun ⟨h1, h2⟩ => ⟨⟨h1, by linarith⟩, h2⟩⟩]
      exact hX₁_cont
    · rw [compl_Iic, closure_Ioi, show Icc 0 (a + b) ∩ Ici a = Icc a (a + b) from by
        ext x; simp only [mem_inter_iff, mem_Icc, mem_Ici]
        exact ⟨fun ⟨⟨_, h2⟩, h3⟩ => ⟨h3, h2⟩,
               fun ⟨h1, h2⟩ => ⟨⟨by linarith, h2⟩, h1⟩⟩]
      exact hX₂_cont.comp ((continuous_id.sub continuous_const).continuousOn)
        (fun x hx => by simp only [mem_Icc] at hx ⊢; constructor <;> linarith)
  · -- HasDerivWithinAt on Icc 0 (a+b)
    intro t ht
    rcases eq_or_lt_of_le (mem_Icc.mp ht).1 with h0 | h0
    · -- t = 0
      rw [← h0, show X 0 = X₁ 0 from by simp [X, le_of_lt ha]]
      have hw := hX₁_within 0 (left_mem_Icc.mpr (le_of_lt ha))
      have h1 : HasDerivWithinAt X (v (X₁ 0)) (Icc 0 a) 0 :=
        hw.congr (fun s hs => show X s = X₁ s by simp [X, (mem_Icc.mp hs).2])
          (show X 0 = X₁ 0 by simp [X, le_of_lt ha])
      exact h1.mono_of_mem_nhdsWithin (mem_nhdsWithin.mpr
        ⟨Iio a, isOpen_Iio, mem_Iio.mpr ha,
          fun s ⟨hs1, hs2⟩ => ⟨(mem_Icc.mp hs2).1, le_of_lt (mem_Iio.mp hs1)⟩⟩)
    · rcases eq_or_lt_of_le (mem_Icc.mp ht).2 with hab | hab
      · -- t = a + b
        rw [hab, show X (a + b) = X₂ b from by simp [X, show ¬(a + b ≤ a) from by linarith]]
        have hw := hX₂_within b (right_mem_Icc.mpr (le_of_lt hb))
        have h1' : HasDerivWithinAt X₂ (v (X₂ b)) (Icc 0 b) ((fun s => s - a) (a + b)) := by
          simp only [add_sub_cancel_left]; exact hw
        have hda : HasDerivWithinAt (fun s => s - a) (1 : ℝ) (Icc a (a + b)) (a + b) :=
          ((hasDerivAt_id _).sub_const a).hasDerivWithinAt
        have hmaps : MapsTo (fun s => s - a) (Icc a (a + b)) (Icc 0 b) := fun s hs => by
          simp only [mem_Icc] at hs ⊢; constructor <;> linarith
        have h2 : HasDerivWithinAt (fun s => X₂ (s - a)) (v (X₂ b))
            (Icc a (a + b)) (a + b) := by
          have := HasDerivWithinAt.scomp (h := fun s => s - a) _ h1' hda hmaps
          simpa using this
        have h3 : HasDerivWithinAt X (v (X₂ b)) (Icc a (a + b)) (a + b) :=
          h2.congr (fun s hs => by
            by_cases hle : s ≤ a
            · exact show X s = X₂ (s - a) by
                simp [X, le_antisymm hle (mem_Icc.mp hs).1, sub_self, hglue]
            · exact show X s = X₂ (s - a) by simp [X, hle])
            (show X (a + b) = X₂ ((a + b) - a) by
              simp [X, show ¬(a + b ≤ a) from by linarith])
        exact h3.mono_of_mem_nhdsWithin (mem_nhdsWithin.mpr
          ⟨Ioi a, isOpen_Ioi, mem_Ioi.mpr (by linarith),
            fun s ⟨hs1, hs2⟩ => ⟨le_of_lt (mem_Ioi.mp hs1), (mem_Icc.mp hs2).2⟩⟩)
      · -- t ∈ Ioo 0 (a+b)
        exact (hX_hasDerivAt t ⟨h0, hab⟩).hasDerivWithinAt

end Pasting

/-! ### Global ODE existence -/

section GlobalExistence

variable [CompleteSpace E]

/-- Auxiliary induction: ODE existence for `T ≤ (n+1) * δ` where `δ < 1/(2K+2)`. -/
theorem exists_solution_aux
    (v : E → E) (K : NNReal) (hv_lip : LipschitzWith K v)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_small : δ < 1 / (2 * ↑K + 2)) :
    ∀ (n : ℕ) (x₀ : E) (T : ℝ), 0 < T → T ≤ (n + 1) * δ →
    ∃ X : ℝ → E, X 0 = x₀ ∧
      ContinuousOn X (Icc 0 T) ∧
      (∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt X (v (X t)) t) ∧
      (∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt X (v (X t)) (Icc 0 T) t) := by
  intro n
  induction n with
  | zero =>
    intro x₀ T hT hTle
    exact exists_solution_smallInterval v K hv_lip x₀ T hT (by push_cast at hTle; linarith)
  | succ n ih =>
    intro x₀ T hT hTle
    by_cases hle : T ≤ (n + 1) * δ
    · exact ih x₀ T hT hle
    · push_neg at hle
      obtain ⟨X₁, hX₁_init, hX₁_cont, hX₁_deriv, hX₁_within⟩ :=
        exists_solution_smallInterval v K hv_lip x₀ δ hδ_pos hδ_small
      have hn1_ge : (1 : ℝ) ≤ (↑n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
      have hTδ_pos : 0 < T - δ := by
        have : δ ≤ ((↑n : ℝ) + 1) * δ := le_mul_of_one_le_left (le_of_lt hδ_pos) hn1_ge
        linarith
      have hTδ_le' : T - δ ≤ ((↑n : ℝ) + 1) * δ := by
        have h1 : T ≤ ((↑n : ℝ) + 2) * δ := by push_cast at hTle; linarith
        linarith
      obtain ⟨X₂, hX₂_init, hX₂_cont, hX₂_deriv, hX₂_within⟩ :=
        ih (X₁ δ) (T - δ) hTδ_pos hTδ_le'
      have hsum : δ + (T - δ) = T := by ring
      obtain ⟨X, hX_init, hX_cont, hX_deriv, hX_within⟩ :=
        paste_solutions hδ_pos hTδ_pos hX₁_cont hX₁_deriv hX₁_within
          hX₂_cont hX₂_deriv hX₂_within hX₂_init
      rw [hsum] at hX_cont hX_deriv hX_within
      exact ⟨X, by rw [hX_init, hX₁_init], hX_cont, hX_deriv, hX_within⟩

/-- **Global ODE existence for Lipschitz vector fields.**
Given a globally Lipschitz vector field `v : E → E` with Lipschitz constant `K` on a
Banach space `E`, for any initial condition `x₀ : E` and time horizon `T > 0`,
there exists a solution `X : ℝ → E` satisfying:
- `X 0 = x₀` (initial condition),
- `ContinuousOn X (Icc 0 T)` (continuity on `[0, T]`),
- `HasDerivAt X (v (X t)) t` for all `t ∈ (0, T)` (ODE in the interior),
- `HasDerivWithinAt X (v (X t)) (Ici t) t` for all `t ∈ [0, T)` (right derivative at left
  endpoint and interior points).

This extends Mathlib's local Picard-Lindelöf theory (`IsPicardLindelof`) to arbitrary
time intervals by iterating local solutions and pasting them together. -/
theorem exists_solution_of_lipschitzWith
    (v : E → E) (K : NNReal) (hv_lip : LipschitzWith K v)
    (x₀ : E) (T : ℝ) (hT : 0 < T) :
    ∃ X : ℝ → E, X 0 = x₀ ∧
      ContinuousOn X (Icc 0 T) ∧
      (∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt X (v (X t)) t) ∧
      (∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt X (v (X t)) (Ici t) t) := by
  set δ : ℝ := 1 / (2 * ↑K + 3) with hδ_def
  have hδ_pos : (0 : ℝ) < δ := by positivity
  have hδ_small : δ < 1 / (2 * ↑K + 2) := by
    show 1 / (2 * ↑K + 3) < 1 / (2 * ↑K + 2)
    refine div_lt_div_of_pos_left one_pos (by positivity : (0 : ℝ) < 2 * ↑K + 2) ?_
    show 2 * (↑K : ℝ) + 2 < 2 * ↑K + 3; linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (T / δ)
  have hTle : T ≤ ((↑n : ℝ) + 1) * δ := by
    have h2 : T < (↑n : ℝ) * δ := by
      by_contra h; push_neg at h
      have : (↑n : ℝ) ≤ T / δ := le_div_iff₀ hδ_pos |>.mpr (by linarith)
      linarith
    nlinarith
  obtain ⟨X, hX_init, hX_cont, hX_deriv, hX_within⟩ :=
    exists_solution_aux v K hv_lip δ hδ_pos hδ_small n x₀ T hT hTle
  refine ⟨X, hX_init, hX_cont, hX_deriv, fun t ht => ?_⟩
  rcases eq_or_lt_of_le (mem_Ico.mp ht).1 with h0 | h0
  · rw [← h0]
    exact (hX_within 0 (left_mem_Icc.mpr (le_of_lt hT))).mono_of_mem_nhdsWithin
      (mem_nhdsWithin.mpr ⟨Iio T, isOpen_Iio, mem_Iio.mpr hT,
        fun s ⟨hs1, hs2⟩ => ⟨mem_Ici.mp hs2, le_of_lt (mem_Iio.mp hs1)⟩⟩)
  · exact (hX_deriv t ⟨h0, (mem_Ico.mp ht).2⟩).hasDerivWithinAt

end GlobalExistence

end ODE
