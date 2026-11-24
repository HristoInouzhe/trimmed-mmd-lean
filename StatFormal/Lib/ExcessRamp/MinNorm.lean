import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Basic

/-!
# Uniqueness of the element of minimal norm of a convex set

Library component (trimmed-mmd, the population witness `d⋆`, §2 :196-197). Untrusted library code.

* `inner_nonneg_of_norm_le_segment`: first-order optimality of a norm minimum along a segment (copy-adapted from the proved
  route lemma `StatFormal.Wave30tz.inner_nonneg_of_norm_le`, `Wave30tz/RoutePop.lean`);
* `minNorm_unique`: in a real inner-product space, a convex set has at most one element of minimal norm
  (`⟪p, q − p⟫ ≥ 0` and `⟪q, p − q⟫ ≥ 0` add up to `−‖p − q‖² ≥ 0`).
-/

set_option linter.style.longLine false

noncomputable section
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.ExcessRamp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- First-order optimality of a norm minimum along a segment: `‖e‖ ≤ ‖e + s d‖` for `s ∈ (0,1]` gives `⟪e, d⟫ ≥ 0`.
(Copy-adapted from `StatFormal.Wave30tz.inner_nonneg_of_norm_le`.) -/
theorem inner_nonneg_of_norm_le_segment {e d : E} (h : ∀ s : ℝ, 0 < s → s ≤ 1 → ‖e‖ ≤ ‖e + s • d‖) :
    0 ≤ ⟪e, d⟫_ℝ := by
  by_contra hneg
  push Not at hneg
  have hd : d ≠ 0 := by rintro rfl; simp at hneg
  have hc : 0 < ‖d‖ ^ 2 := by positivity
  set s := min 1 (-⟪e, d⟫_ℝ / ‖d‖ ^ 2) with hs
  have hs0 : 0 < s := lt_min one_pos (div_pos (by linarith) hc)
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsc : s * ‖d‖ ^ 2 ≤ -⟪e, d⟫_ℝ := by
    have : s ≤ -⟪e, d⟫_ℝ / ‖d‖ ^ 2 := min_le_right _ _
    rwa [le_div_iff₀ hc] at this
  have h1 := h s hs0 hs1
  have h2 : ‖e‖ ^ 2 ≤ ‖e + s • d‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [norm_add_sq_real, norm_smul, real_inner_smul_right, Real.norm_eq_abs, abs_of_pos hs0, mul_pow] at h2
  have h3 : 0 ≤ s * (-⟪e, d⟫_ℝ - s * ‖d‖ ^ 2) := mul_nonneg hs0.le (by linarith)
  have h4 : s * ⟪e, d⟫_ℝ < 0 := mul_neg_of_pos_of_neg hs0 hneg
  nlinarith

/-- **A convex set has at most one element of minimal norm.** -/
theorem minNorm_unique {C : Set E} (hC : Convex ℝ C) {p q : E} (hp : p ∈ C) (hpm : ∀ x ∈ C, ‖p‖ ≤ ‖x‖)
    (hq : q ∈ C) (hqm : ∀ x ∈ C, ‖q‖ ≤ ‖x‖) : p = q := by
  have h1 : 0 ≤ ⟪p, q - p⟫_ℝ := inner_nonneg_of_norm_le_segment fun s hs0 hs1 => by
    have hmem : (1 - s) • p + s • q ∈ C := hC hp hq (by linarith) hs0.le (by ring)
    have e : (1 - s) • p + s • q = p + s • (q - p) := by rw [smul_sub, sub_smul, one_smul]; abel
    rw [← e]; exact hpm _ hmem
  have h2 : 0 ≤ ⟪q, p - q⟫_ℝ := inner_nonneg_of_norm_le_segment fun s hs0 hs1 => by
    have hmem : (1 - s) • q + s • p ∈ C := hC hq hp (by linarith) hs0.le (by ring)
    have e : (1 - s) • q + s • p = q + s • (p - q) := by rw [smul_sub, sub_smul, one_smul]; abel
    rw [← e]; exact hqm _ hmem
  have h3 : ⟪p, q - p⟫_ℝ + ⟪q, p - q⟫_ℝ = -‖p - q‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_comm p q]
    ring
  have h5 : ‖p - q‖ = 0 := by nlinarith [norm_nonneg (p - q)]
  exact sub_eq_zero.1 (norm_eq_zero.1 h5)

end StatFormal.ExcessRamp
