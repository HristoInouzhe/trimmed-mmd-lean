import Mathlib.Analysis.Convex.Continuous

/-!
# Convex functions bounded above on a ball are Lipschitz on smaller balls

Library component (untrusted; no `Statements.lean` involved).

Mathlib provides `ConvexOn.lipschitzOnWith_of_abs_le`: a convex function with `|f| ≤ M` on
`ball x₀ r` is `2M/ε`-Lipschitz on `ball x₀ (r - ε)`. This file removes the two-sided bound:
an *upper* bound suffices, since convexity gives the lower bound `f a ≥ 2 f x₀ - M` by reflecting
`a` through the centre. This is the quantitative form of Rockafellar, *Convex Analysis*,
Thm 10.4 (the local step of its proof).

## Main results

* `StatFormal.Convex.abs_le_of_le_on_ball`: `f ≤ M` on `ball x₀ r` ⇒ `|f| ≤ |M| + 2|f x₀|` there.
* `StatFormal.Convex.lipschitzOnWith_of_le_on_ball`: `f ≤ M` on `ball x₀ r`, `0 < ε` ⇒ `f` is
  `2(|M| + 2|f x₀|)/ε`-Lipschitz on `ball x₀ (r - ε)`.
-/

open Metric Set

namespace StatFormal.Convex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Two-sided bound from an upper bound.** Let `f` be convex on the open ball `B(x₀, r)` in a
real normed space and bounded above there by `M`. Then `|f a| ≤ |M| + 2|f x₀|` on `B(x₀, r)`.
Proof: `a` and its reflection `2x₀ - a` both lie in the ball, and convexity at the midpoint `x₀`
gives `2 f x₀ ≤ f a + f (2x₀ - a) ≤ f a + M`.
(Rockafellar, *Convex Analysis*, proof of Thm 10.4.) -/
theorem abs_le_of_le_on_ball {f : E → ℝ} {x₀ : E} {r M : ℝ} (hf : ConvexOn ℝ (ball x₀ r) f)
    (hM : ∀ a ∈ ball x₀ r, f a ≤ M) : ∀ a ∈ ball x₀ r, |f a| ≤ |M| + 2 * |f x₀| := by
  intro a ha
  have hx₀ : x₀ ∈ ball x₀ r := mem_ball_self (pos_of_mem_ball ha)
  have ha' : (2 : ℝ) • x₀ - a ∈ ball x₀ r := by
    rw [mem_ball_iff_norm] at ha ⊢
    have : (2 : ℝ) • x₀ - a - x₀ = -(a - x₀) := by rw [two_smul]; abel
    rwa [this, norm_neg]
  have hmid := hf.2 ha ha' (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  have hpt : (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • ((2 : ℝ) • x₀ - a) = x₀ := by
    rw [smul_sub, smul_smul]; norm_num
  rw [hpt, smul_eq_mul, smul_eq_mul] at hmid
  have h1 := hM a ha
  have h2 := hM _ ha'
  rw [abs_le]
  constructor
  · have := neg_abs_le (f x₀); have := le_abs_self M; linarith
  · have := abs_nonneg (f x₀); have := le_abs_self M; linarith

/-- **Convex functions bounded above on a ball are Lipschitz on smaller balls, with an explicit
constant** (Rockafellar, *Convex Analysis*, Thm 10.4, quantitative form). Let `f` be convex on
`B(x₀, r)` in a real normed space `E`, with `f ≤ M` on `B(x₀, r)`, and let `ε > 0`. Then `f` is
Lipschitz on `B(x₀, r - ε)` with constant `2(|M| + 2|f x₀|)/ε`. No finite-dimensionality is
needed. -/
theorem lipschitzOnWith_of_le_on_ball {f : E → ℝ} {x₀ : E} {r M ε : ℝ}
    (hf : ConvexOn ℝ (ball x₀ r) f) (hε : 0 < ε) (hM : ∀ a ∈ ball x₀ r, f a ≤ M) :
    LipschitzOnWith (2 * (|M| + 2 * |f x₀|) / ε).toNNReal f (ball x₀ (r - ε)) :=
  hf.lipschitzOnWith_of_abs_le hε fun a ha => abs_le_of_le_on_ball hf hM a ha

/-- Real-valued form of `lipschitzOnWith_of_le_on_ball`:
`|f a - f b| ≤ 2(|M| + 2|f x₀|)/ε · ‖a - b‖` for `a, b ∈ B(x₀, r - ε)`. -/
theorem abs_sub_le_of_le_on_ball {f : E → ℝ} {x₀ : E} {r M ε : ℝ}
    (hf : ConvexOn ℝ (ball x₀ r) f) (hε : 0 < ε) (hM : ∀ a ∈ ball x₀ r, f a ≤ M)
    {a b : E} (ha : a ∈ ball x₀ (r - ε)) (hb : b ∈ ball x₀ (r - ε)) :
    |f a - f b| ≤ 2 * (|M| + 2 * |f x₀|) / ε * ‖a - b‖ := by
  have h := (lipschitzOnWith_of_le_on_ball hf hε hM).dist_le_mul a ha b hb
  have hK : 0 ≤ 2 * (|M| + 2 * |f x₀|) / ε := by positivity
  rwa [Real.coe_toNNReal _ hK, Real.dist_eq, dist_eq_norm] at h

end StatFormal.Convex
