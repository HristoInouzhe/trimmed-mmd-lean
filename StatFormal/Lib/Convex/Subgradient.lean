import StatFormal.Lib.Convex.UniformConvergence
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Convergence of subgradients of convergent convex functions

Library component (untrusted; no `Statements.lean` involved).

Rockafellar, *Convex Analysis*, Thm 24.5 and Thm 25.7: if convex `Fₙ → f` pointwise on an open
convex set `U` of a finite-dimensional space, `f` is differentiable at `x ∈ U`, `xₙ → x`, and
`gₙ` is a subgradient of `Fₙ` at `xₙ`, then `gₙ → ∇f(x)`. Consequently, at every point of `U`
where `f` and all `Fₙ` are differentiable, `∇Fₙ → ∇f`.

Subgradients are elements of the dual `E →L[ℝ] ℝ` (a gradient version on inner-product spaces
is in `StatFormal.Foundations.Convex.GradientAE`), and "subgradient at `xₙ`" is only required
relative to `U`: `Fₙ (xₙ) + gₙ (y - xₙ) ≤ Fₙ y` for `y ∈ U`.

## Proof of the main theorem (direct, no compactness of the subgradients)

For `‖v‖ ≤ 1` and small `t > 0`, the subgradient inequality gives
`t gₙ v ≤ Fₙ(xₙ + t v) - Fₙ(xₙ)`. By uniform convergence on a compact ball (Thm 10.8,
`tendstoUniformlyOn_of_tendsto`) and uniform continuity of `f` there, the right side is eventually
within `2α` of `f(x + t v) - f(x)`, which is `≤ t f' v + η t` by Fréchet differentiability. Hence
`(gₙ - f') v ≤ 3η` uniformly for `‖v‖ ≤ 1`; applying this to `±v` bounds the operator norm.

## Main results

* `StatFormal.Convex.add_fderiv_le_of_hasFDerivAt` — a convex function lies above its tangent
  hyperplane: `f x + f' (y - x) ≤ f y` on `U`.
* `StatFormal.Convex.tendsto_subgradient` — **Rockafellar Thm 24.5 / 25.7**: `gₙ → f'`.
* `StatFormal.Convex.tendsto_fderiv_of_tendsto`, `StatFormal.Convex.tendsto_fderiv_at` —
  derivatives (at `xₙ → x`, resp. at `x`) converge.
-/

open Metric Set Filter
open scoped Topology NNReal

namespace StatFormal.Convex

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Tangent-hyperplane inequality.** If `f` is convex on a convex set `U ∋ x` and has Fréchet
derivative `f'` at `x`, then `f'` is a subgradient of `f` at `x` relative to `U`:
`f x + f' (y - x) ≤ f y` for all `y ∈ U` (Rockafellar, *Convex Analysis*, Thm 25.1). -/
theorem add_fderiv_le_of_hasFDerivAt {U : Set E} {f : E → ℝ} (hf : ConvexOn ℝ U f) {x : E}
    (hx : x ∈ U) {f' : E →L[ℝ] ℝ} (hf' : HasFDerivAt f f' x) {y : E} (hy : y ∈ U) :
    f x + f' (y - x) ≤ f y := by
  set φ : ℝ → ℝ := fun t => f (x + t • (y - x)) with hφ
  have hline : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).const_add x
  have hφd : HasDerivAt φ (f' (y - x)) 0 :=
    hf'.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hslope := hφd.tendsto_slope_zero_right
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ • (φ (0 + t) - φ 0) ≤ f y - f x := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    have hc := hf.2 hx hy (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le (by ring)
    have hpt : (1 - t) • x + t • y = x + t • (y - x) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [hpt, smul_eq_mul, smul_eq_mul] at hc
    simp only [hφ, zero_add, zero_smul, add_zero, smul_eq_mul]
    rw [inv_mul_le_iff₀ ht0]
    linarith
  have := le_of_tendsto hslope hev
  linarith

variable [FiniteDimensional ℝ E] {l : Filter ι} {F : ι → E → ℝ} {f : E → ℝ} {U : Set E}

/-- **Convergence of subgradients** (Rockafellar, *Convex Analysis*, Thm 24.5 and Thm 25.7).
Let `E` be a finite-dimensional real normed space, `U ⊆ E` open, `Fₙ` (eventually along the
filter `l`) convex on `U`, and `Fₙ x → f x` for every `x ∈ U` with `f : E → ℝ` finite. Suppose `f`
has Fréchet derivative `f'` at `x ∈ U`, `xₙ → x`, and (eventually) `gₙ : E →L[ℝ] ℝ` is a
subgradient of `Fₙ` at `xₙ` relative to `U`, i.e. `Fₙ xₙ + gₙ (y - xₙ) ≤ Fₙ y` for all `y ∈ U`.
Then `gₙ → f'` in operator norm. -/
theorem tendsto_subgradient (hU : IsOpen U) (hF : ∀ᶠ n in l, ConvexOn ℝ U (F n))
    (hlim : ∀ x ∈ U, Tendsto (fun n => F n x) l (𝓝 (f x))) {x : E} (hx : x ∈ U)
    {f' : E →L[ℝ] ℝ} (hf : HasFDerivAt f f' x) {xs : ι → E} (hxs : Tendsto xs l (𝓝 x))
    {g : ι → E →L[ℝ] ℝ} (hg : ∀ᶠ n in l, ∀ y ∈ U, F n (xs n) + g n (y - xs n) ≤ F n y) :
    Tendsto g l (𝓝 f') := by
  rcases l.eq_or_neBot with rfl | hl
  · exact tendsto_bot
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- a closed ball `B̄(x, 2r) ⊆ U`
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.1 hU x hx
  set r := R / 3 with hr_def
  have hr : 0 < r := by positivity
  set K := closedBall x (2 * r)
  have hKU : K ⊆ U := (closedBall_subset_ball (by linarith)).trans hRU
  have hKc : IsCompact K := isCompact_closedBall x (2 * r)
  -- differentiability of `f` at `x` with tolerance `η = ε/4`
  set η := ε / 4 with hη_def
  have hη : 0 < η := by positivity
  obtain ⟨δ, hδ, hδf⟩ := Metric.eventually_nhds_iff.1 (hf.isLittleO.def hη)
  set t := min r (δ / 2) with ht_def
  have ht : 0 < t := lt_min hr (by positivity)
  have htr : t ≤ r := min_le_left _ _
  have htδ : t < δ := (min_le_right _ _).trans_lt (by linarith)
  set α := η * t with hα_def
  have hα : 0 < α := by positivity
  -- uniform continuity of `f` on `K`
  have hfc : ContinuousOn f U := (convexOn_of_tendsto hF hlim).continuousOn hU
  obtain ⟨β, hβ, hβf⟩ := Metric.uniformContinuousOn_iff.1
    (hKc.uniformContinuousOn_of_continuous (hfc.mono hKU)) (α / 2) (by positivity)
  -- uniform convergence on `K`
  have hunif := Metric.tendstoUniformlyOn_iff.1
    (tendstoUniformlyOn_of_tendsto hU hF hlim hKU hKc) (α / 2) (by positivity)
  have hxs' := hxs.eventually (ball_mem_nhds x (lt_min hr hβ))
  filter_upwards [hunif, hxs', hg] with n hnu hnx hng
  have hnx' : dist (xs n) x < r := hnx.trans_le (min_le_left _ _)
  have hnxβ : dist (xs n) x < β := hnx.trans_le (min_le_right _ _)
  -- the one-sided bound `(gₙ - f') v ≤ 3η` for `‖v‖ ≤ 1`
  have key : ∀ v : E, ‖v‖ ≤ 1 → (g n - f') v ≤ 3 * η := by
    intro v hv
    have htv : ‖t • v‖ ≤ t := by
      rw [norm_smul, Real.norm_of_nonneg ht.le]; nlinarith [norm_nonneg v]
    have hxsK : xs n ∈ K := mem_closedBall.2 (by linarith)
    have hxK : x ∈ K := mem_closedBall_self (by linarith)
    have hyK : xs n + t • v ∈ K := by
      rw [mem_closedBall, dist_eq_norm]
      calc ‖xs n + t • v - x‖ = ‖(xs n - x) + t • v‖ := by abel_nf
        _ ≤ ‖xs n - x‖ + ‖t • v‖ := norm_add_le _ _
        _ ≤ 2 * r := by rw [← dist_eq_norm]; linarith
    have hzK : x + t • v ∈ K := by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]; linarith
    -- subgradient inequality
    have h1 := hng _ (hKU hyK)
    rw [add_sub_cancel_left, map_smul, smul_eq_mul] at h1
    -- uniform convergence at the two points
    have h2 := hnu _ hyK
    have h3 := hnu _ hxsK
    rw [Real.dist_eq, abs_lt] at h2 h3
    -- uniform continuity of `f`
    have h4 := hβf _ hyK _ hzK (by
      rw [dist_eq_norm, add_sub_add_right_eq_sub, ← dist_eq_norm]; exact hnxβ)
    have h5 := hβf _ hxsK _ hxK hnxβ
    rw [Real.dist_eq, abs_lt] at h4 h5
    -- differentiability at `x`
    have h6 := hδf (show dist (x + t • v) x < δ by
      rw [dist_eq_norm, add_sub_cancel_left]; linarith)
    rw [Real.norm_eq_abs, add_sub_cancel_left, abs_le, map_smul, smul_eq_mul] at h6
    have h6' : f (x + t • v) - f x - t * f' v ≤ η * t := h6.2.trans
      (mul_le_mul_of_nonneg_left htv hη.le)
    have hmain : t * (g n v) ≤ t * (f' v) + t * (3 * η) := by
      nlinarith
    rw [sub_apply]
    have := le_of_mul_le_mul_left (by linarith : t * (g n v - f' v) ≤ t * (3 * η)) ht
    linarith
  have hnorm : ‖g n - f'‖ ≤ 3 * η := by
    refine ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity) fun v hv => ?_
    rw [Real.norm_eq_abs, abs_le]
    refine ⟨?_, key v hv.le⟩
    have := key (-v) (by rw [norm_neg, hv])
    rw [map_neg] at this
    linarith
  rw [dist_eq_norm]
  linarith

/-- **Convergence of derivatives along converging points** (Rockafellar, *Convex Analysis*,
Thm 25.7). Under the hypotheses of `tendsto_subgradient` (`U` open, `Fₙ` eventually convex on `U`,
`Fₙ → f` pointwise on `U`, `x ∈ U`, `xₙ → x`), if `f` is differentiable at `x` and, eventually,
`Fₙ` is differentiable at `xₙ`, then `fderiv Fₙ (xₙ) → fderiv f x`. -/
theorem tendsto_fderiv_of_tendsto (hU : IsOpen U) (hF : ∀ᶠ n in l, ConvexOn ℝ U (F n))
    (hlim : ∀ x ∈ U, Tendsto (fun n => F n x) l (𝓝 (f x))) {x : E} (hx : x ∈ U)
    (hf : DifferentiableAt ℝ f x) {xs : ι → E} (hxs : Tendsto xs l (𝓝 x))
    (hFd : ∀ᶠ n in l, DifferentiableAt ℝ (F n) (xs n)) :
    Tendsto (fun n => fderiv ℝ (F n) (xs n)) l (𝓝 (fderiv ℝ f x)) :=
  tendsto_subgradient hU hF hlim hx hf.hasFDerivAt hxs <| by
    filter_upwards [hF, hFd, hxs.eventually (hU.mem_nhds hx)] with n hn hnd hnU y hy
    exact add_fderiv_le_of_hasFDerivAt hn hnU hnd.hasFDerivAt hy

/-- **Pointwise convergence of derivatives** (Rockafellar, *Convex Analysis*, Thm 25.7). If
`Fₙ` are eventually convex on the open set `U`, `Fₙ → f` pointwise on `U`, and at `x ∈ U` the
limit `f` and (eventually) every `Fₙ` are differentiable, then `fderiv Fₙ x → fderiv f x`. -/
theorem tendsto_fderiv_at (hU : IsOpen U) (hF : ∀ᶠ n in l, ConvexOn ℝ U (F n))
    (hlim : ∀ x ∈ U, Tendsto (fun n => F n x) l (𝓝 (f x))) {x : E} (hx : x ∈ U)
    (hf : DifferentiableAt ℝ f x) (hFd : ∀ᶠ n in l, DifferentiableAt ℝ (F n) x) :
    Tendsto (fun n => fderiv ℝ (F n) x) l (𝓝 (fderiv ℝ f x)) :=
  tendsto_fderiv_of_tendsto hU hF hlim hx hf tendsto_const_nhds hFd

end StatFormal.Convex
