import StatFormal.Lib.Convex.Subgradient
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Analysis.Calculus.Rademacher

/-!
# Almost-everywhere convergence of gradients of convergent convex functions

Library component (untrusted; no `Statements.lean` involved).

Corollaries of `StatFormal.Convex.tendsto_subgradient` (Rockafellar, *Convex Analysis*,
Thm 24.5 / 25.7):

* `ae_tendsto_fderiv` — for any measure `μ`: if each `Fₙ` (countably many) and `f` are
  differentiable `μ`-a.e. on `U`, then `fderiv Fₙ → fderiv f` `μ`-a.e. on `U`;
* `ae_tendsto_fderiv_of_isAddHaarMeasure` — for an additive Haar measure (Lebesgue measure) the
  differentiability hypotheses are automatic (Rademacher for convex functions, Rockafellar
  Thm 25.5, via Tau Ceti's `ConvexOn.ae_differentiableAt_of_mem`);
* `tendsto_subgradient_inner` — the gradient form of Thm 24.5 on a finite-dimensional inner-product
  space: vector subgradients `gₙ` at `xₙ → x` converge to `∇f(x)`;
* `ae_tendsto_gradient`, `ae_tendsto_gradient_volume` — `∇Fₙ → ∇f` a.e. on `U`, in particular
  Lebesgue-a.e. on `U ⊆ EuclideanSpace ℝ (Fin d)`.
-/

open Metric Set Filter MeasureTheory
open scoped Topology Gradient InnerProductSpace

namespace StatFormal.Convex

section Normed

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] {l : Filter ι} {F : ι → E → ℝ} {f : E → ℝ} {U : Set E}

/-- **A.e. convergence of derivatives** (Rockafellar, *Convex Analysis*, Thm 25.7, a.e. form).
Let `E` be a finite-dimensional real normed space with a measure `μ`, `U ⊆ E` open, `ι` countable,
`Fₙ` convex on `U` with `Fₙ → f` pointwise on `U` (`f : E → ℝ` finite). If every `Fₙ` and `f` are
differentiable at `μ`-almost every point of `U`, then for `μ`-a.e. `y ∈ U`,
`fderiv Fₙ y → fderiv f y` along `l`. -/
theorem ae_tendsto_fderiv [Countable ι] {μ : Measure E} (hU : IsOpen U)
    (hF : ∀ n, ConvexOn ℝ U (F n)) (hlim : ∀ x ∈ U, Tendsto (fun n => F n x) l (𝓝 (f x)))
    (hFd : ∀ n, ∀ᵐ y ∂μ, y ∈ U → DifferentiableAt ℝ (F n) y)
    (hfd : ∀ᵐ y ∂μ, y ∈ U → DifferentiableAt ℝ f y) :
    ∀ᵐ y ∂μ, y ∈ U → Tendsto (fun n => fderiv ℝ (F n) y) l (𝓝 (fderiv ℝ f y)) := by
  filter_upwards [ae_all_iff.2 hFd, hfd] with y hy hyf hyU
  exact tendsto_fderiv_at hU (Eventually.of_forall hF) hlim hyU (hyf hyU)
    (Eventually.of_forall fun n => hy n hyU)

/-- **Lebesgue-a.e. convergence of derivatives of convex functions** (Rockafellar, *Convex
Analysis*, Thm 25.7 with Thm 25.5). For an additive Haar measure `μ` (e.g. Lebesgue measure) on a
finite-dimensional real normed space, `U` open, `ι` countable, `Fₙ` convex on `U` and `Fₙ → f`
pointwise on `U` with `f` finite: `fderiv Fₙ y → fderiv f y` for `μ`-a.e. `y ∈ U`. No
differentiability hypothesis is needed: convex functions are differentiable a.e. (Rademacher). -/
theorem ae_tendsto_fderiv_of_isAddHaarMeasure [Countable ι] [BorelSpace E] {μ : Measure E}
    [μ.IsAddHaarMeasure] (hU : IsOpen U) (hF : ∀ n, ConvexOn ℝ U (F n))
    (hlim : ∀ x ∈ U, Tendsto (fun n => F n x) l (𝓝 (f x))) :
    ∀ᵐ y ∂μ, y ∈ U → Tendsto (fun n => fderiv ℝ (F n) y) l (𝓝 (fderiv ℝ f y)) := by
  rcases l.eq_or_neBot with rfl | hl
  · exact Eventually.of_forall fun _ _ => tendsto_bot
  exact ae_tendsto_fderiv hU hF hlim (fun n => (hF n).ae_differentiableAt_of_mem)
    (convexOn_of_tendsto (Eventually.of_forall hF) hlim).ae_differentiableAt_of_mem

end Normed

section Inner

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  {l : Filter ι} {F : ι → H → ℝ} {f : H → ℝ} {U : Set H}

/-- **Convergence of (vector) subgradients to the gradient** (Rockafellar, *Convex Analysis*,
Thm 24.5 / 25.7, inner-product form). Let `H` be a finite-dimensional real inner-product space
(e.g. `EuclideanSpace ℝ (Fin d)`), `U ⊆ H` open, `Fₙ` eventually convex on `U`, `Fₙ → f`
pointwise on `U` with `f` finite, `f` with gradient `∇f(x) = g₀` at `x ∈ U`, `xₙ → x`, and
(eventually) `gₙ ∈ H` a subgradient of `Fₙ` at `xₙ` relative to `U`:
`Fₙ xₙ + ⟪gₙ, y - xₙ⟫ ≤ Fₙ y` for `y ∈ U`. Then `gₙ → g₀`. -/
theorem tendsto_subgradient_inner (hU : IsOpen U) (hF : ∀ᶠ n in l, ConvexOn ℝ U (F n))
    (hlim : ∀ x ∈ U, Tendsto (fun n => F n x) l (𝓝 (f x))) {x : H} (hx : x ∈ U) {g₀ : H}
    (hf : HasGradientAt f g₀ x) {xs : ι → H} (hxs : Tendsto xs l (𝓝 x)) {g : ι → H}
    (hg : ∀ᶠ n in l, ∀ y ∈ U, F n (xs n) + ⟪g n, y - xs n⟫_ℝ ≤ F n y) :
    Tendsto g l (𝓝 g₀) := by
  have h := tendsto_subgradient (g := fun n => InnerProductSpace.toDual ℝ H (g n)) hU hF hlim hx
    hf.hasFDerivAt hxs (by simpa only [InnerProductSpace.toDual_apply_apply] using hg)
  have hc := ((InnerProductSpace.toDual ℝ H).symm.continuous.tendsto _).comp h
  simpa only [Function.comp_def, LinearIsometryEquiv.symm_apply_apply] using hc

/-- **Gradients along converging points converge** (Rockafellar, Thm 25.7, gradient form): under
the hypotheses of `tendsto_fderiv_of_tendsto`, `∇Fₙ(xₙ) → ∇f(x)`. -/
theorem tendsto_gradient_of_tendsto (hU : IsOpen U) (hF : ∀ᶠ n in l, ConvexOn ℝ U (F n))
    (hlim : ∀ x ∈ U, Tendsto (fun n => F n x) l (𝓝 (f x))) {x : H} (hx : x ∈ U)
    (hf : DifferentiableAt ℝ f x) {xs : ι → H} (hxs : Tendsto xs l (𝓝 x))
    (hFd : ∀ᶠ n in l, DifferentiableAt ℝ (F n) (xs n)) :
    Tendsto (fun n => ∇ (F n) (xs n)) l (𝓝 (∇ f x)) :=
  ((InnerProductSpace.toDual ℝ H).symm.continuous.tendsto _).comp
    (tendsto_fderiv_of_tendsto hU hF hlim hx hf hxs hFd)

/-- **A.e. convergence of gradients** (Rockafellar, Thm 25.7, a.e. gradient form): for any
measure `μ` on `H`, `ι` countable, `Fₙ` convex on the open set `U`, `Fₙ → f` pointwise on `U`,
and every `Fₙ` and `f` differentiable `μ`-a.e. on `U`, we have `∇Fₙ y → ∇f y` for `μ`-a.e.
`y ∈ U`. -/
theorem ae_tendsto_gradient [MeasurableSpace H] [Countable ι] {μ : Measure H} (hU : IsOpen U)
    (hF : ∀ n, ConvexOn ℝ U (F n)) (hlim : ∀ x ∈ U, Tendsto (fun n => F n x) l (𝓝 (f x)))
    (hFd : ∀ n, ∀ᵐ y ∂μ, y ∈ U → DifferentiableAt ℝ (F n) y)
    (hfd : ∀ᵐ y ∂μ, y ∈ U → DifferentiableAt ℝ f y) :
    ∀ᵐ y ∂μ, y ∈ U → Tendsto (fun n => ∇ (F n) y) l (𝓝 (∇ f y)) := by
  filter_upwards [ae_tendsto_fderiv hU hF hlim hFd hfd] with y hy hyU
  exact ((InnerProductSpace.toDual ℝ H).symm.continuous.tendsto _).comp (hy hyU)

/-- **Lebesgue-a.e. convergence of gradients of convex functions on `ℝᵈ`** (Rockafellar, *Convex
Analysis*, Thm 25.7 with Rademacher, Thm 25.5). On `EuclideanSpace ℝ (Fin d)` with Lebesgue
measure, let `U` be open, `ι` countable, `Fₙ` convex on `U` and `Fₙ → f` pointwise on `U` with
`f : ℝᵈ → ℝ` finite. Then `∇Fₙ y → ∇f y` for Lebesgue-a.e. `y ∈ U`. -/
theorem ae_tendsto_gradient_volume {d : ℕ} [Countable ι] {l : Filter ι}
    {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) (hF : ∀ n, ConvexOn ℝ U (F n))
    (hlim : ∀ x ∈ U, Tendsto (fun n => F n x) l (𝓝 (f x))) :
    ∀ᵐ y, y ∈ U → Tendsto (fun n => ∇ (F n) y) l (𝓝 (∇ f y)) := by
  filter_upwards [ae_tendsto_fderiv_of_isAddHaarMeasure (μ := volume) hU hF hlim] with y hy hyU
  exact ((InnerProductSpace.toDual ℝ _).symm.continuous.tendsto _).comp (hy hyU)

end Inner

end StatFormal.Convex
