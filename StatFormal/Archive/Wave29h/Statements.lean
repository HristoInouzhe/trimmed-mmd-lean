import StatFormal.Archive.Wave28f.Statements
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# FROZEN STATEMENTS — wave 29h: ICL `thm:score` for a parameter in `ℝ^p` (`p` general) — the Hessian uniform law,
# the linearisation, asymptotic normality `√n(θ̂ − θ⋆) ⇝ N(0, V⁻¹(Σ_pool + κ⁻¹Σ_val)V⁻¹)` — and `cor:inference`

Sources:
* ICL `thm:score` (`context-distribution-ICL/paper/v3/sections/06_estimation.tex:137-148`) and `cor:inference`
  (`:154-167`), with the objective of `subsec:score-guarantees` (`:127-135`).
* Supplement `supp/proofs_score.tex`: Assumptions `as:compact`–`as:interior` (`:14-48`), the normality proof
  Steps 1–4 (`:207-296`; Step 1 `:207-213`, Step 2 / `eq:e-linear` `:215-278`, Steps 3–4 `:279-296`),
  the proof of `cor:inference` (`:298-326`), `prop:swor-score` (`:349-356`).
Imports the frozen Wave 28f statements (and through them the frozen Wave 28b `jScore`, `jScoreIid`, `jPop`; Wave 11b
`jSwor`, `jIid`, `wScore`; Wave 24c `ctxLawT`, `empCtxLaw`, `normC`, `coverRho`, `klPop`; Wave 24e `wPop`), not
copied. The frozen objects are already generic in the parameter type, so they are used at `Θ = ℝ^p =
EuclideanSpace ℝ (Fin p)` directly. Mathlib's `multivariateGaussian`, `gradient`, `fderiv`, `ContDiffOn`,
`TendstoInDistribution`, `TendstoInMeasure`, `HasLaw`, `variance`, `covariance` otherwise. New definitions:
`hessMat` (Hessian matrix in the standard basis), `covMat` (covariance matrix of an `ℝ^p`-valued function),
`tauInfl` (`τ_θ = g_θ∇Γᵀ(φ − μ_θφ)`), `inferVar` (`σ²_Ψ`).

Covered:
* Step 1 (`score_hessian_ulln_multi`): `J ∈ C²(U)` on `U = B(θ⋆, δ) ⊆ ℝ^p`, every `J^iid_{n,m}` is `C²` on `U`, and
  almost surely (one null set for all radii) `∇²J^iid_{n,m} → ∇²J` uniformly in operator norm on every closed ball
  `B̄(θ⋆, r)`, `r < δ`.
* Step 2 (`score_linearization_multi`): `eq:e-linear` times `√n` for the `ℝ^p`-valued gradient at a local minimiser
  `θ⋆` of `J`: bounded measurable `P₀`-centred `ψ_pool, ψ_val : 𝒵 → ℝ^p` with
  `√n ∇J^iid_{n,m}(θ⋆) − (n^{−1/2} Σ ψ_pool(Z_i) + √n m^{−1} Σ ψ_val(Z̃_i)) → 0` in probability.
* `thm:score`, asymptotic normality, `p` general (`score_asymp_normal_multi`): on a compact `Θ = T ⊆ ℝ^p` with
  `J` uniquely minimised at `θ⋆`, `B(θ⋆, δ) ⊆ T`, `V = ∇²J(θ⋆)` positive definite, the without-replacement
  objective is differentiable at `θ⋆` (eventually), the influence functions of `∇J_{n,m}(θ⋆)` exist (as in Step 2,
  for the without-replacement gradient) and the exact minimisers satisfy
  `√n(θ̂_n − θ⋆) ⇝ N(0, V⁻¹(Σ_pool + κ⁻¹Σ_val)V⁻¹)`, `Σ_· = Cov_{P₀} ψ_·`.
* `cor:inference` (`inference_plugin`): under the same hypotheses, for continuous `φ₁, …, φ_k` and `C¹` `Γ`,
  `T(θ) = Γ(∫φ dμ_θ)` is differentiable at `θ⋆`, and the plug-in from the pool satisfies
  `√n(Γ(∫φ dμ_{θ̂,n}) − T(θ⋆)) ⇝ N(0, σ²_Ψ)` with the printed
  `σ²_Ψ = Var_{P₀}(τ_{θ⋆} − ∇TᵀV⁻¹ψ_pool) + κ⁻¹∇TᵀV⁻¹Σ_val V⁻¹∇T`, the `ψ`'s being influence functions of
  `∇J_{n,m}(θ⋆)` (the linearisation is part of the conclusion, which pins them down `P₀`-a.e.).

Not covered:
* The relabelling representative of `as:interior` (`J` is assumed uniquely minimised on `Θ`, as in Waves 28b/28f).
* Closed forms of `ψ_pool`, `ψ_val` (existential, as printed: "the influence functions").
* Two of the examples listed in `cor:inference`: the effective fraction `e^{−KL(μ | P₀)}` is not of the form
  `Γ(∫φ dμ)` with a fixed `φ` (the supplement's proof uses the pool plug-in `KL(μ_{θ,n} | P_n)`, whose fixed-`θ`
  pool influence function is `g_θ(log g_θ − KL(μ_θ | P₀) − 1)` up to a constant, not the `τ_θ`-form
  `g_θ(log g_θ − KL(μ_θ | P₀))`), and the mass of a region needs an indicator `φ`, which is not continuous (covered
  only for clopen regions).
* The variance-component estimators mentioned after `cor:inference` (finite differences, sample covariances) and the
  computational caveats (`‖∇J_{n,m}(θ̃)‖ = o_P(n^{−1/2})` for computed minimisers): not stated as results.

Encodings (to be checked by the critic):
* Parameter: `θ ∈ ℝ^p = EuclideanSpace ℝ (Fin p)`; `as:smooth`: `s : ℝ^p → 𝒵 → ℝ` with `s₋ ≤ s ≤ s₊` everywhere,
  Fréchet derivatives `s1 = ∂_θ s : ℝ^p → 𝒵 → (ℝ^p)*`, `s2 = ∂_θ s1` on `U` (`HasFDerivAt`), and `s`, `s1`, `s2`
  jointly continuous on `U × 𝒵` (operator-norm topology) — the exact `p`-dimensional analogue of the Wave 28f
  hypotheses (no Lipschitz conditions, no `𝒵 ⊂` Euclidean space). `s` jointly continuous on `T × 𝒵` for consistency.
* `as:kernel`, `as:loss`, sampling, penalties, `m/n → κ`, `√n(λ_{·,n} − λ_·) → 0`: as in Wave 28f.
* Hessian: `hessMat f θ = (D²f(θ)(e_i, e_j))_{ij}` (Mathlib `fderiv` twice); `V⁻¹` is Mathlib's `Matrix.inv`
  (a genuine inverse under the `PosDef` hypothesis); Step 1's uniform law is in operator norm on
  `ℝ^p →L ℝ^p →L ℝ`. Gradients are Mathlib's `gradient` (Riesz representative of `fderiv`).
* Limit law: any `G` with `HasLaw G (multivariateGaussian 0 Σ)` on any probability space, Mathlib's
  `TendstoInDistribution` (weak convergence of the laws on `ℝ^p`).
* `cor:inference`: `Ψ(μ_{θ,n})` is evaluated at the frozen weighted pool law `empCtxLaw s X n θ` (`μ_{θ,n}`), `T` at the
  frozen `ctxLawT P₀ s θ` (`μ_θ`); `φ_r` continuous (bounded since `𝒵` is compact; printed: bounded continuous),
  `Γ` `C¹` on `ℝ^k` (printed: continuously differentiable); `∇Γ` is `fderiv Γ` at `(∫φ_r dμ_{θ⋆})_r` applied to the
  unit vectors.
* Junk values: `hessMat` uses `fderiv`, but Step 1 (whose hypotheses are contained in the normality hypotheses) proves
  `J ∈ C²(U)`, so it is the true Hessian (a junk `0` would contradict `PosDef` for `p ≥ 1`); `gradient` is guarded by
  the `DifferentiableAt` conclusions (and `T` is differentiable at `θ⋆` by the corollary's first conjunct);
  `multivariateGaussian 0 Σ` is the Dirac mass only for non-PSD `Σ`, while here `Σ = V⁻¹AV⁻¹` with `A` a covariance
  combination is PSD (proved in the route); `Matrix.inv` is a genuine inverse (PosDef); `empCtxLaw` at `n = 0` is the
  zero measure (finitely many `n`); `√n/m(n)` at `m(n) = 0` multiplies an empty sum; `normC ≥ s₋ > 0`; the Gaussian
  variances are `≥ 0` before `toNNReal`.

Drafter notes:
* All 4 claims are proved in `Wave29h/Route*.lean`, collected in `Wave29h/Proofs.lean` (kernel dependencies: propext,
  Classical.choice, Quot.sound). Routes: `RouteULLN` (Wave 28f uniform laws of the derivative pieces for a general
  compact parameter set), `RouteSmooth` (`C²` of `J^iid` in `θ ∈ ℝ^p`, directional derivatives = Wave 28f
  one-dimensional formulas along lines, polarisation), `RouteHessianM` (Step 1), `RouteLinearM` (Step 2: the frozen
  Wave 28f `score_linearization` on each coordinate line), `RouteSworM` (smoothness of `jScore`; the certified WaveP1d
  `swor_derivs` along lines), `RouteNormalM`, `RouteMainM` (normality), `RouteInfer{Pieces,ULLN,Delta}`,
  `RouteInference` (`cor:inference`). New library: `Foundations/CLT/MultiZEstimator.lean` (coordinates on `ℝ^p`,
  coercivity from `PosDef`, the multivariate mean-value step `zest_multi_lin`, projections of multivariate Gaussians,
  the Cramér–Wold assembly `asymp_normal_multi_of_lin` on Mathlib's
  `tendstoInDistribution_iff_tendstoInDistribution_inner`), `Foundations/CLT/MultiULLN.lean` (almost-sure uniform
  laws to outer probability over a separable parameter space).

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset Matrix
open scoped ENNReal NNReal Real

namespace StatFormal.Wave29h

open StatFormal.Wave28b

/-- The Hessian matrix in the standard basis of `ℝ^p`: `(∇²f(θ))_{ij} = D²f(θ)(e_i, e_j)`. -/
def hessMat {p : ℕ} (f : EuclideanSpace ℝ (Fin p) → ℝ) (θ : EuclideanSpace ℝ (Fin p)) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun i j => fderiv ℝ (fderiv ℝ f) θ (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

/-- The covariance matrix `Cov_{P₀}(ψ)` of an `ℝ^p`-valued function. -/
def covMat {p : ℕ} {Z : Type*} [MeasurableSpace Z] (P0 : Measure Z) (ψ : Z → EuclideanSpace ℝ (Fin p)) :
    Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun i j => cov[fun z => (ψ z).ofLp i, fun z => (ψ z).ofLp j; P0]


/-- `τ_θ = g_θ ∇Γᵀ(φ − μ_θφ)`, `g_θ = s_θ/P₀s_θ`, `∇Γ` at `μ_θφ = (∫φ_r dμ_θ)_r` (`cor:inference`). -/
def tauInfl {Θ Z : Type*} [MeasurableSpace Z] (P0 : Measure Z) (s : Θ → Z → ℝ) {k : ℕ} (φ : Fin k → Z → ℝ)
    (Γ : (Fin k → ℝ) → ℝ) (θ : Θ) (z : Z) : ℝ :=
  s θ z / StatFormal.Wave24c.normC P0 s θ * ∑ r, fderiv ℝ Γ (fun r => ∫ y, φ r y ∂StatFormal.Wave24c.ctxLawT P0 s θ)
    (Pi.single r 1) * (φ r z - ∫ y, φ r y ∂StatFormal.Wave24c.ctxLawT P0 s θ)

/-- `σ²_Ψ = Var_{P₀}(τ_{θ⋆} − ∇TᵀV⁻¹ψ_pool) + κ⁻¹ ∇TᵀV⁻¹Σ_val V⁻¹∇T` with `T(θ) = Γ(∫φ dμ_θ)`, `V = ∇²J(θ⋆)`. -/
def inferVar {p : ℕ} {Z : Type*} [MeasurableSpace Z] (P0 : Measure Z) (s : EuclideanSpace ℝ (Fin p) → Z → ℝ) {M : ℕ}
    (L : Z → (Fin M → Z) → ℝ) (K : Z → Z → ℝ) (lc lK κ : ℝ) {k : ℕ} (φ : Fin k → Z → ℝ) (Γ : (Fin k → ℝ) → ℝ)
    (θs : EuclideanSpace ℝ (Fin p)) (ψp ψv : Z → EuclideanSpace ℝ (Fin p)) : ℝ :=
  Var[fun z => tauInfl P0 s φ Γ θs z - ((hessMat (jPop P0 s L K lc lK) θs)⁻¹ *ᵥ
      (gradient (fun θ => Γ fun r => ∫ y, φ r y ∂StatFormal.Wave24c.ctxLawT P0 s θ) θs).ofLp) ⬝ᵥ (ψp z).ofLp; P0] +
    κ⁻¹ * (((hessMat (jPop P0 s L K lc lK) θs)⁻¹ *ᵥ
      (gradient (fun θ => Γ fun r => ∫ y, φ r y ∂StatFormal.Wave24c.ctxLawT P0 s θ) θs).ofLp) ⬝ᵥ
      covMat P0 ψv *ᵥ ((hessMat (jPop P0 s L K lc lK) θs)⁻¹ *ᵥ
      (gradient (fun θ => Γ fun r => ∫ y, φ r y ∂StatFormal.Wave24c.ctxLawT P0 s θ) θs).ofLp))

namespace Claims

/-- ICL `thm:score`, normality proof, Step 1, parameter in `ℝ^p`: `J ∈ C²(U)`, every `J^iid_{n,m}` is `C²` on `U`,
and almost surely (one null set for all radii) `∇²J^iid_{n,m} → ∇²J` uniformly (in operator norm) on every closed
ball `B̄(θ⋆, r)`, `r < δ`. -/
def score_hessian_ulln_multi : Prop :=
  ∀ (p M : ℕ) (sm sp Kmin Kmax lc lK δ : ℝ) (θs : EuclideanSpace ℝ (Fin p)) (Z Ω : Type) [MetricSpace Z]
    [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (P0 : Measure Z) (X Y : ℕ → Ω → Z) (m : ℕ → ℕ) (s : EuclideanSpace ℝ (Fin p) → Z → ℝ)
    (s1 : EuclideanSpace ℝ (Fin p) → Z → EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ)
    (s2 : EuclideanSpace ℝ (Fin p) → Z → EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ)
    (L : Z → (Fin M → Z) → ℝ) (K : Z → Z → ℝ) (lcn lKn : ℕ → ℝ),
    1 ≤ M → 0 < sm → (∀ t x, sm ≤ s t x ∧ s t x ≤ sp) → 0 < δ →
    ContinuousOn (Function.uncurry s) (Metric.ball θs δ ×ˢ univ) →
    ContinuousOn (Function.uncurry s1) (Metric.ball θs δ ×ˢ univ) →
    ContinuousOn (Function.uncurry s2) (Metric.ball θs δ ×ˢ univ) →
    (∀ x, ∀ t ∈ Metric.ball θs δ, HasFDerivAt (fun t => s t x) (s1 t x) t ∧
      HasFDerivAt (fun t => s1 t x) (s2 t x) t) →
    Continuous (Function.uncurry L) → Continuous (Function.uncurry K) → 0 < Kmin →
    (∀ x y, Kmin ≤ K x y ∧ K x y ≤ Kmax) →
    (∀ i, Measurable (X i)) → iIndepFun X P → (∀ i, P.map (X i) = P0) →
    (∀ i, Measurable (Y i)) → iIndepFun Y P → (∀ i, P.map (Y i) = P0) →
    Tendsto m atTop atTop → Tendsto lcn atTop (𝓝 lc) → Tendsto lKn atTop (𝓝 lK) →
      ContDiffOn ℝ 2 (jPop P0 s L K lc lK) (Metric.ball θs δ) ∧
      (∀ n ω, ContDiffOn ℝ 2 (jScoreIid s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n))
        (Metric.ball θs δ)) ∧
      ∀ᵐ ω ∂P, ∀ r, r < δ →
        TendstoUniformlyOn
          (fun n => fderiv ℝ (fderiv ℝ (jScoreIid s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n))))
          (fderiv ℝ (fderiv ℝ (jPop P0 s L K lc lK))) atTop (Metric.closedBall θs r)

/-- ICL `thm:score`, normality proof, Step 2 (`eq:e-linear` times `√n`), parameter in `ℝ^p`: the i.i.d.-context
gradient at a local minimiser `θ⋆` of `J` is asymptotically linear in the pool and the validation sample, with
bounded measurable centred `ℝ^p`-valued influence functions (every `J^iid_{n,m}` is differentiable at `θ⋆`). -/
def score_linearization_multi : Prop :=
  ∀ (p M : ℕ) (sm sp Kmin Kmax κ lc lK δ : ℝ) (θs : EuclideanSpace ℝ (Fin p)) (Z Ω : Type) [MetricSpace Z]
    [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (P0 : Measure Z) (X Y : ℕ → Ω → Z) (m : ℕ → ℕ) (s : EuclideanSpace ℝ (Fin p) → Z → ℝ)
    (s1 : EuclideanSpace ℝ (Fin p) → Z → EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ)
    (s2 : EuclideanSpace ℝ (Fin p) → Z → EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ)
    (L : Z → (Fin M → Z) → ℝ) (K : Z → Z → ℝ) (lcn lKn : ℕ → ℝ),
    1 ≤ M → 0 < sm → (∀ t x, sm ≤ s t x ∧ s t x ≤ sp) → 0 < δ →
    ContinuousOn (Function.uncurry s) (Metric.ball θs δ ×ˢ univ) →
    ContinuousOn (Function.uncurry s1) (Metric.ball θs δ ×ˢ univ) →
    ContinuousOn (Function.uncurry s2) (Metric.ball θs δ ×ˢ univ) →
    (∀ x, ∀ t ∈ Metric.ball θs δ, HasFDerivAt (fun t => s t x) (s1 t x) t ∧
      HasFDerivAt (fun t => s1 t x) (s2 t x) t) →
    Continuous (Function.uncurry L) → Continuous (Function.uncurry K) → 0 < Kmin →
    (∀ x y, Kmin ≤ K x y ∧ K x y ≤ Kmax) →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X P → iIndepFun Y P →
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) P → (∀ i, P.map (X i) = P0) → (∀ i, P.map (Y i) = P0) →
    0 < κ → Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ) →
    Tendsto lcn atTop (𝓝 lc) → Tendsto lKn atTop (𝓝 lK) →
    Tendsto (fun n : ℕ => √(n : ℝ) * (lcn n - lc)) atTop (𝓝 0) →
    Tendsto (fun n : ℕ => √(n : ℝ) * (lKn n - lK)) atTop (𝓝 0) →
    (∀ t ∈ Metric.ball θs δ, jPop P0 s L K lc lK θs ≤ jPop P0 s L K lc lK t) →
      (∀ n ω, DifferentiableAt ℝ (jScoreIid s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n)) θs) ∧
      ∃ ψp ψv : Z → EuclideanSpace ℝ (Fin p), Measurable ψp ∧ Measurable ψv ∧
        (∃ C, ∀ z, ‖ψp z‖ ≤ C ∧ ‖ψv z‖ ≤ C) ∧ ∫ z, ψp z ∂P0 = 0 ∧ ∫ z, ψv z ∂P0 = 0 ∧
        TendstoInMeasure P (fun (n : ℕ) ω =>
          √(n : ℝ) • gradient (jScoreIid s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n)) θs -
            ((√(n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, ψp (X i ω) +
              (√(n : ℝ) / m n) • ∑ i ∈ Finset.range (m n), ψv (Y i ω))) atTop 0

/-- ICL `thm:score`, asymptotic normality, parameter in `ℝ^p`: on a compact `Θ ⊆ ℝ^p` with `J` uniquely minimised
at the interior `θ⋆` and `V = ∇²J(θ⋆)` positive definite, there are bounded measurable centred influence functions
`ψ_pool`, `ψ_val` of the without-replacement gradient `∇J_{n,m}(θ⋆)`, and the exact minimisers `θ̂_n` of `J_{n,m}`
satisfy `√n(θ̂_n − θ⋆) ⇝ N(0, V⁻¹(Σ_pool + κ⁻¹Σ_val)V⁻¹)`, `Σ_· = Cov_{P₀} ψ_·`. -/
def score_asymp_normal_multi : Prop :=
  ∀ (p M : ℕ) (sm sp BL Kmin Kmax κ lc lK δ : ℝ) (θs : EuclideanSpace ℝ (Fin p))
    (T : Set (EuclideanSpace ℝ (Fin p))) (Z Ω : Type) [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (P0 : Measure Z) (X Y : ℕ → Ω → Z)
    (m : ℕ → ℕ) (s : EuclideanSpace ℝ (Fin p) → Z → ℝ)
    (s1 : EuclideanSpace ℝ (Fin p) → Z → EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ)
    (s2 : EuclideanSpace ℝ (Fin p) → Z → EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ)
    (L : Z → (Fin M → Z) → ℝ) (K : Z → Z → ℝ) (lcn lKn : ℕ → ℝ) (θh : ℕ → Ω → EuclideanSpace ℝ (Fin p)),
    1 ≤ M → 0 < sm → (∀ t x, sm ≤ s t x ∧ s t x ≤ sp) → IsCompact T →
    ContinuousOn (Function.uncurry s) (T ×ˢ univ) → 0 < δ → Metric.ball θs δ ⊆ T →
    ContinuousOn (Function.uncurry s1) (Metric.ball θs δ ×ˢ univ) →
    ContinuousOn (Function.uncurry s2) (Metric.ball θs δ ×ˢ univ) →
    (∀ x, ∀ t ∈ Metric.ball θs δ, HasFDerivAt (fun t => s t x) (s1 t x) t ∧
      HasFDerivAt (fun t => s1 t x) (s2 t x) t) →
    Continuous (Function.uncurry L) → (∀ x t, 0 ≤ L x t ∧ L x t ≤ BL) →
    (∀ x t (σ : Equiv.Perm (Fin M)), L x (t ∘ σ) = L x t) →
    Continuous (Function.uncurry K) → 0 < Kmin → (∀ x y, Kmin ≤ K x y ∧ K x y ≤ Kmax) →
    (∀ n, 0 ≤ lcn n) → Tendsto lcn atTop (𝓝 lc) → Tendsto lKn atTop (𝓝 lK) →
    Tendsto (fun n : ℕ => √(n : ℝ) * (lcn n - lc)) atTop (𝓝 0) →
    Tendsto (fun n : ℕ => √(n : ℝ) * (lKn n - lK)) atTop (𝓝 0) →
    0 < κ → Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ) →
    (∀ θ ∈ T, (∀ θ' ∈ T, jPop P0 s L K lc lK θ ≤ jPop P0 s L K lc lK θ') → θ = θs) →
    (hessMat (jPop P0 s L K lc lK) θs).PosDef →
    (∀ n, Measurable (θh n)) →
    (∀ n ω, θh n ω ∈ T ∧ ∀ t ∈ T, jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n)
      (lKn n) (θh n ω) ≤ jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n) t) →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X P → iIndepFun Y P →
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) P → (∀ i, P.map (X i) = P0) → (∀ i, P.map (Y i) = P0) →
      (∀ᶠ n in atTop, ∀ ω, DifferentiableAt ℝ
        (jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n)) θs) ∧
      ∃ ψp ψv : Z → EuclideanSpace ℝ (Fin p), Measurable ψp ∧ Measurable ψv ∧
        (∃ C, ∀ z, ‖ψp z‖ ≤ C ∧ ‖ψv z‖ ≤ C) ∧ ∫ z, ψp z ∂P0 = 0 ∧ ∫ z, ψv z ∂P0 = 0 ∧
        TendstoInMeasure P (fun (n : ℕ) ω =>
          √(n : ℝ) • gradient (jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n)) θs -
            ((√(n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, ψp (X i ω) +
              (√(n : ℝ) / m n) • ∑ i ∈ Finset.range (m n), ψv (Y i ω))) atTop 0 ∧
        ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
          (G : Ω' → EuclideanSpace ℝ (Fin p)),
          HasLaw G (multivariateGaussian 0 ((hessMat (jPop P0 s L K lc lK) θs)⁻¹ *
            (covMat P0 ψp + κ⁻¹ • covMat P0 ψv) * (hessMat (jPop P0 s L K lc lK) θs)⁻¹)) P' →
          TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) • (θh n ω - θs)) atTop G (fun _ => P) P'

/-- ICL `cor:inference`: under the hypotheses of `thm:score` (as in `score_asymp_normal_multi`), for
`Ψ(μ) = Γ(∫φ₁ dμ, …, ∫φ_k dμ)` with continuous (hence bounded) `φ_r` and `C¹` `Γ`, `T(θ) = Ψ(μ_θ)` is differentiable at
`θ⋆`, and with the influence functions `ψ_pool`, `ψ_val` of `∇J_{n,m}(θ⋆)` the plug-in `Ψ(μ_{θ̂,n})` computed from the
pool satisfies `√n(Ψ(μ_{θ̂,n}) − T(θ⋆)) ⇝ N(0, σ²_Ψ)`, `σ²_Ψ = Var_{P₀}(τ_{θ⋆} − ∇TᵀV⁻¹ψ_pool) +
κ⁻¹∇TᵀV⁻¹Σ_val V⁻¹∇T`. -/
def inference_plugin : Prop :=
  ∀ (p M : ℕ) (sm sp BL Kmin Kmax κ lc lK δ : ℝ) (θs : EuclideanSpace ℝ (Fin p))
    (T : Set (EuclideanSpace ℝ (Fin p))) (Z Ω : Type) [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (P0 : Measure Z) (X Y : ℕ → Ω → Z)
    (m : ℕ → ℕ) (s : EuclideanSpace ℝ (Fin p) → Z → ℝ)
    (s1 : EuclideanSpace ℝ (Fin p) → Z → EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ)
    (s2 : EuclideanSpace ℝ (Fin p) → Z → EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ)
    (L : Z → (Fin M → Z) → ℝ) (K : Z → Z → ℝ) (lcn lKn : ℕ → ℝ) (θh : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (k : ℕ) (φ : Fin k → Z → ℝ) (Γ : (Fin k → ℝ) → ℝ),
    (∀ r, Continuous (φ r)) → ContDiff ℝ 1 Γ →
    1 ≤ M → 0 < sm → (∀ t x, sm ≤ s t x ∧ s t x ≤ sp) → IsCompact T →
    ContinuousOn (Function.uncurry s) (T ×ˢ univ) → 0 < δ → Metric.ball θs δ ⊆ T →
    ContinuousOn (Function.uncurry s1) (Metric.ball θs δ ×ˢ univ) →
    ContinuousOn (Function.uncurry s2) (Metric.ball θs δ ×ˢ univ) →
    (∀ x, ∀ t ∈ Metric.ball θs δ, HasFDerivAt (fun t => s t x) (s1 t x) t ∧
      HasFDerivAt (fun t => s1 t x) (s2 t x) t) →
    Continuous (Function.uncurry L) → (∀ x t, 0 ≤ L x t ∧ L x t ≤ BL) →
    (∀ x t (σ : Equiv.Perm (Fin M)), L x (t ∘ σ) = L x t) →
    Continuous (Function.uncurry K) → 0 < Kmin → (∀ x y, Kmin ≤ K x y ∧ K x y ≤ Kmax) →
    (∀ n, 0 ≤ lcn n) → Tendsto lcn atTop (𝓝 lc) → Tendsto lKn atTop (𝓝 lK) →
    Tendsto (fun n : ℕ => √(n : ℝ) * (lcn n - lc)) atTop (𝓝 0) →
    Tendsto (fun n : ℕ => √(n : ℝ) * (lKn n - lK)) atTop (𝓝 0) →
    0 < κ → Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ) →
    (∀ θ ∈ T, (∀ θ' ∈ T, jPop P0 s L K lc lK θ ≤ jPop P0 s L K lc lK θ') → θ = θs) →
    (hessMat (jPop P0 s L K lc lK) θs).PosDef →
    (∀ n, Measurable (θh n)) →
    (∀ n ω, θh n ω ∈ T ∧ ∀ t ∈ T, jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n)
      (lKn n) (θh n ω) ≤ jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n) t) →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X P → iIndepFun Y P →
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) P → (∀ i, P.map (X i) = P0) → (∀ i, P.map (Y i) = P0) →
      DifferentiableAt ℝ (fun θ => Γ fun r => ∫ z, φ r z ∂StatFormal.Wave24c.ctxLawT P0 s θ) θs ∧
      ∃ ψp ψv : Z → EuclideanSpace ℝ (Fin p), Measurable ψp ∧ Measurable ψv ∧
        (∃ C, ∀ z, ‖ψp z‖ ≤ C ∧ ‖ψv z‖ ≤ C) ∧ ∫ z, ψp z ∂P0 = 0 ∧ ∫ z, ψv z ∂P0 = 0 ∧
        TendstoInMeasure P (fun (n : ℕ) ω =>
          √(n : ℝ) • gradient (jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n)) θs -
            ((√(n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, ψp (X i ω) +
              (√(n : ℝ) / m n) • ∑ i ∈ Finset.range (m n), ψv (Y i ω))) atTop 0 ∧
        ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P'] (G : Ω' → ℝ),
          HasLaw G (gaussianReal 0 (inferVar P0 s L K lc lK κ φ Γ θs ψp ψv).toNNReal) P' →
          TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) *
            ((Γ fun r => ∫ z, φ r z ∂StatFormal.Wave24c.empCtxLaw s (fun i => X i ω) n (θh n ω)) -
              Γ fun r => ∫ z, φ r z ∂StatFormal.Wave24c.ctxLawT P0 s θs)) atTop G (fun _ => P) P'

end Claims

end StatFormal.Wave29h
