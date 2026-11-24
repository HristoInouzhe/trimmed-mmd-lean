import StatFormal.Archive.Wave28b.Statements
import StatFormal.Archive.Wave29h.Statements
import StatFormal.Archive.Wave29t.Statements
import StatFormal.Archive.Wave29g.Statements
import StatFormal.Archive.Wave25a.Statements

/-!
# FROZEN STATEMENTS — wave 29y: ICL `thm:score` modulo a finite relabelling group (the representative of
# `as:interior`: consistency and asymptotic normality of the closest relabelling); SB `lem:dplan` + `prop:mixture`
# in `ℝᵈ` with general covariances on path space (`eq:gaussmarg` in `ℝᵈ`) and the `ℝᵈ` path-space discharges of
# `thm:paritydefect` / `prop:corrected`

Sources (current text read 2026-10-20):
* ICL `context-distribution-ICL/paper/v3/`: `thm:score` (`sections/06_estimation.tex:137-148`: "the minimizer closest
  to `θ⋆` among its relabelings satisfies `√n(θ̂ − θ⋆) ⇝ N(0, V⁻¹(Σ_pool + κ⁻¹Σ_val)V⁻¹)`"); supplement
  `supp/proofs_score.tex`: `as:compact`–`as:interior` (`:14-46`; `as:interior`: "every minimizer of `J` is obtained
  from `θ⋆` by a relabeling symmetry of the parametrization"), the remark after `as:interior` (`:46-48`: "the
  relabeling of `θ̂_{n,m}` closest to `θ⋆` converges to `θ⋆` almost surely. This is the representative used in the
  normality part"), Step 4 of the normality proof (`:281-296`: "Take `θ̂_{n,m}` to be the relabeling closest to `θ⋆`").
* SB `data-fairness-repair/schrodinger_bridge_fairness_repair.tex`: `sec:schrodinger` (`:374-393`, `eq:dynamic`),
  `def:repair` (`:438-446`: `μ^ε_{s,t} = Law_{P*_ε(R_s,ν)}(X_t)`), `prop:mixture` (`:458-473`, in `ℝᵈ`),
  `eq:threeops` (`:654-662`: `T^ε_{s,t}(X) = E[X_t | X₀ = X]`), `lem:dplan` (`:671-697`: `π*_ε(N(m₀,A), N(m₁,B))` is
  Gaussian with cross-covariance `C_ε(A,B)`), `thm:paritydefect` (`:712-730`: `T^ε_s = T^ε_{s,1}` is linear with
  matrix `C_sᵀA_s⁻¹`, push-forward covariance `P_s = C_sᵀA_s⁻¹C_s`), `prop:corrected` (`:840-851`: "if `R₀, R₁` and `ν`
  are Gaussian, `(T̃^ε_s)_# R_s = ν`"); `lem:gaussplan` (`:2223-2240`) and `thm:gaussian` / `eq:gaussmarg`
  (`:2537-2575`), `prop:noisefree` (`:1617-1631`) — the last three printed for SCALAR Gaussians only.
Imports the frozen `Wave28b` (`jScore`, `jPop`, the `score_argmin_*` claims), `Wave29h` (`hessMat`, `covMat`,
`score_asymp_normal_multi`), `Wave29t` (`IsBrownianRefD`, `IsSchrodingerBridgeD`, `mixtureD_uncond`), `Wave29g`
(`jointGauss`, `affD`, `IsEntPlanD`, `dplan_*`, `corrected_gaussian_eot`; through it `SBFairness/DPlan` `Cmat`) and
`Wave25a` (`meanV`, `covM`, `corrMap`) statements, not copied; Mathlib (`multivariateGaussian`, `MulAction`,
`Isometry`, `TendstoInDistribution`) otherwise. New definitions: `IsClosestRelabel`, `bridgeCovD`. Libraries (new):
`Foundations/RelabelSelect.lean`, `Foundations/GaussianDensityD.lean` (the Lebesgue density of `N(m, B)`, `B ≻ 0`,
which Mathlib lacks), `Foundations/GaussianInterpD.lean`.

Covered:
* ICL, the relabelling representative (frozen Waves 28b/28f/29h assume a UNIQUE minimiser):
  `score_relabel_select` (a measurable closest-relabelling selection `r : Θ → Θ` exists for every finite group acting
  continuously on a metric space; so the representative of a measurable `θ̂` is measurable);
  `score_relabel_cons` (consistency of the representative: under the hypotheses of the frozen `score_argmin_discharged`,
  if every minimiser of `J` is `g • θ⋆` for some `g` in a finite group `G` acting continuously on `Θ`, then ANY
  closest relabelling `θ̃_n ∈ G·θ̂_n` of the `ε_n`-minimisers converges to `θ⋆` almost surely);
  `score_relabel_normal` (`thm:score` normality modulo `G`, `θ ∈ ℝ^p`: under the hypotheses of the frozen
  `score_asymp_normal_multi` with the uniqueness premise replaced by `as:interior` modulo `G` — every minimiser of `J`
  on `T` is a relabelling of `θ⋆` — for a finite group `G` acting continuously on `ℝ^p`, the stabiliser of `θ⋆` acting
  by isometries, preserving `T` and the score family, the measurable closest relabellings `θ̃_n` of the exact minimisers are themselves exact minimisers of
  `J_{n,m}` over `T` and `√n(θ̃_n − θ⋆) ⇝ N(0, V⁻¹(Σ_pool + κ⁻¹Σ_val)V⁻¹)`, with the influence functions of
  `∇J_{n,m}(θ⋆)` as in the frozen claim).
* SB, `ℝᵈ` Gaussian case on path space (the `ℝᵈ` analogue of the frozen Wave 29q `mixture_gauss`; the gap declared by
  Wave 29t): `mixtureD_gauss` (for `μ = N(m₀, A)`, `ν = N(m₁, B)`, `A, B ≻ 0`, `ε > 0` and every `ε`-Brownian
  reference on `ℝᵈ`: `P*_ε` exists and is unique, its endpoint law is the frozen Wave 29g Gaussian plan
  `N((m₀,m₁), [[A, C], [Cᵀ, B]])`, `C = C_ε(A,B)`, and for every `t ∈ [0,1]` the time-`t` law is the Gaussian
  `N((1−t)m₀ + tm₁, (1−t)²A + t²B + t(1−t)(C + Cᵀ) + εt(1−t)I)` with positive definite covariance — `eq:gaussmarg` in
  `ℝᵈ`; at `d = 1`, `C + Cᵀ + εI = 2c_ε + ε = κ_ε` and this is `v_s(t)`).
* SB, `ℝᵈ` PATH-SPACE DISCHARGES (the plan-level frozen Wave 29g claims, with `π*_ε` replaced by the endpoint law of
  an arbitrary Schrödinger bridge `P = P*_ε(R_s, ν)` relative to an arbitrary `ε`-Brownian reference on `ℝᵈ`, and the
  barycentric projection read on path space, `T^ε_s(x) = E_P[X₁ | X₀ = x]` as in `eq:threeops`):
  `gaussplanD_barycentric_path` (`thm:paritydefect`: `E_P[X₁ | X₀ = x] = m₁ + CᵀA⁻¹(x − m₀)` and it pushes `R_s` to
  `N(m₁, CᵀA⁻¹C)`), `gaussplanD_corrected_path` (`prop:corrected`: any integrable version `T` of `E_P[X₁ | X₀]`
  gives the corrected map `x ↦ m_ν + V_ν^{1/2}P^{−1/2}(T(x) − E T)` pushing `R_s` onto `ν`).

Not covered (declared):
* ICL: in the normality claim, a relabelling group whose stabiliser of `θ⋆` contains a non-isometric map (the claim
  covers every continuous action with trivial stabiliser of `θ⋆` — e.g. the relabellings of the supplement's mixture
  example at distinct components, which in the chart `α = softmax(a)`, `a₁ = 0` are affine but NOT isometric for
  `R ≥ 3` — and every isometric action); a relabelling group not preserving `T` (the paper's `s_θ` is defined on `Θ`
  only, so its relabellings are maps of `Θ`); symmetries with `s_{g•θ} = c·s_θ`, `c ≠ 1` (`J`, `J_{n,m}` depend on
  `s_θ` only through `g_θ`, `w(θ)`, so they also qualify; specialised to `c = 1`); the one-dimensional frozen Wave 28f form (the
  `ℝ^p` claim at `p = 1` covers `Θ ⊆ ℝ ≅ EuclideanSpace ℝ (Fin 1)`); `cor:inference` modulo `G` (not attempted).
* SB `thm:gaussian`, `eq:gaussF`, (a)–(d) and `prop:noisefree` in `d ≥ 2`: NOT APPLICABLE — printed for scalar
  Gaussians only (`σ_s`, `τ`, `κ_{ε,s}`, `W₂` between scalar Gaussians); their `d = 1` path forms are the frozen Wave 29q
  `*_path` claims. `lem:gaussplan` (scalar) is the frozen Wave 29q `mixture_gauss`. No `ℝᵈ` statement of them exists in
  the paper.
* SB: the barycentric projection `T^ε_{s,t}` at `t < 1` (only `t = 1` is printed in `thm:paritydefect`).
* Existence of Wiener measure on `C([0,1]; ℝᵈ)`: as in Waves 29q/29t, the claims quantify over every `(Ω, X, R)` with
  the three-time laws of `X₀ + √ε B`; non-vacuity is the Wave 29t route lemma `isBrownianRefD_witness` (every
  probability `μ`, in particular `N(m₀, A)`).

Encodings (to be checked by the critic):
* Relabelling group: `G` a finite group (`Group G`, `Fintype G`) acting on `Θ` (`MulAction G Θ`). For consistency the
  action is continuous (`ContinuousConstSMul G Θ`) and NO invariance of `J` is assumed (a generalisation: only the
  orbit structure of the minimiser set is used); for normality on `Θ = T ⊆ ℝ^p` each `θ ↦ g • θ` is continuous, those
  fixing `θ⋆` are isometries (automatic if the stabiliser of `θ⋆` is trivial or `G` acts isometrically), `T` is
  `G`-stable and the score family is `G`-invariant on `T` (`s_{g•θ} = s_θ`: "a relabeling symmetry of the
  parametrization"), which makes every `J_{n,m}` `G`-invariant on `T` (proved in the route).
* "`θ̃` is the relabelling of `θ` closest to `θ⋆`" (`IsClosestRelabel G θs θ θ̃`): `θ̃ = g • θ` for some `g` and
  `d(θ̃, θ⋆) ≤ d(g • θ, θ⋆)` for every `g` (ties allowed: ANY closest relabelling, stated for every selection);
  `score_relabel_select` shows a measurable selection exists (`r ∘ θ̂` is then measurable).
* `as:interior` modulo `G`: every minimiser of `J` (on `Θ` for consistency, on `T` for normality) is `g • θ⋆` for some
  `g`. That `θ⋆` itself minimises `J` ("`J` has a minimizer `θ⋆`") is not assumed: consistency does not need it (nor
  any invariance of `J`); for normality it is proved — `J` attains its minimum on `T` (frozen `score_argmin_discharged`)
  at some `g • θ⋆`, and `J(g • θ⋆) = J(θ⋆)` by invariance of the score family. All other hypotheses are those of the
  frozen `score_argmin_discharged` resp. `score_asymp_normal_multi`, verbatim; the uniqueness premise
  `∀ θ, (θ minimises J) → θ = θ⋆` is exactly the orbit premise for the trivial group, so with `G` trivial
  (`θ̃_n = θ̂_n`) the claims imply the frozen `score_argmin_unique` / `score_asymp_normal_multi` (checked in Lean:
  `RouteRelabel.relabel_cons_implies_frozen`, `RouteRelabel.relabel_normal_implies_frozen`).
* SB objects: the frozen Wave 29t `IsBrownianRefD`, `IsSchrodingerBridgeD` and Wave 29g `jointGauss`, `affD`, `Cmat`
  (with the frozen hypotheses on `S = A^{1/2}`, `N = (4SBS + ε²I)^{1/2}` copied verbatim from `dplan_eot`);
  `N(m, Σ) = multivariateGaussian m Σ`. `bridgeCovD A B C ε t = (1−t)²A + t²B + t(1−t)(C + Cᵀ) + εt(1−t)I` (the
  covariance of `(1−t)X₀ + tX₁ + √(εt(1−t)) Z`; `C` need not be symmetric — the paper proves `BC` symmetric).
* Path barycentric projection: the defining identity `E_P[X₁ⱼ h(X₀)] = ∫ T(x)ⱼ h(x) dR_s` against bounded measurable `h`
  (as in the frozen `dplan_barycentric`, `corrected_gaussian_eot`), with integrability asserted.
* Junk values: `multivariateGaussian m Σ` is a Dirac mass for non-PSD `Σ` — the time-`t` covariance is ASSERTED positive
  definite; `Matrix.inv` of the PD matrices `A`, `V` (frozen `hessMat` PosDef) is a genuine inverse; no `Measure.map` of
  a non-measurable map (`X t` measurable by `IsBrownianRefD`, `affD`, `corrMap` continuous/affine); `√(εt(1−t))` of a
  nonnegative number; the Gaussian variance of the ICL limit as in the frozen claim.

Drafter notes:
* All 6 claims are proved in `Wave29y/Route{Relabel,GaussD}.lean`, collected in `Wave29y/Proofs.lean` (kernel
  dependencies: propext, Classical.choice, Quot.sound). Routes reuse the certified frozen Wave 28b
  `score_argmin_discharged`, Wave 29h `score_asymp_normal_multi` (applied on the Dirichlet domain
  `D = {θ ∈ T : d(θ, θ⋆) ≤ d(gθ, θ⋆) ∀g}`, compact, containing a ball around `θ⋆`, on which `θ⋆` is the unique
  minimiser and which contains every closest relabelling), Wave 29t `mixtureD_uncond` and Wave 29g `dplan_eot`,
  `dplan_barycentric`, `corrected_gaussian_eot`.
* New library: `Foundations/RelabelSelect.lean` (measurable closest-relabelling selection by a finite fold;
  convergence of closest relabellings when all cluster points lie in one orbit), `Foundations/GaussianDensityD.lean`
  (`multivariateGaussian_eq_withDensity`: `N(m,B) = Leb.withDensity(((2π)ᵈ det B)^{−1/2} e^{−½(y−m)ᵀB⁻¹(y−m)})`,
  via `map_linearMap_addHaar_eq_smul_addHaar`, `Matrix.PosSemidef.det_sqrt`; integrability of `log` of the density and
  of `‖y‖²`), `Foundations/GaussianInterpD.lean` (`interp_gauss`: the law of `(1−t)X₀ + tX₁ + √s Z` for a joint Gaussian
  `(X₀, X₁)`, characteristic functions; positive definiteness of its covariance).

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset Matrix
open scoped ENNReal NNReal Real

namespace StatFormal.Wave29y

open StatFormal.Wave28b (jScore jPop)
open StatFormal.Wave29h (hessMat covMat)
open StatFormal.Wave29t (IsBrownianRefD IsSchrodingerBridgeD)
open StatFormal.Wave29g (jointGauss affD)
open StatFormal.SBFairness.DPlan (Cmat)

local notation "E" d => EuclideanSpace ℝ (Fin d)

/-- `θ'` is a relabelling of `θ` closest to `θ⋆`: `θ' = g • θ` for some `g ∈ G` and `d(θ', θ⋆) ≤ d(g • θ, θ⋆)` for all
`g ∈ G`. -/
def IsClosestRelabel (G : Type*) {Θ : Type*} [SMul G Θ] [Dist Θ] (θs θ θ' : Θ) : Prop :=
  (∃ g : G, θ' = g • θ) ∧ ∀ g : G, dist θ' θs ≤ dist (g • θ) θs

/-- The covariance of `(1−t)X₀ + tX₁ + √(εt(1−t)) Z` for `(X₀, X₁)` with covariance `[[A, C], [Cᵀ, B]]` and `Z ∼ N(0, I)`
independent: `(1−t)²A + t²B + t(1−t)(C + Cᵀ) + εt(1−t)I`. -/
def bridgeCovD {d : ℕ} (A B C : Matrix (Fin d) (Fin d) ℝ) (ε t : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (1 - t) ^ 2 • A + t ^ 2 • B + (t * (1 - t)) • (C + Cᵀ) + (ε * t * (1 - t)) • (1 : Matrix (Fin d) (Fin d) ℝ)

namespace Claims

/-! ### ICL `thm:score` modulo a finite relabelling group -/

/-- The measurable representative: for a finite group acting continuously on a metric space, there is a measurable
map `r` choosing, for every `θ`, a relabelling of `θ` closest to `θ⋆`. -/
def score_relabel_select : Prop :=
  ∀ (Θ G : Type) [MetricSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ] [Group G] [Fintype G] [MulAction G Θ]
    [ContinuousConstSMul G Θ] (θs : Θ),
    ∃ r : Θ → Θ, Measurable r ∧ ∀ θ, IsClosestRelabel G θs θ (r θ)

/-- ICL `thm:score`, consistency of the representative (remark after `as:interior`): under the hypotheses of the
frozen `score_argmin_discharged`, if every minimiser of `J` is a relabelling `g • θ⋆` (`G` finite, acting
continuously), then every closest relabelling `θ̃_n` of the `ε_n`-minimisers `θ̂_n` converges to `θ⋆` almost surely. -/
def score_relabel_cons : Prop :=
  ∀ (Θ Z Ω G : Type) [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MetricSpace Z] [CompactSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [MeasurableSpace Ω] [Group G] [Fintype G] [MulAction G Θ]
    [ContinuousConstSMul G Θ] (P : Measure Ω) (P0 : Measure Z) (M : ℕ)
    (X Y : ℕ → Ω → Z) (m : ℕ → ℕ) (s : Θ → Z → ℝ) (L : Z → (Fin M → Z) → ℝ) (K : Z → Z → ℝ)
    (sm sp BL Kmin Kmax lc lK : ℝ) (lcn lKn : ℕ → ℝ) (θn : ℕ → Ω → Θ) (εn : ℕ → Ω → ℝ) (θs : Θ)
    (θr : ℕ → Ω → Θ),
    IsProbabilityMeasure P → IsProbabilityMeasure P0 → 1 ≤ M →
    Continuous (Function.uncurry s) → 0 < sm → (∀ θ z, sm ≤ s θ z ∧ s θ z ≤ sp) →
    Continuous (Function.uncurry K) → 0 < Kmin → (∀ z z', Kmin ≤ K z z' ∧ K z z' ≤ Kmax) →
    Continuous (Function.uncurry L) → (∀ z t, 0 ≤ L z t ∧ L z t ≤ BL) →
    (∀ z t (σ : Equiv.Perm (Fin M)), L z (t ∘ σ) = L z t) →
    (∀ j, Measurable (X j)) → iIndepFun X P → (∀ j, P.map (X j) = P0) →
    (∀ j, Measurable (Y j)) → iIndepFun Y P → (∀ j, P.map (Y j) = P0) →
    Tendsto m atTop atTop → (∀ n, 0 ≤ lcn n) → Tendsto lcn atTop (𝓝 lc) → Tendsto lKn atTop (𝓝 lK) →
    (∀ᵐ ω ∂P, Tendsto (fun n => εn n ω) atTop (𝓝 0)) →
    (∀ᵐ ω ∂P, ∀ n θ, jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n) (θn n ω) ≤
      jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n) θ + εn n ω) →
    (∀ θ, (∀ θ', jPop P0 s L K lc lK θ ≤ jPop P0 s L K lc lK θ') → ∃ g : G, θ = g • θs) →
    (∀ n ω, IsClosestRelabel G θs (θn n ω) (θr n ω)) →
      ∀ᵐ ω ∂P, Tendsto (fun n => θr n ω) atTop (𝓝 θs)

/-- ICL `thm:score`, asymptotic normality modulo a finite relabelling group, parameter in `ℝ^p`: under the hypotheses
of the frozen `score_asymp_normal_multi`, with uniqueness of the minimiser replaced by `as:interior` (every minimiser of
`J` on `T` is a relabelling of `θ⋆`) for a finite group acting continuously on `ℝ^p`, preserving `T` and the score
family, whose elements fixing `θ⋆` act by isometries, the measurable closest relabellings `θ̃_n` of the exact minimisers `θ̂_n` are exact minimisers of
`J_{n,m}` over `T`, and `√n(θ̃_n − θ⋆) ⇝ N(0, V⁻¹(Σ_pool + κ⁻¹Σ_val)V⁻¹)` with bounded measurable centred influence
functions `ψ_pool`, `ψ_val` of `∇J_{n,m}(θ⋆)`, `Σ_· = Cov_{P₀} ψ_·`. -/
def score_relabel_normal : Prop :=
  ∀ (p M : ℕ) (sm sp BL Kmin Kmax κ lc lK δ : ℝ) (θs : EuclideanSpace ℝ (Fin p))
    (T : Set (EuclideanSpace ℝ (Fin p))) (Z Ω G : Type) [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] [MeasurableSpace Ω] [Group G] [Fintype G] [MulAction G (EuclideanSpace ℝ (Fin p))]
    (P : Measure Ω) [IsProbabilityMeasure P] (P0 : Measure Z) (X Y : ℕ → Ω → Z)
    (m : ℕ → ℕ) (s : EuclideanSpace ℝ (Fin p) → Z → ℝ)
    (s1 : EuclideanSpace ℝ (Fin p) → Z → EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ)
    (s2 : EuclideanSpace ℝ (Fin p) → Z → EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ)
    (L : Z → (Fin M → Z) → ℝ) (K : Z → Z → ℝ) (lcn lKn : ℕ → ℝ) (θh θr : ℕ → Ω → EuclideanSpace ℝ (Fin p)),
    (∀ g : G, Continuous (fun θ : EuclideanSpace ℝ (Fin p) => g • θ)) →
    (∀ g : G, g • θs = θs → Isometry (fun θ : EuclideanSpace ℝ (Fin p) => g • θ)) → (∀ g : G, ∀ θ ∈ T, g • θ ∈ T) →
    (∀ g : G, ∀ θ ∈ T, s (g • θ) = s θ) →
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
    (∀ θ ∈ T, (∀ θ' ∈ T, jPop P0 s L K lc lK θ ≤ jPop P0 s L K lc lK θ') → ∃ g : G, θ = g • θs) →
    (hessMat (jPop P0 s L K lc lK) θs).PosDef →
    (∀ n, Measurable (θh n)) →
    (∀ n ω, θh n ω ∈ T ∧ ∀ t ∈ T, jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n)
      (lKn n) (θh n ω) ≤ jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n) t) →
    (∀ n, Measurable (θr n)) → (∀ n ω, IsClosestRelabel G θs (θh n ω) (θr n ω)) →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X P → iIndepFun Y P →
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) P → (∀ i, P.map (X i) = P0) → (∀ i, P.map (Y i) = P0) →
      (∀ n ω, θr n ω ∈ T ∧ ∀ t ∈ T, jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n)
        (lKn n) (θr n ω) ≤ jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n) t) ∧
      (∀ᶠ n in atTop, ∀ ω, DifferentiableAt ℝ
        (jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n)) θs) ∧
      ∃ ψp ψv : Z → EuclideanSpace ℝ (Fin p), Measurable ψp ∧ Measurable ψv ∧
        (∃ C, ∀ z, ‖ψp z‖ ≤ C ∧ ‖ψv z‖ ≤ C) ∧ ∫ z, ψp z ∂P0 = 0 ∧ ∫ z, ψv z ∂P0 = 0 ∧
        TendstoInMeasure P (fun (n : ℕ) ω =>
          √(n : ℝ) • gradient (jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n)) θs -
            ((√(n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, ψp (X i ω) +
              (√(n : ℝ) / m n) • ∑ i ∈ Finset.range (m n), ψv (Y i ω))) atTop 0 ∧
        ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
          (G' : Ω' → EuclideanSpace ℝ (Fin p)),
          HasLaw G' (multivariateGaussian 0 ((hessMat (jPop P0 s L K lc lK) θs)⁻¹ *
            (covMat P0 ψp + κ⁻¹ • covMat P0 ψv) * (hessMat (jPop P0 s L K lc lK) θs)⁻¹)) P' →
          TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) • (θr n ω - θs)) atTop G' (fun _ => P) P'

/-! ### SB `lem:dplan` + `prop:mixture` in `ℝᵈ` on path space -/

/-- `lem:dplan` + `prop:mixture` + `eq:gaussmarg` in `ℝᵈ`, on path space: for `μ = N(m₀, A)`, `ν = N(m₁, B)`,
`A, B ≻ 0`, `ε > 0` and every `ε`-Brownian reference on `ℝᵈ`, the Schrödinger bridge exists and is unique, its endpoint
law is the Gaussian plan with cross-covariance `C = C_ε(A,B)`, and for every `t ∈ [0,1]` its time-`t` law is
`N((1−t)m₀ + tm₁, (1−t)²A + t²B + t(1−t)(C + Cᵀ) + εt(1−t)I)`, the covariance being positive definite. -/
def mixtureD_gauss : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (d : ℕ) (A B S N : Matrix (Fin d) (Fin d) ℝ) (ε : ℝ) (m₀ m₁ : E d)
    (X : ℝ → Ω → E d) (R : Measure Ω),
    A.PosDef → B.PosDef → 0 < ε → S.PosDef → S * S = A → N.PosDef →
    N * N = 4 • (S * B * S) + ε ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ) →
    IsBrownianRefD ε (multivariateGaussian m₀ A) X R →
      (∃! P : Measure Ω, IsSchrodingerBridgeD X R (multivariateGaussian m₀ A) (multivariateGaussian m₁ B) P) ∧
      ∀ P : Measure Ω, IsSchrodingerBridgeD X R (multivariateGaussian m₀ A) (multivariateGaussian m₁ B) P →
        P.map (fun ω => (X 0 ω, X 1 ω)) = jointGauss m₀ m₁ A B (Cmat S N ε) ∧
        ∀ t ∈ Icc (0 : ℝ) 1, (bridgeCovD A B (Cmat S N ε) ε t).PosDef ∧
          P.map (X t) = multivariateGaussian ((1 - t) • m₀ + t • m₁) (bridgeCovD A B (Cmat S N ε) ε t)

/-! ### SB `ℝᵈ` path-space discharges: `thm:paritydefect`, `prop:corrected` -/

/-- `thm:paritydefect` on path space: for the Schrödinger bridge `P = P*_ε(N(m₀,A), N(m₁,B))` relative to any
`ε`-Brownian reference, the barycentric projection `T^ε_s(x) = E_P[X₁ | X₀ = x]` is `x ↦ m₁ + CᵀA⁻¹(x − m₀)` (defining
identity against bounded measurable `h`, each coordinate), and it pushes `N(m₀, A)` to `N(m₁, CᵀA⁻¹C)`. -/
def gaussplanD_barycentric_path : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (d : ℕ) (A B S N : Matrix (Fin d) (Fin d) ℝ) (ε : ℝ) (m₀ m₁ : E d)
    (X : ℝ → Ω → E d) (R P : Measure Ω),
    A.PosDef → B.PosDef → 0 < ε → S.PosDef → S * S = A → N.PosDef →
    N * N = 4 • (S * B * S) + ε ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ) →
    IsBrownianRefD ε (multivariateGaussian m₀ A) X R →
    IsSchrodingerBridgeD X R (multivariateGaussian m₀ A) (multivariateGaussian m₁ B) P →
      (∀ h : (E d) → ℝ, Measurable h → (∃ K : ℝ, ∀ x, |h x| ≤ K) → ∀ j,
        Integrable (fun ω => X 1 ω j * h (X 0 ω)) P ∧
          ∫ ω, X 1 ω j * h (X 0 ω) ∂P =
            ∫ x, affD m₀ m₁ ((Cmat S N ε)ᵀ * A⁻¹) x j * h x ∂(multivariateGaussian m₀ A)) ∧
      (multivariateGaussian m₀ A).map (affD m₀ m₁ ((Cmat S N ε)ᵀ * A⁻¹)) =
        multivariateGaussian m₁ ((Cmat S N ε)ᵀ * A⁻¹ * Cmat S N ε)

open StatFormal.Wave25a (meanV covM corrMap) in
/-- `prop:corrected` on path space: for Gaussian `R_s = N(m₀, A)`, `ν = N(m₁, B)`, the Schrödinger bridge
`P = P*_ε(R_s, ν)` relative to any `ε`-Brownian reference, and ANY integrable version `T` of its barycentric projection
`E_P[X₁ | X₀]`, the corrected map pushes `R_s` exactly onto `ν` (hypotheses on `V^{1/2}`, `P^{−1/2}` as in the frozen
`corrected_gaussian_eot`). -/
def gaussplanD_corrected_path : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (d : ℕ) (A B S N : Matrix (Fin d) (Fin d) ℝ) (ε : ℝ) (m₀ m₁ : E d)
    (X : ℝ → Ω → E d) (R P : Measure Ω) (T : (E d) → (E d)) (Vh Ph : Matrix (Fin d) (Fin d) ℝ),
    A.PosDef → B.PosDef → 0 < ε → S.PosDef → S * S = A → N.PosDef →
    N * N = 4 • (S * B * S) + ε ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ) →
    IsBrownianRefD ε (multivariateGaussian m₀ A) X R →
    IsSchrodingerBridgeD X R (multivariateGaussian m₀ A) (multivariateGaussian m₁ B) P →
    Integrable T (multivariateGaussian m₀ A) →
    (∀ h : (E d) → ℝ, Measurable h → (∃ K : ℝ, ∀ x, |h x| ≤ K) → ∀ j,
      ∫ ω, X 1 ω j * h (X 0 ω) ∂P = ∫ x, T x j * h x ∂(multivariateGaussian m₀ A)) →
    Vh.transpose = Vh → Vh * Vh = covM (multivariateGaussian m₁ B) id → Ph.transpose = Ph →
    Ph * covM (multivariateGaussian m₀ A) T * Ph = 1 →
      (multivariateGaussian m₀ A).map
          (corrMap (multivariateGaussian m₀ A) T (meanV (multivariateGaussian m₁ B) id) (Vh * Ph)) =
        multivariateGaussian m₁ B

end Claims

end StatFormal.Wave29y
