import StatFormal.Archive.OTFD.Bands2.Statements
import StatFormal.Archive.OTFD.Wave1.Statements
import StatFormal.Archive.OTFD.WaveL1.Statements
import StatFormal.Archive.OTFD.Wave5a.Statements
import StatFormal.Archive.OTFD.WaveL3.Statements
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.CDF
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Rearrangement
import TauCeti.Probability.Quantile
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Probability.Notation

/-!
# FROZEN STATEMENTS — wave 23d (QUEUE rows 300–306): robust-equality paper 2 `prop:repair`; otfd A `lem:app-cm-plans`
# (i)–(iii), (iv) moment-free existence/gradient and conditional uniqueness; R `prop:ball`, `thm:student` (ii) in `ℝ^K`;
# B `prop:ext-sinkhorn-aposteriori` (with Birkhoff's contraction proved)

Sources (verbatim in `lean-formalisation/inventory/extracted/{robust-equality-paper2,otfd-A_sieves,otfd-R_robustness,
otfd-B_bands}.md`; current text after the 2026-10-15 corrections):
* paper 2 `prop:repair` (`robust-equality-outcomes-under-distribution-shift/paper2/main.tex:642-662`), section preamble
  `:632-640` (`μ_s = h#P̂_s`, `q_s`, `π_s`, budgets `σ_s` in `W₂` on the prediction line).
* A `lem:app-cm-plans` (`otfd/papers/A_sieves/supplement.tex:1429-1472`, proof `:1474-1610`), with
  `def:app-lipschitz-hypersurface` (`:931-943`) and `cor:app-ghs-lipschitz` (`:1067-1078`, GHS Cor. 2.7).
* R `prop:ball` (`R_robustness/sections/s5_families.tex:28-37`, proof `appendix_b.tex:51-64`), ball law (S2) of
  `s2_setting.tex:17-21`, `eq:TDH` (`:7-10`), `def:beta` (`s3_infinite.tex:112-121`).
* R `thm:student` (`R_robustness/sections/s6_references.tex:71-88`, proof `:90-98`).
* B `prop:ext-sinkhorn-aposteriori` (`B_bands/supplement.tex:4907-4946`, proof `:4948-4980`).
Imports the frozen `OTFD/Bands2` (`osc`), `OTFD/Wave1` (`truncK`, `tukeyDepth`, `regionDepth`), `OTFD/WaveL1`
(`CycMon`, `CMConc`, `Graph`, `LipNull`), `OTFD/WaveL3` (`Mom1`), `OTFD/Wave5a` (`betaStar`, `depthRegion`) statements, not
copied; Mathlib
(`gaussianReal`, `stdGaussian`, `gammaMeasure`, `cdf`) and Tau Ceti (`wassersteinEDist`, `Measure.quantile`) otherwise.

Covered:
* B: `birkhoff_contraction` (Birkhoff 1957 / Peyré–Cuturi Thm 4.1, `λ = tanh(¼ log η)`, PROVED, not assumed),
  `sinkhorn_constants` (`η(𝖪) = e^{Δ_C/ε}`, `λ = (√η−1)/(√η+1) = tanh(Δ_C/4ε)`), `sinkhorn_deltaC_diam` (inner-product
  form of `Δ_C` and the diameter bound), `sinkhorn_aposteriori_i` ((i) and `ε/(1−λ²) = ε cosh²`),
  `sinkhorn_aposteriori_ii` ((ii), `ελ/(1−λ²) = (ε/2) sinh(Δ_C/2ε)`, and "(i) is never larger").
* R `prop:ball`: `ball_region_bound` (for every `τ > 0`), `ball_tau_mono`, `ball_decay` ("decays like
  `exp{−cK^{2/3}}`" as the upper bound it is).
* A: (i) `cm_closure`, `cm_transpose`, `cm_support`; (ii) `cm_rockafellar`; (iii) `cm_gateaux`; (iv) `cm_graph_exists`
  (first sentence, no moment), `cm_graph_gradient` (bounded target: `T = ∇f` a.e., `f` finite convex `M`-Lipschitz, no
  moment), `cm_unique_cond` (uniqueness of the cyclically monotone coupling, CONDITIONAL on `GHSGradUnique`);
  under an added first moment `m₁(A) < ∞`, UNCONDITIONAL via the certified wave-L3 `brenier_uniq_H_bdd`:
  `ghs_grad_unique_m1` (the premise `GHSGradUnique` itself discharged) and `cm_unique_uncond`.
* R `thm:student` (ii), `ℝ^K`: `student_depth`, `student_content`, `student_beta`, `student_region` (content `≥ p`,
  robustness exactly `β*_K(p)`, optimal among regions of content `p`).
* paper 2 `prop:repair`: (i) `repair_cert`, `repair_omega_le_lip`; (ii) `repair_partial_delta` (`Δ_T = ℓΔ`, atomless),
  `repair_root_affine`; (iii) `repair_convex_omega`, `repair_convex_lip`, `repair_convex_delta`,
  `repair_sqrt_envelope_not_convex` (the printed caveat, on one fixed explicit instance).

Not covered (declared):
* `prop:repair`: the dual formula `ω_s(σ)² = inf_λ{λσ² + E sup_y[…]}` (W-DRO strong duality, missing; `ω` is encoded by
  its primal sup); in (ii) `Lip(T_s) = ℓ + (1−ℓ)ζ_s` (derivatives of quantile functions) and the empirical tie-randomised
  remark; in (iii) the SOC representation and the convexity of the full programme with a convex risk (immediate from the
  three convexity claims plus additivity; squares not formalised); the group-blind variant (restriction to `t₀ = t₁`);
  the positive half of the caveat (the fixed-multiplier envelope itself is convex in the values; only its square root's
  failure is claimed).
* A: (iv) moment-free uniqueness itself (GHS Cor. 2.7 without a moment: `GHSGradUnique`, no Lean proof; with
  `m₁(A) < ∞` it is `ghs_grad_unique_m1` / `cm_unique_uncond`); (iv)'s "`T` is the unique gradient" clause is
  `GHSGradUnique` (conditional) or `ghs_grad_unique_m1` (first moment); (v) tightness, (vi) uniform
  integrability, (vii) density of `C_b` in `L²(A;H)`, (viii) the transpose identity and `𝕼 = 𝔽⁻¹` (all L4 / not
  attempted in this wave).
* R `thm:student`: (i) (Gaussian measures on `H`, `𝒫^ℓ`, `m₂ = ν/(ν−2) tr Σ`), the rate `≍ K^{−ν/2}` (`thm:rates`(f)),
  exact uniformity of the outlyingness and content EXACTLY `p` of the ellipsoid (both need atomlessness of `F_{K,ν}`;
  `student_region` proves content `≥ p`, which is all `β*` uses), (iii) (`thm:region-breakdown`).
* R `prop:ball`: no gap; the bound is the printed one. "Decays like `exp{−cK^{2/3}}`" is encoded as the upper bound
  `ball_decay` only; this matches the paper, which adds that the bound is not tight (numerically faster decay), so no
  lower bound is printed. `ball_decay` assumes `τ_{K₀,p} > 0` (automatic for the printed `R ~ Unif(0,1)`; needed for
  the generalised `R ∈ [0,1]`, e.g. `R ≡ 0`).
* B: none for the proposition; `rem:ext-sinkhorn-use`.
* G `prop:blindspot` and G `thm:rates`: NOT ATTEMPTED in this wave (see the report).

Encodings (to be checked by the critic):
* B: index sets `Fin n`, `Fin m` nonempty; `d_H(x,y) = osc(log x − log y)` with the frozen `osc` (no `sSup ∅` junk:
  `n, m ≥ 1`); `𝖪 = gibbs ε C`, `ε > 0`, `a, b > 0`; `(f*, g*)` any solution of the dual (`IsDualSol`: both marginals of
  `π = e^{(f+g−C)/ε}` exact), so no uniqueness is used; `r(f) = π^f 1`, `g^f = colStep`, the row half-step `rowStep`;
  `η(M)` and `Δ_C` are maxima over all index quadruples. Birkhoff is stated for every positive `p × q` matrix and
  positive vectors (exactly Peyré–Cuturi Thm 4.1).
* `prop:ball`: `H` any real inner product space with Borel σ-algebra, `e` orthonormal; `Z_k` i.i.d. `N(0,1)`
  (`iIndepFun`, laws `gaussianReal 0 1`); `ζ : Ω → H` measurable with `⟨e_k, ζ⟩ = Z_k/(k+1)` (`λ_k = 1/k`, indices from
  `1`; a generalisation: `ζ` may have components outside `span e`); `R` measurable with values in `[0,1]` (no
  uniform law or independence needed); `X = (R/‖ζ‖) ζ` (`= 0` on the null event `ζ = 0`); `μ_K = Π_K#law(X)`
  (`truncK`); `τ_{K,p} = inf{t ≥ 0 : μ_K(‖u‖ ≤ t) ≥ p}` (nonempty for `p ≤ 1`, Bessel). The side condition
  `(τK)^{2/3} ≥ 1.6` is dropped (the bound holds for every `τ > 0`).
* A: `H` complete, second countable (separable Hilbert), Borel; cyclical monotonicity is the frozen cycle form
  `CycMon`; "concentrated on a cyclically monotone set" is the frozen `CMConc` (support version: `cm_support`); the
  first marginal `γ.fst` is the frozen `LipNull`; `∂f(x) = subdiff f x`; `D_f = gatSet f` is the set of Gâteaux
  differentiability points (`GatDiff`: every directional map `t ↦ f(x+th)` has derivative `⟨g,h⟩` at `0`);
  `∇f = gatGrad f` (a choice on `D_f`, `0` off `D_f`, which is `A`-null). `GHSGradUnique A B` is GHS Cor. 2.7's
  uniqueness for finite convex Lipschitz potentials with Gâteaux gradients (implied by GHS for the bounded `B = γ²` at
  which it is used); `cm_graph_exists` assumes `CMConc` instead of "cyclically monotone support" (weaker: by
  `cm_support` the support form implies it).
* `thm:student`: `ℝ^K = EuclideanSpace ℝ (Fin K)`, `K ≥ 1`; `Σ_K = AAᵀ` for an invertible `A`, so
  `‖Σ_K^{-1/2}u‖ = ‖A^{-1}u‖`; `μ_K = law(√W A Z)` with `Z` the Mathlib standard Gaussian and `W = 1/V`,
  `V ~ Gamma(ν/2, rate ν/2)` independent (product measure); `F_{t_ν}` and `F_{K,ν}` are the distribution functions
  (`cdf`) of `Z₁/√V` and `(‖Z‖²/K)/V` (the textbook ratio definitions); `F_{K,ν}^{-1}(p) = inf{x : F_{K,ν}(x) ≥ p}`
  (nonempty, bounded below by `0` for `0 < p < 1`); `ν > 0` (generalisation: the printed `ν > 2` is needed only
  for the moment in (i), i.e. for membership in R's standing finite-second-moment class; for `ν ≤ 2` the law is
  outside that class but the finite-dimensional facts of (ii) still hold, so the claims are consistent with it); depth, regions and `β*` are the frozen `tukeyDepth`, `regionDepth`, `betaStar`. "The depth
  regions are the ellipsoids" is covered as: depth is the nonincreasing function `F_{t_ν}(−‖A^{-1}u‖)` of the
  Mahalanobis norm.
* `prop:repair`: score laws are probability measures on `ℝ`; `W₂ = wassersteinEDist 2` (`[0,∞]`); "admissible" is
  `W₂(μ_s, μ_s') ≤ σ_s`; `ω_s(σ) = omegaMod μ_s G σ T_s`, the sup over joint laws of `(U, U')` with `U ∼ μ_s`,
  `‖U' − U‖_{L²} ≤ σ` and `U' ∈ G` a.s. of `‖T(U') − T(U)‖_{L²}` (`G = univ` in (i); a grid in (iii)); `Lip = lipConst`
  in `[0,∞]`; maps given "by their values on the grid, extended by any rule linear in the values" are `ext t` for a
  linear `ext : ℝ^N → (ℝ → ℝ)` (measurable extensions for `ω`); convexity is the inequality with weights
  `ofReal a, ofReal b` in `[0,∞]`; (ii): `T_s = g_s ∘ F_s` with Tau Ceti's `quantile`; the values of `q` at the levels
  `0, 1` (`F_s(Y) ∈ {0,1}`) are reached only on a `μ_s`-null set (atomless `μ_s`), so they do not affect `T_s#μ_s`;
  `envFix` is the fixed-multiplier envelope on a finite grid.

Critic notes:
* All 30 claims are proved in `Wave23d/Route{Sinkhorn,Ball,CM,Grad,Student,Repair,Uniq}.lean` (no forbidden tokens).
  CONDITIONAL: `cm_unique_cond` (on `GHSGradUnique`); `ghs_grad_unique_m1`, `cm_unique_uncond` add `m₁(A) < ∞` and
  use the certified wave-L3 route theorem `brenier_uniq_H_bdd`. Routes reuse the certified wave-L3 `cycMon_swap`, `cycMon_mono`,
  `cycMon_subgradGraph`, wave-5a `depth_regions_optimal`, the library `Foundations/Potentials/HilbertUniqueness`
  (`measure_multivaluedSet_eq_zero`, `exists_eq_graphPlan_of_ae_mem`), Tau Ceti's 1-D quantile formula
  `wassersteinEDist_eq_eLpNorm_quantile_sub`, `quantile_map_volume_Ioo_ae`, `cdf_map_eq_volume_restrict`, triangle
  inequality and attainment of `W₂`.
* Suspected manuscript issues: none false. `prop:ball` needs no side condition; `prop:ext-sinkhorn-aposteriori` uses
  no uniqueness of `(f*, g*)`; `thm:student` (ii) needs only `ν > 0`; `prop:repair`(iii)'s "convex in the values" for
  `Δ_T` needs the maps to be nondecreasing (stated in the paper's last sentence; the claim carries it).
* Critic (2026-10-15): ACCEPT-WITH-NOTE. Fixes: `repair_sqrt_envelope_not_convex` pinned to its explicit instance (the
  existential form let the witness range over empty grids and non-integrable laws, where `⨆ ∅ = 0` and `∫ = 0` junk
  could manufacture or mask non-convexity); first-moment unconditional uniqueness added. `GHSGradUnique` checked no
  stronger than GHS Cor. 2.7 (finite convex Lipschitz potentials with Gâteaux gradients are a subclass of GHS's
  proper l.s.c. convex potentials; used only at a Lipschitz-null `A` and a boundedly supported `B`).
  `repair_root_affine` is pure algebra in free reals `ζ_s` (the L0 part of (ii)); `Lip(T_s) = ℓ + (1 − ℓ)ζ_s` is not
  formalised.

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset TauCeti
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave23d

open StatFormal.OTFD.Bands2 (osc)
open StatFormal.OTFD.Wave1 (truncK regionDepth tukeyDepth)
open StatFormal.OTFD.WaveL1 (CycMon CMConc Graph LipNull)
open StatFormal.OTFD.Wave5a (betaStar depthRegion)

/-! ### B `prop:ext-sinkhorn-aposteriori`: Hilbert's projective metric and Sinkhorn half-steps -/

/-- Hilbert's projective metric on positive vectors, `d_H(x, y) = osc(log x − log y)`. -/
def hilb {n : ℕ} (x y : Fin n → ℝ) : ℝ := osc fun i => Real.log (x i) - Real.log (y i)

/-- `(M x)_i = Σ_j M_ij x_j`. -/
def matVec {p q : ℕ} (M : Fin p → Fin q → ℝ) (x : Fin q → ℝ) : Fin p → ℝ := fun i => ∑ j, M i j * x j

/-- `η(M) = max_{i,i',j,j'} M_ij M_i'j' / (M_i'j M_ij')` (Birkhoff's cross-ratio bound). -/
def etaM {p q : ℕ} (M : Fin p → Fin q → ℝ) : ℝ :=
  ⨆ (i : Fin p) (i' : Fin p) (j : Fin q) (j' : Fin q), M i j * M i' j' / (M i' j * M i j')

/-- `Δ_C = max_{i,i',j,j'} (C_ij + C_i'j' − C_ij' − C_i'j)`. -/
def deltaC {n m : ℕ} (C : Fin n → Fin m → ℝ) : ℝ :=
  ⨆ (i : Fin n) (i' : Fin n) (j : Fin m) (j' : Fin m), C i j + C i' j' - C i j' - C i' j

/-- The Gibbs kernel `𝖪_ij = e^{−C_ij/ε}`. -/
def gibbs {n m : ℕ} (ε : ℝ) (C : Fin n → Fin m → ℝ) : Fin n → Fin m → ℝ := fun i j => Real.exp (-C i j / ε)

/-- The plan built from dual vectors, `π_ij = e^{(f_i + g_j − C_ij)/ε}`. -/
def planFG {n m : ℕ} (ε : ℝ) (C : Fin n → Fin m → ℝ) (f : Fin n → ℝ) (g : Fin m → ℝ) :
    Fin n → Fin m → ℝ := fun i j => Real.exp ((f i + g j - C i j) / ε)

/-- Row sums `π 1_m`. -/
def rowSum {n m : ℕ} (π : Fin n → Fin m → ℝ) : Fin n → ℝ := fun i => ∑ j, π i j

/-- Column sums `π^⊤ 1_n`. -/
def colSum {n m : ℕ} (π : Fin n → Fin m → ℝ) : Fin m → ℝ := fun j => ∑ i, π i j

/-- The column half-step `g^f_j = ε log b_j − ε log Σ_i e^{(f_i − C_ij)/ε}`. -/
def colStep {n m : ℕ} (ε : ℝ) (b : Fin m → ℝ) (C : Fin n → Fin m → ℝ) (f : Fin n → ℝ) : Fin m → ℝ :=
  fun j => ε * Real.log (b j) - ε * Real.log (∑ i, Real.exp ((f i - C i j) / ε))

/-- The row half-step `f_i = ε log a_i − ε log Σ_j e^{(g_j − C_ij)/ε}`. -/
def rowStep {n m : ℕ} (ε : ℝ) (a : Fin n → ℝ) (C : Fin n → Fin m → ℝ) (g : Fin m → ℝ) : Fin n → ℝ :=
  fun i => ε * Real.log (a i) - ε * Real.log (∑ j, Real.exp ((g j - C i j) / ε))

/-- `(f, g)` solves the entropic dual (both marginals of `π` exact). -/
def IsDualSol {n m : ℕ} (ε : ℝ) (a : Fin n → ℝ) (b : Fin m → ℝ) (C : Fin n → Fin m → ℝ)
    (f : Fin n → ℝ) (g : Fin m → ℝ) : Prop :=
  rowSum (planFG ε C f g) = a ∧ colSum (planFG ε C f g) = b

/-! ### R `prop:ball`: the ball law -/

/-- The ball law's random element `X = R ζ/‖ζ‖` (`X = 0` on the null event `ζ = 0`). -/
def ballX {Ω H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (R : Ω → ℝ) (ζ : Ω → H) (ω : Ω) : H :=
  (R ω / ‖ζ ω‖) • ζ ω

/-- `τ_{K,p} = c_K^{-1}(p) = inf{t ≥ 0 : μ_K(‖u‖ ≤ t) ≥ p}`, the radius of the ball region of content `p`. -/
def ballTau {K : ℕ} (μK : Measure (EuclideanSpace ℝ (Fin K))) (p : ℝ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal p ≤ μK (Metric.closedBall 0 t)}

/-- The ball-law setting: `Z_k` i.i.d. `N(0,1)`, `ζ` with coordinates `⟨e_k, ζ⟩ = λ_k Z_k`, `λ_k = 1/k` (indices from `1`,
here `k + 1`), `R ∈ [0, 1]`. -/
def BallSetting {Ω H : Type*} [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
    (P : Measure Ω) (e : ℕ → H) (Z : ℕ → Ω → ℝ) (ζ : Ω → H) (R : Ω → ℝ) : Prop :=
  Orthonormal ℝ e ∧ (∀ k, Measurable (Z k)) ∧ iIndepFun Z P ∧ (∀ k, P.map (Z k) = gaussianReal 0 1) ∧
    Measurable ζ ∧ (∀ k ω, ⟪e k, ζ ω⟫ = Z k ω / ((k : ℝ) + 1)) ∧ Measurable R ∧ (∀ ω, 0 ≤ R ω ∧ R ω ≤ 1)

/-- `μ_K = Π_K # law(X)`. -/
def ballLawK {Ω H : Type*} [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H] (P : Measure Ω)
    (e : ℕ → H) (ζ : Ω → H) (R : Ω → ℝ) (K : ℕ) : Measure (EuclideanSpace ℝ (Fin K)) :=
  P.map fun ω => truncK e K (ballX R ζ ω)

/-! ### R `thm:student` (finite dimension) -/

/-- The law of Student's `t_ν = Z/√(χ²_ν/ν)`: `Z ~ N(0,1)` independent of `V ~ Gamma(ν/2, rate ν/2)`. -/
def tLaw (ν : ℝ) : Measure ℝ :=
  ((gaussianReal 0 1).prod (gammaMeasure (ν / 2) (ν / 2))).map fun p => p.1 / √p.2

/-- `F_{t_ν}`, the distribution function of `t_ν`. -/
def tCDF (ν : ℝ) (x : ℝ) : ℝ := cdf (tLaw ν) x

/-- The law of Fisher–Snedecor's `F_{K,ν} = (χ²_K/K)/(χ²_ν/ν)`, `χ²_K = ‖Z‖²` for `Z` standard Gaussian in `ℝ^K`. -/
def fLaw (K : ℕ) (ν : ℝ) : Measure ℝ :=
  ((stdGaussian (EuclideanSpace ℝ (Fin K))).prod (gammaMeasure (ν / 2) (ν / 2))).map
    fun p => ‖p.1‖ ^ 2 / K / p.2

/-- `F_{K,ν}`, its distribution function. -/
def fCDF (K : ℕ) (ν : ℝ) (x : ℝ) : ℝ := cdf (fLaw K ν) x

/-- The quantile `F_{K,ν}^{-1}(p) = inf{x : F_{K,ν}(x) ≥ p}`. -/
def fQuant (K : ℕ) (ν p : ℝ) : ℝ := sInf {x | p ≤ fCDF K ν x}

/-- The `K`-variate Student law with scale `Σ_K = A Aᵀ`: the law of `√W A Z`, `Z` standard Gaussian in `ℝ^K`,
`W = 1/V ~ InvGamma(ν/2, ν/2)` independent. -/
def studentLaw (K : ℕ) (ν : ℝ) (A : EuclideanSpace ℝ (Fin K) ≃L[ℝ] EuclideanSpace ℝ (Fin K)) :
    Measure (EuclideanSpace ℝ (Fin K)) :=
  ((stdGaussian (EuclideanSpace ℝ (Fin K))).prod (gammaMeasure (ν / 2) (ν / 2))).map fun p => (√p.2)⁻¹ • A p.1

/-! ### robust-equality paper 2 `prop:repair`: post-processing a fixed score -/

/-- The exact modulus of a map `T` on the prediction line, `ω(σ) = sup{‖T(U') − T(U)‖_{L²} : U ∼ μ, ‖U' − U‖_{L²} ≤ σ}`
(the joint law `π` of `(U, U')`), with the shifted score `U'` restricted to `G` (`G = univ`: unrestricted; a finite
grid in (iii)); in `[0, ∞]`. -/
def omegaMod (μ : Measure ℝ) (G : Set ℝ) (σ : ℝ) (T : ℝ → ℝ) : ℝ≥0∞ :=
  ⨆ (π : Measure (ℝ × ℝ)) (_ : IsProbabilityMeasure π ∧ π.fst = μ ∧ π (univ ×ˢ Gᶜ) = 0 ∧
      eLpNorm (fun z : ℝ × ℝ => edist z.1 z.2) 2 π ≤ ENNReal.ofReal σ),
    eLpNorm (fun z : ℝ × ℝ => edist (T z.1) (T z.2)) 2 π

/-- The Lipschitz constant `Lip(T) = sup_{x ≠ y} |T x − T y|/|x − y|`, in `[0, ∞]`. -/
def lipConst (T : ℝ → ℝ) : ℝ≥0∞ := ⨆ (x : ℝ) (y : ℝ) (_ : x ≠ y), ENNReal.ofReal (|T x - T y| / |x - y|)

/-- The fixed-multiplier groupwise envelope `λσ² + E_μ max_{y ∈ G}[(T(y) − T(U))² − λ(y − U)²]` (finite grid `G`). -/
def envFix (μ : Measure ℝ) (G : Finset ℝ) (lam σ : ℝ) (T : ℝ → ℝ) : ℝ :=
  lam * σ ^ 2 + ∫ x, (⨆ y : G, ((T y - T x) ^ 2 - lam * ((y : ℝ) - x) ^ 2)) ∂μ

/-! ### A `lem:app-cm-plans` (iii)–(iv): Gâteaux gradients of convex functions -/

/-- The subdifferential `∂f(x) = {y : f(x) + ⟨y, z − x⟩ ≤ f(z) ∀ z}`. -/
def subdiff {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (f : H → ℝ) (x : H) : Set H :=
  {y | ∀ z, f x + ⟪y, z - x⟫ ≤ f z}

/-- `f` is Gâteaux differentiable at `x` with gradient `g`: `t ↦ f(x + t h)` has derivative `⟨g, h⟩` at `0`, every `h`. -/
def GatDiff {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (f : H → ℝ) (x g : H) : Prop :=
  ∀ h, HasDerivAt (fun t : ℝ => f (x + t • h)) ⟪g, h⟫ 0

/-- `D_f`, the Gâteaux differentiability points. -/
def gatSet {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (f : H → ℝ) : Set H :=
  {x | ∃ g, GatDiff f x g}

/-- `∇f` on `D_f` (a chosen gradient; `0` off `D_f`, where it is not used). -/
def gatGrad {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (f : H → ℝ) (x : H) : H :=
  open Classical in if h : ∃ g, GatDiff f x g then h.choose else 0

/-- GHS Cor. 2.7 (uniqueness clause), specialised to finite convex Lipschitz potentials: for `A` null on Lipschitz
hypersurfaces and a target `B`, two Borel maps that are `A`-a.e. Gâteaux gradients of finite convex Lipschitz
functions and push `A` to `B` agree `A`-a.e. (GHS state it for every boundedly supported `B` and all convex
potentials; it is not proved here.) -/
def GHSGradUnique {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
    (A B : Measure H) : Prop :=
  ∀ (f f' : H → ℝ) (T T' : H → H) (L L' : ℝ), ConvexOn ℝ univ f → ConvexOn ℝ univ f' →
    (∀ x z, |f x - f z| ≤ L * ‖x - z‖) → (∀ x z, |f' x - f' z| ≤ L' * ‖x - z‖) → Measurable T → Measurable T' →
    (∀ᵐ x ∂A, GatDiff f x (T x)) → (∀ᵐ x ∂A, GatDiff f' x (T' x)) → A.map T = B → A.map T' = B → T =ᵐ[A] T'

namespace Claims

/-- Birkhoff's contraction theorem (Birkhoff 1957; Peyré–Cuturi Thm 4.1): a positive matrix contracts Hilbert's
projective metric by `λ(M) = tanh(¼ log η(M))`. -/
def birkhoff_contraction : Prop :=
  ∀ (p q : ℕ) (M : Fin p → Fin q → ℝ), 0 < p → 0 < q → (∀ i j, 0 < M i j) →
    ∀ x y : Fin q → ℝ, (∀ j, 0 < x j) → (∀ j, 0 < y j) →
      hilb (matVec M x) (matVec M y) ≤ Real.tanh (Real.log (etaM M) / 4) * hilb x y

/-- The constants: `η(𝖪) = e^{Δ_C/ε}`, so `λ(𝖪) = (√η − 1)/(√η + 1) = tanh(Δ_C/(4ε))`; for `C_ij = ‖Z_i − u_j‖²`,
`Δ_C = 2 max ⟨Z_i − Z_i', u_j' − u_j⟩ ≤ 2 diam{Z_i} diam{u_j}`. -/
def sinkhorn_constants : Prop :=
  ∀ (n m : ℕ) (ε : ℝ) (C : Fin n → Fin m → ℝ), 0 < n → 0 < m → 0 < ε →
    etaM (gibbs ε C) = Real.exp (deltaC C / ε) ∧
    Real.tanh (Real.log (etaM (gibbs ε C)) / 4) = Real.tanh (deltaC C / (4 * ε)) ∧
    (√(etaM (gibbs ε C)) - 1) / (√(etaM (gibbs ε C)) + 1) = Real.tanh (deltaC C / (4 * ε))

/-- The cost identity and the diameter bound for `C_ij = ‖Z_i − u_j‖²` in a real inner product space (`M_K`). -/
def sinkhorn_deltaC_diam : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n m : ℕ) (Z : Fin n → E) (u : Fin m → E),
    0 < n → 0 < m →
    deltaC (fun i j => ‖Z i - u j‖ ^ 2) =
        2 * ⨆ (i : Fin n) (i' : Fin n) (j : Fin m) (j' : Fin m), ⟪Z i - Z i', u j' - u j⟫ ∧
      deltaC (fun i j => ‖Z i - u j‖ ^ 2) ≤ 2 * Metric.diam (Set.range Z) * Metric.diam (Set.range u)

/-- (i): for every `f`, after one column half-step, `osc(f − f*) ≤ ε/(1−λ²) d_H(r(f), a) = ε cosh²(Δ_C/4ε) d_H(r(f), a)`. -/
def sinkhorn_aposteriori_i : Prop :=
  ∀ (n m : ℕ) (ε : ℝ) (a : Fin n → ℝ) (b : Fin m → ℝ) (C : Fin n → Fin m → ℝ) (fs : Fin n → ℝ)
    (gs : Fin m → ℝ) (f : Fin n → ℝ), 0 < n → 0 < m → 0 < ε → (∀ i, 0 < a i) → (∀ j, 0 < b j) →
    IsDualSol ε a b C fs gs →
      osc (f - fs) ≤ ε / (1 - Real.tanh (deltaC C / (4 * ε)) ^ 2) *
          hilb (rowSum (planFG ε C f (colStep ε b C f))) a ∧
      ε / (1 - Real.tanh (deltaC C / (4 * ε)) ^ 2) = ε * Real.cosh (deltaC C / (4 * ε)) ^ 2

/-- (ii): if `f` is the row half-step of `g` and `π` the plan of `(f, g)`, then
`osc(f − f*) ≤ ελ/(1−λ²) d_H(π^⊤1, b) = (ε/2) sinh(Δ_C/2ε) d_H(π^⊤1, b)`, and the bound of (i) is at most this one. -/
def sinkhorn_aposteriori_ii : Prop :=
  ∀ (n m : ℕ) (ε : ℝ) (a : Fin n → ℝ) (b : Fin m → ℝ) (C : Fin n → Fin m → ℝ) (fs : Fin n → ℝ)
    (gs : Fin m → ℝ) (g : Fin m → ℝ), 0 < n → 0 < m → 0 < ε → (∀ i, 0 < a i) → (∀ j, 0 < b j) →
    IsDualSol ε a b C fs gs →
      let f := rowStep ε a C g
      let lam := Real.tanh (deltaC C / (4 * ε))
      let d := hilb (colSum (planFG ε C f g)) b
      osc (f - fs) ≤ ε * lam / (1 - lam ^ 2) * d ∧
      ε * lam / (1 - lam ^ 2) = ε / 2 * Real.sinh (deltaC C / (2 * ε)) ∧
      ε / (1 - lam ^ 2) * hilb (rowSum (planFG ε C f (colStep ε b C f))) a ≤ ε * lam / (1 - lam ^ 2) * d

/-! #### R `prop:ball` -/

/-- The bound, for every radius `τ > 0` (the printed side condition `(τK)^{2/3} ≥ 1.6` is not needed):
`β({‖u‖ ≤ τ}; μ_K) ≤ 4 exp{−0.43 (τK)^{2/3}}`. -/
def ball_region_bound : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (e : ℕ → H) (Z : ℕ → Ω → ℝ)
    (ζ : Ω → H) (R : Ω → ℝ), BallSetting P e Z ζ R → ∀ (K : ℕ) (τ : ℝ), 0 < K → 0 < τ →
      regionDepth (ballLawK P e ζ R K) (Metric.closedBall 0 τ) ≤
        ENNReal.ofReal (4 * Real.exp (-0.43 * (τ * K) ^ ((2 : ℝ) / 3)))

/-- `τ_{K,p}` is nondecreasing in `K`. -/
def ball_tau_mono : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (e : ℕ → H) (Z : ℕ → Ω → ℝ)
    (ζ : Ω → H) (R : Ω → ℝ), BallSetting P e Z ζ R → ∀ (K : ℕ) (p : ℝ), 0 < p → p ≤ 1 →
      ballTau (ballLawK P e ζ R K) p ≤ ballTau (ballLawK P e ζ R (K + 1)) p

/-- "Decays like `exp{−cK^{2/3}}`", as an upper bound: if `τ_{K₀,p} > 0`, then for every `K ≥ K₀` the region of content
`p` has `β(A_{K,p}) ≤ 4 exp{−0.43 (τ_{K₀,p} K)^{2/3}}`. -/
def ball_decay : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (e : ℕ → H) (Z : ℕ → Ω → ℝ)
    (ζ : Ω → H) (R : Ω → ℝ), BallSetting P e Z ζ R → ∀ (K₀ : ℕ) (p : ℝ), 0 < K₀ → 0 < p → p ≤ 1 →
      0 < ballTau (ballLawK P e ζ R K₀) p → ∀ K, K₀ ≤ K →
        regionDepth (ballLawK P e ζ R K) (Metric.closedBall 0 (ballTau (ballLawK P e ζ R K) p)) ≤
          ENNReal.ofReal (4 * Real.exp (-0.43 * (ballTau (ballLawK P e ζ R K₀) p * K) ^ ((2 : ℝ) / 3)))

/-! #### A `lem:app-cm-plans` -/

/-- (i) The norm closure of a cyclically monotone set is cyclically monotone. -/
def cm_closure : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (Γ : Set (E × E)), CycMon Γ → CycMon (closure Γ)

/-- (i) The transpose `s(Γ) = {(y, x) : (x, y) ∈ Γ}` of a cyclically monotone set is cyclically monotone. -/
def cm_transpose : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (Γ : Set (E × E)), CycMon Γ → CycMon (Prod.swap ⁻¹' Γ)

/-- (i) A measure concentrated on a cyclically monotone set has cyclically monotone support. -/
def cm_support : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] (π : Measure (E × E)),
    CMConc π → CycMon π.support

/-- (ii) Rockafellar's construction with bounded slopes: a nonempty cyclically monotone `Γ` with `‖y‖ ≤ M` on `Γ`
lies in the subdifferential of a finite convex `M`-Lipschitz `f`. -/
def cm_rockafellar : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (Γ : Set (H × H)) (M : ℝ),
    Γ.Nonempty → CycMon Γ → (∀ p ∈ Γ, ‖p.2‖ ≤ M) →
      ∃ f : H → ℝ, ConvexOn ℝ univ f ∧ (∀ x z, |f x - f z| ≤ M * ‖x - z‖) ∧
        ∀ p ∈ Γ, ∀ z, f p.1 + ⟪p.2, z - p.1⟫ ≤ f z

/-- (iv), first sentence, moment-free: a probability `γ` on `H × H` concentrated on a cyclically monotone set, whose
first marginal `A` is null on Lipschitz hypersurfaces, is a graph plan `(Id × T)#A` of a Borel `T`, and `T#A = γ²`. -/
def cm_graph_exists : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (γ : Measure (H × H)), IsProbabilityMeasure γ → LipNull γ.fst → CMConc γ →
      ∃ T : H → H, Measurable T ∧ γ = Graph γ.fst T ∧ γ.fst.map T = γ.snd

/-! #### R `thm:student` (ii), in `ℝ^K` -/

/-- The depth formula: `TD(u; μ_K) = F_{t_ν}(−‖Σ_K^{-1/2} u‖)` (`‖Σ_K^{-1/2}u‖ = ‖A^{-1}u‖`); in particular the depth is
`F_{t_ν}(−r)` on the boundary of the ellipsoid of radius `r`. -/
def student_depth : Prop :=
  ∀ (K : ℕ) (ν : ℝ) (A : EuclideanSpace ℝ (Fin K) ≃L[ℝ] EuclideanSpace ℝ (Fin K)), 0 < K → 0 < ν →
    ∀ u, tukeyDepth (studentLaw K ν A) u = ENNReal.ofReal (tCDF ν (-‖A.symm u‖))

/-- The content of the ellipsoid of radius `r` is `F_{K,ν}(r²/K)`. -/
def student_content : Prop :=
  ∀ (K : ℕ) (ν : ℝ) (A : EuclideanSpace ℝ (Fin K) ≃L[ℝ] EuclideanSpace ℝ (Fin K)), 0 < K → 0 < ν →
    ∀ r : ℝ, 0 ≤ r → studentLaw K ν A {u | ‖A.symm u‖ ≤ r} = ENNReal.ofReal (fCDF K ν (r ^ 2 / K))

/-- The robustness index: `β*_K(p) = F_{t_ν}(−√(K F_{K,ν}^{-1}(p)))`. -/
def student_beta : Prop :=
  ∀ (K : ℕ) (ν : ℝ) (A : EuclideanSpace ℝ (Fin K) ≃L[ℝ] EuclideanSpace ℝ (Fin K)) (p : ℝ), 0 < K → 0 < ν →
    0 < p → p < 1 →
      betaStar (studentLaw K ν A) (ENNReal.ofReal p) = ENNReal.ofReal (tCDF ν (-√(K * fQuant K ν p)))

/-- The ellipsoid of content `p` (radius `√(K F_{K,ν}^{-1}(p))`) has content `≥ p` and robustness exactly `β*_K(p)`,
the best any region of content `p` can have. -/
def student_region : Prop :=
  ∀ (K : ℕ) (ν : ℝ) (A : EuclideanSpace ℝ (Fin K) ≃L[ℝ] EuclideanSpace ℝ (Fin K)) (p : ℝ), 0 < K → 0 < ν →
    0 < p → p < 1 →
      let E := {u | ‖A.symm u‖ ≤ √(K * fQuant K ν p)}
      ENNReal.ofReal p ≤ studentLaw K ν A E ∧
      regionDepth (studentLaw K ν A) E = betaStar (studentLaw K ν A) (ENNReal.ofReal p) ∧
      ∀ B, ENNReal.ofReal p ≤ studentLaw K ν A B → regionDepth (studentLaw K ν A) B ≤ regionDepth (studentLaw K ν A) E

/-! #### robust-equality paper 2 `prop:repair` -/

/-- (i) The certificate of a repaired rule: for every admissible pair (`W₂(μ_s, μ_s') ≤ σ_s`),
`W₂(T_0#μ_0', T_1#μ_1') ≤ Δ_T + ω_0(σ_0) + ω_1(σ_1)`, `Δ_T = W₂(T_0#μ_0, T_1#μ_1)`. -/
def repair_cert : Prop :=
  ∀ (μ₀ μ₁ μ₀' μ₁' : Measure ℝ) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₀']
    [IsProbabilityMeasure μ₁'] (T₀ T₁ : ℝ → ℝ) (σ₀ σ₁ : ℝ), Measurable T₀ → Measurable T₁ → 0 ≤ σ₀ → 0 ≤ σ₁ →
    wassersteinEDist 2 μ₀ μ₀' ≤ ENNReal.ofReal σ₀ → wassersteinEDist 2 μ₁ μ₁' ≤ ENNReal.ofReal σ₁ →
      wassersteinEDist 2 (μ₀'.map T₀) (μ₁'.map T₁) ≤
        wassersteinEDist 2 (μ₀.map T₀) (μ₁.map T₁) + omegaMod μ₀ univ σ₀ T₀ + omegaMod μ₁ univ σ₁ T₁

/-- (i) `ω_s(σ) ≤ Lip(T_s) σ` (any grid restriction `G`). -/
def repair_omega_le_lip : Prop :=
  ∀ (μ : Measure ℝ) (G : Set ℝ) (σ : ℝ) (T : ℝ → ℝ), 0 ≤ σ → omegaMod μ G σ T ≤ lipConst T * ENNReal.ofReal σ

/-- (ii) For atomless `μ_s`, partial barycentric repair `T_s = g_s ∘ F_s`, `g_s = ℓ q_s + (1 − ℓ) q_B`,
`q_B = π_0 q_0 + π_1 q_1`, `ℓ ∈ [0, 1]`, has `Δ_T = ℓ Δ`, `Δ = W₂(μ_0, μ_1)`. -/
def repair_partial_delta : Prop :=
  ∀ (μ₀ μ₁ : Measure ℝ) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] [NullSingletonClass μ₀]
    [NullSingletonClass μ₁] (π₀ π₁ ℓ : ℝ), 0 ≤ π₀ → 0 ≤ π₁ → 0 ≤ ℓ → ℓ ≤ 1 →
      let qB : ℝ → ℝ := fun t => π₀ * μ₀.quantile t + π₁ * μ₁.quantile t
      let T₀ : ℝ → ℝ := fun y => ℓ * μ₀.quantile (cdf μ₀ y) + (1 - ℓ) * qB (cdf μ₀ y)
      let T₁ : ℝ → ℝ := fun y => ℓ * μ₁.quantile (cdf μ₁ y) + (1 - ℓ) * qB (cdf μ₁ y)
      wassersteinEDist 2 (μ₀.map T₀) (μ₁.map T₁) = ENNReal.ofReal ℓ * wassersteinEDist 2 μ₀ μ₁

/-- (ii) The Lipschitz certificate root `ℓΔ + Σ_s σ_s{ℓ + (1 − ℓ)ζ_s}` is affine in `ℓ`, and full repair (`ℓ = 0`) lowers it
below the unrepaired value (`ℓ = 1`) iff `Δ > Σ_s σ_s(ζ_s − 1)`. -/
def repair_root_affine : Prop :=
  ∀ (S : ℕ) (Δ : ℝ) (σ ζ : Fin S → ℝ),
    let root : ℝ → ℝ := fun ℓ => ℓ * Δ + ∑ s, σ s * (ℓ + (1 - ℓ) * ζ s)
    (∀ ℓ, root ℓ = (1 - ℓ) * root 0 + ℓ * root 1) ∧ (root 0 < root 1 ↔ ∑ s, σ s * (ζ s - 1) < Δ)

/-- (iii) On a grid of `N` values extended to the line by a linear rule `ext` (measurable extensions), the exact modulus
`ω(σ)` is a convex function of the values. -/
def repair_convex_omega : Prop :=
  ∀ (N : ℕ) (ext : (Fin N → ℝ) →ₗ[ℝ] (ℝ → ℝ)) (μ : Measure ℝ) (G : Set ℝ) (σ : ℝ), (∀ t, Measurable (ext t)) →
    ∀ (t t' : Fin N → ℝ) (a b : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 →
      omegaMod μ G σ (ext (a • t + b • t')) ≤
        ENNReal.ofReal a * omegaMod μ G σ (ext t) + ENNReal.ofReal b * omegaMod μ G σ (ext t')

/-- (iii) `Lip(T)` is a convex function of the values. -/
def repair_convex_lip : Prop :=
  ∀ (N : ℕ) (ext : (Fin N → ℝ) →ₗ[ℝ] (ℝ → ℝ)) (t t' : Fin N → ℝ) (a b : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 →
    lipConst (ext (a • t + b • t')) ≤ ENNReal.ofReal a * lipConst (ext t) + ENNReal.ofReal b * lipConst (ext t')

/-- (iii) `Δ_T` is a convex function of the values on the (convex) set of pairs of nondecreasing maps. -/
def repair_convex_delta : Prop :=
  ∀ (N : ℕ) (ext : (Fin N → ℝ) →ₗ[ℝ] (ℝ → ℝ)) (μ₀ μ₁ : Measure ℝ) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (t₀ t₁ t₀' t₁' : Fin N → ℝ) (a b : ℝ), Monotone (ext t₀) → Monotone (ext t₁) → Monotone (ext t₀') →
    Monotone (ext t₁') → 0 ≤ a → 0 ≤ b → a + b = 1 →
      Monotone (ext (a • t₀ + b • t₀')) ∧
      wassersteinEDist 2 (μ₀.map (ext (a • t₀ + b • t₀'))) (μ₁.map (ext (a • t₁ + b • t₁'))) ≤
        ENNReal.ofReal a * wassersteinEDist 2 (μ₀.map (ext t₀)) (μ₁.map (ext t₁)) +
          ENNReal.ofReal b * wassersteinEDist 2 (μ₀.map (ext t₀')) (μ₁.map (ext t₁'))

/-- (iii), the caveat: at a fixed multiplier the square root of the groupwise envelope need not be convex in the values,
on the explicit instance (one-point score law `δ_0`, grid `{0, 1}`, `λ = 1`, `σ = 1/2`, the map `y ↦ d y` given by its
values `(0, d)` on the grid; the instance is fixed so that no junk value of `∫` or of `⨆` over an empty grid can help). -/
def repair_sqrt_envelope_not_convex : Prop :=
  ¬ ConvexOn ℝ univ (fun d : ℝ => √(envFix (Measure.dirac 0) {0, 1} 1 (1 / 2) (fun y => d * y)))

/-- (iii) For a finite convex Lipschitz `f` and `A` null on Lipschitz hypersurfaces: `D_f` is Borel, `A(D_fᶜ) = 0`,
`∂f(x) = {∇f(x)}` on `D_f`, and `∇f` is Borel. -/
def cm_gateaux : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (A : Measure H) (f : H → ℝ) (L : ℝ), LipNull A → ConvexOn ℝ univ f →
    (∀ x z, |f x - f z| ≤ L * ‖x - z‖) →
      MeasurableSet (gatSet f) ∧ A (gatSet f)ᶜ = 0 ∧ (∀ x ∈ gatSet f, subdiff f x = {gatGrad f x}) ∧
        Measurable (gatGrad f)

/-- (iv), second sentence, the gradient part (moment-free): if moreover the second marginal is carried by
`B̄(0, M)`, the map is `A`-a.e. the Gâteaux gradient of a finite convex `M`-Lipschitz `f`. -/
def cm_graph_gradient : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (γ : Measure (H × H)) (M : ℝ), IsProbabilityMeasure γ → LipNull γ.fst →
    CMConc γ → γ.snd (Metric.closedBall 0 M)ᶜ = 0 →
      ∃ (T : H → H) (f : H → ℝ), Measurable T ∧ γ = Graph γ.fst T ∧ γ.fst.map T = γ.snd ∧ ConvexOn ℝ univ f ∧
        (∀ x z, |f x - f z| ≤ M * ‖x - z‖) ∧ ∀ᵐ x ∂γ.fst, GatDiff f x (T x)

/-- (iv), uniqueness, CONDITIONAL on GHS Cor. 2.7 (`GHSGradUnique`): with a boundedly supported second marginal, `γ` is
the only element of `Π(A, γ²)` concentrated on a cyclically monotone set. -/
def cm_unique_cond : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (γ γ' : Measure (H × H)) (M : ℝ), IsProbabilityMeasure γ →
    IsProbabilityMeasure γ' → γ'.fst = γ.fst → γ'.snd = γ.snd → LipNull γ.fst → γ.snd (Metric.closedBall 0 M)ᶜ = 0 →
    CMConc γ → CMConc γ' → GHSGradUnique γ.fst γ.snd → γ' = γ

/-- GHS Cor. 2.7's uniqueness clause (the premise `GHSGradUnique`) DISCHARGED under a first moment of `A` (an extra
hypothesis: (iv) assumes no moment), via the certified wave-L3 `brenier_uniq_H_bdd`: for `A` null on Lipschitz
hypersurfaces with `m₁(A) < ∞` and `B` carried by `B̄(0, M)`, two Borel maps that are `A`-a.e. Gâteaux gradients of
finite convex Lipschitz functions and push `A` to `B` agree `A`-a.e. -/
def ghs_grad_unique_m1 : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (A B : Measure H) (M : ℝ), IsProbabilityMeasure A → LipNull A →
    StatFormal.OTFD.WaveL3.Mom1 A ≠ ∞ → B (Metric.closedBall 0 M)ᶜ = 0 → GHSGradUnique A B

/-- (iv), uniqueness, UNCONDITIONAL (`GHSGradUnique`-free) under a first moment of `A` (an extra hypothesis; the printed
(iv) assumes none): with `γ²` carried by `B̄(0, M)`, `γ` is the only element of `Π(A, γ²)` concentrated on a cyclically
monotone set. -/
def cm_unique_uncond : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (γ γ' : Measure (H × H)) (M : ℝ), IsProbabilityMeasure γ →
    IsProbabilityMeasure γ' → γ'.fst = γ.fst → γ'.snd = γ.snd → LipNull γ.fst →
    StatFormal.OTFD.WaveL3.Mom1 γ.fst ≠ ∞ → γ.snd (Metric.closedBall 0 M)ᶜ = 0 → CMConc γ → CMConc γ' → γ' = γ

end Claims

end StatFormal.Wave23d
