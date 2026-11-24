import StatFormal.Archive.Wave22c.Statements
import StatFormal.Archive.WaveP1c.Statements
import TauCeti.MeasureTheory.OptimalTransport.Entropic.Basic

/-!
# FROZEN STATEMENTS — wave P3b (partial-audit wave 3d, GAUSS-EOT): SB `lem:gaussplan` (the 1-D entropic plan between
# Gaussians, `eq:ceps`, `eq:cepsval`), with the mechanical discharges of the Gaussian-plan premises of the frozen
# Wave 18b `noisefree_*`, Wave 22c `noisefree_*_plan` and Wave P1c `gaussian_*`, `eps2_W2` claims

Sources (`data-fairness-repair/schrodinger_bridge_fairness_repair.tex`, current text read 2026-10-16):
* `eq:static` (`:385-394`: `C_ε(μ,ν) = min_π {½∫|x−y|² dπ − ε H(π)}`, `H` differential entropy, minimiser `π*_ε`,
  unique when finite) and `ass:ac` (`:396-400`).
* `lem:gaussplan` (`:2217-2232`: `π*_ε(N(m₀,σ₀²), N(m₁,σ₁²))` is the bivariate Gaussian with these marginals and
  cross-covariance `c_ε = (−ε + √(ε² + 4σ₀²σ₁²))/2`, the unique positive root of `c² + εc = σ₀²σ₁²`; `eq:cepsval`),
  the remark after it (`:2234-2240`: Schrödinger form, `c_ε → σ₀σ₁`, the monotone coupling), proof `:2847-2870`.
* `prop:noisefree` (`:1611-1624`, proof `:3230-3248`), `thm:gaussian` (`:2529-2570`, `eq:gaussmarg`), `prop:eps2`
  (`:2621-2632`), through the frozen claims they condition.
Imports the frozen `Wave22c` (`gaussPlan`; through it `Wave18b` `muSB`, the `noisefree_*` claims, `SBFairness`
`cEps`, `kappa`, `v`, `geo`, `Wave4b` `endpointMixture1`, `Wave9b` `stoPlan`, `qcost`) and `WaveP1c` statements, not
copied; Tau Ceti (`IsCoupling`, `entropicTransportCost`, `transportCost`, `wassersteinEDist`) and Mathlib otherwise.
Library: `StatFormal/Foundations/GaussianEOT` (new).

Covered:
* `lem:gaussplan`: `gaussplan_eot` (for `ε > 0` the entropic value is finite and `π` is an optimal plan iff
  `π = gaussPlan m₀ σ₀ m₁ σ₁ c_ε`: existence, uniqueness and identification of `π*_ε`); `gaussplan_ot` (`ε = 0`: the
  optimal transport plan exists, is unique and is the comonotone `gaussPlan … c₀`, `c₀ = cEps 0 σ₀ σ₁ = σ₀σ₁`, value
  `½[(m₀−m₁)² + (σ₀−σ₁)²]`); `gaussplan_quad` (a Gaussian coupling with `|c| < σ₀σ₁` is optimal iff
  `c² + εc = σ₀²σ₁²`: the paper's "iff" for the Schrödinger form, as an optimality statement); `gaussplan_schrodinger`
  (the Lebesgue density on `ℝ²` of `π*_ε` is `exp{(f(x) + g(y) − ½(x−y)²)/ε}` with quadratic `f`, `g`);
  `gaussplan_cepsval` (`eq:cepsval`: the value at the minimiser of the paper's objective `½∫(x−y)² dπ − εH(π)`, with
  `H(π) = −∫ log p dπ` for the Lebesgue density `p` of `π*_ε`; the Tau Ceti value `∫ c dπ + ε KL(π ‖ μ ⊗ ν)` and its
  difference `ε(H(μ) + H(ν))`, `H(N(m,σ²)) = −∫ log φ_{m,σ²} dN(m,σ²) = ½ log(2πeσ²)`).
* `thm:paritydefect`, `prop:corrected`, `lem:dplan` for `d = 1`: `gaussplan_barycentric` (the barycentric projection of
  every optimal plan, `ε ≥ 0`, is the affine map with slope `C_εᵀA⁻¹ = c_ε/σ₀²`, as `∫ y h(x) dπ = ∫ T(x) h(x) dμ` for
  bounded measurable `h`; push-forward variance `P = c_ε²/σ₀² = σ₁² − εc_ε/σ₀²`, the exact `d = 1` form of `eq:Ps`).
* DISCHARGES (same frozen objects; the frozen Gaussian-plan / closed-form marginal is replaced by the endpoint mixture
  of an ARBITRARY entropic optimal plan `π*_ε`, resp. optimal transport plan `π*_0`, of the two Gaussians):
  `noisefree_bridge_exact_eot`, `noisefree_additive_exact_eot`, `noisefree_bridge_theta_eot`,
  `noisefree_additive_theta_eot`, `noisefree_limits_eot` (all of the frozen Wave 18b `prop:noisefree` claims stated with
  `muSB`, which were CONDITIONAL on `eq:gaussmarg`; and the Wave 22c `noisefree_bridge_exact_plan`,
  `noisefree_limits_plan`, which were relative to "`π*_ε` Gaussian with cross-covariance `c_ε`, `π*_0` comonotone");
  `gaussian_F_eot`, `gaussian_a_eot`, `gaussian_d_flow_eot`, `gaussian_d_sto_eot`, `eps2_W2_eot` (the frozen Wave P1c
  `thm:gaussian`, `prop:eps2` claims, stated for the endpoint mixtures of the Gaussian plans; every `ε ≥ 0`, resp. `ε > 0`
  as frozen).

Not covered (declared):
* `lem:dplan` (`ℝ^d`, `d ≥ 2`): that `π*_ε(N(m₀,A), N(m₁,B))` is Gaussian with cross-covariance `C_ε` (multivariate
  Gaussian densities on `ℝ^{2d}` and the matrix Schrödinger form are not built); hence also the identification of the
  barycentric map of `π*_ε` with `C_sᵀA_s⁻¹` in `thm:paritydefect` and "`T` affine" in `prop:corrected` (Wave 25a
  `corrected_gaussian`, stated on `EuclideanSpace ℝ (Fin d)`) stay hypotheses for `d ≥ 2` (for `d = 1` see
  `gaussplan_barycentric`; the transfer to `EuclideanSpace ℝ (Fin 1)` is not done). The matrix algebra is the frozen `SBFairness/DPlan`.
* `prop:mixture` path space: that the Schrödinger-bridge marginal `μ^ε_{s,t}` IS the endpoint mixture
  `ρ_t ∗ N(0, εt(1−t))` of `π*_ε` (the frozen `endpointMixture1` encodes it; Brownian-bridge path measures are not built).
* `eq:static` in the paper's normalisation as a minimisation over ALL couplings (differential entropy of a general
  coupling): the minimiser is characterised in Tau Ceti's normalisation `∫ c dπ + ε KL(π ‖ μ ⊗ ν)`, which under
  `ass:ac` differs from the paper's objective by the constant `ε(H(μ) + H(ν))` on couplings of finite entropy (the
  standard identity `−H(π) = KL(π ‖ μ ⊗ ν) − H(μ) − H(ν)`; the same minimisers); `gaussplan_cepsval` (iii) checks the
  constant at the Gaussian marginals. The path-space calibration `eq:calib` (`lem:equiv`) is not used.

Encodings (to be checked by the critic):
* Cost `½(x − y)² = sqCost` (`ENNReal.ofReal`, finite); temperature `ε.toNNReal` (`ε > 0`, resp. `ε = 0`; Tau Ceti's
  `ε : ℝ≥0`); `IsEntPlan ε μ ν π` = `π` is a coupling of `μ`, `ν` attaining `entropicTransportCost sqCost ε μ ν`
  (`inf_π ∫ c dπ + ε KL(π ‖ μ ⊗ ν)`); at `ε = 0` this is `∫ c dπ = transportCost sqCost μ ν` (Tau Ceti
  `entropicTransportCost_zero`, `0 · KL = 0`), i.e. `π*_0`. `IsEntPlan` itself does not assert finiteness (at value
  `∞` every coupling would attain it); finiteness at the Gaussian marginals is asserted separately in `gaussplan_eot`
  (`≠ ∞`) and `gaussplan_ot` (explicit value), and `gaussplan_eot`/`gaussplan_ot` also give existence, so the
  discharges' premise `IsEntPlan … π` is satisfiable and pins `π` down (with these, each `*_eot` implies its frozen
  original).
* `N(m, σ²) = gaussianReal m (σ²).toNNReal`, `σ > 0`; the bivariate Gaussian with cross-covariance `c` is the frozen
  `gaussPlan` (law of `(m₀ + σ₀U, m₁ + (c/σ₀)U + √(σ₁² − c²/σ₀²) V)`; marginals and covariance are the certified Wave
  22c `gaussPlan_marginals`, `gaussPlan_cov`); `c_ε = cEps ε σ₀ σ₁`.
* Densities are against Lebesgue measure `volume` on `ℝ × ℝ` (`withDensity` of `ENNReal.ofReal` of a positive,
  measurable function: no junk; the density is then unique a.e., so `∫ log p dπ` does not depend on the witness); `log p` and `(x−y)²` are asserted integrable, so the Bochner integrals are genuine; "quadratic" is
  `∃ α β γ, ∀ x, f x = αx² + βx + γ`; `log(2πe) = log(2π) + 1`.
* Discharges: the frozen `muSB ε σ τ a a⋆ t` (resp. `endpointMixture1 ε t (gaussPlan … (cEps ε σ τ))`) is replaced by
  `endpointMixture1 ε t π` for an arbitrary `π` with `IsEntPlan ε (N(a,σ²)) (N(a⋆,τ²)) π` (for the `ε → 0` limits a
  family `π ε`, one optimal plan for each `ε > 0`), and `muSB 0 …` by `endpointMixture1 0 t π₀`, `π₀` any optimal
  transport plan; all other premises and conclusions are copied verbatim.

Critic notes:
* All 16 claims are proved in `WaveP3b/Route{Plan,Discharge}.lean` from the library `Foundations/GaussianEOT`
  (`gaussCoupling_eq_withDensity`: Schrödinger form against `μ ⊗ ν` with explicit quadratic potentials; Tau Ceti
  `IsCoupling.lintegral_add_mul_klDiv_eq_entropicTransportCost_of_eq_withDensity` (sufficiency) and
  `IsCoupling.eq_of_klDiv_eq_schroedingerValue` with the Gibbs reformulation (uniqueness); `ε = 0`: the certificate
  `½(x−y)² = φ₀(x) + ψ₀(y) + (σ₀/(2σ₁))(y − ℓ(x))²`), and the certified Wave 18b, Wave 22c, Wave P1c theorems.
* Manuscript check: `eq:ceps` and the normalisation (`½|x−y|²`, `−εH`) are as printed and consistent with
  `c² + εc = σ₀²σ₁²` (xy-coefficient `c/det Σ = 1/ε`); `eq:cepsval` is correct in the paper's normalisation; in the
  Tau Ceti normalisation the value is `½[(m₀−m₁)² + σ₀² + σ₁² − 2c_ε] + (ε/2) log(σ₀²σ₁²/(εc_ε)) ≥ 0`. The proof's
  "by strict convexity the solution is unique, and it is characterised by having a density of Schrödinger form" uses
  sufficiency only (proved here for the quadratic, unbounded cost). No statement was found false.

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TauCeti InformationTheory
open scoped ENNReal NNReal

namespace StatFormal.WaveP3b

/-- The quadratic cost `c(x, y) = ½(x − y)²` of `eq:static`. -/
def sqCost (z : ℝ × ℝ) : ℝ≥0∞ := ENNReal.ofReal ((z.1 - z.2) ^ 2 / 2)

/-- `π` is the entropic optimal plan `π*_ε(μ, ν)` (`ε > 0`), resp. the optimal transport plan `π*_0` (`ε = 0`), for the
cost `½(x−y)²`: a coupling of `μ` and `ν` attaining `inf_π ∫ c dπ + ε KL(π ‖ μ ⊗ ν)`. -/
def IsEntPlan (ε : ℝ) (μ ν : Measure ℝ) (P : Measure (ℝ × ℝ)) : Prop :=
  IsCoupling P μ ν ∧
    ∫⁻ z, sqCost z ∂P + (ε.toNNReal : ℝ≥0∞) * klDiv P (μ.prod ν) = entropicTransportCost sqCost ε.toNNReal μ ν

namespace Claims

open StatFormal.Wave22c (gaussPlan)
open StatFormal.SBFairness (cEps kappa v geo)
open StatFormal.Wave4b (endpointMixture1)
open StatFormal.Wave9b (stoPlan qcost)

/-! ### SB `lem:gaussplan` -/

/-- `lem:gaussplan`: for `ε > 0`, the entropic transport problem between `N(m₀,σ₀²)` and `N(m₁,σ₁²)` has finite value,
and a measure `π` is an optimal plan iff it is the bivariate Gaussian with cross-covariance `c_ε`. -/
def gaussplan_eot : Prop :=
  ∀ ε σ₀ σ₁ m₀ m₁ : ℝ, 0 < ε → 0 < σ₀ → 0 < σ₁ →
    entropicTransportCost sqCost ε.toNNReal (gaussianReal m₀ (σ₀ ^ 2).toNNReal) (gaussianReal m₁ (σ₁ ^ 2).toNNReal) ≠ ∞ ∧
      ∀ P : Measure (ℝ × ℝ), IsEntPlan ε (gaussianReal m₀ (σ₀ ^ 2).toNNReal) (gaussianReal m₁ (σ₁ ^ 2).toNNReal) P ↔
        P = gaussPlan m₀ σ₀ m₁ σ₁ (cEps ε σ₀ σ₁)

/-- `lem:gaussplan`, `ε = 0` (the remark: `c_ε → σ₀σ₁`, the monotone coupling): the quadratic transport cost is
`½[(m₀−m₁)² + (σ₀−σ₁)²]`, and the optimal transport plan exists, is unique and is the comonotone Gaussian plan
`gaussPlan … c₀`, `c₀ = σ₀σ₁`. -/
def gaussplan_ot : Prop :=
  ∀ σ₀ σ₁ m₀ m₁ : ℝ, 0 < σ₀ → 0 < σ₁ →
    cEps 0 σ₀ σ₁ = σ₀ * σ₁ ∧
    transportCost sqCost (gaussianReal m₀ (σ₀ ^ 2).toNNReal) (gaussianReal m₁ (σ₁ ^ 2).toNNReal) =
        ENNReal.ofReal (((m₀ - m₁) ^ 2 + (σ₀ - σ₁) ^ 2) / 2) ∧
      ∀ P : Measure (ℝ × ℝ), IsEntPlan 0 (gaussianReal m₀ (σ₀ ^ 2).toNNReal) (gaussianReal m₁ (σ₁ ^ 2).toNNReal) P ↔
        P = gaussPlan m₀ σ₀ m₁ σ₁ (cEps 0 σ₀ σ₁)

/-- `lem:gaussplan`, the "iff" of the proof as optimality: a Gaussian coupling with cross-covariance `c`,
`|c| < σ₀σ₁`, is the entropic optimal plan iff `c² + εc = σ₀²σ₁²`. -/
def gaussplan_quad : Prop :=
  ∀ ε σ₀ σ₁ m₀ m₁ c : ℝ, 0 < ε → 0 < σ₀ → 0 < σ₁ → |c| < σ₀ * σ₁ →
    (IsEntPlan ε (gaussianReal m₀ (σ₀ ^ 2).toNNReal) (gaussianReal m₁ (σ₁ ^ 2).toNNReal) (gaussPlan m₀ σ₀ m₁ σ₁ c) ↔
      c ^ 2 + ε * c = σ₀ ^ 2 * σ₁ ^ 2)

/-- `lem:gaussplan`, the Schrödinger form: the Lebesgue density on `ℝ²` of `π*_ε` is
`exp{(f(x) + g(y) − ½(x−y)²)/ε}` with quadratic potentials `f`, `g`. -/
def gaussplan_schrodinger : Prop :=
  ∀ ε σ₀ σ₁ m₀ m₁ : ℝ, 0 < ε → 0 < σ₀ → 0 < σ₁ →
    ∃ f g : ℝ → ℝ, (∃ α β γ : ℝ, ∀ x, f x = α * x ^ 2 + β * x + γ) ∧ (∃ α β γ : ℝ, ∀ y, g y = α * y ^ 2 + β * y + γ) ∧
      gaussPlan m₀ σ₀ m₁ σ₁ (cEps ε σ₀ σ₁) =
        volume.withDensity (fun z : ℝ × ℝ => ENNReal.ofReal (Real.exp ((f z.1 + g z.2 - (z.1 - z.2) ^ 2 / 2) / ε)))

/-- `eq:cepsval`: (i) the Tau Ceti value `min_π ∫ c dπ + ε KL(π ‖ μ ⊗ ν)` is `ofReal V`,
`V = ½[(m₀−m₁)² + σ₀² + σ₁² − 2c_ε] + (ε/2) log(σ₀²σ₁²/(εc_ε)) ≥ 0`; (ii) `π*_ε` has a positive measurable Lebesgue density `p`
with `log p`, `(x−y)²` integrable, and the paper's objective at `π*_ε`, `½∫(x−y)² dπ*_ε − εH(π*_ε)` with
`H(π) = −∫ log p dπ`, equals `½[(m₀−m₁)² + σ₀² + σ₁² − 2c_ε] − ε[log(2πe) + ½ log(εc_ε)]`; (iii) the two differ by
`ε(H(μ) + H(ν))`, `H(N(m,σ²)) = −∫ log φ_{m,σ²} dN(m,σ²) = ½ log(2πeσ²)`. -/
def gaussplan_cepsval : Prop :=
  ∀ ε σ₀ σ₁ m₀ m₁ : ℝ, 0 < ε → 0 < σ₀ → 0 < σ₁ →
    (0 ≤ ((m₀ - m₁) ^ 2 + σ₀ ^ 2 + σ₁ ^ 2 - 2 * cEps ε σ₀ σ₁) / 2 +
        ε / 2 * Real.log (σ₀ ^ 2 * σ₁ ^ 2 / (ε * cEps ε σ₀ σ₁)) ∧
      entropicTransportCost sqCost ε.toNNReal (gaussianReal m₀ (σ₀ ^ 2).toNNReal) (gaussianReal m₁ (σ₁ ^ 2).toNNReal) =
        ENNReal.ofReal (((m₀ - m₁) ^ 2 + σ₀ ^ 2 + σ₁ ^ 2 - 2 * cEps ε σ₀ σ₁) / 2 +
          ε / 2 * Real.log (σ₀ ^ 2 * σ₁ ^ 2 / (ε * cEps ε σ₀ σ₁)))) ∧
    (∃ p : ℝ × ℝ → ℝ, Measurable p ∧ (∀ z, 0 < p z) ∧
      gaussPlan m₀ σ₀ m₁ σ₁ (cEps ε σ₀ σ₁) = volume.withDensity (fun z => ENNReal.ofReal (p z)) ∧
      Integrable (fun z => Real.log (p z)) (gaussPlan m₀ σ₀ m₁ σ₁ (cEps ε σ₀ σ₁)) ∧
      Integrable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2) (gaussPlan m₀ σ₀ m₁ σ₁ (cEps ε σ₀ σ₁)) ∧
      (∫ z, (z.1 - z.2) ^ 2 / 2 ∂(gaussPlan m₀ σ₀ m₁ σ₁ (cEps ε σ₀ σ₁))) -
          ε * (-∫ z, Real.log (p z) ∂(gaussPlan m₀ σ₀ m₁ σ₁ (cEps ε σ₀ σ₁))) =
        ((m₀ - m₁) ^ 2 + σ₀ ^ 2 + σ₁ ^ 2 - 2 * cEps ε σ₀ σ₁) / 2 -
          ε * ((Real.log (2 * Real.pi) + 1) + Real.log (ε * cEps ε σ₀ σ₁) / 2)) ∧
    (-∫ x, Real.log (gaussianPDFReal m₀ (σ₀ ^ 2).toNNReal x) ∂(gaussianReal m₀ (σ₀ ^ 2).toNNReal) =
        Real.log (2 * Real.pi * Real.exp 1 * σ₀ ^ 2) / 2 ∧
      -∫ y, Real.log (gaussianPDFReal m₁ (σ₁ ^ 2).toNNReal y) ∂(gaussianReal m₁ (σ₁ ^ 2).toNNReal) =
        Real.log (2 * Real.pi * Real.exp 1 * σ₁ ^ 2) / 2 ∧
      ((m₀ - m₁) ^ 2 + σ₀ ^ 2 + σ₁ ^ 2 - 2 * cEps ε σ₀ σ₁) / 2 +
          ε / 2 * Real.log (σ₀ ^ 2 * σ₁ ^ 2 / (ε * cEps ε σ₀ σ₁)) =
        (((m₀ - m₁) ^ 2 + σ₀ ^ 2 + σ₁ ^ 2 - 2 * cEps ε σ₀ σ₁) / 2 -
          ε * ((Real.log (2 * Real.pi) + 1) + Real.log (ε * cEps ε σ₀ σ₁) / 2)) +
        ε * (Real.log (2 * Real.pi * Real.exp 1 * σ₀ ^ 2) / 2 + Real.log (2 * Real.pi * Real.exp 1 * σ₁ ^ 2) / 2))

/-- `thm:paritydefect` / `prop:corrected` / `lem:dplan` in `d = 1`: the barycentric projection
`T^ε(x) = E_{π*_ε}[Y | X = x]` of every optimal plan (`ε ≥ 0`) is the affine map `x ↦ m₁ + (c_ε/σ₀²)(x − m₀)` (the
matrix `C_εᵀA⁻¹ = c_ε/σ₀²`), as the defining identity `∫ y h(x) dπ*_ε = ∫ T^ε(x) h(x) dμ` for every bounded measurable
`h`; its push-forward variance is `P = C_εᵀA⁻¹C_ε = c_ε²/σ₀² = σ₁² − εc_ε/σ₀²`. -/
def gaussplan_barycentric : Prop :=
  ∀ ε σ₀ σ₁ m₀ m₁ : ℝ, 0 ≤ ε → 0 < σ₀ → 0 < σ₁ →
    ∀ P : Measure (ℝ × ℝ), IsEntPlan ε (gaussianReal m₀ (σ₀ ^ 2).toNNReal) (gaussianReal m₁ (σ₁ ^ 2).toNNReal) P →
      (∀ h : ℝ → ℝ, Measurable h → (∃ C : ℝ, ∀ x, |h x| ≤ C) →
        Integrable (fun z : ℝ × ℝ => z.2 * h z.1) P ∧
          ∫ z, z.2 * h z.1 ∂P = ∫ x, (m₁ + cEps ε σ₀ σ₁ / σ₀ ^ 2 * (x - m₀)) * h x ∂(gaussianReal m₀ (σ₀ ^ 2).toNNReal)) ∧
      ∫ x, ((m₁ + cEps ε σ₀ σ₁ / σ₀ ^ 2 * (x - m₀)) - m₁) ^ 2 ∂(gaussianReal m₀ (σ₀ ^ 2).toNNReal) =
        cEps ε σ₀ σ₁ ^ 2 / σ₀ ^ 2 ∧
      cEps ε σ₀ σ₁ ^ 2 / σ₀ ^ 2 = σ₁ ^ 2 - ε * cEps ε σ₀ σ₁ / σ₀ ^ 2

/-! ### Discharges: Wave 18b / Wave 22c `prop:noisefree` -/

/-- DISCHARGE of Wave 18b `noisefree_bridge_exact` (and Wave 22c `noisefree_bridge_exact_plan`): with `μ^ε_{s,t}`,
`μ^0_{s,t}` the endpoint mixtures of ANY entropic optimal plan `π*_ε` and ANY optimal transport plan `π*_0` between
`R_s = N(a,σ²)` and `ν = N(a⋆,τ²)`. -/
def noisefree_bridge_exact_eot : Prop :=
  ∀ ε σ τ a astar t : ℝ, 0 < ε → 0 < σ → 0 < τ → t ∈ Ioo (0 : ℝ) 1 →
    ∀ P P₀ : Measure (ℝ × ℝ),
      IsEntPlan ε (gaussianReal a (σ ^ 2).toNNReal) (gaussianReal astar (τ ^ 2).toNNReal) P →
      IsEntPlan 0 (gaussianReal a (σ ^ 2).toNNReal) (gaussianReal astar (τ ^ 2).toNNReal) P₀ →
        wassersteinEDist 2 (endpointMixture1 ε t P) (endpointMixture1 0 t P₀) =
            ENNReal.ofReal (t * (1 - t) * (kappa ε σ τ - 2 * σ * τ) / (√(v ε σ τ t) + √(v 0 σ τ t))) ∧
          kappa ε σ τ - 2 * σ * τ = ε ^ 2 / (kappa ε σ τ + 2 * σ * τ)

/-- DISCHARGE of Wave 18b `noisefree_additive_exact`: `μ^0_{s,t}` the endpoint mixture of any optimal transport plan. -/
def noisefree_additive_exact_eot : Prop :=
  ∀ ε σ τ a astar t : ℝ, 0 < ε → 0 < σ → 0 < τ → t ∈ Ioo (0 : ℝ) 1 →
    ∀ P₀ : Measure (ℝ × ℝ), IsEntPlan 0 (gaussianReal a (σ ^ 2).toNNReal) (gaussianReal astar (τ ^ 2).toNNReal) P₀ →
      wassersteinEDist 2 (endpointMixture1 0 t P₀ ∗ gaussianReal 0 (ε * t * (1 - t)).toNNReal)
          (endpointMixture1 0 t P₀) =
        ENNReal.ofReal (√(v 0 σ τ t + ε * t * (1 - t)) - √(v 0 σ τ t))

/-- DISCHARGE of Wave 18b `noisefree_bridge_theta`: for any family `π*_ε` (`ε > 0`) of entropic optimal plans and any
optimal transport plan `π*_0`. -/
def noisefree_bridge_theta_eot : Prop :=
  ∀ σ τ a astar t : ℝ, 0 < σ → 0 < τ → t ∈ Ioo (0 : ℝ) 1 →
    ∀ (P : ℝ → Measure (ℝ × ℝ)) (P₀ : Measure (ℝ × ℝ)),
      (∀ ε, 0 < ε → IsEntPlan ε (gaussianReal a (σ ^ 2).toNNReal) (gaussianReal astar (τ ^ 2).toNNReal) (P ε)) →
      IsEntPlan 0 (gaussianReal a (σ ^ 2).toNNReal) (gaussianReal astar (τ ^ 2).toNNReal) P₀ →
        ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ ε in 𝓝[>] 0,
          ENNReal.ofReal (c₁ * (ε * t * (1 - t)) ^ 2) ≤
              wassersteinEDist 2 (endpointMixture1 ε t (P ε)) (endpointMixture1 0 t P₀) ∧
            wassersteinEDist 2 (endpointMixture1 ε t (P ε)) (endpointMixture1 0 t P₀) ≤
              ENNReal.ofReal (c₂ * (ε * t * (1 - t)) ^ 2)

/-- DISCHARGE of Wave 18b `noisefree_additive_theta`. -/
def noisefree_additive_theta_eot : Prop :=
  ∀ σ τ a astar t : ℝ, 0 < σ → 0 < τ → t ∈ Ioo (0 : ℝ) 1 →
    ∀ P₀ : Measure (ℝ × ℝ), IsEntPlan 0 (gaussianReal a (σ ^ 2).toNNReal) (gaussianReal astar (τ ^ 2).toNNReal) P₀ →
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ ε in 𝓝[>] 0,
        ENNReal.ofReal (c₁ * (ε * t * (1 - t))) ≤
            wassersteinEDist 2 (endpointMixture1 0 t P₀ ∗ gaussianReal 0 (ε * t * (1 - t)).toNNReal)
              (endpointMixture1 0 t P₀) ∧
          wassersteinEDist 2 (endpointMixture1 0 t P₀ ∗ gaussianReal 0 (ε * t * (1 - t)).toNNReal)
              (endpointMixture1 0 t P₀) ≤ ENNReal.ofReal (c₂ * (ε * t * (1 - t)))

/-- DISCHARGE of Wave 18b `noisefree_limits` (and Wave 22c `noisefree_limits_plan`). -/
def noisefree_limits_eot : Prop :=
  ∀ σ τ a astar t : ℝ, 0 < σ → 0 < τ → t ∈ Ioo (0 : ℝ) 1 →
    ∀ (P : ℝ → Measure (ℝ × ℝ)) (P₀ : Measure (ℝ × ℝ)),
      (∀ ε, 0 < ε → IsEntPlan ε (gaussianReal a (σ ^ 2).toNNReal) (gaussianReal astar (τ ^ 2).toNNReal) (P ε)) →
      IsEntPlan 0 (gaussianReal a (σ ^ 2).toNNReal) (gaussianReal astar (τ ^ 2).toNNReal) P₀ →
        Tendsto (fun ε => (wassersteinEDist 2 (endpointMixture1 ε t (P ε)) (endpointMixture1 0 t P₀)).toReal /
            (ε * t * (1 - t)) ^ 2) (𝓝[>] 0)
          (𝓝 (1 / (8 * σ * τ * geo σ τ t * (t * (1 - t))))) ∧
        Tendsto (fun ε => (wassersteinEDist 2 (endpointMixture1 0 t P₀ ∗ gaussianReal 0 (ε * t * (1 - t)).toNNReal)
            (endpointMixture1 0 t P₀)).toReal / (ε * t * (1 - t))) (𝓝[>] 0)
          (𝓝 (1 / (2 * geo σ τ t))) ∧
        Tendsto (fun ε => (wassersteinEDist 2 (endpointMixture1 ε t (P ε)) (endpointMixture1 0 t P₀)).toReal /
            (wassersteinEDist 2 (endpointMixture1 0 t P₀ ∗ gaussianReal 0 (ε * t * (1 - t)).toNNReal)
              (endpointMixture1 0 t P₀)).toReal) (𝓝[>] 0) (𝓝 0)

/-! ### Discharges: Wave P1c `thm:gaussian`, `prop:eps2` -/

/-- DISCHARGE of Wave P1c `gaussian_F` (`eq:gaussF`): `μ^ε_{s,t}` the endpoint mixtures of any optimal plans
`π*_ε(R_s, ν)` (`ε ≥ 0`; at `ε = 0` the optimal transport plans). -/
def gaussian_F_eot : Prop :=
  ∀ ε σ₀ σ₁ τ a₀ a₁ astar t : ℝ, 0 ≤ ε → 0 < σ₀ → 0 < σ₁ → 0 < τ → t ∈ Icc (0 : ℝ) 1 →
    ∀ P₀ P₁ : Measure (ℝ × ℝ),
      IsEntPlan ε (gaussianReal a₀ (σ₀ ^ 2).toNNReal) (gaussianReal astar (τ ^ 2).toNNReal) P₀ →
      IsEntPlan ε (gaussianReal a₁ (σ₁ ^ 2).toNNReal) (gaussianReal astar (τ ^ 2).toNNReal) P₁ →
        wassersteinEDist 2 (endpointMixture1 ε t P₀) (endpointMixture1 ε t P₁) ^ 2 =
          ENNReal.ofReal ((1 - t) ^ 2 * (a₀ - a₁) ^ 2 + (√(v ε σ₀ τ t) - √(v ε σ₁ τ t)) ^ 2)

/-- DISCHARGE of Wave P1c `gaussian_a` (`thm:gaussian` (a)). -/
def gaussian_a_eot : Prop :=
  ∀ ε σ₀ σ₁ τ a₀ a₁ astar t : ℝ, 0 ≤ ε → 0 < σ₀ → 0 < σ₁ → 0 < τ → t ∈ Icc (0 : ℝ) 1 →
    ∀ P₀ P₁ : Measure (ℝ × ℝ),
      IsEntPlan ε (gaussianReal a₀ (σ₀ ^ 2).toNNReal) (gaussianReal astar (τ ^ 2).toNNReal) P₀ →
      IsEntPlan ε (gaussianReal a₁ (σ₁ ^ 2).toNNReal) (gaussianReal astar (τ ^ 2).toNNReal) P₁ →
        ∫ x, x ∂(endpointMixture1 ε t P₀) - ∫ x, x ∂(endpointMixture1 ε t P₁) = (1 - t) * (a₀ - a₁)

/-- DISCHARGE of Wave P1c `gaussian_d_flow` (`thm:gaussian` (d), flow cost). -/
def gaussian_d_flow_eot : Prop :=
  ∀ ε σ τ a astar t : ℝ, 0 ≤ ε → 0 < σ → 0 < τ → t ∈ Icc (0 : ℝ) 1 →
    ∀ P : Measure (ℝ × ℝ), IsEntPlan ε (gaussianReal a (σ ^ 2).toNNReal) (gaussianReal astar (τ ^ 2).toNNReal) P →
      wassersteinEDist 2 (gaussianReal a (σ ^ 2).toNNReal) (endpointMixture1 ε t P) ^ 2 =
        ENNReal.ofReal (t ^ 2 * (astar - a) ^ 2 + (√(v ε σ τ t) - σ) ^ 2)

/-- DISCHARGE of Wave P1c `gaussian_d_sto` (`thm:gaussian` (d), stochastic cost over `π*_ε`). -/
def gaussian_d_sto_eot : Prop :=
  ∀ ε σ τ a astar t : ℝ, 0 ≤ ε → 0 < σ → 0 < τ → t ∈ Icc (0 : ℝ) 1 →
    ∀ P : Measure (ℝ × ℝ), IsEntPlan ε (gaussianReal a (σ ^ 2).toNNReal) (gaussianReal astar (τ ^ 2).toNNReal) P →
      0 ≤ (a - astar) ^ 2 + σ ^ 2 + τ ^ 2 - 2 * cEps ε σ τ ∧
        qcost (stoPlan ε t P) =
          ENNReal.ofReal (t ^ 2 * ((a - astar) ^ 2 + σ ^ 2 + τ ^ 2 - 2 * cEps ε σ τ) + ε * t * (1 - t))

/-- DISCHARGE of Wave P1c `eps2_W2` (`prop:eps2`, the `W₂` statement): `μ^ε_{s,t}`, `μ^0_{s,t}` the endpoint mixtures
of any `π*_ε` and any `π*_0`. -/
def eps2_W2_eot : Prop :=
  ∀ ε σ τ a astar : ℝ, 0 < ε → 0 < σ → 0 < τ →
    ∀ P P₀ : Measure (ℝ × ℝ),
      IsEntPlan ε (gaussianReal a (σ ^ 2).toNNReal) (gaussianReal astar (τ ^ 2).toNNReal) P →
      IsEntPlan 0 (gaussianReal a (σ ^ 2).toNNReal) (gaussianReal astar (τ ^ 2).toNNReal) P₀ →
        (∀ t ∈ Icc (0 : ℝ) 1,
          wassersteinEDist 2 (endpointMixture1 ε t P) (endpointMixture1 0 t P₀) =
            ENNReal.ofReal (√(v ε σ τ t) - geo σ τ t)) ∧
        ⨆ t ∈ Icc (0 : ℝ) 1, wassersteinEDist 2 (endpointMixture1 ε t P) (endpointMixture1 0 t P₀) ≤
          ENNReal.ofReal (ε ^ 2 / (32 * σ * τ * min σ τ))

end Claims

end StatFormal.WaveP3b
