import StatFormal.Archive.WaveP3b.Statements

/-!
# FROZEN STATEMENTS — wave 29q: SB `prop:mixture` on path space (with the path-space half of `lem:equiv`), `d = 1`;
# path-space discharges of the frozen SB `prop:noisefree`, `thm:gaussian` and `eq:gaussmarg` claims

Sources (`data-fairness-repair/schrodinger_bridge_fairness_repair.tex`, current text read 2026-10-20):
* `sec:schrodinger` (`:376-394`): `Ω = C([0,1]; ℝ^d)`, `𝕎^ε_μ` the law of `dX_t = √ε dB_t`, `X₀ ∼ μ`; the Schrödinger
  problem `eq:dynamic` `P*_ε(μ,ν) = argmin {KL(P ‖ 𝕎^ε_μ) : P ∈ 𝒫(Ω), P₀ = μ, P₁ = ν}`; the static problem `eq:static`.
* `lem:equiv` (`:413-427`, proof `:2722-2738`): `P*_ε` exists, is unique, has endpoint marginal `π*_ε` and is, given
  `(X₀, X₁) = (x, y)`, the `ε`-Brownian bridge; `eq:calib`. The proof: `KL(P ‖ 𝕎) = KL(π ‖ R₀₁) + E_π KL(P^{xy} ‖ R^{xy})`,
  `R₀₁(dx,dy) = μ(dx) p_ε(y − x) dy`.
* `def:repair` (`:433-446`): `μ^ε_{s,t} = Law_{P*_ε(R_s, ν)}(X_t)`.
* `prop:mixture` (`:456-470`, proof `:2740-2746`): `μ^ε_t = Law((1−t)X₀ + tX₁ + √(εt(1−t)) Z)`, `(X₀,X₁) ∼ π*_ε`
  (`eq:mixture`), `= ρ^ε_t ∗ N(0, εt(1−t))` (`eq:convolution`).
* `prop:noisefree` (`:1615-1629`), `thm:gaussian` with `eq:gaussmarg` (`:2535-2575`), through the frozen claims they
  condition (Wave 18b, Wave 22c, Wave P1c, Wave P3b).
Imports the frozen `WaveP3b` statements (`sqCost`, `IsEntPlan`, the `*_eot` claims; through them Wave 22c `gaussPlan`,
Wave 18b `muSB`, `SBFairness` `cEps`, `kappa`, `v`, `geo`, Wave 4b `endpointMixture1`, Wave 9b `stoPlan`, `qcost`), not
copied; Tau Ceti (`IsCoupling`, `entropicTransportCost`, `wassersteinEDist`) and Mathlib (`klDiv`, `gaussianReal`)
otherwise. Libraries: `StatFormal/Foundations/SchrodingerPath` (new).

Covered:
* `prop:mixture` with the path-space half of `lem:equiv` (`d = 1`, every `ε > 0`, ARBITRARY `μ`, `ν`):
  `mixture_bridge` (every Schrödinger bridge `P*` relative to an `ε`-Brownian reference `R = 𝕎^ε_μ` is the
  `h`-transform `dP*/dR = g(X₀, X₁)` of `R` by a function of the endpoints — the mixture of the reference bridges over
  its endpoint law `π*`; `π*` minimises the static problem `KL(· ‖ R₀₁)` over `Π(μ,ν)` with the same value; for every
  `t ∈ [0,1]` the law of `((X₀,X₁), X_t)` is `π*` mixed with the bridge kernel `N((1−t)x + ty, εt(1−t))`, hence
  `μ^ε_t = endpointMixture1 ε t π*` (`eq:mixture`/`eq:convolution`) and `Law(X₀, X_t) = stoPlan ε t π*`);
  `mixture_exists` (every static minimiser is the endpoint law of a Schrödinger bridge; two Schrödinger bridges with
  the same endpoint law coincide).
* `lem:equiv`, static half (`eq:calib` at the level of plans): `mixture_static` (for `ν` with a Lebesgue density `q`
  of finite entropy and `μ, ν ∈ 𝒫₂`, every coupling has `KL(π ‖ R₀₁) < ∞ ⟺ KL(π ‖ μ ⊗ ν) < ∞` and then
  `ε KL(π ‖ R₀₁) = ∫ ½(x−y)² dπ + ε KL(π ‖ μ ⊗ ν) + ε(∫ log q dν + ½ log(2πε))`), `mixture_static_plan` (hence the
  static Schrödinger minimisers are exactly the entropic optimal plans `IsEntPlan` of the frozen Wave P3b, and the
  entropic cost is finite). This removes the "informal KL/differential-entropy identity" of the Wave P3b card for the
  path-space objects: `μ^ε_{s,t}` is defined from `eq:dynamic`, and its endpoint law is shown to be `IsEntPlan` directly.
* Gaussian case (`lem:gaussplan` + `eq:gaussmarg` on path space): `mixture_gauss` (for `μ = N(a,σ²)`,
  `ν = N(a⋆,τ²)` and every `ε`-Brownian reference, `P*_ε` exists and is unique, its endpoint law is the frozen
  `gaussPlan … c_ε`, and `Law(X_t) = muSB ε σ τ a a⋆ t = N((1−t)a + ta⋆, v(t))` for every `t ∈ [0,1]`).
* PATH-SPACE DISCHARGES (the plan-level `μ^ε_{s,t} = endpointMixture1 ε t π*_ε` of the frozen Wave P3b `*_eot` claims
  is replaced by the time-`t` law `P.map (X t)` of an arbitrary Schrödinger bridge `P = P*_ε(R_s, ν)` relative to an
  arbitrary `ε`-Brownian reference `𝕎^ε_{R_s}`, `ε > 0`; `μ^0_{s,t}` stays the McCann interpolant `endpointMixture1 0 t π*_0`
  of an optimal transport plan, as in the paper, which defines `P*_ε` only for `ε > 0`):
  `noisefree_bridge_exact_path`, `noisefree_bridge_theta_path`, `noisefree_limits_path` (frozen Wave 18b / Wave 22c /
  Wave P3b `prop:noisefree`), `gaussianthm_F_path`, `gaussianthm_a_path`, `gaussianthm_d_flow_path`,
  `gaussianthm_d_sto_path` (frozen Wave P1c / Wave P3b `thm:gaussian`; the stochastic cost is `E_{P*}|X_t − X₀|²`).

Not covered (declared):
* `d ≥ 2` (`prop:mixture` in `ℝ^d`): the library is one-dimensional (the Gaussian identities are for `ℝ × ℝ`).
* Existence of Wiener measure on `C([0,1]; ℝ)`: Mathlib has `IsBrownianReal`/`IsPreBrownianReal` (predicates) but no
  construction (no Kolmogorov extension / continuity theorem). The claims quantify over every measurable space `Ω`,
  every process `X` and every reference `R` whose three-time laws are those of `X₀ + √ε B` (see Encodings); Wiener
  measure on `C([0,1]; ℝ)` with the coordinate process `X t ω = ω(projIcc 0 1 t)` is one instance (a
  generalisation), as is `X₀ + √ε B_t` for any Mathlib `IsPreBrownianReal B` with measurable `B t`,
  independent of a measurable `X₀ ∼ μ`, on any `Ω` (not proved here).
  Non-vacuity is a ROUTE lemma, not a target (critic, wave 29q): `RouteMixture.isBrownianRef_refMeasure` exhibits ONE
  process `X_t(x, z₁, z₂) = x + t z₁ + √(t(1−t)) z₂` on `ℝ³` carrying an `ε`-Brownian reference
  `μ ⊗ N(0,ε) ⊗ N(0,ε)` for EVERY `ε ≥ 0` and EVERY probability `μ` (the three-time laws hold for every `t ∈ [0,1]`;
  it is NOT a Brownian motion), and `RouteGauss.path_family_exists` (with `mixture_gauss`) gives, on that one
  `(Ω, X)`, a reference `R ε` and a Schrödinger bridge `P ε` for every `ε > 0`; so every premise of every claim
  (including the families of the `θ`/limit claims and the two references of `gaussianthm_*` on one `(Ω, X)`) is
  satisfiable.
* `lem:equiv` in general: existence/uniqueness of `π*_ε` for general `μ`, `ν` (lower semicontinuity and strict
  convexity) is not proved; `mixture_exists` transfers existence and uniqueness from the static to the dynamic problem,
  and the Gaussian case is complete (`mixture_gauss`). `eq:calib` itself (the differential-entropy normalisation of the
  value, `Ent(π)`) is not stated; `mixture_static` gives the relation with Tau Ceti's normalisation instead.
* The `ε = 0` parts (`μ^0_{s,t}`, `noisefree_additive_*`, `thm:gaussian` at `ε = 0`): no path space; covered by the
  frozen Wave P3b `*_eot` claims.

Encodings (to be checked by the critic):
* Path space and reference (`IsBrownianRef ε μ X R`): `Ω` any measurable space, `X : ℝ → Ω → ℝ` with `X t` measurable
  for `t ∈ [0,1]` (times outside `[0,1]` are never used), `R` a measure on `Ω` such that for every `t ∈ [0,1]`
  `(X₀, X_t − X₀, X₁ − X_t) ∼ μ ⊗ N(0, εt) ⊗ N(0, ε(1−t))` under `R` (independent Gaussian increments, independent of
  `X₀ ∼ μ`; `N(0, 0) = δ₀`). Under `𝕎^ε_μ` the coordinate process satisfies this; only these three-time laws are used,
  so the claims are stated (and are true) for every such `R` — a generalisation.
* Constraint set (`IsPathCoupling`): probability measures `P` on `Ω` with `P ∘ X₀⁻¹ = μ`, `P ∘ X₁⁻¹ = ν` (the maps are
  measurable under `IsBrownianRef`, no `Measure.map` junk). `IsSchrodingerBridge X R μ ν P`: `P` is in the constraint
  set, `KL(P ‖ R) < ∞` (the paper's `C_ε(μ,ν) < ∞`; at value `∞` every feasible `P` would be a minimiser) and
  `KL(P ‖ R) ≤ KL(Q ‖ R)` for every feasible `Q` (Mathlib `klDiv`, `[0,∞]`-valued).
* `refPlan ε μ` = law of `(x, x + √ε G)`, `x ∼ μ`, `G ∼ N(0,1)` independent = `μ(dx) N(x, ε)(dy)` = `R₀₁` of the proof of
  `lem:equiv` (`mixture_bridge` proves `R ∘ (X₀,X₁)⁻¹ = refPlan ε μ`). `IsStaticBridge ε μ ν π`: `π ∈ Π(μ,ν)`
  (Tau Ceti `IsCoupling`), `KL(π ‖ R₀₁) < ∞`, minimal among couplings.
* `bridgeLaw ε t π` = law of `((X₀, X₁), (1−t)X₀ + tX₁ + Z)`, `(X₀,X₁) ∼ π`, `Z ∼ N(0, εt(1−t))` independent: the
  `ε`-Brownian bridge from `x` to `y` seen at time `t` is `N((1−t)x + ty, εt(1−t))` (proof of `prop:mixture`).
  "`P*` is the mixture over `π*` of `ε`-Brownian bridges" is encoded twice: as the density statement
  `P* = R.withDensity (g ∘ (X₀,X₁))`, `π* = R₀₁.withDensity g` (`P*` and `R` have the same conditional law given the
  endpoints), and as the three-time law `Law_{P*}((X₀,X₁), X_t) = bridgeLaw ε t π*`.
* `mixture_static`: `ν = volume.withDensity (ofReal ∘ q)`, `q ≥ 0` measurable, `log q` integrable under `ν` (finite
  differential entropy, `ass:ac` for `ν`; `log 0 = 0` is junk only on the `ν`-null set `{q = 0}`), `x²` integrable under
  `μ` and `ν` (`𝒫₂`); the identity is stated with `toReal` under finiteness (all terms finite). `ass:ac` for `μ` is not
  needed.
* Gaussians `N(m, s²) = gaussianReal m (s²).toNNReal`, `s > 0`; Wasserstein distance Tau Ceti `wassersteinEDist 2`;
  families in `ε` (the `θ` and limit claims) are a reference `R ε` and a bridge `P ε` for each `ε > 0` on one `(Ω, X)`;
  all other premises and conclusions are copied verbatim from the frozen Wave P3b `*_eot` claims.

Critic notes (wave 29q, 2026-10-20):
* 12 targets (13 drafted; `mixture_ref_exists`, a pure non-vacuity witness with no paper statement, moved to the
  routes and strengthened to one `ε`-independent process; see Not covered).
* `IsBrownianRef` is a genuine generalisation: Wiener measure `𝕎^ε_μ` on `C([0,1]; ℝ)` satisfies it, and every claim is
  universally quantified over `(Ω, X, R)`, so each implies the printed statement for `𝕎^ε_μ` (should it be constructed).
  The conclusions concern only `P`, the `X_t` and frozen objects; the minimiser of `KL(· ‖ R)` over the constraint set
  is the `h`-transform `R.withDensity (g ∘ (X₀, X₁))` for EVERY reference `R` (data processing + equality case), so
  its time-`t` laws depend on `R` only through the law of `(X₀, X_t, X₁)` — exactly what `IsBrownianRef` pins down.
* "Conditionally on `(X₀,X₁) = (x,y)` it is the `ε`-Brownian bridge" is encoded as `P = R.withDensity (g ∘ (X₀,X₁))`:
  for `P ≪ R` (forced by `KL < ∞`) this is equivalent, on standard Borel `Ω`, to `P` and `R` having the same regular
  conditional law given `(X₀, X₁)`; for `𝕎^ε_μ` that law is the Brownian bridge. It avoids disintegration and is
  stronger than needed for the stated time-`t` conclusions, which are also stated directly (`bridgeLaw`).
* The path discharges are mechanical corollaries of `mixture_bridge`/`mixture_gauss` and the certified frozen `*_eot`
  claims; their content is that the paper's `μ^ε_{s,t} = Law_{P*_ε}(X_t)` (`def:repair`, defined from `eq:dynamic`, no
  differential entropy) is the object. The conjuncts copied verbatim that do not mention `P` are junk guards:
  `κ − 2στ = ε²/(κ + 2στ)` (positivity inside `ofReal`), the additive limit in `noisefree_limits_path` (non-zero
  denominator of the ratio), `0 ≤ M` in `gaussianthm_d_sto_path` (`ofReal` faithful).

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TauCeti InformationTheory
open scoped ENNReal NNReal

namespace StatFormal.Wave29q

open StatFormal.WaveP3b (sqCost IsEntPlan)

section Defs

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `R` is an `ε`-Brownian reference started from `μ` (`𝕎^ε_μ` of `eq:dynamic`), through its three-time laws: each `X t`,
`t ∈ [0,1]`, is measurable and `(X₀, X_t − X₀, X₁ − X_t) ∼ μ ⊗ N(0, εt) ⊗ N(0, ε(1−t))` under `R`. -/
def IsBrownianRef (ε : ℝ) (μ : Measure ℝ) (X : ℝ → Ω → ℝ) (R : Measure Ω) : Prop :=
  (∀ t ∈ Icc (0 : ℝ) 1, Measurable (X t)) ∧
    ∀ t ∈ Icc (0 : ℝ) 1, R.map (fun ω => (X 0 ω, X t ω - X 0 ω, X 1 ω - X t ω)) =
      μ.prod ((gaussianReal 0 (ε * t).toNNReal).prod (gaussianReal 0 (ε * (1 - t)).toNNReal))

/-- The constraint set of `eq:dynamic`: probability measures on path space with `P₀ = μ` and `P₁ = ν`. -/
def IsPathCoupling (X : ℝ → Ω → ℝ) (μ ν : Measure ℝ) (P : Measure Ω) : Prop :=
  IsProbabilityMeasure P ∧ P.map (X 0) = μ ∧ P.map (X 1) = ν

/-- `P = P*_ε(μ, ν)` (`eq:dynamic`) for the reference `R = 𝕎^ε_μ`: a minimiser of `KL(· ‖ R)` over the constraint set,
with finite minimum. -/
def IsSchrodingerBridge (X : ℝ → Ω → ℝ) (R : Measure Ω) (μ ν : Measure ℝ) (P : Measure Ω) : Prop :=
  IsPathCoupling X μ ν P ∧ klDiv P R ≠ ∞ ∧ ∀ Q : Measure Ω, IsPathCoupling X μ ν Q → klDiv P R ≤ klDiv Q R

end Defs

/-- The reference endpoint law `R₀₁(dx, dy) = μ(dx) N(x, ε)(dy)`: the law of `(x, x + √ε G)`. -/
def refPlan (ε : ℝ) (μ : Measure ℝ) : Measure (ℝ × ℝ) :=
  (μ.prod (gaussianReal 0 ε.toNNReal)).map (fun p => (p.1, p.1 + p.2))

/-- The static Schrödinger problem: `π ∈ Π(μ, ν)` minimises `KL(· ‖ R₀₁)` over `Π(μ, ν)`, with finite minimum. -/
def IsStaticBridge (ε : ℝ) (μ ν : Measure ℝ) (π : Measure (ℝ × ℝ)) : Prop :=
  IsCoupling π μ ν ∧ klDiv π (refPlan ε μ) ≠ ∞ ∧
    ∀ π' : Measure (ℝ × ℝ), IsCoupling π' μ ν → klDiv π (refPlan ε μ) ≤ klDiv π' (refPlan ε μ)

/-- The endpoint law `π` mixed with the `ε`-Brownian bridge at time `t`: the law of `((X₀, X₁), (1−t)X₀ + tX₁ + Z)`,
`(X₀, X₁) ∼ π`, `Z ∼ N(0, εt(1−t))` independent. -/
def bridgeLaw (ε t : ℝ) (π : Measure (ℝ × ℝ)) : Measure ((ℝ × ℝ) × ℝ) :=
  (π.prod (gaussianReal 0 (ε * t * (1 - t)).toNNReal)).map (fun q => (q.1, (1 - t) * q.1.1 + t * q.1.2 + q.2))

namespace Claims

open StatFormal.Wave22c (gaussPlan)
open StatFormal.Wave18b (muSB)
open StatFormal.SBFairness (cEps kappa v geo)
open StatFormal.Wave4b (endpointMixture1)
open StatFormal.Wave9b (stoPlan qcost)

/-! ### SB `prop:mixture`, `lem:equiv` -/

/-- `prop:mixture` with the path-space half of `lem:equiv`: a Schrödinger bridge `P` relative to an `ε`-Brownian
reference `R` has `dP/dR = g(X₀, X₁)` (the mixture of the reference bridges over its endpoint law `π*`), `π*` is the
static minimiser with the same value, and for every `t ∈ [0,1]` the law of `((X₀,X₁), X_t)` is `bridgeLaw ε t π*`, so
`Law(X_t) = endpointMixture1 ε t π*` (`eq:mixture`, `eq:convolution`) and `Law(X₀, X_t) = stoPlan ε t π*`. -/
def mixture_bridge : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (ε : ℝ) (μ ν : Measure ℝ) (X : ℝ → Ω → ℝ) (R P : Measure Ω),
    0 < ε → IsProbabilityMeasure μ → IsBrownianRef ε μ X R → IsSchrodingerBridge X R μ ν P →
      R.map (fun ω => (X 0 ω, X 1 ω)) = refPlan ε μ ∧
      IsStaticBridge ε μ ν (P.map (fun ω => (X 0 ω, X 1 ω))) ∧
      klDiv P R = klDiv (P.map (fun ω => (X 0 ω, X 1 ω))) (refPlan ε μ) ∧
      (∃ g : ℝ × ℝ → ℝ≥0∞, Measurable g ∧ P.map (fun ω => (X 0 ω, X 1 ω)) = (refPlan ε μ).withDensity g ∧
        P = R.withDensity (fun ω => g (X 0 ω, X 1 ω))) ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        P.map (fun ω => ((X 0 ω, X 1 ω), X t ω)) = bridgeLaw ε t (P.map (fun ω => (X 0 ω, X 1 ω))) ∧
        P.map (X t) = endpointMixture1 ε t (P.map (fun ω => (X 0 ω, X 1 ω))) ∧
        P.map (fun ω => (X 0 ω, X t ω)) = stoPlan ε t (P.map (fun ω => (X 0 ω, X 1 ω)))

/-- `lem:equiv`, existence and uniqueness transfer: every static minimiser `π` is the endpoint law of a Schrödinger
bridge, and two Schrödinger bridges with the same endpoint law coincide. -/
def mixture_exists : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (ε : ℝ) (μ ν : Measure ℝ) (X : ℝ → Ω → ℝ) (R : Measure Ω),
    0 < ε → IsProbabilityMeasure μ → IsBrownianRef ε μ X R →
      (∀ π : Measure (ℝ × ℝ), IsStaticBridge ε μ ν π →
        ∃ P : Measure Ω, IsSchrodingerBridge X R μ ν P ∧ P.map (fun ω => (X 0 ω, X 1 ω)) = π) ∧
      ∀ P P' : Measure Ω, IsSchrodingerBridge X R μ ν P → IsSchrodingerBridge X R μ ν P' →
        P.map (fun ω => (X 0 ω, X 1 ω)) = P'.map (fun ω => (X 0 ω, X 1 ω)) → P = P'

/-- `lem:equiv`, static half: for `ν` with a Lebesgue density `q` of finite entropy and `μ, ν ∈ 𝒫₂`, a coupling has
`KL(π ‖ R₀₁) < ∞` iff `KL(π ‖ μ ⊗ ν) < ∞`, and then
`ε KL(π ‖ R₀₁) = ∫ ½(x−y)² dπ + ε KL(π ‖ μ ⊗ ν) + ε(∫ log q dν + ½ log(2πε))`. -/
def mixture_static : Prop :=
  ∀ (ε : ℝ) (μ ν : Measure ℝ) (q : ℝ → ℝ), 0 < ε → IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    Measurable q → (∀ y, 0 ≤ q y) → ν = volume.withDensity (fun y => ENNReal.ofReal (q y)) →
    Integrable (fun y => Real.log (q y)) ν → Integrable (fun x : ℝ => x ^ 2) μ → Integrable (fun y : ℝ => y ^ 2) ν →
    ∀ π : Measure (ℝ × ℝ), IsCoupling π μ ν →
      (klDiv π (refPlan ε μ) ≠ ∞ ↔ klDiv π (μ.prod ν) ≠ ∞) ∧
      (klDiv π (μ.prod ν) ≠ ∞ →
        ε * (klDiv π (refPlan ε μ)).toReal =
          ∫ z, (z.1 - z.2) ^ 2 / 2 ∂π + ε * (klDiv π (μ.prod ν)).toReal +
            ε * (∫ y, Real.log (q y) ∂ν + Real.log (2 * Real.pi * ε) / 2))

/-- `lem:equiv`, consequence: under the hypotheses of `mixture_static` the entropic cost is finite and the static
Schrödinger minimisers are exactly the entropic optimal plans of the frozen Wave P3b (`IsEntPlan`). -/
def mixture_static_plan : Prop :=
  ∀ (ε : ℝ) (μ ν : Measure ℝ) (q : ℝ → ℝ), 0 < ε → IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    Measurable q → (∀ y, 0 ≤ q y) → ν = volume.withDensity (fun y => ENNReal.ofReal (q y)) →
    Integrable (fun y => Real.log (q y)) ν → Integrable (fun x : ℝ => x ^ 2) μ → Integrable (fun y : ℝ => y ^ 2) ν →
      entropicTransportCost sqCost ε.toNNReal μ ν ≠ ∞ ∧
        ∀ π : Measure (ℝ × ℝ), IsStaticBridge ε μ ν π ↔ IsEntPlan ε μ ν π

/-- `prop:mixture` + `lem:gaussplan` + `eq:gaussmarg` on path space: for `μ = N(a,σ²)`, `ν = N(a⋆,τ²)` and every
`ε`-Brownian reference, the Schrödinger bridge exists and is unique, its endpoint law is the Gaussian plan with
cross-covariance `c_ε`, and its time-`t` law is `N((1−t)a + ta⋆, v(t))`. -/
def mixture_gauss : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (ε σ τ a astar : ℝ) (X : ℝ → Ω → ℝ) (R : Measure Ω),
    0 < ε → 0 < σ → 0 < τ → IsBrownianRef ε (gaussianReal a (σ ^ 2).toNNReal) X R →
      (∃! P : Measure Ω,
        IsSchrodingerBridge X R (gaussianReal a (σ ^ 2).toNNReal) (gaussianReal astar (τ ^ 2).toNNReal) P) ∧
      ∀ P : Measure Ω,
        IsSchrodingerBridge X R (gaussianReal a (σ ^ 2).toNNReal) (gaussianReal astar (τ ^ 2).toNNReal) P →
          P.map (fun ω => (X 0 ω, X 1 ω)) = gaussPlan a σ astar τ (cEps ε σ τ) ∧
          ∀ t ∈ Icc (0 : ℝ) 1, P.map (X t) = muSB ε σ τ a astar t

/-! ### Path-space discharges: `prop:noisefree` -/

/-- `prop:noisefree`, exact form, on path space: `μ^ε_{s,t}` is the time-`t` law of the Schrödinger bridge
`P*_ε(N(a,σ²), N(a⋆,τ²))`, `μ^0_{s,t}` the McCann interpolant of an optimal transport plan. -/
def noisefree_bridge_exact_path : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (ε σ τ a astar t : ℝ) (X : ℝ → Ω → ℝ) (R P : Measure Ω) (P₀ : Measure (ℝ × ℝ)),
    0 < ε → 0 < σ → 0 < τ → t ∈ Ioo (0 : ℝ) 1 →
    IsBrownianRef ε (gaussianReal a (σ ^ 2).toNNReal) X R →
    IsSchrodingerBridge X R (gaussianReal a (σ ^ 2).toNNReal) (gaussianReal astar (τ ^ 2).toNNReal) P →
    IsEntPlan 0 (gaussianReal a (σ ^ 2).toNNReal) (gaussianReal astar (τ ^ 2).toNNReal) P₀ →
      wassersteinEDist 2 (P.map (X t)) (endpointMixture1 0 t P₀) =
          ENNReal.ofReal (t * (1 - t) * (kappa ε σ τ - 2 * σ * τ) / (√(v ε σ τ t) + √(v 0 σ τ t))) ∧
        kappa ε σ τ - 2 * σ * τ = ε ^ 2 / (kappa ε σ τ + 2 * σ * τ)

/-- `prop:noisefree`, `W₂(μ^ε_{s,t}, μ^0_{s,t}) = Θ(σ⁴)` on path space (`σ² = εt(1−t)`), for any family of
Schrödinger bridges `P ε` relative to `ε`-Brownian references `R ε`. -/
def noisefree_bridge_theta_path : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (σ τ a astar t : ℝ) (X : ℝ → Ω → ℝ) (R P : ℝ → Measure Ω)
    (P₀ : Measure (ℝ × ℝ)), 0 < σ → 0 < τ → t ∈ Ioo (0 : ℝ) 1 →
    (∀ ε, 0 < ε → IsBrownianRef ε (gaussianReal a (σ ^ 2).toNNReal) X (R ε) ∧
      IsSchrodingerBridge X (R ε) (gaussianReal a (σ ^ 2).toNNReal) (gaussianReal astar (τ ^ 2).toNNReal) (P ε)) →
    IsEntPlan 0 (gaussianReal a (σ ^ 2).toNNReal) (gaussianReal astar (τ ^ 2).toNNReal) P₀ →
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ ε in 𝓝[>] 0,
        ENNReal.ofReal (c₁ * (ε * t * (1 - t)) ^ 2) ≤ wassersteinEDist 2 ((P ε).map (X t)) (endpointMixture1 0 t P₀) ∧
          wassersteinEDist 2 ((P ε).map (X t)) (endpointMixture1 0 t P₀) ≤ ENNReal.ofReal (c₂ * (ε * t * (1 - t)) ^ 2)

/-- `prop:noisefree`, the limits on path space. -/
def noisefree_limits_path : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (σ τ a astar t : ℝ) (X : ℝ → Ω → ℝ) (R P : ℝ → Measure Ω)
    (P₀ : Measure (ℝ × ℝ)), 0 < σ → 0 < τ → t ∈ Ioo (0 : ℝ) 1 →
    (∀ ε, 0 < ε → IsBrownianRef ε (gaussianReal a (σ ^ 2).toNNReal) X (R ε) ∧
      IsSchrodingerBridge X (R ε) (gaussianReal a (σ ^ 2).toNNReal) (gaussianReal astar (τ ^ 2).toNNReal) (P ε)) →
    IsEntPlan 0 (gaussianReal a (σ ^ 2).toNNReal) (gaussianReal astar (τ ^ 2).toNNReal) P₀ →
      Tendsto (fun ε => (wassersteinEDist 2 ((P ε).map (X t)) (endpointMixture1 0 t P₀)).toReal /
          (ε * t * (1 - t)) ^ 2) (𝓝[>] 0)
        (𝓝 (1 / (8 * σ * τ * geo σ τ t * (t * (1 - t))))) ∧
      Tendsto (fun ε => (wassersteinEDist 2 (endpointMixture1 0 t P₀ ∗ gaussianReal 0 (ε * t * (1 - t)).toNNReal)
          (endpointMixture1 0 t P₀)).toReal / (ε * t * (1 - t))) (𝓝[>] 0)
        (𝓝 (1 / (2 * geo σ τ t))) ∧
      Tendsto (fun ε => (wassersteinEDist 2 ((P ε).map (X t)) (endpointMixture1 0 t P₀)).toReal /
          (wassersteinEDist 2 (endpointMixture1 0 t P₀ ∗ gaussianReal 0 (ε * t * (1 - t)).toNNReal)
            (endpointMixture1 0 t P₀)).toReal) (𝓝[>] 0) (𝓝 0)

/-! ### Path-space discharges: `thm:gaussian` -/

/-- `thm:gaussian`, `eq:gaussF`, on path space: `μ^ε_{s,t}` the time-`t` laws of the Schrödinger bridges
`P*_ε(R_s, ν)`, `R_s = N(a_s, σ_s²)`, `ν = N(a⋆, τ²)`, `ε > 0`. -/
def gaussianthm_F_path : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (ε σ₀ σ₁ τ a₀ a₁ astar t : ℝ) (X : ℝ → Ω → ℝ) (R₀ R₁ P₀ P₁ : Measure Ω),
    0 < ε → 0 < σ₀ → 0 < σ₁ → 0 < τ → t ∈ Icc (0 : ℝ) 1 →
    IsBrownianRef ε (gaussianReal a₀ (σ₀ ^ 2).toNNReal) X R₀ →
    IsBrownianRef ε (gaussianReal a₁ (σ₁ ^ 2).toNNReal) X R₁ →
    IsSchrodingerBridge X R₀ (gaussianReal a₀ (σ₀ ^ 2).toNNReal) (gaussianReal astar (τ ^ 2).toNNReal) P₀ →
    IsSchrodingerBridge X R₁ (gaussianReal a₁ (σ₁ ^ 2).toNNReal) (gaussianReal astar (τ ^ 2).toNNReal) P₁ →
      wassersteinEDist 2 (P₀.map (X t)) (P₁.map (X t)) ^ 2 =
        ENNReal.ofReal ((1 - t) ^ 2 * (a₀ - a₁) ^ 2 + (√(v ε σ₀ τ t) - √(v ε σ₁ τ t)) ^ 2)

/-- `thm:gaussian` (a) on path space: the mean gap is `(1−t)(a₀ − a₁)`. -/
def gaussianthm_a_path : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (ε σ₀ σ₁ τ a₀ a₁ astar t : ℝ) (X : ℝ → Ω → ℝ) (R₀ R₁ P₀ P₁ : Measure Ω),
    0 < ε → 0 < σ₀ → 0 < σ₁ → 0 < τ → t ∈ Icc (0 : ℝ) 1 →
    IsBrownianRef ε (gaussianReal a₀ (σ₀ ^ 2).toNNReal) X R₀ →
    IsBrownianRef ε (gaussianReal a₁ (σ₁ ^ 2).toNNReal) X R₁ →
    IsSchrodingerBridge X R₀ (gaussianReal a₀ (σ₀ ^ 2).toNNReal) (gaussianReal astar (τ ^ 2).toNNReal) P₀ →
    IsSchrodingerBridge X R₁ (gaussianReal a₁ (σ₁ ^ 2).toNNReal) (gaussianReal astar (τ ^ 2).toNNReal) P₁ →
      ∫ x, x ∂(P₀.map (X t)) - ∫ x, x ∂(P₁.map (X t)) = (1 - t) * (a₀ - a₁)

/-- `thm:gaussian` (d), flow cost, on path space: `W₂²(R_s, μ^ε_{s,t})`. -/
def gaussianthm_d_flow_path : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (ε σ τ a astar t : ℝ) (X : ℝ → Ω → ℝ) (R P : Measure Ω),
    0 < ε → 0 < σ → 0 < τ → t ∈ Icc (0 : ℝ) 1 →
    IsBrownianRef ε (gaussianReal a (σ ^ 2).toNNReal) X R →
    IsSchrodingerBridge X R (gaussianReal a (σ ^ 2).toNNReal) (gaussianReal astar (τ ^ 2).toNNReal) P →
      wassersteinEDist 2 (gaussianReal a (σ ^ 2).toNNReal) (P.map (X t)) ^ 2 =
        ENNReal.ofReal (t ^ 2 * (astar - a) ^ 2 + (√(v ε σ τ t) - σ) ^ 2)

/-- `thm:gaussian` (d), stochastic cost, on path space: `E_{P*}|X_t − X₀|²`. -/
def gaussianthm_d_sto_path : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (ε σ τ a astar t : ℝ) (X : ℝ → Ω → ℝ) (R P : Measure Ω),
    0 < ε → 0 < σ → 0 < τ → t ∈ Icc (0 : ℝ) 1 →
    IsBrownianRef ε (gaussianReal a (σ ^ 2).toNNReal) X R →
    IsSchrodingerBridge X R (gaussianReal a (σ ^ 2).toNNReal) (gaussianReal astar (τ ^ 2).toNNReal) P →
      0 ≤ (a - astar) ^ 2 + σ ^ 2 + τ ^ 2 - 2 * cEps ε σ τ ∧
        qcost (P.map (fun ω => (X 0 ω, X t ω))) =
          ENNReal.ofReal (t ^ 2 * ((a - astar) ^ 2 + σ ^ 2 + τ ^ 2 - 2 * cEps ε σ τ) + ε * t * (1 - t))

end Claims

end StatFormal.Wave29q
