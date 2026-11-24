import StatFormal.Archive.Wave24f.Statements
import StatFormal.Archive.Wave24c.Statements
import StatFormal.Archive.WaveP3a.Statements
import StatFormal.Lib.Distances.TV
import StatFormal.Archive.OTFD.WaveL3.Statements
import StatFormal.Archive.Wave24e.Statements
import StatFormal.Archive.Wave23b.Statements
import StatFormal.Archive.Wave23c.Statements

/-!
# FROZEN STATEMENTS — wave P3e (partial-audit blocker RIEM, "Riemannian geometry layer"): model spaces and CAT(0)
# comparison in place of a general Riemannian layer — otfd T `eq:hadamard-lower` on every CAT(0) space; G
# `lem:polish`, `lem:decoupling` on curved targets; G `prop:quantile` (b) on Hadamard targets; G `lem:jacobicosh`
# (transport corollary, sharpness), T `prop:Cb`/`eq:basebridge`, G `cor:discretisation` (c) on `H_k`; G
# `prop:reference` (c), (d), `prop:equivariance` on `S^d`, `H_k`; G `thm:flatlimit` and T `thm:pop-sieve` (`H₀`)
# unconditionally on `S^d`; the rank-pair premises of T `thm:population`, `prop:transfer-M` discharged

Sources (current text of `otfd/papers/`, checked 2026-10-16; audit rows `inventory/PARTIAL_AUDIT.md`, blocker RIEM):
* T `prop:hadamard-distortion`, `eq:hadamard-lower` (`T_tangent/supp_moved.tex:59-79`, proof `app_proofs.tex:332-345`);
  `prop:base`, `eq:basebridge` (`sec_tangent_theory.tex:641-660`); `prop:Cb` (`supp_moved.tex:1017-1049`, proof
  `app_proofs.tex:205-240`); `thm:population` (`sec_tangent_theory.tex:137-170`); `thm:pop-sieve`
  (`sec_tangent_theory.tex:252-268`, the `H₀` remark `:270-276`); `prop:transfer-M` (`supp_toolkit.tex:181-218`).
* G `lem:polish` (`G_geodesic/main.tex:242-245`, proof `appendix.tex:3-56`); `lem:decoupling` (`appendix.tex:80-129`);
  `prop:reference` (`main.tex:371-405`); `prop:quantile` (`main.tex:550-563`), `eq:quantile-pointwise`
  (`supp_moved.tex:121-124`), `ex:geometries` (ii) (`main.tex:299-307`); `prop:equivariance` (`main.tex:638-650`);
  `lem:jacobicosh` (`appendix.tex:131-148`, proof `:150-201`); `cor:discretisation` (c) (`supp_moved.tex:202-237`).
Imports the frozen statement files of waves 24f (`minkB`, `OnHyp`, `tanNorm`, `hypExp`, `hypDist`, `otCost`), 24c
(`frechetSet`, `IsEntPlanG`), 24e (`refV`), 23b (`cK`, `sgnK`; through it 8c `IsRankPair`, `IsGradMap`, 5b
`GibbsHyp`, `gibbsMean`), P3a (`sphTransport`, `sphD`, `sphCost`, `refCurve`; through it 6b `sphDist`, `sphExp`), L3
(through it L1 `IsCMMapAE`, `LipNull`, `Euc`; 1 `PellClass`, `truncK`; 8b `embed`) and the locked
`Foundations/Distances/TV` (`tvDist`), not copied. New definitions: `IsCAT0`, `IsGeodFrom`, `hypLog`, `hypTransport`,
`hypD`, `hypCost`, `hypRef`, `hypRefHat`, `sphLog`, `curveD`, `curveSet`, `frechetJ`, `psiT`.

Covered (27 claims):
* Model spaces: `cat0_inner` (every real inner product space is CAT(0): the flat case `k = 0`); `hyperboloid_cat0`
  (on `H_k`: `hypDist` is a metric, midpoints exist, every midpoint satisfies CN, `Exp_p` maps `T_pH_k` into `H_k`,
  `Log_p` with `B(p, Log_p x) = 0`, `|Log_p x| = d(p, x)`, `Exp_p ∘ Log_p = id`, radial geodesics, and the first-order
  property of `Log_p` — every hypothesis of `hadamard_lower_cat0` holds on the paper's model space).
* T `eq:hadamard-lower` (row: "constant curvature only; variable curvature and `k = 0`"): `hadamard_lower_cat0`
  (pointwise, every CAT(0) space), `hadamard_cost_cat0` (`c_geo ≥ c_m^{H₀}` and `OT_{c_geo} ≥ OT_{c_m^{H₀}}`).
* G `lem:polish` (row: "flat case only"): `polish_metric` (any complete separable metric target).
* G `lem:decoupling` (row: "flat case only"): `decoupling_metric` (Tonelli, finiteness and continuity off a null set
  and the characterisation of `argmin J` for any separable metric target; nonemptiness and a.e. uniqueness on complete
  CAT(0) targets).
* G `prop:quantile` (row: "flat case only"): (b) on Hadamard targets — `frechet_cat0` (Sturm: unique Fréchet mean
  under a second moment), `quantile_hadamard` (unique pointwise minimiser at EVERY `v`, `t`, lying in `B̄(o_t, ρ)` for
  any `ρ`; continuity of `v ↦ q_v(t)`), `quantile_cat0_stable` (`d ≤ 4R · TV`); (a) and the curve-level uniqueness via
  `decoupling_metric` with `ν = π_ε(· | v)`.
* G `lem:jacobicosh` (row: "matrix Riccati core"): the consequence and its sharpness on the hyperbolic space,
  `jacobicosh_transport_hyp` (`Γ` the parallel transport: isometric, identity on `span{p, q}^⊥`, `Γ Log_p q =
  −Log_q p`; `d(Exp_q Γξ, Exp_p ξ) ≤ cosh(k|ξ|) d(p, q)`), `jacobicosh_sharp_hyp` (the factor is the limit ratio).
* T `eq:basebridge` (row: "abstract skeleton"), with T `prop:Cb` (a)/(i): `basebridge_hyp` (`C_b = cosh(kb)`,
  `L_b = sinh(kb)/(kb)` on `H_k`), `basebridge_sphere` (`C_b = L_b = 1` on `S^d`), pointwise and in `D_∞` form.
* G `cor:discretisation` (c), Hadamard case, on `H_k`: `disc_base_cost_hyp` (cost bound with `D(m, m̂)` multiplied by
  `cosh(k s b)`), `disc_base_rank_hyp` (rank bound).
* G `prop:reference` (row: "(c) support, (d) equivariance"): `reference_support_sphere`, `reference_support_hyp`
  (`D(m, E_m(sv)) ≤ s‖v‖`, resp. `= s‖v‖`: the hypothesis of the frozen `reference_calibration` holds on the model
  spaces), `reference_equivariance_sphere` ((d) pathwise on `S^d`, cost invariance).
* G `prop:equivariance` (row: "cost invariance as hypothesis"): `equivariance_plan_sphere`, `equivariance_plan_hyp`
  (the premise of the frozen `equivariance_plan` discharged for the geodesic cost of `S^d`, `H_k`), `equivariance_hyp`
  (Lorentz maps commute with `Exp`, `Log`, `Γ` and preserve `d`).
* G `thm:flatlimit` (row: "conditional on Riemannian Taylor bound"): `flatlimit_sphere` (the Taylor premise of the
  frozen `flatlimit` DISCHARGED on `S^d` with the paper's `Θ(r) = 1 − r cot r`, `r = ρ₀ + sb < π`, `esssup_t |v(t)| ≤ b`:
  unconditional on the unit sphere; the second-order analysis of `½ arccos(A cos σ + B sin σ)²` in
  `Foundations/ModelSpaces/SphereTaylor`).
* T `thm:pop-sieve` (row: "`H₀` mean-squared `D₂` clause"): `pop_sieve_sphere` (on `S^d`, where `dExp` is globally
  bounded, as the paper's remark says).
* T `thm:population` (row: "manifold form on given rank pairs"): `pop_manifold_mccann`; T `prop:transfer-M` (row:
  "(i)–(iii) on given rank pairs"): `transferM_push_mccann`, `transferM_unique_mccann`, `transferM_cocycle_mccann`.
  Each is `(existence of the rank pairs under the paper's hypotheses) ∧ (the frozen claim's body, frozen binders)`;
  `RouteImplies` checks `Claims.X_mccann → Wave23b.Claims.X` mechanically.

Not covered (declared):
* General Riemannian geometry. The bridges "a Hadamard manifold is a complete CAT(0) space" (Bridson–Haefliger
  II.1A.6, II.4.1), "the Riemannian `Log_p` has the first-order property" (`dExp_p(0) = id`), "a complete Riemannian
  manifold is a complete separable metric space with a measurable selection of minimal geodesics" are textbook facts,
  not formalised; the CAT(0)/metric claims are GENERALISATIONS whose application to a given manifold uses them (all
  are proved for `H_k` and for inner product spaces).
* T `eq:hadamard-two-sided` and G `lem:jacobicosh`/`cor:discretisation` (c) for VARIABLE curvature (need a lower
  curvature bound: Rauch/Toponogov); the Jacobi-field statement of `lem:jacobicosh` and its constant-curvature
  equality; `prop:Cb` (a) for locally symmetric spaces beyond `S^d`, `H_k`, (b), (ii), (iii) (Fisher–Rao, SPD).
* G `lem:decoupling`, `prop:quantile` (a): existence of a minimiser on compact non-CAT(0) targets (spheres) — needs a
  measurable selection theorem (Kuratowski–Ryll-Nardzewski, measurable maximum theorem), absent from Mathlib; the
  sphere case `ρ < π/2` of `prop:quantile` (b) (Afsari/Karcher convexity); continuity of `v ↦ Q_ε(v)` into `(𝒳, D)`.
* G `cor:discretisation` (c): the variance bound `E D(m̂, m)² ≤ E D(m, X)²/n₀` (needs the first-variation formula
  for `Log_b`, a Riemannian fact).
* G `thm:flatlimit`: the Riemannian Taylor bound stays a premise on `H_k` and on variable-curvature targets
  (`Θ(r) ≤ κr coth κr − 1`, Hessian comparison).
* G `prop:reference` (c), (d) and `prop:equivariance` on targets other than `S^d`, `H_k` (they need `Exp` of a general
  manifold); on `H_k`, (d) at the level of the reference process (only `Exp`/`Log`/`Γ` commutation and cost
  invariance are proved); the clauses of (d) on the Fréchet mean curve, the data covariance and the isotropic kernel;
  in `prop:equivariance`, the quantile and rank clauses keep the conditional-law transformation `π'(· | Φv) = ψ#π(· | v)`
  as the hypothesis of the frozen `equivariance_quantile`, `equivariance_rank` (only the plan clause is discharged).
* T `thm:pop-sieve`, `H₀` clause, under a common pointwise bound on the output fields (general `M`, via `eq:L`), and on
  targets other than `S^d` with a globally bounded exponential differential.
* T `prop:chart` (i), (iii) on curved `M` (isometry equivariance of the chart constructions: Fréchet mean curves,
  frames and parallel transport along broken geodesics); T `thm:population`/`prop:transfer-M`: the chart itself
  (`E_m` injective on `𝒟_r` with Borel inverse) stays the paper's model assumption.

Encodings (to be checked by the critic):
* CAT(0) = Bruhat–Tits: a metric space with midpoints in which EVERY midpoint `m` of `y, z` satisfies
  `d(m, x)² ≤ ½d(y, x)² + ½d(z, x)² − ¼d(y, z)²` (`IsCAT0`; Bridson–Haefliger II.1.9). A complete `IsCAT0` space is a
  Hadamard space. Replacing "Hadamard manifold" by "(complete) CAT(0) space" is a GENERALISATION wherever used
  (`hadamard_*_cat0`, `frechet_cat0`, `quantile_*`, `decoupling_metric` (iv)); conversely no claim specialises the
  paper's Hadamard statements except those on `H_k` (constant curvature `−k²`: SPECIALISATION of "curvature
  `≥ −κ²`").
* The logarithm at `p` of a CAT(0) space is any `Log : M → E` (`E` a real inner product space) with the first-order
  property `d(γ_x(s), γ_y(s))/s → ‖Log x − Log y‖` (`s ↓ 0`) along constant-speed geodesics `γ_x` from `p`
  (`IsGeodFrom`); on a Riemannian manifold `γ_x(s) = Exp_p(s Log_p x)`. No global property of `Log` is assumed.
* "Complete Riemannian manifold `M`" in G `lem:polish`, `lem:decoupling` is replaced by "complete separable metric
  space" (GENERALISATION; the paper's proofs use only this, plus Hopf–Rinow for existence, which we replace by the
  CAT(0) hypothesis there); `T = [0, 1]` as `Icc` with any probability `λ` (lem:polish) or any measurable space with
  a probability `λ` (decoupling); the curve space `𝒳` is the SET `curveSet` of measurable curves with `D(x, m) < ∞`
  (before passing to `λ`-a.e. classes; the claims state `D = 0 ⇔ a.e. equal`, so the quotient is the paper's metric
  space); `D` in `[0, ∞]`; the geodesic clause takes a measurable geodesic bicombing `σ` of `M` (the paper's
  "measurably selected minimal geodesic") as a CONDITION. Laws of curves in `decoupling_metric` live on a label
  space `Ω` with a jointly measurable evaluation (`lem:evaluation`).
* `H_k = {B(x, x) = −1/k², x₀ > 0}` (frozen); `hypLog k p x = (kd/sinh(kd))(x − cosh(kd)p)`, `d = d(p, x)` (at
  `x = p`, `0/0 = 0` gives `Log_p p = 0`, the true value); `hypTransport k p q ξ = ξ + (k²B(q, ξ)/(1 + c))(p + q)`,
  `c = −k²B(p, q) ≥ 1` (denominator `≥ 2`); isometries of `H_k` as linear maps preserving `B` (`equivariance_hyp`;
  orientation of the sheet not needed for the identities); isometries of `S^d` as linear isometries of `ℝ^{d+1}`
  (every isometry of `S^d` is one; not formalised). Curves on `H_k` take values in `ℝ × ℝ^d`; `hypD`, `hypCost` are
  Bochner integrals used ONLY under integrability hypotheses (`d(m, x)²`, `d(m, m̂)²` integrable), under which every
  integrand appearing is proved integrable — no junk values.
* Fréchet sets are the frozen `frechetSet` (`∫⁻ edist²`); conditional laws in `quantile_hadamard` are any family
  `κ v t` (the entropic conditionals pushed by evaluation at `t`) carried by `B̄(o_t, ρ)`; their TV-continuity in `v`
  is a HYPOTHESIS of the continuity clause (a property of the entropic plan, not of the geometry).
* `disc_base_rank_hyp`: the reference fields `Hs` with `|ev v(t)| ≤ b‖v‖` (the constant `b_K` of `prop:cap` (a)) and
  `∫|ev v(t)|² dλ ≤ ‖v‖²`; the costs are unbounded off `{‖v‖ ≤ 1}`; the proof clips them there (same plans, same rank
  maps), so `lem:stability` applies — the claim needs no boundedness hypothesis.
* `D_∞` sups are taken in `ℝ≥0∞`. `pop_sieve_sphere`: a field space `H` whose norm dominates the `L²(λ)` norm of the
  tangent fields (`H₀` itself, or `H₁`). `flatlimit_sphere`: `H` with the `H₀` inner product
  `⟨v, v'⟩ = ∫ ⟨ev v(t), ev v'(t)⟩ dλ` (the tangent route's `L²` geometry), `μ`-a.s. `esssup_t |v(t)| ≤ b` (as
  printed), `L x` any element of `H` whose field is `λ`-a.e. `Log_{m(t)} x(t)` (`sphLog`); tangency of `ev v` is also
  only `λ`-a.e., so `ev` may pick arbitrary measurable representatives of `H₀` classes (then `L x` exists in `H₀`),
  measurability of the cost and of `D(m, ·)²` and the Gibbs forms of the two plans as in the frozen claim.

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/
set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.WaveP3e

open StatFormal.Wave24f (minkB OnHyp tanNorm hypExp hypDist otCost)
open StatFormal.Wave24c (frechetSet)
open StatFormal.Distances (tvDist)
open StatFormal.OTFD.Wave6b (sphDist sphExp)
open StatFormal.WaveP3a (sphTransport)
open StatFormal.OTFD.WaveL1 (IsCMMapAE Euc LipNull)
open StatFormal.OTFD.Wave8c (IsRankPair IsGradMap)
open StatFormal.Wave23b (cK sgnK)
open StatFormal.OTFD.Wave1 (PellClass truncK)
open StatFormal.OTFD.Wave8b (embed)
open StatFormal.Wave24c (IsEntPlanG)
open StatFormal.OTFD.Wave5b (GibbsHyp gibbsMean gibbsPlan)
open StatFormal.SBFairness.Stability (tv)
open StatFormal.Wave24e (refV)
open StatFormal.WaveP3a (sphCost refCurve sphD)

/-- CAT(0) in the sense of Bruhat–Tits: midpoints exist, and every midpoint `m` of `y, z` satisfies the CN inequality
`d(m, x)² ≤ ½d(y, x)² + ½d(z, x)² − ¼d(y, z)²` for all `x`. -/
def IsCAT0 (M : Type*) [MetricSpace M] : Prop :=
  (∀ y z : M, ∃ m : M, dist m y = dist y z / 2 ∧ dist m z = dist y z / 2) ∧
    ∀ x y z m : M, dist m y = dist y z / 2 → dist m z = dist y z / 2 →
      dist m x ^ 2 ≤ dist y x ^ 2 / 2 + dist z x ^ 2 / 2 - dist y z ^ 2 / 4

/-- `γ` is a constant-speed geodesic from `p` to `x` on `[0, 1]`. -/
def IsGeodFrom {M : Type*} [MetricSpace M] (p x : M) (γ : ℝ → M) : Prop :=
  γ 0 = p ∧ γ 1 = x ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, dist (γ s) (γ t) = |s - t| * dist p x

section Hyp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The logarithm of `H_k`: `Log_p x = (kd/sinh(kd)) (x − cosh(kd) p)`, `d = d(p, x)`. -/
def hypLog (k : ℝ) (p x : ℝ × E) : ℝ × E :=
  (k * hypDist k p x / Real.sinh (k * hypDist k p x)) • (x - Real.cosh (k * hypDist k p x) • p)

/-- Parallel transport of `H_k` along the geodesic from `p` to `q`:
`Γ_{p→q} ξ = ξ + (k² B(q, ξ)/(1 − k² B(p, q))) (p + q)`. -/
def hypTransport (k : ℝ) (p q ξ : ℝ × E) : ℝ × E :=
  ξ + (k ^ 2 * minkB q ξ / (1 + -(k ^ 2) * minkB p q)) • (p + q)

/-- The curve distance on `H_k`, `D(y, x) = (∫ d(y(t), x(t))² dλ)^{1/2}` (used under integrability hypotheses). -/
def hypD (k : ℝ) (lam : Measure ℝ) (y x : ℝ → ℝ × E) : ℝ := √(∫ t, hypDist k (y t) (x t) ^ 2 ∂lam)

/-- The cost `½ D(y, x)²` on `H_k` (`eq:cost`). -/
def hypCost (k : ℝ) (lam : Measure ℝ) (y x : ℝ → ℝ × E) : ℝ := (∫ t, hypDist k (y t) (x t) ^ 2 ∂lam) / 2

/-- The reference curve `E_m(s v)(t) = Exp_{m(t)}(s v(t))` on `H_k`. -/
def hypRef (k : ℝ) (m v : ℝ → ℝ × E) (s : ℝ) : ℝ → ℝ × E := fun t => hypExp k (m t) (s • v t)

/-- The reference curve at an estimated base, `E_{m̂}(s Γv)(t) = Exp_{m̂(t)}(s Γ_t v(t))`. -/
def hypRefHat (k : ℝ) (m mh v : ℝ → ℝ × E) (s : ℝ) : ℝ → ℝ × E :=
  fun t => hypExp k (mh t) (s • hypTransport k (m t) (mh t) (v t))

end Hyp

/-- The logarithm of the unit sphere, `Log_p y = (d/sin d)(y − cos d · p)`, `d = d_S(p, y)` (`0/0 = 0` gives
`Log_p p = 0`, the true value). -/
def sphLog {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (p y : E) : E :=
  (sphDist p y / Real.sin (sphDist p y)) • (y - Real.cos (sphDist p y) • p)

section Curves

variable {T M : Type*} [MeasurableSpace T]

/-- The curve distance `D(x, y) = (∫ d(x(t), y(t))² dλ)^{1/2}` in `[0, ∞]` (`eq:D`). -/
def curveD [PseudoEMetricSpace M] (lam : Measure T) (x y : T → M) : ℝ≥0∞ :=
  (∫⁻ t, edist (x t) (y t) ^ (2 : ℝ) ∂lam) ^ (1 / 2 : ℝ)

/-- The curve space `𝒳 = {x : T → M measurable : D(x, m) < ∞}` (before passing to `λ`-a.e. classes). -/
def curveSet [MetricSpace M] [MeasurableSpace M] (lam : Measure T) (m : T → M) : Set (T → M) :=
  {x | Measurable x ∧ curveD lam x m < ⊤}

/-- `J(z) = ∫ D(z, x)² ν(dx)` for a law `ν` on curve labels `Ω` with evaluation `ev` (`D² = ∫ d² dλ`), in `[0, ∞]`. -/
def frechetJ {Ω : Type*} [MeasurableSpace Ω] [PseudoEMetricSpace M] (lam : Measure T) (ν : Measure Ω)
    (ev : Ω → T → M) (z : T → M) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ t, edist (z t) (ev ω t) ^ (2 : ℝ) ∂lam ∂ν

/-- `Ψ_t(p) = ∫ d(p, x(t))² ν(dx)`, in `[0, ∞]`. -/
def psiT {Ω : Type*} [MeasurableSpace Ω] [PseudoEMetricSpace M] (ν : Measure Ω) (ev : Ω → T → M) (t : T)
    (p : M) : ℝ≥0∞ :=
  ∫⁻ ω, edist p (ev ω t) ^ (2 : ℝ) ∂ν

end Curves

namespace Claims

/-! ### Model spaces -/

/-- The flat model (`k = 0`): every real inner product space is CAT(0) (CN holds with equality). -/
def cat0_inner : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E], IsCAT0 E

/-- The hyperbolic space `H_k` of curvature `−k²` (`k > 0`) is a CAT(0) space with a first-order logarithm: `hypDist`
is a metric on `H_k`; midpoints exist and every midpoint satisfies CN; `Exp_p` maps `T_pH_k` into `H_k`;
`Log_p x ∈ T_pH_k`, `|Log_p x| = d(p, x)`, `Exp_p(Log_p x) = x`; `s ↦ Exp_p(s Log_p x)` is a constant-speed geodesic
from `p` to `x`; and `d(Exp_p(s Log_p x), Exp_p(s Log_p y))/s → |Log_p x − Log_p y|` as `s ↓ 0`. -/
def hyperboloid_cat0 : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (k : ℝ), 0 < k →
    (∀ x y z : ℝ × E, OnHyp k x → OnHyp k y → OnHyp k z →
      hypDist k x x = 0 ∧ hypDist k x y = hypDist k y x ∧ (hypDist k x y = 0 → x = y) ∧
        hypDist k x z ≤ hypDist k x y + hypDist k y z) ∧
    (∀ y z : ℝ × E, OnHyp k y → OnHyp k z →
      ∃ m, OnHyp k m ∧ hypDist k m y = hypDist k y z / 2 ∧ hypDist k m z = hypDist k y z / 2) ∧
    (∀ x y z m : ℝ × E, OnHyp k x → OnHyp k y → OnHyp k z → OnHyp k m →
      hypDist k m y = hypDist k y z / 2 → hypDist k m z = hypDist k y z / 2 →
        hypDist k m x ^ 2 ≤ hypDist k y x ^ 2 / 2 + hypDist k z x ^ 2 / 2 - hypDist k y z ^ 2 / 4) ∧
    (∀ p v : ℝ × E, OnHyp k p → minkB p v = 0 → OnHyp k (hypExp k p v)) ∧
    (∀ p x : ℝ × E, OnHyp k p → OnHyp k x →
      minkB p (hypLog k p x) = 0 ∧ tanNorm (hypLog k p x) = hypDist k p x ∧ hypExp k p (hypLog k p x) = x) ∧
    (∀ p x : ℝ × E, OnHyp k p → OnHyp k x →
      hypExp k p ((0 : ℝ) • hypLog k p x) = p ∧ hypExp k p ((1 : ℝ) • hypLog k p x) = x ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          hypDist k (hypExp k p (s • hypLog k p x)) (hypExp k p (t • hypLog k p x)) = |s - t| * hypDist k p x) ∧
    ∀ p x y : ℝ × E, OnHyp k p → OnHyp k x → OnHyp k y →
      Tendsto (fun s : ℝ => hypDist k (hypExp k p (s • hypLog k p x)) (hypExp k p (s • hypLog k p y)) / s)
        (𝓝[>] 0) (𝓝 (tanNorm (hypLog k p x - hypLog k p y)))

/-! ### T `eq:hadamard-lower` on CAT(0) spaces -/

/-- T `eq:hadamard-lower`, GENERALISED from Hadamard manifolds to CAT(0) spaces: if `M` is CAT(0), `γ_x` are
constant-speed geodesics from `p` and `Log : M → E` has the first-order property
`d(γ_x(s), γ_y(s))/s → ‖Log x − Log y‖` (`s ↓ 0`), then `d(x, y) ≥ ‖Log x − Log y‖` for all `x, y`, with no
restriction on the radius. -/
def hadamard_lower_cat0 : Prop :=
  ∀ (M : Type) [MetricSpace M] (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (p : M) (Log : M → E)
    (γ : M → ℝ → M),
    IsCAT0 M → (∀ x, IsGeodFrom p x (γ x)) →
    (∀ x y, Tendsto (fun s : ℝ => dist (γ x s) (γ y s) / s) (𝓝[>] 0) (𝓝 ‖Log x - Log y‖)) →
      ∀ x y, ‖Log x - Log y‖ ≤ dist x y

/-- T `prop:hadamard-distortion`, cost and transport form on a CAT(0) target: curves `x ∈ X` (`crv x : T → M`), a base
curve `m` with a first-order logarithm `Log_t` at every `m(t)`; `c_geo(x, y) = ∫ d(x(t), y(t))² dλ` and
`c_m^{H₀}(x, y) = ∫ ‖Log_t x(t) − Log_t y(t)‖² dλ` (in `[0, ∞]`). Then `c_geo ≥ c_m^{H₀}` and
`OT_{c_geo}(P, P') ≥ OT_{c_m^{H₀}}(P, P')` for all laws `P, P'` of curves. -/
def hadamard_cost_cat0 : Prop :=
  ∀ (M : Type) [MetricSpace M] (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (T X : Type)
    [MeasurableSpace T] [MeasurableSpace X] (lam : Measure T) (m : T → M) (Log : T → M → E) (γ : T → M → ℝ → M)
    (crv : X → T → M),
    IsCAT0 M → (∀ t x, IsGeodFrom (m t) x (γ t x)) →
    (∀ t x y, Tendsto (fun s : ℝ => dist (γ t x s) (γ t y s) / s) (𝓝[>] 0) (𝓝 ‖Log t x - Log t y‖)) →
      let cgeo : X → X → ℝ≥0∞ := fun x y => ∫⁻ t, ENNReal.ofReal (dist (crv x t) (crv y t) ^ 2) ∂lam
      let cm : X → X → ℝ≥0∞ := fun x y => ∫⁻ t, ENNReal.ofReal (‖Log t (crv x t) - Log t (crv y t)‖ ^ 2) ∂lam
      (∀ x y, cm x y ≤ cgeo x y) ∧ ∀ P P' : Measure X, otCost cm P P' ≤ otCost cgeo P P'

/-! ### G `prop:quantile` (b) on Hadamard targets -/

/-- Fréchet means on a complete CAT(0) space (G `ex:geometries` (ii), Sturm): every law with a finite second moment has
exactly one Fréchet mean. -/
def frechet_cat0 : Prop :=
  ∀ (M : Type) [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [CompleteSpace M] (ν : Measure M) (o : M),
    IsCAT0 M → IsProbabilityMeasure ν → ∫⁻ x, edist o x ^ 2 ∂ν < ∞ → ∃ q, frechetSet ν = {q}

/-- G `prop:quantile` (b) on a Hadamard target (complete CAT(0); "any `ρ` on Hadamard `M`"): if every conditional law
`κ v t` of `X(t)` given the reference field `v` is carried by `B̄(o_t, ρ)` (`o_t` not necessarily measurable in `t`),
then for EVERY `v` and EVERY `t` (no exceptional null set) the minimiser of `eq:quantile-pointwise` exists, is unique
and lies in `B̄(o_t, ρ)`; and for every `t` at which `v ↦ κ v t` is continuous in total variation, `v ↦ q_v(t)` is
continuous. -/
def quantile_hadamard : Prop :=
  ∀ (M : Type) [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [CompleteSpace M] (V T : Type)
    [TopologicalSpace V] (κ : V → T → Measure M) (o : T → M) (ρ : ℝ),
    IsCAT0 M → (∀ v t, IsProbabilityMeasure (κ v t)) → (∀ v t, κ v t (Metric.closedBall (o t) ρ)ᶜ = 0) →
      (∀ v t, ∃ q, frechetSet (κ v t) = {q} ∧ q ∈ Metric.closedBall (o t) ρ) ∧
      ∀ t, (∀ v, Tendsto (fun v' => tvDist (κ v' t) (κ v t)) (𝓝 v) (𝓝 0)) →
        ∀ q : V → M, (∀ v, q v ∈ frechetSet (κ v t)) → Continuous q

/-- The stability behind the continuity in `quantile_hadamard`: on a CAT(0) space, Fréchet means of two laws carried by
`B̄(o, R)` satisfy `d(q, q') ≤ 4R · TV(μ, ν)`. -/
def quantile_cat0_stable : Prop :=
  ∀ (M : Type) [MetricSpace M] [MeasurableSpace M] [BorelSpace M] (μ ν : Measure M) (o : M) (R : ℝ),
    IsCAT0 M → IsProbabilityMeasure μ → IsProbabilityMeasure ν → μ (Metric.closedBall o R)ᶜ = 0 →
      ν (Metric.closedBall o R)ᶜ = 0 → ∀ q q', q ∈ frechetSet μ → q' ∈ frechetSet ν →
        dist q q' ≤ 4 * R * tvDist μ ν

/-! ### G `lem:jacobicosh` (consequence) and T `prop:Cb` on `H_k` -/

/-- G `lem:jacobicosh`, consequence, on the hyperbolic space `H_k` (curvature `−k²`, so in `[−κ², 0]` with `κ = k`):
for `p, q ∈ H_k` and `ξ ∈ T_pH_k`, the parallel transport `Γ = Γ_{p→q}` maps `T_pH_k` isometrically to `T_qH_k`,
fixes the vectors `B`-orthogonal to `p` and `q`, sends the initial velocity `Log_p q` of the geodesic to its final
velocity `−Log_q p`, and `d(Exp_q(Γξ), Exp_p ξ) ≤ cosh(k|ξ|) d(p, q)`. -/
def jacobicosh_transport_hyp : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (k : ℝ) (p q ξ : ℝ × E),
    0 < k → OnHyp k p → OnHyp k q → minkB p ξ = 0 →
      minkB q (hypTransport k p q ξ) = 0 ∧ tanNorm (hypTransport k p q ξ) = tanNorm ξ ∧
      (minkB q ξ = 0 → hypTransport k p q ξ = ξ) ∧ hypTransport k p q (hypLog k p q) = -hypLog k q p ∧
      hypDist k (hypExp k q (hypTransport k p q ξ)) (hypExp k p ξ) ≤ Real.cosh (k * tanNorm ξ) * hypDist k p q

/-- G `lem:jacobicosh`, sharpness: "the factor `cosh(κ|ξ|)` cannot be replaced by a smaller one on the hyperbolic
space" — moving the base point to `q_r = Exp_p(r u)` along a unit direction `u ⊥ ξ`,
`d(Exp_{q_r}(Γξ), Exp_p ξ)/d(p, q_r) → cosh(k|ξ|)` as `r ↓ 0`. -/
def jacobicosh_sharp_hyp : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (k : ℝ) (p ξ u : ℝ × E),
    0 < k → OnHyp k p → minkB p ξ = 0 → minkB p u = 0 → minkB u u = 1 → minkB u ξ = 0 →
      Tendsto (fun r : ℝ => hypDist k (hypExp k (hypExp k p (r • u)) (hypTransport k p (hypExp k p (r • u)) ξ))
          (hypExp k p ξ) / hypDist k p (hypExp k p (r • u))) (𝓝[>] 0) (𝓝 (Real.cosh (k * tanNorm ξ)))

/-! ### T `eq:basebridge` on the model spaces -/

/-- T `eq:basebridge` on `H_k` with the constants of `prop:Cb`, `C_b = cosh(kb)` and `L_b = sinh(kb)/(kb)`: for base
curves `m, m̂` in `H_k`, `J_t` the parallel transport from `m(t)` to `m̂(t)` and tangent fields `v, v̂` bounded by
`b > 0`, pointwise `d(Exp_{m̂(t)} v̂(t), Exp_{m(t)} v(t)) ≤ cosh(kb) d(m̂(t), m(t)) + (sinh(kb)/(kb)) |v̂(t) − J_t v(t)|`,
hence the `D_∞` form (suprema in `[0, ∞]`). -/
def basebridge_hyp : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (T : Type) (k b : ℝ) (m mh v vh : T → ℝ × E),
    0 < k → 0 < b → (∀ t, OnHyp k (m t)) → (∀ t, OnHyp k (mh t)) → (∀ t, minkB (m t) (v t) = 0) →
    (∀ t, minkB (mh t) (vh t) = 0) → (∀ t, tanNorm (v t) ≤ b) → (∀ t, tanNorm (vh t) ≤ b) →
      (∀ t, hypDist k (hypExp k (mh t) (vh t)) (hypExp k (m t) (v t)) ≤
        Real.cosh (k * b) * hypDist k (mh t) (m t) +
          Real.sinh (k * b) / (k * b) * tanNorm (vh t - hypTransport k (m t) (mh t) (v t))) ∧
      (⨆ t, ENNReal.ofReal (hypDist k (hypExp k (mh t) (vh t)) (hypExp k (m t) (v t)))) ≤
        ENNReal.ofReal (Real.cosh (k * b)) * (⨆ t, ENNReal.ofReal (hypDist k (mh t) (m t))) +
          ENNReal.ofReal (Real.sinh (k * b) / (k * b)) *
            ⨆ t, ENNReal.ofReal (tanNorm (vh t - hypTransport k (m t) (mh t) (v t)))

/-- T `eq:basebridge` on the unit sphere `S^d` with `C_b = L_b = 1` (`prop:Cb` (i), `prop:sphere`), for every `b`: for
base curves with `m(t) ≠ −m̂(t)`, `J_t` the parallel transport (frozen `sphTransport`) and tangent fields `v, v̂`,
`d(Exp_{m̂(t)} v̂(t), Exp_{m(t)} v(t)) ≤ d(m̂(t), m(t)) + ‖v̂(t) − J_t v(t)‖`, hence the `D_∞` form. -/
def basebridge_sphere : Prop :=
  ∀ (d : ℕ) (T : Type) (m mh v vh : T → EuclideanSpace ℝ (Fin (d + 1))),
    (∀ t, ‖m t‖ = 1) → (∀ t, ‖mh t‖ = 1) → (∀ t, -1 < ⟪m t, mh t⟫_ℝ) → (∀ t, ⟪m t, v t⟫_ℝ = 0) →
    (∀ t, ⟪mh t, vh t⟫_ℝ = 0) →
      (∀ t, sphDist (sphExp (mh t) (vh t)) (sphExp (m t) (v t)) ≤
        sphDist (mh t) (m t) + ‖vh t - sphTransport (m t) (mh t) (v t)‖) ∧
      (⨆ t, ENNReal.ofReal (sphDist (sphExp (mh t) (vh t)) (sphExp (m t) (v t)))) ≤
        (⨆ t, ENNReal.ofReal (sphDist (mh t) (m t))) + ⨆ t, ENNReal.ofReal ‖vh t - sphTransport (m t) (mh t) (v t)‖

/-! ### T `thm:pop-sieve`, the `H₀` reconstruction clause on the sphere -/

/-- T `thm:pop-sieve`, last sentence, on the unit sphere `S^d` ("the exponential differential is globally bounded":
`prop:sphere`): under the hypotheses of the frozen `integrated_quantile_uncond` (`eq:popQ`), for a field space `H`
whose fields `ev h` are tangent along a base curve `m` and whose norm dominates the `H₀ = L²(λ)` norm
(`∫ ‖ev h(t) − ev h'(t)‖² dλ ≤ ‖h − h'‖²`, equality for `H₀`), the exponential reconstructions converge in mean
squared `D₂`: `∫ D₂(E_m(ι_K Q_K Π_K u), E_m(Q u))² μ(du) → 0`, with no pointwise bound on the output fields. -/
def pop_sieve_sphere : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (P μ : ProbabilityMeasure H) (Q : H → H) (M : ℝ) (QK : (K : ℕ) → Euc K → Euc K)
    (d : ℕ) (T : Type) [MeasurableSpace T] (lam : Measure T) (m : T → EuclideanSpace ℝ (Fin (d + 1)))
    (ev : H → T → EuclideanSpace ℝ (Fin (d + 1))),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    PellClass (P : Measure H) → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
    Measurable Q → (μ : Measure H).map Q = P → IsCMMapAE (μ : Measure H) Q →
    (∀ K, Measurable (QK K)) →
    (∀ K, ((μ : Measure H).map (truncK e K)).map (QK K) = (P : Measure H).map (truncK e K)) →
    (∀ K, IsCMMapAE ((μ : Measure H).map (truncK e K)) (QK K)) →
    (∀ t, ‖m t‖ = 1) → (∀ h t, ⟪m t, ev h t⟫_ℝ = 0) →
    (∀ h h', ∫⁻ t, ‖ev h t - ev h' t‖ₑ ^ 2 ∂lam ≤ ‖h - h'‖ₑ ^ 2) →
      Tendsto (fun K => ∫⁻ u, ∫⁻ t, ENNReal.ofReal (sphDist (sphExp (m t) (ev (embed e K (QK K (truncK e K u))) t))
          (sphExp (m t) (ev (Q u) t)) ^ 2) ∂lam ∂(μ : Measure H)) atTop (𝓝 0)

/-! ### G `prop:reference` (d) and `prop:equivariance` on the model spaces -/

/-- G `prop:reference` (d) on the unit sphere, pathwise: let `A` be a linear isometry of `ℝ^{d+1}` (an isometry
`φ = A|_{S^d}` of the sphere, `dφ = A`), `J` a linear isometry of the field space `H` acting as `dφ` on fields
(`ev(J h)(t) = A ev(h)(t)`, so a Gaussian `G` with covariance `Σ` becomes `J G` with covariance `JΣJ*`). Then the
Gaussian-direction reference point of `J G` is `J V` (`V = τ G/‖G‖`), and the reference process built at `φ ∘ m` from
it is `φ` applied to the original one, realisation by realisation; in particular `R_s` is replaced by `φ#R_s`.
The cost is invariant: `c'_s(dφ v, φ ∘ x) = c_s(v, x)`. -/
def reference_equivariance_sphere : Prop :=
  ∀ (d : ℕ) (Ω H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : EuclideanSpace ℝ (Fin (d + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (d + 1))) (J : H ≃ₗᵢ[ℝ] H)
    (ev : H → ℝ → EuclideanSpace ℝ (Fin (d + 1))) (G : Ω → H) (τ : Ω → ℝ) (m : ℝ → EuclideanSpace ℝ (Fin (d + 1)))
    (s : ℝ),
    (∀ h t, ev (J h) t = A (ev h t)) →
      (∀ ω, refV (fun ω => J (G ω)) τ ω = J (refV G τ ω)) ∧
      (∀ ω, refCurve (fun t => A (m t)) (ev (refV (fun ω => J (G ω)) τ ω)) s =
        fun t => A (refCurve m (ev (refV G τ ω)) s t)) ∧
      ∀ (lam : Measure ℝ) (v x : ℝ → EuclideanSpace ℝ (Fin (d + 1))),
        sphCost lam (refCurve (fun t => A (m t)) (fun t => A (v t)) s) (fun t => A (x t)) =
          sphCost lam (refCurve m v s) x

/-- G `prop:equivariance`, the plan, on the unit sphere: the cost-invariance PREMISE of the frozen
`equivariance_plan` DISCHARGED for the geodesic cost `c_s(v, x) = ½ D(E_m(s v), x)²`: if a linear isometry `A`
acts on the reference fields through a measurable bijection `Φ` (`ev'(Φ v) = A ∘ ev v`) and on the curves through a
measurable bijection `ψ` (`crv'(ψ x) = A ∘ crv x`), the entropic plans of the transformed problem (base curve
`A ∘ m`) are exactly the pushforwards `(Φ × ψ)#π` of the original ones, and `π'_ε = (Φ × ψ)#π_ε` when `π_ε` is
unique (the frozen conclusion verbatim). -/
def equivariance_plan_sphere : Prop :=
  ∀ (d : ℕ) (V V' X X' : Type) [MeasurableSpace V] [MeasurableSpace V'] [MeasurableSpace X] [MeasurableSpace X']
    (Φ : V ≃ᵐ V') (ψ : X ≃ᵐ X') (A : EuclideanSpace ℝ (Fin (d + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
    (lam : Measure ℝ) (m : ℝ → EuclideanSpace ℝ (Fin (d + 1))) (ev : V → ℝ → EuclideanSpace ℝ (Fin (d + 1)))
    (ev' : V' → ℝ → EuclideanSpace ℝ (Fin (d + 1))) (crv : X → ℝ → EuclideanSpace ℝ (Fin (d + 1)))
    (crv' : X' → ℝ → EuclideanSpace ℝ (Fin (d + 1))) (s ε : ℝ) (μ : Measure V) (P : Measure X),
    IsProbabilityMeasure μ → IsProbabilityMeasure P → (∀ v t, ev' (Φ v) t = A (ev v t)) →
    (∀ x t, crv' (ψ x) t = A (crv x t)) →
      let c : V × X → ℝ≥0∞ := fun z => ENNReal.ofReal (sphCost lam (refCurve m (ev z.1) s) (crv z.2))
      let c' : V' × X' → ℝ≥0∞ := fun z =>
        ENNReal.ofReal (sphCost lam (refCurve (fun t => A (m t)) (ev' z.1) s) (crv' z.2))
      {π' | IsEntPlanG c' ε (μ.map Φ) (P.map ψ) π'} =
          (fun π => π.map (Prod.map Φ ψ)) '' {π | IsEntPlanG c ε μ P π} ∧
        ∀ π, IsEntPlanG c ε μ P π → (∀ ρ, IsEntPlanG c ε μ P ρ → ρ = π) →
          ∀ π', IsEntPlanG c' ε (μ.map Φ) (P.map ψ) π' → π' = π.map (Prod.map Φ ψ)

/-- G `prop:equivariance` on `H_k`: a linear map `L` of `ℝ × E` preserving the Minkowski form (a Lorentz
transformation; those preserving the upper sheet are the isometries of `H_k`) commutes with `Exp`, `Log` and parallel
transport and preserves the distance; hence the geodesic cost `c(v, x) = ½ ∫ d(Exp_{m(t)}(s v(t)), x(t))² dλ`
(in `[0, ∞]`) is invariant: `c'(dφ v, φ ∘ x) = c(v, x)` with `dφ = L`. -/
def equivariance_hyp : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (k : ℝ) (L : (ℝ × E) →ₗ[ℝ] (ℝ × E)),
    (∀ x y, minkB (L x) (L y) = minkB x y) →
      (∀ x y, hypDist k (L x) (L y) = hypDist k x y) ∧ (∀ p v, hypExp k (L p) (L v) = L (hypExp k p v)) ∧
      (∀ p x, hypLog k (L p) (L x) = L (hypLog k p x)) ∧
      (∀ p q ξ, hypTransport k (L p) (L q) (L ξ) = L (hypTransport k p q ξ)) ∧
      ∀ (lam : Measure ℝ) (m v x : ℝ → ℝ × E) (s : ℝ),
        ∫⁻ t, ENNReal.ofReal (hypDist k (hypExp k (L (m t)) (s • L (v t))) (L (x t)) ^ 2 / 2) ∂lam =
          ∫⁻ t, ENNReal.ofReal (hypDist k (hypExp k (m t) (s • v t)) (x t) ^ 2 / 2) ∂lam

/-- G `prop:equivariance`, the plan, on `H_k`: the cost-invariance premise of the frozen `equivariance_plan`
DISCHARGED for the geodesic cost of `H_k` under a Lorentz transformation `L` acting on fields and curves through
measurable bijections `Φ`, `ψ`; the frozen conclusion verbatim. -/
def equivariance_plan_hyp : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (V V' X X' : Type) [MeasurableSpace V]
    [MeasurableSpace V'] [MeasurableSpace X] [MeasurableSpace X'] (Φ : V ≃ᵐ V') (ψ : X ≃ᵐ X') (k : ℝ)
    (L : (ℝ × E) →ₗ[ℝ] (ℝ × E)) (lam : Measure ℝ) (m : ℝ → ℝ × E) (ev : V → ℝ → ℝ × E) (ev' : V' → ℝ → ℝ × E)
    (crv : X → ℝ → ℝ × E) (crv' : X' → ℝ → ℝ × E) (s ε : ℝ) (μ : Measure V) (P : Measure X),
    IsProbabilityMeasure μ → IsProbabilityMeasure P → (∀ x y, minkB (L x) (L y) = minkB x y) →
    (∀ v t, ev' (Φ v) t = L (ev v t)) → (∀ x t, crv' (ψ x) t = L (crv x t)) →
      let c : V × X → ℝ≥0∞ := fun z =>
        ∫⁻ t, ENNReal.ofReal (hypDist k (hypExp k (m t) (s • ev z.1 t)) (crv z.2 t) ^ 2 / 2) ∂lam
      let c' : V' × X' → ℝ≥0∞ := fun z =>
        ∫⁻ t, ENNReal.ofReal (hypDist k (hypExp k (L (m t)) (s • ev' z.1 t)) (crv' z.2 t) ^ 2 / 2) ∂lam
      {π' | IsEntPlanG c' ε (μ.map Φ) (P.map ψ) π'} =
          (fun π => π.map (Prod.map Φ ψ)) '' {π | IsEntPlanG c ε μ P π} ∧
        ∀ π, IsEntPlanG c ε μ P π → (∀ ρ, IsEntPlanG c ε μ P ρ → ρ = π) →
          ∀ π', IsEntPlanG c' ε (μ.map Φ) (P.map ψ) π' → π' = π.map (Prod.map Φ ψ)

/-! ### G `cor:discretisation` (c), Hadamard case, on `H_k` -/

/-- G `cor:discretisation` (c), the cost bound on the hyperbolic space `H_k` of curvature `−k²` ("on a Hadamard
manifold with curvature bounded below by `−κ²` the same holds with `D(m, m̂)` multiplied by
`cosh(κ s esssup_t|v(t)|)`"): for a reference field `v` tangent along `m` with `|v(t)| ≤ b` and `‖v‖_{H_m} ≤ 1`,
`s ≥ 0`, and a data curve `x` with `D(m, x) ≤ B`, writing `C = cosh(k s b)`,
`|c_{s,m̂}(Γv, x) − c_{s,m}(v, x)| ≤ (s + B + C D(m, m̂)) C D(m, m̂)`. The squared distances `d(m, x)²`, `d(m, m̂)²` are
assumed integrable (so `D` is not a junk value; on `H_k` they need not be bounded). -/
def disc_base_cost_hyp : Prop :=
  ∀ (d : ℕ) (lam : Measure ℝ) [IsProbabilityMeasure lam] (k s b B : ℝ) (m mh v x : ℝ → ℝ × Euc d),
    0 < k → Measurable m → Measurable mh → Measurable v → Measurable x →
    (∀ t, OnHyp k (m t)) → (∀ t, OnHyp k (mh t)) → (∀ t, OnHyp k (x t)) → (∀ t, minkB (m t) (v t) = 0) →
    (∀ t, tanNorm (v t) ≤ b) → ∫ t, tanNorm (v t) ^ 2 ∂lam ≤ 1 → 0 ≤ s →
    Integrable (fun t => hypDist k (m t) (x t) ^ 2) lam → hypD k lam m x ≤ B →
    Integrable (fun t => hypDist k (m t) (mh t) ^ 2) lam →
      |hypCost k lam (hypRefHat k m mh v s) x - hypCost k lam (hypRef k m v s) x| ≤
        (s + B + Real.cosh (k * s * b) * hypD k lam m mh) * (Real.cosh (k * s * b) * hypD k lam m mh)

/-- G `cor:discretisation` (c), the rank bound on `H_k`: `∫ ‖Γ^{-1}F_{m̂} − F_m‖ dP ≤ (s + B + C D(m, m̂)) C D(m, m̂)/ε`,
`C = cosh(k s b)`. The reference fields form a Hilbert space `H_m` (`Hs`, e.g. the span `S` of a rank-`K` reference)
with evaluation `ev` tangent along `m`, `∫ |ev v(t)|² dλ ≤ ‖v‖²` and the pointwise constant of `prop:cap` (a),
`|ev v(t)| ≤ b ‖v‖`; `μ`-a.s. `‖v‖ ≤ 1`; data curves with `D(m, X x) ≤ B` (`ass:bounded`) and integrable squared
distances. Identifying `H_{m̂}` with `H_m` by `Γ`, `Γ^{-1}F_{m̂}` is the rank map (`gibbsMean`, `ψ = id`) of the
entropic plan for the cost `c_{s,m̂}(Γv, x)`. The costs are unbounded off `{‖v‖ ≤ 1}` (as on any Hadamard target);
the plans and rank maps only see them `μ ⊗ P`-a.e. -/
def disc_base_rank_hyp : Prop :=
  ∀ (d : ℕ) (Hs 𝒳 : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℝ Hs] [CompleteSpace Hs] [MeasurableSpace Hs]
    [BorelSpace Hs] [SecondCountableTopology Hs] [MeasurableSpace 𝒳]
    (μ : Measure Hs) (P : Measure 𝒳) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (lam : Measure ℝ) [IsProbabilityMeasure lam] (k s b B ε : ℝ) (m mh : ℝ → ℝ × Euc d)
    (ev : Hs → ℝ → ℝ × Euc d) (X : 𝒳 → ℝ → ℝ × Euc d) (f f' : Hs → ℝ) (g g' : 𝒳 → ℝ),
    0 < k → 0 ≤ b → Measurable m → Measurable mh → (∀ t, OnHyp k (m t)) → (∀ t, OnHyp k (mh t)) →
    Integrable (fun t => hypDist k (m t) (mh t) ^ 2) lam →
    (∀ v, Measurable (ev v)) → (∀ v t, minkB (m t) (ev v t) = 0) → (∀ v t, tanNorm (ev v t) ≤ b * ‖v‖) →
    (∀ v, ∫ t, tanNorm (ev v t) ^ 2 ∂lam ≤ ‖v‖ ^ 2) →
    (∀ x, Measurable (X x)) → (∀ x t, OnHyp k (X x t)) →
    (∀ x, Integrable (fun t => hypDist k (m t) (X x t) ^ 2) lam) → (∀ x, hypD k lam m (X x) ≤ B) →
    0 ≤ s → 0 < ε → (∀ᵐ v ∂μ, ‖v‖ ≤ 1) →
    Measurable (fun z : Hs × 𝒳 => hypCost k lam (hypRef k m (ev z.1) s) (X z.2)) →
    Measurable (fun z : Hs × 𝒳 => hypCost k lam (hypRefHat k m mh (ev z.1) s) (X z.2)) →
    GibbsHyp μ P ε (fun z => hypCost k lam (hypRef k m (ev z.1) s) (X z.2)) f g →
    GibbsHyp μ P ε (fun z => hypCost k lam (hypRefHat k m mh (ev z.1) s) (X z.2)) f' g' →
      ∫⁻ x, ‖gibbsMean μ ε (fun z => hypCost k lam (hypRefHat k m mh (ev z.1) s) (X z.2)) f' g' id x -
          gibbsMean μ ε (fun z => hypCost k lam (hypRef k m (ev z.1) s) (X z.2)) f g id x‖ₑ ∂P ≤
        ENNReal.ofReal ((s + B + Real.cosh (k * s * b) * hypD k lam m mh) *
          (Real.cosh (k * s * b) * hypD k lam m mh) / ε)

/-! ### T `thm:population`, `prop:transfer-M`: the rank-pair premises discharged -/

/-- T `thm:population`, manifold form, with the rank-pair PREMISE of the frozen `pop_manifold` DISCHARGED: under
`ass:model` in the chart (`X ∈ 𝒳_r = E_m(𝒟_r)` a.s., `L_m` the Borel inverse of `E_m` on `𝒟_r`), with `ν = L_m#P` and
the reference `μ` boundedly supported and null on Lipschitz hypersurfaces, quadratic transport supplies Borel maps
`F_ν`, `Q_ν` — a rank pair, each `a.e.` the subgradient of a convex potential — and `F^m = F_ν L_m`, `Q^m = E_m Q_ν`
satisfy `eq:manifoldinverse` (the frozen conclusion verbatim). -/
def pop_manifold_mccann : Prop :=
  ∀ (H X : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (μ : Measure H) [IsProbabilityMeasure μ]
    (Em : H → X) (Lm : X → H) (Dr : Set H),
    Measurable Em → Measurable Lm → MeasurableSet Dr → (∀ v ∈ Dr, Lm (Em v) = v) →
    (∀ᵐ x ∂P, Lm x ∈ Dr ∧ Em (Lm x) = x) →
      (∀ [CompleteSpace H] [SecondCountableTopology H] [BorelSpace H] (B Bμ : ℝ),
        LipNull (P.map Lm) → LipNull μ → (∀ᵐ v ∂(P.map Lm), ‖v‖ ≤ B) → (∀ᵐ u ∂μ, ‖u‖ ≤ Bμ) →
          ∃ F Q : H → H, IsRankPair μ (P.map Lm) F Q ∧ IsGradMap (P.map Lm) μ F ∧ IsGradMap μ (P.map Lm) Q) ∧
      ∀ F Q : H → H, IsRankPair μ (P.map Lm) F Q →
        P.map (F ∘ Lm) = μ ∧ μ.map (Em ∘ Q) = P ∧ (∀ᵐ x ∂P, Em (Q (F (Lm x))) = x) ∧
          ∀ᵐ u ∂μ, F (Lm (Em (Q u))) = u

/-- T `prop:transfer-M` (i) with the rank-pair PREMISES of the frozen `transferM_push` DISCHARGED: for fixed charts
`Φ_g` with Borel inverses `Ψ_g` (`Φ_g Ψ_g = Id` `P^K_g`-a.e.), coefficient laws `ν_{g,K} = Ψ_g#P^K_g` absolutely
continuous with bounded support (`ass:model`, as printed) and a reference `μ_K` null on Lipschitz hypersurfaces with
bounded support, rank pairs `(F_g, Q_g)` of `(μ_K, ν_{g,K})` (McCann maps) exist, and for every such choice the
frozen conclusion holds: `T_{A→B}#P^K_A = P^K_B`, and depth and sign are preserved `P^K_A`-a.e. -/
def transferM_push_mccann : Prop :=
  ∀ (K : ℕ) (X : Type) [MeasurableSpace X] (μ : Measure (EuclideanSpace ℝ (Fin K))) (PA PB : Measure X)
    (ΦA ΦB : EuclideanSpace ℝ (Fin K) → X) (ΨA ΨB : X → EuclideanSpace ℝ (Fin K)),
    Measurable ΦA → Measurable ΦB → Measurable ΨA → Measurable ΨB →
    (∀ᵐ x ∂PA, ΦA (ΨA x) = x) → (∀ᵐ x ∂PB, ΦB (ΨB x) = x) →
      (∀ B Bμ : ℝ, IsProbabilityMeasure μ → IsProbabilityMeasure PA → IsProbabilityMeasure PB → LipNull μ → (∀ᵐ u ∂μ, ‖u‖ ≤ Bμ) → PA.map ΨA ≪ volume → PB.map ΨB ≪ volume →
        (∀ᵐ z ∂(PA.map ΨA), ‖z‖ ≤ B) → (∀ᵐ z ∂(PB.map ΨB), ‖z‖ ≤ B) →
      ∃ FA QA FB QB : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K),
        IsRankPair μ (PA.map ΨA) FA QA ∧ IsRankPair μ (PB.map ΨB) FB QB) ∧
      ∀ FA QA FB QB : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K),
        IsRankPair μ (PA.map ΨA) FA QA → IsRankPair μ (PB.map ΨB) FB QB →
          PA.map (fun x => ΦB (QB (FA (ΨA x)))) = PB ∧
            ∀ᵐ x ∂PA, FB (ΨB (ΦB (QB (FA (ΨA x))))) = FA (ΨA x) ∧
              cK μ ‖FB (ΨB (ΦB (QB (FA (ΨA x)))))‖ = cK μ ‖FA (ΨA x)‖ ∧
              sgnK (FB (ΨB (ΦB (QB (FA (ΨA x)))))) = sgnK (FA (ΨA x))

/-- T `prop:transfer-M` (ii) with the rank-pair premises discharged as in `transferM_push_mccann`: rank pairs exist,
and for every choice `T_{A→B}` is the `P^K_A`-a.e. unique Borel map pushing `P^K_A` to `P^K_B` that preserves depth
and sign (frozen `transferM_unique` conclusion). -/
def transferM_unique_mccann : Prop :=
  ∀ (K : ℕ) (X : Type) [MeasurableSpace X] (μ : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure μ]
    (PA PB : Measure X) [IsProbabilityMeasure PA]
    (ΦA ΦB : EuclideanSpace ℝ (Fin K) → X) (ΨA ΨB : X → EuclideanSpace ℝ (Fin K)),
    Measurable ΦA → Measurable ΦB → Measurable ΨA → Measurable ΨB →
    (∀ᵐ x ∂PA, ΦA (ΨA x) = x) → (∀ᵐ x ∂PB, ΦB (ΨB x) = x) →
      (∀ B Bμ : ℝ, IsProbabilityMeasure PB → LipNull μ → (∀ᵐ u ∂μ, ‖u‖ ≤ Bμ) → PA.map ΨA ≪ volume → PB.map ΨB ≪ volume →
        (∀ᵐ z ∂(PA.map ΨA), ‖z‖ ≤ B) → (∀ᵐ z ∂(PB.map ΨB), ‖z‖ ≤ B) →
      ∃ FA QA FB QB : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K),
        IsRankPair μ (PA.map ΨA) FA QA ∧ IsRankPair μ (PB.map ΨB) FB QB) ∧
      ∀ (FA QA FB QB : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (T' : X → X),
        IsRankPair μ (PA.map ΨA) FA QA → IsRankPair μ (PB.map ΨB) FB QB →
        Measurable T' → PA.map T' = PB →
        (∀ᵐ x ∂PA, cK μ ‖FB (ΨB (T' x))‖ = cK μ ‖FA (ΨA x)‖) →
        (∀ᵐ x ∂PA, sgnK (FB (ΨB (T' x))) = sgnK (FA (ΨA x))) →
          ∀ᵐ x ∂PA, T' x = ΦB (QB (FA (ΨA x)))

/-- T `prop:transfer-M` (iii), cocycle, with the rank-pair premises discharged for three laws (frozen
`transferM_cocycle` conclusion). -/
def transferM_cocycle_mccann : Prop :=
  ∀ (K : ℕ) (X : Type) [MeasurableSpace X] (μ : Measure (EuclideanSpace ℝ (Fin K))) (PA PB PC : Measure X)
    (ΦA ΦB ΦC : EuclideanSpace ℝ (Fin K) → X) (ΨA ΨB ΨC : X → EuclideanSpace ℝ (Fin K)),
    Measurable ΦA → Measurable ΦB → Measurable ΦC → Measurable ΨA → Measurable ΨB → Measurable ΨC →
    (∀ᵐ x ∂PA, ΦA (ΨA x) = x) → (∀ᵐ x ∂PB, ΦB (ΨB x) = x) → (∀ᵐ x ∂PC, ΦC (ΨC x) = x) →
      (∀ B Bμ : ℝ, IsProbabilityMeasure μ → IsProbabilityMeasure PA → IsProbabilityMeasure PB →
        IsProbabilityMeasure PC → LipNull μ → (∀ᵐ u ∂μ, ‖u‖ ≤ Bμ) → PA.map ΨA ≪ volume → PB.map ΨB ≪ volume →
        PC.map ΨC ≪ volume → (∀ᵐ z ∂(PA.map ΨA), ‖z‖ ≤ B) → (∀ᵐ z ∂(PB.map ΨB), ‖z‖ ≤ B) →
        (∀ᵐ z ∂(PC.map ΨC), ‖z‖ ≤ B) →
      ∃ FA QA FB QB FC QC : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K),
        IsRankPair μ (PA.map ΨA) FA QA ∧ IsRankPair μ (PB.map ΨB) FB QB ∧ IsRankPair μ (PC.map ΨC) FC QC) ∧
      ∀ FA QA FB QB FC QC : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K),
        IsRankPair μ (PA.map ΨA) FA QA → IsRankPair μ (PB.map ΨB) FB QB → IsRankPair μ (PC.map ΨC) FC QC →
          (∀ᵐ x ∂PA, ΦA (QA (FA (ΨA x))) = x) ∧
            ∀ᵐ x ∂PA, ΦC (QC (FB (ΨB (ΦB (QB (FA (ΨA x))))))) = ΦC (QC (FA (ΨA x)))

/-! ### G `prop:reference` (c) on the model spaces -/

/-- G `prop:reference` (c), geometric step, on the unit sphere: `D(m, E_m(s v)) ≤ s ‖v‖_{H_m}` (`d_S(p, Exp_p w) ≤ |w|`),
so a reference field with `‖v‖ ≤ 1` gives `D(m, Y) ≤ s` — the hypothesis `dist m (E_m(s v)) ≤ s ‖v‖` of the frozen
`reference_calibration`, `firstmoment_cost` holds for the sphere's curve metric. -/
def reference_support_sphere : Prop :=
  ∀ (d : ℕ) (lam : Measure ℝ) [IsProbabilityMeasure lam] (m v : ℝ → EuclideanSpace ℝ (Fin (d + 1))) (s : ℝ),
    Measurable m → Measurable v → (∀ t, ‖m t‖ = 1) → (∀ t, ⟪m t, v t⟫_ℝ = 0) →
    Integrable (fun t => ‖v t‖ ^ 2) lam → 0 ≤ s →
      sphD lam m (refCurve m v s) ≤ s * √(∫ t, ‖v t‖ ^ 2 ∂lam)

/-- G `prop:reference` (c), geometric step, on `H_k`: for tangent fields with `∫ |v(t)|² dλ < ∞`, `d(m, E_m(s v))²` is
integrable (so `D` is genuine) and `D(m, E_m(s v)) = s ‖v‖_{H_m}` exactly (`d(p, Exp_p w) = |w|`, no cut locus). -/
def reference_support_hyp : Prop :=
  ∀ (d : ℕ) (lam : Measure ℝ) (k : ℝ) (m v : ℝ → ℝ × Euc d) (s : ℝ),
    0 < k → (∀ t, OnHyp k (m t)) → (∀ t, minkB (m t) (v t) = 0) → Integrable (fun t => tanNorm (v t) ^ 2) lam →
    0 ≤ s → Integrable (fun t => hypDist k (m t) (hypRef k m v s t) ^ 2) lam ∧
      hypD k lam m (hypRef k m v s) = s * √(∫ t, tanNorm (v t) ^ 2 ∂lam)

/-! ### G `lem:polish` on a curved target -/

/-- G `lem:polish`, GENERALISED from complete Riemannian manifolds to complete separable metric spaces `M` (the paper's
proof uses only this): for any probability `λ` on `T = [0, 1]` and measurable base curve `m`, `D` is a pseudometric on
`𝒳 = {x measurable : D(x, m) < ∞}` that vanishes exactly on `λ`-a.e. equal curves (so `(𝒳/∼_λ, D)` is a metric
space); `𝒳` is complete (every `D`-Cauchy sequence has a `D`-limit in `𝒳`) and separable (a countable `D`-dense
subset); and, given a measurable selection of minimal geodesics of `M` (a geodesic bicombing `σ`, CONDITION: the
paper's "measurably selected minimal geodesic"), every two curves are joined by `θ ↦ x_θ` with
`D(x_θ, x_θ') = |θ − θ'| D(x, x')`. -/
def polish_metric : Prop :=
  ∀ (M : Type) [MetricSpace M] [CompleteSpace M] [TopologicalSpace.SeparableSpace M] [MeasurableSpace M]
    [BorelSpace M] (lam : Measure (Icc (0 : ℝ) 1)) [IsProbabilityMeasure lam] (m : Icc (0 : ℝ) 1 → M), Measurable m →
    (∀ x ∈ curveSet lam m, ∀ y ∈ curveSet lam m, ∀ z ∈ curveSet lam m,
      curveD lam x y < ⊤ ∧ curveD lam x x = 0 ∧ curveD lam x y = curveD lam y x ∧
        curveD lam x z ≤ curveD lam x y + curveD lam y z ∧ (curveD lam x y = 0 ↔ x =ᵐ[lam] y)) ∧
    (∀ x : ℕ → Icc (0 : ℝ) 1 → M, (∀ n, x n ∈ curveSet lam m) →
      (∀ ε > 0, ∃ N, ∀ a ≥ N, ∀ b ≥ N, curveD lam (x a) (x b) < ε) →
        ∃ y ∈ curveSet lam m, Tendsto (fun n => curveD lam (x n) y) atTop (𝓝 0)) ∧
    (∃ S ⊆ curveSet lam m, S.Countable ∧ ∀ x ∈ curveSet lam m, ∀ ε > 0, ∃ s ∈ S, curveD lam x s < ε) ∧
    ∀ σ : M → M → ℝ → M, (∀ θ, Measurable fun p : M × M => σ p.1 p.2 θ) → (∀ p q, σ p q 0 = p ∧ σ p q 1 = q) →
      (∀ p q, ∀ θ ∈ Icc (0 : ℝ) 1, ∀ θ' ∈ Icc (0 : ℝ) 1, dist (σ p q θ) (σ p q θ') = |θ - θ'| * dist p q) →
        ∀ x ∈ curveSet lam m, ∀ x' ∈ curveSet lam m, ∃ γ : ℝ → Icc (0 : ℝ) 1 → M, γ 0 = x ∧ γ 1 = x' ∧
          (∀ θ ∈ Icc (0 : ℝ) 1, γ θ ∈ curveSet lam m) ∧
          ∀ θ ∈ Icc (0 : ℝ) 1, ∀ θ' ∈ Icc (0 : ℝ) 1,
            curveD lam (γ θ) (γ θ') = ENNReal.ofReal |θ - θ'| * curveD lam x x'

/-! ### G `lem:decoupling` on curved targets -/

/-- G `lem:decoupling`, GENERALISED in its first and last clauses from complete Riemannian manifolds to separable
metric spaces, and its existence clause on Hadamard targets (complete CAT(0) spaces): for a law `ν` of curves (labels
`Ω`, jointly measurable evaluation `ev`, `lem:evaluation`) with `∫ D(m, x)² ν(dx) < ∞`,
`J(z) = ∫ D(z, x)² ν(dx) = ∫ Ψ_t(z(t)) dλ` (Tonelli); off a measurable `λ`-null set `Ψ_t` is finite and continuous;
`z ∈ 𝒳` minimises `J` over `𝒳` iff `z(t)` minimises `Ψ_t` for `λ`-a.e. `t`; and on a complete CAT(0) target
`argmin J` is nonempty and its elements agree `λ`-a.e. (with `ν = π_ε(· | v)` this is G `prop:quantile` (a) and the
uniqueness in (b) at the curve level). -/
def decoupling_metric : Prop :=
  ∀ (M : Type) [MetricSpace M] [TopologicalSpace.SeparableSpace M] [MeasurableSpace M] [BorelSpace M]
    (T Ω : Type) [MeasurableSpace T] [MeasurableSpace Ω] (lam : Measure T) [IsProbabilityMeasure lam]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (ev : Ω → T → M) (m : T → M),
    Measurable (Function.uncurry ev) → Measurable m → frechetJ lam ν ev m < ⊤ →
      (∀ z : T → M, Measurable z → frechetJ lam ν ev z = ∫⁻ t, psiT ν ev t (z t) ∂lam) ∧
      (∃ N : Set T, MeasurableSet N ∧ lam N = 0 ∧ ∀ t ∉ N, (∀ p, psiT ν ev t p < ⊤) ∧ Continuous (psiT ν ev t)) ∧
      (∀ z ∈ curveSet lam m, (∀ z' ∈ curveSet lam m, frechetJ lam ν ev z ≤ frechetJ lam ν ev z') ↔
        ∀ᵐ t ∂lam, ∀ p, psiT ν ev t (z t) ≤ psiT ν ev t p) ∧
      (IsCAT0 M → ∀ [CompleteSpace M],
        (∃ z ∈ curveSet lam m, ∀ z' ∈ curveSet lam m, frechetJ lam ν ev z ≤ frechetJ lam ν ev z') ∧
        ∀ z ∈ curveSet lam m, ∀ z' ∈ curveSet lam m,
          (∀ w ∈ curveSet lam m, frechetJ lam ν ev z ≤ frechetJ lam ν ev w) →
          (∀ w ∈ curveSet lam m, frechetJ lam ν ev z' ≤ frechetJ lam ν ev w) → z =ᵐ[lam] z')

/-! ### G `thm:flatlimit` on the unit sphere: the Taylor premise discharged -/

/-- G `thm:flatlimit` UNCONDITIONALLY on the unit sphere `S^d` ("on the unit sphere `Θ(r) = 1 − r cot r`"): the
Riemannian Taylor premise of the frozen `flatlimit` is DISCHARGED for the geodesic cost
`c_s(v, x) = ½ D(E_m(s v), x)²` (frozen `sphCost`, `refCurve`) with `Θ = 1 − r cot r`, `r = ρ₀ + s b < π`: the
reference fields form a Hilbert space `H` identified with tangent fields along `m` by `ev`
(`⟨v, v'⟩_H = ∫ ⟨v(t), v'(t)⟩ dλ`, the `H₀` geometry; tangency `λ`-a.e.), `μ`-a.s. `‖v‖ ≤ 1` and
`esssup_t |v(t)| ≤ b`; the data satisfy `sup_t d(m(t), x(t)) ≤ ρ₀`; `L x = Log_m x` (frozen-style abstract map with
`ev (L x) = Log_{m(·)} x(·)` `λ`-a.e.) and
`d2 x = D(m, x)²`. Then `TV(π^geo_s, π^tan) ≤ sΘ/(4η)` and `∫ ‖F^geo_s − F^tan‖ dP ≤ sΘ/(2η)` (the frozen
conclusion verbatim). -/
def flatlimit_sphere : Prop :=
  ∀ (d : ℕ) (H 𝒳 : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    [BorelSpace H] [SecondCountableTopology H] [MeasurableSpace 𝒳] (μ : Measure H) (P : Measure 𝒳)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] (lam : Measure ℝ) [IsProbabilityMeasure lam]
    (m : ℝ → EuclideanSpace ℝ (Fin (d + 1))) (ev : H → ℝ → EuclideanSpace ℝ (Fin (d + 1)))
    (X : 𝒳 → ℝ → EuclideanSpace ℝ (Fin (d + 1))) (L : 𝒳 → H) (s η ρ₀ b : ℝ) (f f' : H → ℝ) (g g' : 𝒳 → ℝ),
    0 < s → 0 < η → 0 ≤ ρ₀ → 0 ≤ b → 0 < ρ₀ + s * b → ρ₀ + s * b < Real.pi →
    Measurable m → (∀ t, ‖m t‖ = 1) → (∀ v, Measurable (ev v)) → (∀ v, ∀ᵐ t ∂lam, ⟪m t, ev v t⟫_ℝ = 0) →
    (∀ v v', ⟪v, v'⟫_ℝ = ∫ t, ⟪ev v t, ev v' t⟫_ℝ ∂lam) →
    (∀ x, Measurable (X x)) → (∀ x t, ‖X x t‖ = 1) → (∀ x t, sphDist (m t) (X x t) ≤ ρ₀) →
    (∀ x, ∀ᵐ t ∂lam, ev (L x) t = sphLog (m t) (X x t)) → Measurable L →
    Measurable (fun z : H × 𝒳 => sphCost lam (refCurve m (ev z.1) s) (X z.2)) →
    Measurable (fun x => ∫ t, sphDist (m t) (X x t) ^ 2 ∂lam) →
    (∀ᵐ v ∂μ, ‖v‖ ≤ 1) → (∀ᵐ v ∂μ, ∀ᵐ t ∂lam, ‖ev v t‖ ≤ b) →
    GibbsHyp μ P (s * η) (fun z => sphCost lam (refCurve m (ev z.1) s) (X z.2)) f g →
    GibbsHyp μ P η (fun z => ‖z.1 - L z.2‖ ^ 2 / 2) f' g' →
      tv (gibbsPlan μ P (s * η) (fun z => sphCost lam (refCurve m (ev z.1) s) (X z.2)) f g)
          (gibbsPlan μ P η (fun z => ‖z.1 - L z.2‖ ^ 2 / 2) f' g') ≤
          s * (1 - (ρ₀ + s * b) * Real.cos (ρ₀ + s * b) / Real.sin (ρ₀ + s * b)) / (4 * η) ∧
        ∫⁻ x, ‖gibbsMean μ (s * η) (fun z => sphCost lam (refCurve m (ev z.1) s) (X z.2)) f g id x -
          gibbsMean μ η (fun z => ‖z.1 - L z.2‖ ^ 2 / 2) f' g' id x‖ₑ ∂P ≤
          ENNReal.ofReal (s * (1 - (ρ₀ + s * b) * Real.cos (ρ₀ + s * b) / Real.sin (ρ₀ + s * b)) / (2 * η))

end Claims

end StatFormal.WaveP3e
