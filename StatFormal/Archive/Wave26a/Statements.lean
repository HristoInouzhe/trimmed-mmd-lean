import StatFormal.Archive.Wave24b.Statements
import StatFormal.Archive.Wave24c.Statements
import TauCeti.MeasureTheory.OptimalTransport.Entropic.Basic

/-!
# FROZEN STATEMENTS — wave 26a: Rigollet–Stromme sample complexity of entropic OT for bounded costs and general laws
# (and the downstream G `thm:rates` 1/r term, T `cor:randomised` premise, A `prop:curse`)

Sources:
* Rigollet–Stromme, *On the sample complexity of entropic optimal transport*, Ann. Statist. 53(1) 2025,
  arXiv:2206.13472v1 (checked against the v1 PDF, 2026-10-16): Theorem 1 (duality), Proposition 10 (bounded
  potentials and densities), Lemma 11 / Proposition 12 / (4.3) (strong concavity, error bound), Proposition 13 and
  Lemma 15 (canonical extensions), Lemma 14 (dual gradient at the population potentials), Theorem 3 (cost),
  Theorems 4 and 7 (entropic regression function, labels). RS assume `‖x‖, ‖y‖ ≤ 1/2`, quadratic cost, equal sample
  sizes, and remark (p. 1) that "our results readily extend to any cost that is uniformly bounded".
* otfd G `thm:rates` (`otfd/papers/G_geodesic/main.tex:855-878`, proof `appendix.tex:626-715`): the `1/r` term.
* otfd T `cor:randomised` (theory:374): the Rigollet–Stromme premise of the frozen Wave 24c `randomised_calibration`.
* otfd A `prop:curse` (`otfd/papers/A_sieves/main.tex:319-337`), with the entropic rank map of B `subsec:oos-menu`
  (`otfd/papers/B_bands/main.tex:597-605`, cost `‖z − u‖²`).
Imports the frozen `Wave24b` (`IsMaxDual`, `condMean`, `empLaw`) and `Wave24c` (`randCDF`, `empNormCDF`; through it
`Wave23a.cdfK`) statements, Tau Ceti (`entropicTransportCost`) and Mathlib.

Covered (bounded measurable cost `0 ≤ c ≤ c̄` on arbitrary measurable spaces, arbitrary probability laws, `ε > 0`):
* `schpot_exists` (canonically extended Schrödinger potentials exist; Tau Ceti's Sinkhorn fixed point),
  `schpot_unique` (unique up to `(a, −a)` at every point), `schpot_bounds` (`osc f, osc g ≤ c̄`,
  `e^{−2c̄/ε} ≤ p ≤ e^{2c̄/ε}` everywhere; RS Proposition 10 has `e^{±5η}`).
* `schpot_stability` (RS (4.3), any two pairs of laws): `∫ ((f₁ − f₀) ⊕ (g₁ − g₀))² d(μ'⊗ν') ≤
  ε² e^{4c̄/ε} ‖∇Φ_{μ',ν'}(f₀, g₀)‖²`.
* `dual_grad_second_moment` (RS Lemma 14, sizes `m`, `n`): `E ‖∇Φ_{m,n}(f*, g*)‖² ≤ (e^{2c̄/ε} − 1)(1/m + 1/n)`.
* `potential_rate` ((4.3) + Lemma 14): `E m⁻¹n⁻¹ Σ_{j,i} ((f̂ − f*)(X_j) + (ĝ − g*)(Y_i))² ≤
  ε² e^{4c̄/ε}(e^{2c̄/ε} − 1)(1/m + 1/n)`, for every choice of empirical potentials.
* `map_rate` (RS Theorems 4 and 7): Hilbert-valued labels `ψ(x, y)`, `‖ψ‖ ≤ U`;
  `E ∫ ‖b̂ − b‖² dμ ≤ 22 U² e^{18c̄/ε}(1/m + 1/n)`, `b̂` the plug-in through the canonical extension.
* `cost_rate` (RS Theorem 3, mean square and mean absolute error): `S_ε = entropicTransportCost` (Tau Ceti) is finite,
  `E |S_ε(μ_m, ν_n) − S_ε(μ, ν)|² ≤ C_S (1/m + 1/n)` and `E |S_ε(μ_m, ν_n) − S_ε(μ, ν)| ≤ (C_S (1/m + 1/n))^{1/2}`,
  `C_S = 2ε² e^{4c̄/ε}(e^{2c̄/ε} − 1) + 4c̄²`.
* G `thm:rates`, the `1/r` term (DISCHARGE of what frozen Wave 24b leaves out): reference draws `V_1..V_r` i.i.d. `μ`
  (any law: G's reference is continuous, which is not used), data i.i.d. `P`, independent; `F̂ = condMean` at any maximiser `f̂` of the frozen semi-dual,
  `F_ε(x) = ∫ v p*(v, x) dμ(v)`: `rates_rank_two_sample` (`E ∫ ‖F̂ − F_ε‖² dP` and `E ∫ (‖F̂‖ − ‖F_ε‖)² dP
  ≤ 22 e^{18c̄/ε}(1/n + 1/r)`), `rates_label_two_sample` (any labels `ψ(v, x)`, `‖ψ‖ ≤ U`, constant `22U²e^{18c̄/ε}`;
  the radial rank `ψ = ‖v‖` and the transport cost `ψ = c`, `U = c̄`, are instances).
* T `cor:randomised` (DISCHARGE of the Rigollet–Stromme premises of frozen Wave 24c `randomised_calibration`):
  `randomised_calibration_rs` — the frozen conclusion for i.i.d. reference draws and data and any empirical
  Schrödinger potentials, with `A = 4e^{12c̄/ε}(e^{2c̄/ε} − 1)`, `M = 2c̄/ε`; only DKW–Massart stays a hypothesis.
* A `prop:curse`: `curse_sampling` — for every `K`, laws on the `ρ`-ball of `ℝ^K`, cost `‖u − z‖²`, `n` data and `n`
  reference draws: `E ∫ ‖F̂ − F_{K,ε}‖² dP_K ≤ 4ρ² C(4ρ²/ε)/n` with `C(t) = 11 e^{18t}` (independent of `K`, `P`, `μ`).

Not covered (declared):
* RS high-probability bounds (Theorems 3–6 "moreover" parts), the bias `|E S_n − S| ≲ 1/n` (only the mean-square
  rate; the bias bound needs the PL inequality at second order), Theorem 5 (density in `L²(μ⊗ν)`), Theorem 6
  (`(π_n − π*)(φ)`), Theorems 8–9 (classification).
* G `thm:rates`: stratified/antithetic reference draws (`lem:stratified`, the `2/r`), the quantile clause.
* T `cor:randomised`: DKW–Massart itself (hypothesis, as in the frozen claim).
* A `prop:curse`: the projection step `‖Π_K X‖ ≤ ‖X‖` from `H` to `ℝ^K` (one line; the claim starts from the coefficient
  laws on the `ρ`-ball, `ρ = max(B, R)`).

Encodings (to be checked by the critic):
* `schDens ε c f g x y = exp((f x + g y − c x y)/ε)`; `IsSchrodingerPot`: measurable potentials with BOTH marginal
  equations at EVERY point (the canonical extension; `∫ = 1` forces integrability, so no junk). For empirical laws
  (frozen `Wave24b.empLaw`) this is RS §2.3. Every Schrödinger pair of potentials agrees a.e. with such a pair
  (route `exists_isSchPot_of_ae`), so nothing is lost.
* Costs are bounded on all of `X × Y` (`BddCost`), as in frozen Wave 24b: `X`, `Y` may be taken to be full-measure
  sets (the closed balls in `curse_sampling`, the unit ball of reference fields in G).
* Samples: `Measure.pi` products, the two samples independent (`Measure.prod`); `m` and `n` arbitrary (RS: `m = n`).
* Errors and gradients are written as the finite sums they are (`dualGradSq`, `potErrSq`, `empBary`); the
  conclusions include measurability in the sample and integrability in the evaluation point; expectations are lower
  Lebesgue integrals of `ofReal` of nonnegative measurable functions (equal to the Bochner expectations).
* Empirical potentials are ANY selection `ω ↦ (f̂_ω, ĝ_ω)` (no measurability assumed; the errors do not depend on the
  selection by `schpot_unique`, and are proved measurable).
* Cost: `S_ε(μ, ν) = entropicTransportCost (ofReal ∘ c) ε.toNNReal μ ν` in `[0,∞]`; its finiteness is part of the
  conclusion, so `toReal` is not junk.
* G: reference space `V` with labels `lab : V → E` (`‖lab‖ ≤ 1`; G: `V` the unit ball of reference fields, `lab` the
  inclusion) and cost `cost : V → K → ℝ`; `F̂` is the frozen `condMean` with weights `1/r`, costs `cost(V_j, ·)`, labels
  `lab(V_j)`, at ANY maximiser of the frozen semi-dual `J_{P_n}` (the frozen `IsMaxDual`); `F_ε` uses population
  potentials of `(μ, P)`. `ϱ = ‖F‖`.
* T: `Ω` is the product of the two samples; the frozen `randCDF` is evaluated at the empirical potentials at the
  reference draws; the DKW–Massart hypothesis is stated for the reference sample.
* A: laws on the closed ball `closedBall 0 ρ` of `EuclideanSpace ℝ (Fin K)` (subtype), cost `‖u − z‖²` (B
  `subsec:oos-menu`), `F̂` the frozen `condMean` (softmax over the reference draws with the fitted reference potential).

Proof notes (author of the draft, 2026-10-16): all 12 claims are proved in `Wave26a/Route{Core,Rates,RandCal,Cost}.lean`
(`Proofs.lean` checks each claim against its route theorem; axioms: propext, Classical.choice, Quot.sound) from the new
library `Foundations/EntropicRates/{Basic,Stability,Exists,Empirical,Variance,Rates,OOS,Map,Cost}.lean`. Ingredients:
strong monotonicity of the dual gradient without second derivatives (`(s−t)(eˢ−eᵗ) ≥ (s−t)² min(eˢ,eᵗ)`, Fubini,
Young after centring), Tau Ceti's Sinkhorn fixed point for existence and `entropicTransportCost_eq_ofReal_of_eq_withDensity`
for the cost, the measurable normalised discrete potential `solF` of frozen-wave route `Wave24b.RouteSolF`, and the
Hilbert sample-mean variance of `Foundations/Concentration`. No chaining, no empirical-process suprema. The frozen
Wave 24c `randomised_calibration` is used through its certified route (`Wave24c.RouteRandRank`).
Constants: RS's `e^{5η}` (Prop. 10), `e^{5η}/η` ((4.3)) and `2e^{10η}/n` (Lemma 14) become `e^{2c̄/ε}`, `ε e^{2c̄/ε}`
and `(e^{2c̄/ε} − 1)(1/m + 1/n)` (RS: `c̄ = 1`, `η = 1/ε`), because no normalisation of the potentials is needed in
the monotonicity argument; the map constant `22 e^{18c̄/ε}` coincides in its exponent with frozen Wave 24b's
`K_ε = 4e^{18c̄/ε}`.

Paper notes: (1) A `prop:curse` and QUEUE row 320: RS p. 4 says only that the suppressed constants "are typically
exponentially large in η" (a statement about size, not an upper bound on growth; A's current wording "typically
exponentially large", DEFECTS row 32, matches it); the upper bound "at most exponential" is supplied by `curse_sampling`,
`C(t) = 11e^{18t}` with `t = 4ρ²/ε` (cost `‖u − z‖²`, as in B `subsec:oos-menu`; for the cost `½‖u − z‖²` the argument is `2ρ²/ε`). (2) G
`app:rates` and T `cor:randomised` use RS with unequal sizes `n ≠ r`; RS state `m = n` only — the extension is exactly
`dual_grad_second_moment`/`potential_rate`, and G's `E‖∇Φ‖² ≤ C(1/n + 1/r)` is confirmed with `C = e^{2c̄/ε} − 1`.
(3) G's normalisation `P_n(ĝ) = 0` and the bounds `‖f̄‖ ≤ 3c̄` are not needed: every bound depends only on `f̂ ⊕ ĝ`.

Critic notes (2026-10-16, adversarial review; `lake build StatFormal.Wave26a.Proofs` succeeds, all 12 route theorems
depend on propext, Classical.choice, Quot.sound only):
* Normalisation (check (a)): RS (2.1)–(2.3) is `π(‖x − y‖²) + η⁻¹ KL(π‖P⊗Q)` with density `e^{η(f ⊕ g − c)}`, i.e.
  `ε = 1/η` and `schDens` exactly; RS's supports `‖x‖, ‖y‖ ≤ 1/2` give `0 ≤ c ≤ 1 = c̄`. Tau Ceti's
  `entropicTransportCost` is RS (2.1) (`∫⁻ c dπ + ε klDiv π (μ.prod ν)` over couplings). With RS's normalisation
  `ν_n(g_n) = ν_n(ḡ⋆) = 0` the cross term vanishes, so RS's `‖(f_n − f̄⋆, g_n − ḡ⋆)‖²_n` EQUALS `potErrSq` — the
  potential claims are not weaker than RS. The improved constants are genuine: canonical pairs satisfy
  `f ⊕ g − c ∈ [−2c̄, 2c̄]` everywhere (RS bound `f`, `g` separately: `|f|, |g| ≤ 2`, whence `5η`); (4.3) follows from
  `(s−t)(eˢ−eᵗ) ≥ (s−t)² min(eˢ, eᵗ)` and centring (the gradient's two means coincide), inverse modulus `ε e^{2c̄/ε}`;
  Lemma 14 uses `Var p ≤ E p² − 1 ≤ sup p − 1` instead of RS's `Var p ≤ sup p²`.
* `randomised_calibration_rs` (check (b)), diff against frozen Wave 24c `randomised_calibration`: `Ω` specialised to
  `(Fin N → ℝ^K) × (Fin n → Z)` with `μ_K^N ⊗ ν^n`, `U l ω = ω.1 l`, `fh_frozen ω l = fh ω (ω.1 l)`; removed: the six
  measurability premises, the two `≤ M` premises, the population normalisation (implied by `IsSchrodingerPot`), `0 ≤ A`
  and the two RS mean-square premises; added: `BddCost`, `IsSchrodingerPot` (population and empirical); `M`, `A`
  instantiated (`2e^M√A = 4e^{8c̄/ε}(e^{2c̄/ε} − 1)^{1/2}` checked); DKW–Massart is stated on the reference marginal
  `μ_K^N` (equivalent to the frozen form, the integrand depending on `ω.1` only); conclusion verbatim (`randCDF`,
  `cdfK`, constant). `BddCost` asks `c ≤ c̄` on ALL of `ℝ^K × Z` (the frozen `μ_K` lives on `ℝ^K`, not on a ball): for
  T's quadratic cost use `min(c, c̄)`, which agrees with `c` on `supp μ_K × supp ν` and so leaves `randCDF` unchanged
  almost surely (card note).
* `rates_*_two_sample` (check (c)): `condMean` with weights `1/r` is G (eq:estimators) (the weights cancel); `F_ε` is G
  `app:rates` `∫ v p⋆(v, x) dμ(v)`; G's `K_ε` (`22e^{18c̄/ε}`), `c̄²K_ε` for `κ̂` and `ϱ = ‖F‖` match. Not covered: the
  `2/r` stratified/antithetic case, the quantile clause. The draft's "continuous `μ`" wording was removed: continuity is
  not a hypothesis.
* `curse_sampling` (check (c)): the claim is about laws on the `ρ`-ball of `ℝ^K` only; A's projection step (`‖Π_K X‖ ≤ ‖X‖`,
  so `P_K`, `μ_K` live on that ball) and the passage from laws on `ℝ^K` concentrated on the ball to laws on the subtype
  (restriction, no loss) are the paper-side gap. `F̂` is defined on the ball only (A extends it to `ℝ^K`), which does
  not affect `∫ · dP_K`. A's cost is B's `‖z − u‖²_{M_K}` with `M_K = I` (orthonormal coordinates). `C(t) = 11e^{18t}`
  is uniform in `K`, `P`, `μ` as A states.
* Junk values (check (d)): `IsSchrodingerPot` forces integrability (`∫ = 1`); all expectations are lintegrals of
  `ofReal` of nonnegative quantities, with measurability and integrability proved as conjuncts; `toReal` of the costs is
  guarded by the finiteness conjuncts; `1/m`, `1/n` are real divisions with `0 < m, n`; `ε.toNNReal` is guarded by
  `0 < ε`. Supports as types (closed balls, `V`, `K`) are not a restriction: a law with bounded support restricts to
  its support. Non-vacuity: canonical pairs exist (`schpot_exists`, also for `empLaw`), semi-dual maximisers exist
  (the first-order solution of Wave 24b `focM_exists` maximises the concave `J`; not itself formalised), DKW–Massart holds for every law of the radii.
* `map_rate` also covers RS Theorem 7 (random labels) through the instance `Y × 𝒜` (docstring updated).
* Paper note (1) corrected: RS do not state "at most exponential"; `curse_sampling` does.

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace StatFormal.Wave26a

section Objects

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The Gibbs density `p_{f,g}(x, y) = exp((f x + g y − c x y)/ε)` of a pair of potentials. -/
def schDens (ε : ℝ) (c : X → Y → ℝ) (f : X → ℝ) (g : Y → ℝ) (x : X) (y : Y) : ℝ :=
  Real.exp ((f x + g y - c x y) / ε)

/-- Canonically extended Schrödinger potentials of `(μ, ν)`: measurable, with both marginal equations
`∫ p(x, ·) dν = 1` and `∫ p(·, y) dμ = 1` at every point. -/
def IsSchrodingerPot (ε : ℝ) (c : X → Y → ℝ) (μ : Measure X) (ν : Measure Y) (f : X → ℝ) (g : Y → ℝ) : Prop :=
  Measurable f ∧ Measurable g ∧ (∀ x, ∫ y, schDens ε c f g x y ∂ν = 1) ∧ ∀ y, ∫ x, schDens ε c f g x y ∂μ = 1

/-- `ε > 0` and a jointly measurable cost with `0 ≤ c ≤ c̄` everywhere. -/
def BddCost (ε cbar : ℝ) (c : X → Y → ℝ) : Prop :=
  0 < ε ∧ Measurable (Function.uncurry c) ∧ ∀ x y, 0 ≤ c x y ∧ c x y ≤ cbar

/-- Squared norm of the dual gradient of the empirical problem at `(f, g)`:
`m⁻¹ Σ_j (1 − n⁻¹ Σ_i p(x_j, y_i))² + n⁻¹ Σ_i (1 − m⁻¹ Σ_j p(x_j, y_i))²`. -/
def dualGradSq {m n : ℕ} (ε : ℝ) (c : X → Y → ℝ) (f : X → ℝ) (g : Y → ℝ) (x : Fin m → X) (y : Fin n → Y) : ℝ :=
  ∑ j, (m : ℝ)⁻¹ * (1 - ∑ i, (n : ℝ)⁻¹ * schDens ε c f g (x j) (y i)) ^ 2 +
    ∑ i, (n : ℝ)⁻¹ * (1 - ∑ j, (m : ℝ)⁻¹ * schDens ε c f g (x j) (y i)) ^ 2

/-- In-sample squared error `m⁻¹ n⁻¹ Σ_{j,i} ((fh − f)(x_j) + (gh − g)(y_i))²` of potentials `(fh, gh)`. -/
def potErrSq {m n : ℕ} (fh f : X → ℝ) (gh g : Y → ℝ) (x : Fin m → X) (y : Fin n → Y) : ℝ :=
  ∑ j, (m : ℝ)⁻¹ * ∑ i, (n : ℝ)⁻¹ * ((fh (x j) - f (x j)) + (gh (y i) - g (y i))) ^ 2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Population barycentric map `b(x) = ∫ p(x, y) ψ(x, y) dν(y)` (RS (2.14) for `ψ(x, y) = y`). -/
def popBary (ε : ℝ) (c : X → Y → ℝ) (f : X → ℝ) (g : Y → ℝ) (ν : Measure Y) (ψ : X → Y → H) (x : X) : H :=
  ∫ y, schDens ε c f g x y • ψ x y ∂ν

/-- Empirical barycentric map `b̂(x) = n⁻¹ Σ_i p̂(x, y_i) ψ(x, y_i)` (RS (2.18), (3.7)). -/
def empBary {n : ℕ} (ε : ℝ) (c : X → Y → ℝ) (fh : X → ℝ) (gh : Y → ℝ) (y : Fin n → Y) (ψ : X → Y → H) (x : X) : H :=
  ∑ i, (n : ℝ)⁻¹ • (schDens ε c fh gh x (y i) • ψ x (y i))

end Objects

/-- The constant of `prop:curse`, `C(t) = 11 e^{18t}`. -/
def curseC (t : ℝ) : ℝ := 11 * Real.exp (18 * t)

/-- The quadratic cost `‖u − z‖²` between points of the closed `ρ`-ball of `ℝ^K` (B `subsec:oos-menu`). -/
def sqCost {K : ℕ} {ρ : ℝ} (u z : Metric.closedBall (0 : EuclideanSpace ℝ (Fin K)) ρ) : ℝ :=
  ‖(u : EuclideanSpace ℝ (Fin K)) - (z : EuclideanSpace ℝ (Fin K))‖ ^ 2

namespace Claims

/-! #### Rigollet–Stromme: structure of the problem -/

/-- Existence: for any probability laws and any bounded measurable cost, canonically extended Schrödinger
potentials exist. -/
def schpot_exists : Prop :=
  ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (ε cbar : ℝ) (c : X → Y → ℝ),
    BddCost ε cbar c → ∃ f g, IsSchrodingerPot ε c μ ν f g

/-- Uniqueness: two pairs differ by `(a, −a)` at every point. -/
def schpot_unique : Prop :=
  ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (ε cbar : ℝ) (c : X → Y → ℝ) (f f' : X → ℝ) (g g' : Y → ℝ),
    BddCost ε cbar c → IsSchrodingerPot ε c μ ν f g → IsSchrodingerPot ε c μ ν f' g' →
      ∃ a : ℝ, (∀ x, f' x = f x + a) ∧ ∀ y, g' y = g y - a

/-- Bounds (RS Proposition 10): `f x − f x' ≤ c̄`, `g y − g y' ≤ c̄` and `e^{−2c̄/ε} ≤ p ≤ e^{2c̄/ε}` everywhere. -/
def schpot_bounds : Prop :=
  ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (ε cbar : ℝ) (c : X → Y → ℝ) (f : X → ℝ) (g : Y → ℝ),
    BddCost ε cbar c → IsSchrodingerPot ε c μ ν f g →
      (∀ x x', f x - f x' ≤ cbar) ∧ (∀ y y', g y - g y' ≤ cbar) ∧
        ∀ x y, Real.exp (-(2 * cbar) / ε) ≤ schDens ε c f g x y ∧ schDens ε c f g x y ≤ Real.exp (2 * cbar / ε)

/-- Stability (RS (4.3), for arbitrary laws): for Schrödinger potentials `(f₀, g₀)` of `(μ, ν)` and `(f₁, g₁)` of
`(μ', ν')`, `∫ ((f₁ − f₀) ⊕ (g₁ − g₀))² d(μ' ⊗ ν') ≤ ε² e^{4c̄/ε} (∫ Δ₁² dμ' + ∫ Δ₂² dν')`, where
`Δ₁ = 1 − ∫ p₀(·, y) dν'(y)`, `Δ₂ = 1 − ∫ p₀(x, ·) dμ'(x)` is the dual gradient of the `(μ', ν')` problem at
`(f₀, g₀)`; all three integrands are integrable. -/
def schpot_stability : Prop :=
  ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] (μ μ' : Measure X) (ν ν' : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν']
    (ε cbar : ℝ) (c : X → Y → ℝ) (f₀ f₁ : X → ℝ) (g₀ g₁ : Y → ℝ),
    BddCost ε cbar c → IsSchrodingerPot ε c μ ν f₀ g₀ → IsSchrodingerPot ε c μ' ν' f₁ g₁ →
      Integrable (fun z : X × Y => ((f₁ z.1 - f₀ z.1) + (g₁ z.2 - g₀ z.2)) ^ 2) (μ'.prod ν') ∧
      Integrable (fun x => (1 - ∫ y, schDens ε c f₀ g₀ x y ∂ν') ^ 2) μ' ∧
      Integrable (fun y => (1 - ∫ x, schDens ε c f₀ g₀ x y ∂μ') ^ 2) ν' ∧
      ∫ z, ((f₁ z.1 - f₀ z.1) + (g₁ z.2 - g₀ z.2)) ^ 2 ∂(μ'.prod ν') ≤
        ε ^ 2 * Real.exp (4 * cbar / ε) *
          (∫ x, (1 - ∫ y, schDens ε c f₀ g₀ x y ∂ν') ^ 2 ∂μ' + ∫ y, (1 - ∫ x, schDens ε c f₀ g₀ x y ∂μ') ^ 2 ∂ν')

/-! #### Rigollet–Stromme: rates -/

/-- RS Lemma 14 (sample sizes `m`, `n`): at the population potentials, the squared empirical dual gradient is
measurable in the samples and `E ‖∇Φ_{m,n}(f*, g*)‖² ≤ (e^{2c̄/ε} − 1)(1/m + 1/n)`. -/
def dual_grad_second_moment : Prop :=
  ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (ε cbar : ℝ) (c : X → Y → ℝ) (m n : ℕ) (f : X → ℝ) (g : Y → ℝ),
    BddCost ε cbar c → 0 < m → 0 < n → IsSchrodingerPot ε c μ ν f g →
      Measurable (fun ω : (Fin m → X) × (Fin n → Y) => dualGradSq ε c f g ω.1 ω.2) ∧
      ∫⁻ ω, ENNReal.ofReal (dualGradSq ε c f g ω.1 ω.2)
          ∂((Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin n => ν)) ≤
        ENNReal.ofReal ((Real.exp (2 * cbar / ε) - 1) * (1 / m + 1 / n))

/-- RS (4.3) with Lemma 14 (parametric rate of the potentials): for ANY empirical Schrödinger potentials
`(f̂_ω, ĝ_ω)` of `(μ_m, ν_n)`, the in-sample squared error is measurable in the samples and
`E potErrSq ≤ ε² e^{4c̄/ε} (e^{2c̄/ε} − 1)(1/m + 1/n)`. -/
def potential_rate : Prop :=
  ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (ε cbar : ℝ) (c : X → Y → ℝ) (m n : ℕ) (f : X → ℝ) (g : Y → ℝ)
    (fh : (Fin m → X) × (Fin n → Y) → X → ℝ) (gh : (Fin m → X) × (Fin n → Y) → Y → ℝ),
    BddCost ε cbar c → 0 < m → 0 < n → IsSchrodingerPot ε c μ ν f g →
    (∀ ω, IsSchrodingerPot ε c (StatFormal.Wave24b.empLaw ω.1) (StatFormal.Wave24b.empLaw ω.2) (fh ω) (gh ω)) →
      Measurable (fun ω : (Fin m → X) × (Fin n → Y) => potErrSq (fh ω) f (gh ω) g ω.1 ω.2) ∧
      ∫⁻ ω, ENNReal.ofReal (potErrSq (fh ω) f (gh ω) g ω.1 ω.2)
          ∂((Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin n => ν)) ≤
        ENNReal.ofReal (ε ^ 2 * Real.exp (4 * cbar / ε) * (Real.exp (2 * cbar / ε) - 1) * (1 / m + 1 / n))

/-- RS Theorems 4 and 7 (entropic regression function, labels): for labels `ψ : X → Y → H` with `‖ψ‖ ≤ U` and ANY
empirical Schrödinger potentials, `x ↦ ‖b̂_ω(x) − b(x)‖²` is `μ`-integrable, its integral is measurable in the
samples, and `E ∫ ‖b̂ − b‖² dμ ≤ 22 U² e^{18c̄/ε}(1/m + 1/n)`. RS Theorem 7's random labels `A` (`(Y, A) ∼ ω`) are the
instance `Y × 𝒜`, `ν = ω`, cost `c(x, y)`, `ψ(x, (y, a)) = a`. -/
def map_rate : Prop :=
  ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] (ε cbar U : ℝ) (c : X → Y → ℝ) (ψ : X → Y → H)
    (m n : ℕ) (f : X → ℝ) (g : Y → ℝ) (fh : (Fin m → X) × (Fin n → Y) → X → ℝ)
    (gh : (Fin m → X) × (Fin n → Y) → Y → ℝ),
    BddCost ε cbar c → 0 < m → 0 < n → Measurable (Function.uncurry ψ) → (∀ x y, ‖ψ x y‖ ≤ U) →
    IsSchrodingerPot ε c μ ν f g →
    (∀ ω, IsSchrodingerPot ε c (StatFormal.Wave24b.empLaw ω.1) (StatFormal.Wave24b.empLaw ω.2) (fh ω) (gh ω)) →
      (∀ ω : (Fin m → X) × (Fin n → Y),
        Integrable (fun x => ‖empBary ε c (fh ω) (gh ω) ω.2 ψ x - popBary ε c f g ν ψ x‖ ^ 2) μ) ∧
      Measurable (fun ω : (Fin m → X) × (Fin n → Y) =>
        ∫ x, ‖empBary ε c (fh ω) (gh ω) ω.2 ψ x - popBary ε c f g ν ψ x‖ ^ 2 ∂μ) ∧
      ∫⁻ ω, ENNReal.ofReal (∫ x, ‖empBary ε c (fh ω) (gh ω) ω.2 ψ x - popBary ε c f g ν ψ x‖ ^ 2 ∂μ)
          ∂((Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin n => ν)) ≤
        ENNReal.ofReal (22 * U ^ 2 * Real.exp (18 * cbar / ε) * (1 / m + 1 / n))

/-- RS Theorem 3 (cost, mean square and mean absolute error): the entropic costs are finite, the empirical cost is
measurable in the samples, `E |S_ε(μ_m, ν_n) − S_ε(μ, ν)|² ≤ C_S (1/m + 1/n)` and
`E |S_ε(μ_m, ν_n) − S_ε(μ, ν)| ≤ (C_S (1/m + 1/n))^{1/2}`, `C_S = 2ε² e^{4c̄/ε}(e^{2c̄/ε} − 1) + 4c̄²`. -/
def cost_rate : Prop :=
  ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (ε cbar : ℝ) (c : X → Y → ℝ) (m n : ℕ),
    BddCost ε cbar c → 0 < m → 0 < n →
      TauCeti.entropicTransportCost (fun z => ENNReal.ofReal (c z.1 z.2)) ε.toNNReal μ ν ≠ ∞ ∧
      (∀ ω : (Fin m → X) × (Fin n → Y), TauCeti.entropicTransportCost (fun z => ENNReal.ofReal (c z.1 z.2))
        ε.toNNReal (StatFormal.Wave24b.empLaw ω.1) (StatFormal.Wave24b.empLaw ω.2) ≠ ∞) ∧
      Measurable (fun ω : (Fin m → X) × (Fin n → Y) => (TauCeti.entropicTransportCost
        (fun z => ENNReal.ofReal (c z.1 z.2)) ε.toNNReal (StatFormal.Wave24b.empLaw ω.1)
          (StatFormal.Wave24b.empLaw ω.2)).toReal) ∧
      ∫⁻ ω, ENNReal.ofReal (((TauCeti.entropicTransportCost (fun z => ENNReal.ofReal (c z.1 z.2)) ε.toNNReal
          (StatFormal.Wave24b.empLaw ω.1) (StatFormal.Wave24b.empLaw ω.2)).toReal -
          (TauCeti.entropicTransportCost (fun z => ENNReal.ofReal (c z.1 z.2)) ε.toNNReal μ ν).toReal) ^ 2)
          ∂((Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin n => ν)) ≤
        ENNReal.ofReal ((2 * ε ^ 2 * Real.exp (4 * cbar / ε) * (Real.exp (2 * cbar / ε) - 1) + 4 * cbar ^ 2) *
          (1 / m + 1 / n)) ∧
      ∫⁻ ω, ENNReal.ofReal |(TauCeti.entropicTransportCost (fun z => ENNReal.ofReal (c z.1 z.2)) ε.toNNReal
          (StatFormal.Wave24b.empLaw ω.1) (StatFormal.Wave24b.empLaw ω.2)).toReal -
          (TauCeti.entropicTransportCost (fun z => ENNReal.ofReal (c z.1 z.2)) ε.toNNReal μ ν).toReal|
          ∂((Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin n => ν)) ≤
        ENNReal.ofReal (Real.sqrt ((2 * ε ^ 2 * Real.exp (4 * cbar / ε) * (Real.exp (2 * cbar / ε) - 1) +
          4 * cbar ^ 2) * (1 / m + 1 / n)))

/-! #### otfd G `thm:rates`: the `1/r` term (continuous reference) -/

/-- G `thm:rates` with i.i.d. reference draws, any labels `ψ(v, x)` with `‖ψ‖ ≤ U` (rank `ψ = lab v`, radial rank
`ψ = ‖lab v‖`, transport cost `ψ = cost`, `U = c̄`): for `V ∼ μ^r`, `X ∼ P^n` independent and any maximisers `f̂` of the
frozen semi-dual `J_{P_n}` with weights `1/r`, the error of the frozen `condMean` against
`F_ε(x) = ∫ ψ(v, x) p*(v, x) dμ(v)` is `P`-integrable, measurable in the samples, and
`E ∫ ‖F̂ − F_ε‖² dP ≤ 22 U² e^{18c̄/ε}(1/n + 1/r)`. -/
def rates_label_two_sample : Prop :=
  ∀ (K V : Type) [MeasurableSpace K] [MeasurableSpace V] (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] (n r : ℕ) (ε cbar U : ℝ)
    (cost : V → K → ℝ) (ψ : V → K → E) (μ : Measure V) (P : Measure K) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P] (fstar : V → ℝ) (gstar : K → ℝ) (fhat : (Fin r → V) × (Fin n → K) → Fin r → ℝ),
    BddCost ε cbar cost → 0 < n → 0 < r → Measurable (Function.uncurry ψ) → (∀ v x, ‖ψ v x‖ ≤ U) →
    IsSchrodingerPot ε cost μ P fstar gstar →
    (∀ ω, StatFormal.Wave24b.IsMaxDual ε (fun _ => (r : ℝ)⁻¹) (fun j => cost (ω.1 j))
      (StatFormal.Wave24b.empLaw ω.2) (fhat ω)) →
      (∀ ω : (Fin r → V) × (Fin n → K), Integrable (fun x =>
        ‖StatFormal.Wave24b.condMean ε (fun _ => (r : ℝ)⁻¹) (fhat ω) (fun j => cost (ω.1 j)) (fun j => ψ (ω.1 j)) x -
          ∫ v, schDens ε cost fstar gstar v x • ψ v x ∂μ‖ ^ 2) P) ∧
      Measurable (fun ω : (Fin r → V) × (Fin n → K) => ∫ x,
        ‖StatFormal.Wave24b.condMean ε (fun _ => (r : ℝ)⁻¹) (fhat ω) (fun j => cost (ω.1 j)) (fun j => ψ (ω.1 j)) x -
          ∫ v, schDens ε cost fstar gstar v x • ψ v x ∂μ‖ ^ 2 ∂P) ∧
      ∫⁻ ω, ENNReal.ofReal (∫ x,
        ‖StatFormal.Wave24b.condMean ε (fun _ => (r : ℝ)⁻¹) (fhat ω) (fun j => cost (ω.1 j)) (fun j => ψ (ω.1 j)) x -
          ∫ v, schDens ε cost fstar gstar v x • ψ v x ∂μ‖ ^ 2 ∂P)
          ∂((Measure.pi fun _ : Fin r => μ).prod (Measure.pi fun _ : Fin n => P)) ≤
        ENNReal.ofReal (22 * U ^ 2 * Real.exp (18 * cbar / ε) * (1 / n + 1 / r))

/-- G `thm:rates`, ranks and rank radius, with i.i.d. reference draws from any `μ` (continuity is not needed; labels
in the unit ball): `E ∫ ‖F̂ − F_ε‖² dP ≤ 22 e^{18c̄/ε}(1/n + 1/r)` and `E ∫ (‖F̂‖ − ‖F_ε‖)² dP ≤ 22 e^{18c̄/ε}(1/n + 1/r)`, the
errors `P`-integrable and measurable in the samples. -/
def rates_rank_two_sample : Prop :=
  ∀ (K V : Type) [MeasurableSpace K] [MeasurableSpace V] (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] (n r : ℕ) (ε cbar : ℝ)
    (cost : V → K → ℝ) (lab : V → E) (μ : Measure V) (P : Measure K) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P] (fstar : V → ℝ) (gstar : K → ℝ) (fhat : (Fin r → V) × (Fin n → K) → Fin r → ℝ),
    BddCost ε cbar cost → 0 < n → 0 < r → Measurable lab → (∀ v, ‖lab v‖ ≤ 1) →
    IsSchrodingerPot ε cost μ P fstar gstar →
    (∀ ω, StatFormal.Wave24b.IsMaxDual ε (fun _ => (r : ℝ)⁻¹) (fun j => cost (ω.1 j))
      (StatFormal.Wave24b.empLaw ω.2) (fhat ω)) →
      (∀ ω : (Fin r → V) × (Fin n → K), Integrable (fun x =>
        ‖StatFormal.Wave24b.condMean ε (fun _ => (r : ℝ)⁻¹) (fhat ω) (fun j => cost (ω.1 j))
            (fun j _ => lab (ω.1 j)) x - ∫ v, schDens ε cost fstar gstar v x • lab v ∂μ‖ ^ 2) P) ∧
      (∀ ω : (Fin r → V) × (Fin n → K), Integrable (fun x =>
        (‖StatFormal.Wave24b.condMean ε (fun _ => (r : ℝ)⁻¹) (fhat ω) (fun j => cost (ω.1 j))
            (fun j _ => lab (ω.1 j)) x‖ - ‖∫ v, schDens ε cost fstar gstar v x • lab v ∂μ‖) ^ 2) P) ∧
      Measurable (fun ω : (Fin r → V) × (Fin n → K) => ∫ x,
        ‖StatFormal.Wave24b.condMean ε (fun _ => (r : ℝ)⁻¹) (fhat ω) (fun j => cost (ω.1 j))
            (fun j _ => lab (ω.1 j)) x - ∫ v, schDens ε cost fstar gstar v x • lab v ∂μ‖ ^ 2 ∂P) ∧
      Measurable (fun ω : (Fin r → V) × (Fin n → K) => ∫ x,
        (‖StatFormal.Wave24b.condMean ε (fun _ => (r : ℝ)⁻¹) (fhat ω) (fun j => cost (ω.1 j))
            (fun j _ => lab (ω.1 j)) x‖ - ‖∫ v, schDens ε cost fstar gstar v x • lab v ∂μ‖) ^ 2 ∂P) ∧
      ∫⁻ ω, ENNReal.ofReal (∫ x,
        ‖StatFormal.Wave24b.condMean ε (fun _ => (r : ℝ)⁻¹) (fhat ω) (fun j => cost (ω.1 j))
            (fun j _ => lab (ω.1 j)) x - ∫ v, schDens ε cost fstar gstar v x • lab v ∂μ‖ ^ 2 ∂P)
          ∂((Measure.pi fun _ : Fin r => μ).prod (Measure.pi fun _ : Fin n => P)) ≤
        ENNReal.ofReal (22 * Real.exp (18 * cbar / ε) * (1 / n + 1 / r)) ∧
      ∫⁻ ω, ENNReal.ofReal (∫ x,
        (‖StatFormal.Wave24b.condMean ε (fun _ => (r : ℝ)⁻¹) (fhat ω) (fun j => cost (ω.1 j))
            (fun j _ => lab (ω.1 j)) x‖ - ‖∫ v, schDens ε cost fstar gstar v x • lab v ∂μ‖) ^ 2 ∂P)
          ∂((Measure.pi fun _ : Fin r => μ).prod (Measure.pi fun _ : Fin n => P)) ≤
        ENNReal.ofReal (22 * Real.exp (18 * cbar / ε) * (1 / n + 1 / r))

/-! #### otfd T `cor:randomised`: the Rigollet–Stromme premise -/

/-- T `cor:randomised` with the Rigollet–Stromme premises DISCHARGED: reference draws `U ∼ μ_K^N` and curves
`Z ∼ ν^n` independent, ANY empirical Schrödinger potentials `(f̂, ĝ)` of `(μ_N, ν_n)` (cost `0 ≤ c ≤ c̄`); under the
DKW–Massart bound for the reference radii, `E sup_ρ |P(‖U*‖ ≤ ρ | data) − c_K(ρ)| ≤
(4 e^{8c̄/ε}(e^{2c̄/ε} − 1)^{1/2} + (π/2)^{1/2})(n^{−1/2} + N^{−1/2})` (the frozen constant `2e^M A^{1/2} + (π/2)^{1/2}`
with `M = 2c̄/ε`, `A = 4e^{12c̄/ε}(e^{2c̄/ε} − 1)`). -/
def randomised_calibration_rs : Prop :=
  ∀ (K N n : ℕ) (Z : Type) [MeasurableSpace Z] (ν : Measure Z) (μK : Measure (EuclideanSpace ℝ (Fin K)))
    (c : EuclideanSpace ℝ (Fin K) → Z → ℝ) (ε cbar : ℝ) (fb : EuclideanSpace ℝ (Fin K) → ℝ) (gb : Z → ℝ)
    (fh : (Fin N → EuclideanSpace ℝ (Fin K)) × (Fin n → Z) → EuclideanSpace ℝ (Fin K) → ℝ)
    (gh : (Fin N → EuclideanSpace ℝ (Fin K)) × (Fin n → Z) → Z → ℝ),
    IsProbabilityMeasure ν → IsProbabilityMeasure μK → 0 < N → 0 < n → BddCost ε cbar c →
    IsSchrodingerPot ε c μK ν fb gb →
    (∀ ω, IsSchrodingerPot ε c (StatFormal.Wave24b.empLaw ω.1) (StatFormal.Wave24b.empLaw ω.2) (fh ω) (gh ω)) →
    ∫⁻ U, ⨆ ρ : ℝ, ENNReal.ofReal |StatFormal.Wave24c.empNormCDF U ρ -
        StatFormal.Wave23a.cdfK μK (fun u => ‖u‖) ρ| ∂(Measure.pi fun _ : Fin N => μK) ≤
      ENNReal.ofReal (Real.sqrt (Real.pi / (2 * N))) →
      ∫⁻ ω, ⨆ ρ : ℝ, ENNReal.ofReal |StatFormal.Wave24c.randCDF ν ε ω.1 (fun l => fh ω (ω.1 l)) (gh ω) c ρ -
          StatFormal.Wave23a.cdfK μK (fun u => ‖u‖) ρ|
          ∂((Measure.pi fun _ : Fin N => μK).prod (Measure.pi fun _ : Fin n => ν)) ≤
        ENNReal.ofReal ((4 * Real.exp (8 * cbar / ε) * Real.sqrt (Real.exp (2 * cbar / ε) - 1) +
          Real.sqrt (Real.pi / 2)) * (1 / Real.sqrt n + 1 / Real.sqrt N))

/-! #### otfd A `prop:curse` -/

/-- A `prop:curse`: for every `K`, coefficient and reference laws on the `ρ`-ball of `ℝ^K`, cost `‖u − z‖²`, `n` data
and `n` reference draws, any maximisers of the frozen semi-dual, `E ∫ ‖F̂ − F_{K,ε}‖² dP_K ≤ 4ρ² C(4ρ²/ε)/n` with
`C = curseC` (`C(t) = 11 e^{18t}`, a function of `t` alone); the error is `P_K`-integrable and measurable. -/
def curse_sampling : Prop :=
  ∀ (K n : ℕ) (ε ρ : ℝ) (P μ : Measure (Metric.closedBall (0 : EuclideanSpace ℝ (Fin K)) ρ))
    [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    (fstar gstar : Metric.closedBall (0 : EuclideanSpace ℝ (Fin K)) ρ → ℝ)
    (fhat : (Fin n → Metric.closedBall (0 : EuclideanSpace ℝ (Fin K)) ρ) ×
      (Fin n → Metric.closedBall (0 : EuclideanSpace ℝ (Fin K)) ρ) → Fin n → ℝ),
    0 < ε → 0 < n → IsSchrodingerPot ε sqCost μ P fstar gstar →
    (∀ ω, StatFormal.Wave24b.IsMaxDual ε (fun _ => (n : ℝ)⁻¹) (fun j => sqCost (ω.1 j))
      (StatFormal.Wave24b.empLaw ω.2) (fhat ω)) →
      (∀ ω : (Fin n → Metric.closedBall (0 : EuclideanSpace ℝ (Fin K)) ρ) ×
          (Fin n → Metric.closedBall (0 : EuclideanSpace ℝ (Fin K)) ρ),
        Integrable (fun z => ‖StatFormal.Wave24b.condMean ε (fun _ => (n : ℝ)⁻¹) (fhat ω) (fun j => sqCost (ω.1 j))
          (fun j _ => ((ω.1 j : Metric.closedBall (0 : EuclideanSpace ℝ (Fin K)) ρ) : EuclideanSpace ℝ (Fin K))) z -
        ∫ u, schDens ε sqCost fstar gstar u z • (u : EuclideanSpace ℝ (Fin K)) ∂μ‖ ^ 2) P) ∧
      Measurable (fun ω : (Fin n → Metric.closedBall (0 : EuclideanSpace ℝ (Fin K)) ρ) ×
          (Fin n → Metric.closedBall (0 : EuclideanSpace ℝ (Fin K)) ρ) =>
        ∫ z, ‖StatFormal.Wave24b.condMean ε (fun _ => (n : ℝ)⁻¹) (fhat ω) (fun j => sqCost (ω.1 j))
          (fun j _ => ((ω.1 j : Metric.closedBall (0 : EuclideanSpace ℝ (Fin K)) ρ) : EuclideanSpace ℝ (Fin K))) z -
        ∫ u, schDens ε sqCost fstar gstar u z • (u : EuclideanSpace ℝ (Fin K)) ∂μ‖ ^ 2 ∂P) ∧
      ∫⁻ ω, ENNReal.ofReal (∫ z, ‖StatFormal.Wave24b.condMean ε (fun _ => (n : ℝ)⁻¹) (fhat ω)
          (fun j => sqCost (ω.1 j))
          (fun j _ => ((ω.1 j : Metric.closedBall (0 : EuclideanSpace ℝ (Fin K)) ρ) : EuclideanSpace ℝ (Fin K))) z -
        ∫ u, schDens ε sqCost fstar gstar u z • (u : EuclideanSpace ℝ (Fin K)) ∂μ‖ ^ 2 ∂P)
          ∂((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => P)) ≤
        ENNReal.ofReal (4 * ρ ^ 2 * curseC (4 * ρ ^ 2 / ε) / n)

end Claims

end StatFormal.Wave26a
