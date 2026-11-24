import StatFormal.Archive.OTFD.Bands.Statements
import StatFormal.Archive.OTFD.Bands2.Statements
import StatFormal.Archive.OTFD.Wave2.Statements
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# FROZEN STATEMENTS — otfd wave 4: C `prop:conditional-certificate`, C `lem:neural-witness-ball`,
# G `prop:lipschitz`, G `prop:calibration`, T `lem:depthsign-rank`

Sources (verbatim in `lean-formalisation/inventory/extracted/otfd-C_conditional.md`, `otfd-G_geodesic.md`,
`otfd-T_tangent.md`; paths below are under `otfd/papers/`):
* C `prop:conditional-certificate` (`C_conditional/main.tex:533-554`), with `eq:oos` (`main.tex:286-295`), `eq:band`
  (`main.tex:300-304`), `eq:conditional-map` (`main.tex:393-397`) and `A_{K,p}` (`main.tex:271-276`).
* C `lem:neural-witness-ball` (`C_conditional/supplement.tex:2814-2824`; inventory line 2810), proof
  `supplement.tex:1226-1240`.
* G `prop:lipschitz` (`G_geodesic/main.tex:573-585`), with `eq:cost` (`main.tex:459-462`), the conditional laws
  `π_ε(dv|x)` (`main.tex:503-505`) and `def:ranks` (`main.tex:512-526`); proof `main.tex:586-601`.
* G `prop:calibration` (`G_geodesic/main.tex:612-626`, proof `:627-630`), with `def:reference` (`main.tex:323-331`).
* T `lem:depthsign-rank` (unlabelled in the inventory, `T_tangent/supp_toolkit.tex:153-159`, proof `:161-`).
Reuses the frozen `OTFD/Bands/Statements.lean` (`simplex`, `score`, `IsSimplexProj`), `OTFD/Bands2/Statements.lean`
(`edgeUp`, `edgeLo`, `curve`, `band`, `calInv`) and `OTFD/Wave2/Statements.lean` (`condA`, `condB`, `condGap`,
`condWitness`, `condMapEnt`, `entWeights`, `cappedSimplex`, `IsGreedyFill`), imported, not copied.

Covered:
* C `prop:conditional-certificate`: `cond_potential_ent`, `cond_potential_quad` (`T_x = ½∇ψ`, `ψ` convex, for either
  penalty); `cond_sup_attained_ent`, `cond_sup_attained_quad` (the band supremum is attained on `∂A`);
  `cond_validity_ent`, `cond_validity_quad` (the band event is measurable and has probability `≥ p`, simultaneously in
  `t`); `cond_gap_witness` (`eq:conditional-gap-witness`); `cond_caps_ent`, `cond_caps_quad` (the caps);
  `cond_outer_edges_ent`, `cond_outer_edges_quad` (the greedy fill of the capped simplex gives valid outer edges).
* C `lem:neural-witness-ball`: `neural_witness_ball` (`eq:neural-witness-bound`, pointwise on `S`).
* G `prop:lipschitz`: `lip_rank` (the displayed bound and `σ_ε ≤ 1`), `lip_rank_limsup`, `lip_rank_ball` (Lipschitz on
  `D`-balls around `m`), `lip_radial` (radial rank), `lip_cost` (transport cost).
* G `prop:calibration`: `cal_randomised` (a), `cal_condexp`, `cal_convex_order`, `cal_variance`, `cal_radial` (b),
  `cal_pit` (c).
* T `lem:depthsign-rank`: `depthsign_rank`, **without** the continuity hypothesis (see critic notes).

Not covered (declared):
* C: that the weights are the out-of-sample formula of a weighted transport solution (stage two, `eq:potential-tilt`);
  the retained set `I_x` is the index type `Fin n`; the saturation cap and the remarks after the proposition; the
  inner edge (Bands2 `inner_*`); that `A_{K,p}` is convex with `0` in its interior (only compactness is used).
* C `lem:neural-witness-ball`: the positivity `m_S(r) > 0`, which the paper asserts inside the definition of `m_S(r)` (it
  enters as the hypothesis that some real `m > 0` lower-bounds the ball masses); the sentence "for convergence, first let
  `n → ∞` …" of the proof.
* G `prop:lipschitz`: existence/uniqueness of `π_ε` and of its canonical potentials (`thm:wellposed`); the moment
  hypothesis `E D(m,X)² < ∞` enters only there (the claims hold for every Gibbs kernel, a generalisation); the
  geometric input is reduced to `D(m, E_m(sv)) ≤ s‖v‖`. The final sentence ("no smoothness … is used") is a remark.
* G `prop:calibration`: that the Gibbs kernel disintegrates `π_ε` (the kernel and the coupling enter as hypotheses);
  the Gaussian-direction construction of `def:reference` (only its consequence `‖V‖ ∼ Unif[0,1]` is used); the
  interpretive sentence "contracted towards the centre".
* T: "this holds under `ass:model`" (a separate item, see the ranking note).

Encodings (see card):
* C: `ℝ^K = Fin K → ℝ`; scores `s_i(u|x) = a_i(x) + 2⟨Z_i, u⟩` with the frozen `condA f Z`, `condB Z` (the query enters
  only through the potential `f = f(x)`). Entropic map: the frozen `condMapEnt`; quadratic map: `Σ_i q_i(u) Z_i` for any
  selection `q(u)` of the simplex projection of `s(u|x)/(γ/m)` (`IsQuadWeights`; the projection is unique, so this is
  the map). "Gradient of a convex potential": `ψ` convex, `2T(u)` a subgradient at every `u` (the frozen B encoding with
  `M = 1`), and `HasFDerivAt ψ ⟨2T(u), ·⟩ u`. `A_{K,p} = {u ∈ 𝒰 : g(u) ≤ c_K^{-1}(p)}` with `𝒰` compact, `μ_K(𝒰) = 1`,
  `g = ρ_{μ_K}` continuous, `c_K^{-1}` = frozen `calInv`, `0 < p ≤ 1` (as in Bands2). Band edges are the frozen
  `EReal` `edgeUp/edgeLo`; outer edges `Σ_i q_i[𝔪(t) + ⟨e(t), Z_i⟩]` at a greedy fill (frozen `IsGreedyFill`, threshold
  form of "filling caps in order"); verified gap lower bounds are any `δ̲_i ≤ δ_i(p|x)` (the paper's `[0, δ_i]`).
  `σ_A` in `L_i` is the frozen `condWitness` (`sSup`, no junk on compact nonempty `A`).
* C `lem:neural-witness-ball`: `ℝ^K = EuclideanSpace ℝ (Fin K)`, `μ_K` any measure; "closed `5r/4`-neighbourhood" =
  `Metric.cthickening`; `ω_Q` any modulus on it, nondecreasing on `[0,∞)`; `T` monotone on `O` = `⟨Tv − Tw, v − w⟩ ≥ 0`;
  `𝓡` enters as any real `R ≥ ∫⁻_O ‖T − Q‖²` (a lower integral, so no measurability or integrability is needed; if the
  integral is `∞` the claim is vacuous); `m` any real with `0 < m ≤ μ_K(B(u + re, r/4))` for all `u ∈ S`, `‖e‖ = 1`;
  `sup_{u∈S}` is stated pointwise. The `5r/4`-neighbourhood is assumed inside `O` (as printed); `int 𝒰_K` is unused.
* G: the curve space `(𝒳, D)` is any pseudometric space (`D = dist`), the tangent space `H_m` any separable real
  Hilbert space `H`, `μ` any probability on `H` with `‖v‖ ≤ 1` a.s.; `Em v = E_m(sv)` any measurable map with
  `D(m, Em v) ≤ s‖v‖`; cost `c_s(v,x) = ½ D(Em v, x)²` (`geoCost`). The conditional law is the Gibbs kernel
  `π_ε(dv|x) ∝ ρ(v) e^{−c_s(v,x)/ε} μ(dv)` with `ρ = e^{f/ε} ≥ 0` measurable, `μ`-integrable, `∫ρ dμ > 0` (`f = −∞`
  allowed); `∫ φ dπ_ε(·|x)` is written `(∫ w_x dμ)⁻¹ ∫ w_x φ dμ`, `w_x = ρ e^{−c_s(·,x)/ε}` (`gibbsInt`; the
  normaliser is shown positive, no junk). "limsup ≤ c" is the `∀ η > 0` neighbourhood form (no division by `D = 0`).
* G calibration: `(X, V)` (the paper's `(V, X)`) on a probability space; the conditional law is a Markov kernel
  `κ : 𝒳 → H` with `law(X, V) = law(X) ⊗ κ` and `(law(X) ⊗ κ).snd = μ` (this is `π_ε ∈ Π(μ, P)` with `κ` its
  disintegration); `F(x) = ∫ v dκ_x`, `σ(x)² = ∫ ‖v − F(x)‖² dκ_x`, `R(x) = ∫ ‖v‖ dκ_x`; `E[· | X]` is `condExp` for
  `σ(X)`; "the reference of `def:reference`" is `law(‖V‖) = Unif[0,1]` (`volume.restrict (Icc 0 1)`), the only
  property used; `G_ε` is Mathlib's `cdf` of `law(R(X))`. **Convex order: `φ` convex and continuous on the closed unit
  ball with `φ(V)` integrable** (the printed "every convex `φ`" is ill-posed on an infinite-dimensional `H_m`, see the
  critic notes); integrability of `φ(F(X))` is part of the conclusion. For the radial rank, `ψ` convex and continuous on
  `[0,1]`.
* T: `ℝ^K` generalised to any normed space `E` with Borel σ-algebra; `c_K(ρ) = μ_K{‖u‖ ≤ ρ}` is Mathlib's `cdf` of the
  law of `‖U‖` (a CDF on `ℝ`); "`U'/‖U'‖ = U/‖U‖`, any convention at the origin" is `sgn U' = sgn U` a.s. for any
  `sgn` with `sgn u = ‖u‖⁻¹ u` for `u ≠ 0`.
Critic notes:
* T: the continuity hypothesis is not needed: for **every** law, `c_K(‖U'‖) = c_K(‖U‖)` a.s. forces `‖U'‖ = ‖U‖` a.s.
  (the quantile of the CDF is the identity a.e., Tau Ceti `quantile_cdf_ae`), so `depthsign_rank` drops it (a
  generalisation, which covers the paper's statement). The manuscript proof was corrected on 2026-10-14 to handle an
  atom at 0 (`supp_toolkit.tex:161`); continuity is now simply unnecessary.
* G `cal_convex_order`: as printed ("every convex `φ`", general `μ`) the claim is **false** on infinite-dimensional
  `H_m`, even when every expectation exists: `P = δ_x`, `μ = Σ 2⁻ⁿ δ_{e_n}` (orthonormal `e_n`), so `F(X) = E V =
  Σ 2⁻ⁿ e_n ∉ span{e_n}`; a Hamel-basis linear `φ` with `φ(e_n) = 0`, `φ(E V) = 1` gives `E φ(F(X)) = 1 > 0 = E φ(V)`.
  (Finite-rank `μ`, e.g. the default rank-`K` reference, is saved by finite-dimensional Jensen.) Continuity on the
  ball (lower semicontinuity would also do) and integrability of `φ(V)` are added — the standard convex-order convention.
* G calibration: the kernel `κ` is arbitrary (any disintegration with the stated marginals); it is not tied to
  `gRank`/`gibbsInt`, so these claims cover the paper's `π_ε` as an instance.
* G `lip_rank_ball`: holds in every pseudometric space, without the geodesics of `lem:polish` used for chaining in the
  printed proof (`‖F_ε‖ ≤ 1` handles large distances).
* C `neural_witness_ball`: the constant `5/3` is exact as printed.
* G `cal_pit` holds for every Markov kernel (no ball hypothesis is needed); under the ball hypothesis of the other
  calibration claims `R(x)` is the genuine radial rank for `law(X)`-a.e. `x`.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

noncomputable section
open Finset Matrix MeasureTheory ProbabilityTheory Set
open scoped InnerProductSpace ENNReal

namespace StatFormal.OTFD.Wave4

open StatFormal.OTFD.Bands StatFormal.OTFD.Bands2 StatFormal.OTFD.Wave2

variable {n K : ℕ}

/-! ### C `prop:conditional-certificate` -/

/-- Quadratic conditional map `T_x(u) = Σ_i q_i(u|x) Z_i` for a weight selection `q`. -/
def condMapQuad (q : (Fin K → ℝ) → Fin n → ℝ) (Z : Fin n → Fin K → ℝ) (u : Fin K → ℝ) : Fin K → ℝ :=
  ∑ i, q u i • Z i

/-- `q(u) = P_△(s(u|x)/(γ/m))` for every `u` (quadratic weights of `eq:oos`). -/
def IsQuadWeights (γ : ℝ) (m : ℕ) (f : Fin n → ℝ) (Z : Fin n → Fin K → ℝ)
    (q : (Fin K → ℝ) → Fin n → ℝ) : Prop :=
  ∀ u, IsSimplexProj (fun k => score (condA f Z) (condB Z) k u / (γ / m)) (q u)

/-- The linear functional `y ↦ ⟨g, y⟩` as a continuous linear map (the derivative of a potential with gradient `g`). -/
def dotCLM (g : Fin K → ℝ) : (Fin K → ℝ) →L[ℝ] ℝ :=
  ∑ k, g k • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin K => ℝ) k

/-- `T = ½∇ψ` with `ψ` convex: convexity, the subgradient inequality `ψ(y) ≥ ψ(u) + ⟨2T(u), y − u⟩`, and
differentiability with gradient `2T(u)` at every `u`. -/
def IsHalfGradPotential (ψ : (Fin K → ℝ) → ℝ) (T : (Fin K → ℝ) → Fin K → ℝ) : Prop :=
  ConvexOn ℝ Set.univ ψ ∧ (∀ u y, ψ u + (2 • T u) ⬝ᵥ (y - u) ≤ ψ y) ∧
    ∀ u, HasFDerivAt ψ (dotCLM (2 • T u)) u

/-- The level-`p` region `A_{K,p} = {u ∈ 𝒰 : g(u) ≤ c_K^{-1}(p)}`. -/
def condRegion (μ : Measure (Fin K → ℝ)) (g : (Fin K → ℝ) → ℝ) (𝒰 : Set (Fin K → ℝ)) (p : ℝ) :
    Set (Fin K → ℝ) :=
  {u | u ∈ 𝒰 ∧ g u ≤ calInv μ g p}

/-- The band event of `eq:band`: the reconstruction of `T(U)` lies in `B̂(A)` for every `t`. -/
def bandEvent {Ω 𝒯 : Type} (T : (Fin K → ℝ) → Fin K → ℝ) (A : Set (Fin K → ℝ)) (mo : 𝒯 → ℝ)
    (e : 𝒯 → Fin K → ℝ) (U : Ω → Fin K → ℝ) : Set Ω :=
  {ω | curve mo e (T (U ω)) ∈ band (fun t => edgeLo T A (mo t) (e t)) (fun t => edgeUp T A (mo t) (e t))}

/-! ### G `prop:lipschitz`, `prop:calibration` -/

section Geodesic

variable {H 𝒳 E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [PseudoMetricSpace 𝒳] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `c_s(v, x) = ½ D(E_m(sv), x)²` with `Em v = E_m(sv)`. -/
def geoCost (Em : H → 𝒳) (v : H) (x : 𝒳) : ℝ := dist (Em v) x ^ 2 / 2

/-- Unnormalised Gibbs weight `w_x(v) = ρ(v) e^{−c_s(v,x)/ε}` (`ρ = e^{f/ε}`). -/
def gibbsW (ρ : H → ℝ) (Em : H → 𝒳) (ε : ℝ) (x : 𝒳) (v : H) : ℝ :=
  ρ v * Real.exp (-geoCost Em v x / ε)

/-- `∫ φ dπ_ε(·|x) = (∫ w_x dμ)⁻¹ ∫ w_x φ dμ`. -/
def gibbsInt (μ : Measure H) (ρ : H → ℝ) (Em : H → 𝒳) (ε : ℝ) (φ : H → E) (x : 𝒳) : E :=
  (∫ v, gibbsW ρ Em ε x v ∂μ)⁻¹ • ∫ v, gibbsW ρ Em ε x v • φ v ∂μ

/-- Rank `F_ε(x) = ∫ v π_ε(dv|x)`. -/
def gRank (μ : Measure H) (ρ : H → ℝ) (Em : H → 𝒳) (ε : ℝ) (x : 𝒳) : H :=
  gibbsInt μ ρ Em ε id x

/-- Conditional spread `σ_ε(x) = (∫ ‖v − F_ε(x)‖² π_ε(dv|x))^{1/2}`. -/
def gSpread (μ : Measure H) (ρ : H → ℝ) (Em : H → 𝒳) (ε : ℝ) (x : 𝒳) : ℝ :=
  Real.sqrt (gibbsInt μ ρ Em ε (fun v => ‖v - gRank μ ρ Em ε x‖ ^ 2) x)

/-- Radial rank `R_ε(x) = ∫ ‖v‖ π_ε(dv|x)`. -/
def gRadial (μ : Measure H) (ρ : H → ℝ) (Em : H → 𝒳) (ε : ℝ) (x : 𝒳) : ℝ :=
  gibbsInt μ ρ Em ε (fun v => ‖v‖) x

/-- Conditional standard deviation of `‖V‖`. -/
def gRadialSpread (μ : Measure H) (ρ : H → ℝ) (Em : H → 𝒳) (ε : ℝ) (x : 𝒳) : ℝ :=
  Real.sqrt (gibbsInt μ ρ Em ε (fun v => (‖v‖ - gRadial μ ρ Em ε x) ^ 2) x)

/-- Transport cost `κ_ε(x) = ∫ c_s(v,x) π_ε(dv|x)`. -/
def gCost (μ : Measure H) (ρ : H → ℝ) (Em : H → 𝒳) (ε : ℝ) (x : 𝒳) : ℝ :=
  (∫ v, gibbsW ρ Em ε x v ∂μ)⁻¹ * ∫ v, gibbsW ρ Em ε x v * geoCost Em v x ∂μ

/-- Standing hypotheses of `prop:lipschitz` (see the encodings). -/
def GibbsHyp [MeasurableSpace 𝒳] (μ : Measure H) (ρ : H → ℝ) (Em : H → 𝒳) (m : 𝒳) (s ε : ℝ) : Prop :=
  Measurable ρ ∧ (∀ v, 0 ≤ ρ v) ∧ Integrable ρ μ ∧ 0 < ∫ v, ρ v ∂μ ∧ Measurable Em ∧ 0 ≤ s ∧
    (∀ v, dist m (Em v) ≤ s * ‖v‖) ∧ (∀ᵐ v ∂μ, ‖v‖ ≤ 1) ∧ 0 < ε

/-- Kernel rank `F(x) = ∫ v κ_x(dv)`. -/
def kRank [MeasurableSpace 𝒳] (κ : Kernel 𝒳 H) (x : 𝒳) : H := ∫ v, v ∂κ x

/-- Kernel spread `σ(x)² = ∫ ‖v − F(x)‖² κ_x(dv)`. -/
def kSpreadSq [MeasurableSpace 𝒳] (κ : Kernel 𝒳 H) (x : 𝒳) : ℝ := ∫ v, ‖v - kRank κ x‖ ^ 2 ∂κ x

/-- Kernel radial rank `R(x) = ∫ ‖v‖ κ_x(dv)`. -/
def kRadial [MeasurableSpace 𝒳] (κ : Kernel 𝒳 H) (x : 𝒳) : ℝ := ∫ v, ‖v‖ ∂κ x

end Geodesic

namespace Claims

/-! ### C `prop:conditional-certificate` -/

/-- Entropic `T_x` is half the gradient of a convex potential. -/
def cond_potential_ent : Prop :=
  ∀ (n K : ℕ) (ε : ℝ) (f : Fin n → ℝ) (Z : Fin n → Fin K → ℝ),
    0 < n → 0 < ε → ∃ ψ : (Fin K → ℝ) → ℝ, IsHalfGradPotential ψ (condMapEnt ε f Z)

/-- Quadratic `T_x` is half the gradient of a convex potential. -/
def cond_potential_quad : Prop :=
  ∀ (n K m : ℕ) (γ : ℝ) (f : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) (q : (Fin K → ℝ) → Fin n → ℝ),
    0 < γ → 0 < m → IsQuadWeights γ m f Z q →
      ∃ ψ : (Fin K → ℝ) → ℝ, IsHalfGradPotential ψ (condMapQuad q Z)

/-- Entropic: on a nonempty compact `A ⊆ ℝ^K`, `K ≥ 1`, `sup_{u∈A} ⟨v, T_x(u)⟩` is attained at a point of `∂A`. -/
def cond_sup_attained_ent : Prop :=
  ∀ (n K : ℕ) (ε : ℝ) (f : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) (A : Set (Fin K → ℝ)) (v : Fin K → ℝ),
    0 < n → 0 < K → 0 < ε → IsCompact A → A.Nonempty →
      ∃ u' ∈ frontier A, ∀ u ∈ A, v ⬝ᵥ condMapEnt ε f Z u ≤ v ⬝ᵥ condMapEnt ε f Z u'

/-- Quadratic: the band supremum is attained on `∂A`. -/
def cond_sup_attained_quad : Prop :=
  ∀ (n K m : ℕ) (γ : ℝ) (f : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) (q : (Fin K → ℝ) → Fin n → ℝ)
    (A : Set (Fin K → ℝ)) (v : Fin K → ℝ),
    0 < K → 0 < γ → 0 < m → IsQuadWeights γ m f Z q → IsCompact A → A.Nonempty →
      ∃ u' ∈ frontier A, ∀ u ∈ A, v ⬝ᵥ condMapQuad q Z u ≤ v ⬝ᵥ condMapQuad q Z u'

/-- Entropic fitted-law validity: for `U ∼ μ_K`, the band event of `A_{K,p}` is measurable and has probability
`≥ p`, simultaneously in `t`. -/
def cond_validity_ent : Prop :=
  ∀ (n K : ℕ) (𝒯 Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (ε : ℝ)
    (f : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) (U : Ω → Fin K → ℝ) (g : (Fin K → ℝ) → ℝ)
    (𝒰 : Set (Fin K → ℝ)) (p : ℝ) (mo : 𝒯 → ℝ) (e : 𝒯 → Fin K → ℝ),
    0 < n → 0 < ε → Measurable U → Continuous g → IsCompact 𝒰 → P.map U 𝒰 = 1 → 0 < p → p ≤ 1 →
      MeasurableSet (bandEvent (condMapEnt ε f Z) (condRegion (P.map U) g 𝒰 p) mo e U) ∧
      ENNReal.ofReal p ≤ P (bandEvent (condMapEnt ε f Z) (condRegion (P.map U) g 𝒰 p) mo e U)

/-- Quadratic fitted-law validity. -/
def cond_validity_quad : Prop :=
  ∀ (n K m : ℕ) (𝒯 Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (γ : ℝ)
    (f : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) (q : (Fin K → ℝ) → Fin n → ℝ) (U : Ω → Fin K → ℝ)
    (g : (Fin K → ℝ) → ℝ) (𝒰 : Set (Fin K → ℝ)) (p : ℝ) (mo : 𝒯 → ℝ) (e : 𝒯 → Fin K → ℝ),
    0 < γ → 0 < m → IsQuadWeights γ m f Z q → Measurable U → Continuous g → IsCompact 𝒰 →
    P.map U 𝒰 = 1 → 0 < p → p ≤ 1 →
      MeasurableSet (bandEvent (condMapQuad q Z) (condRegion (P.map U) g 𝒰 p) mo e U) ∧
      ENNReal.ofReal p ≤ P (bandEvent (condMapQuad q Z) (condRegion (P.map U) g 𝒰 p) mo e U)

/-- `eq:conditional-gap-witness`: `δ_i(p|x) ≥ L_i(ω, x)` for every `ω` in the simplex. -/
def cond_gap_witness : Prop :=
  ∀ (n K : ℕ) (f : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) (A : Set (Fin K → ℝ)) (ω : Fin n → ℝ) (i : Fin n),
    IsCompact A → A.Nonempty → ω ∈ simplex n → condWitness f Z A ω i ≤ condGap f Z A i

/-- Entropic caps: for `u ∈ A` and verified `δ̲_i ≤ δ_i(p|x)`, `q(u|x) ∈ 𝒫_κ`, `κ_i = e^{−δ̲_i/ε}`. -/
def cond_caps_ent : Prop :=
  ∀ (n K : ℕ) (ε : ℝ) (f : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) (A : Set (Fin K → ℝ)) (δlow : Fin n → ℝ)
    (u : Fin K → ℝ),
    0 < n → 0 < ε → u ∈ A → (∀ i, δlow i ≤ condGap f Z A i) →
      entWeights (condA f Z) (condB Z) ε u ∈ cappedSimplex (fun i => Real.exp (-δlow i / ε))

/-- Quadratic caps: `q(u|x) ∈ 𝒫_κ`, `κ_i = (1 − δ̲_i/(γ/m))_+`. -/
def cond_caps_quad : Prop :=
  ∀ (n K m : ℕ) (γ : ℝ) (f : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) (q : (Fin K → ℝ) → Fin n → ℝ)
    (A : Set (Fin K → ℝ)) (δlow : Fin n → ℝ) (u : Fin K → ℝ),
    0 < γ → 0 < m → IsQuadWeights γ m f Z q → u ∈ A → (∀ i, δlow i ≤ condGap f Z A i) →
      q u ∈ cappedSimplex (fun i => max 0 (1 - δlow i / (γ / m)))

/-- Entropic outer edges: greedy fills `q⁺` (values `c_i = 𝔪 + ⟨v, Z_i⟩`) and `q⁻` (values `−c`) of the capped
simplex give `x̂↑ ≤ Σ q⁺_i c_i` and `Σ q⁻_i c_i ≤ x̂↓`. -/
def cond_outer_edges_ent : Prop :=
  ∀ (n K : ℕ) (ε : ℝ) (f : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) (A : Set (Fin K → ℝ)) (δlow : Fin n → ℝ)
    (mo : ℝ) (v : Fin K → ℝ) (qhi qlo : Fin n → ℝ),
    0 < n → 0 < ε → (∀ i, δlow i ≤ condGap f Z A i) →
    IsGreedyFill (fun i => Real.exp (-δlow i / ε)) (fun i => mo + v ⬝ᵥ Z i) qhi →
    IsGreedyFill (fun i => Real.exp (-δlow i / ε)) (fun i => -(mo + v ⬝ᵥ Z i)) qlo →
      edgeUp (condMapEnt ε f Z) A mo v ≤ ((∑ i, qhi i * (mo + v ⬝ᵥ Z i) : ℝ) : EReal) ∧
      ((∑ i, qlo i * (mo + v ⬝ᵥ Z i) : ℝ) : EReal) ≤ edgeLo (condMapEnt ε f Z) A mo v

/-- Quadratic outer edges. -/
def cond_outer_edges_quad : Prop :=
  ∀ (n K m : ℕ) (γ : ℝ) (f : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) (q : (Fin K → ℝ) → Fin n → ℝ)
    (A : Set (Fin K → ℝ)) (δlow : Fin n → ℝ) (mo : ℝ) (v : Fin K → ℝ) (qhi qlo : Fin n → ℝ),
    0 < γ → 0 < m → IsQuadWeights γ m f Z q → (∀ i, δlow i ≤ condGap f Z A i) →
    IsGreedyFill (fun i => max 0 (1 - δlow i / (γ / m))) (fun i => mo + v ⬝ᵥ Z i) qhi →
    IsGreedyFill (fun i => max 0 (1 - δlow i / (γ / m))) (fun i => -(mo + v ⬝ᵥ Z i)) qlo →
      edgeUp (condMapQuad q Z) A mo v ≤ ((∑ i, qhi i * (mo + v ⬝ᵥ Z i) : ℝ) : EReal) ∧
      ((∑ i, qlo i * (mo + v ⬝ᵥ Z i) : ℝ) : EReal) ≤ edgeLo (condMapQuad q Z) A mo v

/-! ### C `lem:neural-witness-ball` -/

/-- `sup_{u∈S} ‖T(u) − Q(u)‖ ≤ (5/3){ω_Q(5r/4) + √(𝓡/m_S(r))}`. -/
def neural_witness_ball : Prop :=
  ∀ (K : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin K))) (S O : Set (EuclideanSpace ℝ (Fin K)))
    (T Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (ω : ℝ → ℝ) (r m R : ℝ),
    IsCompact S → IsOpen O → S ⊆ O → ContinuousOn Q O →
    (∀ v ∈ O, ∀ w ∈ O, 0 ≤ ⟪T v - T w, v - w⟫_ℝ) →
    0 < r → Metric.cthickening (5 * r / 4) S ⊆ O → MonotoneOn ω (Set.Ici 0) →
    (∀ x ∈ Metric.cthickening (5 * r / 4) S, ∀ y ∈ Metric.cthickening (5 * r / 4) S,
      ‖Q x - Q y‖ ≤ ω ‖x - y‖) →
    0 < m → (∀ u ∈ S, ∀ e : EuclideanSpace ℝ (Fin K), ‖e‖ = 1 →
      ENNReal.ofReal m ≤ μ (Metric.ball (u + r • e) (r / 4))) →
    (∫⁻ u in O, ENNReal.ofReal (‖T u - Q u‖ ^ 2) ∂μ) ≤ ENNReal.ofReal R →
      ∀ u ∈ S, ‖T u - Q u‖ ≤ 5 / 3 * (ω (5 * r / 4) + Real.sqrt (R / m))

/-! ### G `prop:lipschitz` -/

/-- `‖F_ε(x) − F_ε(x')‖ ≤ σ_ε(x)(e^{2L D(x,x')/ε} − 1)`, `L = s + ½(D(m,x) + D(m,x'))`, and `σ_ε(x) ≤ 1`. -/
def lip_rank : Prop :=
  ∀ (H 𝒳 : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    [BorelSpace H] [SecondCountableTopology H] [PseudoMetricSpace 𝒳] [MeasurableSpace 𝒳]
    [OpensMeasurableSpace 𝒳] (μ : Measure H) [IsProbabilityMeasure μ] (ρ : H → ℝ) (Em : H → 𝒳) (m : 𝒳)
    (s ε : ℝ),
    GibbsHyp μ ρ Em m s ε → ∀ x x' : 𝒳,
      ‖gRank μ ρ Em ε x - gRank μ ρ Em ε x'‖ ≤
        gSpread μ ρ Em ε x *
          (Real.exp (2 * (s + (dist m x + dist m x') / 2) * dist x x' / ε) - 1) ∧
      gSpread μ ρ Em ε x ≤ 1

/-- `limsup_{x'→x} ‖F_ε(x) − F_ε(x')‖ / D(x,x') ≤ 2Lσ_ε(x)/ε` with `L = s + D(m,x)`. -/
def lip_rank_limsup : Prop :=
  ∀ (H 𝒳 : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    [BorelSpace H] [SecondCountableTopology H] [PseudoMetricSpace 𝒳] [MeasurableSpace 𝒳]
    [OpensMeasurableSpace 𝒳] (μ : Measure H) [IsProbabilityMeasure μ] (ρ : H → ℝ) (Em : H → 𝒳) (m : 𝒳)
    (s ε : ℝ),
    GibbsHyp μ ρ Em m s ε → ∀ (x : 𝒳) (η : ℝ), 0 < η → ∃ δ > 0, ∀ x' : 𝒳, dist x x' < δ →
      ‖gRank μ ρ Em ε x - gRank μ ρ Em ε x'‖ ≤
        (2 * (s + dist m x) * gSpread μ ρ Em ε x / ε + η) * dist x x'

/-- `F_ε` is Lipschitz on every `D`-ball around `m`. -/
def lip_rank_ball : Prop :=
  ∀ (H 𝒳 : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    [BorelSpace H] [SecondCountableTopology H] [PseudoMetricSpace 𝒳] [MeasurableSpace 𝒳]
    [OpensMeasurableSpace 𝒳] (μ : Measure H) [IsProbabilityMeasure μ] (ρ : H → ℝ) (Em : H → 𝒳) (m : 𝒳)
    (s ε : ℝ),
    GibbsHyp μ ρ Em m s ε → ∀ r : ℝ, ∃ C : ℝ, ∀ x x' : 𝒳, dist m x ≤ r → dist m x' ≤ r →
      ‖gRank μ ρ Em ε x - gRank μ ρ Em ε x'‖ ≤ C * dist x x'

/-- The same bound for the radial rank, with the conditional standard deviation of `‖V‖`. -/
def lip_radial : Prop :=
  ∀ (H 𝒳 : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    [BorelSpace H] [SecondCountableTopology H] [PseudoMetricSpace 𝒳] [MeasurableSpace 𝒳]
    [OpensMeasurableSpace 𝒳] (μ : Measure H) [IsProbabilityMeasure μ] (ρ : H → ℝ) (Em : H → 𝒳) (m : 𝒳)
    (s ε : ℝ),
    GibbsHyp μ ρ Em m s ε → ∀ x x' : 𝒳,
      |gRadial μ ρ Em ε x - gRadial μ ρ Em ε x'| ≤
        gRadialSpread μ ρ Em ε x *
          (Real.exp (2 * (s + (dist m x + dist m x') / 2) * dist x x' / ε) - 1)

/-- `|κ_ε(x) − κ_ε(x')| ≤ L D(x,x') + ½(s + D(m,x))²(e^{2L D(x,x')/ε} − 1)`. -/
def lip_cost : Prop :=
  ∀ (H 𝒳 : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    [BorelSpace H] [SecondCountableTopology H] [PseudoMetricSpace 𝒳] [MeasurableSpace 𝒳]
    [OpensMeasurableSpace 𝒳] (μ : Measure H) [IsProbabilityMeasure μ] (ρ : H → ℝ) (Em : H → 𝒳) (m : 𝒳)
    (s ε : ℝ),
    GibbsHyp μ ρ Em m s ε → ∀ x x' : 𝒳,
      |gCost μ ρ Em ε x - gCost μ ρ Em ε x'| ≤
        (s + (dist m x + dist m x') / 2) * dist x x' +
          (s + dist m x) ^ 2 / 2 *
            (Real.exp (2 * (s + (dist m x + dist m x') / 2) * dist x x' / ε) - 1)

/-! ### G `prop:calibration` -/

/-- (a) The randomised rank `V ∼ κ_X` has law `μ`; with `‖V‖ ∼ Unif[0,1]` under `μ`, `1 − ‖V‖ ∼ Unif[0,1]`. -/
def cal_randomised : Prop :=
  ∀ (H 𝒳 Ω : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace 𝒳] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure H)
    (κ : Kernel 𝒳 H) [IsMarkovKernel κ] (X : Ω → 𝒳) (V : Ω → H),
    Measurable X → Measurable V → P.map (fun ω => (X ω, V ω)) = (P.map X) ⊗ₘ κ →
    ((P.map X) ⊗ₘ κ).snd = μ →
      P.map V = μ ∧
      (μ.map (fun v => ‖v‖) = volume.restrict (Icc (0 : ℝ) 1) →
        P.map (fun ω => 1 - ‖V ω‖) = volume.restrict (Icc (0 : ℝ) 1))

/-- (b) `F(X) = E[V | X]` and `R(X) = E[‖V‖ | X]` a.s. -/
def cal_condexp : Prop :=
  ∀ (H 𝒳 Ω : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    [BorelSpace H] [SecondCountableTopology H] [MeasurableSpace 𝒳] [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (μ : Measure H) (κ : Kernel 𝒳 H) [IsMarkovKernel κ] (X : Ω → 𝒳) (V : Ω → H),
    Measurable X → Measurable V → P.map (fun ω => (X ω, V ω)) = (P.map X) ⊗ₘ κ →
    ((P.map X) ⊗ₘ κ).snd = μ → (∀ᵐ v ∂μ, ‖v‖ ≤ 1) →
      (fun ω => kRank κ (X ω)) =ᵐ[P] P[V | MeasurableSpace.comap X inferInstance] ∧
      (fun ω => kRadial κ (X ω)) =ᵐ[P] P[fun ω => ‖V ω‖ | MeasurableSpace.comap X inferInstance]

/-- (b) Convex order: `E φ(F(X)) ≤ E φ(V)` for `φ` convex and continuous on the closed unit ball with `φ(V)`
integrable (and `φ(F(X))` is integrable). -/
def cal_convex_order : Prop :=
  ∀ (H 𝒳 Ω : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    [BorelSpace H] [SecondCountableTopology H] [MeasurableSpace 𝒳] [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (μ : Measure H) (κ : Kernel 𝒳 H) [IsMarkovKernel κ] (X : Ω → 𝒳) (V : Ω → H)
    (φ : H → ℝ),
    Measurable X → Measurable V → P.map (fun ω => (X ω, V ω)) = (P.map X) ⊗ₘ κ →
    ((P.map X) ⊗ₘ κ).snd = μ → (∀ᵐ v ∂μ, ‖v‖ ≤ 1) →
    ConvexOn ℝ (Metric.closedBall 0 1) φ → ContinuousOn φ (Metric.closedBall 0 1) →
    Integrable (fun ω => φ (V ω)) P →
      Integrable (fun ω => φ (kRank κ (X ω))) P ∧
      ∫ ω, φ (kRank κ (X ω)) ∂P ≤ ∫ ω, φ (V ω) ∂P

/-- (b) `E‖F(X)‖² = E‖V‖² − E σ(X)²`. -/
def cal_variance : Prop :=
  ∀ (H 𝒳 Ω : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    [BorelSpace H] [SecondCountableTopology H] [MeasurableSpace 𝒳] [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (μ : Measure H) (κ : Kernel 𝒳 H) [IsMarkovKernel κ] (X : Ω → 𝒳) (V : Ω → H),
    Measurable X → Measurable V → P.map (fun ω => (X ω, V ω)) = (P.map X) ⊗ₘ κ →
    ((P.map X) ⊗ₘ κ).snd = μ → (∀ᵐ v ∂μ, ‖v‖ ≤ 1) →
      ∫ ω, ‖kRank κ (X ω)‖ ^ 2 ∂P = ∫ ω, ‖V ω‖ ^ 2 ∂P - ∫ ω, kSpreadSq κ (X ω) ∂P

/-- (b) With `‖V‖ ∼ Unif[0,1]`: `E R(X) = 1/2`, and `E ψ(R(X)) ≤ ∫₀¹ ψ` for `ψ` convex and continuous on `[0,1]`. -/
def cal_radial : Prop :=
  ∀ (H 𝒳 Ω : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    [BorelSpace H] [SecondCountableTopology H] [MeasurableSpace 𝒳] [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (μ : Measure H) (κ : Kernel 𝒳 H) [IsMarkovKernel κ] (X : Ω → 𝒳) (V : Ω → H),
    Measurable X → Measurable V → P.map (fun ω => (X ω, V ω)) = (P.map X) ⊗ₘ κ →
    ((P.map X) ⊗ₘ κ).snd = μ → μ.map (fun v => ‖v‖) = volume.restrict (Icc (0 : ℝ) 1) →
      ∫ ω, kRadial κ (X ω) ∂P = 1 / 2 ∧
      ∀ ψ : ℝ → ℝ, ConvexOn ℝ (Icc 0 1) ψ → ContinuousOn ψ (Icc 0 1) →
        Integrable (fun ω => ψ (kRadial κ (X ω))) P ∧
        ∫ ω, ψ (kRadial κ (X ω)) ∂P ≤ ∫ t in Icc (0 : ℝ) 1, ψ t

/-- (c) If `G = cdf(law R(X))` is continuous, `D^cal(X) = 1 − G(R(X)) ∼ Unif[0,1]`. -/
def cal_pit : Prop :=
  ∀ (H 𝒳 Ω : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    [BorelSpace H] [SecondCountableTopology H] [MeasurableSpace 𝒳] [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (κ : Kernel 𝒳 H) [IsMarkovKernel κ] (X : Ω → 𝒳),
    Measurable X → Continuous (cdf (P.map (fun ω => kRadial κ (X ω)))) →
      P.map (fun ω => 1 - cdf (P.map (fun ω => kRadial κ (X ω))) (kRadial κ (X ω))) =
        volume.restrict (Icc (0 : ℝ) 1)

/-! ### T `lem:depthsign-rank` -/

/-- If `U, U' ∼ μ_K` (any coupling), `c_K(‖U'‖) = c_K(‖U‖)` and `sgn U' = sgn U` a.s., then `U' = U` a.s. -/
def depthsign_rank : Prop :=
  ∀ (E Ω : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure E) [IsProbabilityMeasure μ]
    (U U' : Ω → E) (sgn : E → E),
    Measurable U → Measurable U' → P.map U = μ → P.map U' = μ →
    (∀ u, u ≠ 0 → sgn u = ‖u‖⁻¹ • u) →
    (∀ᵐ ω ∂P, cdf (μ.map (fun u => ‖u‖)) ‖U' ω‖ = cdf (μ.map (fun u => ‖u‖)) ‖U ω‖) →
    (∀ᵐ ω ∂P, sgn (U' ω) = sgn (U ω)) →
      ∀ᵐ ω ∂P, U' ω = U ω

end Claims
end StatFormal.OTFD.Wave4
