import StatFormal.Archive.Wave23a.Statements
import StatFormal.Archive.Wave20a.Statements
import StatFormal.Archive.RobustEquality.Paper2.Alternating.Statements
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# FROZEN STATEMENTS — wave 28e: SB `prop:sbbary` (minimisation over all of `𝒫₂(ℝ)`); paper 2 `prop:jointmin`
# (anisotropic sets on an unbounded `K`, structured sets with a finite cell cover)

Sources (current text, read 2026-10-17; paths under `~/pCloudDrive/research-lines/`):
* SB `prop:sbbary` (`data-fairness-repair/schrodinger_bridge_fairness_repair.tex:2255-2273`, proof `:2876-2916`), with
  `eq:static` (`:385-392`: `𝒞_ε(μ,ν) = min_{π ∈ Π(μ,ν)} {½∫|x−y|² dπ − ε Ent(π)}`, `Ent(π) = −∫ π log π` the
  differential entropy), `eq:sbbary` (`:2205`) and `eq:ceps` (`lem:gaussplan`, `:2222-2236`). The scalar layer (root
  uniqueness, zero root, monotonicity, limits) is frozen in Wave 23a (`sbbary_*`); missing there: "the minimiser of
  `eq:sbbary` over all of `𝒫₂(ℝ)` is `N(a⋆, τ_ε²)`, `a⋆ = Σ_s p_s a_s`" (card wave23a.md).
* paper 2 `prop:jointmin` (`robust-equality-outcomes-under-distribution-shift/paper2/main.tex:305-313`, proof
  `app_proofs.tex:47-57`), with the anisotropic sets (`main.tex:230-232`), the structured sets and `eq:F`
  (`:234-243`), `eq:T` read at `ε = 0` (`:244-252`), `thm:certificate` and its proof (`:254-261`, `app_proofs.tex:14-31`:
  "For an anisotropic set the same argument holds with `c` replaced by `c_M` … For a linear rule and `K = ℝ^d`
  every quantity above is finite"), `eq:problems` (`:276-282`), `lem:delta-inf` (`:296-303`) and `prop:structured`
  (`:361-377`). The case `ε = 0` with a reference support is frozen in Wave P2d (`jointmin_upper0`, `jointmin_inf0`),
  bounded costs in Wave 21a; missing (card waveP2d.md): anisotropic sets on an unbounded `K` and structured sets with a
  finite cell cover.
Imports the frozen `Wave23a` (`psiSB`; through it `SBFairness.cEps`, Wave 19b `worstDisp`, Tau Ceti `IsCoupling`,
`HasFiniteMoment`), `Wave20a` (`ProbW`, `Polytope`, `gamNorm`, `Lcell`, `sqrtE`, `certStruct`; through it
`Paper2.Seminorm` `T0`, `Deltafin`) and `Paper2.Alternating` (`centre`) statements, not copied. New definitions:
`sbObj`, `sbCost`, `sbBary` (SB); `anisoBall`, `jointObjAniso`, `penObjAniso`, `worstStruct`, `jointObjStruct` (paper 2).

Covered:
* `prop:sbbary` (the minimisation over `𝒫₂(ℝ)`, for every `ε > 0`, `S` groups): `sbbary_min` — for `τ > 0` with
  `Ψ_ε(τ) = 1` (THE root, by the frozen `sbbary_root_unique`), `ν⋆ = N(Σ_s p_s a_s, τ²) ∈ 𝒫₂`, the functional
  `Σ_s p_s 𝒞_ε(R_s, ·)` is finite at `ν⋆`, each inner `𝒞_ε(R_s, ν⋆)` is attained (the `min` of `eq:static`), `ν⋆`
  minimises the functional over all of `𝒫₂(ℝ)`, and every minimiser in `𝒫₂(ℝ)` equals `ν⋆`. ADDED: `sbbary_gap` — the
  quantitative form `Σ_s p_s 𝒞_ε(R_s, ν) ≥ min + (ε/4)(ν(A) − ν⋆(A))²` for every `ν ∈ 𝒫₂(ℝ)` and Borel `A`.
* `prop:jointmin`, anisotropic sets (`ε = 0`, full-support reference, `K = E` a real Hilbert space, so unbounded;
  linear rules `h_w = ⟪w, ·⟫`): `jointmin_aniso_upper` (every value of `Ψ(λ, γ)` bounds `R + ηF`, `F` the worst case
  over the two sets: `thm:certificate` for these sets, derived), `jointmin_aniso_inf` (the infimum of `Ψ` over
  `(λ₀, λ₁, γ)` is the objective of `(P_η)`, `inf_λ {R + ηF̄}`, and both equal `R + η(Δ + N₀ + N₁)²`, finite).
* `prop:jointmin`, structured sets with a finite cell cover (common affine map `𝔗_θ`, anisotropic differential sets
  on `K = E`, any `Θ`, cells `Θ_j ∋ θ_j` covering `Θ`): `jointmin_struct_upper` (every value of the cell objective
  `R + η max_j (|M_{γ_j}^{1/2}A_{θ_j}ᵀw| + L_j + √T⁰₀ + √T⁰₁)²` bounds `R + ηF_Θ`; "the supremum over `θ` becomes a
  maximum over finitely many cells"), `jointmin_struct_inf` (its infimum over `(λ₀, λ₁, (γ_j)_j)` is
  `R + η max_j (Δ(A_{θ_j}ᵀw) + L_j + N₀ + N₁)²`, which dominates the `(P_η)` objective `R + η certStruct`).
* `prop:jointmin`, structured sets, the printed equality REFUTED (critic): `jointmin_struct_printed_false` — under
  exactly the printed hypotheses (`K = ℝ^d`, `Θ` compact, `θ ↦ A_θ` continuous, Wasserstein balls with `β_s > 0`, a
  finite cover with `θ_j ∈ Θ_j`, any common point `p`) the infimum of the cell function is in general different from
  BOTH readings of the `(P_η)` objective (`inf_λ {R + η sup_θ F̄_θ}`, new `penObjStruct`; and `R + η certStruct`).
  Witness (`RouteRefute`): `E = ℝ`, `Θ = Bool`, `A = ±I`, `P̂₀ = δ₁`, `P̂₁ = δ₋₁`, `β_s = 1`, one cell, `w = 1`:
  cell function `≥ 36`, both `(P_η)` readings `≤ 16`.

Not covered (declared):
* `prop:sbbary`: nothing of the statement is left; the printed proof's route (Lagrange multipliers for the joint
  problem, "a stationary point of a strictly convex problem is the unique global minimiser") is replaced by a Gibbs
  inequality against the explicit Gaussian Schrödinger potentials (see Route notes). The remaining sentences of the
  proposition ("Moreover … strictly increasing … limits") are the frozen Wave 23a `sbbary_strictMono`,
  `sbbary_limits`.
* `prop:jointmin`: classes satisfying the mixture assumption (frozen Wave 21a `jointmin_free`, finite `L` only),
  entropic sets (`ε > 0`) on an unbounded `K` (the Gibbs principle with an unbounded exponent), non-linear rules on an
  unbounded `K`, the entropic differential sets of the "cell bounds of the companion paper", and max-sliced balls.
  For structured sets the equality "objective of `(P_η)` = infimum" is NOT claimed (see Critic notes): what is proved is
  equality with the cell objective and domination of the `(P_η)` objective.

Encodings (to be checked by the critic):
* SB: `R_s = gaussianReal a_s σ_s²`, `ν⋆ = gaussianReal (Σ p_s a_s) τ²`; groups `Fin S`, `p_s > 0`, `Σ p_s = 1`,
  `σ_s > 0`, `ε > 0`; `Ψ_ε = psiSB` (frozen, `cEps > 0`, no junk division). `𝒫₂(ℝ)` = probability measures with
  `HasFiniteMoment 2` (as in the frozen Wave 23a `qgrowth_*`). `sbObj ε π = ∫ (x−y)²/2 dπ + ε ∫ log(dπ/dLeb) dπ`
  (`EReal`, Lebesgue measure on `ℝ²`, `dπ/dLeb = π.rnDeriv volume`) when `π ≪ Leb` and both integrands are
  `π`-integrable, `+∞` otherwise. Junk audit: for `π` with marginals in `𝒫₂` the negative part of `log(dπ/dLeb)` is
  always `π`-integrable (`f log⁻ f ≤ f|z|² + C e^{−|z|²/2}`), so non-integrability means `∫ π log π = +∞` and `⊤` is
  the true value; a plan without a density has `Ent = −∞` in the paper's convention, value `+∞`; `log 0 = 0` and
  `rnDeriv = ∞` only on `π`-null sets. `sbCost = ⨅_{π ∈ Π(μ,ν)} sbObj` (`EReal`, coupling set nonempty), `sbBary =
  Σ_s p_s sbCost` (`EReal`; no `⊥` summand is reachable: `sbCost ≥` a real number, proved). "Is the minimiser" is: a
  minimiser, and the only one (equality of values forces `ν = ν⋆`); the values are compared in `EReal`.
* paper 2: covariates in a real Hilbert space `E` (`CompleteSpace`, Borel; generalises `K = ℝ^d`, unbounded);
  weighted centres `P̂_s = centre a_s x_s` with `ProbW a_s` (generalises `1/n_s`); the anisotropic set with matrix
  `M_s ≻ 0` is encoded, as in the frozen `Paper2.Seminorm` and Wave 20a, by a continuous linear automorphism `G_s`
  with cost `‖G_s(x' − x)‖²` (`G_s = M_s^{−1/2}`: `(x'−x)ᵀM_s⁻¹(x'−x)`; `G_s = id`: ordinary Wasserstein balls on the
  whole space) — the bridge `‖M^{−1/2}u‖² = uᵀM⁻¹u` to the frozen matrix form `Quick.InAniso` is not formalised;
  membership is `inf_{γ ∈ Π(P̂_s, Q)} ∫⁻ ‖G_s(x' − x)‖² dγ ≤ β_s` (`ℝ≥0∞`, `Q` a probability measure); `F(w)` is the
  frozen `worstDisp` (`ℝ≥0∞`); `T⁰_s` is the frozen `T0` (`EReal`, `+∞` for `λ < ‖(G_s⁻¹)ᵀw‖²`) and `√T⁰_s` the frozen
  `sqrtE` (`√⊤ = ⊤`; `T0 ≥ 0` since its supremum is `≥ 0` at `x = x_i` and `λβ ≥ 0`, so `sqrtE` is not truncating);
  `|M_γ^{1/2}w|` is the frozen `gamNorm`, `Δ(w)` the frozen `Deltafin` (coupling form, equal to `W₂(h_w#P̂₀, h_w#P̂₁)`
  by the certified `delta_inf_W2`, used in the routes); the coupling `γ` ranges over the frozen `Polytope a₀ a₁`;
  `R(w)` is a constant `Rh ≥ 0` (`R` does not depend on `(λ, γ)`), `η > 0`, `λ_s` over `Ioi 0`; objectives in `ℝ≥0∞`
  with `⨅`. Structured: `𝔗_θ x = A_θ x + b_θ` (`A_θ : E →L E`, any index type `Θ`, no compactness or continuity — the
  cell objective may be `+∞` when `L_j = ∞`), transported centres `A_θ x_i + b_θ`, `F_Θ = worstStruct = sup_θ worstDisp`;
  cells `cell j ⊆ Θ` covering `Θ`, `θc j ∈ cell j`, `L_j = Lcell` (frozen, `Σ_s` about a common point `p`); in the
  cell objective `T⁰_s` is evaluated at the untransported centres (it does not depend on the atoms: route `T0_centre`;
  the paper computes it "on the transported centres"); `(P_η)`'s structured objective is `R + η certStruct` (frozen).

Critic notes (from the formalisation):
* All 7 claims are proved in `Wave28e/Route{SBBary,JointMin,Refute}.lean` (dependencies: propext, Classical.choice, Quot.sound).
  Routes reuse Foundations/GaussianEOT (`gaussCoupling_lebesgue_form`, `lebF_quadratic`, `lebG_quadratic`, `cPos_*`),
  the certified `Paper2.Alternating.delta_inf_W2`, `Paper2.Seminorm.T0_eq` with the route `sup_quad`, `seminorm_wass`
  (through Wave 20a `iInf_sqrtT0`), the certified Wave 20a `structured_value`, `structured_cells`, `deltafin_affine`, and
  Tau Ceti (`wassersteinEDist_triangle`, `_comm`, `_rpow_le_lintegral`).
* SB (manuscript): the printed proof is formal — it differentiates in infinite dimensions and asserts that a stationary
  point of a strictly convex problem with linear constraints is the global minimiser without exhibiting multipliers or
  attainment. A rigorous two-line replacement: with the Gaussian plans in Schrödinger form `π⋆_s ∝ exp{(f_s(x) + g_s(y) −
  ½|x−y|²)/ε}` against Lebesgue measure, Gibbs' inequality gives, for EVERY `ν` and `π_s ∈ Π(R_s, ν)`,
  `½∫|x−y|² dπ_s − εEnt(π_s) ≥ ∫ f_s dR_s + ∫ g_s dν + ε H²(π_s, π⋆_s)`, and `Σ_s p_s g_s` is constant exactly when
  `Ψ_ε(τ) = 1` and the mean is `a⋆` (the proof's coefficient matching); summing gives minimality and, through
  `|ν(A) − ν⋆(A)| ≤ 2H(π_s, π⋆_s)`, uniqueness with the gap `(ε/4)(ν(A) − ν⋆(A))²`. No compactness or lower
  semicontinuity is needed. The paper's `a⋆ − a_s` coefficient of `g_s` agrees with the formalised potentials.
* paper 2 (manuscript): for structured sets the proof's "every substitution replaces a term by an upper bound that is
  attained at the infimum over the new variables" fails for the cell bound (`L_j` is slack): e.g. `E = ℝ²`, `A_θ` the
  rotation by `θ ∈ [−π, π]` (one cell, `θ_1 = 0`), `x⁰ = e₁`, `x¹ = −e₁`, `w = e₁`: `sup_θ Δ(A_θᵀw) = 2` but
  `Δ(A_0ᵀw) + L_1 ≥ 6` for every common point `p`. So the infimum of the joint function is the cell objective, an
  upper bound for the `(P_η)` objective, not equal to it; the statement's "equals the objective of `(P_η)`" should be
  restricted to models without cells, or read with the cell objective as the structured `(P_η)`. Confirmed by the
  critic and formalised as `jointmin_struct_printed_false` (1-D reduction of the rotation example: `θ ∈ {0, π}`).
  The refutation is robust to the shape of the cell function: any function containing `L_j` additively inside the
  square, with nonnegative other terms, is `≥ L_1² = 16 > (P_η)` in a variant with `β_s = 0`; the bound uses only
  `L_1 = 4` (for every `p`: `2|1 − p| + 2|1 + p| ≥ 4`). The upper-bound half of the proposition is unaffected.

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TauCeti
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave28e

/-! ### SB `prop:sbbary`: the Schrödinger barycenter functional over `𝒫₂(ℝ)` -/

open Classical in
/-- The objective of `eq:static`, `½∫|x−y|² dπ − ε Ent(π)` with the differential entropy
`Ent(π) = −∫ log(dπ/dLeb) dπ`; it is `+∞` unless `π ≪ Leb` and both integrands are `π`-integrable. -/
def sbObj (ε : ℝ) (π : Measure (ℝ × ℝ)) : EReal :=
  if π ≪ volume ∧ Integrable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2) π ∧
      Integrable (fun z => Real.log (π.rnDeriv volume z).toReal) π then
    ((∫ z, (z.1 - z.2) ^ 2 / 2 ∂π + ε * ∫ z, Real.log (π.rnDeriv volume z).toReal ∂π : ℝ) : EReal)
  else ⊤

/-- The static entropic cost `𝒞_ε(μ, ν) = inf_{π ∈ Π(μ,ν)} sbObj ε π` (`eq:static`), in `EReal`. -/
def sbCost (ε : ℝ) (μ ν : Measure ℝ) : EReal :=
  ⨅ (π : Measure (ℝ × ℝ)) (_ : IsCoupling π μ ν), sbObj ε π

/-- The Schrödinger barycenter functional `ν ↦ Σ_s p_s 𝒞_ε(R_s, ν)` of `eq:sbbary`. -/
def sbBary {S : ℕ} (ε : ℝ) (p : Fin S → ℝ) (R : Fin S → Measure ℝ) (ν : Measure ℝ) : EReal :=
  ∑ s, ((p s : ℝ) : EReal) * sbCost ε (R s) ν

/-! ### paper 2 `prop:jointmin`: anisotropic and structured sets on the whole space -/

section JointMin
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] {n₀ n₁ : ℕ}

open StatFormal.RobustEquality.Paper2.Seminorm StatFormal.Wave20a

/-- The anisotropic set (`ε = 0`, reference of full support on `K = E`) around `P̂ = Σ_i a_i δ_{x_i}`, cost
`c(x, x') = ‖G(x' − x)‖²` (`G = M^{-1/2}`: `(x'−x)ᵀM⁻¹(x'−x)`; `G = id`: Wasserstein balls):
`{Q : inf_{γ ∈ Π(P̂,Q)} E_γ c ≤ β}`. -/
def anisoBall (G : E ≃L[ℝ] E) {n : ℕ} (a : Fin n → ℝ) (x : Fin n → E) (β : ℝ) : Set (Measure E) :=
  {Q | IsProbabilityMeasure Q ∧
    (⨅ (γ : Measure (E × E)) (_ : IsCoupling γ (StatFormal.RobustEquality.Paper2.Alternating.centre a x) Q),
      ∫⁻ z, ENNReal.ofReal (‖G (z.2 - z.1)‖ ^ 2) ∂γ) ≤ ENNReal.ofReal β}

/-- The joint objective for independent anisotropic sets and the linear rule `h_w = ⟪w, ·⟫`:
`Ψ(λ, γ) = R + η (|M_γ^{1/2} w| + √T⁰₀(w, λ₀) + √T⁰₁(w, λ₁))²`, in `ℝ≥0∞`. -/
def jointObjAniso (G₀ G₁ : E ≃L[ℝ] E) (β₀ β₁ : ℝ) (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ)
    (x₁ : Fin n₁ → E) (w : E) (Rh η lam₀ lam₁ : ℝ) (γ : Fin n₀ → Fin n₁ → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal Rh + ENNReal.ofReal η *
    (ENNReal.ofReal (gamNorm γ x₀ x₁ w) + sqrtE (T0 G₀ β₀ a₀ x₀ w lam₀) + sqrtE (T0 G₁ β₁ a₁ x₁ w lam₁)) ^ 2

/-- The objective of `(P_η)` at `w` and `λ`: `R + η F̄(w; λ)`, `F̄ = (Δ(w) + √T⁰₀ + √T⁰₁)²`. -/
def penObjAniso (G₀ G₁ : E ≃L[ℝ] E) (β₀ β₁ : ℝ) (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ)
    (x₁ : Fin n₁ → E) (w : E) (Rh η lam₀ lam₁ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal Rh + ENNReal.ofReal η *
    (ENNReal.ofReal (Deltafin a₀ x₀ a₁ x₁ w) + sqrtE (T0 G₀ β₀ a₀ x₀ w lam₀) +
      sqrtE (T0 G₁ β₁ a₁ x₁ w lam₁)) ^ 2

/-- The worst-case disparity of the structured model `𝒮_Θ = ⋃_θ 𝓑₀(𝔗_θ P̂₀; β₀) × 𝓑₁(𝔗_θ P̂₁; β₁)`,
`𝔗_θ x = A_θ x + b_θ`, with anisotropic differential sets: `sup_θ sup_{Q_s} W₂²(h_w#Q₀, h_w#Q₁)`. -/
def worstStruct {Θ : Type*} (G₀ G₁ : E ≃L[ℝ] E) (β₀ β₁ : ℝ) (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E)
    (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (A : Θ → E →L[ℝ] E) (b : Θ → E) (w : E) : ℝ≥0∞ :=
  ⨆ θ, StatFormal.Wave19b.worstDisp (anisoBall G₀ a₀ (fun i => A θ (x₀ i) + b θ) β₀)
    (anisoBall G₁ a₁ (fun j => A θ (x₁ j) + b θ) β₁) (fun z => ⟪w, z⟫)

/-- The joint objective of the structured model with a finite cell cover `(Θ_j, θ_j)` and one coupling `γ_j`
per cell: `R + η max_j (|M_{γ_j}^{1/2} A_{θ_j}ᵀ w| + L_j(w) + √T⁰₀(w, λ₀) + √T⁰₁(w, λ₁))²`. -/
def jointObjStruct [CompleteSpace E] {Θ : Type*} {J : ℕ} (G₀ G₁ : E ≃L[ℝ] E) (β₀ β₁ : ℝ) (a₀ : Fin n₀ → ℝ)
    (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (A : Θ → E →L[ℝ] E) (cell : Fin J → Set Θ)
    (θc : Fin J → Θ) (p w : E) (Rh η lam₀ lam₁ : ℝ) (γ : Fin J → Fin n₀ → Fin n₁ → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal Rh + ENNReal.ofReal η *
    ⨆ j, (ENNReal.ofReal (gamNorm (γ j) x₀ x₁ (ContinuousLinearMap.adjoint (A (θc j)) w)) +
      Lcell a₀ x₀ a₁ x₁ p A (cell j) (θc j) w + sqrtE (T0 G₀ β₀ a₀ x₀ w lam₀) +
      sqrtE (T0 G₁ β₁ a₁ x₁ w lam₁)) ^ 2

/-- The objective of `(P_η)` for the structured model at `w` and `λ`, read literally from `eq:problems` ("the same
with `sup_θ F̄_θ` for structured sets", `thm:certificate`: `Δ_θ`, `T^θ_s` on the transported centres):
`R + η sup_θ (Δ_θ(w) + √T^θ_0(w, λ₀) + √T^θ_1(w, λ₁))²`. -/
def penObjStruct {Θ : Type*} (G₀ G₁ : E ≃L[ℝ] E) (β₀ β₁ : ℝ) (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E)
    (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (A : Θ → E →L[ℝ] E) (b : Θ → E) (w : E) (Rh η lam₀ lam₁ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal Rh + ENNReal.ofReal η *
    ⨆ θ, (ENNReal.ofReal (Deltafin a₀ (fun i => A θ (x₀ i) + b θ) a₁ (fun j => A θ (x₁ j) + b θ) w) +
      sqrtE (T0 G₀ β₀ a₀ (fun i => A θ (x₀ i) + b θ) w lam₀) +
      sqrtE (T0 G₁ β₁ a₁ (fun j => A θ (x₁ j) + b θ) w lam₁)) ^ 2

end JointMin

namespace Claims

/-- `prop:sbbary`: for `R_s = N(a_s, σ_s²)`, `ε > 0` and `τ > 0` with `Ψ_ε(τ) = 1`, the Gaussian
`ν⋆ = N(Σ_s p_s a_s, τ²)` lies in `𝒫₂(ℝ)`, the barycenter functional is finite at `ν⋆`, each inner problem
`𝒞_ε(R_s, ν⋆)` is attained, `ν⋆` minimises the functional over all of `𝒫₂(ℝ)`, and it is the only minimiser. -/
def sbbary_min : Prop :=
  ∀ (S : ℕ) (ε : ℝ) (p a σ : Fin S → ℝ) (τ : ℝ),
    0 < ε → (∀ s, 0 < p s) → ∑ s, p s = 1 → (∀ s, 0 < σ s) → 0 < τ →
    StatFormal.Wave23a.psiSB ε p σ τ = 1 →
      HasFiniteMoment 2 (gaussianReal (∑ s, p s * a s) (τ ^ 2).toNNReal) ∧
      (∃ v : ℝ, sbBary ε p (fun s => gaussianReal (a s) (σ s ^ 2).toNNReal)
          (gaussianReal (∑ s, p s * a s) (τ ^ 2).toNNReal) = v) ∧
      (∀ s, ∃ π : Measure (ℝ × ℝ),
          IsCoupling π (gaussianReal (a s) (σ s ^ 2).toNNReal) (gaussianReal (∑ s, p s * a s) (τ ^ 2).toNNReal) ∧
          sbObj ε π = sbCost ε (gaussianReal (a s) (σ s ^ 2).toNNReal)
            (gaussianReal (∑ s, p s * a s) (τ ^ 2).toNNReal)) ∧
      (∀ ν : Measure ℝ, IsProbabilityMeasure ν → HasFiniteMoment 2 ν →
          sbBary ε p (fun s => gaussianReal (a s) (σ s ^ 2).toNNReal)
              (gaussianReal (∑ s, p s * a s) (τ ^ 2).toNNReal) ≤
            sbBary ε p (fun s => gaussianReal (a s) (σ s ^ 2).toNNReal) ν) ∧
      (∀ ν : Measure ℝ, IsProbabilityMeasure ν → HasFiniteMoment 2 ν →
          sbBary ε p (fun s => gaussianReal (a s) (σ s ^ 2).toNNReal) ν =
            sbBary ε p (fun s => gaussianReal (a s) (σ s ^ 2).toNNReal)
              (gaussianReal (∑ s, p s * a s) (τ ^ 2).toNNReal) →
          ν = gaussianReal (∑ s, p s * a s) (τ ^ 2).toNNReal)

/-- Quantitative form: with `v` the minimum value, `Σ_s p_s 𝒞_ε(R_s, ν) ≥ v + (ε/4)(ν(A) − ν⋆(A))²` for every
`ν ∈ 𝒫₂(ℝ)` and every Borel `A`. -/
def sbbary_gap : Prop :=
  ∀ (S : ℕ) (ε : ℝ) (p a σ : Fin S → ℝ) (τ : ℝ),
    0 < ε → (∀ s, 0 < p s) → ∑ s, p s = 1 → (∀ s, 0 < σ s) → 0 < τ →
    StatFormal.Wave23a.psiSB ε p σ τ = 1 →
      ∃ v : ℝ, sbBary ε p (fun s => gaussianReal (a s) (σ s ^ 2).toNNReal)
          (gaussianReal (∑ s, p s * a s) (τ ^ 2).toNNReal) = v ∧
        ∀ ν : Measure ℝ, IsProbabilityMeasure ν → HasFiniteMoment 2 ν → ∀ A : Set ℝ, MeasurableSet A →
          ((v + ε / 4 * (ν.real A - (gaussianReal (∑ s, p s * a s) (τ ^ 2).toNNReal).real A) ^ 2 : ℝ) : EReal) ≤
            sbBary ε p (fun s => gaussianReal (a s) (σ s ^ 2).toNNReal) ν

/-! #### paper 2 `prop:jointmin`: anisotropic sets on `K = E` (unbounded) -/

open StatFormal.RobustEquality.Paper2.Seminorm StatFormal.Wave20a in
/-- Independent anisotropic sets on the whole space, linear rule `h_w`: every value of the joint objective
`Ψ(λ, γ)` bounds `R(w) + η F(w)` from above, `F(w) = sup_{Q_s ∈ 𝓑_s} W₂²(h_w#Q₀, h_w#Q₁)`. -/
def jointmin_aniso_upper : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    (n₀ n₁ : ℕ) (G₀ G₁ : E ≃L[ℝ] E) (β₀ β₁ : ℝ) (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ)
    (x₁ : Fin n₁ → E) (w : E) (Rh η lam₀ lam₁ : ℝ) (γ : Fin n₀ → Fin n₁ → ℝ),
    ProbW a₀ → ProbW a₁ → 0 ≤ β₀ → 0 ≤ β₁ → 0 ≤ Rh → 0 < η → 0 < lam₀ → 0 < lam₁ → γ ∈ Polytope a₀ a₁ →
      ENNReal.ofReal Rh + ENNReal.ofReal η *
          StatFormal.Wave19b.worstDisp (anisoBall G₀ a₀ x₀ β₀) (anisoBall G₁ a₁ x₁ β₁) (fun z => ⟪w, z⟫) ≤
        jointObjAniso G₀ G₁ β₀ β₁ a₀ x₀ a₁ x₁ w Rh η lam₀ lam₁ γ

open StatFormal.RobustEquality.Paper2.Seminorm StatFormal.Wave20a in
/-- Independent anisotropic sets: the infimum of `Ψ` over `(λ₀, λ₁, γ)` is the objective of `(P_η)`,
`inf_λ {R + η F̄(w; λ)}`, and both equal `R + η (Δ(w) + N₀(w) + N₁(w))²`, `N_s(w) = √β_s ‖(G_s⁻¹)ᵀ w‖`
(finite, so the bounds of `jointmin_aniso_upper` are not vacuous). -/
def jointmin_aniso_inf : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
    (n₀ n₁ : ℕ) (G₀ G₁ : E ≃L[ℝ] E) (β₀ β₁ : ℝ) (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ)
    (x₁ : Fin n₁ → E) (w : E) (Rh η : ℝ),
    ProbW a₀ → ProbW a₁ → 0 ≤ β₀ → 0 ≤ β₁ → 0 < η →
      (⨅ (lam₀ : Set.Ioi (0 : ℝ)) (lam₁ : Set.Ioi (0 : ℝ)) (γ : Polytope a₀ a₁),
          jointObjAniso G₀ G₁ β₀ β₁ a₀ x₀ a₁ x₁ w Rh η lam₀ lam₁ γ) =
        (⨅ (lam₀ : Set.Ioi (0 : ℝ)) (lam₁ : Set.Ioi (0 : ℝ)),
          penObjAniso G₀ G₁ β₀ β₁ a₀ x₀ a₁ x₁ w Rh η lam₀ lam₁) ∧
      (⨅ (lam₀ : Set.Ioi (0 : ℝ)) (lam₁ : Set.Ioi (0 : ℝ)),
          penObjAniso G₀ G₁ β₀ β₁ a₀ x₀ a₁ x₁ w Rh η lam₀ lam₁) =
        ENNReal.ofReal Rh + ENNReal.ofReal η *
          (ENNReal.ofReal (Deltafin a₀ x₀ a₁ x₁ w) +
            ENNReal.ofReal (√β₀ * ‖ContinuousLinearMap.adjoint (G₀.symm : E →L[ℝ] E) w‖) +
            ENNReal.ofReal (√β₁ * ‖ContinuousLinearMap.adjoint (G₁.symm : E →L[ℝ] E) w‖)) ^ 2

/-! #### paper 2 `prop:jointmin`: structured sets with a finite cell cover -/

open StatFormal.RobustEquality.Paper2.Seminorm StatFormal.Wave20a in
/-- Structured sets (common affine map `𝔗_θ`, anisotropic differential sets on `K = E`), a finite cell cover
`Θ = ⋃_j Θ_j`, `θ_j ∈ Θ_j`: every value of the cell objective at `(λ₀, λ₁, (γ_j)_j)` bounds `R(w) + η F_Θ(w)`. -/
def jointmin_struct_upper : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    (Θ : Type) (n₀ n₁ J : ℕ) (G₀ G₁ : E ≃L[ℝ] E) (β₀ β₁ : ℝ) (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E)
    (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (A : Θ → E →L[ℝ] E) (b : Θ → E) (cell : Fin J → Set Θ) (θc : Fin J → Θ)
    (p w : E) (Rh η lam₀ lam₁ : ℝ) (γ : Fin J → Fin n₀ → Fin n₁ → ℝ),
    ProbW a₀ → ProbW a₁ → 0 ≤ β₀ → 0 ≤ β₁ → 0 ≤ Rh → 0 < η → 0 < lam₀ → 0 < lam₁ →
    (∀ θ, ∃ j, θ ∈ cell j) → (∀ j, θc j ∈ cell j) → (∀ j, γ j ∈ Polytope a₀ a₁) →
      ENNReal.ofReal Rh + ENNReal.ofReal η * worstStruct G₀ G₁ β₀ β₁ a₀ x₀ a₁ x₁ A b w ≤
        jointObjStruct G₀ G₁ β₀ β₁ a₀ x₀ a₁ x₁ A cell θc p w Rh η lam₀ lam₁ γ

open StatFormal.RobustEquality.Paper2.Seminorm StatFormal.Wave20a in
/-- Structured sets with a finite cell cover: the infimum of the cell objective over `(λ₀, λ₁, (γ_j)_j)` is
`R + η max_j (Δ(A_{θ_j}ᵀ w) + L_j(w) + N₀(w) + N₁(w))²` (the supremum over `θ` became a maximum over the cells), and
it dominates the objective of `(P_η)` for the structured model, `R + η sup_θ inf_λ F̄_θ(w; λ)`. -/
def jointmin_struct_inf : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
    (Θ : Type) (n₀ n₁ J : ℕ) (G₀ G₁ : E ≃L[ℝ] E) (β₀ β₁ : ℝ) (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E)
    (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (A : Θ → E →L[ℝ] E) (b : Θ → E) (cell : Fin J → Set Θ) (θc : Fin J → Θ)
    (p w : E) (Rh η : ℝ),
    ProbW a₀ → ProbW a₁ → 0 ≤ β₀ → 0 ≤ β₁ → 0 < η → (∀ θ, ∃ j, θ ∈ cell j) → (∀ j, θc j ∈ cell j) →
      (⨅ (lam₀ : Set.Ioi (0 : ℝ)) (lam₁ : Set.Ioi (0 : ℝ)) (γ : Fin J → Polytope a₀ a₁),
          jointObjStruct G₀ G₁ β₀ β₁ a₀ x₀ a₁ x₁ A cell θc p w Rh η lam₀ lam₁ (fun j => γ j)) =
        ENNReal.ofReal Rh + ENNReal.ofReal η *
          ⨆ j, (ENNReal.ofReal (Deltafin a₀ x₀ a₁ x₁ (ContinuousLinearMap.adjoint (A (θc j)) w)) +
            Lcell a₀ x₀ a₁ x₁ p A (cell j) (θc j) w +
            ENNReal.ofReal (√β₀ * ‖ContinuousLinearMap.adjoint (G₀.symm : E →L[ℝ] E) w‖) +
            ENNReal.ofReal (√β₁ * ‖ContinuousLinearMap.adjoint (G₁.symm : E →L[ℝ] E) w‖)) ^ 2 ∧
      ENNReal.ofReal Rh + ENNReal.ofReal η * certStruct G₀ G₁ β₀ β₁ a₀ x₀ a₁ x₁ A b w ≤
        ⨅ (lam₀ : Set.Ioi (0 : ℝ)) (lam₁ : Set.Ioi (0 : ℝ)) (γ : Fin J → Polytope a₀ a₁),
          jointObjStruct G₀ G₁ β₀ β₁ a₀ x₀ a₁ x₁ A cell θc p w Rh η lam₀ lam₁ (fun j => γ j)

open StatFormal.RobustEquality.Paper2.Seminorm StatFormal.Wave20a in
/-- REFUTATION of the printed `prop:jointmin` for structured sets with a finite cell cover: it is NOT true that
the objective of `(P_η)` equals the infimum of the cell function, under exactly the printed hypotheses
(`K = ℝ^d`, `Θ` compact, `θ ↦ A_θ` continuous, Wasserstein balls with budgets `β_s > 0` around the transported
centres, a finite cover `Θ = ⋃_j Θ_j` with `θ_j ∈ Θ_j`, `Σ_s` about any common point `p`). Both readings of the
`(P_η)` objective are refuted at once: the literal `inf_λ {R + η sup_θ F̄_θ(w; λ)}` (`eq:problems`) and the certified
worst case `R + η sup_θ inf_λ F̄_θ(w; λ)` of `prop:structured`. -/
def jointmin_struct_printed_false : Prop :=
  ¬ ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (Θ : Type) [TopologicalSpace Θ] [CompactSpace Θ] [Nonempty Θ]
    (n₀ n₁ J : ℕ) (G₀ G₁ : E ≃L[ℝ] E) (β₀ β₁ : ℝ) (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E)
    (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (A : Θ → E →L[ℝ] E) (b : Θ → E) (cell : Fin J → Set Θ) (θc : Fin J → Θ)
    (p w : E) (Rh η : ℝ),
    ProbW a₀ → ProbW a₁ → 0 < β₀ → 0 < β₁ → 0 ≤ Rh → 0 < η → Continuous A → (∀ θ, ∃ j, θ ∈ cell j) →
    (∀ j, θc j ∈ cell j) →
      (⨅ (lam₀ : Set.Ioi (0 : ℝ)) (lam₁ : Set.Ioi (0 : ℝ)) (γ : Fin J → Polytope a₀ a₁),
          jointObjStruct G₀ G₁ β₀ β₁ a₀ x₀ a₁ x₁ A cell θc p w Rh η lam₀ lam₁ (fun j => γ j)) =
        (⨅ (lam₀ : Set.Ioi (0 : ℝ)) (lam₁ : Set.Ioi (0 : ℝ)),
          penObjStruct G₀ G₁ β₀ β₁ a₀ x₀ a₁ x₁ A b w Rh η lam₀ lam₁) ∨
      (⨅ (lam₀ : Set.Ioi (0 : ℝ)) (lam₁ : Set.Ioi (0 : ℝ)) (γ : Fin J → Polytope a₀ a₁),
          jointObjStruct G₀ G₁ β₀ β₁ a₀ x₀ a₁ x₁ A cell θc p w Rh η lam₀ lam₁ (fun j => γ j)) =
        ENNReal.ofReal Rh + ENNReal.ofReal η * certStruct G₀ G₁ β₀ β₁ a₀ x₀ a₁ x₁ A b w

end Claims

end StatFormal.Wave28e
