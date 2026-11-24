import StatFormal.Archive.SBFairness.DPlan.Statements
import StatFormal.Archive.Wave25a.Statements
import StatFormal.Archive.Wave20a.Statements
import StatFormal.Archive.Wave23d.Statements
import TauCeti.MeasureTheory.OptimalTransport.Entropic.Basic
import TauCeti.Probability.Distributions.ChiSquared
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.HasLaw

/-!
# FROZEN STATEMENTS — wave 29g: SB `lem:dplan` (optimality of the Gaussian plan in `ℝᵈ`) with the identification of
# the barycentric projection (`thm:paritydefect`, `prop:corrected`); robust equality paper 2 `prop:translation` (iii),
# `prop:structured` (max-sliced balls), `prop:repair` (dual formula and SOC form on the grid; `σ = 0` refutation)

Sources (current text read 2026-10-20):
* SB `data-fairness-repair/schrodinger_bridge_fairness_repair.tex`: `eq:static` (`:385-394`, cost `½|x−y|²`,
  `−εH(π)`, minimiser `π*_ε`, unique when finite), `lem:dplan` (`:665-690`: "`π*_ε(N(m₀,A), N(m₁,B))` is Gaussian with
  cross-covariance `C = C_ε(A,B)`", `eq:dC`, `eq:dquad`), `thm:paritydefect` (`:712-730`: the barycentric projection
  `T^ε_s = E[X₁ | X₀ = x]` is linear with matrix `C_sᵀA_s⁻¹`, push-forward covariance `P_s = C_sᵀA_s⁻¹C_s`),
  `eq:threeops` (`:654-662`), `prop:corrected` (`:840-851`: "if `R₀, R₁` and `ν` are Gaussian, `(T̃^ε_s)_# R_s = ν`"),
  `rem:notelliptical` (`:853-862`).
* Robust equality paper 2 `paper2/main.tex`: `prop:translation` (`:620-631`, (iii): "if `δ ∼ N(0,C)` with `rank C = k`,
  the bound in (ii) holds with probability at least `Pr[χ²_k ≤ β]`"); `prop:structured` (`:366-383`, max-sliced balls,
  "the exact groupwise worst case `√β_s|w|`"; proof `app_proofs.tex:105-123`); `prop:repair` (`:648-670`, (i) the dual
  formula `ω_s(σ)² = sup{…} = inf_{λ≥0}{λσ² + E_{μ_s} sup_y[(T_s(y) − T_s(U))² − λ(y − U)²]}`, (iii) the grid and the
  second-order cone constraints).
Imports the frozen `SBFairness/DPlan` (`Cmat`; its hypotheses on `S = A^{1/2}`, `N = (4SBS + ε²I)^{1/2}` copied
verbatim), `Wave25a` (`meanV`, `covM`, `corrMap`; frozen `corrected_gaussian` discharged), `Wave20a` (`realised`,
`gapW`, `ellip`, `ProbW`; frozen `translation_sup` used), `RobustEquality/Paper2/Seminorm` (`Deltafin`) and `Wave23d`
(`omegaMod`, `envFix`) statements, not copied; Mathlib (`multivariateGaussian`, `HasLaw`, covariance) and Tau Ceti
(`IsCoupling`, `entropicTransportCost`, `wassersteinEDist`, `chiSquaredMeasure`) otherwise. Libraries (new):
`Foundations/GaussianEOTd`, `Foundations/GaussianChi`, `Foundations/MaxSliced`, `Foundations/RepairDual`.

Covered:
* `lem:dplan`: `dplan_eot` (for `ε > 0`, every `d`: the entropic value between `N(m₀,A)` and `N(m₁,B)` is finite, the
  block matrix `Σ = [[A, C], [Cᵀ, B]]`, `C = Cmat S N ε`, is positive definite, and `π` is an entropic optimal plan iff
  `π = N((m₀,m₁), Σ)`: existence, uniqueness and identification of `π*_ε`); `dplan_crosscov` (`Cov(Xᵢ, Yⱼ) = Cᵢⱼ`).
* `thm:paritydefect` / `prop:corrected`: `dplan_barycentric` (the barycentric projection of every optimal plan is
  `x ↦ m₁ + CᵀA⁻¹(x − m₀)`, and it pushes `N(m₀,A)` to `N(m₁, CᵀA⁻¹C)`, the `P_s` of `eq:Ps`).
* DISCHARGE of the frozen Wave 25a `corrected_gaussian` (premise "`T` affine"): `corrected_gaussian_eot`.
* paper 2 `prop:translation` (iii): `translation_chisq`.
* paper 2 `prop:structured`, max-sliced balls: `structured_ms_group` (exact groupwise worst case `√β|w|`, attained by the
  translate of the centre by `√β w/|w|`), `structured_ms_value` (the certified worst case does not depend on `b_θ` and
  equals `(sup_θ Δ(A_θᵀw) + √β₀|w| + √β₁|w|)²`).
* paper 2 `prop:repair`: `repair_dual_grid` (the dual formula, with the minimum attained, in the setting of (iii): score
  law `Σᵢ aᵢ δ_{xᵢ}` with atoms on the finite grid `G`, shifted scores in `G`, any `T`, every `σ ≥ 0`), `repair_soc` (the
  printed SOC form, `t > 0`: `ω(σ) ≤ t` iff `∃ μ ≥ 0, z` with `(T(y) − T(xᵢ))² ≤ t(zᵢ + μ(y − xᵢ)²)` on the grid and
  `μσ² + Σ aᵢzᵢ ≤ t`).
* REFUTED (fair, degenerate budget `σ = 0`): `repair_dual_sigma0_counter` — the printed dual formula of (i) fails at
  `σ = 0` for the nondecreasing step map `T = 1_{(0,∞)}` and `μ = δ₀` (`ω(0) = 0`, every dual value `= 1`).

Not covered (declared):
* `lem:dplan`: the value `C_ε(μ,ν)` in `ℝᵈ` (not printed); the limit `ε ↓ 0` as an OT statement.
* SB `prop:noisefree`, `thm:gaussian` for `d ≥ 2`: NOT APPLICABLE — both are printed for scalar Gaussians (`σ_s`, `τ`,
  `κ_{ε,s}`); the `d = 1` premise is discharged (Wave P3b). `prop:mixture` (path space) stays open.
* SB `cor:tdelta`, attainment: already certified (Wave P1c `tdelta_attained`, batch 91); the partial note is stale.
* paper 2 `prop:repair` (i): the dual formula for general score laws and `y ∈ ℝ` with `σ > 0` (W-DRO strong duality with
  measurable selections over `ℝ`); (ii) `Lip(T_s) = ℓ + (1−ℓ)ζ_s`.

Encodings (to be checked by the critic):
* `ℝᵈ = EuclideanSpace ℝ (Fin d)`; `N(m, Σ) = multivariateGaussian m Σ` (`Σ ⪰ 0` throughout: `A, B ≻ 0` assumed, the
  block matrix `≻ 0` proved, `CᵀA⁻¹C = (L diag c Li)ᵀ…` proved equal to `Liᵀ diag(c²) Li ⪰ 0` in the route).
* Joint law: `N(joinD m₀ m₁, fromBlocks A C Cᵀ B)` on `EuclideanSpace ℝ (Fin d ⊕ Fin d)` pushed by `splitD`; `C` is the
  upper-right block, so `Cᵢⱼ = Cov(Xᵢ, Yⱼ)`.
* Cost `½‖x − y‖² = sqCostD`; `IsEntPlanD` as the frozen Wave P3b `IsEntPlan` (Tau Ceti normalisation
  `∫ c dπ + ε KL(π ‖ μ ⊗ ν)`, same minimisers as the paper's `½∫|x−y|² dπ − εH(π)` under `ass:ac`); finiteness asserted.
* Barycentric projection via its defining identity against bounded measurable `h` (as Wave P3b `gaussplan_barycentric`).
* `translation_chisq`: `HasLaw (δ₀ − δ₁) (N(0,C)) P`, `C` PSD (`toEuclideanCLM C` is the frozen operator), `rank C =
  Matrix.rank C`, `Pr[χ²_k ≤ β] = chiSquaredMeasure k (Iic β)`; "with probability at least" = a MEASURABLE event of at
  least that probability on which both bounds of (ii) hold.
* Max-sliced ball: `{Q prob. : ∀ ‖u‖ = 1, W₂(⟨u,·⟩_# P, ⟨u,·⟩_# Q) ≤ √β}` (= `sup_u W₂² ≤ β`); `msWorst` = the exact
  groupwise worst case `sup_{Q ∈ ball} W₂(h_w # P, h_w # Q)`; the structured certified worst case `certStructMS` mirrors
  the frozen `certStruct` with the groupwise term replaced by `msWorst` (as printed: max-sliced balls are not of the form
  `eq:BN`); centres `finLaw a x = Σ aᵢ δ_{xᵢ}`.
* `repair_*`: `ω = ` frozen `omegaMod μ G σ T` with `G` the finite grid (`↑G`), the dual objective = frozen `envFix`
  (`⨆` over the grid subtype, Bochner integral against the discrete law); `x i ∈ G` is the pooled-grid hypothesis of (iii).
  The `σ = 0` refutation uses `G = univ` and the printed real dual objective at `μ = δ₀` (a real `⨆` over `ℝ` of a family
  bounded above by `1`, so not a junk value; the integral is against `δ₀`).

Junk audit: no division (`x/0`); `√` only of `β ≥ 0`, `⟪w, Cw⟫ ≥ 0`; `Measure.map` only of continuous maps; `corrMap` of
an integrable `T`; `entropicTransportCost ≠ ∞` asserted; Bochner integrals with integrability asserted or of
bounded × Gaussian-integrable integrands, or against finite discrete laws; `⨅` over `λ ≥ 0` bounded below by `0` (the
stay option) and attained; `⨆` over a nonempty finite grid; Mathlib's `eLpNorm` of a non-a.e.-strongly-measurable
function is `∞` — the route proves a.e. strong measurability on every feasible (finitely supported) joint law, so
`omegaMod` on the grid carries no junk; `Matrix.rank` of a PSD matrix.

Proof notes: GaussianEOTd: spectral decomposition `N = U diag(n) Uᵀ`, `L = SU`, `Li = UᵀS⁻¹`, `cᵢ = (nᵢ − ε)/2 > 0` (from
`4SBS ≻ 0`), `τᵢ² = cᵢ² + εcᵢ`; the plan is the image of the product of the one-dimensional Gaussian couplings
`gaussCoupling 0 1 0 τᵢ cᵢ` under `z ↦ (m₀ + Lz₁, m₁ + Liᵀz₂)`; the one-dimensional Schrödinger densities multiply, and the
cross term `Σ uᵢvᵢ = ⟪x − m₀, y − m₁⟫` (`Liᵀ Lᵀ = (L Li)ᵀ = I`) gives the density `exp((f(x) + g(y) − ½‖x − y‖²)/ε)`
against `μ ⊗ ν` with integrable quadratic `f`, `g`; Tau Ceti's sufficiency and uniqueness conclude. GaussianChi:
`T = {Uᵀx vanishes on null eigen-directions, Σ (Uᵀx)ᵢ²/λᵢ ≤ β} ⊆ ellip`, whose `N(0,C)`-preimage under `U diag(√λ)`
contains `{Σ_{λᵢ≠0} wᵢ² ≤ β}`, of `γ`-measure `χ²_{rank C}`. MaxSliced: scaling and translation bounds for `W₂` on `ℝ`
(`W₂ ≥ W₁ ≥` mean shift by Kantorovich–Rubinstein). RepairDual: one-constraint Lagrangian duality on a finite grid (the
dual is attained; one-sided slopes at the minimiser give two selections whose mixture saturates the budget).

Manuscript notes: (1) `prop:repair` (i) dual formula is false at `σ = 0` for discontinuous nondecreasing `T` (formal
counterexample above; fix: state the dual equality for `σ > 0`, where the stay coupling is strictly feasible (Slater).
Continuity of `T` is NOT a sufficient fix: for the continuous nondecreasing `T(y) = exp(max(y,0)²)` and `μ = δ₀` every
dual value at `σ = 0` is `+∞` while `ω(0) = 0`). (2) No other statement was found false.

DRAFT — not yet in `certify/statements.lock`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Matrix WithLp TauCeti InformationTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace StatFormal.Wave29g

local notation "E" d => EuclideanSpace ℝ (Fin d)

variable {d : ℕ}

/-- The quadratic cost `½‖x − y‖²` on `ℝᵈ × ℝᵈ`. -/
def sqCostD (z : (E d) × (E d)) : ℝ≥0∞ := ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)

/-- `π` is an entropic optimal plan `π*_ε(μ, ν)` for the cost `½‖x − y‖²`: a coupling attaining
`inf_π ∫ c dπ + ε KL(π ‖ μ ⊗ ν)`. -/
def IsEntPlanD (ε : ℝ) (μ ν : Measure (E d)) (P : Measure ((E d) × (E d))) : Prop :=
  IsCoupling P μ ν ∧
    ∫⁻ z, sqCostD z ∂P + (ε.toNNReal : ℝ≥0∞) * klDiv P (μ.prod ν) = entropicTransportCost sqCostD ε.toNNReal μ ν

/-- `ℝ^{d ⊕ d} → ℝᵈ × ℝᵈ`. -/
def splitD (z : EuclideanSpace ℝ (Fin d ⊕ Fin d)) : (E d) × (E d) :=
  (toLp 2 fun i => z (Sum.inl i), toLp 2 fun j => z (Sum.inr j))

/-- `(m₀, m₁) ∈ ℝ^{d ⊕ d}`. -/
def joinD (m₀ m₁ : E d) : EuclideanSpace ℝ (Fin d ⊕ Fin d) := toLp 2 (Sum.elim (ofLp m₀) (ofLp m₁))

/-- The Gaussian law on `ℝᵈ × ℝᵈ` with means `(m₀, m₁)` and block covariance `[[A, C], [Cᵀ, B]]`. -/
def jointGauss (m₀ m₁ : E d) (A B C : Matrix (Fin d) (Fin d) ℝ) : Measure ((E d) × (E d)) :=
  (multivariateGaussian (joinD m₀ m₁) (fromBlocks A C Cᵀ B)).map splitD

/-- The affine map `x ↦ m₁ + M(x − m₀)`. -/
def affD (m₀ m₁ : E d) (M : Matrix (Fin d) (Fin d) ℝ) (x : E d) : E d := m₁ + toLp 2 (M *ᵥ ofLp (x - m₀))

section MaxSliced
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]

/-- The discrete law `Σᵢ aᵢ δ_{xᵢ}`. -/
def finLaw {n : ℕ} (a : Fin n → ℝ) (x : Fin n → H) : Measure H := ∑ i, ENNReal.ofReal (a i) • Measure.dirac (x i)

/-- The max-sliced `W₂` ball of budget `β` around `P`: probability laws `Q` with
`sup_{‖u‖ = 1} W₂²(⟨u,·⟩_# P, ⟨u,·⟩_# Q) ≤ β`. -/
def msBall (P : Measure H) (β : ℝ) : Set (Measure H) :=
  {Q | IsProbabilityMeasure Q ∧ ∀ u : H, ‖u‖ = 1 →
    wassersteinEDist 2 (P.map fun x => ⟪u, x⟫) (Q.map fun x => ⟪u, x⟫) ≤ ENNReal.ofReal √β}

/-- The exact groupwise worst case of the linear rule `h_w = ⟨w,·⟩` over the max-sliced ball:
`sup_{Q ∈ B} W₂(h_w # P, h_w # Q)`. -/
def msWorst (P : Measure H) (β : ℝ) (w : H) : ℝ≥0∞ :=
  ⨆ Q ∈ msBall P β, wassersteinEDist 2 (P.map fun x => ⟪w, x⟫) (Q.map fun x => ⟪w, x⟫)

open StatFormal.RobustEquality.Paper2.Seminorm (Deltafin) in
/-- The certified worst case of the structured model with max-sliced differential balls of budgets `β_s` around the
transported centres `𝔗_θ P̂_s` (`𝔗_θ x = A_θ x + b_θ`): `sup_θ (Δ_θ(w) + groupwise worst₀ + groupwise worst₁)²`. -/
def certStructMS [CompleteSpace H] {Θ : Type*} {n₀ n₁ : ℕ} (β₀ β₁ : ℝ) (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → H)
    (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → H) (A : Θ → H →L[ℝ] H) (b : Θ → H) (w : H) : ℝ≥0∞ :=
  ⨆ θ, (ENNReal.ofReal (Deltafin a₀ (fun i => A θ (x₀ i) + b θ) a₁ (fun j => A θ (x₁ j) + b θ) w) +
    msWorst (finLaw a₀ fun i => A θ (x₀ i) + b θ) β₀ w + msWorst (finLaw a₁ fun j => A θ (x₁ j) + b θ) β₁ w) ^ 2

end MaxSliced

namespace Claims

open StatFormal.SBFairness.DPlan (Cmat)

/-! ### SB `lem:dplan` -/

/-- `lem:dplan`: for `ε > 0` the entropic transport problem between `N(m₀,A)` and `N(m₁,B)` on `ℝᵈ` has finite value,
`Σ = [[A, C], [Cᵀ, B]]` is positive definite (`C = C_ε(A,B)` of `eq:dC`), and `π` is an optimal plan iff `π` is the
Gaussian `N((m₀,m₁), Σ)`. -/
def dplan_eot : Prop :=
  ∀ (d : ℕ) (A B S N : Matrix (Fin d) (Fin d) ℝ) (ε : ℝ) (m₀ m₁ : E d), A.PosDef → B.PosDef → 0 < ε →
    S.PosDef → S * S = A → N.PosDef → N * N = 4 • (S * B * S) + ε ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ) →
      entropicTransportCost sqCostD ε.toNNReal (multivariateGaussian m₀ A) (multivariateGaussian m₁ B) ≠ ∞ ∧
      (fromBlocks A (Cmat S N ε) (Cmat S N ε)ᵀ B).PosDef ∧
      ∀ P : Measure ((E d) × (E d)), IsEntPlanD ε (multivariateGaussian m₀ A) (multivariateGaussian m₁ B) P ↔
        P = jointGauss m₀ m₁ A B (Cmat S N ε)

/-- `lem:dplan`, "with cross-covariance `C`": every optimal plan has `Cov(Xᵢ, Yⱼ) = Cᵢⱼ`. -/
def dplan_crosscov : Prop :=
  ∀ (d : ℕ) (A B S N : Matrix (Fin d) (Fin d) ℝ) (ε : ℝ) (m₀ m₁ : E d), A.PosDef → B.PosDef → 0 < ε →
    S.PosDef → S * S = A → N.PosDef → N * N = 4 • (S * B * S) + ε ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ) →
      ∀ P : Measure ((E d) × (E d)), IsEntPlanD ε (multivariateGaussian m₀ A) (multivariateGaussian m₁ B) P →
        ∀ i j, cov[fun z : (E d) × (E d) => z.1 i, fun z => z.2 j; P] = Cmat S N ε i j

/-- `thm:paritydefect` / `prop:corrected` / `rem:notelliptical`: the barycentric projection `E_π[Y | X = x]` of every
optimal plan is the affine map `x ↦ m₁ + CᵀA⁻¹(x − m₀)` (defining identity against bounded measurable `h`, each
coordinate), and it pushes `N(m₀, A)` to `N(m₁, CᵀA⁻¹C)` (the push-forward covariance `P_s` of `eq:Ps`). -/
def dplan_barycentric : Prop :=
  ∀ (d : ℕ) (A B S N : Matrix (Fin d) (Fin d) ℝ) (ε : ℝ) (m₀ m₁ : E d), A.PosDef → B.PosDef → 0 < ε →
    S.PosDef → S * S = A → N.PosDef → N * N = 4 • (S * B * S) + ε ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ) →
      ∀ P : Measure ((E d) × (E d)), IsEntPlanD ε (multivariateGaussian m₀ A) (multivariateGaussian m₁ B) P →
        (∀ h : (E d) → ℝ, Measurable h → (∃ K : ℝ, ∀ x, |h x| ≤ K) → ∀ j,
          Integrable (fun z : (E d) × (E d) => z.2 j * h z.1) P ∧
            ∫ z, z.2 j * h z.1 ∂P =
              ∫ x, affD m₀ m₁ ((Cmat S N ε)ᵀ * A⁻¹) x j * h x ∂(multivariateGaussian m₀ A)) ∧
        (multivariateGaussian m₀ A).map (affD m₀ m₁ ((Cmat S N ε)ᵀ * A⁻¹)) =
          multivariateGaussian m₁ ((Cmat S N ε)ᵀ * A⁻¹ * Cmat S N ε)

open StatFormal.Wave25a (meanV covM corrMap) in
/-- DISCHARGE of Wave 25a `corrected_gaussian` (premise "`T` affine"): for Gaussian groups and target and ANY integrable
version `T` of the barycentric projection of ANY entropic optimal plan `π*_ε(R, ν)`, the corrected map pushes `R`
exactly onto `ν` (hypotheses on `V^{1/2}`, `P^{-1/2}` as frozen). -/
def corrected_gaussian_eot : Prop :=
  ∀ (d : ℕ) (A B S N : Matrix (Fin d) (Fin d) ℝ) (ε : ℝ) (m₀ m₁ : E d) (P : Measure ((E d) × (E d)))
    (T : (E d) → (E d)) (Vh Ph : Matrix (Fin d) (Fin d) ℝ), A.PosDef → B.PosDef → 0 < ε →
    S.PosDef → S * S = A → N.PosDef → N * N = 4 • (S * B * S) + ε ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ) →
    IsEntPlanD ε (multivariateGaussian m₀ A) (multivariateGaussian m₁ B) P →
    Integrable T (multivariateGaussian m₀ A) →
    (∀ h : (E d) → ℝ, Measurable h → (∃ K : ℝ, ∀ x, |h x| ≤ K) → ∀ j,
      ∫ z, z.2 j * h z.1 ∂P = ∫ x, T x j * h x ∂(multivariateGaussian m₀ A)) →
    Vh.transpose = Vh → Vh * Vh = covM (multivariateGaussian m₁ B) id → Ph.transpose = Ph →
    Ph * covM (multivariateGaussian m₀ A) T * Ph = 1 →
      (multivariateGaussian m₀ A).map
          (corrMap (multivariateGaussian m₀ A) T (meanV (multivariateGaussian m₁ B) id) (Vh * Ph)) =
        multivariateGaussian m₁ B

/-! ### Robust equality paper 2 `prop:translation` (iii) -/

open StatFormal.Wave20a (realised gapW ProbW) in
open StatFormal.RobustEquality.Paper2.Seminorm (Deltafin) in
open TauCeti.Probability (chiSquaredMeasure) in
/-- (iii): if `δ = δ₀ − δ₁ ∼ N(0, C)`, `C ⪰ 0`, `β ≥ 0`, the bounds of (ii) hold on a measurable event of probability at
least `Pr[χ²_{rank C} ≤ β]`. -/
def translation_chisq : Prop :=
  ∀ (d n₀ n₁ : ℕ) (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E d) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E d) (w : E d)
    (C : Matrix (Fin d) (Fin d) ℝ) (β : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (δ₀ δ₁ : Ω → E d),
    ProbW a₀ → ProbW a₁ → C.PosSemidef → 0 ≤ β → HasLaw (fun ω => δ₀ ω - δ₁ ω) (multivariateGaussian 0 C) P →
      ∃ Sev : Set Ω, MeasurableSet Sev ∧ chiSquaredMeasure (C.rank : ℝ) (Iic β) ≤ P Sev ∧
        ∀ ω ∈ Sev,
          realised a₀ x₀ a₁ x₁ w (δ₀ ω) (δ₁ ω) ≤
              Deltafin a₀ x₀ a₁ x₁ w ^ 2 - gapW a₀ x₀ a₁ x₁ w ^ 2 +
                (|gapW a₀ x₀ a₁ x₁ w| + √β * √⟪w, toEuclideanCLM (𝕜 := ℝ) C w⟫) ^ 2 ∧
            realised a₀ x₀ a₁ x₁ w (δ₀ ω) (δ₁ ω) ≤
              (Deltafin a₀ x₀ a₁ x₁ w + √β * √⟪w, toEuclideanCLM (𝕜 := ℝ) C w⟫) ^ 2

/-! ### Robust equality paper 2 `prop:structured`, max-sliced balls -/

open StatFormal.Wave20a (ProbW) in
/-- The exact groupwise worst case of a linear rule over a max-sliced ball of budget `β` is `√β |w|`. -/
def structured_ms_group : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H] (n : ℕ)
    (a : Fin n → ℝ) (x : Fin n → H) (β : ℝ) (w : H),
    ProbW a → 0 ≤ β → msWorst (finLaw a x) β w = ENNReal.ofReal (√β * ‖w‖)

open StatFormal.Wave20a (ProbW) in
open StatFormal.RobustEquality.Paper2.Seminorm (Deltafin) in
/-- `prop:structured` for max-sliced balls: the certified worst case does not depend on `b_θ` and equals
`(sup_θ Δ(A_θᵀ w) + √β₀|w| + √β₁|w|)²`. -/
def structured_ms_value : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
    (Θ : Type) [Nonempty Θ] (n₀ n₁ : ℕ) (β₀ β₁ : ℝ) (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → H) (a₁ : Fin n₁ → ℝ)
    (x₁ : Fin n₁ → H) (A : Θ → H →L[ℝ] H) (b : Θ → H) (w : H),
    0 ≤ β₀ → 0 ≤ β₁ → ProbW a₀ → ProbW a₁ →
      certStructMS β₀ β₁ a₀ x₀ a₁ x₁ A b w =
        ((⨆ θ, ENNReal.ofReal (Deltafin a₀ x₀ a₁ x₁ (ContinuousLinearMap.adjoint (A θ) w))) +
          ENNReal.ofReal (√β₀ * ‖w‖) + ENNReal.ofReal (√β₁ * ‖w‖)) ^ 2

/-! ### Robust equality paper 2 `prop:repair`: the dual formula and the SOC form on a finite grid -/

open StatFormal.Wave20a (ProbW) in
open StatFormal.Wave23d (omegaMod envFix) in
/-- (i)/(iii), the W-DRO dual formula in the computational setting of (iii): for a score law `μ = Σᵢ aᵢ δ_{xᵢ}` whose
atoms lie on the finite grid `G` and shifted scores restricted to `G`,
`ω(σ)² = min_{λ ≥ 0} {λσ² + E_μ max_{y ∈ G}[(T(y) − T(U))² − λ(y − U)²]}` (the infimum is attained). -/
def repair_dual_grid : Prop :=
  ∀ (n : ℕ) (a : Fin n → ℝ) (x : Fin n → ℝ) (G : Finset ℝ) (σ : ℝ) (T : ℝ → ℝ),
    ProbW a → (∀ i, x i ∈ G) → 0 ≤ σ →
      omegaMod (finLaw a x) (G : Set ℝ) σ T ^ 2 =
          ENNReal.ofReal (⨅ lam : Set.Ici (0 : ℝ), envFix (finLaw a x) G lam σ T) ∧
        ∃ lam : ℝ, 0 ≤ lam ∧ envFix (finLaw a x) G lam σ T = ⨅ l : Set.Ici (0 : ℝ), envFix (finLaw a x) G l σ T

open StatFormal.Wave20a (ProbW) in
open StatFormal.Wave23d (omegaMod) in
/-- (iii), the SOC form as printed in the proof (`app_proofs.tex:272-277`): with the shifted scores restricted to the
grid and `t > 0`, `ω(σ) ≤ t` iff there are `μ ≥ 0` and auxiliary variables `zᵢ` with the rotated second-order cone
constraints `(T(y) − T(xᵢ))² ≤ t (zᵢ + μ (y − xᵢ)²)` for all grid points `y` and the linear constraint
`μσ² + Σᵢ aᵢ zᵢ ≤ t` (jointly in the values of `T`, `t`, `z`, `μ`). -/
def repair_soc : Prop :=
  ∀ (n : ℕ) (a : Fin n → ℝ) (x : Fin n → ℝ) (G : Finset ℝ) (σ : ℝ) (T : ℝ → ℝ) (t : ℝ),
    ProbW a → (∀ i, x i ∈ G) → 0 ≤ σ → 0 < t →
      (omegaMod (finLaw a x) (G : Set ℝ) σ T ≤ ENNReal.ofReal t ↔
        ∃ m : ℝ, 0 ≤ m ∧ ∃ z : Fin n → ℝ, (∀ i, ∀ y ∈ G, (T y - T (x i)) ^ 2 ≤ t * (z i + m * (y - x i) ^ 2)) ∧
          m * σ ^ 2 + ∑ i, a i * z i ≤ t)

open StatFormal.Wave23d (omegaMod) in
/-- REFUTATION (fair, degenerate budget) of the printed dual formula of (i) at `σ = 0`: for the nondecreasing map
`T = 1_{(0,∞)}` and the score law `δ₀`, the exact modulus is `ω(0) = 0`, while every dual value
`λ·0² + E_{δ₀} sup_{y ∈ ℝ}[(T(y) − T(U))² − λ(y − U)²]` equals `1`, so `ω(0)² = 0 ≠ 1 = inf_λ{…}`. -/
def repair_dual_sigma0_counter : Prop :=
  Monotone ((Set.Ioi (0 : ℝ)).indicator (1 : ℝ → ℝ)) ∧
    omegaMod (Measure.dirac 0) Set.univ 0 ((Set.Ioi (0 : ℝ)).indicator 1) = 0 ∧
    ∀ lam : ℝ, 0 ≤ lam →
      lam * 0 ^ 2 + ∫ u, (⨆ y : ℝ, (((Set.Ioi (0 : ℝ)).indicator (1 : ℝ → ℝ) y -
          (Set.Ioi (0 : ℝ)).indicator (1 : ℝ → ℝ) u) ^ 2 - lam * (y - u) ^ 2)) ∂(Measure.dirac 0) = 1

end Claims

end StatFormal.Wave29g
