import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Data.Sign.Basic

/-!
# FROZEN STATEMENTS — Schrödinger-bridge fairness repair, Gaussian layer

Paper: `data-fairness-repair/schrodinger_bridge_fairness_repair.tex`.
This file is the *trusted specification*. It is hashed in `certify/statements.lock`;
any edit requires human re-approval (`python3 tools/certify.py approve`).
AI agents must not edit it. Every claim has a fidelity card in `certify/cards/`.

Scope: real-analytic layer only. The OT identifications (entropic plan between Gaussians
has cross-covariance `c_ε`; the bridge marginal is `N(m_s(t), v_s(t))`; 1-D Gaussian `W₂`)
are NOT formalised: they enter through the definitions below. See the cards.
-/

noncomputable section
open Real

namespace StatFormal.SBFairness

/-- eq:ceps: `c_ε(σ₀,σ₁) = (-ε + √(ε² + 4σ₀²σ₁²))/2`. -/
def cEps (ε σ₀ σ₁ : ℝ) : ℝ := (-ε + √(ε ^ 2 + 4 * σ₀ ^ 2 * σ₁ ^ 2)) / 2

/-- `κ_{ε,s} = √(ε² + 4σ_s²τ²)` (thm:gaussian). -/
def kappa (ε σ τ : ℝ) : ℝ := √(ε ^ 2 + 4 * σ ^ 2 * τ ^ 2)

/-- eq:gaussmarg: `v_s(t) = (1-t)²σ_s² + t²τ² + t(1-t)κ_{ε,s}`. -/
def v (ε σ τ t : ℝ) : ℝ := (1 - t) ^ 2 * σ ^ 2 + t ^ 2 * τ ^ 2 + t * (1 - t) * kappa ε σ τ

/-- The `W₂`-geodesic scale `(1-t)σ + tτ`. -/
def geo (σ τ t : ℝ) : ℝ := (1 - t) * σ + t * τ

namespace Claims

/-- `lem:gaussplan` (algebraic part, eq:ceps): `c_ε` is the unique positive root of
`c² + εc = σ₀²σ₁²` when `ε, σ₀, σ₁ > 0`. -/
def lem_gaussplan_root : Prop :=
  ∀ ε σ₀ σ₁ : ℝ, 0 < ε → 0 < σ₀ → 0 < σ₁ →
    0 < cEps ε σ₀ σ₁ ∧ cEps ε σ₀ σ₁ ^ 2 + ε * cEps ε σ₀ σ₁ = σ₀ ^ 2 * σ₁ ^ 2 ∧
      ∀ c : ℝ, 0 < c → c ^ 2 + ε * c = σ₀ ^ 2 * σ₁ ^ 2 → c = cEps ε σ₀ σ₁

/-- `thm:gaussian` (b), no crossing: `sign(v₀(t) − v₁(t)) = sign(σ₀ − σ₁)` for all `t ∈ [0,1)`.
(The paper's setting has `ε > 0`, `τ > 0`, `σ_s > 0`; we state it for every real `ε`,
which is a generalisation, see card.) -/
def thm_gaussian_b : Prop :=
  ∀ ε σ₀ σ₁ τ t : ℝ, 0 < σ₀ → 0 < σ₁ → 0 < τ → t ∈ Set.Ico (0 : ℝ) 1 →
    SignType.sign (v ε σ₀ τ t - v ε σ₁ τ t) = SignType.sign (σ₀ - σ₁)

/-- `thm:gaussian` (c), variance inflation. -/
def thm_gaussian_c : Prop :=
  ∀ ε σ τ t : ℝ, 0 < ε → 0 < σ → 0 < τ → t ∈ Set.Ioo (0 : ℝ) 1 →
    v ε σ τ t - geo σ τ t ^ 2 = t * (1 - t) * (kappa ε σ τ - 2 * σ * τ) ∧
      0 < v ε σ τ t - geo σ τ t ^ 2

/-- `prop:eps2`, the two inequalities (the equality with `W₂` is out of scope). -/
def prop_eps2_bounds : Prop :=
  ∀ ε σ τ t : ℝ, 0 < ε → 0 < σ → 0 < τ → t ∈ Set.Icc (0 : ℝ) 1 →
    √(v ε σ τ t) - geo σ τ t ≤ t * (1 - t) * ε ^ 2 / (8 * σ * τ * geo σ τ t) ∧
      t * (1 - t) * ε ^ 2 / (8 * σ * τ * geo σ τ t) ≤ ε ^ 2 / (32 * σ * τ * min σ τ)

/-- `conj:mono` (OPEN in the paper, MC-supported only): for Gaussian groups the fairness
functional `F_ε(t)` with `F_ε(t)² = (1-t)²(a₀-a₁)² + (√v₀(t) − √v₁(t))²` is non-increasing on
`[0,1]`. Not yet proved. -/
def conj_mono : Prop :=
  ∀ ε τ σ₀ σ₁ a₀ a₁ : ℝ, 0 < ε → 0 < τ → 0 < σ₀ → 0 < σ₁ →
    AntitoneOn (fun t => (1 - t) ^ 2 * (a₀ - a₁) ^ 2 + (√(v ε σ₀ τ t) - √(v ε σ₁ τ t)) ^ 2)
      (Set.Icc 0 1)

end Claims
end StatFormal.SBFairness
