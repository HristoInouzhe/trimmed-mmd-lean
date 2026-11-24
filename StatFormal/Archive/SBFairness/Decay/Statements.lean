import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# FROZEN STATEMENTS — SB fairness repair: certified decay (`thm:decay`, `def:glued`, `cor:tdelta`)

Source: `data-fairness-repair/schrodinger_bridge_fairness_repair.tex:2340-2420` (`def:glued`,
`thm:decay`, `cor:tdelta`), proof `:2721-2740`; `prop:mixture` (l.455): the bridge marginal is the law
of `(1−t)X₀ + tX₁ + √(εt(1−t)) Z`, `(X₀,X₁) ∼ π`, `Z ∼ N(0,I)` independent.

Conditional formalisation (see card): the bridge marginal is *defined* by the mixture formula of
`prop:mixture`, and the plans `π₀, π₁` are arbitrary probability measures on `ℝᵈ × ℝᵈ` with a common
second marginal (the paper takes the entropic plans `π^⋆_ε(R_s,ν)`; the proof uses only the common
marginal). `W₂` is Tau Ceti's `wassersteinEDist 2`; `G_ε²` is an infimum in `ℝ≥0∞`.
Hashed in `certify/statements.lock`; AI agents must not edit this file.
-/

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti Set
open scoped ENNReal

namespace StatFormal.SBFairness.Decay

variable {d : ℕ}

local notation "E" d => EuclideanSpace ℝ (Fin d)

/-- `prop:mixture`: the time-`t` bridge marginal of the plan `π` at noise level `ε`. -/
def bridge (π : Measure ((E d) × (E d))) (ε t : ℝ) : Measure (E d) :=
  (π.prod (stdGaussian (E d))).map
    (fun p => (1 - t) • p.1.1 + t • p.1.2 + Real.sqrt (ε * t * (1 - t)) • p.2)

/-- `def:glued`: `Γ` is a law of triples `(X⁰₀, X¹₀, X₁)` with `(X^s₀, X₁) ∼ π_s`. -/
def IsGluing (Γ : Measure ((E d) × (E d) × (E d))) (π₀ π₁ : Measure ((E d) × (E d))) : Prop :=
  Γ.map (fun q => (q.1, q.2.2)) = π₀ ∧ Γ.map (fun q => (q.2.1, q.2.2)) = π₁

/-- `def:glued`: `G_ε² = inf_Γ E_Γ ‖X⁰₀ − X¹₀‖²` (in `ℝ≥0∞`; `⊤` if there is no gluing). -/
def Gsq (π₀ π₁ : Measure ((E d) × (E d))) : ℝ≥0∞ :=
  ⨅ (Γ : Measure ((E d) × (E d) × (E d))) (_ : IsGluing Γ π₀ π₁), ∫⁻ q, edist q.1 q.2.1 ^ 2 ∂Γ

namespace Claims

/-- Sentence after `def:glued`: "Such `Γ` exist by the gluing lemma" — the set of gluings of two
probability plans with a common second marginal is nonempty. (Finiteness of `G_ε` additionally needs
second moments; not stated.) -/
def gluing_exists : Prop :=
  ∀ (d : ℕ) (π₀ π₁ : Measure ((E d) × (E d))) [IsProbabilityMeasure π₀] [IsProbabilityMeasure π₁],
    π₀.snd = π₁.snd → ∃ Γ, IsGluing Γ π₀ π₁

/-- `thm:decay`: `W₂(μ_{0,t}, μ_{1,t}) ≤ (1−t) G_ε`, stated squared:
`W₂² ≤ (1−t)² G_ε²`, for every `ε ≥ 0` and `t ∈ [0,1]`. -/
def decay : Prop :=
  ∀ (d : ℕ) (π₀ π₁ : Measure ((E d) × (E d))) [IsProbabilityMeasure π₀] [IsProbabilityMeasure π₁]
    (ε t : ℝ), π₀.snd = π₁.snd → 0 ≤ ε → t ∈ Icc (0 : ℝ) 1 →
      wassersteinEDist 2 (bridge π₀ ε t) (bridge π₁ ε t) ^ 2 ≤ ENNReal.ofReal ((1 - t) ^ 2) * Gsq π₀ π₁

/-- `cor:tdelta`, bound part: with `F(t) = W₂(μ_{0,t}, μ_{1,t})`, `G = G_ε < ∞` and `0 < δ < G`,
`t_δ = inf{t ∈ [0,1] : F(t) ≤ δ} ≤ 1 − δ/G`. (Attainment of the infimum is not covered.) -/
def tdelta_bound : Prop :=
  ∀ (d : ℕ) (π₀ π₁ : Measure ((E d) × (E d))) [IsProbabilityMeasure π₀] [IsProbabilityMeasure π₁]
    (ε δ : ℝ), π₀.snd = π₁.snd → 0 ≤ ε → Gsq π₀ π₁ ≠ ⊤ → 0 < δ →
      δ < Real.sqrt (Gsq π₀ π₁).toReal →
        sInf {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧
            wassersteinEDist 2 (bridge π₀ ε t) (bridge π₁ ε t) ≤ ENNReal.ofReal δ}
          ≤ 1 - δ / Real.sqrt (Gsq π₀ π₁).toReal

end Claims
end StatFormal.SBFairness.Decay
