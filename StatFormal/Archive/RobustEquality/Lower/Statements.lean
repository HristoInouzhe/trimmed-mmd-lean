import StatFormal.Lib.Distances.TV
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# FROZEN STATEMENTS — robust equality (JASA): what validity forces (lower bounds)

Sources (verbatim in `inventory/extracted/robust-equality-jasa.md`):
* `thm:loc-lower`, display `eq:twopoint` (`jasa/supp_proofs.tex:569-576`);
* `def:ad-moduli`, `thm:ad-lower` (`jasa/supp_calibration.tex:218-233`), with the definition of a valid
  upper confidence bound at level `α` (`supp_calibration.tex:211-214`): a measurable `ρ̂` of
  `Y_1, …, Y_m` with `P^m[ρ̂ ≥ Θ(P)] ≥ 1 − α` for every `P ∈ 𝒫(K)`.

Encodings (see card):
* `Θ = OT_ε(μ, ·)` enters as an **arbitrary** functional `Θ : Measure K → ℝ` (both results use nothing
  about it), so the claims are stronger than the paper's.
* `P^m` is `Measure.pi (fun _ : Fin m => P)`; probabilities are `Measure.real`.
* `‖·‖_TV` is `StatFormal.Distances.tvDist` (`sup_A |P(A) − Q(A)|`, the paper's convention; if the norm
  were read as the full variation `2 sup_A`, the claim here is the stronger one).
* `KL(P ‖ P̃)` is Mathlib's `klDiv` (an `ℝ≥0∞`); `kl(p‖q) = p log(p/q) + (1−p) log((1−p)/(1−q))` is the
  Bernoulli relative entropy, used only at `p = ½`, `q ∈ (½, 1)`.
* `P_1 = (1−η)P̃ + ηQ`, `η ∈ [0, 1)`, `(1−η)^m > 2α`, `m KL(P‖P̃) ≤ kl(½ ‖ 1 − α(1−η)^{−m})`: the
  admissible alternatives of `def:ad-moduli`.
* "median excess ≥ Θ(P₁) − Θ(P)" is the probability statement itself; the expectation bound is stated
  with the lower Lebesgue integral of `(ρ̂ − Θ(P))_+` (no integrability assumption needed).
Not covered (declared): `thm:loc-lower` (i) unseen mass and (ii) instability (they need the canonical
potential, i.e. strong semi-discrete duality); the supremum `Ω_P(α,m)` itself (stated per admissible
`P₁`); the lower bounds of `Ω_P` by `ω_P(κ_α/m)` and `ω^far_P(η)` beyond the admissibility checks below.
Hashed in `certify/statements.lock`; AI agents must not edit this file.
-/

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal

namespace StatFormal.RobustEquality.Lower

/-- Bernoulli relative entropy `kl(p ‖ q)`. -/
def klBern (p q : ℝ) : ℝ := p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))

/-- `ρ̂` is a valid upper confidence bound for `Θ` at level `α` from `m` i.i.d. draws. -/
def IsValidUCB {K : Type*} [MeasurableSpace K] (Θ : Measure K → ℝ) (m : ℕ)
    (ρ : (Fin m → K) → ℝ) (α : ℝ) : Prop :=
  Measurable ρ ∧ ∀ P : Measure K, IsProbabilityMeasure P →
    1 - α ≤ (Measure.pi fun _ : Fin m => P).real {y | Θ P ≤ ρ y}

namespace Claims

/-- `eq:twopoint`: if `ρ̂` covers `Θ` at level `1 − δ` on a family containing `P₀, P₁`, then
`P₀^m[ρ̂ − Θ(P₀) ≥ Θ(P₁) − Θ(P₀)] ≥ 1 − δ − ‖P₀^m − P₁^m‖_TV`. -/
def twopoint : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (Θ : Measure K → ℝ) (𝔓 : Set (Measure K)) (m : ℕ)
    (ρ : (Fin m → K) → ℝ) (δ : ℝ) (P₀ P₁ : Measure K),
    Measurable ρ → (∀ P ∈ 𝔓, IsProbabilityMeasure P) →
    (∀ P ∈ 𝔓, 1 - δ ≤ (Measure.pi fun _ : Fin m => P).real {y | Θ P ≤ ρ y}) →
    P₀ ∈ 𝔓 → P₁ ∈ 𝔓 →
      1 - δ - StatFormal.Distances.tvDist (Measure.pi fun _ : Fin m => P₀)
          (Measure.pi fun _ : Fin m => P₁) ≤
        (Measure.pi fun _ : Fin m => P₀).real {y | Θ P₁ - Θ P₀ ≤ ρ y - Θ P₀}

/-- `thm:ad-lower`: for a valid bound at level `α < ½` and every admissible `P₁ = (1−η)P̃ + ηQ`,
`P^m[ρ̂ − Θ(P) ≥ Θ(P₁) − Θ(P)] ≥ ½`. -/
def ad_lower : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (Θ : Measure K → ℝ) (m : ℕ) (ρ : (Fin m → K) → ℝ) (α η : ℝ)
    (P Pt Q : Measure K) [IsProbabilityMeasure P] [IsProbabilityMeasure Pt] [IsProbabilityMeasure Q],
    0 < α → α < 1 / 2 → IsValidUCB Θ m ρ α →
    0 ≤ η → η < 1 → 2 * α < (1 - η) ^ m →
    (m : ℝ≥0∞) * klDiv P Pt ≤ ENNReal.ofReal (klBern (1 / 2) (1 - α * ((1 - η) ^ m)⁻¹)) →
      1 / 2 ≤ (Measure.pi fun _ : Fin m => P).real
        {y | Θ (ENNReal.ofReal (1 - η) • Pt + ENNReal.ofReal η • Q) - Θ P ≤ ρ y - Θ P}

/-- `thm:ad-lower`, expectation form: `E_P (ρ̂ − Θ(P))_+ ≥ ½ (Θ(P₁) − Θ(P))` for every admissible `P₁`. -/
def ad_lower_mean : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (Θ : Measure K → ℝ) (m : ℕ) (ρ : (Fin m → K) → ℝ) (α η : ℝ)
    (P Pt Q : Measure K) [IsProbabilityMeasure P] [IsProbabilityMeasure Pt] [IsProbabilityMeasure Q],
    0 < α → α < 1 / 2 → IsValidUCB Θ m ρ α →
    0 ≤ η → η < 1 → 2 * α < (1 - η) ^ m →
    (m : ℝ≥0∞) * klDiv P Pt ≤ ENNReal.ofReal (klBern (1 / 2) (1 - α * ((1 - η) ^ m)⁻¹)) →
      ENNReal.ofReal ((1 / 2) *
          (Θ (ENNReal.ofReal (1 - η) • Pt + ENNReal.ofReal η • Q) - Θ P)) ≤
        ∫⁻ y, ENNReal.ofReal (ρ y - Θ P) ∂(Measure.pi fun _ : Fin m => P)

/-- `def:ad-moduli`: `κ_α := kl(½ ‖ 1 − α) = ½ log(1/(4α(1−α)))` for `α ∈ (0, ½)`. -/
def kappa_formula : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 / 2 →
    klBern (1 / 2) (1 - α) = (1 / 2) * Real.log (1 / (4 * α * (1 - α)))

/-- `def:ad-moduli`, the two admissibility checks behind `Ω_P ≥ max{ω_P(κ_α/m), ω^far_P(η)}`:
(a) `η = 0`, `P̃ = P₁` with `m KL(P‖P₁) ≤ κ_α` is admissible; (b) `P̃ = P`, any `Q` (e.g. `δ_z`) and
`0 ≤ η < η_α := 1 − (2α)^{1/m}` is admissible. -/
def admissible_checks : Prop :=
  ∀ (m : ℕ) (α η : ℝ), 1 ≤ m → 0 < α → α < 1 / 2 →
    (2 * α < (1 - 0) ^ m ∧
      klBern (1 / 2) (1 - α * ((1 - 0 : ℝ) ^ m)⁻¹) = klBern (1 / 2) (1 - α)) ∧
    (0 ≤ η → η < 1 - (2 * α) ^ ((1 : ℝ) / m) →
      2 * α < (1 - η) ^ m ∧ 0 ≤ klBern (1 / 2) (1 - α * ((1 - η) ^ m)⁻¹))

end Claims
end StatFormal.RobustEquality.Lower
