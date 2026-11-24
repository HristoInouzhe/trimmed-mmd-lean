import StatFormal.Archive.TrimmedMMD.Statements
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# FROZEN STATEMENTS — trimmed MMD: finite-sample region concentration

Sources (verbatim in `inventory/extracted/trimmed-mmd.md`): `ass:regularity` (`paper.tex:546`), `eq:region`
(`paper.tex:629`), `thm:concentration` (`paper.tex:765`), `cor:uniform` (`paper.tex:785`); proof via
`eq:reduction`, `eq:hormander`, `eq:cvar`, `lem:tcompact` in the supplement.

Encodings (see card):
* the RKHS enters through its feature map: `H` a real Hilbert space (complete inner product space),
  **separable** (A2), `φ : 𝒳 → H` strongly measurable with `‖φ x‖ ≤ κ` (A1: `k(x,x) = ‖φ x‖² ≤ κ²`); the
  sample space `𝒳` is any measurable space (as in the paper). (A3, characteristicness, is not used.)
* `𝒞_{α,k}(P) = {E_P[g φ] : g measurable, 0 ≤ g ≤ 1/(1−α), E_P g = 1}` (`region`; `L^∞(P)` classes are
  represented by bounded measurable functions, which does not change the set);
* `P_n` is the empirical measure of `X_1, …, X_n` (`Σ_i n⁻¹ δ_{X_i}`), `X_{1:n} ∼ P^{⊗n}` = `Measure.pi`;
* `d_H` is `Metric.hausdorffDist` (finite here: the regions are nonempty and bounded by `κ`);
* `r_n(α, δ) = κ/(1−α)·[4/√n + √(2 log(2/δ)/n)]` is the frozen `TrimmedMMD.rn`;
* "with probability at least `1 − δ`" is stated as the existence of a **measurable** event of probability
  `≥ 1 − δ` on which the bound holds (critic: `Measure.real` of a non-measurable set is an outer measure, which
  is strictly weaker; for `cor:uniform` the event is an intersection over uncountably many `α`).
Hashed in `certify/statements.lock` (with its imports); AI agents must not edit this file.
-/

noncomputable section
open MeasureTheory

namespace StatFormal.TrimmedMMD.Concentration

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The trimmed kernel-mean region `𝒞_{α,k}(P)`. -/
def region (φ : 𝒳 → H) (α : ℝ) (P : Measure 𝒳) : Set H :=
  {z | ∃ g : 𝒳 → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x ∧ g x ≤ 1 / (1 - α)) ∧ ∫ x, g x ∂P = 1 ∧
    z = ∫ x, g x • φ x ∂P}

/-- Empirical measure of a sample. -/
def empirical {n : ℕ} (x : Fin n → 𝒳) : Measure 𝒳 :=
  ∑ i, ENNReal.ofReal (1 / n) • Measure.dirac (x i)

namespace Claims

/-- `thm:concentration`: for every `α ∈ [0,1)`, `n ≥ 1`, `δ ∈ (0,1)`, with probability at least `1 − δ`,
`d_H(𝒞_{α,k}(P_n), 𝒞_{α,k}(P)) ≤ r_n(α, δ)`. -/
def concentration : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P : Measure 𝒳) [IsProbabilityMeasure P] (φ : 𝒳 → H) (κ α δ : ℝ)
    (n : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → 1 ≤ n → 0 < δ → δ < 1 →
      ∃ E : Set (Fin n → 𝒳), MeasurableSet E ∧ 1 - δ ≤ (Measure.pi fun _ : Fin n => P).real E ∧
        E ⊆ {x | Metric.hausdorffDist (region φ α (empirical x)) (region φ α P) ≤
          StatFormal.TrimmedMMD.rn κ α δ n}

/-- `cor:uniform`: one event of probability at least `1 − δ` on which the bound holds for every
`α ∈ [0,1)` at once. -/
def uniform_alpha : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P : Measure 𝒳) [IsProbabilityMeasure P] (φ : 𝒳 → H) (κ δ : ℝ)
    (n : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 1 ≤ n → 0 < δ → δ < 1 →
      ∃ E : Set (Fin n → 𝒳), MeasurableSet E ∧ 1 - δ ≤ (Measure.pi fun _ : Fin n => P).real E ∧
        E ⊆ {x | ∀ α, 0 ≤ α → α < 1 →
          Metric.hausdorffDist (region φ α (empirical x)) (region φ α P) ≤
            StatFormal.TrimmedMMD.rn κ α δ n}

/-- `cor:uniform`, the displayed consequence: for fixed `η ∈ (0,1)`,
`Pr(sup_{α ∈ [0, 1−η]} d_H(…) > r_n(1−η, δ)) ≤ δ`, stated as the complementary event. -/
def uniform_sup : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P : Measure 𝒳) [IsProbabilityMeasure P] (φ : 𝒳 → H) (κ δ η : ℝ)
    (n : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 1 ≤ n → 0 < δ → δ < 1 → 0 < η → η < 1 →
      ∃ E : Set (Fin n → 𝒳), MeasurableSet E ∧ 1 - δ ≤ (Measure.pi fun _ : Fin n => P).real E ∧
        E ⊆ {x | ∀ α, 0 ≤ α → α ≤ 1 - η →
          Metric.hausdorffDist (region φ α (empirical x)) (region φ α P) ≤
            StatFormal.TrimmedMMD.rn κ (1 - η) δ n}

end Claims
end StatFormal.TrimmedMMD.Concentration
