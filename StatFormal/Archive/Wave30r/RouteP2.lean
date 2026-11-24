import StatFormal.Archive.Wave30r.Statements
import StatFormal.Archive.Wave8a.RouteSharp
import StatFormal.Lib.EntropicPlan.Quadratic

set_option linter.style.longLine false

/-!
# Wave 30r route: `lem:sharp` for the entropic plan with `𝒫₂` marginals (journal and FAccT objectives)

The entropic library `Foundations/EntropicPlan` (existence, uniqueness, positive density for any cost with
`∫ c d(μ⊗ν) < ∞`), applied to `‖x − y‖²` and `½‖x − y‖²` (integrable against `R ⊗ ν` for `R, ν ∈ 𝒫₂`,
`EntropicPlan.Quadratic`), and the certified Wave 8a `sharp_density`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti Set InformationTheory
open scoped ENNReal NNReal

namespace StatFormal.Wave30r

open StatFormal.Wave8a StatFormal.Foundations.EntropicPlan

variable {d : ℕ}

theorem measurable_halfQuadCost : Measurable (halfQuadCost (d := d)) :=
  measurable_quadCost.div_const 2

theorem lintegral_quadCost_ne_top {R ν : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure R]
    [IsProbabilityMeasure ν] (hR : HasFiniteMoment 2 R) (hν : HasFiniteMoment 2 ν) :
    ∫⁻ z, quadCost z ∂(R.prod ν) ≠ ∞ :=
  lintegral_sqdist_prod_ne_top hR hν

theorem lintegral_halfQuadCost_ne_top {R ν : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure R]
    [IsProbabilityMeasure ν] (hR : HasFiniteMoment 2 R) (hν : HasFiniteMoment 2 ν) :
    ∫⁻ z, halfQuadCost z ∂(R.prod ν) ≠ ∞ :=
  ne_top_of_le_ne_top (lintegral_quadCost_ne_top hR hν) (lintegral_mono fun _ => ENNReal.half_le_self)

/-- The common skeleton: for a measurable cost integrable against `R ⊗ ν`, the entropic plan exists, is unique, and
for every version of its barycentric projection `T_#R = ν` iff `ν` is Dirac (`ν ∈ 𝒫₂`). -/
theorem sharp_of_cost {R ν : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure R] [IsProbabilityMeasure ν]
    {c : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞} {ε : ℝ≥0} (hc : Measurable c)
    (hcP : ∫⁻ z, c z ∂(R.prod ν) ≠ ∞) (hν : HasFiniteMoment 2 ν) (hε : ε ≠ 0) :
    (∃! π, IsCoupling π R ν ∧ ∫⁻ z, c z ∂π + ε * klDiv π (R.prod ν) = entropicTransportCost c ε R ν) ∧
      ∀ (π : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)))
        (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
        (IsCoupling π R ν ∧ ∫⁻ z, c z ∂π + ε * klDiv π (R.prod ν) = entropicTransportCost c ε R ν) →
          IsBaryProj π T → (R.map T = ν ↔ ∃ y, ν = Measure.dirac y) := by
  refine ⟨?_, fun π T hπ hT => ?_⟩
  · obtain ⟨π, hπc, hπo⟩ := exists_entropicPlan hc.aemeasurable hε hcP
    exact ⟨π, ⟨hπc, hπo⟩, fun σ hσ => entropicPlan_unique hc.aemeasurable hε hcP hσ.1 hσ.2 hπc hπo⟩
  · obtain ⟨f, hf, hpos, hπf⟩ := entropicPlan_eq_withDensity hε hcP hπ.1 hπ.2
    exact sharp_density d R ν π T f hπ.1 hν hT hf hpos hπf

theorem sharp_P2 : Claims.sharp_P2 := by
  intro d R ν _ _ ε hR hν hε
  exact sharp_of_cost measurable_quadCost (lintegral_quadCost_ne_top hR hν) hν hε

theorem sharp_P2_density : Claims.sharp_P2_density := by
  intro d R ν _ _ ε hR hν hε π hπ
  exact entropicPlan_eq_withDensity hε (lintegral_quadCost_ne_top hR hν) hπ.1 hπ.2

theorem sharp_facct : Claims.sharp_facct := by
  intro d μ ν _ _ ε hμ hν hε
  exact sharp_of_cost measurable_halfQuadCost (lintegral_halfQuadCost_ne_top hμ hν) hν hε

end StatFormal.Wave30r
