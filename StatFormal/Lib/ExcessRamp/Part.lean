import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Parts of a measure given by a density with values in `[0,1]`

Library component (trimmed-mmd, the closest parts `P′ = (1−α)g·P` of Lemmas S4.17–S4.18). Untrusted library code.

For a measurable `γ : Ω → [0,1]`, the measure `γ·μ = μ.withDensity (ofReal ∘ γ)` is a part of `μ` (`γ·μ ≤ μ`) of mass `∫ γ dμ`, and
`∫ f d(γ·μ) = ∫ γ f dμ`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.ExcessRamp

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A density with values `≤ 1` gives a part: `γ·μ ≤ μ`. -/
theorem withDensity_ofReal_le (μ : Measure Ω) {γ : Ω → ℝ} (h1 : ∀ x, γ x ≤ 1) :
    μ.withDensity (fun x => ENNReal.ofReal (γ x)) ≤ μ := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [withDensity_apply _ hs]
  calc ∫⁻ x in s, ENNReal.ofReal (γ x) ∂μ ≤ ∫⁻ _ in s, 1 ∂μ :=
        lintegral_mono fun x => ENNReal.ofReal_le_one.2 (h1 x)
    _ = μ s := by rw [setLIntegral_const, one_mul]

/-- The mass of the part `γ·μ` is `∫ γ dμ`. -/
theorem withDensity_ofReal_real_univ (μ : Measure Ω) [IsFiniteMeasure μ] {γ : Ω → ℝ} (hγ : Measurable γ)
    (h0 : ∀ x, 0 ≤ γ x) (h1 : ∀ x, γ x ≤ 1) :
    (μ.withDensity fun x => ENNReal.ofReal (γ x)).real univ = ∫ x, γ x ∂μ := by
  have hint : Integrable γ μ := Integrable.of_mem_Icc 0 1 hγ.aemeasurable (ae_of_all _ fun x => ⟨h0 x, h1 x⟩)
  rw [measureReal_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ h0), ENNReal.toReal_ofReal (integral_nonneg h0)]

/-- Integrals against the part `γ·μ`: `∫ f d(γ·μ) = ∫ γ f dμ`. -/
theorem integral_withDensity_ofReal (μ : Measure Ω) {γ : Ω → ℝ} (hγ : Measurable γ) (h0 : ∀ x, 0 ≤ γ x)
    (f : Ω → ℝ) : ∫ x, f x ∂(μ.withDensity fun x => ENNReal.ofReal (γ x)) = ∫ x, γ x * f x ∂μ := by
  have hfun : (fun x => ENNReal.ofReal (γ x)) = fun x => ((γ x).toNNReal : ℝ≥0∞) := rfl
  rw [hfun, integral_withDensity_eq_integral_smul hγ.real_toNNReal f]
  congr 1; funext x
  rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (h0 x)]

end StatFormal.ExcessRamp
