import Mathlib.Probability.Distributions.Gaussian.Real
import StatFormal.Lib.MatchedGrid.Product

/-!
# Second moments of centred real Gaussians
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace StatFormal.Foundations.MatchedGrid

lemma integral_sq_gaussianReal_zero (v : ℝ≥0) : ∫ x, x ^ 2 ∂(gaussianReal 0 v) = v := by
  have h := variance_eq_integral (X := fun x : ℝ => x) (μ := gaussianReal 0 v) measurable_id.aemeasurable
  rw [variance_fun_id_gaussianReal, integral_id_gaussianReal] at h
  simpa using h.symm

lemma lintegral_sq_gaussianReal_zero (v : ℝ≥0) :
    ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂(gaussianReal 0 v) = ENNReal.ofReal v := by
  have hi : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) := (memLp_id_gaussianReal 2).integrable_sq
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun x => sq_nonneg x), integral_sq_gaussianReal_zero]

end StatFormal.Foundations.MatchedGrid
