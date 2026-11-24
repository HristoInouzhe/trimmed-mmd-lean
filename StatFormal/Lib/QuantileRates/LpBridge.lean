import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Quantile rates — `eLpNorm · 2` squared as a lower Lebesgue integral

`‖f‖²_{L²(μ)} = ∫ ‖f‖ₑ²` (Mathlib's `eLpNorm f 2 μ` squared), the real and Euclidean pointwise forms
`‖r‖ₑ² = (r²)⁺`, `‖v‖ₑ² = Σ_k (v_k²)⁺`, and measurability of `ω ↦ eLpNorm (F ω) 2 μ`.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.Foundations.QuantileRates

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma eLpNorm_two_sq {E : Type*} [NormedAddCommGroup E] {f : α → E} (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero hf
  simpa [ENNReal.rpow_two] using h

lemma enorm_sq_real (r : ℝ) : ‖r‖ₑ ^ 2 = ENNReal.ofReal (r ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg r), sq_abs]

lemma enorm_sq_euc {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) :
    ‖v‖ₑ ^ 2 = ∑ k, ENNReal.ofReal (v k ^ 2) := by
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg v), EuclideanSpace.norm_sq_eq,
    ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
  simp [Real.norm_eq_abs, sq_abs]

lemma eLpNorm_two_sq_real {f : α → ℝ} (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ := by
  rw [eLpNorm_two_sq hf]; simp_rw [enorm_sq_real]

lemma eLpNorm_two_sq_euc {d : ℕ} {f : α → EuclideanSpace ℝ (Fin d)} (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ∑ k, ENNReal.ofReal (f x k ^ 2) ∂μ := by
  rw [eLpNorm_two_sq hf]; simp_rw [enorm_sq_euc]

lemma sq_le_sq_iff_ennreal {x y : ℝ≥0∞} : x ^ 2 ≤ y ^ 2 ↔ x ≤ y := by
  constructor
  · intro h
    by_contra hxy
    exact absurd h (not_le.2 (ENNReal.pow_lt_pow_left two_ne_zero (not_le.1 hxy)))
  · intro h; exact pow_le_pow_left₀ zero_le h 2

lemma measurable_eLpNorm_two {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [NormedAddCommGroup E]
    {F : Ω → α → E} (hF : ∀ ω, AEStronglyMeasurable (F ω) μ)
    (hm : Measurable fun ω => ∫⁻ x, ‖F ω x‖ₑ ^ 2 ∂μ) :
    Measurable fun ω => eLpNorm (F ω) 2 μ := by
  have h : (fun ω => eLpNorm (F ω) 2 μ) = fun ω => (∫⁻ x, ‖F ω x‖ₑ ^ 2 ∂μ) ^ (1 / (2 : ℝ)) := by
    funext ω
    have := eLpNorm_nnreal_eq_lintegral (p := 2) two_ne_zero (hF ω)
    simpa [ENNReal.rpow_two] using this
  rw [h]
  exact hm.pow_const _

end StatFormal.Foundations.QuantileRates
