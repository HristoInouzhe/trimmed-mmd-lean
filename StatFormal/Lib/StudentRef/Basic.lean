import Mathlib.Probability.Distributions.Gamma
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Probability.Moments.Variance

/-!
# Inverse-gamma means and Parseval for second moments (untrusted library code)

* `lintegral_inv_gammaMeasure`: for `V ∼ Gamma(a, rate r)` with `a > 1`, `E[1/V] = r/(a − 1)` (as a lower Lebesgue
  integral in `[0, ∞]`); hence `E W = ν/(ν − 2)` for `W ∼ InvGamma(ν/2, ν/2)`, `ν > 2`.
* `enorm_sq_eq_tsum`, `lintegral_enorm_sq_eq_tsum`: for a Hilbert basis `(e_k)`,
  `‖x‖² = Σ_k ⟨e_k, x⟩²` and `E‖X‖² = Σ_k E⟨e_k, X⟩²` in `[0, ∞]`.
* `lintegral_sq_eq_variance`: `E⟨v, X⟩² = Var⟨v, X⟩` for a centred square-integrable coordinate.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.StudentRef

lemma gammaPDF_toReal' {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (v : ℝ) :
    (gammaPDF a b v).toReal = gammaPDFReal a b v := by
  rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hb v)]

lemma measurable_gammaPDF' (a b : ℝ) : Measurable (gammaPDF a b) :=
  ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal a b)

/-- `∫⁻ ofReal(1/v) dGamma(a, r) = ofReal(∫_{(0,∞)} gammaPDF(v)/v dv)`, the integrand vanishing off `(0, ∞)`. -/
lemma lintegral_inv_gamma_eq {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∫⁻ v, ENNReal.ofReal v⁻¹ ∂(gammaMeasure a r) =
      ∫⁻ v in Ioi 0, ENNReal.ofReal (r ^ a / Gamma a * (v ^ (a - 1 - 1) * exp (-(r * v)))) := by
  rw [gammaMeasure, lintegral_withDensity_eq_lintegral_mul₀ (measurable_gammaPDF' a r).aemeasurable
    (g := fun v : ℝ => ENNReal.ofReal v⁻¹) (by fun_prop : Measurable fun v : ℝ => ENNReal.ofReal v⁻¹).aemeasurable]
  have hsplit : ∀ v : ℝ, (gammaPDF a r * fun v => ENNReal.ofReal v⁻¹) v =
      (Ioi (0 : ℝ)).indicator
        (fun v => ENNReal.ofReal (r ^ a / Gamma a * (v ^ (a - 1 - 1) * exp (-(r * v))))) v := by
    intro v
    simp only [Pi.mul_apply]
    by_cases hv : 0 < v
    · rw [indicator_of_mem (show v ∈ Ioi (0 : ℝ) from hv), gammaPDF, ← ENNReal.ofReal_mul
        (gammaPDFReal_nonneg ha hr v), gammaPDFReal, if_pos hv.le]
      congr 1
      rw [rpow_sub hv, rpow_one, rpow_sub hv, rpow_one]
      field_simp
      rw [mul_comm, ← rpow_add_one hv.ne', sub_add_cancel]
    · rw [indicator_of_notMem (show v ∉ Ioi (0 : ℝ) from hv)]
      rcases (not_lt.1 hv).lt_or_eq with h | h
      · simp [gammaPDF, gammaPDFReal, not_le.2 h]
      · rw [h]; simp
  simp_rw [hsplit]
  rw [lintegral_indicator measurableSet_Ioi]

/-- **Inverse-gamma mean.** For `V ∼ Gamma(a, r)` with `a > 1`, `E[1/V] = r/(a − 1)`. -/
theorem lintegral_inv_gammaMeasure {a r : ℝ} (ha : 1 < a) (hr : 0 < r) :
    ∫⁻ v, ENNReal.ofReal v⁻¹ ∂(gammaMeasure a r) = ENNReal.ofReal (r / (a - 1)) := by
  have ha0 : 0 < a := by linarith
  have ha1 : 0 < a - 1 := by linarith
  rw [lintegral_inv_gamma_eq ha0 hr]
  have hint : IntegrableOn (fun v : ℝ => r ^ a / Gamma a * (v ^ (a - 1 - 1) * exp (-(r * v)))) (Ioi 0) := by
    refine Integrable.const_mul ?_ _
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := a - 1 - 1) (p := 1) (b := r) (by linarith) one_pos hr
    refine this.congr_fun (fun v hv => ?_) measurableSet_Ioi
    simp only [rpow_one, neg_mul]
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    rw [integral_const_mul, integral_rpow_mul_exp_neg_mul_Ioi ha1 hr]
    have hG : Gamma a = (a - 1) * Gamma (a - 1) := by
      have := Real.Gamma_add_one (s := a - 1) ha1.ne'
      rw [sub_add_cancel] at this
      exact this
    have hGp : 0 < Gamma (a - 1) := Real.Gamma_pos_of_pos ha1
    rw [hG, one_div, inv_rpow hr.le, ← rpow_neg hr.le]
    have hrr : r ^ a * r ^ (-(a - 1)) = r := by
      rw [← rpow_add hr]; simp
    field_simp
    exact hrr
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun v hv => ?_)
    have hv : 0 < v := hv
    positivity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **Parseval** in `[0, ∞]`: `‖x‖² = Σ_k ⟨e_k, x⟩²`. -/
lemma enorm_sq_eq_tsum (e : HilbertBasis ℕ ℝ H) (x : H) :
    ‖x‖ₑ ^ 2 = ∑' k, ENNReal.ofReal (⟪e k, x⟫ ^ 2) := by
  have hs := e.summable_inner_mul_inner x x
  have ht := e.tsum_inner_mul_inner x x
  have heq : (fun k => ⟪x, e k⟫ * ⟪e k, x⟫) = fun k => ⟪e k, x⟫ ^ 2 := by
    funext k; rw [real_inner_comm x (e k)]; ring
  rw [heq] at hs ht
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) hs, ht, real_inner_self_eq_norm_sq,
    ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]

variable [MeasurableSpace H] [OpensMeasurableSpace H]

/-- `E‖X‖² = Σ_k E⟨e_k, X⟩²` in `[0, ∞]`. -/
lemma lintegral_enorm_sq_eq_tsum {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (e : HilbertBasis ℕ ℝ H)
    {X : Ω → H} (hX : Measurable X) :
    ∫⁻ ω, ‖X ω‖ₑ ^ 2 ∂P = ∑' k, ∫⁻ ω, ENNReal.ofReal (⟪e k, X ω⟫ ^ 2) ∂P := by
  simp_rw [enorm_sq_eq_tsum e]
  refine lintegral_tsum fun k => ?_
  exact (ENNReal.measurable_ofReal.comp
    (((continuous_const.inner continuous_id).measurable.comp hX).pow_const 2)).aemeasurable

/-- `E⟨v, X⟩² = Var⟨v, X⟩` in `[0, ∞]` for a centred square-integrable coordinate. -/
lemma lintegral_sq_eq_variance {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {Y : Ω → ℝ}
    (hY : MemLp Y 2 P) (h0 : ∫ ω, Y ω ∂P = 0) :
    ∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂P = ENNReal.ofReal (Var[Y; P]) := by
  rw [variance_of_integral_eq_zero hY.aemeasurable h0,
    ofReal_integral_eq_lintegral_ofReal hY.integrable_sq (Filter.Eventually.of_forall fun ω => sq_nonneg _)]

end StatFormal.StudentRef
