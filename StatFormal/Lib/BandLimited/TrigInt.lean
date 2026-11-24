import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Fourier.FourierTransform

/-!
# Trigonometric integrals over symmetric intervals, and Fourier transforms of real functions with compact support
(library, untrusted)

* `∫_{−a}^{a} cos(kw) dw = 2 sin(ka)/k` (`k ≠ 0`), `= 2a` (`k = 0`); odd integrands integrate to `0` over `[−a, a]`;
* for a real `f` vanishing off `[−a, a]` and integrable there, `𝓕 f(t) = ∫_{−a}^{a} cos(2πtw) f(w) dw − i ∫_{−a}^{a} sin(2πtw) f(w) dw`
  (Mathlib's convention `𝓕 f(t) = ∫ e^{−2πiwt} f(w) dw`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set FourierTransform

namespace StatFormal.BandLimited

/-- `∫_{−a}^{a} cos(kw) dw = 2 sin(ka)/k` for `k ≠ 0`. -/
theorem integral_cos_mul_symm {k : ℝ} (hk : k ≠ 0) (a : ℝ) :
    ∫ w in -a..a, Real.cos (k * w) = 2 * Real.sin (k * a) / k := by
  rw [intervalIntegral.integral_comp_mul_left (fun v => Real.cos v) hk, integral_cos, smul_eq_mul, mul_neg,
    Real.sin_neg]
  field_simp
  ring

/-- `∫_{−a}^{a} cos(0·w) dw = 2a`. -/
theorem integral_cos_zero_mul_symm (a : ℝ) : ∫ w in -a..a, Real.cos (0 * w) = 2 * a := by
  simp only [zero_mul, Real.cos_zero, intervalIntegral.integral_const, smul_eq_mul, mul_one]
  ring

/-- Odd functions integrate to `0` over `[−a, a]`. -/
theorem integral_odd_symm {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x) (a : ℝ) : ∫ x in -a..a, f x = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := -a) (b := a) f
  simp only [neg_neg, hodd, intervalIntegral.integral_neg] at h
  linarith

/-- The complex exponential against a real number: `e^{−iθ} x = cos θ x − i sin θ x`. -/
theorem cexp_neg_smul_ofReal (θ x : ℝ) :
    Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) • (x : ℂ) =
      ((Real.cos θ * x : ℝ) : ℂ) - ((Real.sin θ * x : ℝ) : ℂ) * Complex.I := by
  rw [Complex.exp_mul_I, smul_eq_mul, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

/-- **The Fourier transform of a real function supported in `[−a, a]`**:
`𝓕 f(t) = ∫_{−a}^{a} cos(2πtw) f(w) dw − i ∫_{−a}^{a} sin(2πtw) f(w) dw`. -/
theorem fourier_ofReal_of_support {f : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a) (hfi : IntervalIntegrable f MeasureTheory.volume (-a) a)
    (hsupp : ∀ w, w ∉ Icc (-a) a → f w = 0) (t : ℝ) :
    𝓕 (fun w => (f w : ℂ)) t =
      ((∫ w in -a..a, Real.cos (2 * Real.pi * t * w) * f w : ℝ) : ℂ) -
        ((∫ w in -a..a, Real.sin (2 * Real.pi * t * w) * f w : ℝ) : ℂ) * Complex.I := by
  have hpt : ∀ w, Complex.exp (((-2 * Real.pi * w * t : ℝ) : ℂ) * Complex.I) • (f w : ℂ) =
      ((Real.cos (2 * Real.pi * t * w) * f w : ℝ) : ℂ) - ((Real.sin (2 * Real.pi * t * w) * f w : ℝ) : ℂ) * Complex.I := by
    intro w
    rw [show (-2 * Real.pi * w * t : ℝ) = -(2 * Real.pi * t * w) by ring, cexp_neg_smul_ofReal]
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hcomp : ∫ w, Complex.exp (((-2 * Real.pi * w * t : ℝ) : ℂ) * Complex.I) • (f w : ℂ) =
      ∫ w in Icc (-a) a, Complex.exp (((-2 * Real.pi * w * t : ℝ) : ℂ) * Complex.I) • (f w : ℂ) := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw => ?_).symm
    rw [hsupp w hw]; simp
  have hneg : -a ≤ a := by linarith
  rw [hcomp, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hneg]
  simp_rw [hpt]
  have hci : IntervalIntegrable (fun w => Real.cos (2 * Real.pi * t * w) * f w) MeasureTheory.volume (-a) a :=
    hfi.continuousOn_mul (by fun_prop)
  have hsi : IntervalIntegrable (fun w => Real.sin (2 * Real.pi * t * w) * f w) MeasureTheory.volume (-a) a :=
    hfi.continuousOn_mul (by fun_prop)
  have hci' : IntervalIntegrable (fun w => ((Real.cos (2 * Real.pi * t * w) * f w : ℝ) : ℂ)) MeasureTheory.volume (-a) a :=
    ⟨hci.1.ofReal, hci.2.ofReal⟩
  have hsi' : IntervalIntegrable (fun w => ((Real.sin (2 * Real.pi * t * w) * f w : ℝ) : ℂ)) MeasureTheory.volume (-a) a :=
    ⟨hsi.1.ofReal, hsi.2.ofReal⟩
  rw [intervalIntegral.integral_sub hci' (hsi'.mul_const _), intervalIntegral.integral_mul_const,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]

end StatFormal.BandLimited
