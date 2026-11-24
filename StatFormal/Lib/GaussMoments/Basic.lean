import StatFormal.Wave31tp.Statements
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Moments of the Gaussian spectral density on `ℝ` (library, untrusted)

For `σ > 0` the Gaussian profile `k₀(x) = e^{−x²/(2σ²)}` has Fourier transform `𝓕k₀(ξ) = σ√(2π) e^{−2π²σ²ξ²}` (Mathlib's
`fourier_gaussian_pi`), and its even angular moments are those of `N(0, σ^{−2})`:
`∫ (2πξ)^{2N} 𝓕k₀(ξ) dξ = (2N − 1)‼ σ^{−2N}` (paper S4 :896, :935).

Route. `∫_ℝ x^{2n} e^{−bx²} = 2 ∫_0^∞ x^{2n} e^{−bx²} = b^{−(n+1/2)} Γ(n + 1/2)` (`integral_comp_abs`,
`integral_rpow_mul_exp_neg_mul_rpow` with `p = 2`) and `Γ(n + 1/2) = (2n − 1)‼ √π / 2^n` (`Real.Gamma_nat_add_half`); then
`b = 2π²σ²` and the constants cancel. At `N = 0`, `(2·0 − 1)‼ = 0‼ = 1`.

* `integral_pow_mul_exp_neg_mul_sq`: `∫ x^{2n} e^{−bx²} = (2n − 1)‼ √π / (2^n b^n √b)`;
* `fourier_gauss_profile`, `specDens_gauss`: the Fourier transform and the spectral density of `k₀`;
* `integrable_gauss_spec_moment`, `integral_gauss_spec_moment`: L23.
-/

set_option linter.style.longLine false

noncomputable section
open Real MeasureTheory Set Complex
open scoped Nat FourierTransform

namespace StatFormal.GaussMoments

open StatFormal.Wave31tp

/-- Even moments of `e^{−bx²}` on the half-line, in Gamma form. -/
lemma integral_Ioi_pow_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) (n : ℕ) :
    ∫ x in Ioi (0 : ℝ), x ^ (2 * n) * Real.exp (-b * x ^ 2) =
      b ^ (-(((2 * n : ℕ) : ℝ) + 1) / 2) * (1 / 2) * Real.Gamma ((((2 * n : ℕ) : ℝ) + 1) / 2) := by
  have hq : (-1 : ℝ) < ((2 * n : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  rw [← integral_rpow_mul_exp_neg_mul_rpow two_pos hq hb]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  simp only [Real.rpow_natCast, Real.rpow_two]

/-- **Even Gaussian moments.** `∫_ℝ x^{2n} e^{−bx²} dx = (2n − 1)‼ √π / (2^n b^n √b)` for `b > 0`. -/
theorem integral_pow_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) (n : ℕ) :
    ∫ x : ℝ, x ^ (2 * n) * Real.exp (-b * x ^ 2) = ((2 * n - 1)‼ : ℝ) * √π / (2 ^ n * (b ^ n * √b)) := by
  have h1 : ∫ x : ℝ, x ^ (2 * n) * Real.exp (-b * x ^ 2) =
      ∫ x : ℝ, |x| ^ (2 * n) * Real.exp (-b * |x| ^ 2) := by
    congr 1
    funext x
    simp only [pow_mul, sq_abs]
  have hgam : (((2 * n : ℕ) : ℝ) + 1) / 2 = (n : ℝ) + 1 / 2 := by push_cast; ring
  have hexp : b ^ (-(((2 * n : ℕ) : ℝ) + 1) / 2) = (b ^ n * √b)⁻¹ := by
    rw [show -(((2 * n : ℕ) : ℝ) + 1) / 2 = -((n : ℝ) + 1 / 2) by push_cast; ring, rpow_neg hb.le, rpow_add hb,
      rpow_natCast, ← sqrt_eq_rpow]
  rw [h1, integral_comp_abs (f := fun y : ℝ => y ^ (2 * n) * Real.exp (-b * y ^ 2)),
    integral_Ioi_pow_mul_exp_neg_mul_sq hb, hgam, hexp, Real.Gamma_nat_add_half]
  have : 0 < √b := Real.sqrt_pos.mpr hb
  field_simp

/-- The Fourier transform of the Gaussian profile on `ℝ`: `𝓕[e^{−x²/(2σ²)}](ξ) = σ√(2π) e^{−2π²σ²ξ²}`. -/
theorem fourier_gauss_profile {σ : ℝ} (hσ : 0 < σ) (ξ : ℝ) :
    𝓕 (fun x : ℝ => ((Real.exp (-x ^ 2 / (2 * σ ^ 2)) : ℝ) : ℂ)) ξ =
      ((σ * √(2 * π) * Real.exp (-(2 * π ^ 2 * σ ^ 2) * ξ ^ 2) : ℝ) : ℂ) := by
  have hb : 0 < (2 * π * σ ^ 2)⁻¹ := by positivity
  have hfun : (fun x : ℝ => ((Real.exp (-x ^ 2 / (2 * σ ^ 2)) : ℝ) : ℂ)) =
      fun x : ℝ => cexp (-π * (((2 * π * σ ^ 2)⁻¹ : ℝ) : ℂ) * x ^ 2) := by
    funext x
    rw [ofReal_exp]
    congr 1
    push_cast
    field_simp
  rw [hfun, fourier_gaussian_pi (by rw [ofReal_re]; exact hb)]
  have hcpow : ((((2 * π * σ ^ 2)⁻¹ : ℝ) : ℂ)) ^ (1 / 2 : ℂ) = ((√((2 * π * σ ^ 2)⁻¹) : ℝ) : ℂ) := by
    rw [sqrt_eq_rpow, ofReal_cpow hb.le]
    push_cast
    rfl
  have hsq : √((2 * π * σ ^ 2)⁻¹) = (σ * √(2 * π))⁻¹ := by
    rw [Real.sqrt_inv, show 2 * π * σ ^ 2 = (σ * √(2 * π)) ^ 2 by
      rw [mul_pow, sq_sqrt (by positivity)]; ring, sqrt_sq (by positivity)]
  rw [hcpow, hsq]
  push_cast
  congr 1
  · field_simp
  · congr 1
    field_simp

/-- The spectral density of the Gaussian profile on `ℝ`: `specDens k₀ ξ = σ√(2π) e^{−2π²σ²ξ²}`. -/
theorem specDens_gauss {σ : ℝ} (hσ : 0 < σ) (ξ : ℝ) :
    specDens (fun x : ℝ => Real.exp (-x ^ 2 / (2 * σ ^ 2))) ξ =
      σ * √(2 * π) * Real.exp (-(2 * π ^ 2 * σ ^ 2) * ξ ^ 2) := by
  simp only [specDens]
  rw [fourier_gauss_profile hσ ξ, ofReal_re]

lemma gauss_spec_moment_eq {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (ξ : ℝ) :
    (2 * π * ξ) ^ (2 * N) * specDens (fun x : ℝ => Real.exp (-x ^ 2 / (2 * σ ^ 2))) ξ =
      ((2 * π) ^ (2 * N) * (σ * √(2 * π))) * (ξ ^ (2 * N) * Real.exp (-(2 * π ^ 2 * σ ^ 2) * ξ ^ 2)) := by
  rw [specDens_gauss hσ, mul_pow]
  ring

/-- The even angular moments of the Gaussian spectral density are finite. -/
theorem integrable_gauss_spec_moment {σ : ℝ} (hσ : 0 < σ) (N : ℕ) :
    Integrable (fun ξ : ℝ => (2 * π * ξ) ^ (2 * N) * specDens (fun x : ℝ => Real.exp (-x ^ 2 / (2 * σ ^ 2))) ξ) := by
  have hb : 0 < 2 * π ^ 2 * σ ^ 2 := by positivity
  have hq : (-1 : ℝ) < ((2 * N : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ ((2 * N : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have h := (integrable_rpow_mul_exp_neg_mul_sq hb hq).const_mul ((2 * π) ^ (2 * N) * (σ * √(2 * π)))
  simp only [Real.rpow_natCast] at h
  simp_rw [gauss_spec_moment_eq hσ N]
  exact h

/-- **Moments of the Gaussian spectral density (L23).** `∫ (2πξ)^{2N} 𝓕k₀(ξ) dξ = (2N − 1)‼ σ^{−2N}` for
`k₀(x) = e^{−x²/(2σ²)}`, `σ > 0`. -/
theorem integral_gauss_spec_moment {σ : ℝ} (hσ : 0 < σ) (N : ℕ) :
    ∫ ξ : ℝ, (2 * π * ξ) ^ (2 * N) * specDens (fun x : ℝ => Real.exp (-x ^ 2 / (2 * σ ^ 2))) ξ =
      ((2 * N - 1)‼ : ℝ) * σ⁻¹ ^ (2 * N) := by
  have hb : 0 < 2 * π ^ 2 * σ ^ 2 := by positivity
  simp_rw [gauss_spec_moment_eq hσ N]
  rw [integral_const_mul, integral_pow_mul_exp_neg_mul_sq hb N]
  have hsb : √(2 * π ^ 2 * σ ^ 2) = √2 * (π * σ) := by
    rw [show 2 * π ^ 2 * σ ^ 2 = 2 * (π * σ) ^ 2 by ring, Real.sqrt_mul (by norm_num),
      sqrt_sq (by positivity)]
  have h2pi : √(2 * π) = √2 * √π := Real.sqrt_mul (by norm_num) π
  have hpi : √π ^ 2 = π := sq_sqrt pi_pos.le
  have h2 : 0 < √2 := by positivity
  have hpi0 : 0 < √π := Real.sqrt_pos.mpr pi_pos
  rw [hsb, h2pi, inv_pow]
  field_simp
  rw [mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, pow_mul (2 : ℝ) 2 N]
  ring_nf
  rw [hpi]
  ring_nf
  rw [show (4 : ℝ) ^ N = 2 ^ (N * 2) by rw [mul_comm, pow_mul]; norm_num]

end StatFormal.GaussMoments
