import StatFormal.Lib.TIKernel.Profile
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Spectral densities of the Gaussian and Laplace profiles (library, untrusted)

With Mathlib's convention `𝓕 f (ξ) = ∫ 𝐞(−⟪x, ξ⟫) f x dx`, `𝐞 t = e^{2πit}`:

* Gaussian on any finite-dimensional real inner-product space `V` (`d = finrank ℝ V`), `σ > 0`:
  `𝓕[e^{−‖x‖²/(2σ²)}](ξ) = (2πσ²)^{d/2} e^{−2π²σ²‖ξ‖²}` (`fourier_gauss`), from Mathlib's
  `fourier_gaussian_innerProductSpace` at `b = 1/(2σ²)`; hence the spectral density (`specDens_gauss`), which is positive.
* Laplace on `ℝ`: `𝓕[e^{−|x|}](ξ) = 2/(1 + 4π²ξ²)` (`fourier_laplace`): the profile is even, so its transform is the cosine
  transform `2 ∫₀^∞ e^{−y} cos(2πξy) dy = 2 Re ∫₀^∞ e^{(−1 + 2πiξ)y} dy = 2 Re (1 − 2πiξ)⁻¹`.
-/

noncomputable section
open MeasureTheory Filter Topology Set FourierTransform Complex
open scoped ENNReal ComplexConjugate InnerProductSpace RealInnerProductSpace

set_option linter.unusedSectionVars false

namespace StatFormal.TIKernel

open StatFormal.Wave31tp

section Gauss

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

/-- The Gaussian profile `e^{−‖x‖²/(2σ²)}` is continuous. -/
lemma gauss_continuous (σ : ℝ) : Continuous (fun x : V => Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) := by
  fun_prop

/-- The complex Gaussian profile as `cexp (−b ‖x‖²)` with `b = (2σ²)⁻¹`. -/
lemma gauss_cexp_eq (σ : ℝ) :
    (fun x : V => ((Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) : ℝ) : ℂ)) =
      fun x => cexp (-(((2 * σ ^ 2)⁻¹ : ℝ) : ℂ) * (‖x‖ : ℂ) ^ 2) := by
  funext x
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- The Gaussian profile is integrable. -/
lemma gauss_integrable {σ : ℝ} (hσ : 0 < σ) : Integrable (fun x : V => Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) := by
  have hb : 0 < ((((2 * σ ^ 2)⁻¹ : ℝ) : ℂ)).re := by rw [Complex.ofReal_re]; positivity
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V) hb 0 0).re
  refine h.congr (Eventually.of_forall fun x => ?_)
  have := congrFun (gauss_cexp_eq (V := V) σ) x
  simp only [zero_mul, add_zero] at this ⊢
  rw [← this]; rfl

/-- **The Fourier transform of the Gaussian profile** on `V`: `(2πσ²)^{d/2} e^{−2π²σ²‖ξ‖²}`. -/
theorem fourier_gauss {σ : ℝ} (hσ : 0 < σ) (ξ : V) :
    𝓕 (fun x : V => ((Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) : ℝ) : ℂ)) ξ =
      (((2 * Real.pi * σ ^ 2) ^ ((Module.finrank ℝ V : ℝ) / 2) * Real.exp (-2 * Real.pi ^ 2 * σ ^ 2 * ‖ξ‖ ^ 2) : ℝ) : ℂ) := by
  have hb : 0 < ((((2 * σ ^ 2)⁻¹ : ℝ) : ℂ)).re := by rw [Complex.ofReal_re]; positivity
  rw [gauss_cexp_eq σ, fourier_gaussian_innerProductSpace hb ξ]
  have hσ2 : σ ^ 2 ≠ 0 := by positivity
  have hpi : (Real.pi : ℂ) / (((2 * σ ^ 2)⁻¹ : ℝ) : ℂ) = ((2 * Real.pi * σ ^ 2 : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [hpi, show ((Module.finrank ℝ V : ℂ) / 2) = (((Module.finrank ℝ V : ℝ) / 2 : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow (by positivity), Complex.ofReal_mul, Complex.ofReal_exp]
  congr 2
  push_cast
  field_simp

/-- The spectral density of the Gaussian profile: `(2πσ²)^{d/2} e^{−2π²σ²‖ξ‖²}`. -/
theorem specDens_gauss_eq {σ : ℝ} (hσ : 0 < σ) (ξ : V) :
    specDens (fun x : V => Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) ξ =
      (2 * Real.pi * σ ^ 2) ^ ((Module.finrank ℝ V : ℝ) / 2) * Real.exp (-2 * Real.pi ^ 2 * σ ^ 2 * ‖ξ‖ ^ 2) := by
  simp only [specDens]
  rw [fourier_gauss hσ ξ, Complex.ofReal_re]

/-- The Gaussian spectral density is positive. -/
lemma specDens_gauss_pos {σ : ℝ} (hσ : 0 < σ) (ξ : V) :
    0 < specDens (fun x : V => Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) ξ := by
  rw [specDens_gauss_eq hσ]
  positivity

end Gauss

section Laplace

/-- The Laplace profile `e^{−|x|}` on `ℝ` is integrable. -/
lemma laplace_integrable : Integrable (fun x : ℝ => Real.exp (-|x|)) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  constructor
  · refine (integrableOn_exp_Iic 0).congr_fun (fun x hx => ?_) measurableSet_Iic
    simp only [abs_of_nonpos (mem_Iic.mp hx), neg_neg]
  · refine (integrableOn_exp_neg_Ioi 0).congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp only [abs_of_pos (mem_Ioi.mp hx)]

/-- `∫₀^∞ e^{−y} cos(cy) dy = 1/(1 + c²)`. -/
lemma integral_exp_neg_mul_cos (c : ℝ) :
    ∫ y in Ioi (0 : ℝ), Real.exp (-y) * Real.cos (c * y) = 1 / (1 + c ^ 2) := by
  set a : ℂ := -1 + c * Complex.I
  have ha : a.re < 0 := by simp [a]
  have hint : IntegrableOn (fun y : ℝ => Complex.exp (a * y)) (Ioi 0) := integrableOn_exp_mul_complex_Ioi ha 0
  have hI := integral_exp_mul_complex_Ioi ha 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero] at hI
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  have hpt : ∀ y : ℝ, (Complex.exp (a * y)).re = Real.exp (-y) * Real.cos (c * y) := by
    intro y
    rw [Complex.exp_re]
    simp [a]
  simp_rw [hpt] at hre
  rw [hre, hI]
  have hne : a ≠ 0 := fun h => by simpa [h] using ha
  have hns : Complex.normSq a = 1 + c ^ 2 := by simp [a, Complex.normSq_apply]; ring
  rw [neg_div, Complex.neg_re, Complex.div_re, hns]
  simp [a]
  field_simp

/-- **The Fourier transform of the Laplace profile** on `ℝ`: `𝓕[e^{−|x|}](ξ) = 2/(1 + 4π²ξ²)`. -/
theorem fourier_laplace (ξ : ℝ) :
    𝓕 (fun x : ℝ => ((Real.exp (-|x|) : ℝ) : ℂ)) ξ = ((2 / (1 + 4 * Real.pi ^ 2 * ξ ^ 2) : ℝ) : ℂ) := by
  have hev : ∀ z : ℝ, Real.exp (-|-z|) = Real.exp (-|z|) := fun z => by rw [abs_neg]
  rw [fourier_even_real hev laplace_integrable ξ]
  congr 1
  have h1 : ∀ x : ℝ, Real.exp (-|x|) * Real.cos (2 * Real.pi * ⟪x, ξ⟫) =
      (fun y : ℝ => Real.exp (-y) * Real.cos ((2 * Real.pi * ξ) * y)) |x| := by
    intro x
    simp only [RCLike.inner_apply, conj_trivial]
    rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg hx]; ring_nf
    · rw [abs_of_neg hx, show 2 * Real.pi * ξ * -x = -(2 * Real.pi * (ξ * x)) by ring, Real.cos_neg]
  simp_rw [h1]
  rw [integral_comp_abs (f := fun y : ℝ => Real.exp (-y) * Real.cos ((2 * Real.pi * ξ) * y)),
    integral_exp_neg_mul_cos]
  rw [mul_pow]
  field_simp
  ring

end Laplace

end StatFormal.TIKernel
