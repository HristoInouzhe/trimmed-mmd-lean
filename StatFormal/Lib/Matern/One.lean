import StatFormal.Lib.Matern.Fourier
import Mathlib.Analysis.Fourier.Inversion

/-!
# The Bessel potential `G₁` on `ℝ` is `e^{−|x|}/2` (library, untrusted)

On `ℝ` (`finrank ℝ ℝ = 1`, so `s = 1 > 1/2`) the Bessel potential `G₁ = Wave31tp.besselPot 1` and the half Laplace profile
`e^{−|x|}/2` are both continuous and integrable, with the same Fourier transform `(1 + 4π²ξ²)⁻¹`
(`Matern.fourier_besselPot`, `TIKernel.fourier_laplace`), which is integrable (`integrable_inv_one_add_four_pi_sq_mul_sq`).
Fourier inversion (`Continuous.fourierInv_fourier_eq`) then gives `G₁ = e^{−|x|}/2` everywhere (`besselPot_one_real`): the Matérn
kernel of smoothness `ν = 1/2` is the Laplace kernel.
-/

noncomputable section
open MeasureTheory Filter Topology Set FourierTransform
open scoped InnerProductSpace RealInnerProductSpace

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace StatFormal.Matern

open StatFormal.Wave31tp

/-- On `ℝ` the exponent `s = 1` exceeds `finrank ℝ ℝ / 2 = 1/2`. -/
lemma finrank_real_half_lt_one : (Module.finrank ℝ ℝ : ℝ) / 2 < 1 := by
  rw [Module.finrank_self]
  norm_num

/-- `ξ ↦ (1 + 4π²ξ²)⁻¹` is integrable on `ℝ`. -/
lemma integrable_inv_one_add_four_pi_sq_mul_sq : Integrable (fun ξ : ℝ => (1 + 4 * Real.pi ^ 2 * ξ ^ 2)⁻¹) := by
  have h := integrable_inv_one_add_sq.comp_mul_left' (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  refine h.congr (Eventually.of_forall fun ξ => ?_)
  simp only
  ring_nf

/-- The transform of `G₁` on `ℝ`: `𝓕 G₁ (ξ) = (1 + 4π²ξ²)⁻¹`. -/
lemma fourier_besselPot_one_real (ξ : ℝ) :
    𝓕 (fun x : ℝ => (besselPot (V := ℝ) 1 x : ℂ)) ξ = (((1 + 4 * Real.pi ^ 2 * ξ ^ 2)⁻¹ : ℝ) : ℂ) := by
  rw [fourier_besselPot finrank_real_half_lt_one ξ, Real.norm_eq_abs, sq_abs, Real.rpow_neg_one]

/-- The transform of the half Laplace profile: `𝓕[e^{−|x|}/2](ξ) = (1 + 4π²ξ²)⁻¹`. -/
lemma fourier_half_laplace (ξ : ℝ) :
    𝓕 (fun x : ℝ => ((Real.exp (-|x|) / 2 : ℝ) : ℂ)) ξ = (((1 + 4 * Real.pi ^ 2 * ξ ^ 2)⁻¹ : ℝ) : ℂ) := by
  have hL := TIKernel.fourier_laplace ξ
  simp only [Real.fourier_eq] at hL
  have hpt : ∀ x : ℝ, 𝐞 (-⟪x, ξ⟫) • ((Real.exp (-|x|) / 2 : ℝ) : ℂ) =
      ((1 / 2 : ℝ) : ℂ) * (𝐞 (-⟪x, ξ⟫) • ((Real.exp (-|x|) : ℝ) : ℂ)) := by
    intro x
    simp only [Circle.smul_def, smul_eq_mul]
    push_cast
    ring
  rw [Real.fourier_eq, integral_congr_ae (Eventually.of_forall hpt), integral_const_mul, hL, ← Complex.ofReal_mul]
  congr 1
  have : 0 < 1 + 4 * Real.pi ^ 2 * ξ ^ 2 := by positivity
  field_simp

/-- **`G₁ = e^{−|x|}/2` on `ℝ`** (the Matérn kernel of smoothness `1/2` is the Laplace kernel), by Fourier inversion. -/
theorem besselPot_one_real (x : ℝ) : besselPot (V := ℝ) 1 x = Real.exp (-|x|) / 2 := by
  set f : ℝ → ℂ := fun x => (besselPot (V := ℝ) 1 x : ℂ) with hf
  set g : ℝ → ℂ := fun x => ((Real.exp (-|x|) / 2 : ℝ) : ℂ) with hg
  have hfg : 𝓕 f = 𝓕 g := by
    funext ξ
    rw [hf, hg, fourier_besselPot_one_real, fourier_half_laplace]
  have hFf : Integrable (𝓕 f) := by
    have : 𝓕 f = fun ξ : ℝ => (((1 + 4 * Real.pi ^ 2 * ξ ^ 2)⁻¹ : ℝ) : ℂ) := funext fourier_besselPot_one_real
    rw [this]
    exact integrable_inv_one_add_four_pi_sq_mul_sq.ofReal
  have hfc : Continuous f := Complex.continuous_ofReal.comp (continuous_besselPot finrank_real_half_lt_one)
  have hfi : Integrable f := (integrable_besselPot finrank_real_half_lt_one).ofReal
  have hgc : Continuous g := Complex.continuous_ofReal.comp (by fun_prop)
  have hgi : Integrable g := (TIKernel.laplace_integrable.div_const 2).ofReal
  have h := congrFun (hfc.fourierInv_fourier_eq hfi hFf) x
  rw [hfg, (hgc.fourierInv_fourier_eq hgi (hfg ▸ hFf))] at h
  exact Complex.ofReal_injective h.symm

end StatFormal.Matern
