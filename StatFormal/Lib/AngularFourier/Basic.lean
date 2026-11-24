import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Angular rescaling `ξ = 2πη` and spectral comparisons (library, untrusted)

The paper's angular Fourier transform `ĝ(ξ) = ∫ g e^{−i⟨ξ,x⟩}` is Mathlib's `𝓕 g (ξ/2π)`. This file collects the change of
variables `ξ ↦ (2π)⁻¹ • ξ` on a finite-dimensional real inner-product space `V` with its Lebesgue measure `volume` (`d = finrank`):

* `integral_comp_inv_two_pi_smul`: `∫ g((2π)⁻¹ξ) dξ = (2π)^d ∫ g` (Mathlib's `Measure.integral_comp_smul`);
* `integrable_comp_inv_two_pi_smul`: integrability is preserved;
* `four_pi_sq_mul_norm_inv_two_pi_smul_sq`, `norm_two_pi_smul_sq`: `4π²‖(2π)⁻¹ξ‖² = ‖ξ‖²`, `‖2πη‖² = 4π²‖η‖²`;

and two pointwise-to-integral comparisons in `[0, ∞]` for weights `w > 0`: a lower spectral bound `k ≥ c/w` gives
`∫ a/k ≤ (∫ a w)/c` (`lintegral_div_le_of_lower`), an upper bound `0 < k ≤ C/w` gives `(∫ a w)/C ≤ ∫ a/k`
(`div_le_lintegral_of_upper`). With `a = |f̂|²`, `k` the spectral density and `w = (1 + |ξ|²)^s` these compare the native-space and
Sobolev functionals (Wendland, *Scattered Data Approximation*, Cor. 10.13).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace StatFormal.AngularFourier

section Scaling

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

/-- `∫ g((2π)⁻¹ ξ) dξ = (2π)^d ∫ g`. -/
theorem integral_comp_inv_two_pi_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : V → E) :
    ∫ ξ, g ((2 * Real.pi)⁻¹ • ξ) = (2 * Real.pi) ^ Module.finrank ℝ V • ∫ η, g η := by
  rw [Measure.integral_comp_smul volume g (2 * Real.pi)⁻¹, inv_pow, inv_inv, abs_of_pos (by positivity)]

/-- `ξ ↦ g((2π)⁻¹ ξ)` is integrable when `g` is. -/
theorem integrable_comp_inv_two_pi_smul {E : Type*} [NormedAddCommGroup E] {g : V → E} (hg : Integrable g) :
    Integrable (fun ξ => g ((2 * Real.pi)⁻¹ • ξ)) :=
  hg.comp_smul (inv_ne_zero (by positivity))

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `4π² ‖(2π)⁻¹ ξ‖² = ‖ξ‖²`. -/
theorem four_pi_sq_mul_norm_inv_two_pi_smul_sq (ξ : V) :
    4 * Real.pi ^ 2 * ‖(2 * Real.pi)⁻¹ • ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [norm_smul, Real.norm_of_nonneg (by positivity), mul_pow]
  field_simp
  ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `‖2π η‖² = 4π² ‖η‖²`. -/
theorem norm_two_pi_smul_sq (η : V) : ‖(2 * Real.pi) • η‖ ^ 2 = 4 * Real.pi ^ 2 * ‖η‖ ^ 2 := by
  rw [norm_smul, Real.norm_of_nonneg (by positivity), mul_pow]
  ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `(2π)⁻¹ • (2π) • η = η`. -/
theorem inv_two_pi_smul_two_pi_smul (η : V) : (2 * Real.pi)⁻¹ • (2 * Real.pi) • η = η := by
  rw [smul_smul, inv_mul_cancel₀ (by positivity), one_smul]

end Scaling

section Compare

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- A lower bound `k ≥ c / w` (`c, w > 0`) gives `∫ a / k ≤ (∫ a w) / c` in `[0, ∞]`. -/
theorem lintegral_div_le_of_lower {a : X → ℝ≥0∞} {k w : X → ℝ} {c : ℝ} (hc : 0 < c) (hw : ∀ ξ, 0 < w ξ)
    (hk : ∀ ξ, c * (w ξ)⁻¹ ≤ k ξ) :
    ∫⁻ ξ, a ξ / ENNReal.ofReal (k ξ) ∂μ ≤ (∫⁻ ξ, a ξ * ENNReal.ofReal (w ξ) ∂μ) / ENNReal.ofReal c := by
  rw [div_eq_mul_inv, ← lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hc).ne')]
  refine lintegral_mono fun ξ => ?_
  have hcw : 0 < c * (w ξ)⁻¹ := mul_pos hc (inv_pos.2 (hw ξ))
  have hkpos : 0 < k ξ := hcw.trans_le (hk ξ)
  have hinv : (k ξ)⁻¹ ≤ w ξ * c⁻¹ := by
    calc (k ξ)⁻¹ ≤ (c * (w ξ)⁻¹)⁻¹ := inv_anti₀ hcw (hk ξ)
      _ = w ξ * c⁻¹ := by rw [mul_inv, inv_inv, mul_comm]
  rw [div_eq_mul_inv, mul_assoc, ← ENNReal.ofReal_inv_of_pos hkpos, ← ENNReal.ofReal_inv_of_pos hc,
    ← ENNReal.ofReal_mul (hw ξ).le]
  gcongr

/-- An upper bound `0 < k ≤ C / w` (`C, w > 0`) gives `(∫ a w) / C ≤ ∫ a / k` in `[0, ∞]`. -/
theorem div_le_lintegral_of_upper {a : X → ℝ≥0∞} {k w : X → ℝ} {C : ℝ} (hC : 0 < C) (hw : ∀ ξ, 0 < w ξ)
    (hk0 : ∀ ξ, 0 < k ξ) (hk : ∀ ξ, k ξ ≤ C * (w ξ)⁻¹) :
    (∫⁻ ξ, a ξ * ENNReal.ofReal (w ξ) ∂μ) / ENNReal.ofReal C ≤ ∫⁻ ξ, a ξ / ENNReal.ofReal (k ξ) ∂μ := by
  rw [div_eq_mul_inv, ← lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hC).ne')]
  refine lintegral_mono fun ξ => ?_
  have hinv : w ξ * C⁻¹ ≤ (k ξ)⁻¹ := by
    calc w ξ * C⁻¹ = (C * (w ξ)⁻¹)⁻¹ := by rw [mul_inv, inv_inv, mul_comm]
      _ ≤ (k ξ)⁻¹ := inv_anti₀ (hk0 ξ) (hk ξ)
  rw [div_eq_mul_inv, mul_assoc, ← ENNReal.ofReal_inv_of_pos (hk0 ξ), ← ENNReal.ofReal_inv_of_pos hC,
    ← ENNReal.ofReal_mul (hw ξ).le]
  gcongr

end Compare

/-- For `y ≥ 1`, `min(1, 2^{−s}) · y^{−2s} ≤ (1 + y²)^{−s}`. -/
theorem min_mul_rpow_le_one_add_sq_rpow_neg {y s : ℝ} (hy : 1 ≤ y) :
    min 1 ((2 : ℝ) ^ (-s)) * y ^ (-2 * s) ≤ (1 + y ^ 2) ^ (-s) := by
  have hy0 : 0 < y := by linarith
  have hyy : y ^ (-2 * s) = (y ^ 2) ^ (-s) := by
    rw [show -2 * s = (2 : ℝ) * (-s) by ring, Real.rpow_mul hy0.le, Real.rpow_two]
  rw [hyy]
  rcases le_total 0 s with hs | hs
  · calc min 1 ((2 : ℝ) ^ (-s)) * (y ^ 2) ^ (-s) ≤ (2 : ℝ) ^ (-s) * (y ^ 2) ^ (-s) := by
          gcongr; exact min_le_right _ _
      _ = (2 * y ^ 2) ^ (-s) := (Real.mul_rpow (by norm_num) (by positivity)).symm
      _ ≤ (1 + y ^ 2) ^ (-s) := Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith) (by linarith)
  · calc min 1 ((2 : ℝ) ^ (-s)) * (y ^ 2) ^ (-s) ≤ 1 * (y ^ 2) ^ (-s) := by
          gcongr; exact min_le_left _ _
      _ = (y ^ 2) ^ (-s) := one_mul _
      _ ≤ (1 + y ^ 2) ^ (-s) := Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)

end StatFormal.AngularFourier
