import StatFormal.Lib.BandLimited.BandTrig
import StatFormal.Wave31tp.Proofs
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Fourier transforms of the band-limited function `h` (library, untrusted)

In Mathlib's convention (`𝓕 f(t) = ∫ e^{−2πiwt} f(w) dw`), let `a = 1/(4π)` and

* `c(w) = cos(2π² clamp_a(w))` (`bandC`): `cos(2π²w)` on `[−a, a]` and `0` off it (`cos(±π/2) = 0`), continuous, even, compactly
  supported — the paper's `ĥ(ξ) = cos(πξ)1_{[−1/2,1/2]}(ξ)` at `ξ = 2πw`;
* `g(w) = −2π² sin(2π²w) 1_{[−a,a]}(w)` (`bandG`), the derivative of `c` on `(−a, a)`.

Then `𝓕 c = h` and `𝓕 g(t) = 2πi t h(t)` (`Lib/BandLimited/BandTrig` and `TrigInt.fourier_ofReal_of_support`), so by Plancherel
(31tp L1) `∫ h² = ∫ c² = a = 1/(4π)` and `4π² ∫ t² h(t)² dt = ∫ g² = 4π⁴a`, i.e. `∫ t² h² = π/4`; `h = O(t^{−2})` is integrable,
and Fourier inversion (Mathlib's `Continuous.fourier_fourierInv_eq`, `c` even) gives `𝓕 h = c`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set FourierTransform

namespace StatFormal.BandLimited

open StatFormal.Wave31tq

/-- The clamp to `[−a, a]`. -/
def bandClamp (w : ℝ) : ℝ := max (-bandA) (min w bandA)

/-- `c(w) = cos(2π² clamp_a(w))`: the transform of `h` in Mathlib's convention. -/
def bandC (w : ℝ) : ℝ := Real.cos (2 * Real.pi ^ 2 * bandClamp w)

/-- `g(w) = −2π² sin(2π²w)` on `[−a, a]`, `0` off it. -/
def bandG (w : ℝ) : ℝ := (Icc (-bandA) bandA).indicator (fun w => -(2 * Real.pi ^ 2) * Real.sin (2 * Real.pi ^ 2 * w)) w

theorem bandC_of_mem {w : ℝ} (hw : w ∈ Icc (-bandA) bandA) : bandC w = Real.cos (2 * Real.pi ^ 2 * w) := by
  unfold bandC bandClamp
  rw [min_eq_left hw.2, max_eq_right hw.1]

theorem bandC_of_notMem {w : ℝ} (hw : w ∉ Icc (-bandA) bandA) : bandC w = 0 := by
  unfold bandC bandClamp
  have hA := bandA_pos
  rcases not_and_or.1 hw with h | h
  · push Not at h
    rw [min_eq_left (by linarith), max_eq_left h.le, mul_neg, two_pi_sq_mul_bandA, Real.cos_neg, Real.cos_pi_div_two]
  · push Not at h
    rw [min_eq_right h.le, max_eq_right (by linarith), two_pi_sq_mul_bandA, Real.cos_pi_div_two]

theorem continuous_bandC : Continuous bandC := by
  unfold bandC bandClamp; fun_prop

theorem bandC_neg (w : ℝ) : bandC (-w) = bandC w := by
  by_cases hw : w ∈ Icc (-bandA) bandA
  · have hw' : -w ∈ Icc (-bandA) bandA := ⟨by linarith [hw.2], by linarith [hw.1]⟩
    rw [bandC_of_mem hw, bandC_of_mem hw', mul_neg, Real.cos_neg]
  · have hw' : -w ∉ Icc (-bandA) bandA := fun h => hw ⟨by linarith [h.2], by linarith [h.1]⟩
    rw [bandC_of_notMem hw, bandC_of_notMem hw']

theorem hasCompactSupport_bandC : HasCompactSupport bandC :=
  HasCompactSupport.intro isCompact_Icc fun _ hw => bandC_of_notMem hw

theorem bandG_neg (w : ℝ) : bandG (-w) = -bandG w := by
  unfold bandG
  by_cases hw : w ∈ Icc (-bandA) bandA
  · have hw' : -w ∈ Icc (-bandA) bandA := ⟨by linarith [hw.2], by linarith [hw.1]⟩
    rw [indicator_of_mem hw, indicator_of_mem hw', mul_neg, Real.sin_neg]; ring
  · have hw' : -w ∉ Icc (-bandA) bandA := fun h => hw ⟨by linarith [h.2], by linarith [h.1]⟩
    rw [indicator_of_notMem hw, indicator_of_notMem hw', neg_zero]

theorem integrable_bandG : Integrable bandG :=
  (integrable_indicator_iff measurableSet_Icc).2 ((by fun_prop : Continuous fun w : ℝ =>
    -(2 * Real.pi ^ 2) * Real.sin (2 * Real.pi ^ 2 * w)).integrableOn_Icc)

theorem memLp_bandG_ofReal : MemLp (fun w => (bandG w : ℂ)) 2 := by
  have hm : AEStronglyMeasurable (fun w => (bandG w : ℂ)) volume :=
    (Complex.continuous_ofReal.measurable.comp_aemeasurable integrable_bandG.aemeasurable).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
  have hdom : Integrable (fun w => (Icc (-bandA) bandA).indicator (fun _ => (2 * Real.pi ^ 2) ^ 2) w) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp [Real.volume_Icc]))
  refine hdom.mono' (hm.norm.pow 2) (Filter.Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Complex.norm_real, Real.norm_eq_abs, sq_abs]
  unfold bandG
  by_cases hw : w ∈ Icc (-bandA) bandA
  · rw [indicator_of_mem hw, indicator_of_mem hw]
    have hs : Real.sin (2 * Real.pi ^ 2 * w) ^ 2 ≤ 1 := Real.sin_sq_le_one _
    have h1 : (-(2 * Real.pi ^ 2) * Real.sin (2 * Real.pi ^ 2 * w)) ^ 2 =
        (2 * Real.pi ^ 2) ^ 2 * Real.sin (2 * Real.pi ^ 2 * w) ^ 2 := by ring
    rw [h1]
    nlinarith [sq_nonneg (2 * Real.pi ^ 2)]
  · rw [indicator_of_notMem hw, indicator_of_notMem hw]; simp

/-- **`𝓕 c = h`**. -/
theorem fourier_bandC (t : ℝ) : 𝓕 (fun w => (bandC w : ℂ)) t = (bandH t : ℂ) := by
  rw [fourier_ofReal_of_support bandA_pos.le (continuous_bandC.intervalIntegrable _ _) (fun w hw => bandC_of_notMem hw) t]
  have hcos : ∫ w in -bandA..bandA, Real.cos (2 * Real.pi * t * w) * bandC w = bandH t := by
    rw [← integral_cos_cos_band t]
    refine intervalIntegral.integral_congr fun w hw => ?_
    rw [uIcc_of_le (by linarith [bandA_pos])] at hw
    simp only [bandC_of_mem hw]
  have hsin : ∫ w in -bandA..bandA, Real.sin (2 * Real.pi * t * w) * bandC w = 0 :=
    integral_odd_symm (fun w => by rw [bandC_neg, mul_neg, Real.sin_neg]; ring) _
  rw [hcos, hsin]; simp

/-- **`𝓕 g(t) = 2πi t h(t)`**. -/
theorem fourier_bandG (t : ℝ) : 𝓕 (fun w => (bandG w : ℂ)) t = ((2 * Real.pi * t * bandH t : ℝ) : ℂ) * Complex.I := by
  rw [fourier_ofReal_of_support bandA_pos.le integrable_bandG.intervalIntegrable (fun w hw => by
    unfold bandG; rw [indicator_of_notMem hw]) t]
  have hcos : ∫ w in -bandA..bandA, Real.cos (2 * Real.pi * t * w) * bandG w = 0 :=
    integral_odd_symm (fun w => by simp only [bandG_neg, mul_neg, Real.cos_neg]) _
  have hsin : ∫ w in -bandA..bandA, Real.sin (2 * Real.pi * t * w) * bandG w = -(2 * Real.pi * t * bandH t) := by
    have h1 : ∫ w in -bandA..bandA, Real.sin (2 * Real.pi * t * w) * bandG w =
        ∫ w in -bandA..bandA, -(2 * Real.pi ^ 2) * (Real.sin (2 * Real.pi * t * w) * Real.sin (2 * Real.pi ^ 2 * w)) := by
      refine intervalIntegral.integral_congr fun w hw => ?_
      rw [uIcc_of_le (by linarith [bandA_pos])] at hw
      simp only [bandG, indicator_of_mem hw]; ring
    rw [h1, intervalIntegral.integral_const_mul, integral_sin_sin_band]
    field_simp
  rw [hcos, hsin]; push_cast; ring

/-- `c` and `g` as complex functions are integrable and square integrable. -/
theorem hasCompactSupport_bandC_ofReal : HasCompactSupport (fun w => (bandC w : ℂ)) :=
  hasCompactSupport_bandC.comp_left (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero

theorem continuous_bandC_ofReal : Continuous (fun w => (bandC w : ℂ)) := Complex.continuous_ofReal.comp continuous_bandC

theorem integrable_bandC_ofReal : Integrable (fun w => (bandC w : ℂ)) :=
  continuous_bandC_ofReal.integrable_of_hasCompactSupport hasCompactSupport_bandC_ofReal

theorem memLp_bandC_ofReal : MemLp (fun w => (bandC w : ℂ)) 2 :=
  continuous_bandC_ofReal.memLp_of_hasCompactSupport hasCompactSupport_bandC_ofReal

theorem integrable_bandG_ofReal : Integrable (fun w => (bandG w : ℂ)) := integrable_bandG.ofReal

/-- `∫ ‖c‖² = a`. -/
theorem integral_norm_bandC_sq : ∫ w, ‖(bandC w : ℂ)‖ ^ 2 = bandA := by
  have h1 : ∫ w, ‖(bandC w : ℂ)‖ ^ 2 = ∫ w in Icc (-bandA) bandA, ‖(bandC w : ℂ)‖ ^ 2 :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw => by rw [bandC_of_notMem hw]; simp).symm
  rw [h1, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [bandA_pos])]
  refine (intervalIntegral.integral_congr (g := fun w => Real.cos (2 * Real.pi ^ 2 * w) ^ 2) fun w hw => ?_).trans
    integral_cos_sq_band
  rw [uIcc_of_le (by linarith [bandA_pos])] at hw
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, bandC_of_mem hw]

/-- `∫ ‖g‖² = 4π⁴ a`. -/
theorem integral_norm_bandG_sq : ∫ w, ‖(bandG w : ℂ)‖ ^ 2 = 4 * Real.pi ^ 4 * bandA := by
  have h1 : ∫ w, ‖(bandG w : ℂ)‖ ^ 2 = ∫ w in Icc (-bandA) bandA, ‖(bandG w : ℂ)‖ ^ 2 :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw => by simp [bandG, indicator_of_notMem hw]).symm
  rw [h1, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [bandA_pos]),
    show 4 * Real.pi ^ 4 * bandA = 4 * Real.pi ^ 4 * ∫ w in -bandA..bandA, Real.sin (2 * Real.pi ^ 2 * w) ^ 2 by
      rw [integral_sin_sq_band], ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun w hw => ?_
  rw [uIcc_of_le (by linarith [bandA_pos])] at hw
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, bandG, indicator_of_mem hw]
  ring

/-- **Plancherel for `c`**: `h` is square integrable and `∫ h² = a = 1/(4π)`. -/
theorem bandH_sq_facts : Integrable (fun t => bandH t ^ 2) ∧ ∫ t, bandH t ^ 2 = bandA := by
  obtain ⟨hmem, hnorm, -⟩ := Wave31tp.plancherel ℝ _ _ integrable_bandC_ofReal memLp_bandC_ofReal integrable_bandC_ofReal
    memLp_bandC_ofReal
  have hF : 𝓕 (fun w => (bandC w : ℂ)) = fun t => (bandH t : ℂ) := funext fourier_bandC
  rw [hF] at hmem hnorm
  have hsq : (fun t => ‖(bandH t : ℂ)‖ ^ 2) = fun t => bandH t ^ 2 := by
    funext t; rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  refine ⟨?_, ?_⟩
  · have := hmem.integrable_norm_pow two_ne_zero
    rwa [hsq] at this
  · rw [← hsq, hnorm, integral_norm_bandC_sq]

/-- **Plancherel for `g`**: `t ↦ t² h(t)²` is integrable and `∫ t² h² = π/4`. -/
theorem bandH_moment_facts : Integrable (fun t => t ^ 2 * bandH t ^ 2) ∧ ∫ t, t ^ 2 * bandH t ^ 2 = Real.pi / 4 := by
  obtain ⟨hmem, hnorm, -⟩ := Wave31tp.plancherel ℝ _ _ integrable_bandG_ofReal memLp_bandG_ofReal integrable_bandG_ofReal
    memLp_bandG_ofReal
  have hF : 𝓕 (fun w => (bandG w : ℂ)) = fun t => ((2 * Real.pi * t * bandH t : ℝ) : ℂ) * Complex.I :=
    funext fourier_bandG
  rw [hF] at hmem hnorm
  have hsq : (fun t => ‖((2 * Real.pi * t * bandH t : ℝ) : ℂ) * Complex.I‖ ^ 2) =
      fun t => (4 * Real.pi ^ 2) * (t ^ 2 * bandH t ^ 2) := by
    funext t; rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]; ring
  have hi : Integrable fun t => (4 * Real.pi ^ 2) * (t ^ 2 * bandH t ^ 2) := by
    have := hmem.integrable_norm_pow two_ne_zero
    rwa [hsq] at this
  have hπ : (4 * Real.pi ^ 2) ≠ 0 := by positivity
  refine ⟨?_, ?_⟩
  · have := hi.const_mul (4 * Real.pi ^ 2)⁻¹
    simp only [← mul_assoc, inv_mul_cancel₀ hπ, one_mul] at this
    exact this
  · rw [hsq, integral_norm_bandG_sq, integral_const_mul] at hnorm
    have hA : bandA = (4 * Real.pi)⁻¹ := rfl
    rw [hA] at hnorm
    field_simp at hnorm
    nlinarith [Real.pi_pos]

/-- **`h` is integrable**: `|h(t)| ≤ (1 + 4π²)/(1 + t²)`. -/
theorem integrable_bandH : Integrable bandH := by
  have hb : ∀ t, |bandH t| ≤ (1 + 4 * Real.pi ^ 2) * (1 + t ^ 2)⁻¹ := by
    intro t
    have hpos : 0 < 1 + t ^ 2 := by positivity
    rw [le_mul_inv_iff₀ hpos]
    by_cases ht : t ^ 2 ≤ 4 * Real.pi ^ 2
    · have h1 := abs_bandH_le t
      have hA : 2 * bandA = (2 * Real.pi)⁻¹ := by unfold bandA; field_simp; ring
      rw [hA] at h1
      have h2 : (2 * Real.pi)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [Real.pi_gt_three])
      nlinarith [abs_nonneg (bandH t)]
    · push Not at ht
      have hne : ¬ t ^ 2 = Real.pi ^ 2 := by nlinarith [Real.pi_pos]
      have hd : 0 < t ^ 2 - Real.pi ^ 2 := by nlinarith [Real.pi_pos]
      have hval : |bandH t| ≤ 1 / (t ^ 2 - Real.pi ^ 2) := by
        unfold bandH
        rw [ite_eq_right hne, abs_div, abs_of_neg (show Real.pi ^ 2 - t ^ 2 < 0 by linarith), neg_sub]
        exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) hd.le
      calc |bandH t| * (1 + t ^ 2) ≤ 1 / (t ^ 2 - Real.pi ^ 2) * (1 + t ^ 2) :=
            mul_le_mul_of_nonneg_right hval hpos.le
        _ ≤ 1 + 4 * Real.pi ^ 2 := by
            rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hd]
            have hπ2 : 9 < Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
            have h4 : 0 < 4 * Real.pi ^ 2 := by positivity
            nlinarith [mul_pos h4 (sub_pos.2 ht), sq_nonneg (Real.pi ^ 2)]
  refine (integrable_inv_one_add_sq.const_mul (1 + 4 * Real.pi ^ 2)).mono' continuous_bandH.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs]; exact hb t

/-- **Fourier inversion**: `𝓕 h = c`. -/
theorem fourier_bandH : 𝓕 (fun t => (bandH t : ℂ)) = fun w => (bandC w : ℂ) := by
  have hinv : 𝓕⁻ (fun w => (bandC w : ℂ)) = fun t => (bandH t : ℂ) := by
    rw [Real.fourierInv_eq_fourier_comp_neg]
    simp_rw [bandC_neg]
    exact funext fourier_bandC
  have hF : 𝓕 (fun w => (bandC w : ℂ)) = fun t => (bandH t : ℂ) := funext fourier_bandC
  rw [← hinv]
  exact Continuous.fourier_fourierInv_eq continuous_bandC_ofReal integrable_bandC_ofReal
    (by rw [hF]; exact integrable_bandH.ofReal)

end StatFormal.BandLimited
