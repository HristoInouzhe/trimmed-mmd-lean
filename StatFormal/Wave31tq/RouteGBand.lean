import StatFormal.Wave31tq.RouteG
import StatFormal.Lib.BandLimited.BandFourier
import StatFormal.Lib.BandLimited.Autocorr

/-!
# Wave 31tq, chunk G: the band-limited density (Q15 `bandB_facts`)

Route (S4 :664-670). In Mathlib's convention, `h = 𝓕 c` with `c(w) = cos(2π²w)1_{[−a,a]}(w)`, `a = 1/(4π)`
(`Lib/BandLimited/BandTrig`, `BandFourier`: explicit trigonometric integration), `h` is integrable (`O(t^{−2})`), and by inversion
`𝓕 h = c`, i.e. the angular `ĥ(ξ) = c(ξ/2π) = cos(πξ)1_{[−1/2,1/2]}(ξ)`. Plancherel (31tp L1) gives `‖h‖² = ∫ c² = 1/(4π)` and,
with `g = c′1_{(−a,a)}` and `𝓕 g(t) = 2πi t h(t)`, `∫ t² h² = π/4`, so `m₂ = 4π · π/4 = π²`. The transform of `b = 4πh²` is
`4π (c ⋆ c)` (`Lib/BandLimited/Autocorr`), real and supported in `[−2a, 2a]`, i.e. `b̂ = 0` off `[−1, 1]` in the angular variable,
and equal to `(2π)^{−1}·4π·(ĥ ⋆ ĥ)` after `η = 2πu`. The tail bounds are arithmetic and `∫_t^∞ 16πx^{−4} dx = 16π/(3t³)`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology FourierTransform
open scoped ENNReal NNReal InnerProductSpace

namespace StatFormal.Wave31tq.RouteG

open StatFormal StatFormal.Wave31tp StatFormal.BandLimited

/-- `b = 4π h²` pointwise (both with their continuous values at `±π`). -/
theorem bandB_eq (t : ℝ) : bandB t = 4 * Real.pi * bandH t ^ 2 := by
  unfold bandB bandH
  split_ifs with h
  · field_simp
  · rw [div_pow]; ring

/-- The angular transform of `h` is `c(ξ/2π)`. -/
theorem ftA_bandH (ξ : ℝ) : ftA (fun t => (bandH t : ℂ)) ξ = (bandC ((2 * Real.pi)⁻¹ * ξ) : ℂ) := by
  unfold ftA; rw [fourier_bandH, smul_eq_mul]

/-- `ξ/2π ∈ [−a, a]` iff `|ξ| ≤ 1/2`. -/
theorem mem_band_iff (ξ : ℝ) : (2 * Real.pi)⁻¹ * ξ ∈ Icc (-bandA) bandA ↔ |ξ| ≤ 1 / 2 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have e1 : ∀ x : ℝ, (2 * Real.pi)⁻¹ * x ≤ bandA ↔ x ≤ 1 / 2 := fun x => by
    unfold bandA
    rw [show (4 * Real.pi)⁻¹ = (2 * Real.pi)⁻¹ * (1 / 2) by field_simp; ring]
    exact mul_le_mul_iff_of_pos_left (by positivity)
  have e2 : ∀ x : ℝ, -bandA ≤ (2 * Real.pi)⁻¹ * x ↔ -(1 / 2) ≤ x := fun x => by
    unfold bandA
    rw [show -(4 * Real.pi)⁻¹ = (2 * Real.pi)⁻¹ * (-(1 / 2)) by field_simp; ring]
    exact mul_le_mul_iff_of_pos_left (by positivity)
  rw [mem_Icc, e1, e2, abs_le]

/-- `𝓕 (c · f) = c · 𝓕 f`. -/
theorem fourier_const_mul (c : ℂ) (f : ℝ → ℂ) (w : ℝ) : 𝓕 (fun t => c * f t) w = c * 𝓕 f w := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq, ← integral_const_mul]
  congr 1; funext v
  rw [Circle.smul_def, Circle.smul_def, smul_eq_mul, smul_eq_mul]; ring

/-- `𝓕⁻ c = h`. -/
theorem fourierInv_bandC : 𝓕⁻ (fun w => (bandC w : ℂ)) = fun t => (bandH t : ℂ) := by
  funext t
  rw [Real.fourierInv_eq_fourier_neg, fourier_bandC, bandH_neg]

/-- The self-convolution `c ⋆ c`. -/
def convC : ℝ → ℂ := convolution (fun u => (bandC u : ℂ)) (fun u => (bandC u : ℂ)) (ContinuousLinearMap.mul ℂ ℂ) volume

theorem convC_apply (w : ℝ) : convC w = ∫ u, (bandC u : ℂ) * (bandC (w - u) : ℂ) := by
  simp [convC, convolution_def]

/-- `c ⋆ c` is real. -/
theorem convC_eq_ofReal (w : ℝ) : convC w = ((∫ u, bandC u * bandC (w - u) : ℝ) : ℂ) := by
  rw [convC_apply, ← integral_complex_ofReal]; push_cast; rfl

/-- `c ⋆ c` vanishes off `[−2a, 2a]`. -/
theorem convC_eq_zero {w : ℝ} (hw : 2 * bandA < |w|) : convC w = 0 := by
  rw [convC_apply]
  refine (integral_congr_ae (Eventually.of_forall fun u => ?_)).trans (integral_zero ℝ ℂ)
  show (bandC u : ℂ) * (bandC (w - u) : ℂ) = 0
  by_cases hu : u ∈ Icc (-bandA) bandA
  · have : w - u ∉ Icc (-bandA) bandA := by
      intro h
      have h1 := abs_le.2 ⟨hu.1, hu.2⟩
      have h2 := abs_le.2 ⟨h.1, h.2⟩
      have := abs_sub_abs_le_abs_sub w u
      have := abs_sub_le_iff.1 (le_refl |w - u|)
      linarith [abs_add_le (w - u) u, show w - u + u = w by ring]
    rw [bandC_of_notMem this]; simp
  · rw [bandC_of_notMem hu]; simp

/-- **The transform of `b`**: `𝓕 b = 4π (c ⋆ c)`. -/
theorem fourier_bandB (w : ℝ) : 𝓕 (fun t => (bandB t : ℂ)) w = ((4 * Real.pi : ℝ) : ℂ) * convC w := by
  have hfun : (fun t => (bandB t : ℂ)) = fun t => ((4 * Real.pi : ℝ) : ℂ) *
      (𝓕⁻ (fun u => (bandC u : ℂ)) t * 𝓕⁻ (fun u => (bandC u : ℂ)) t) := by
    funext t; rw [fourierInv_bandC, bandB_eq]; push_cast; ring
  have hint : Integrable (fun t => 𝓕⁻ (fun u => (bandC u : ℂ)) t * 𝓕⁻ (fun u => (bandC u : ℂ)) t) := by
    rw [fourierInv_bandC]
    have := bandH_sq_facts.1.ofReal (𝕜 := ℂ)
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only [sq]; exact RCLike.ofReal_mul _ _
  rw [hfun, fourier_const_mul, fourier_mul_self_fourierInv continuous_bandC_ofReal hasCompactSupport_bandC_ofReal hint]
  rfl

/-- The angular transform of `b`: `b̂(ξ) = 4π (c ⋆ c)(ξ/2π)`. -/
theorem ftA_bandB (ξ : ℝ) : ftA (fun t => (bandB t : ℂ)) ξ = ((4 * Real.pi : ℝ) : ℂ) * convC ((2 * Real.pi)⁻¹ * ξ) := by
  unfold ftA; rw [fourier_bandB, smul_eq_mul]

/-- `∫ ĥ(η) ĥ(ξ − η) dη = 2π (c ⋆ c)(ξ/2π)` (`η = 2πu`). -/
theorem integral_ftA_bandH_mul (ξ : ℝ) :
    ∫ η : ℝ, ftA (fun t => (bandH t : ℂ)) η * ftA (fun t => (bandH t : ℂ)) (ξ - η) =
      ((2 * Real.pi : ℝ) : ℂ) * convC ((2 * Real.pi)⁻¹ * ξ) := by
  simp_rw [ftA_bandH]
  set g : ℝ → ℂ := fun u => (bandC u : ℂ) * (bandC ((2 * Real.pi)⁻¹ * ξ - u) : ℂ) with hg
  have h1 : (fun η : ℝ => (bandC ((2 * Real.pi)⁻¹ * η) : ℂ) * (bandC ((2 * Real.pi)⁻¹ * (ξ - η)) : ℂ)) =
      fun η => g ((2 * Real.pi)⁻¹ * η) := by
    funext η; simp only [hg, mul_sub]
  rw [h1, Measure.integral_comp_mul_left g, inv_inv, abs_of_pos (by positivity), convC_apply, Complex.real_smul]

/-- `ĥ` has derivative `−π sin(πξ)` on `(−1/2, 1/2)` (it is `cos(πξ)` there). -/
theorem hasDerivAt_ftA_bandH {ξ : ℝ} (hξ : ξ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) :
    HasDerivAt (ftA (fun t => (bandH t : ℂ))) ((-(Real.pi * Real.sin (Real.pi * ξ)) : ℝ) : ℂ) ξ := by
  have hcos : HasDerivAt (fun ζ : ℝ => ((Real.cos (Real.pi * ζ) : ℝ) : ℂ))
      ((-(Real.pi * Real.sin (Real.pi * ξ)) : ℝ) : ℂ) ξ := by
    have h1 : HasDerivAt (fun ζ : ℝ => Real.cos (Real.pi * ζ)) (-(Real.pi * Real.sin (Real.pi * ξ))) ξ := by
      have := (Real.hasDerivAt_cos (Real.pi * ξ)).comp ξ ((hasDerivAt_id ξ).const_mul Real.pi)
      convert this using 1 <;> first | rfl | (simp only [mul_one]; ring)
    exact h1.ofReal_comp
  refine hcos.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hξ.1 hξ.2] with ζ hζ
  rw [ftA_bandH, bandC_of_mem ((mem_band_iff ζ).2 (abs_le.2 ⟨hζ.1.le, hζ.2.le⟩))]
  congr 2; field_simp

/-- `∫_{−1/2}^{1/2} |ĥ′|² = π²/2`. -/
theorem integral_deriv_ftA_bandH_sq :
    ∫ ξ in (-(1 / 2) : ℝ)..(1 / 2), ‖deriv (ftA (fun t => (bandH t : ℂ))) ξ‖ ^ 2 = Real.pi ^ 2 / 2 := by
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 / 2 := by rw [ae_iff]; simp
  have hcongr : ∫ ξ in (-(1 / 2) : ℝ)..(1 / 2), ‖deriv (ftA (fun t => (bandH t : ℂ))) ξ‖ ^ 2 =
      ∫ ξ in (-(1 / 2) : ℝ)..(1 / 2), Real.pi ^ 2 * Real.sin (Real.pi * ξ) ^ 2 := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hne] with x hx hmem
    rw [uIoc_of_le (by norm_num)] at hmem
    have hIoo : x ∈ Ioo (-(1 / 2) : ℝ) (1 / 2) := ⟨hmem.1, lt_of_le_of_ne hmem.2 hx⟩
    rw [(hasDerivAt_ftA_bandH hIoo).deriv, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  rw [hcongr]
  have hsq : ∀ ξ : ℝ, Real.pi ^ 2 * Real.sin (Real.pi * ξ) ^ 2 =
      Real.pi ^ 2 / 2 - Real.pi ^ 2 / 2 * Real.cos ((2 * Real.pi) * ξ) := fun ξ => by
    rw [Real.sin_sq, Real.cos_sq, show 2 * (Real.pi * ξ) = 2 * Real.pi * ξ by ring]; ring
  simp_rw [hsq]
  have hci : IntervalIntegrable (fun ξ : ℝ => Real.pi ^ 2 / 2 * Real.cos (2 * Real.pi * ξ)) volume (-(1 / 2)) (1 / 2) :=
    (by fun_prop : Continuous fun ξ : ℝ => Real.pi ^ 2 / 2 * Real.cos (2 * Real.pi * ξ)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub intervalIntegrable_const hci,
    intervalIntegral.integral_const_mul, integral_cos_mul_symm (by positivity),
    show 2 * Real.pi * (1 / 2) = Real.pi by ring, Real.sin_pi]
  norm_num

/-- `∫ |ĥ|² = 1/2` (`ξ = 2πw`). -/
theorem integral_norm_ftA_bandH_sq : ∫ ξ : ℝ, ‖ftA (fun t => (bandH t : ℂ)) ξ‖ ^ 2 = 1 / 2 := by
  simp_rw [ftA_bandH]
  rw [Measure.integral_comp_mul_left (fun u => ‖(bandC u : ℂ)‖ ^ 2), inv_inv, abs_of_pos (by positivity),
    integral_norm_bandC_sq, smul_eq_mul]
  unfold bandA; field_simp; ring

/-- The tail bounds of `b` (S4 :669-670). -/
theorem bandB_tail {t : ℝ} (ht : √2 * Real.pi ≤ t) :
    t ^ 2 / 2 ≤ t ^ 2 - Real.pi ^ 2 ∧ bandB t ≤ 16 * Real.pi / t ^ 4 ∧ bbar bandB t ≤ 16 * Real.pi / (3 * t ^ 3) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hs : (0 : ℝ) < √2 * Real.pi := by positivity
  -- pointwise bound
  have hpt : ∀ x : ℝ, √2 * Real.pi ≤ x → x ^ 2 / 2 ≤ x ^ 2 - Real.pi ^ 2 ∧ bandB x ≤ 16 * Real.pi / x ^ 4 := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hs hx
    have hx2 : 2 * Real.pi ^ 2 ≤ x ^ 2 := by
      have := pow_le_pow_left₀ hs.le hx 2
      rwa [mul_pow, Real.sq_sqrt (by norm_num)] at this
    refine ⟨by linarith, ?_⟩
    have hne : ¬ x ^ 2 = Real.pi ^ 2 := by nlinarith
    unfold bandB
    rw [ite_eq_right hne, div_le_div_iff₀ (by positivity) (by positivity)]
    have hc : Real.cos (x / 2) ^ 2 ≤ 1 := Real.cos_sq_le_one _
    have hsq : x ^ 4 ≤ 4 * (Real.pi ^ 2 - x ^ 2) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hc (by positivity : (0 : ℝ) ≤ 4 * Real.pi * x ^ 4)]
  obtain ⟨h1, h2⟩ := hpt t ht
  refine ⟨h1, h2, ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le hs ht
  have hint : IntegrableOn (fun x : ℝ => 16 * Real.pi * x ^ (-4 : ℝ)) (Ioi t) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) ht0).const_mul _
  have hbint : IntegrableOn bandB (Ioi t) := by
    rw [funext bandB_eq]; exact (bandH_sq_facts.1.const_mul _).integrableOn
  calc bbar bandB t = ∫ x in Ioi t, bandB x := rfl
    _ ≤ ∫ x in Ioi t, 16 * Real.pi * x ^ (-4 : ℝ) := by
        refine setIntegral_mono_on hbint hint measurableSet_Ioi fun x hx => ?_
        have hx0 : 0 < x := lt_trans ht0 hx
        rw [Real.rpow_neg hx0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← div_eq_mul_inv]
        exact (hpt x (ht.trans (le_of_lt hx))).2
    _ = 16 * Real.pi / (3 * t ^ 3) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) ht0,
          show (-4 : ℝ) + 1 = -3 by norm_num, Real.rpow_neg ht0.le,
          show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        field_simp

/-- Q15 `bandB_facts`. -/
theorem bandB_facts_route : Claims.bandB_facts := by
  have hπ : 0 < Real.pi := Real.pi_pos
  obtain ⟨hHsq, hHsq1⟩ := bandH_sq_facts
  obtain ⟨hHm, hHm1⟩ := bandH_moment_facts
  have hA : bandA = 1 / (4 * Real.pi) := by unfold bandA; rw [one_div]
  have hBfun : bandB = fun t => 4 * Real.pi * bandH t ^ 2 := funext bandB_eq
  refine ⟨⟨continuous_bandH, integrable_bandH, hHsq, fun ξ hξ => ?_, fun ξ hξ => ?_, by rw [hHsq1, hA], ?_⟩,
    ⟨?_, ?_, fun t => ?_, fun t => ?_, ?_, ?_, fun ξ => ?_, fun ξ hξ => ?_, fun ξ => ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  -- (a)
  · rw [ftA_bandH, bandC_of_mem ((mem_band_iff ξ).2 hξ)]
    congr 2; field_simp
  · rw [ftA_bandH, bandC_of_notMem (fun h => (not_le.2 hξ) ((mem_band_iff ξ).1 h))]; simp
  · funext t; rw [hHsq1, bandB_eq, hA]; field_simp
  -- (b)
  · rw [hBfun]; exact continuous_const.mul (continuous_bandH.pow 2)
  · refine ⟨4 * Real.pi * (2 * bandA) ^ 2, ?_⟩
    rintro _ ⟨t, rfl⟩
    rw [bandB_eq]
    have h := abs_bandH_le t
    have : bandH t ^ 2 ≤ (2 * bandA) ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
    nlinarith
  · rw [bandB_eq, bandB_eq, bandH_neg]
  · rw [bandB_eq]; positivity
  · rw [hBfun]; exact hHsq.const_mul _
  · rw [hBfun, integral_const_mul, hHsq1]; unfold bandA; field_simp
  · rw [ftA_bandB, convC_eq_ofReal]; simp
  · rw [ftA_bandB, convC_eq_zero, mul_zero]
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.pi)⁻¹), hA]
    rw [show 2 * (1 / (4 * Real.pi)) = (2 * Real.pi)⁻¹ * 1 by field_simp; ring]
    exact mul_lt_mul_of_pos_left hξ (by positivity)
  · rw [ftA_bandB, integral_ftA_bandH_mul]
    push_cast
    field_simp
  -- (c)
  · rw [hBfun]
    have := hHm.const_mul (4 * Real.pi)
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only; ring
  · rw [hBfun]
    have : (fun t => t ^ 2 * (4 * Real.pi * bandH t ^ 2)) = fun t => 4 * Real.pi * (t ^ 2 * bandH t ^ 2) := by
      funext t; ring
    rw [this, integral_const_mul, hHm1]; ring
  · exact fun ξ hξ => hasDerivAt_ftA_bandH hξ
  · rw [integral_deriv_ftA_bandH_sq, integral_norm_ftA_bandH_sq]; field_simp
  -- (d)
  · exact fun t ht => bandB_tail ht

end StatFormal.Wave31tq.RouteG
