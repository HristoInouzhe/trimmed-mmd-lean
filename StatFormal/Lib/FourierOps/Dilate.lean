import StatFormal.Wave31tp.Statements

/-!
# Dilations and the L¹ bound for the Fourier transform (library, untrusted)

On a finite-dimensional real inner-product space `V` of dimension `d`, the dilation `b_w(x) = w^{-d} b(x/w)` (`w > 0`) of an
integrable `b` is integrable, has the same integral, and its Fourier transform is `𝓕 b_w(ξ) = 𝓕 b(w ξ)` (Stein–Weiss, Ch. I §1):
the change of variables `x = w y`, `dx = w^d dy` (Mathlib's `Measure.integral_comp_inv_smul_of_nonneg`). The last two identities
need no integrability (both sides are `0` by the junk convention otherwise). Also: `‖𝓕 b(ξ)‖ ≤ ∫ ‖b‖`, and the real dilation
`dilateR` is the real part of the complex one.
-/

noncomputable section
open MeasureTheory FourierTransform
open scoped InnerProductSpace RealInnerProductSpace

set_option linter.unusedSectionVars false

namespace StatFormal.FourierOps

open StatFormal.Wave31tp

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

/-- The dilation of an integrable function is integrable. -/
theorem integrable_dilate {b : V → ℂ} (hb : Integrable b) {w : ℝ} (hw : 0 < w) : Integrable (dilate w b) :=
  (hb.comp_smul (inv_ne_zero hw.ne')).const_mul _

/-- Dilation preserves the integral (`x = w y`, `dx = w^d dy`); no integrability needed. -/
theorem integral_dilate (b : V → ℂ) {w : ℝ} (hw : 0 < w) : ∫ x, dilate w b x = ∫ x, b x := by
  have hd : (w ^ Module.finrank ℝ V : ℝ) ≠ 0 := pow_ne_zero _ hw.ne'
  simp only [dilate]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume b hw.le, Complex.real_smul,
    ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hd, Complex.ofReal_one, one_mul]

/-- **Fourier transform of a dilation**: `𝓕 (w^{-d} b(·/w)) (ξ) = 𝓕 b (w ξ)`; no integrability needed. -/
theorem fourier_dilate (b : V → ℂ) {w : ℝ} (hw : 0 < w) (ξ : V) : 𝓕 (dilate w b) ξ = 𝓕 b (w • ξ) := by
  have hd : (w ^ Module.finrank ℝ V : ℝ) ≠ 0 := pow_ne_zero _ hw.ne'
  set g : V → ℂ := fun y => (𝐞 (-⟪y, w • ξ⟫) : ℂ) • b y with hg
  have hpt : ∀ x : V, (𝐞 (-⟪x, ξ⟫) : ℂ) • dilate w b x = (((w ^ Module.finrank ℝ V)⁻¹ : ℝ) : ℂ) * g (w⁻¹ • x) := by
    intro x
    simp only [hg, dilate, smul_eq_mul, real_inner_smul_right, real_inner_smul_left]
    rw [show w * (w⁻¹ * ⟪x, ξ⟫) = ⟪x, ξ⟫ by field_simp]
    ring
  rw [Real.fourier_eq, Real.fourier_eq]
  simp_rw [Circle.smul_def]
  rw [show (fun x => (𝐞 (-⟪x, ξ⟫) : ℂ) • dilate w b x) = fun x => (((w ^ Module.finrank ℝ V)⁻¹ : ℝ) : ℂ) * g (w⁻¹ • x)
    from funext hpt, integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume g hw.le, Complex.real_smul,
    ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hd, Complex.ofReal_one, one_mul]

/-- The sup norm of a Fourier transform is bounded by the L¹ norm: `‖𝓕 b ξ‖ ≤ ∫ ‖b‖`. -/
theorem norm_fourier_le_integral_norm (b : V → ℂ) (ξ : V) : ‖𝓕 b ξ‖ ≤ ∫ x, ‖b x‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (innerₗ V) b ξ

/-- The complex dilation of a real function is the coercion of its real dilation. -/
theorem dilate_ofReal (b : V → ℝ) (w : ℝ) : dilate w (fun x => (b x : ℂ)) = fun x => (dilateR w b x : ℂ) := by
  funext x
  simp [dilate, dilateR]

/-- The real dilation of an integrable function is integrable. -/
theorem integrable_dilateR {b : V → ℝ} (hb : Integrable b) {w : ℝ} (hw : 0 < w) : Integrable (dilateR w b) :=
  (hb.comp_smul (inv_ne_zero hw.ne')).const_mul _

/-- Real dilation preserves the integral; no integrability needed. -/
theorem integral_dilateR (b : V → ℝ) {w : ℝ} (hw : 0 < w) : ∫ x, dilateR w b x = ∫ x, b x := by
  have hd : (w ^ Module.finrank ℝ V : ℝ) ≠ 0 := pow_ne_zero _ hw.ne'
  simp only [dilateR]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume b hw.le, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hd, one_mul]

/-- The real dilation of a nonnegative function is nonnegative. -/
theorem dilateR_nonneg {b : V → ℝ} (hb : ∀ x, 0 ≤ b x) {w : ℝ} (hw : 0 < w) (x : V) : 0 ≤ dilateR w b x :=
  mul_nonneg (inv_nonneg.2 (pow_nonneg hw.le _)) (hb _)

/-- If `b` vanishes off the closed unit ball, its dilation by `w > 0` vanishes off the closed ball of radius `w`. -/
theorem support_dilateR_subset {b : V → ℝ} (hb : Function.support b ⊆ Metric.closedBall 0 1) {w : ℝ} (hw : 0 < w) :
    Function.support (dilateR w b) ⊆ Metric.closedBall 0 w := by
  intro x hx
  have hx' : w⁻¹ • x ∈ Metric.closedBall (0 : V) 1 := hb (fun h => hx (by simp [dilateR, h]))
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hw)] at hx'
  rw [mem_closedBall_zero_iff]
  have := mul_le_mul_of_nonneg_left hx' hw.le
  rwa [← mul_assoc, mul_inv_cancel₀ hw.ne', one_mul, mul_one] at this

end StatFormal.FourierOps
