import StatFormal.Lib.TIKernel.Native
import StatFormal.Lib.TIKernel.Spectra

/-!
# Band-limited functions lie in the native space (library, untrusted)

On a finite-dimensional real inner-product space `V`, with Mathlib's unitary L² Fourier
transform (`ft2`):

* `lintegral_enorm_ft2_sq`: Plancherel in `ℝ≥0∞` form, `∫⁻ ‖ft2 f‖ₑ² = ∫⁻ ‖f‖ₑ²` for `f ∈ L²`
  (`Lp.norm_fourier_eq`).
* `nativeN_le_of_bandlimited`: if `ft2 f = 0` a.e. off the ball `‖ξ‖ ≤ Ω` and
  `specDens k₀ ≥ m > 0` on it, then `nativeN k₀ f ≤ ‖f‖₂² / m` (pointwise:
  `|f̂|²/specDens ≤ |f̂|²/m` on the band, `0` off it).
* `bandlimited_rep` (Wave31tp L20 (a)): such a continuous real `f ∈ L²` is represented in any
  feature map with profile `k₀`, with `‖g‖² ≤ ∫ f² / m` (the native-space inclusion
  `TIKernel.native_incl_facts`).
* `bandlimited_gauss_rep` (Wave31tp L20 (b), eq:newbandlim; Steinwart–Hush–Scovel 2006, the
  elementary half): for the Gaussian kernel `e^{−‖x−y‖²/(2σ²)}`,
  `‖g‖² ≤ (2πσ²)^{−d/2} e^{2π²σ²Ω²} ∫ f²`, since the Gaussian spectral density
  `(2πσ²)^{d/2} e^{−2π²σ²‖ξ‖²}` (`TIKernel.specDens_gauss_eq`) is at least
  `(2πσ²)^{d/2} e^{−2π²σ²Ω²}` on the band.
-/

noncomputable section
open MeasureTheory Filter Topology Set FourierTransform
open scoped ENNReal InnerProductSpace RealInnerProductSpace

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace StatFormal.SobolevFin

open StatFormal.Wave31tp

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

/-- `∫⁻ ‖h‖ₑ² = (eLpNorm h 2)²` for an a.e. strongly measurable `h`. -/
lemma lintegral_enorm_sq_eq_eLpNorm {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E] {h : α → E}
    (hm : AEStronglyMeasurable h μ) : ∫⁻ x, ‖h x‖ₑ ^ 2 ∂μ = eLpNorm h 2 μ ^ 2 := by
  have := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (p := 2) two_ne_zero hm
  simp only [NNReal.coe_ofNat, ENNReal.rpow_two, ENNReal.coe_ofNat] at this
  exact this.symm

/-- **Plancherel in `ℝ≥0∞` form**: `∫⁻ ‖ft2 f‖ₑ² = ∫⁻ ‖f‖ₑ²` for `f ∈ L²`. -/
theorem lintegral_enorm_ft2_sq {f : V → ℂ} (hf : MemLp f 2) :
    ∫⁻ ξ, ‖ft2 f ξ‖ₑ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  set F : Lp ℂ 2 (volume : Measure V) := hf.toLp f
  have hFF : ‖(𝓕 F : Lp ℂ 2 (volume : Measure V))‖ₑ = ‖F‖ₑ := by
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
    congr 1
    exact NNReal.eq (by simp only [coe_nnnorm]; exact Lp.norm_fourier_eq F)
  rw [TIKernel.ft2_eq' hf, lintegral_enorm_sq_eq_eLpNorm (Lp.aestronglyMeasurable _), ← Lp.enorm_def, hFF,
    Lp.enorm_def, eLpNorm_congr_ae hf.coeFn_toLp, lintegral_enorm_sq_eq_eLpNorm hf.aestronglyMeasurable]

/-- For a real `f ∈ L²`, `∫⁻ ‖(f x : ℂ)‖ₑ² = ∫ f²`. -/
lemma lintegral_enorm_ofReal_sq {f : V → ℝ} (hf : MemLp f 2) :
    ∫⁻ x, ‖(f x : ℂ)‖ₑ ^ 2 = ENNReal.ofReal (∫ x, f x ^ 2) := by
  rw [ofReal_integral_eq_lintegral_ofReal hf.integrable_sq (Eventually.of_forall fun x => sq_nonneg (f x))]
  refine lintegral_congr fun x => ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **The native functional of a band-limited function.** If `ft2 f = 0` a.e. off the ball `‖ξ‖ ≤ Ω` and the spectral density
is at least `m > 0` on it, then `nativeN k₀ f ≤ (∫⁻ ‖f‖ₑ²) / m`. -/
theorem nativeN_le_of_bandlimited {k₀ : V → ℝ} {Ω m : ℝ} (hm : 0 < m) (hband : ∀ ξ, ‖ξ‖ ≤ Ω → m ≤ specDens k₀ ξ)
    {f : V → ℂ} (hf : MemLp f 2) (hsupp : ∀ᵐ ξ ∂volume, Ω < ‖ξ‖ → ft2 f ξ = 0) :
    nativeN k₀ f ≤ (∫⁻ x, ‖f x‖ₑ ^ 2) / ENNReal.ofReal m := by
  unfold nativeN
  rw [← lintegral_enorm_ft2_sq hf, div_eq_mul_inv,
    ← lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr (by simpa using hm))]
  refine lintegral_mono_ae ?_
  filter_upwards [hsupp] with ξ hξ
  rcases le_or_gt ‖ξ‖ Ω with h | h
  · rw [← div_eq_mul_inv]
    exact ENNReal.div_le_div_left (ENNReal.ofReal_le_ofReal (hband ξ h)) _
  · simp [hξ h]

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Wave31tp L20 (a).** Band-limited functions are represented: if `specDens k₀ ≥ m > 0` on the ball `‖ξ‖ ≤ Ω` and the L²
transform of a continuous real `f ∈ L²` vanishes a.e. off it, then some `g` represents `f` in any feature map with profile `k₀`,
with `‖g‖² ≤ ∫ f² / m`. -/
theorem bandlimited_rep {φ : V → H} {k₀ : V → ℝ} (hφ : ∀ x y, ⟪φ x, φ y⟫ = k₀ (x - y)) (hc : Continuous k₀)
    (hi : Integrable k₀) {Ω m : ℝ} (hm : 0 < m) (hband : ∀ ξ, ‖ξ‖ ≤ Ω → m ≤ specDens k₀ ξ) {f : V → ℝ}
    (hfc : Continuous f) (hf2 : MemLp f 2) (hsupp : ∀ᵐ ξ ∂volume, Ω < ‖ξ‖ → ft2 (fun x => (f x : ℂ)) ξ = 0) :
    ∃ g : H, (∀ x, ⟪g, φ x⟫ = f x) ∧ ‖g‖ ^ 2 ≤ (∫ x, f x ^ 2) / m := by
  have hle : nativeN k₀ (fun x => (f x : ℂ)) ≤ ENNReal.ofReal ((∫ x, f x ^ 2) / m) := by
    rw [ENNReal.ofReal_div_of_pos hm, ← lintegral_enorm_ofReal_sq hf2]
    exact nativeN_le_of_bandlimited hm hband hf2.ofReal hsupp
  obtain ⟨g, hg, hgn⟩ := (TIKernel.native_incl_facts hφ hc hi f).1 hfc hf2 (hle.trans_lt ENNReal.ofReal_lt_top)
  exact ⟨g, hg, (ENNReal.ofReal_le_ofReal_iff
    (div_nonneg (integral_nonneg fun x => sq_nonneg (f x)) hm.le)).mp (hgn.trans hle)⟩

/-- **Wave31tp L20 (b)**, eq:newbandlim for the Gaussian kernel `e^{−‖x−y‖²/(2σ²)}` on `V` (`d = finrank ℝ V`): a band-limited
continuous real `f ∈ L²` (`ft2 f = 0` a.e. off `‖ξ‖ ≤ Ω`) is represented with `‖g‖² ≤ (2πσ²)^{−d/2} e^{2π²σ²Ω²} ∫ f²`. -/
theorem bandlimited_gauss_rep {φ : V → H} {σ Ω : ℝ} (hσ : 0 < σ)
    (hφ : ∀ x y, ⟪φ x, φ y⟫ = Real.exp (-‖x - y‖ ^ 2 / (2 * σ ^ 2))) {f : V → ℝ} (hfc : Continuous f) (hf2 : MemLp f 2)
    (hsupp : ∀ᵐ ξ ∂volume, Ω < ‖ξ‖ → ft2 (fun x => (f x : ℂ)) ξ = 0) :
    ∃ g : H, (∀ x, ⟪g, φ x⟫ = f x) ∧
      ‖g‖ ^ 2 ≤ (2 * Real.pi * σ ^ 2) ^ (-(Module.finrank ℝ V : ℝ) / 2) *
        Real.exp (2 * Real.pi ^ 2 * σ ^ 2 * Ω ^ 2) * ∫ x, f x ^ 2 := by
  set m := (2 * Real.pi * σ ^ 2) ^ ((Module.finrank ℝ V : ℝ) / 2) * Real.exp (-2 * Real.pi ^ 2 * σ ^ 2 * Ω ^ 2) with hm_def
  have hm : 0 < m := by positivity
  have hband : ∀ ξ : V, ‖ξ‖ ≤ Ω → m ≤ specDens (fun x : V => Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) ξ := by
    intro ξ hξ
    rw [TIKernel.specDens_gauss_eq hσ]
    have h2 : ‖ξ‖ ^ 2 ≤ Ω ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hξ 2
    have h3 : -2 * Real.pi ^ 2 * σ ^ 2 * Ω ^ 2 ≤ -2 * Real.pi ^ 2 * σ ^ 2 * ‖ξ‖ ^ 2 := by
      have : 0 ≤ 2 * Real.pi ^ 2 * σ ^ 2 := by positivity
      nlinarith
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h3) (by positivity)
  obtain ⟨g, hg, hgn⟩ := bandlimited_rep (k₀ := fun x : V => Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) hφ
    (TIKernel.gauss_continuous σ) (TIKernel.gauss_integrable hσ) hm hband hfc hf2 hsupp
  refine ⟨g, hg, hgn.trans_eq ?_⟩
  rw [hm_def, div_eq_inv_mul, mul_inv, ← Real.rpow_neg (by positivity), ← Real.exp_neg, neg_div]
  ring_nf

end Rep

end StatFormal.SobolevFin
