import StatFormal.Lib.TIKernel.Native

/-!
# RKHS functions of a translation-invariant kernel as Fourier integrals (library, untrusted)

Let `k₀ : V → ℝ` be continuous and integrable on a finite-dimensional real inner-product space `V`, `s = specDens k₀` its
spectral density, and `φ : V → H` any feature map with `⟪φ x, φ y⟫ = k₀ (x − y)`. Every function `x ↦ ⟪g, φ x⟫` (`g : H`) is
the real part of a Fourier integral:

  `⟪g, φ x⟫ = Re 𝓕 h (x)`,  `h = s · conj G`,

where `G ∈ L²(s · vol; ℂ)` represents `g` in the Fourier feature map `Ψ = fourierFeature s` (equal Gram functions,
`TIKernel.gram_rep_le`), and `⟪G, Ψ x⟫ = ∫ s(ξ) Re(conj G(ξ) 𝐞(−⟪x, ξ⟫)) dξ`. The weight `h` inherits every weighted
integrability of `s`: if `w² s` is integrable then so is `w ‖h‖`, by `2 |w| ‖G‖ ≤ w² + ‖G‖²` and `∫ s ‖G‖² = ‖G‖² < ∞`
(no Hölder inequality needed). This is the common step of the regularity results of `RKHSReg`: smoothness from spectral moments
(`Smooth.lean`), decay at infinity by Riemann–Lebesgue, and the Gaussian case (`Gauss.lean`).

Main results: `inner_fourierFeature_eq_re_fourier` (any measurable `ψ ≥ 0`, integrable), `exists_rep_fourier` and
`exists_fourier_weight` (any feature map with a continuous integrable profile).
-/

noncomputable section
open MeasureTheory Filter Topology Set FourierTransform Complex
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace RealInnerProductSpace

set_option linter.unusedSectionVars false

namespace StatFormal.RKHSReg

open StatFormal.Wave31tp StatFormal.TIKernel

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

/-- The spectral weight of `G ∈ L²(ψ · vol; ℂ)`: `ξ ↦ ψ(ξ) · conj (G ξ)`. Its Fourier transform carries the inner products
`⟪G, fourierFeature ψ x⟫` (`inner_fourierFeature_eq_re_fourier`). -/
def specWeight (ψ : V → ℝ) (G : Lp ℂ 2 (specMeas ψ)) (ξ : V) : ℂ := (ψ ξ : ℂ) * conj ((G : V → ℂ) ξ)

section Feature

variable {ψ : V → ℝ} (hψm : Measurable ψ) (hψ0 : ∀ ξ, 0 ≤ ψ ξ)
include hψm

/-- The spectral weight is measurable. -/
lemma measurable_specWeight (G : Lp ℂ 2 (specMeas ψ)) : Measurable (specWeight ψ G) :=
  (Complex.measurable_ofReal.comp hψm).mul (Complex.continuous_conj.measurable.comp (Lp.stronglyMeasurable G).measurable)

include hψ0

/-- `G ∈ L²(ψ · vol)` means that `ψ ‖G‖²` is Lebesgue integrable. -/
lemma integrable_mul_norm_sq (G : Lp ℂ 2 (specMeas ψ)) : Integrable (fun ξ => ψ ξ * ‖(G : V → ℂ) ξ‖ ^ 2) := by
  have h : Integrable (fun ξ => ‖(G : V → ℂ) ξ‖ ^ 2)
      (volume.withDensity fun ξ => ((Real.toNNReal (ψ ξ) : ℝ≥0) : ℝ≥0∞)) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable G)).1 (Lp.memLp G)
  rw [integrable_withDensity_iff_integrable_smul hψm.real_toNNReal] at h
  refine h.congr (Eventually.of_forall fun ξ => ?_)
  simp [NNReal.smul_def, Real.coe_toNNReal _ (hψ0 ξ)]

/-- **Weighted integrability of the spectral weight**: if `w² ψ` is integrable, so is `w ‖ψ · conj G‖` (from
`2 |w| ‖G‖ ≤ w² + ‖G‖²`). With `w = 1`, the spectral weight of a finite spectral measure is integrable. -/
lemma integrable_weight_mul_specWeight (G : Lp ℂ 2 (specMeas ψ)) {w : V → ℝ} (hwm : Measurable w)
    (hw : Integrable (fun ξ => w ξ ^ 2 * ψ ξ)) : Integrable (fun ξ => w ξ * ‖specWeight ψ G ξ‖) := by
  have hG := integrable_mul_norm_sq hψm hψ0 G
  refine ((hw.add hG).div_const 2).mono' (hwm.mul (measurable_specWeight hψm G).norm).aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  simp only [specWeight, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hψ0 ξ), Complex.norm_conj,
    abs_norm, Pi.add_apply]
  rw [← sq_abs (w ξ)]
  nlinarith [mul_nonneg (hψ0 ξ) (sq_nonneg (|w ξ| - ‖(G : V → ℂ) ξ‖)), sq_abs (w ξ)]

/-- The spectral weight of a finite spectral measure is integrable. -/
lemma integrable_specWeight (hψi : Integrable ψ) (G : Lp ℂ 2 (specMeas ψ)) : Integrable (specWeight ψ G) := by
  have h := integrable_weight_mul_specWeight hψm hψ0 G (w := fun _ => 1) measurable_const (by simpa using hψi)
  simp only [one_mul] at h
  exact (integrable_norm_iff (measurable_specWeight hψm G).aestronglyMeasurable).1 h

/-- **Inner products with the Fourier feature map are Fourier integrals**:
`⟪G, fourierFeature ψ x⟫_ℝ = Re 𝓕 (ψ · conj G) (x)`. -/
theorem inner_fourierFeature_eq_re_fourier (hψi : Integrable ψ) (G : Lp ℂ 2 (specMeas ψ)) (x : V) :
    ⟪G, fourierFeature ψ x⟫ = (𝓕 (specWeight ψ G) x).re := by
  have hint := integrable_specWeight hψm hψ0 hψi G
  have hconv : Integrable (fun ξ => 𝐞 (-⟪ξ, x⟫) • specWeight ψ G ξ) := (Real.fourierIntegral_convergent_iff x).2 hint
  have ere := (integral_re hconv).symm
  simp only [RCLike.re_to_complex] at ere
  have e1 : ∫ ξ, ⟪(G : V → ℂ) ξ, (fourierFeature ψ x : V → ℂ) ξ⟫ ∂(specMeas ψ) =
      ∫ ξ, ψ ξ * ⟪(G : V → ℂ) ξ, (𝐞 (-⟪x, ξ⟫) : ℂ)⟫ := by
    rw [← integral_specMeas hψm hψ0]
    refine integral_congr_ae ?_
    filter_upwards [fourierFeature_ae ψ hψi x] with ξ h
    rw [h]
  rw [L2.inner_def, e1, Real.fourier_eq, ere]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [specWeight, Complex.inner, Circle.smul_def, smul_eq_mul, real_inner_comm ξ x, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im]
  ring

end Feature

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {φ : V → H} {k₀ : V → ℝ} (hφ : ∀ x y, ⟪φ x, φ y⟫ = k₀ (x - y)) (hc : Continuous k₀) (hi : Integrable k₀)
include hφ hc hi

/-- **RKHS functions are Fourier integrals.** For a feature map with continuous integrable profile `k₀`, every `g : H` has a
representer `G ∈ L²(specDens k₀ · vol; ℂ)` with `‖G‖ ≤ ‖g‖` and `⟪g, φ x⟫ = Re 𝓕 (specDens k₀ · conj G) (x)` for all `x`. -/
theorem exists_rep_fourier (g : H) :
    ∃ G : Lp ℂ 2 (specMeas (specDens k₀)), ‖G‖ ≤ ‖g‖ ∧
      ∀ x, ⟪g, φ x⟫ = (𝓕 (specWeight (specDens k₀) G) x).re := by
  obtain ⟨hsc, -, hs0, hsi, -, hΨ⟩ := feature_exists_facts hc hi (gram_posdef hφ)
  have hgram : ∀ x y, ⟪φ x, φ y⟫ = ⟪fourierFeature (specDens k₀) x, fourierFeature (specDens k₀) y⟫ :=
    fun x y => by rw [hΨ, hφ]
  obtain ⟨G, hGn, hG⟩ := gram_rep_le hgram g
  exact ⟨G, hGn, fun x => by rw [← hG, inner_fourierFeature_eq_re_fourier hsc.measurable hs0 hsi]⟩

/-- **RKHS functions as Fourier integrals of a weight with the spectral moments of `k₀`.** Every `x ↦ ⟪g, φ x⟫` is
`Re 𝓕 h` for an integrable `h : V → ℂ` such that `w ‖h‖` is integrable whenever `w` is measurable and `w² · specDens k₀` is
integrable. -/
theorem exists_fourier_weight (g : H) :
    ∃ h : V → ℂ, Integrable h ∧
      (∀ w : V → ℝ, Measurable w → Integrable (fun ξ => w ξ ^ 2 * specDens k₀ ξ) → Integrable (fun ξ => w ξ * ‖h ξ‖)) ∧
      ∀ x, ⟪g, φ x⟫ = (𝓕 h x).re := by
  obtain ⟨hsc, -, hs0, hsi, -, -⟩ := feature_exists_facts hc hi (gram_posdef hφ)
  obtain ⟨G, -, hG⟩ := exists_rep_fourier hφ hc hi g
  exact ⟨specWeight (specDens k₀) G, integrable_specWeight hsc.measurable hs0 hsi G,
    fun w hwm hw => integrable_weight_mul_specWeight hsc.measurable hs0 G hwm hw, hG⟩

end Rep

end StatFormal.RKHSReg
