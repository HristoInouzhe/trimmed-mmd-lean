import StatFormal.Lib.TIKernel.Bochner

/-!
# Gram profiles of translation-invariant feature maps (library, untrusted)

If `⟪φ x, φ y⟫ = k₀ (x − y)` for a real inner-product space `ℋ`, then `k₀` is even, `|k₀| ≤ k₀ 0`,
`‖φ x − φ y‖² = 2 (k₀ 0 − k₀ (x − y))`, the complex cast of `k₀` is positive definite, and continuity of `φ`, of `k₀` and of
`k₀` at `0` are equivalent. For integrable `k₀` the Fourier transform is real and even (the cosine transform); with continuity,
Bochner's theorem (integrable case) gives a nonnegative integrable spectral density with `∫ = k₀ 0` and the cosine inversion formula.
-/

noncomputable section
open MeasureTheory Filter Topology Metric Set FourierTransform Complex
open scoped ENNReal ComplexConjugate InnerProductSpace RealInnerProductSpace

set_option linter.unusedSectionVars false

namespace StatFormal.TIKernel

open StatFormal.Wave31tp

lemma fourierChar_re (t : ℝ) : ((𝐞 t : ℂ)).re = Real.cos (2 * Real.pi * t) := by
  rw [Real.fourierChar_apply, Complex.exp_ofReal_mul_I_re]

lemma fourierChar_im (t : ℝ) : ((𝐞 t : ℂ)).im = Real.sin (2 * Real.pi * t) := by
  rw [Real.fourierChar_apply, Complex.exp_ofReal_mul_I_im]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

section Gram

variable {φ : V → H} {k₀ : V → ℝ} (hφ : ∀ x y, ⟪φ x, φ y⟫ = k₀ (x - y))
include hφ

lemma gram_even (z : V) : k₀ (-z) = k₀ z := by
  have h1 := hφ z 0
  have h2 := hφ 0 z
  rw [real_inner_comm] at h2
  rw [sub_zero] at h1; rw [zero_sub] at h2
  rw [← h1, h2]

lemma gram_norm_sq (x : V) : ‖φ x‖ ^ 2 = k₀ 0 := by
  rw [← real_inner_self_eq_norm_sq, hφ, sub_self]

lemma gram_abs_le (z : V) : |k₀ z| ≤ k₀ 0 := by
  have h := abs_real_inner_le_norm (φ z) (φ 0)
  rw [hφ, sub_zero] at h
  have hn : ‖φ z‖ * ‖φ 0‖ = k₀ 0 := by
    have h1 := gram_norm_sq hφ z
    have h2 := gram_norm_sq hφ 0
    have hz : ‖φ z‖ = ‖φ 0‖ := by
      have := h1.trans h2.symm
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
    rw [hz, ← sq, h2]
  linarith

lemma gram_dist_sq (x y : V) : ‖φ x - φ y‖ ^ 2 = 2 * (k₀ 0 - k₀ (x - y)) := by
  rw [@norm_sub_sq_real, gram_norm_sq hφ, gram_norm_sq hφ, hφ]
  ring

lemma gram_quad {n : ℕ} (x : Fin n → V) (w : Fin n → ℝ) :
    ∑ i, ∑ j, w i * w j * k₀ (x i - x j) = ‖∑ i, w i • φ (x i)‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_smul_left, real_inner_smul_right, hφ]
  ring

lemma gram_posdef : IsPosDefFun (fun z => (k₀ z : ℂ)) := by
  intro n x c
  set a : Fin n → ℝ := fun i => (c i).re
  set b : Fin n → ℝ := fun i => (c i).im
  have hsym : ∀ i j, k₀ (x i - x j) = k₀ (x j - x i) := fun i j => by
    rw [← gram_even hφ, neg_sub]
  have hterm : ∀ i j, c i * conj (c j) * (k₀ (x i - x j) : ℂ) =
      (((a i * a j + b i * b j) * k₀ (x i - x j) : ℝ) : ℂ) +
        (((b i * a j - a i * b j) * k₀ (x i - x j) : ℝ) : ℂ) * Complex.I := by
    intro i j
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.add_re, Complex.I_re, Complex.I_im, a, b]
      ring
    · simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.add_im, Complex.I_re, Complex.I_im, a, b]
      ring
  simp_rw [hterm, Finset.sum_add_distrib]
  have hanti : ∑ i, ∑ j, (b i * a j - a i * b j) * k₀ (x i - x j) = 0 := by
    have h2 : ∑ i, ∑ j, (b i * a j - a i * b j) * k₀ (x i - x j) =
        -∑ i, ∑ j, (b i * a j - a i * b j) * k₀ (x i - x j) := by
      conv_rhs => rw [Finset.sum_comm]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hsym]; ring
    linarith
  have hre : ∑ i, ∑ j, (a i * a j + b i * b j) * k₀ (x i - x j) =
      ‖∑ i, a i • φ (x i)‖ ^ 2 + ‖∑ i, b i • φ (x i)‖ ^ 2 := by
    rw [← gram_quad hφ x a, ← gram_quad hφ x b, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp only [Complex.add_im, Complex.add_re, Complex.im_sum, Complex.re_sum, Complex.ofReal_im,
    Complex.ofReal_re, Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    zero_mul, sub_zero, add_zero, zero_add]
  rw [hanti, hre]
  exact ⟨by simp, by positivity⟩

lemma gram_cont_iff : (Continuous φ ↔ ContinuousAt k₀ 0) ∧ (ContinuousAt k₀ 0 ↔ Continuous k₀) := by
  have hk : Continuous φ → Continuous k₀ := fun h => by
    have : k₀ = fun z => ⟪φ z, φ 0⟫ := funext fun z => by rw [hφ, sub_zero]
    rw [this]; exact h.inner continuous_const
  have hφc : ContinuousAt k₀ 0 → Continuous φ := by
    intro h0
    refine continuous_iff_continuousAt.mpr fun x => ?_
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have h1 : Tendsto (fun y => k₀ (y - x)) (𝓝 x) (𝓝 (k₀ 0)) := by
      have : Tendsto (fun y : V => y - x) (𝓝 x) (𝓝 0) := by
        have := ((continuous_sub_right x).tendsto x)
        simpa using this
      exact h0.tendsto.comp this
    have h2 : Tendsto (fun y => Real.sqrt (2 * (k₀ 0 - k₀ (y - x)))) (𝓝 x) (𝓝 0) := by
      have := (((tendsto_const_nhds (x := k₀ 0)).sub h1).const_mul 2).sqrt
      simpa using this
    refine h2.congr fun y => ?_
    rw [← gram_dist_sq hφ y x, Real.sqrt_sq (norm_nonneg _)]
  exact ⟨⟨fun h => (hk h).continuousAt, hφc⟩, ⟨fun h => hk (hφc h), fun h => h.continuousAt⟩⟩

end Gram

section Fourier

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma integrable_char_mul {f : V → ℂ} (hf : Integrable f) (g : V → ℝ) (hg : Continuous g) :
    Integrable (fun x => (𝐞 (g x) : ℂ) * f x) := by
  refine hf.mono ((continuous_subtype_val.comp (Real.continuous_fourierChar.comp hg)).aestronglyMeasurable.mul
    hf.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
  rw [norm_mul, Circle.norm_coe, one_mul]

/-- The Fourier transform of an even integrable real profile is its cosine transform. -/
lemma fourier_even_real {k₀ : V → ℝ} (hev : ∀ z, k₀ (-z) = k₀ z) (hi : Integrable k₀) (ξ : V) :
    𝓕 (fun x => (k₀ x : ℂ)) ξ = ((∫ x, k₀ x * Real.cos (2 * Real.pi * ⟪x, ξ⟫) : ℝ) : ℂ) := by
  have hint := integrable_char_mul (hi.ofReal (𝕜 := ℂ)) (fun x => -⟪x, ξ⟫) (continuous_id.inner continuous_const).neg
  have hF : 𝓕 (fun x => (k₀ x : ℂ)) ξ = ∫ x, (𝐞 (-⟪x, ξ⟫) : ℂ) * (k₀ x : ℂ) := by
    rw [Real.fourier_eq]; rfl
  rw [hF]
  have ere := (integral_re hint).symm
  have eim := (integral_im hint).symm
  simp only [RCLike.re_to_complex, RCLike.im_to_complex] at ere eim
  apply Complex.ext
  · erw [ere, Complex.ofReal_re]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Complex.mul_re, fourierChar_re]
    simp [mul_comm, Real.cos_neg]
  · erw [eim, Complex.ofReal_im]
    have hS : ∫ x, Real.sin (2 * Real.pi * ⟪x, ξ⟫) * k₀ x = 0 := by
      have h := integral_neg_eq_self (fun x => Real.sin (2 * Real.pi * ⟪x, ξ⟫) * k₀ x) volume
      simp only [inner_neg_left, mul_neg, Real.sin_neg, hev, neg_mul] at h
      rw [integral_neg] at h
      linarith
    calc ∫ x, ((𝐞 (-⟪x, ξ⟫) : ℂ) * (k₀ x : ℂ)).im = ∫ x, -(Real.sin (2 * Real.pi * ⟪x, ξ⟫) * k₀ x) := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp only [Complex.mul_im, fourierChar_im]
          simp [Real.sin_neg]
      _ = 0 := by rw [integral_neg, hS, neg_zero]

variable {φ : V → H} {k₀ : V → ℝ} (hφ : ∀ x y, ⟪φ x, φ y⟫ = k₀ (x - y))
include hφ

/-- All conclusions of Wave31tp L14 (`gram_profile`) on spectral densities. -/
lemma gram_spec_even (hi : Integrable k₀) :
    (∀ ξ, 𝓕 (fun x => (k₀ x : ℂ)) ξ = ((∫ x, k₀ x * Real.cos (2 * Real.pi * ⟪x, ξ⟫) : ℝ) : ℂ)) ∧
    ∀ ξ, specDens k₀ (-ξ) = specDens k₀ ξ := by
  have hev := gram_even hφ
  refine ⟨fourier_even_real hev hi, fun ξ => ?_⟩
  simp only [specDens, fourier_even_real hev hi, Complex.ofReal_re, inner_neg_right, mul_neg, Real.cos_neg]

lemma gram_spec_bochner (hi : Integrable k₀) (hc : Continuous k₀) :
    (∀ ξ, 0 ≤ specDens k₀ ξ) ∧ Integrable (specDens k₀) ∧ ∫ ξ, specDens k₀ ξ = k₀ 0 ∧
      ∀ z, k₀ z = ∫ ξ, specDens k₀ ξ * Real.cos (2 * Real.pi * ⟪z, ξ⟫) := by
  have hpd := gram_posdef hφ
  have hcc : Continuous (fun z => (k₀ z : ℂ)) := Complex.continuous_ofReal.comp hc
  obtain ⟨-, -, -, hnn, hint, hval, hinv⟩ := bochner_integrable hcc (hi.ofReal (𝕜 := ℂ)) hpd
  have hreal : ∀ ξ, 𝓕 (fun x => (k₀ x : ℂ)) ξ = (specDens k₀ ξ : ℂ) :=
    fun ξ => Complex.ext rfl (by simp [specDens, (hnn ξ).1])
  refine ⟨fun ξ => (hnn ξ).2, hint.re, ?_, fun z => ?_⟩
  · have := (integral_re hint).symm
    simp only [RCLike.re_to_complex] at this
    simp only [specDens]
    rw [← this, hval, Complex.ofReal_re]
  · have h1 := congrFun hinv z
    have hI : 𝓕⁻ (𝓕 (fun x => (k₀ x : ℂ))) z = ∫ ξ, (𝐞 ⟪ξ, z⟫ : ℂ) * 𝓕 (fun x => (k₀ x : ℂ)) ξ := by
      rw [Real.fourierInv_eq]; rfl
    rw [hI] at h1
    simp_rw [hreal] at h1
    have hint2 : Integrable (fun ξ => (𝐞 ⟪ξ, z⟫ : ℂ) * (specDens k₀ ξ : ℂ)) :=
      integrable_char_mul (hint.re.ofReal (𝕜 := ℂ)) (fun ξ => ⟪ξ, z⟫) (continuous_id.inner continuous_const)
    have ere := (integral_re hint2).symm
    simp only [RCLike.re_to_complex] at ere
    have := congrArg Complex.re h1
    rw [ere, Complex.ofReal_re] at this
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, fourierChar_re]
    rw [real_inner_comm, mul_comm]

end Fourier

end StatFormal.TIKernel
