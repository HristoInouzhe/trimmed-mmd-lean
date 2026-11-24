import StatFormal.Lib.TIKernel.MMD
import StatFormal.Lib.TIKernel.Gram

/-!
# The native space of a translation-invariant kernel (library, untrusted)

Every continuous `f ∈ L²` with finite native functional `∫ |𝓕₂ f|² / 𝓕k₀` is represented by some `g` with
`‖g‖² ≤ ∫ |𝓕₂ f|² / 𝓕k₀` (Wendland, Thm 10.12, one half): `G = 𝓕₂f / 𝓕k₀ ∈ L²(𝓕k₀ · vol)` represents `f` in the Fourier feature map,
and the Gram isometry transfers it to any feature map with the same kernel.
-/

noncomputable section
open MeasureTheory Filter Topology Metric Set FourierTransform Complex
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace RealInnerProductSpace

set_option linter.unusedSectionVars false

namespace StatFormal.TIKernel

open StatFormal.Wave31tp

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

lemma ft2_eq' {f : V → ℂ} (hf : MemLp f 2) : ft2 f = ⇑(𝓕 (hf.toLp f) : Lp ℂ 2 (volume : Measure V)) := by
  classical
  simp only [ft2, dif_pos hf]

lemma specMeas_eq (s : V → ℝ) : specMeas s = volume.withDensity (fun ξ => ((Real.toNNReal (s ξ) : ℝ≥0) : ℝ≥0∞)) := rfl

lemma native_eq_ft {k₀ : V → ℝ} {f : V → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2) :
    nativeN k₀ f = ∫⁻ ξ, ‖𝓕 f ξ‖ₑ ^ 2 / ENNReal.ofReal (specDens k₀ ξ) := by
  unfold nativeN
  refine lintegral_congr_ae ?_
  rw [ft2_eq' hf2]
  filter_upwards [FourierL2.fourier_toLp_ae hf1 hf2] with ξ h
  rw [h]

section Incl

variable {s : V → ℝ} (hsc : Continuous s) (hs0 : ∀ ξ, 0 ≤ s ξ) (hsi : Integrable s)
include hsc hs0 hsi

omit hsc hs0 hsi in
lemma conj_char (t : ℝ) : conj (𝐞 (-t) : ℂ) = 𝐞 t := by
  rw [← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv, neg_neg]

omit hsc hs0 hsi in
/-- The pointwise identity `‖a‖²/s = s ‖a/s‖²` (with `a = 0` where `s = 0`). -/
lemma pt_native {a : ℂ} {t : ℝ} (ht : 0 ≤ t) (h0 : t = 0 → a = 0) :
    ‖a‖ₑ ^ 2 / ENNReal.ofReal t = ENNReal.ofReal (t * ‖a / (t : ℂ)‖ ^ 2) := by
  rcases ht.lt_or_eq with htp | rfl
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htp, div_pow,
      show t * (‖a‖ ^ 2 / t ^ 2) = ‖a‖ ^ 2 / t by field_simp, ENNReal.ofReal_div_of_pos htp,
      ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  · simp [h0 rfl]

/-- **Native-space inclusion** on the Fourier side: a continuous `f ∈ L²` with finite native functional is represented in
the Fourier feature map of `s` by `G = 𝓕₂f/s`, with `‖G‖² = ∫ |𝓕₂f|²/s`. -/
theorem native_rep_fourier {f : V → ℝ} (hfc : Continuous f) (hf2 : MemLp f 2)
    (hN : ∫⁻ ξ, ‖ft2 (fun x => (f x : ℂ)) ξ‖ₑ ^ 2 / ENNReal.ofReal (s ξ) < ⊤) :
    ∃ G : Lp ℂ 2 (specMeas s), (∀ x, ⟪G, fourierFeature s x⟫ = f x) ∧
      ENNReal.ofReal (‖G‖ ^ 2) = ∫⁻ ξ, ‖ft2 (fun x => (f x : ℂ)) ξ‖ₑ ^ 2 / ENNReal.ofReal (s ξ) := by
  set F : V → ℂ := fun x => (f x : ℂ)
  have hF2 : MemLp F 2 := hf2.ofReal
  set fh := ft2 F
  have hfh : fh = ⇑(𝓕 (hF2.toLp F) : Lp ℂ 2 (volume : Measure V)) := ft2_eq' hF2
  have hfhm : StronglyMeasurable fh := by rw [hfh]; exact Lp.stronglyMeasurable _
  -- Step 1: `fh = 0` a.e. where `s = 0`
  have hzero : ∀ᵐ ξ, s ξ = 0 → fh ξ = 0 := by
    have hm : AEMeasurable (fun ξ => ‖fh ξ‖ₑ ^ 2 / ENNReal.ofReal (s ξ)) :=
      ((hfhm.measurable.enorm.pow_const 2).div (ENNReal.measurable_ofReal.comp hsc.measurable)).aemeasurable
    filter_upwards [ae_lt_top' hm hN.ne] with ξ hξ h0
    rw [h0, ENNReal.ofReal_zero] at hξ
    by_contra hne
    have : ‖fh ξ‖ₑ ^ 2 ≠ 0 := pow_ne_zero 2 (enorm_ne_zero.mpr hne)
    rw [ENNReal.div_zero this] at hξ
    exact lt_irrefl _ hξ
  set G : V → ℂ := fun ξ => fh ξ / (s ξ : ℂ)
  have hGm : StronglyMeasurable G :=
    hfhm.div (Complex.continuous_ofReal.comp hsc).stronglyMeasurable
  have hpt : ∀ᵐ ξ, ‖fh ξ‖ₑ ^ 2 / ENNReal.ofReal (s ξ) = ENNReal.ofReal (s ξ * ‖G ξ‖ ^ 2) := by
    filter_upwards [hzero] with ξ h0
    exact pt_native (hs0 ξ) h0
  have hint : Integrable (fun ξ => s ξ * ‖G ξ‖ ^ 2) := by
    refine ⟨(hsc.stronglyMeasurable.mul (hGm.norm.pow 2)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ξ => mul_nonneg (hs0 ξ) (sq_nonneg _)),
      ← lintegral_congr_ae hpt]
    exact hN
  have hval : ∫⁻ ξ, ‖fh ξ‖ₑ ^ 2 / ENNReal.ofReal (s ξ) = ENNReal.ofReal (∫ ξ, s ξ * ‖G ξ‖ ^ 2) := by
    rw [lintegral_congr_ae hpt, ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun ξ => mul_nonneg (hs0 ξ) (sq_nonneg _))]
  -- `G ∈ L²(μ_s)`
  have hG2 : MemLp G 2 (specMeas s) := by
    rw [memLp_two_iff_integrable_sq_norm hGm.aestronglyMeasurable, specMeas_eq,
      integrable_withDensity_iff_integrable_smul hsc.measurable.real_toNNReal]
    refine hint.congr (Eventually.of_forall fun ξ => ?_)
    simp [NNReal.smul_def, Real.coe_toNNReal _ (hs0 ξ)]
  haveI := specMeas_finite hsi
  -- Step 3: `fh` is integrable
  have hsG : ∀ᵐ ξ, fh ξ = (s ξ : ℂ) * G ξ := by
    filter_upwards [hzero] with ξ h0
    rcases (hs0 ξ).lt_or_eq with hp | he
    · have hne : (s ξ : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
      simp only [G]; field_simp
    · rw [← he] at h0 ⊢; simp [h0 rfl]
  have hfh1 : Integrable fh := by
    have h1 := (hG2.integrable one_le_two)
    rw [specMeas_eq, integrable_withDensity_iff_integrable_smul hsc.measurable.real_toNNReal] at h1
    refine h1.congr ?_
    filter_upwards [hsG] with ξ h
    rw [h, NNReal.smul_def, Real.coe_toNNReal _ (hs0 ξ), Complex.real_smul]
  have hfh2 : MemLp fh 2 := by rw [hfh]; exact Lp.memLp _
  -- Step 4: `F = 𝓕⁻ fh` everywhere
  have hlp : hfh2.toLp fh = 𝓕 (hF2.toLp F) :=
    Lp.ext (hfh2.coeFn_toLp.trans (Eventually.of_forall fun ξ => by rw [hfh]))
  have hae : F =ᵐ[volume] 𝓕⁻ fh := by
    have h1 := FourierL2.fourierInv_toLp_ae hfh1 hfh2
    rw [hlp, fourierInv_fourier_eq] at h1
    exact hF2.coeFn_toLp.symm.trans h1
  have hFc : Continuous F := Complex.continuous_ofReal.comp hfc
  have hic : Continuous (𝓕⁻ fh) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by simpa [Pi.neg_def] using (continuous_inner (𝕜 := ℝ) (E := V)).neg) hfh1
  have hFeq : ∀ x, F x = 𝓕⁻ fh x := fun x => congrFun ((Continuous.ae_eq_iff_eq volume hFc hic).mp hae) x
  -- Step 5: the representer
  refine ⟨hG2.toLp G, fun x => ?_, ?_⟩
  · rw [L2.inner_def]
    have e1 : ∫ ξ, ⟪(hG2.toLp G : V → ℂ) ξ, (fourierFeature s x : V → ℂ) ξ⟫ ∂(specMeas s) =
        ∫ ξ, s ξ * (G ξ * (𝐞 ⟪x, ξ⟫ : ℂ)).re := by
      rw [← integral_specMeas hsc.measurable hs0]
      refine integral_congr_ae ?_
      filter_upwards [hG2.coeFn_toLp, fourierFeature_ae s hsi x] with ξ h1 h2
      rw [h1, h2, Complex.inner]
      erw [← conj_char ⟪x, ξ⟫]
      simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    rw [e1]
    have hx : f x = (𝓕⁻ fh x).re := by rw [← hFeq x]; rfl
    rw [hx]
    have hI : 𝓕⁻ fh x = ∫ ξ, (𝐞 ⟪ξ, x⟫ : ℂ) * fh ξ := by rw [Real.fourierInv_eq]; rfl
    have hint2 : Integrable (fun ξ => (𝐞 ⟪ξ, x⟫ : ℂ) * fh ξ) :=
      integrable_char_mul hfh1 (fun ξ => ⟪ξ, x⟫) (continuous_id.inner continuous_const)
    have ere := (integral_re hint2).symm
    simp only [RCLike.re_to_complex] at ere
    rw [hI, ere]
    refine integral_congr_ae ?_
    filter_upwards [hsG] with ξ h
    rw [h, real_inner_comm]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  · have hn : ‖hG2.toLp G‖ ^ 2 = ∫ ξ, s ξ * ‖G ξ‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def, ← integral_specMeas hsc.measurable hs0]
      refine integral_congr_ae ?_
      filter_upwards [hG2.coeFn_toLp] with ξ h1
      rw [h1, real_inner_self_eq_norm_sq]
    rw [hn, ← hval]

end Incl

section Feature

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {φ : V → H} {k₀ : V → ℝ} (hφ : ∀ x y, ⟪φ x, φ y⟫ = k₀ (x - y)) (hc : Continuous k₀) (hi : Integrable k₀)
include hφ hc hi

/-- Wave31tp L17 (eq:newnative, the inclusion with `≤`), all conclusions. -/
theorem native_incl_facts (f : V → ℝ) :
    (Continuous f → MemLp f 2 → nativeN k₀ (fun x => (f x : ℂ)) < ⊤ →
      ∃ g : H, (∀ x, ⟪g, φ x⟫ = f x) ∧ ENNReal.ofReal (‖g‖ ^ 2) ≤ nativeN k₀ (fun x => (f x : ℂ))) ∧
    (Integrable f → MemLp f 2 →
      nativeN k₀ (fun x => (f x : ℂ)) = ∫⁻ ξ, ‖𝓕 (fun x => (f x : ℂ)) ξ‖ₑ ^ 2 / ENNReal.ofReal (specDens k₀ ξ)) := by
  refine ⟨fun hfc hf2 hN => ?_, fun hf1 hf2 => native_eq_ft hf1.ofReal hf2.ofReal⟩
  have hfe := feature_exists_facts hc hi (gram_posdef hφ)
  obtain ⟨hsc, -, hs0, hsi, -, hΨ⟩ := hfe
  obtain ⟨G, hG, hGn⟩ := native_rep_fourier hsc hs0 hsi hfc hf2 hN
  have hgram : ∀ x y, ⟪fourierFeature (specDens k₀) x, fourierFeature (specDens k₀) y⟫ = ⟪φ x, φ y⟫ :=
    fun x y => by rw [hΨ, hφ]
  obtain ⟨g, hgn, hg⟩ := gram_rep_le hgram G
  refine ⟨g, fun x => by rw [hg, hG], ?_⟩
  unfold nativeN
  rw [← hGn]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hgn 2)

end Feature

lemma pt_sob (a : ℝ≥0∞) {sp c w : ℝ} (hc : 0 < c) (hw : 0 < w) (hsp : c * w⁻¹ ≤ sp) :
    a / ENNReal.ofReal sp ≤ a * ENNReal.ofReal w * (ENNReal.ofReal c)⁻¹ := by
  have h1 : ENNReal.ofReal (c / w) ≤ ENNReal.ofReal sp := ENNReal.ofReal_le_ofReal (by rwa [div_eq_mul_inv])
  calc a / ENNReal.ofReal sp = a * (ENNReal.ofReal sp)⁻¹ := div_eq_mul_inv _ _
    _ ≤ a * (ENNReal.ofReal (c / w))⁻¹ := by gcongr
    _ = a * ENNReal.ofReal (w / c) := by rw [← ENNReal.ofReal_inv_of_pos (div_pos hc hw), inv_div]
    _ = a * ENNReal.ofReal w * (ENNReal.ofReal c)⁻¹ := by
        rw [ENNReal.ofReal_div_of_pos hc, div_eq_mul_inv, mul_assoc]

section Sob

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {φ : V → H} {k₀ : V → ℝ} (hφ : ∀ x y, ⟪φ x, φ y⟫ = k₀ (x - y)) (hc : Continuous k₀) (hi : Integrable k₀)
include hφ hc hi

/-- Wave31tp L19 (a): a spectral lower bound puts the Sobolev functions in the RKHS. -/
theorem sobolev_incl_facts {c s : ℝ} (hc0 : 0 < c)
    (hlow : ∀ ξ, c * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-s) ≤ specDens k₀ ξ) {f : V → ℝ} (hfc : Continuous f)
    (hf2 : MemLp f 2) (hS : sobolevS s (fun x => (f x : ℂ)) < ⊤) :
    ∃ g : H, (∀ x, ⟪g, φ x⟫ = f x) ∧
      ENNReal.ofReal (‖g‖ ^ 2) ≤ sobolevS s (fun x => (f x : ℂ)) / ENNReal.ofReal c := by
  have hle : nativeN k₀ (fun x => (f x : ℂ)) ≤ sobolevS s (fun x => (f x : ℂ)) / ENNReal.ofReal c := by
    unfold nativeN sobolevS
    rw [div_eq_mul_inv, ← lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr (by simpa using hc0))]
    refine lintegral_mono fun ξ => ?_
    have hw : 0 < (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ s := Real.rpow_pos_of_pos (by positivity) s
    refine pt_sob _ hc0 hw ?_
    have := hlow ξ
    rwa [Real.rpow_neg (by positivity)] at this
  have hN : nativeN k₀ (fun x => (f x : ℂ)) < ⊤ :=
    hle.trans_lt (ENNReal.div_lt_top hS.ne (ENNReal.ofReal_pos.mpr hc0).ne')
  obtain ⟨g, hg, hgn⟩ := (native_incl_facts hφ hc hi f).1 hfc hf2 hN
  exact ⟨g, hg, hgn.trans hle⟩

end Sob

end StatFormal.TIKernel
