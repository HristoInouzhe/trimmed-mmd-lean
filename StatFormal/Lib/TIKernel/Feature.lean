import StatFormal.Lib.TIKernel.Profile
import StatFormal.Lib.FourierL2.Agree
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# The Fourier feature map of a spectral density (library, untrusted)

For `ψ ≥ 0` integrable on `V`, the map `x ↦ [ξ ↦ 𝐞(−⟪x, ξ⟫)] ∈ L²(ψ · vol; ℂ)` (with its real inner product) is a continuous feature
map with Gram function `k_ψ(x − y)`, `k_ψ(z) = ∫ ψ cos(2π⟪z, ξ⟫)`; `k_ψ` is the Fourier transform of the even part of `ψ`, and the
transform of an integrable `k_ψ` is that even part. Every continuous integrable positive definite real profile is such a `k_ψ`.
-/

noncomputable section
open MeasureTheory Filter Topology Metric Set FourierTransform Complex
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace RealInnerProductSpace

set_option linter.unusedSectionVars false

namespace StatFormal.TIKernel

open StatFormal.Wave31tp

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

lemma specMeas_finite {ψ : V → ℝ} (hψi : Integrable ψ) : IsFiniteMeasure (specMeas ψ) := by
  constructor
  rw [specMeas, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact hψi.lintegral_lt_top

/-- Integrals against `ψ · vol`. -/
lemma integral_specMeas {ψ : V → ℝ} (hψm : Measurable ψ) (hψ0 : ∀ ξ, 0 ≤ ψ ξ) (g : V → ℝ) :
    ∫ ξ, g ξ ∂(specMeas ψ) = ∫ ξ, ψ ξ * g ξ := by
  have : specMeas ψ = volume.withDensity (fun ξ => ((Real.toNNReal (ψ ξ) : ℝ≥0) : ℝ≥0∞)) := rfl
  rw [this, integral_withDensity_eq_integral_smul hψm.real_toNNReal]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp [NNReal.smul_def, Real.coe_toNNReal _ (hψ0 ξ)]

lemma char_conj_mul (a b : ℝ) : conj (𝐞 a : ℂ) * (𝐞 b : ℂ) = (𝐞 (b - a) : ℂ) := by
  rw [mul_comm]; exact e_mul_conj b a

lemma memLp_char (ψ : V → ℝ) (hψi : Integrable ψ) (x : V) :
    MemLp (fun ξ => (𝐞 (-⟪x, ξ⟫) : ℂ)) 2 (specMeas ψ) := by
  haveI := specMeas_finite hψi
  refine MemLp.of_bound ((continuous_subtype_val.comp (Real.continuous_fourierChar.comp
    (continuous_const.inner continuous_id).neg)).aestronglyMeasurable) 1 (Eventually.of_forall fun ξ => ?_)
  simp [Circle.norm_coe]

lemma fourierFeature_ae (ψ : V → ℝ) (hψi : Integrable ψ) (x : V) :
    (fourierFeature ψ x : V → ℂ) =ᵐ[specMeas ψ] fun ξ => (𝐞 (-⟪x, ξ⟫) : ℂ) := by
  classical
  have h := memLp_char ψ hψi x
  simp only [fourierFeature, dif_pos h]
  exact h.coeFn_toLp

lemma inner_fourierFeature {ψ : V → ℝ} (hψm : Measurable ψ) (hψ0 : ∀ ξ, 0 ≤ ψ ξ) (hψi : Integrable ψ) (x y : V) :
    ⟪fourierFeature ψ x, fourierFeature ψ y⟫ = kSpec ψ (x - y) := by
  rw [L2.inner_def]
  have h1 : ∫ ξ, ⟪(fourierFeature ψ x : V → ℂ) ξ, (fourierFeature ψ y : V → ℂ) ξ⟫ ∂(specMeas ψ) =
      ∫ ξ, Real.cos (2 * Real.pi * ⟪x - y, ξ⟫) ∂(specMeas ψ) := by
    refine integral_congr_ae ?_
    filter_upwards [fourierFeature_ae ψ hψi x, fourierFeature_ae ψ hψi y] with ξ hx hy
    rw [hx, hy, Complex.inner]
    erw [e_mul_conj, fourierChar_re]
    congr 1
    rw [inner_sub_left]
    ring
  rw [h1, integral_specMeas hψm hψ0, kSpec]

lemma kSpec_continuous {ψ : V → ℝ} (hψi : Integrable ψ) : Continuous (kSpec ψ) := by
  refine continuous_of_dominated (bound := fun ξ => |ψ ξ|) (fun z => ?_) (fun z => ?_) hψi.abs ?_
  · exact hψi.aestronglyMeasurable.mul (by fun_prop)
  · refine Eventually.of_forall fun ξ => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |ψ ξ| * |Real.cos (2 * Real.pi * ⟪z, ξ⟫)| ≤ |ψ ξ| * 1 := by gcongr; exact Real.abs_cos_le_one _
      _ = |ψ ξ| := mul_one _
  · exact Eventually.of_forall fun ξ => continuous_const.mul (by fun_prop)

lemma kSpec_even (ψ : V → ℝ) (z : V) : kSpec ψ (-z) = kSpec ψ z := by
  simp [kSpec, inner_neg_left, Real.cos_neg]

lemma kSpec_zero (ψ : V → ℝ) : kSpec ψ 0 = ∫ ξ, ψ ξ := by
  simp [kSpec]

lemma kSpec_abs_le {ψ : V → ℝ} (hψ0 : ∀ ξ, 0 ≤ ψ ξ) (hψi : Integrable ψ) (z : V) : |kSpec ψ z| ≤ kSpec ψ 0 := by
  rw [kSpec_zero, kSpec]
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
    hψi (Eventually.of_forall fun ξ => ?_))
  dsimp only
  rw [abs_mul, abs_of_nonneg (hψ0 ξ)]
  calc ψ ξ * |Real.cos (2 * Real.pi * ⟪z, ξ⟫)| ≤ ψ ξ * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (hψ0 ξ)
    _ = ψ ξ := mul_one _

/-- Fourier inversion almost everywhere: `𝓕 (𝓕⁻ g) = g` a.e. for `g` and `𝓕⁻ g` integrable. -/
theorem fourier_fourierInv_ae {g : V → ℂ} (hg : Integrable g) (hg' : Integrable (𝓕⁻ g)) :
    𝓕 (𝓕⁻ g) =ᵐ[volume] g := by
  have hc : Continuous (𝓕 (𝓕⁻ g)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hg'
  refine ae_eq_of_integral_contDiff_smul_eq hc.locallyIntegrable hg.locallyIntegrable ?_
  intro u hu hus
  set U := FourierL2.testToSchwartz hu hus
  have e1 : ∀ F : V → ℂ, ∫ x, u x • F x = ∫ x, U x • F x := fun F => by
    simp [U, FourierL2.real_smul_eq]
  rw [e1, e1, ← FourierL2.integral_fourier_smul_of_schwartz U hg']
  have h2 := FourierL2.integral_fourierInv_smul_of_schwartz (𝓕 U) hg
  rw [← SchwartzMap.fourierInv_coe, fourierInv_fourier_eq, SchwartzMap.fourier_coe] at h2
  exact h2.symm

lemma integrable_mul_cos {ψ : V → ℝ} (hψi : Integrable ψ) (g : V → ℝ) (hg : Continuous g) :
    Integrable (fun ξ => ψ ξ * Real.cos (g ξ)) := by
  refine hψi.mono (hψi.aestronglyMeasurable.mul (Real.continuous_cos.comp hg).aestronglyMeasurable)
    (Eventually.of_forall fun ξ => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  calc |ψ ξ| * |Real.cos (g ξ)| ≤ |ψ ξ| * 1 := by gcongr; exact Real.abs_cos_le_one _
    _ = |ψ ξ| := mul_one _

lemma kSpec_even_part {ψ : V → ℝ} (hψi : Integrable ψ) (w : V) :
    ∫ ξ, (ψ ξ + ψ (-ξ)) / 2 * Real.cos (2 * Real.pi * ⟪ξ, w⟫) = kSpec ψ w := by
  have hneg : ∫ ξ, ψ (-ξ) * Real.cos (2 * Real.pi * ⟪ξ, w⟫) = ∫ ξ, ψ ξ * Real.cos (2 * Real.pi * ⟪ξ, w⟫) := by
    have := integral_neg_eq_self (fun ξ => ψ ξ * Real.cos (2 * Real.pi * ⟪ξ, w⟫)) volume
    simpa [inner_neg_left, Real.cos_neg] using this
  have hi1 := integrable_mul_cos hψi (fun ξ => 2 * Real.pi * ⟪ξ, w⟫) (by fun_prop)
  have hi2 := integrable_mul_cos hψi.comp_neg (fun ξ => 2 * Real.pi * ⟪ξ, w⟫) (by fun_prop)
  have : (fun ξ => (ψ ξ + ψ (-ξ)) / 2 * Real.cos (2 * Real.pi * ⟪ξ, w⟫)) =
      fun ξ => (ψ ξ * Real.cos (2 * Real.pi * ⟪ξ, w⟫) + ψ (-ξ) * Real.cos (2 * Real.pi * ⟪ξ, w⟫)) / 2 := by
    funext ξ; ring
  rw [this, integral_div, integral_add hi1 hi2, hneg, kSpec]
  simp_rw [real_inner_comm w]
  ring

/-- The kernel of a spectral density is the Fourier transform (and the inverse transform) of its even part. -/
lemma kSpec_eq_fourier {ψ : V → ℝ} (hψi : Integrable ψ) (z : V) :
    (kSpec ψ z : ℂ) = 𝓕 (fun ξ => (((ψ ξ + ψ (-ξ)) / 2 : ℝ) : ℂ)) z ∧
      (kSpec ψ z : ℂ) = 𝓕⁻ (fun ξ => (((ψ ξ + ψ (-ξ)) / 2 : ℝ) : ℂ)) z := by
  have hev : ∀ ξ : V, (ψ (-ξ) + ψ (-(-ξ))) / 2 = (ψ ξ + ψ (-ξ)) / 2 := fun ξ => by rw [neg_neg, add_comm]
  have hei : Integrable (fun ξ => (ψ ξ + ψ (-ξ)) / 2) := (hψi.add hψi.comp_neg).div_const 2
  have hF : ∀ w, 𝓕 (fun ξ => (((ψ ξ + ψ (-ξ)) / 2 : ℝ) : ℂ)) w = (kSpec ψ w : ℂ) := fun w => by
    rw [fourier_even_real (k₀ := fun ξ => (ψ ξ + ψ (-ξ)) / 2) hev hei w, kSpec_even_part hψi w]
  refine ⟨(hF z).symm, ?_⟩
  rw [Real.fourierInv_eq_fourier_neg, hF, kSpec_even]

/-- Cosine inversion for a continuous integrable positive definite real profile. -/
lemma cos_inversion {k₀ : V → ℝ} (hc : Continuous k₀) (hi : Integrable k₀)
    (hpd : IsPosDefFun (fun z => (k₀ z : ℂ))) (z : V) :
    k₀ z = ∫ ξ, specDens k₀ ξ * Real.cos (2 * Real.pi * ⟪z, ξ⟫) := by
  have hcc : Continuous (fun z => (k₀ z : ℂ)) := Complex.continuous_ofReal.comp hc
  obtain ⟨-, -, -, hnn, hint, -, hinv⟩ := bochner_integrable hcc (hi.ofReal (𝕜 := ℂ)) hpd
  have hreal : ∀ ξ, 𝓕 (fun x => (k₀ x : ℂ)) ξ = (specDens k₀ ξ : ℂ) :=
    fun ξ => Complex.ext rfl (by simp [specDens, (hnn ξ).1])
  have h1 := congrFun hinv z
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
  simp only [Complex.mul_re, fourierChar_re]
  simp [real_inner_comm, mul_comm]

/-- Wave31tp L15 (first part), all conclusions. -/
theorem fourier_feature_facts {ψ : V → ℝ} (hψm : Measurable ψ) (hψ0 : ∀ ξ, 0 ≤ ψ ξ) (hψi : Integrable ψ) :
    CompleteSpace (Lp ℂ 2 (specMeas ψ)) ∧ TopologicalSpace.SeparableSpace (Lp ℂ 2 (specMeas ψ)) ∧
      Continuous (fourierFeature ψ) ∧
      (∀ x, (fourierFeature ψ x : V → ℂ) =ᵐ[specMeas ψ] fun ξ => (𝐞 (-⟪x, ξ⟫) : ℂ)) ∧
      (∀ x y, ⟪fourierFeature ψ x, fourierFeature ψ y⟫ = kSpec ψ (x - y)) ∧
      Continuous (kSpec ψ) ∧ (∀ z, kSpec ψ (-z) = kSpec ψ z) ∧ (∀ z, |kSpec ψ z| ≤ kSpec ψ 0) ∧
      kSpec ψ 0 = ∫ ξ, ψ ξ ∧
      (∀ z, (kSpec ψ z : ℂ) = 𝓕 (fun ξ => (((ψ ξ + ψ (-ξ)) / 2 : ℝ) : ℂ)) z ∧
            (kSpec ψ z : ℂ) = 𝓕⁻ (fun ξ => (((ψ ξ + ψ (-ξ)) / 2 : ℝ) : ℂ)) z) ∧
      (Integrable (kSpec ψ) →
        (𝓕 (fun z => (kSpec ψ z : ℂ)) =ᵐ[volume] fun ξ => (((ψ ξ + ψ (-ξ)) / 2 : ℝ) : ℂ)) ∧
        (Continuous ψ → ∀ ξ, 𝓕 (fun z => (kSpec ψ z : ℂ)) ξ = (((ψ ξ + ψ (-ξ)) / 2 : ℝ) : ℂ))) := by
  haveI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
  haveI : SFinite (specMeas ψ) := by unfold specMeas; infer_instance
  have hinner := inner_fourierFeature hψm hψ0 hψi
  have hkc := kSpec_continuous hψi
  have hcont : Continuous (fourierFeature ψ) := ((gram_cont_iff hinner).1).2 hkc.continuousAt
  have hinv : (fun z => (kSpec ψ z : ℂ)) = 𝓕⁻ (fun ξ => (((ψ ξ + ψ (-ξ)) / 2 : ℝ) : ℂ)) :=
    funext fun z => (kSpec_eq_fourier hψi z).2
  have hfw : (fun z => (kSpec ψ z : ℂ)) = 𝓕 (fun ξ => (((ψ ξ + ψ (-ξ)) / 2 : ℝ) : ℂ)) :=
    funext fun z => (kSpec_eq_fourier hψi z).1
  have hei : Integrable (fun ξ => (((ψ ξ + ψ (-ξ)) / 2 : ℝ) : ℂ)) :=
    ((hψi.add hψi.comp_neg).div_const 2).ofReal
  refine ⟨inferInstance, inferInstance, hcont, fourierFeature_ae ψ hψi, hinner, hkc, kSpec_even ψ,
    kSpec_abs_le hψ0 hψi, kSpec_zero ψ, kSpec_eq_fourier hψi, fun hki => ⟨?_, fun hψc ξ => ?_⟩⟩
  · rw [hinv]
    exact fourier_fourierInv_ae hei (by rw [← hinv]; exact hki.ofReal)
  · rw [hinv]
    refine Integrable.fourier_fourierInv_eq hei (by rw [← hfw]; exact hki.ofReal) ?_
    exact (Complex.continuous_ofReal.comp ((hψc.add (hψc.comp continuous_neg)).div_const 2)).continuousAt

/-- Wave31tp L15 (existence). -/
theorem feature_exists_facts {k₀ : V → ℝ} (hc : Continuous k₀) (hi : Integrable k₀)
    (hpd : IsPosDefFun (fun z => (k₀ z : ℂ))) :
    Continuous (specDens k₀) ∧ (∀ ξ, specDens k₀ (-ξ) = specDens k₀ ξ) ∧ (∀ ξ, 0 ≤ specDens k₀ ξ) ∧
      Integrable (specDens k₀) ∧ kSpec (specDens k₀) = k₀ ∧
      ∀ x y, ⟪fourierFeature (specDens k₀) x, fourierFeature (specDens k₀) y⟫ = k₀ (x - y) := by
  have hcc : Continuous (fun z => (k₀ z : ℂ)) := Complex.continuous_ofReal.comp hc
  obtain ⟨hneg, -, -, hnn, hint, -, -⟩ := bochner_integrable hcc (hi.ofReal (𝕜 := ℂ)) hpd
  have hev : ∀ z, k₀ (-z) = k₀ z := fun z => by
    have := hneg z
    simp only [Complex.conj_ofReal] at this
    exact_mod_cast this
  have hsc : Continuous (specDens k₀) := Complex.continuous_re.comp
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner (hi.ofReal (𝕜 := ℂ)))
  have hsev : ∀ ξ, specDens k₀ (-ξ) = specDens k₀ ξ := fun ξ => by
    simp only [specDens, fourier_even_real hev hi, Complex.ofReal_re, inner_neg_right, mul_neg, Real.cos_neg]
  have hs0 : ∀ ξ, 0 ≤ specDens k₀ ξ := fun ξ => (hnn ξ).2
  have hsi : Integrable (specDens k₀) := hint.re
  have hk : kSpec (specDens k₀) = k₀ := funext fun z => (cos_inversion hc hi hpd z).symm
  refine ⟨hsc, hsev, hs0, hsi, hk, fun x y => ?_⟩
  rw [inner_fourierFeature hsc.measurable hs0 hsi, hk]

end StatFormal.TIKernel
