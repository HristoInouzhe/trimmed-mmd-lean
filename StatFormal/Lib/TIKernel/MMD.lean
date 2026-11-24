import StatFormal.Lib.TIKernel.Feature
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Fourier transforms of finite measures and the MMD in Fourier form (library, untrusted)

`ftMeas μ ξ = ∫ 𝐞(−⟪x, ξ⟫) dμ` is continuous, bounded by the mass, equal to the mass at `0`, equal to `𝓕 f` for `μ = f · vol`, and
determines `μ` (Mathlib's `Measure.ext_of_charFun`). For a translation-invariant feature map with continuous integrable profile `k₀`,
`‖∫ φ dμ₁ − ∫ φ dμ₂‖² = ∫ 𝓕k₀ · |ftMeas μ₁ − ftMeas μ₂|²` (Fubini with the cosine inversion of `k₀`) and equals the four-term
double integral of `k₀` (Sriperumbudur et al. 2010).
-/

noncomputable section
open MeasureTheory Filter Topology Metric Set FourierTransform Complex
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace RealInnerProductSpace

set_option linter.unusedSectionVars false

namespace StatFormal.TIKernel

open StatFormal.Wave31tp

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

lemma char_continuous (ξ : V) : Continuous fun x : V => (𝐞 (-⟪x, ξ⟫) : ℂ) :=
  continuous_subtype_val.comp (Real.continuous_fourierChar.comp (continuous_id.inner continuous_const).neg)

lemma ftMeas_continuous (μ : Measure V) [IsFiniteMeasure μ] : Continuous (ftMeas μ) := by
  refine continuous_of_dominated (bound := fun _ => (1 : ℝ)) (fun ξ => (char_continuous ξ).aestronglyMeasurable)
    (fun ξ => Eventually.of_forall fun x => by simp [Circle.norm_coe]) (integrable_const 1) ?_
  refine Eventually.of_forall fun x => ?_
  exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp (continuous_const.inner continuous_id).neg)

lemma ftMeas_norm_le (μ : Measure V) [IsFiniteMeasure μ] (ξ : V) : ‖ftMeas μ ξ‖ ≤ μ.real univ := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp [Circle.norm_coe]

lemma ftMeas_zero (μ : Measure V) [IsFiniteMeasure μ] : ftMeas μ 0 = (μ.real univ : ℂ) := by
  simp [ftMeas]

lemma ftMeas_eq_charFun (μ : Measure V) (ξ : V) : ftMeas μ ξ = charFun μ (-(2 * Real.pi) • ξ) := by
  rw [ftMeas, charFun_apply]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Real.fourierChar_apply, inner_smul_right]
  congr 1
  push_cast
  ring

lemma ftMeas_inj {μ ν : Measure V} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : ftMeas μ = ftMeas ν) : μ = ν := by
  refine Measure.ext_of_charFun (funext fun t => ?_)
  have e : t = -(2 * Real.pi) • (-(2 * Real.pi)⁻¹ • t) := by
    rw [smul_smul, neg_mul_neg, mul_inv_cancel₀ (by positivity), one_smul]
  rw [e, ← ftMeas_eq_charFun, ← ftMeas_eq_charFun, h]

lemma ftMeas_density {f : V → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hfi : Integrable f) :
    ftMeas (volume.withDensity fun x => ENNReal.ofReal (f x)) = 𝓕 (fun x => (f x : ℂ)) := by
  funext ξ
  rw [ftMeas]
  erw [integral_withDensity_eq_integral_toReal_smul₀ hfi.aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [Real.fourier_eq]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  erw [ENNReal.toReal_ofReal (hf0 x)]
  rw [Circle.smul_def, smul_eq_mul, Complex.real_smul, mul_comm]

section MMD

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {φ : V → H} {k₀ : V → ℝ} (hφ : ∀ x y, ⟪φ x, φ y⟫ = k₀ (x - y)) (hc : Continuous k₀) (hi : Integrable k₀)
include hφ hc

lemma phi_continuous : Continuous φ := ((gram_cont_iff hφ).1).2 hc.continuousAt

lemma phi_integrable (μ : Measure V) [IsFiniteMeasure μ] : Integrable φ μ := by
  refine Integrable.mono' (integrable_const (√(k₀ 0))) (phi_continuous hφ hc).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [← Real.sqrt_sq (norm_nonneg (φ x)), gram_norm_sq hφ]

lemma inner_integral_phi (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ⟪∫ x, φ x ∂μ, ∫ y, φ y ∂ν⟫ = ∫ x, ∫ y, k₀ (x - y) ∂ν ∂μ := by
  rw [real_inner_comm, ← integral_inner (phi_integrable hφ hc μ)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [real_inner_comm, ← integral_inner (phi_integrable hφ hc ν)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  exact hφ x y

include hi

lemma inner_y_closed (ν : Measure V) [IsFiniteMeasure ν] (x : V) :
    ∫ y, k₀ (x - y) ∂ν = ∫ ξ, specDens k₀ ξ * (ftMeas ν ξ * conj (𝐞 (-⟪x, ξ⟫) : ℂ)).re := by
  have hpd := gram_posdef hφ
  have hsi : Integrable (specDens k₀) := (feature_exists_facts hc hi hpd).2.2.2.1
  simp_rw [cos_inversion hc hi hpd]
  have hint : Integrable (Function.uncurry fun (y ξ : V) => specDens k₀ ξ * Real.cos (2 * Real.pi * ⟪x - y, ξ⟫))
      (ν.prod volume) := by
    have hp : Integrable (fun p : V × V => (1 : ℝ) * specDens k₀ p.2) (ν.prod volume) :=
      (integrable_const (1 : ℝ)).mul_prod hsi
    refine hp.mono ?_ (Eventually.of_forall fun p => ?_)
    · have hsc := (feature_exists_facts hc hi hpd).1
      refine Continuous.aestronglyMeasurable ?_
      show Continuous fun p : V × V => specDens k₀ p.2 * Real.cos (2 * Real.pi * ⟪x - p.1, p.2⟫)
      exact (hsc.comp continuous_snd).mul (Real.continuous_cos.comp (continuous_const.mul
        ((continuous_const.sub continuous_fst).inner continuous_snd)))
    · simp only [Function.uncurry, norm_mul, one_mul, Real.norm_eq_abs]
      calc |specDens k₀ p.2| * |Real.cos (2 * Real.pi * ⟪x - p.1, p.2⟫)| ≤ |specDens k₀ p.2| * 1 := by
            gcongr; exact Real.abs_cos_le_one _
        _ = |specDens k₀ p.2| := mul_one _
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  rw [integral_const_mul]
  congr 1
  have hc2 : Integrable (fun y => (𝐞 (-⟪y, ξ⟫) : ℂ) * conj (𝐞 (-⟪x, ξ⟫) : ℂ)) ν :=
    (integrable_const (1 : ℂ)).mono ((char_continuous ξ).mul continuous_const).aestronglyMeasurable
      (Eventually.of_forall fun y => by simp [Circle.norm_coe])
  have ere := (integral_re hc2).symm
  simp only [RCLike.re_to_complex] at ere
  rw [ftMeas, ← integral_mul_const, ere]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  erw [e_mul_conj, fourierChar_re]
  congr 1
  rw [inner_sub_left]; ring

lemma double_spec (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∫ x, ∫ y, k₀ (x - y) ∂ν ∂μ = ∫ ξ, specDens k₀ ξ * (ftMeas μ ξ * conj (ftMeas ν ξ)).re := by
  have hpd := gram_posdef hφ
  have hfe := feature_exists_facts hc hi hpd
  have hsi : Integrable (specDens k₀) := hfe.2.2.2.1
  simp_rw [inner_y_closed hφ hc hi ν]
  have hint : Integrable (Function.uncurry fun (x ξ : V) =>
      specDens k₀ ξ * (ftMeas ν ξ * conj (𝐞 (-⟪x, ξ⟫) : ℂ)).re) (μ.prod volume) := by
    have hp : Integrable (fun p : V × V => (ν.real univ) * specDens k₀ p.2) (μ.prod volume) :=
      (integrable_const _).mul_prod hsi
    refine hp.mono ?_ (Eventually.of_forall fun p => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      show Continuous fun p : V × V => specDens k₀ p.2 * (ftMeas ν p.2 * conj (𝐞 (-⟪p.1, p.2⟫) : ℂ)).re
      refine (hfe.1.comp continuous_snd).mul (Complex.continuous_re.comp
        (((ftMeas_continuous ν).comp continuous_snd).mul (Complex.continuous_conj.comp ?_)))
      exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp (continuous_fst.inner continuous_snd).neg)
    · have hb : |(ftMeas ν p.2 * conj (𝐞 (-⟪p.1, p.2⟫) : ℂ)).re| ≤ ν.real univ :=
        calc |(ftMeas ν p.2 * conj (𝐞 (-⟪p.1, p.2⟫) : ℂ)).re| ≤ ‖ftMeas ν p.2 * conj (𝐞 (-⟪p.1, p.2⟫) : ℂ)‖ :=
              Complex.abs_re_le_norm _
          _ = ‖ftMeas ν p.2‖ := by rw [norm_mul, Complex.norm_conj, Circle.norm_coe, mul_one]
          _ ≤ ν.real univ := ftMeas_norm_le ν p.2
      show ‖specDens k₀ p.2 * (ftMeas ν p.2 * conj (𝐞 (-⟪p.1, p.2⟫) : ℂ)).re‖ ≤ ‖ν.real univ * specDens k₀ p.2‖
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hfe.2.2.1 p.2),
        abs_of_nonneg measureReal_nonneg, mul_comm (ν.real univ)]
      exact mul_le_mul_of_nonneg_left hb (hfe.2.2.1 p.2)
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  rw [integral_const_mul]
  congr 1
  have hc2 : Integrable (fun x => ftMeas ν ξ * conj (𝐞 (-⟪x, ξ⟫) : ℂ)) μ :=
    (integrable_const (ftMeas ν ξ)).mono (continuous_const.mul (Complex.continuous_conj.comp
      (char_continuous ξ))).aestronglyMeasurable (Eventually.of_forall fun x => by simp [Circle.norm_coe])
  have ere := (integral_re hc2).symm
  simp only [RCLike.re_to_complex] at ere
  rw [← ere, integral_const_mul, integral_conj]
  show (ftMeas ν ξ * conj (ftMeas μ ξ)).re = (ftMeas μ ξ * conj (ftMeas ν ξ)).re
  simp [Complex.mul_re]
  ring

omit hφ hc hi in
lemma integrable_spec_mul {s g : V → ℝ} (hsi : Integrable s) (hs0 : ∀ ξ, 0 ≤ s ξ) (hg : Continuous g) {C : ℝ}
    (hC : ∀ ξ, |g ξ| ≤ C) : Integrable (fun ξ => s ξ * g ξ) := by
  refine (hsi.const_mul C).mono (hsi.aestronglyMeasurable.mul hg.aestronglyMeasurable)
    (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hs0 ξ)]
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC ξ)
  rw [abs_of_nonneg hC0, mul_comm C]
  exact mul_le_mul_of_nonneg_left (hC ξ) (hs0 ξ)

omit hφ hc hi in
lemma norm_sub_sq_complex (a b : ℂ) :
    ‖a - b‖ ^ 2 = (a * conj a).re - 2 * (a * conj b).re + (b * conj b).re := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re]
  ring

/-- Wave31tp L16 (eq:newbochner), all conclusions. -/
theorem mmd_fourier_facts :
    Continuous φ ∧ StronglyMeasurable φ ∧ (∀ x, ‖φ x‖ = √(k₀ 0)) ∧
    ∀ (μ₁ μ₂ : Measure V) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂],
      Integrable (fun ξ => specDens k₀ ξ * ‖ftMeas μ₁ ξ - ftMeas μ₂ ξ‖ ^ 2) ∧
      ‖∫ x, φ x ∂μ₁ - ∫ x, φ x ∂μ₂‖ ^ 2 = ∫ ξ, specDens k₀ ξ * ‖ftMeas μ₁ ξ - ftMeas μ₂ ξ‖ ^ 2 ∧
      ‖∫ x, φ x ∂μ₁ - ∫ x, φ x ∂μ₂‖ ^ 2 =
        (∫ x, ∫ y, k₀ (x - y) ∂μ₁ ∂μ₁) - 2 * (∫ x, ∫ y, k₀ (x - y) ∂μ₂ ∂μ₁) + ∫ x, ∫ y, k₀ (x - y) ∂μ₂ ∂μ₂ := by
  have hφc := phi_continuous hφ hc
  have hpd := gram_posdef hφ
  have hfe := feature_exists_facts hc hi hpd
  refine ⟨hφc, hφc.stronglyMeasurable, fun x => by rw [← gram_norm_sq hφ x, Real.sqrt_sq (norm_nonneg _)], ?_⟩
  intro μ₁ μ₂ _ _
  set F₁ := ftMeas μ₁
  set F₂ := ftMeas μ₂
  have hF₁ := ftMeas_continuous μ₁
  have hF₂ := ftMeas_continuous μ₂
  have hb : ∀ (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν] ξ,
      |(ftMeas μ ξ * conj (ftMeas ν ξ)).re| ≤ μ.real univ * ν.real univ := by
    intro μ ν _ _ ξ
    calc |(ftMeas μ ξ * conj (ftMeas ν ξ)).re| ≤ ‖ftMeas μ ξ * conj (ftMeas ν ξ)‖ := Complex.abs_re_le_norm _
      _ = ‖ftMeas μ ξ‖ * ‖ftMeas ν ξ‖ := by rw [norm_mul, Complex.norm_conj]
      _ ≤ μ.real univ * ν.real univ := mul_le_mul (ftMeas_norm_le μ ξ) (ftMeas_norm_le ν ξ) (norm_nonneg _)
          measureReal_nonneg
  have hI : ∀ (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      Integrable (fun ξ => specDens k₀ ξ * (ftMeas μ ξ * conj (ftMeas ν ξ)).re) := by
    intro μ ν _ _
    exact integrable_spec_mul hfe.2.2.2.1 hfe.2.2.1 (Complex.continuous_re.comp ((ftMeas_continuous μ).mul
      (Complex.continuous_conj.comp (ftMeas_continuous ν)))) (hb μ ν)
  have hpt : ∀ ξ, specDens k₀ ξ * ‖F₁ ξ - F₂ ξ‖ ^ 2 =
      specDens k₀ ξ * (F₁ ξ * conj (F₁ ξ)).re - 2 * (specDens k₀ ξ * (F₁ ξ * conj (F₂ ξ)).re) +
        specDens k₀ ξ * (F₂ ξ * conj (F₂ ξ)).re := fun ξ => by
    rw [norm_sub_sq_complex]; ring
  have hint : Integrable (fun ξ => specDens k₀ ξ * ‖F₁ ξ - F₂ ξ‖ ^ 2) := by
    simp_rw [hpt]
    exact ((hI μ₁ μ₁).sub ((hI μ₁ μ₂).const_mul 2)).add (hI μ₂ μ₂)
  have hiii : ‖∫ x, φ x ∂μ₁ - ∫ x, φ x ∂μ₂‖ ^ 2 =
      (∫ x, ∫ y, k₀ (x - y) ∂μ₁ ∂μ₁) - 2 * (∫ x, ∫ y, k₀ (x - y) ∂μ₂ ∂μ₁) + ∫ x, ∫ y, k₀ (x - y) ∂μ₂ ∂μ₂ := by
    rw [@norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      inner_integral_phi hφ hc μ₁ μ₁, inner_integral_phi hφ hc μ₁ μ₂, inner_integral_phi hφ hc μ₂ μ₂]
  refine ⟨hint, ?_, hiii⟩
  rw [hiii, double_spec hφ hc hi μ₁ μ₁, double_spec hφ hc hi μ₁ μ₂, double_spec hφ hc hi μ₂ μ₂]
  simp_rw [hpt]
  have h12 : Integrable (fun a => specDens k₀ a * (ftMeas μ₁ a * conj (ftMeas μ₁ a)).re -
      2 * (specDens k₀ a * (ftMeas μ₁ a * conj (ftMeas μ₂ a)).re)) :=
    (hI μ₁ μ₁).sub ((hI μ₁ μ₂).const_mul 2)
  rw [← integral_const_mul, ← integral_sub (hI μ₁ μ₁) ((hI μ₁ μ₂).const_mul 2), ← integral_add h12 (hI μ₂ μ₂)]

end MMD

end StatFormal.TIKernel
