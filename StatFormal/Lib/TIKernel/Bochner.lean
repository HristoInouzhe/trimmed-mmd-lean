import StatFormal.Lib.TIKernel.Window
import Mathlib.Analysis.Fourier.Inversion

/-!
# Bochner's theorem, the integrable case (library, untrusted)

For `k₀ : V → ℂ` continuous, integrable and positive definite (`Wave31tp.IsPosDefFun`, the Bochner–Rudin notion): `𝓕 k₀` is real
and nonnegative (ball windows and integral positive definiteness), integrable with `∫ 𝓕 k₀ = k₀ 0` (Gaussian regularization and
monotone convergence), and `𝓕⁻ (𝓕 k₀) = k₀` (Mathlib's inversion theorem). Rudin, *Fourier Analysis on Groups*, §§1.4–1.5.
-/

noncomputable section
open MeasureTheory Filter Topology Metric Set FourierTransform Complex
open scoped ENNReal ComplexConjugate InnerProductSpace

set_option linter.unusedSectionVars false

namespace StatFormal.TIKernel

open StatFormal.Wave31tp

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

lemma e_mul_conj (a b : ℝ) : (𝐞 a : ℂ) * conj (𝐞 b : ℂ) = (𝐞 (a - b) : ℂ) := by
  simp only [Real.fourierChar_apply, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Modulation preserves positive definiteness. -/
lemma posdef_modulate {k : V → ℂ} (hk : IsPosDefFun k) (ξ : V) :
    IsPosDefFun (fun z => (𝐞 (-⟪z, ξ⟫_ℝ) : ℂ) * k z) := by
  intro n x c
  have h := hk n x (fun i => c i * (𝐞 (-⟪x i, ξ⟫_ℝ) : ℂ))
  have e : ∀ i j, c i * (𝐞 (-⟪x i, ξ⟫_ℝ) : ℂ) * conj (c j * (𝐞 (-⟪x j, ξ⟫_ℝ) : ℂ)) * k (x i - x j) =
      c i * conj (c j) * ((𝐞 (-⟪x i - x j, ξ⟫_ℝ) : ℂ) * k (x i - x j)) := by
    intro i j
    have h2 := e_mul_conj (-⟪x i, ξ⟫_ℝ) (-⟪x j, ξ⟫_ℝ)
    rw [show -⟪x i - x j, ξ⟫_ℝ = -⟪x i, ξ⟫_ℝ - -⟪x j, ξ⟫_ℝ by rw [inner_sub_left]; ring, ← h2, map_mul]
    ring
  simp_rw [e] at h
  exact h

lemma measurable_window (R : ℝ) : Measurable (window (V := V) R) := by
  have hS : MeasurableSet {p : V × V | p.2 ∈ ball (0 : V) R ∧ p.2 - p.1 ∈ ball (0 : V) R} :=
    (measurableSet_ball.preimage measurable_snd).inter
      (measurableSet_ball.preimage (measurable_snd.sub measurable_fst))
  have h := measurable_measure_prodMk_left (ν := (volume : Measure V)) hS
  have e : (fun z : V => volume (Prod.mk z ⁻¹' {p : V × V | p.2 ∈ ball (0 : V) R ∧ p.2 - p.1 ∈ ball (0 : V) R})) =
      fun z => volume (ball (0 : V) R ∩ (fun x => x - z) ⁻¹' ball (0 : V) R) := by
    funext z; rfl
  rw [e] at h
  exact (h.ennreal_toReal).div_const _

lemma continuous_modulate {k : V → ℂ} (hc : Continuous k) (ξ : V) :
    Continuous fun z => (𝐞 (-⟪z, ξ⟫_ℝ) : ℂ) * k z := by
  refine Continuous.mul ?_ hc
  exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp (continuous_id.inner continuous_const).neg)

lemma norm_modulate (k : V → ℂ) (ξ z : V) : ‖(𝐞 (-⟪z, ξ⟫_ℝ) : ℂ) * k z‖ = ‖k z‖ := by
  rw [norm_mul, Circle.norm_coe, one_mul]

/-- **Bochner, integrable case, step 1**: `𝓕 k₀` is real and nonnegative. -/
theorem fourier_posdef_nonneg {k : V → ℂ} (hc : Continuous k) (hi : Integrable k) (hk : IsPosDefFun k) (ξ : V) :
    (𝓕 k ξ).im = 0 ∧ 0 ≤ (𝓕 k ξ).re := by
  set h : V → ℂ := fun z => (𝐞 (-⟪z, ξ⟫_ℝ) : ℂ) * k z
  have hh : IsPosDefFun h := posdef_modulate hk ξ
  have hhc : Continuous h := continuous_modulate hc ξ
  have hhi : Integrable h :=
    hi.mono hhc.aestronglyMeasurable (Eventually.of_forall fun z => by rw [norm_modulate])
  have hC : ∀ z, ‖h z‖ ≤ (k 0).re := fun z => by rw [norm_modulate]; exact posdef_norm_le k hk z
  have hF : 𝓕 k ξ = ∫ z, h z := by
    rw [Real.fourier_eq]
    rfl
  set T : ℕ → ℂ := fun n => ∫ z, h z * (window (n : ℝ) z : ℂ)
  have hT : ∀ n : ℕ, 0 < n → (T n).im = 0 ∧ 0 ≤ (T n).re := by
    intro n hn
    have hR : (0 : ℝ) < n := by exact_mod_cast hn
    haveI := unifBall_prob (V := V) hR
    have hD := integral_posdef hh hhc hC (unifBall (V := V) (n : ℝ))
    simp only [T]
    rw [integral_window_eq hhc hhi hC hR]
    set D := ∫ p, h (p.1 - p.2) ∂((unifBall (V := V) (n : ℝ)).prod (unifBall (n : ℝ)))
    have hv := (vol_ball_pos (V := V) hR).le
    constructor
    · simp [Complex.mul_im, hD.1]
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_nonneg hv hD.2
  have hlim : Tendsto T atTop (𝓝 (∫ z, h z)) := by
    have := tendsto_integral_of_dominated_convergence (fun z => ‖h z‖)
      (F := fun (n : ℕ) z => h z * (window (n : ℝ) z : ℂ)) (f := fun z => h z * ((1 : ℝ) : ℂ))
      (fun n => (hhc.aestronglyMeasurable.mul
        ((Complex.continuous_ofReal.measurable.comp (measurable_window _)).aestronglyMeasurable)))
      hhi.norm ?_ ?_
    · simpa using this
    · intro n
      refine Eventually.of_forall fun z => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        simp only [Nat.cast_zero, window, ball_zero, Set.empty_inter, measure_empty, ENNReal.toReal_zero,
          zero_div, abs_zero, mul_zero]
        exact norm_nonneg _
      · have hR : (0 : ℝ) < n := by exact_mod_cast hpos
        rw [abs_of_nonneg (window_nonneg _ _)]
        calc ‖h z‖ * window n z ≤ ‖h z‖ * 1 := by gcongr; exact window_le_one hR z
          _ = ‖h z‖ := mul_one _
    · refine Eventually.of_forall fun z => ?_
      exact tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto 1).comp (tendsto_window z))
  rw [hF]
  constructor
  · have h1 : Tendsto (fun n => (T n).im) atTop (𝓝 (∫ z, h z).im) := (Complex.continuous_im.tendsto _).comp hlim
    have h2 : Tendsto (fun n => (T n).im) atTop (𝓝 0) :=
      tendsto_const_nhds.congr' (by filter_upwards [eventually_gt_atTop 0] with n hn; exact (hT n hn).1.symm)
    exact tendsto_nhds_unique h1 h2
  · have h1 : Tendsto (fun n => (T n).re) atTop (𝓝 (∫ z, h z).re) := (Complex.continuous_re.tendsto _).comp hlim
    exact ge_of_tendsto h1 (by filter_upwards [eventually_gt_atTop 0] with n hn; exact (hT n hn).2)

lemma innerₗ_flip' : (innerₗ V).flip = innerₗ V := by
  ext x y; simp [real_inner_comm]

/-- Gaussian regularization of `∫ 𝓕 k`: the exchange with the Gaussian. -/
lemma gauss_exchange {k : V → ℂ} (hi : Integrable k) {c : ℝ} (hc : 0 < c) :
    ∫ w, cexp (-((c⁻¹ : ℝ) : ℂ) * ‖w‖ ^ 2) • 𝓕 k w =
      ∫ w, (((Real.pi : ℂ) * c) ^ (Module.finrank ℝ V / 2 : ℂ) * cexp (-(Real.pi : ℂ) ^ 2 * c * ‖0 - w‖ ^ 2)) • k w := by
  have hb : 0 < (((c⁻¹ : ℝ) : ℂ)).re := by simpa using inv_pos.mpr hc
  have J : Integrable (fun w : V => cexp (-((c⁻¹ : ℝ) : ℂ) * ‖w‖ ^ 2)) := by
    simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb 0 (0 : V)
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := Real.fourierChar) (μ := volume)
    (ν := volume) (L := innerₗ V) Real.continuous_fourierChar continuous_inner J hi
  rw [innerₗ_flip'] at h
  change ∫ ξ, 𝓕 (fun w : V => cexp (-((c⁻¹ : ℝ) : ℂ) * ‖w‖ ^ 2)) ξ • k ξ =
    ∫ x, cexp (-((c⁻¹ : ℝ) : ℂ) * ‖x‖ ^ 2) • 𝓕 k x at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only
  rw [fourier_gaussian_innerProductSpace hb, zero_sub, norm_neg]
  congr 2
  · congr 1
    push_cast
    field_simp
  · congr 1
    push_cast
    field_simp

/-- **Bochner, integrable case, step 2**: `𝓕 k₀` is integrable and `∫ 𝓕 k₀ = k₀ 0`. -/
theorem fourier_posdef_integrable {k : V → ℂ} (hc : Continuous k) (hi : Integrable k) (hk : IsPosDefFun k) :
    Integrable (𝓕 k) ∧ ∫ ξ, 𝓕 k ξ = k 0 := by
  set f : V → ℝ := fun ξ => (𝓕 k ξ).re
  have hpos := fourier_posdef_nonneg hc hi hk
  have hf0 : ∀ ξ, 0 ≤ f ξ := fun ξ => (hpos ξ).2
  have hfk : ∀ ξ, 𝓕 k ξ = (f ξ : ℂ) := fun ξ => Complex.ext rfl (by simp [f, (hpos ξ).1])
  have hcont : Continuous (𝓕 k) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hi
  have hfc : Continuous f := Complex.continuous_re.comp hcont
  have hfb : ∀ ξ, f ξ ≤ ∫ x, ‖k x‖ := by
    intro ξ
    calc f ξ ≤ ‖𝓕 k ξ‖ := Complex.re_le_norm _
      _ ≤ ∫ x, ‖k x‖ := by
        rw [Real.fourier_eq]
        refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
        congr 1; funext x; rw [Circle.norm_smul]
  -- the regularized integrals
  set g : ℕ → V → ℝ := fun n ξ => Real.exp (-‖ξ‖ ^ 2 / ((n : ℝ) + 1)) * f ξ
  have hgint : ∀ n, Integrable (g n) := by
    intro n
    have hG : Integrable (fun ξ : V => Real.exp (-((((n : ℝ) + 1)⁻¹)) * ‖ξ‖ ^ 2)) := by
      have hb : 0 < ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ).re := by simp only [Complex.ofReal_re]; positivity
      have := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb 0 (0 : V)).norm
      refine this.congr (Eventually.of_forall fun ξ => ?_)
      simp only [zero_mul, add_zero, Complex.norm_exp]
      congr 1
      rw [show (-(((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ)) * (‖ξ‖ : ℂ) ^ 2) = ((-((((n : ℝ) + 1)⁻¹)) * ‖ξ‖ ^ 2 : ℝ) : ℂ) by
        push_cast; ring, Complex.ofReal_re]
    refine (hG.mul_const (∫ x, ‖k x‖)).mono (Measurable.aestronglyMeasurable (by fun_prop)) ?_
    refine Eventually.of_forall fun ξ => ?_
    simp only [g, norm_mul, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le, abs_of_nonneg (hf0 ξ)]
    rw [abs_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
    have : Real.exp (-‖ξ‖ ^ 2 / ((n : ℝ) + 1)) = Real.exp (-((((n : ℝ) + 1)⁻¹)) * ‖ξ‖ ^ 2) := by
      congr 1; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left (hfb ξ) (Real.exp_pos _).le
  have hG_eq : ∀ n : ℕ, ∫ w, cexp (-((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * ‖w‖ ^ 2) • 𝓕 k w = ((∫ ξ, g n ξ : ℝ) : ℂ) := by
    intro n
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [g, smul_eq_mul, hfk w]
    push_cast
    congr 2
    ring
  have hlimC := (Real.tendsto_integral_gaussian_smul' hi (v := (0 : V)) hc.continuousAt).comp
    (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
  have hlimR : Tendsto (fun n : ℕ => ∫ ξ, g n ξ) atTop (𝓝 (k 0).re) := by
    have : Tendsto (fun n : ℕ => (((∫ ξ, g n ξ : ℝ) : ℂ))) atTop (𝓝 (k 0)) := by
      refine hlimC.congr' (Eventually.of_forall fun n => ?_)
      simp only [Function.comp]
      rw [← gauss_exchange hi (by positivity : (0 : ℝ) < (n : ℝ) + 1), hG_eq n]
    refine ((Complex.continuous_re.tendsto _).comp this).congr fun n => ?_
    simp [Function.comp]
  -- monotone convergence
  have hmono : Tendsto (fun n : ℕ => ∫⁻ ξ, ENNReal.ofReal (g n ξ)) atTop (𝓝 (∫⁻ ξ, ENNReal.ofReal (f ξ))) := by
    refine lintegral_tendsto_of_tendsto_of_monotone (fun n => (Measurable.ennreal_ofReal (by fun_prop)).aemeasurable)
      (Eventually.of_forall fun ξ => ?_) (Eventually.of_forall fun ξ => ?_)
    · intro m n hmn
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (hf0 ξ))
      refine Real.exp_le_exp.mpr ?_
      have h1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have h2 : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
      rw [neg_div, neg_div, neg_le_neg_iff]
      exact div_le_div_of_nonneg_left (sq_nonneg _) h1 h2
    · refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
      have : Tendsto (fun n : ℕ => -‖ξ‖ ^ 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
        have := (tendsto_const_div_atTop_nhds_zero_nat (-‖ξ‖ ^ 2)).comp (tendsto_add_atTop_nat 1)
        refine this.congr fun n => ?_
        simp [Function.comp, Nat.cast_add, Nat.cast_one]
      simpa using ((Real.continuous_exp.tendsto 0).comp this).mul_const (f ξ)
  have hlin : ∀ n, ∫⁻ ξ, ENNReal.ofReal (g n ξ) = ENNReal.ofReal (∫ ξ, g n ξ) := fun n =>
    (ofReal_integral_eq_lintegral_ofReal (hgint n) (Eventually.of_forall fun ξ =>
      mul_nonneg (Real.exp_pos _).le (hf0 ξ))).symm
  simp_rw [hlin] at hmono
  have hval : ∫⁻ ξ, ENNReal.ofReal (f ξ) = ENNReal.ofReal (k 0).re :=
    tendsto_nhds_unique hmono ((ENNReal.continuous_ofReal.tendsto _).comp hlimR)
  have hfint : Integrable f := by
    refine ⟨hfc.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hf0), hval]
    exact ENNReal.ofReal_lt_top
  have hfeq : ∫ ξ, f ξ = (k 0).re := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0) hfc.aestronglyMeasurable, hval,
      ENNReal.toReal_ofReal (posdef_zero k hk).2]
  have hK : Integrable (𝓕 k) := (hfint.ofReal (𝕜 := ℂ)).congr (Eventually.of_forall fun ξ => (hfk ξ).symm)
  refine ⟨hK, ?_⟩
  rw [show (fun ξ => 𝓕 k ξ) = fun ξ => (f ξ : ℂ) from funext hfk, integral_complex_ofReal, hfeq]
  exact Complex.ext rfl (by simp [(posdef_zero k hk).1])

/-- **Bochner's theorem, the integrable case** (all conclusions of Wave31tp L13). -/
theorem bochner_integrable {k : V → ℂ} (hc : Continuous k) (hi : Integrable k) (hk : IsPosDefFun k) :
    (∀ z, k (-z) = conj (k z)) ∧ (k 0).im = 0 ∧ (∀ z, ‖k z‖ ≤ (k 0).re) ∧
    (∀ ξ, (𝓕 k ξ).im = 0 ∧ 0 ≤ (𝓕 k ξ).re) ∧ Integrable (𝓕 k) ∧ ∫ ξ, 𝓕 k ξ = k 0 ∧ 𝓕⁻ (𝓕 k) = k := by
  obtain ⟨hint, hval⟩ := fourier_posdef_integrable hc hi hk
  exact ⟨posdef_neg k hk, (posdef_zero k hk).1, posdef_norm_le k hk, fourier_posdef_nonneg hc hi hk, hint, hval,
    Continuous.fourierInv_fourier_eq hc hi hint⟩

end StatFormal.TIKernel
