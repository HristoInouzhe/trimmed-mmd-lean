import StatFormal.Archive.Wave4b.Statements

/-!
# Route — Schrödinger-bridge repair `cor:smoothing`

Generic step: on a group with a left-invariant `s`-finite measure `vol`, for a finite measure `ρ`
and a bounded continuous density `φ ≥ 0`, `ρ ∗ (vol.withDensity φ) = vol.withDensity ψ` with
`ψ(y) = ∫ φ(y − a) dρ(a)` (Tonelli plus translation invariance). `ψ` is continuous (dominated
convergence), positive when `φ > 0` and `ρ ≠ 0`, and bounded by `sup φ` when `ρ` is a probability.
For the Gaussian, `sup φ = (2πv)^{-d/2}`. In dimension one the CDF of a measure with an everywhere
positive density is continuous (no atoms), strictly increasing, and has range `(0,1)` (limits plus the
intermediate value theorem).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatFormal.Wave4b

section Generic

variable {G : Type*} [NormedAddCommGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] (vol : Measure G) [vol.IsAddLeftInvariant] [SFinite vol]

lemma integrable_shift (ρ : Measure G) [IsFiniteMeasure ρ] {φ : G → ℝ} (hφc : Continuous φ)
    (hφ0 : ∀ z, 0 ≤ φ z) {M : ℝ} (hφM : ∀ z, φ z ≤ M) (y : G) :
    Integrable (fun a => φ (y - a)) ρ := by
  refine Integrable.of_bound (hφc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable M
    (ae_of_all _ fun a => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 _)]
  exact hφM _

lemma conv_withDensity (ρ : Measure G) [IsFiniteMeasure ρ] {φ : G → ℝ} (hφc : Continuous φ)
    (hφ0 : ∀ z, 0 ≤ φ z) {M : ℝ} (hφM : ∀ z, φ z ≤ M) :
    ρ ∗ vol.withDensity (fun z => ENNReal.ofReal (φ z)) =
      vol.withDensity (fun y => ENNReal.ofReal (∫ a, φ (y - a) ∂ρ)) := by
  have hφm : Measurable fun z => ENNReal.ofReal (φ z) := hφc.measurable.ennreal_ofReal
  ext A hA
  have hI : Measurable (A.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hA
  rw [← lintegral_indicator_one hA, Measure.lintegral_conv hI]
  have step : ∀ a, ∫⁻ z, A.indicator 1 (a + z) ∂(vol.withDensity fun z => ENNReal.ofReal (φ z))
      = ∫⁻ y, ENNReal.ofReal (φ (y - a)) * A.indicator 1 y ∂vol := by
    intro a
    have hg : Measurable fun z => A.indicator (1 : G → ℝ≥0∞) (a + z) :=
      hI.comp (measurable_const_add a)
    rw [lintegral_withDensity_eq_lintegral_mul _ hφm hg]
    rw [← lintegral_add_left_eq_self
      (fun y => ENNReal.ofReal (φ (y - a)) * A.indicator 1 y) a]
    simp
  simp_rw [step]
  have hjoint : AEMeasurable (Function.uncurry fun a y =>
      ENNReal.ofReal (φ (y - a)) * A.indicator (1 : G → ℝ≥0∞) y) (ρ.prod vol) := by
    refine Measurable.aemeasurable (Measurable.mul ?_ ?_)
    · exact (hφc.measurable.comp (measurable_snd.sub measurable_fst)).ennreal_ofReal
    · exact hI.comp measurable_snd
  rw [lintegral_lintegral_swap hjoint, withDensity_apply _ hA, ← lintegral_indicator hA]
  refine lintegral_congr fun y => ?_
  by_cases hy : y ∈ A
  · simp only [hy, Set.indicator_of_mem, Pi.one_apply, mul_one]
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_shift ρ hφc hφ0 hφM y)
      (ae_of_all _ fun a => hφ0 _)]
  · simp [hy]

lemma continuous_shift (ρ : Measure G) [IsFiniteMeasure ρ] {φ : G → ℝ} (hφc : Continuous φ)
    (hφ0 : ∀ z, 0 ≤ φ z) {M : ℝ} (hφM : ∀ z, φ z ≤ M) :
    Continuous fun y => ∫ a, φ (y - a) ∂ρ := by
  refine continuous_of_dominated (bound := fun _ => M)
    (fun y => (hφc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (fun y => ae_of_all _ fun a => ?_) (integrable_const M)
    (ae_of_all _ fun a => hφc.comp (continuous_id.sub continuous_const))
  rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 _)]
  exact hφM _

lemma shift_bounds (ρ : Measure G) [IsProbabilityMeasure ρ] {φ : G → ℝ} (hφc : Continuous φ)
    (hφ0 : ∀ z, 0 < φ z) {M : ℝ} (hφM : ∀ z, φ z ≤ M) (y : G) :
    0 < ∫ a, φ (y - a) ∂ρ ∧ ∫ a, φ (y - a) ∂ρ ≤ M := by
  have hint := integrable_shift ρ hφc (fun z => (hφ0 z).le) hφM y
  constructor
  · rw [integral_pos_iff_support_of_nonneg (fun a => (hφ0 _).le) hint]
    have : Function.support (fun a => φ (y - a)) = univ :=
      eq_univ_of_forall fun a => (hφ0 _).ne'
    rw [this, measure_univ]
    exact one_pos
  · calc ∫ a, φ (y - a) ∂ρ ≤ ∫ _, M ∂ρ := integral_mono hint (integrable_const M) fun a => hφM _
      _ = M := by simp

/-- The generic smoothing statement. -/
lemma smoothing_generic (ρ : Measure G) [IsProbabilityMeasure ρ] {φ : G → ℝ} (hφc : Continuous φ)
    (hφ0 : ∀ z, 0 < φ z) {M : ℝ} (hφM : ∀ z, φ z ≤ M) :
    ∃ ψ : G → ℝ, Continuous ψ ∧
      ρ ∗ vol.withDensity (fun z => ENNReal.ofReal (φ z)) =
        vol.withDensity (fun y => ENNReal.ofReal (ψ y)) ∧ ∀ y, 0 < ψ y ∧ ψ y ≤ M :=
  ⟨fun y => ∫ a, φ (y - a) ∂ρ, continuous_shift ρ hφc (fun z => (hφ0 z).le) hφM,
    conv_withDensity vol ρ hφc (fun z => (hφ0 z).le) hφM, shift_bounds ρ hφc hφ0 hφM⟩

end Generic

lemma gaussDensity_pos {d : ℕ} {v : ℝ} (hv : 0 < v) (z : EuclideanSpace ℝ (Fin d)) :
    0 < gaussDensity d v z := by
  unfold gaussDensity
  have : 0 < 2 * Real.pi * v := by positivity
  positivity

lemma gaussDensity_le {d : ℕ} {v : ℝ} (hv : 0 < v) (z : EuclideanSpace ℝ (Fin d)) :
    gaussDensity d v z ≤ (2 * Real.pi * v) ^ (-(d : ℝ) / 2) := by
  unfold gaussDensity
  have h1 : 0 < (2 * Real.pi * v) ^ (-(d : ℝ) / 2) := by
    have : 0 < 2 * Real.pi * v := by positivity
    positivity
  have h2 : Real.exp (-(‖z‖ ^ 2) / (2 * v)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [norm_nonneg z]) (by positivity)
  calc _ ≤ (2 * Real.pi * v) ^ (-(d : ℝ) / 2) * 1 := mul_le_mul_of_nonneg_left h2 h1.le
    _ = _ := mul_one _

lemma continuous_gaussDensity (d : ℕ) (v : ℝ) : Continuous (gaussDensity d v) := by
  unfold gaussDensity
  fun_prop

lemma var_pos {ε t : ℝ} (hε : 0 < ε) (ht0 : 0 < t) (ht1 : t < 1) : 0 < ε * t * (1 - t) := by
  have : 0 < 1 - t := by linarith
  positivity

theorem smoothing_density : Claims.smoothing_density := by
  intro d ε t plan _ hε ht0 ht1
  have hv := var_pos hε ht0 ht1
  have hm : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      (1 - t) • p.1 + t • p.2 := by fun_prop
  exact smoothing_generic volume (plan.map fun p => (1 - t) • p.1 + t • p.2)
    (continuous_gaussDensity d _) (gaussDensity_pos hv) (gaussDensity_le hv)

lemma gaussianPDFReal_le' {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    gaussianPDFReal 0 v x ≤ (2 * Real.pi * v) ^ (-(1 : ℝ) / 2) := by
  have hpos : 0 < 2 * Real.pi * (v : ℝ) := by
    have : (0 : ℝ) < v := lt_of_le_of_ne v.2 (by exact_mod_cast hv.symm)
    positivity
  have h2 : Real.exp (-(x - 0) ^ 2 / (2 * v)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity)
  rw [gaussianPDFReal, show (-(1 : ℝ) / 2) = -(1 / 2) by ring, Real.rpow_neg hpos.le,
    ← Real.sqrt_eq_rpow]
  calc _ ≤ (√(2 * Real.pi * v))⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 (Real.sqrt_nonneg _))
    _ = _ := mul_one _

lemma continuous_gaussianPDFReal' (v : ℝ≥0) : Continuous (gaussianPDFReal 0 v) := by
  unfold gaussianPDFReal
  fun_prop

theorem smoothing_density_one : Claims.smoothing_density_one := by
  intro ε t plan _ hε ht0 ht1
  have hv := var_pos hε ht0 ht1
  have hv' : (ε * t * (1 - t)).toNNReal ≠ 0 := by
    simpa [Real.toNNReal_eq_zero, not_le] using hv
  have hcoe : (((ε * t * (1 - t)).toNNReal : ℝ≥0) : ℝ) = ε * t * (1 - t) :=
    Real.coe_toNNReal _ hv.le
  have hm : Measurable fun p : ℝ × ℝ => (1 - t) * p.1 + t * p.2 := by fun_prop
  unfold endpointMixture1
  rw [gaussianReal_of_var_ne_zero 0 hv']
  have hle := gaussianPDFReal_le' hv'
  rw [hcoe] at hle
  exact smoothing_generic volume (plan.map fun p => (1 - t) * p.1 + t * p.2)
    (continuous_gaussianPDFReal' _) (fun x => gaussianPDFReal_pos _ _ _ hv') hle

lemma withDensity_pos_ne_zero {ρ : ℝ → ℝ} (hρc : Continuous ρ) (hρ : ∀ y, 0 < ρ y) {s : Set ℝ}
    (hs : volume s ≠ 0) : volume.withDensity (fun y => ENNReal.ofReal (ρ y)) s ≠ 0 := by
  rw [Ne, withDensity_apply_eq_zero' hρc.measurable.ennreal_ofReal.aemeasurable]
  have : {x | ENNReal.ofReal (ρ x) ≠ 0} = univ :=
    eq_univ_of_forall fun x => by simpa using hρ x
  rwa [this, univ_inter]

theorem smoothing_cdf : Claims.smoothing_cdf := by
  intro ε t plan _ hε ht0 ht1
  obtain ⟨ρ, hρc, hμ, hρ⟩ := smoothing_density_one ε t plan hε ht0 ht1
  set μ := endpointMixture1 ε t plan with hμdef
  have hm : Measurable fun p : ℝ × ℝ => (1 - t) * p.1 + t * p.2 := by fun_prop
  haveI : IsProbabilityMeasure μ := by
    rw [hμdef, endpointMixture1, Measure.conv]
    infer_instance
  have hpos : ∀ s, volume s ≠ 0 → μ s ≠ 0 := fun s hs => by
    rw [hμ]; exact withDensity_pos_ne_zero hρc (fun y => (hρ y).1) hs
  have hmono : StrictMono (cdf μ) := by
    intro x y hxy
    have h := hpos (Ioc x y) (by simp [Real.volume_Ioc, hxy])
    rw [← measure_cdf (μ := μ), StieltjesFunction.measure_Ioc, Ne, ENNReal.ofReal_eq_zero,
      not_le] at h
    linarith
  have hcont : Continuous (cdf μ) := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    have h0 : μ {x} = 0 := by
      rw [hμ]; exact withDensity_absolutelyContinuous _ _ (Real.volume_singleton)
    rw [← measure_cdf (μ := μ), StieltjesFunction.measure_singleton,
      ENNReal.ofReal_eq_zero] at h0
    have hl : Function.leftLim (cdf μ) x = cdf μ x :=
      le_antisymm ((cdf μ).mono.leftLim_le le_rfl) (by linarith)
    rw [(cdf μ).mono.continuousAt_iff_leftLim_eq_rightLim, hl, StieltjesFunction.rightLim_eq]
  refine ⟨hmono, hcont, ?_⟩
  ext u
  constructor
  · rintro ⟨x, rfl⟩
    constructor
    · rw [cdf_eq_real]
      exact ENNReal.toReal_pos (hpos _ (by simp [Real.volume_Iic])) (measure_ne_top _ _)
    · have h := hpos (Ioi x) (by simp [Real.volume_Ioi])
      have hr : 0 < μ.real (Iic x)ᶜ := by
        rw [compl_Iic]; exact ENNReal.toReal_pos h (measure_ne_top _ _)
      rw [probReal_compl_eq_one_sub measurableSet_Iic] at hr
      rw [cdf_eq_real]
      linarith
  · rintro ⟨hu0, hu1⟩
    obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot (μ := μ)).eventually (gt_mem_nhds hu0)).exists
    obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop (μ := μ)).eventually (lt_mem_nhds hu1)).exists
    exact intermediate_value_univ a b hcont ⟨ha.le, hb.le⟩

end StatFormal.Wave4b
