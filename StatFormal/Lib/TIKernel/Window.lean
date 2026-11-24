import StatFormal.Lib.TIKernel.PosDef
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Group.Integral

/-!
# Ball windows (library, untrusted)

`window R z = vol(B_R ∩ (B_R + z)) / vol(B_R)` takes values in `[0,1]` and tends to `1` as `R → ∞`, and for an integrable
bounded continuous `h`, `∫ h · window_R = vol(B_R) · ∫∫ h(x − y) d(μ_R ⊗ μ_R)` with `μ_R` the uniform law on `B_R`. With
`integral_posdef` this gives the nonnegativity of `𝓕 k₀` for positive definite integrable `k₀` (Bochner, the integrable case).
-/

noncomputable section
open MeasureTheory Filter Topology Metric Set
open scoped ENNReal

set_option linter.unusedSectionVars false

namespace StatFormal.TIKernel

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

/-- The ball window `vol(B_R ∩ (B_R + z)) / vol(B_R)`. -/
def window (R : ℝ) (z : V) : ℝ :=
  (volume (ball (0 : V) R ∩ (fun x => x - z) ⁻¹' ball (0 : V) R)).toReal / (volume (ball (0 : V) R)).toReal

lemma vol_ball_pos {R : ℝ} (hR : 0 < R) : 0 < (volume (ball (0 : V) R)).toReal :=
  ENNReal.toReal_pos (measure_ball_pos volume 0 hR).ne' measure_ball_lt_top.ne

lemma window_nonneg (R : ℝ) (z : V) : 0 ≤ window R z := div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

lemma window_le_one {R : ℝ} (hR : 0 < R) (z : V) : window R z ≤ 1 := by
  rw [window, div_le_one (vol_ball_pos hR)]
  exact ENNReal.toReal_mono measure_ball_lt_top.ne (measure_mono inter_subset_left)

lemma window_ge {R : ℝ} (z : V) (hz : ‖z‖ < R) :
    ((R - ‖z‖) / R) ^ Module.finrank ℝ V ≤ window R z := by
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg z) hz
  have hsub : ball (0 : V) (R - ‖z‖) ⊆ ball (0 : V) R ∩ (fun x => x - z) ⁻¹' ball (0 : V) R := by
    intro x hx
    simp only [mem_ball_zero_iff, mem_inter_iff, mem_preimage] at hx ⊢
    constructor
    · linarith [norm_nonneg z]
    · calc ‖x - z‖ ≤ ‖x‖ + ‖z‖ := norm_sub_le _ _
        _ < R := by linarith
  have hfin : volume (ball (0 : V) R ∩ (fun x => x - z) ⁻¹' ball (0 : V) R) ≠ ⊤ :=
    ((measure_mono inter_subset_left).trans_lt measure_ball_lt_top).ne
  have h1 : (volume (ball (0 : V) (R - ‖z‖))).toReal ≤
      (volume (ball (0 : V) R ∩ (fun x => x - z) ⁻¹' ball (0 : V) R)).toReal :=
    ENNReal.toReal_mono hfin (measure_mono hsub)
  rw [window, le_div_iff₀ (vol_ball_pos hR)]
  refine le_trans ?_ h1
  rw [Measure.addHaar_ball_of_pos volume 0 (by linarith : 0 < R - ‖z‖),
    Measure.addHaar_ball_of_pos volume 0 hR, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity), div_pow]
  have hRd : (0 : ℝ) < R ^ Module.finrank ℝ V := by positivity
  field_simp
  rfl

lemma tendsto_window (z : V) : Tendsto (fun n : ℕ => window (n : ℝ) z) atTop (𝓝 1) := by
  set d := Module.finrank ℝ V
  have hlow : Tendsto (fun n : ℕ => (1 - ‖z‖ / (n : ℝ)) ^ d) atTop (𝓝 1) := by
    have : Tendsto (fun n : ℕ => ‖z‖ / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat ‖z‖
    have h2 := ((tendsto_const_nhds (x := (1 : ℝ))).sub this).pow d
    simpa using h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop (⌈‖z‖⌉₊ + 1)] with n hn
    have hzn : ‖z‖ < (n : ℝ) := by
      have := Nat.le_ceil ‖z‖
      have : (⌈‖z‖⌉₊ : ℝ) + 1 < n := by exact_mod_cast hn
      linarith
    have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (norm_nonneg z) hzn
    have := window_ge z hzn
    rwa [sub_div, div_self hnpos.ne'] at this
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact window_le_one (by exact_mod_cast hn) z

/-- The uniform law on the ball `B_R`. -/
def unifBall (R : ℝ) : Measure V := (volume (ball (0 : V) R))⁻¹ • volume.restrict (ball (0 : V) R)

lemma unifBall_prob {R : ℝ} (hR : 0 < R) : IsProbabilityMeasure (unifBall (V := V) R) := by
  constructor
  rw [unifBall, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter, smul_eq_mul,
    ENNReal.inv_mul_cancel (measure_ball_pos volume 0 hR).ne' measure_ball_lt_top.ne]

lemma ind_mul_ind (B : Set V) (z x : V) :
    B.indicator (fun _ => (1 : ℝ)) x * B.indicator (fun _ => (1 : ℝ)) (x - z) =
      (B ∩ (fun x => x - z) ⁻¹' B).indicator (fun _ => (1 : ℝ)) x := by
  by_cases h1 : x ∈ B <;> by_cases h2 : x - z ∈ B <;> simp [h1, h2, indicator]

/-- The double integral of `h(x − y)` over `B × B` as a single integral against the overlap volume. -/
theorem integral_ball_ball {h : V → ℂ} (hc : Continuous h) (hint : Integrable h) {R : ℝ} :
    ∫ x in ball (0 : V) R, ∫ y in ball (0 : V) R, h (x - y) =
      ∫ z, ((volume.real (ball (0 : V) R ∩ (fun x => x - z) ⁻¹' ball (0 : V) R) : ℝ) : ℂ) * h z := by
  set B := ball (0 : V) R
  have hBm : MeasurableSet B := measurableSet_ball
  set I : V → ℝ := B.indicator (fun _ => (1 : ℝ))
  have hIm : Measurable I := measurable_const.indicator hBm
  have hIint : Integrable I := (integrableOn_const measure_ball_lt_top.ne).integrable_indicator hBm
  have hinner : ∀ x, ∫ y in B, h (x - y) = ∫ z, ((I (x - z) : ℝ) : ℂ) * h z := by
    intro x
    rw [← integral_indicator hBm]
    rw [← integral_sub_left_eq_self (μ := volume) (fun w => ((I (x - w) : ℝ) : ℂ) * h w) x]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [sub_sub_cancel, I]
    by_cases hy : y ∈ B <;> simp [hy, indicator]
  simp_rw [hinner]
  rw [← integral_indicator hBm]
  have h1 : ∀ x, B.indicator (fun x => ∫ z, ((I (x - z) : ℝ) : ℂ) * h z) x =
      ∫ z, ((I x * I (x - z) : ℝ) : ℂ) * h z := by
    intro x
    by_cases hx : x ∈ B
    · simp [hx, I, indicator]
    · simp [hx, I, indicator]
  simp_rw [h1]
  have hint2 : Integrable (Function.uncurry fun x z => ((I x * I (x - z) : ℝ) : ℂ) * h z)
      (volume.prod volume) := by
    have hp : Integrable (fun p : V × V => ((I p.1 : ℝ) : ℂ) * h p.2) (volume.prod volume) :=
      (hIint.ofReal (𝕜 := ℂ)).mul_prod hint
    refine hp.mono ?_ (Eventually.of_forall fun p => ?_)
    · refine (Measurable.aestronglyMeasurable ?_)
      exact (Complex.measurable_ofReal.comp ((hIm.comp measurable_fst).mul
        (hIm.comp (measurable_fst.sub measurable_snd)))).mul (hc.measurable.comp measurable_snd)
    · simp only [Function.uncurry, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      gcongr
      have : |I (p.1 - p.2)| ≤ 1 := by
        simp only [I]; by_cases h' : p.1 - p.2 ∈ B <;> simp [h', indicator]
      calc |I p.1| * |I (p.1 - p.2)| ≤ |I p.1| * 1 := by gcongr
        _ = |I p.1| := mul_one _
  rw [integral_integral_swap hint2]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [integral_mul_const, integral_complex_ofReal]
  congr 2
  simp_rw [I, ind_mul_ind B z]
  exact integral_indicator_one (hBm.inter (hBm.preimage (continuous_sub_right z).measurable))

/-- The key identity `∫ h · window_R = vol(B_R) ∫∫ h(x − y) d(μ_R ⊗ μ_R)`. -/
theorem integral_window_eq {h : V → ℂ} (hc : Continuous h) (hint : Integrable h) {C : ℝ}
    (hC : ∀ z, ‖h z‖ ≤ C) {R : ℝ} (hR : 0 < R) :
    ∫ z, h z * (window R z : ℂ) =
      ((volume (ball (0 : V) R)).toReal : ℂ) * ∫ p, h (p.1 - p.2) ∂((unifBall (V := V) R).prod (unifBall R)) := by
  set B := ball (0 : V) R
  have hv : 0 < (volume B).toReal := vol_ball_pos hR
  have hprod : (unifBall (V := V) R).prod (unifBall R) =
      ((volume B)⁻¹ * (volume B)⁻¹) • ((volume.restrict B).prod (volume.restrict B)) := by
    rw [unifBall, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  have hFint : Integrable (fun p : V × V => h (p.1 - p.2)) ((volume.restrict B).prod (volume.restrict B)) := by
    haveI : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    exact Integrable.mono' (integrable_const C)
      (hc.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable (Eventually.of_forall fun p => hC _)
  rw [hprod, integral_smul_measure, integral_prod _ hFint, integral_ball_ball hc hint]
  simp only [window, Measure.real]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, Complex.real_smul, ← integral_const_mul]
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  push_cast
  field_simp
  rfl

end StatFormal.TIKernel
