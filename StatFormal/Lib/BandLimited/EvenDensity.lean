import StatFormal.Wave31tp.Statements
import StatFormal.Lib.FourierOps.Mollify
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Even probability densities on the line and mollified intervals (library, untrusted)

For a measurable, nonnegative, even `b : ℝ → ℝ` with `∫ b = 1` (an even probability density), write
`Φ(s) = ∫_{(−∞, s]} b` (the distribution function) and `b̄(s) = ∫_{(s, ∞)} b` (the tail). Classical facts:

* `Φ(s) + b̄(s) = 1`, `Φ(−s) = b̄(s)` (evenness), `b̄(0) = 1/2`, so `b̄ ≤ 1/2` on `[0, ∞)`;
* `b̄` is antitone and tends to `0` at `+∞` (dominated convergence);
* for the dilation `b_Ω(x) = Ω b(Ω x)` (`dilateR Ω⁻¹ b`, `Ω > 0`) and an interval `I = (a, a + ρ)`, the mollified indicator is
  `(1_I ⋆ b_Ω)(x) = Φ(Ω(x − a)) − Φ(Ω(x − a − ρ))`; it is continuous, and
  `|1_{(a,∞)}(x) − (1_I ⋆ b_Ω)(x)| ≤ b̄(Ω|x − a|) + b̄(Ωρ/2) + 1_{(a + ρ/2, ∞)}(x)` for every `x`.

These are the elementary steps of the proof of Lemma S4.12 of the trimmed-MMD paper (the error of `1_{(x₀,x₀+ρ)} ⋆ b_Ω`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology

namespace StatFormal.BandLimited

open StatFormal.Wave31tp

variable {b : ℝ → ℝ}

/-- A function with integral `1` is integrable (otherwise its Bochner integral would be `0`). -/
theorem integrable_of_integral_eq_one (h1 : ∫ t, b t = 1) : Integrable b :=
  Integrable.of_integral_ne_zero (by rw [h1]; exact one_ne_zero)

/-- The distribution function and the tail add up to the total mass: `Φ(s) + b̄(s) = 1`. -/
theorem cdf_add_tail (h1 : ∫ t, b t = 1) (s : ℝ) :
    (∫ x in Iic s, b x) + ∫ x in Ioi s, b x = 1 := by
  have hi := integrable_of_integral_eq_one h1
  rw [intervalIntegral.integral_Iic_add_Ioi hi.integrableOn hi.integrableOn, h1]

/-- Evenness: `Φ(−s) = b̄(s)`. -/
theorem cdf_neg (hev : ∀ t, b (-t) = b t) (s : ℝ) : ∫ x in Iic (-s), b x = ∫ x in Ioi s, b x := by
  rw [← integral_comp_neg_Ioi]
  simp_rw [hev]

/-- The tail of an even probability density at `0` is `1/2`. -/
theorem tail_zero (h1 : ∫ t, b t = 1) (hev : ∀ t, b (-t) = b t) : ∫ x in Ioi 0, b x = 1 / 2 := by
  have h := cdf_add_tail h1 0
  have h' := cdf_neg hev 0
  rw [neg_zero] at h'
  linarith

/-- The tail is antitone. -/
theorem tail_antitone (h0 : ∀ t, 0 ≤ b t) (h1 : ∫ t, b t = 1) : Antitone fun s => ∫ x in Ioi s, b x := by
  intro s t hst
  exact setIntegral_mono_set (integrable_of_integral_eq_one h1).integrableOn
    (ae_of_all _ fun x => h0 x) (Ioi_subset_Ioi hst).eventuallyLE

/-- The tail is nonnegative. -/
theorem tail_nonneg (h0 : ∀ t, 0 ≤ b t) (s : ℝ) : 0 ≤ ∫ x in Ioi s, b x :=
  setIntegral_nonneg measurableSet_Ioi fun x _ => h0 x

/-- The distribution function is nonnegative. -/
theorem cdf_nonneg (h0 : ∀ t, 0 ≤ b t) (s : ℝ) : 0 ≤ ∫ x in Iic s, b x :=
  setIntegral_nonneg measurableSet_Iic fun x _ => h0 x

/-- `b̄ ≤ 1/2` on `[0, ∞)` for an even probability density. -/
theorem tail_le_half (h0 : ∀ t, 0 ≤ b t) (h1 : ∫ t, b t = 1) (hev : ∀ t, b (-t) = b t) {s : ℝ} (hs : 0 ≤ s) :
    ∫ x in Ioi s, b x ≤ 1 / 2 :=
  (tail_antitone h0 h1 hs).trans (tail_zero h1 hev).le

/-- The tail of an integrable function tends to `0` at `+∞` (dominated convergence). -/
theorem tendsto_tail (hi : Integrable b) : Tendsto (fun s => ∫ x in Ioi s, b x) atTop (𝓝 0) := by
  have h : Tendsto (fun s => ∫ x, (Ioi s).indicator b x) atTop (𝓝 (∫ _ : ℝ, (0 : ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖b x‖) ?_ ?_ hi.norm ?_
    · exact Eventually.of_forall fun s => (hi.indicator measurableSet_Ioi).aestronglyMeasurable
    · exact Eventually.of_forall fun s => ae_of_all _ fun x => norm_indicator_le_norm_self b x
    · refine ae_of_all _ fun x => tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop x] with s hs
      rw [indicator_of_notMem (show x ∉ Ioi s from fun h => (not_lt.2 hs) h)]
  simpa [integral_indicator measurableSet_Ioi] using h

/-- On the line, the dilation `dilateR Ω⁻¹ b` is `x ↦ Ω b(Ω x)`. -/
theorem dilateR_inv_apply (b : ℝ → ℝ) (Ω x : ℝ) : dilateR Ω⁻¹ b x = Ω * b (Ω * x) := by
  simp [dilateR]

/-- **The mollified interval**: `(1_{(a,a+ρ)} ⋆ b_Ω)(x) = ∫_{Ω(x−a−ρ)}^{Ω(x−a)} b` for `Ω > 0`, `ρ ≥ 0`. -/
theorem mollify_Ioo_eq_intervalIntegral (b : ℝ → ℝ) {Ω : ℝ} (hΩ : 0 < Ω) {ρ : ℝ} (hρ : 0 ≤ ρ) (a x : ℝ) :
    mollify (Ioo a (a + ρ)) (dilateR Ω⁻¹ b) x = ∫ v in Ω * (x - a - ρ)..Ω * (x - a), b v := by
  rw [FourierOps.mollify_apply]
  have hfun : (fun t => (Ioo a (a + ρ)).indicator (fun _ => (1 : ℝ)) t * dilateR Ω⁻¹ b (x - t)) =
      (Ioo a (a + ρ)).indicator (fun t => Ω * b (Ω * x - Ω * t)) := by
    funext t
    by_cases ht : t ∈ Ioo a (a + ρ)
    · simp [indicator_of_mem ht, dilateR_inv_apply, mul_sub]
    · simp [indicator_of_notMem ht]
  rw [hfun, integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_mul (fun v => b v) hΩ.ne', smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ hΩ.ne', one_mul]
  congr 1 <;> ring

/-- The mollified interval through the distribution function: `Φ(Ω(x−a)) − Φ(Ω(x−a−ρ))`. -/
theorem mollify_Ioo_eq_cdf (h1 : ∫ t, b t = 1) {Ω : ℝ} (hΩ : 0 < Ω) {ρ : ℝ} (hρ : 0 ≤ ρ) (a x : ℝ) :
    mollify (Ioo a (a + ρ)) (dilateR Ω⁻¹ b) x =
      (∫ v in Iic (Ω * (x - a)), b v) - ∫ v in Iic (Ω * (x - a - ρ)), b v := by
  have hi := integrable_of_integral_eq_one h1
  rw [mollify_Ioo_eq_intervalIntegral b hΩ hρ, intervalIntegral.integral_Iic_sub_Iic hi.integrableOn hi.integrableOn]

/-- The mollified interval is continuous (difference of two continuous primitives). -/
theorem continuous_mollify_Ioo (h1 : ∫ t, b t = 1) {Ω : ℝ} (hΩ : 0 < Ω) {ρ : ℝ} (hρ : 0 ≤ ρ) (a : ℝ) :
    Continuous (mollify (Ioo a (a + ρ)) (dilateR Ω⁻¹ b)) := by
  have hi := integrable_of_integral_eq_one h1
  have hii : ∀ u v : ℝ, IntervalIntegrable b volume u v := fun u v => hi.intervalIntegrable
  have hprim := intervalIntegral.continuous_primitive hii 0
  have heq : mollify (Ioo a (a + ρ)) (dilateR Ω⁻¹ b) =
      fun x => (∫ v in (0 : ℝ)..Ω * (x - a), b v) - ∫ v in (0 : ℝ)..Ω * (x - a - ρ), b v := by
    funext x
    rw [mollify_Ioo_eq_intervalIntegral b hΩ hρ, intervalIntegral.integral_interval_sub_left (hii _ _) (hii _ _)]
  rw [heq]
  exact (hprim.comp (continuous_const.mul (continuous_id.sub continuous_const))).sub
    (hprim.comp (continuous_const.mul ((continuous_id.sub continuous_const).sub continuous_const)))

/-- **The pointwise error bound** of the mollified interval against the half-line indicator: for every `x`,
`|1_{(a,∞)}(x) − (1_{(a,a+ρ)} ⋆ b_Ω)(x)| ≤ b̄(Ω|x − a|) + b̄(Ωρ/2) + 1_{(a+ρ/2, ∞)}(x)`. -/
theorem abs_indicator_sub_mollify_le (h0 : ∀ t, 0 ≤ b t) (h1 : ∫ t, b t = 1) (hev : ∀ t, b (-t) = b t)
    {Ω : ℝ} (hΩ : 0 < Ω) {ρ : ℝ} (hρ : 0 ≤ ρ) (a x : ℝ) :
    |(Ioi a).indicator (fun _ => (1 : ℝ)) x - mollify (Ioo a (a + ρ)) (dilateR Ω⁻¹ b) x| ≤
      (∫ v in Ioi (Ω * |x - a|), b v) + (∫ v in Ioi (Ω * ρ / 2), b v) +
        (Ioi (a + ρ / 2)).indicator (fun _ => (1 : ℝ)) x := by
  have hi := integrable_of_integral_eq_one h1
  have hT0 := tail_nonneg h0
  have hC0 := cdf_nonneg h0
  have hanti := tail_antitone h0 h1
  have hind0 : 0 ≤ (Ioi (a + ρ / 2)).indicator (fun _ => (1 : ℝ)) x :=
    indicator_nonneg (fun _ _ => zero_le_one) x
  have hf0 : 0 ≤ mollify (Ioo a (a + ρ)) (dilateR Ω⁻¹ b) x :=
    FourierOps.mollify_nonneg _ (fun t => by rw [dilateR_inv_apply]; exact mul_nonneg hΩ.le (h0 _)) x
  have hbi : Integrable (dilateR Ω⁻¹ b) := FourierOps.integrable_dilateR hi (inv_pos.2 hΩ)
  have hf1 : mollify (Ioo a (a + ρ)) (dilateR Ω⁻¹ b) x ≤ 1 :=
    FourierOps.mollify_le_one _ (fun t => by rw [dilateR_inv_apply]; exact mul_nonneg hΩ.le (h0 _)) hbi
      (by rw [FourierOps.integral_dilateR b (inv_pos.2 hΩ), h1]) x
  rw [mollify_Ioo_eq_cdf h1 hΩ hρ] at hf0 hf1 ⊢
  rcases le_or_gt x a with hxa | hxa
  · -- left of `a`: the error is `f(x) ≤ Φ(Ω(x−a)) = b̄(Ω(a−x))`
    rw [indicator_of_notMem (show x ∉ Ioi a from fun h => (not_lt.2 hxa) h), zero_sub, abs_neg, abs_of_nonneg hf0]
    have hc : ∫ v in Iic (Ω * (x - a)), b v = ∫ v in Ioi (Ω * |x - a|), b v := by
      rw [abs_of_nonpos (by linarith), ← cdf_neg hev]
      congr 2; ring_nf
    have := hC0 (Ω * (x - a - ρ))
    linarith [hT0 (Ω * ρ / 2)]
  · rw [indicator_of_mem (show x ∈ Ioi a from hxa), abs_of_nonneg (by linarith)]
    -- `1 − f(x) = b̄(Ω(x−a)) + Φ(Ω(x−a−ρ))`
    have h1' := cdf_add_tail h1 (Ω * (x - a))
    have hxa' : |x - a| = x - a := abs_of_pos (by linarith)
    rw [hxa']
    rcases le_or_gt x (a + ρ / 2) with hxm | hxm
    · have hc : ∫ v in Iic (Ω * (x - a - ρ)), b v ≤ ∫ v in Ioi (Ω * ρ / 2), b v := by
        rw [show Ω * (x - a - ρ) = -(Ω * (a + ρ - x)) by ring, cdf_neg hev]
        exact hanti (by nlinarith)
      linarith
    · rw [indicator_of_mem (show x ∈ Ioi (a + ρ / 2) from hxm)]
      have := hC0 (Ω * (x - a))
      linarith [hT0 (Ω * (x - a)), hT0 (Ω * ρ / 2), hC0 (Ω * (x - a - ρ))]

end StatFormal.BandLimited
