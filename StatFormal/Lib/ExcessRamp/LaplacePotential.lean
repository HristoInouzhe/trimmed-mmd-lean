import StatFormal.Lib.ExcessRamp.LaplaceGreen
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Order.Compact

/-!
# Laplace potentials of finite measures on the line and their maximum principle

Library component (trimmed-mmd, Proposition 5.10 (iii)). Untrusted library code.

For `σ > 0` and a finite measure `μ` on `ℝ`, the Laplace potential is `U_μ(x) = ∫ e^{−|x−y|/σ} dμ(y)`.

## Main results

* `lapPot_continuous`, `tendsto_lapPot_cocompact`: `U_μ` is continuous and tends to `0` at `±∞` (dominated convergence);
* `lintegral_lapPot`: `∫ U_μ dx = C_σ μ(ℝ)` with `C_σ = ∫ e^{−|x|/σ} dx < ∞` (Tonelli and translation invariance);
* `exists_lt_of_lapPot_ne`: if `μ(ℝ) = ν(ℝ)` and `U_μ ≠ U_ν`, then `U_μ − U_ν` takes a positive value (a continuous function
  `≤ 0` with integral `0` vanishes);
* `lapPot_second_diff_eq`, `lapPot_second_diff_le`: the second difference of `U_μ` at `x₀` with step `h` is
  `2(cosh(h/σ) − 1)U_μ(x₀)` when `μ` does not charge `(x₀ − h, x₀ + h)`, and at most that in general (the discrete form of
  `(1 − σ²∂²)e^{−|x|/σ} = 2σδ₀`, `ExcessRamp.laplace_second_diff_le`);
* `lapPot_max_principle`: **maximum principle**. If `μ(ℝ) = ν(ℝ)`, `d = U_μ − U_ν ≢ 0` and `μ` does not charge `{d > c}`, then
  `d ≤ c` everywhere: at a maximum point of `d` (it exists and is positive) inside the open set `{d > c}`, the second difference
  of `d` is `≥ 2(cosh(h/σ) − 1) max d > 0`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology Real
open scoped ENNReal

namespace StatFormal.ExcessRamp

/-- The Laplace potential `U_μ(x) = ∫ e^{−|x−y|/σ} dμ(y)` of a measure `μ` on `ℝ`. -/
def lapPot (σ : ℝ) (μ : Measure ℝ) (x : ℝ) : ℝ := ∫ y, exp (-|x - y| / σ) ∂μ

lemma laplace_kernel_le_one {σ : ℝ} (hσ : 0 < σ) (x y : ℝ) : exp (-|x - y| / σ) ≤ 1 :=
  exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (abs_nonneg _)) hσ.le)

lemma laplace_kernel_continuous (σ : ℝ) : Continuous fun p : ℝ × ℝ => exp (-|p.1 - p.2| / σ) := by
  fun_prop

lemma laplace_kernel_integrable {σ : ℝ} (hσ : 0 < σ) (μ : Measure ℝ) [IsFiniteMeasure μ] (x : ℝ) :
    Integrable (fun y => exp (-|x - y| / σ)) μ :=
  Integrable.of_mem_Icc 0 1 (by fun_prop : Continuous fun y => exp (-|x - y| / σ)).measurable.aemeasurable
    (ae_of_all _ fun y => ⟨(exp_pos _).le, laplace_kernel_le_one hσ x y⟩)

lemma lapPot_nonneg (σ : ℝ) (μ : Measure ℝ) (x : ℝ) : 0 ≤ lapPot σ μ x :=
  integral_nonneg fun _ => (exp_pos _).le

/-- The Laplace potential of a finite measure is continuous. -/
theorem lapPot_continuous {σ : ℝ} (hσ : 0 < σ) (μ : Measure ℝ) [IsFiniteMeasure μ] : Continuous (lapPot σ μ) := by
  refine continuous_of_dominated (bound := fun _ => 1) (fun x => ?_) (fun x => ae_of_all _ fun y => ?_)
    (integrable_const 1) (ae_of_all _ fun y => by fun_prop)
  · exact (by fun_prop : Continuous fun y => exp (-|x - y| / σ)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]; exact laplace_kernel_le_one hσ x y

lemma tendsto_kernel_of_abs {σ : ℝ} (hσ : 0 < σ) {l : Filter ℝ} {y : ℝ}
    (h : Tendsto (fun x => |x - y|) l atTop) : Tendsto (fun x => exp (-|x - y| / σ)) l (𝓝 0) :=
  tendsto_exp_atBot.comp ((tendsto_neg_atTop_atBot.comp h).atBot_div_const hσ)

lemma tendsto_lapPot_of {σ : ℝ} (hσ : 0 < σ) (μ : Measure ℝ) [IsFiniteMeasure μ] {l : Filter ℝ}
    [l.IsCountablyGenerated] (h : ∀ y, Tendsto (fun x => |x - y|) l atTop) : Tendsto (lapPot σ μ) l (𝓝 0) := by
  have := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := l)
    (F := fun x y => exp (-|x - y| / σ)) (f := fun _ => 0) (fun _ => 1)
    (Eventually.of_forall fun x => (by fun_prop : Continuous fun y => exp (-|x - y| / σ)).aestronglyMeasurable)
    (Eventually.of_forall fun x => ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]; exact laplace_kernel_le_one hσ x y)
    (integrable_const 1) (ae_of_all _ fun y => tendsto_kernel_of_abs hσ (h y))
  rw [integral_zero] at this
  exact this

/-- The Laplace potential of a finite measure vanishes at infinity. -/
theorem tendsto_lapPot_cocompact {σ : ℝ} (hσ : 0 < σ) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Tendsto (lapPot σ μ) (cocompact ℝ) (𝓝 0) := by
  rw [cocompact_eq_atBot_atTop]
  refine Tendsto.sup ?_ ?_
  · exact tendsto_lapPot_of hσ μ fun y =>
      tendsto_abs_atBot_atTop.comp (tendsto_atBot_add_const_right _ (-y) tendsto_id)
  · exact tendsto_lapPot_of hσ μ fun y =>
      tendsto_abs_atTop_atTop.comp (tendsto_atTop_add_const_right _ (-y) tendsto_id)

/-- The profile `e^{−|x|/σ}` is integrable on `ℝ` (after `Lib/TIKernel/Spectra.laplace_integrable`, rescaled). -/
lemma laplace_profile_integrable {σ : ℝ} (hσ : 0 < σ) : Integrable fun x : ℝ => exp (-|x| / σ) := by
  have h1 : Integrable fun x : ℝ => exp (-|x|) := by
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
    constructor
    · refine (integrableOn_exp_Iic 0).congr_fun (fun x hx => ?_) measurableSet_Iic
      simp only [abs_of_nonpos (mem_Iic.mp hx), neg_neg]
    · refine (integrableOn_exp_neg_Ioi 0).congr_fun (fun x hx => ?_) measurableSet_Ioi
      simp only [abs_of_pos (mem_Ioi.mp hx)]
  have h2 := h1.comp_div hσ.ne'
  refine h2.congr (ae_of_all _ fun x => ?_)
  simp only [abs_div, abs_of_pos hσ, neg_div]

/-- The constant `C_σ = ∫ e^{−|x|/σ} dx` is finite. -/
lemma lintegral_laplace_profile_ne_top {σ : ℝ} (hσ : 0 < σ) :
    ∫⁻ x : ℝ, ENNReal.ofReal (exp (-|x| / σ)) ≠ ∞ := by
  rw [← ofReal_integral_eq_lintegral_ofReal (laplace_profile_integrable hσ) (ae_of_all _ fun _ => (exp_pos _).le)]
  exact ENNReal.ofReal_ne_top

/-- **Tonelli**: `∫ U_μ dx = C_σ μ(ℝ)`. -/
theorem lintegral_lapPot {σ : ℝ} (hσ : 0 < σ) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∫⁻ x, ENNReal.ofReal (lapPot σ μ x) = (∫⁻ x : ℝ, ENNReal.ofReal (exp (-|x| / σ))) * μ univ := by
  have h1 : ∀ x, ENNReal.ofReal (lapPot σ μ x) = ∫⁻ y, ENNReal.ofReal (exp (-|x - y| / σ)) ∂μ := fun x =>
    ofReal_integral_eq_lintegral_ofReal (laplace_kernel_integrable hσ μ x) (ae_of_all _ fun _ => (exp_pos _).le)
  simp_rw [h1]
  have hmeas : Measurable (Function.uncurry fun (x y : ℝ) => ENNReal.ofReal (exp (-|x - y| / σ))) :=
    (laplace_kernel_continuous σ).measurable.ennreal_ofReal
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  have h2 : ∀ y : ℝ, ∫⁻ x, ENNReal.ofReal (exp (-|x - y| / σ)) = ∫⁻ x : ℝ, ENNReal.ofReal (exp (-|x| / σ)) :=
    fun y => lintegral_sub_right_eq_self (fun x => ENNReal.ofReal (exp (-|x| / σ))) y
  simp_rw [h2]
  rw [lintegral_const, mul_comm]

/-- If two finite measures of equal mass have different Laplace potentials, the difference takes a positive value. -/
theorem exists_lt_of_lapPot_ne {σ : ℝ} (hσ : 0 < σ) (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmass : μ univ = ν univ) (hne : ∃ x, lapPot σ μ x ≠ lapPot σ ν x) : ∃ x, lapPot σ ν x < lapPot σ μ x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x₁, hx₁⟩ := hne
  have hle : (fun x => ENNReal.ofReal (lapPot σ μ x)) ≤ᵐ[volume] fun x => ENNReal.ofReal (lapPot σ ν x) :=
    ae_of_all _ fun x => ENNReal.ofReal_le_ofReal (hcon x)
  have hfin : ∫⁻ x, ENNReal.ofReal (lapPot σ μ x) ≠ ∞ := by
    rw [lintegral_lapPot hσ μ]
    exact ENNReal.mul_ne_top (lintegral_laplace_profile_ne_top hσ) (measure_ne_top μ univ)
  have hcμ := lapPot_continuous hσ μ
  have hcν := lapPot_continuous hσ ν
  have hae := ae_eq_of_ae_le_of_lintegral_le hle hfin
    (ENNReal.continuous_ofReal.comp hcν).measurable.aemeasurable
    (by rw [lintegral_lapPot hσ μ, lintegral_lapPot hσ ν, hmass])
  have heq := ((ENNReal.continuous_ofReal.comp hcμ).ae_eq_iff_eq volume (ENNReal.continuous_ofReal.comp hcν)).1 hae
  have := congrFun heq x₁
  simp only [Function.comp_apply] at this
  exact hx₁ ((ENNReal.ofReal_eq_ofReal_iff (lapPot_nonneg σ μ x₁) (lapPot_nonneg σ ν x₁)).1 this)

/-- The second difference of a Laplace potential as an integral of the kernel's second difference. -/
lemma lapPot_second_diff_integral {σ : ℝ} (hσ : 0 < σ) (μ : Measure ℝ) [IsFiniteMeasure μ] (x₀ h : ℝ) :
    lapPot σ μ (x₀ + h) + lapPot σ μ (x₀ - h) - 2 * lapPot σ μ x₀ =
      ∫ y, (exp (-|x₀ + h - y| / σ) + exp (-|x₀ - h - y| / σ) - 2 * exp (-|x₀ - y| / σ)) ∂μ := by
  unfold lapPot
  have i1 := laplace_kernel_integrable hσ μ (x₀ + h)
  have i2 := laplace_kernel_integrable hσ μ (x₀ - h)
  have i3 := laplace_kernel_integrable hσ μ x₀
  have i12 : Integrable (fun y => exp (-|x₀ + h - y| / σ) + exp (-|x₀ - h - y| / σ)) μ := i1.add i2
  have i3' : Integrable (fun y => 2 * exp (-|x₀ - y| / σ)) μ := i3.const_mul 2
  rw [integral_sub i12 i3', integral_add i1 i2, integral_const_mul]

/-- The second difference of `U_μ` is at most `2(cosh(h/σ) − 1)U_μ(x₀)`. -/
theorem lapPot_second_diff_le {σ : ℝ} (hσ : 0 < σ) (μ : Measure ℝ) [IsFiniteMeasure μ] (x₀ : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    lapPot σ μ (x₀ + h) + lapPot σ μ (x₀ - h) - 2 * lapPot σ μ x₀ ≤ 2 * (cosh (h / σ) - 1) * lapPot σ μ x₀ := by
  rw [lapPot_second_diff_integral hσ μ, lapPot, ← integral_const_mul]
  refine integral_mono ?_ ((laplace_kernel_integrable hσ μ _).const_mul _) fun y => laplace_second_diff_le hσ x₀ y hh
  exact ((laplace_kernel_integrable hσ μ _).add (laplace_kernel_integrable hσ μ _)).sub
    ((laplace_kernel_integrable hσ μ _).const_mul 2)

/-- If `μ` does not charge `(x₀ − h, x₀ + h)`, the second difference of `U_μ` is `2(cosh(h/σ) − 1)U_μ(x₀)`. -/
theorem lapPot_second_diff_eq {σ : ℝ} (hσ : 0 < σ) (μ : Measure ℝ) [IsFiniteMeasure μ] (x₀ : ℝ) {h : ℝ} (hh : 0 ≤ h)
    (hμ : μ (Metric.ball x₀ h) = 0) :
    lapPot σ μ (x₀ + h) + lapPot σ μ (x₀ - h) - 2 * lapPot σ μ x₀ = 2 * (cosh (h / σ) - 1) * lapPot σ μ x₀ := by
  rw [lapPot_second_diff_integral hσ μ, lapPot, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hμ] with y hy
  rw [Metric.mem_ball, Real.dist_eq, not_lt, abs_sub_comm] at hy
  exact laplace_second_diff_eq hσ x₀ y hh hy

/-- **Maximum principle for Laplace potentials.** Let `μ, ν` be finite measures on `ℝ` of equal mass, `d = U_μ − U_ν`, and
suppose `d` is not identically `0` and `μ` does not charge `{d > c}`. Then `d ≤ c` everywhere. -/
theorem lapPot_max_principle {σ : ℝ} (hσ : 0 < σ) (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmass : μ univ = ν univ) (hne : ∃ x, lapPot σ μ x ≠ lapPot σ ν x) {c : ℝ}
    (hnull : μ {x | c < lapPot σ μ x - lapPot σ ν x} = 0) : ∀ x, lapPot σ μ x - lapPot σ ν x ≤ c := by
  set d : ℝ → ℝ := fun x => lapPot σ μ x - lapPot σ ν x with hd
  have hdc : Continuous d := (lapPot_continuous hσ μ).sub (lapPot_continuous hσ ν)
  have hdlim : Tendsto d (cocompact ℝ) (𝓝 0) := by
    simpa using (tendsto_lapPot_cocompact hσ μ).sub (tendsto_lapPot_cocompact hσ ν)
  by_contra hcon
  push Not at hcon
  obtain ⟨x₁, hx₁⟩ := hcon
  obtain ⟨xp, hxp⟩ := exists_lt_of_lapPot_ne hσ μ ν hmass hne
  have hxp' : 0 < d xp := by simp only [hd]; linarith
  -- a point `z` with `d z > max(c, 0)`
  obtain ⟨z, hzc, hz0⟩ : ∃ z, c < d z ∧ 0 < d z := by
    rcases le_total (d x₁) (d xp) with h | h
    · exact ⟨xp, hx₁.trans_le h, hxp'⟩
    · exact ⟨x₁, hx₁, hxp'.trans_le h⟩
  have hev : ∀ᶠ x in cocompact ℝ, d x ≤ d z :=
    (hdlim.eventually (gt_mem_nhds hz0)).mono fun x hx => hx.le
  obtain ⟨x₀, hx₀⟩ := hdc.exists_forall_ge' z hev
  have hx₀c : c < d x₀ := hzc.trans_le (hx₀ z)
  have hx₀0 : 0 < d x₀ := hz0.trans_le (hx₀ z)
  -- a window around `x₀` inside the open set `{d > c}`
  have hO : IsOpen {x | c < d x} := isOpen_lt continuous_const hdc
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO x₀ hx₀c
  have hμball : μ (Metric.ball x₀ ε) = 0 := measure_mono_null hball hnull
  have h1 := lapPot_second_diff_eq hσ μ x₀ hε.le hμball
  have h2 := lapPot_second_diff_le hσ ν x₀ hε.le
  have hcosh : 0 < cosh (ε / σ) - 1 := by
    have := Real.one_lt_cosh.2 (div_pos hε hσ).ne'
    linarith
  have h3 : 0 < 2 * (cosh (ε / σ) - 1) * d x₀ := by positivity
  have h4 := hx₀ (x₀ + ε)
  have h5 := hx₀ (x₀ - ε)
  simp only [hd] at h3 h4 h5
  nlinarith

end StatFormal.ExcessRamp
