import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import StatFormal.Lib.TIKernel.Spectra

/-!
# The explicit `L²` feature map of the Laplace kernel on `ℝ` (library, untrusted)

For `σ > 0` let `ψ_σ(x) ∈ L²(ℝ)` be the class of `t ↦ √(2/σ) e^{(t−x)/σ} 1_{t ≤ x}` (`lapFn`, `lapFeat`). Then

* `lapFeat_gram`: `⟪ψ_σ x, ψ_σ y⟫ = e^{−|x−y|/σ}` (the Laplace Gram function; `∫_{(−∞, x∧y]} e^{2t/σ} = (σ/2) e^{2(x∧y)/σ}`);
* `inner_lapFeat`: for `u ∈ L²(ℝ)`, `⟪u, ψ_σ x⟫ = √(2/σ) e^{−x/σ} ∫_{(−∞,x]} e^{t/σ} u(t) dt`;
* `integrableOn_exp_mul_Iic_of_memLp`: `t ↦ e^{t/σ} u(t)` is integrable on every `(−∞, x]` (Cauchy–Schwarz);
* `laplaceProfile_continuous`, `laplaceProfile_integrable`: the profile `e^{−|z|/σ}` is continuous and integrable.

This feature map is the elementary model of the Laplace RKHS used for its `H¹` form (`LaplaceH1.Core`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.LaplaceH1

/-- The profile `t ↦ √(2/σ) e^{(t − x)/σ} 1_{t ≤ x}` of the Laplace feature at `x`. -/
def lapFn (σ x : ℝ) : ℝ → ℝ := (Iic x).indicator fun t => √(2 / σ) * Real.exp (σ⁻¹ * (t - x))

/-- The Laplace profile `e^{−|z|/σ}` is continuous. -/
lemma laplaceProfile_continuous (σ : ℝ) : Continuous (fun z : ℝ => Real.exp (-|z| / σ)) := by
  fun_prop

/-- The Laplace profile `e^{−|z|/σ}` is integrable for `σ > 0`. -/
lemma laplaceProfile_integrable {σ : ℝ} (hσ : 0 < σ) : Integrable (fun z : ℝ => Real.exp (-|z| / σ)) := by
  have h := StatFormal.TIKernel.laplace_integrable.comp_mul_left' (inv_ne_zero hσ.ne')
  refine h.congr (Eventually.of_forall fun z => ?_)
  simp only [abs_mul, abs_inv, abs_of_pos hσ]
  congr 1
  field_simp

lemma exp_sq (c t : ℝ) : Real.exp (c * t) ^ 2 = Real.exp ((2 * c) * t) := by
  rw [sq, ← Real.exp_add]; ring_nf

lemma integrableOn_exp_sq_Iic {σ : ℝ} (hσ : 0 < σ) (x : ℝ) :
    IntegrableOn (fun t => Real.exp (σ⁻¹ * t) ^ 2) (Iic x) := by
  simp_rw [exp_sq]
  exact integrableOn_exp_mul_Iic (by positivity) x

/-- `t ↦ e^{t/σ}` is square integrable on `(−∞, x]`. -/
lemma memLp_exp_Iic {σ : ℝ} (hσ : 0 < σ) (x : ℝ) :
    MemLp (fun t => Real.exp (σ⁻¹ * t)) 2 (volume.restrict (Iic x)) := by
  rw [memLp_two_iff_integrable_sq (by fun_prop)]
  exact integrableOn_exp_sq_Iic hσ x

/-- For `u ∈ L²`, `t ↦ e^{t/σ} u(t)` is integrable on `(−∞, x]`. -/
lemma integrableOn_exp_mul_Iic_of_memLp {σ : ℝ} (hσ : 0 < σ) {u : ℝ → ℝ} (hu : MemLp u 2 volume) (x : ℝ) :
    IntegrableOn (fun t => Real.exp (σ⁻¹ * t) * u t) (Iic x) := by
  have h1 := memLp_exp_Iic hσ x
  have h2 : MemLp u 2 (volume.restrict (Iic x)) := hu.restrict _
  exact h1.integrable_mul h2

lemma lapFn_eq (σ x t : ℝ) :
    lapFn σ x t = (Iic x).indicator (fun t => √(2 / σ) * Real.exp (-(σ⁻¹ * x)) * Real.exp (σ⁻¹ * t)) t := by
  unfold lapFn
  by_cases ht : t ∈ Iic x
  · rw [indicator_of_mem ht, indicator_of_mem ht, mul_assoc, ← Real.exp_add]; ring_nf
  · rw [indicator_of_notMem ht, indicator_of_notMem ht]

lemma measurable_lapFn (σ x : ℝ) : Measurable (lapFn σ x) := by
  unfold lapFn
  exact (by fun_prop : Measurable fun t => √(2 / σ) * Real.exp (σ⁻¹ * (t - x))).indicator measurableSet_Iic

/-- The Laplace feature profile is square integrable. -/
lemma memLp_lapFn {σ : ℝ} (hσ : 0 < σ) (x : ℝ) : MemLp (lapFn σ x) 2 volume := by
  have hfun : lapFn σ x = (Iic x).indicator (fun t => √(2 / σ) * Real.exp (-(σ⁻¹ * x)) * Real.exp (σ⁻¹ * t)) :=
    funext (lapFn_eq σ x)
  rw [hfun]
  exact (memLp_indicator_iff_restrict (μ := volume) (p := 2) (s := Iic x) measurableSet_Iic.nullMeasurableSet).2
    ((memLp_exp_Iic hσ x).const_mul _)

open scoped Classical in
/-- The explicit Laplace feature `ψ_σ(x) ∈ L²(ℝ)` (junk `0` when the profile is not in `L²`, i.e. never for `σ > 0`). -/
def lapFeat (σ x : ℝ) : Lp ℝ 2 (volume : Measure ℝ) :=
  if h : MemLp (lapFn σ x) 2 volume then h.toLp _ else 0

lemma lapFeat_ae {σ : ℝ} (hσ : 0 < σ) (x : ℝ) : (lapFeat σ x : ℝ → ℝ) =ᵐ[volume] lapFn σ x := by
  unfold lapFeat
  rw [dite_eq_left (memLp_lapFn hσ x)]
  exact MemLp.coeFn_toLp _

/-- The `L²(ℝ)` inner product of real functions. -/
lemma inner_L2_eq (u v : Lp ℝ 2 (volume : Measure ℝ)) : ⟪u, v⟫_ℝ = ∫ t, u t * v t := by
  rw [MeasureTheory.L2.inner_def]
  simp [mul_comm]

/-- `‖u‖² = ∫ u²` in `L²(ℝ)`. -/
lemma norm_sq_L2_eq (u : Lp ℝ 2 (volume : Measure ℝ)) : ‖u‖ ^ 2 = ∫ t, u t ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_L2_eq]
  simp [sq]

/-- **The reproducing formula of the explicit feature**: `⟪u, ψ_σ x⟫ = √(2/σ) e^{−x/σ} ∫_{(−∞,x]} e^{t/σ} u`. -/
theorem inner_lapFeat {σ : ℝ} (hσ : 0 < σ) (u : Lp ℝ 2 (volume : Measure ℝ)) (x : ℝ) :
    ⟪u, lapFeat σ x⟫_ℝ = √(2 / σ) * Real.exp (-(σ⁻¹ * x)) * ∫ t in Iic x, Real.exp (σ⁻¹ * t) * u t := by
  rw [inner_L2_eq]
  have h1 : (fun t => u t * lapFeat σ x t) =ᵐ[volume] fun t => u t * lapFn σ x t := by
    filter_upwards [lapFeat_ae hσ x] with t ht
    rw [ht]
  rw [integral_congr_ae h1]
  have h2 : (fun t => u t * lapFn σ x t) =
      (Iic x).indicator (fun t => √(2 / σ) * Real.exp (-(σ⁻¹ * x)) * (Real.exp (σ⁻¹ * t) * u t)) := by
    funext t
    rw [lapFn_eq]
    by_cases ht : t ∈ Iic x
    · rw [indicator_of_mem ht, indicator_of_mem ht]; ring
    · rw [indicator_of_notMem ht, indicator_of_notMem ht, mul_zero]
  rw [h2, integral_indicator measurableSet_Iic, integral_const_mul]

/-- **The Gram function of the explicit feature**: `⟪ψ_σ x, ψ_σ y⟫ = e^{−|x−y|/σ}`. -/
theorem lapFeat_gram {σ : ℝ} (hσ : 0 < σ) (x y : ℝ) :
    ⟪lapFeat σ x, lapFeat σ y⟫_ℝ = Real.exp (-|x - y| / σ) := by
  rw [inner_L2_eq]
  have h1 : (fun t => lapFeat σ x t * lapFeat σ y t) =ᵐ[volume] fun t => lapFn σ x t * lapFn σ y t := by
    filter_upwards [lapFeat_ae hσ x, lapFeat_ae hσ y] with t hx hy
    rw [hx, hy]
  rw [integral_congr_ae h1]
  set m := min x y
  have h2 : (fun t => lapFn σ x t * lapFn σ y t) = (Iic m).indicator
      (fun t => (2 / σ) * Real.exp (-(σ⁻¹ * x)) * Real.exp (-(σ⁻¹ * y)) * Real.exp ((2 * σ⁻¹) * t)) := by
    funext t
    rw [lapFn_eq, lapFn_eq]
    by_cases ht : t ∈ Iic m
    · have hx : t ∈ Iic x := mem_Iic.mpr ((mem_Iic.mp ht).trans (min_le_left _ _))
      have hy : t ∈ Iic y := mem_Iic.mpr ((mem_Iic.mp ht).trans (min_le_right _ _))
      rw [indicator_of_mem ht, indicator_of_mem hx, indicator_of_mem hy, ← exp_sq]
      have : √(2 / σ) * √(2 / σ) = 2 / σ := Real.mul_self_sqrt (by positivity)
      linear_combination (Real.exp (-(σ⁻¹ * x)) * Real.exp (-(σ⁻¹ * y)) * Real.exp (σ⁻¹ * t) ^ 2) * this
    · rw [indicator_of_notMem ht]
      have : t ∉ Iic x ∨ t ∉ Iic y := by
        by_contra hc
        push Not at hc
        exact ht (mem_Iic.mpr (le_min (mem_Iic.mp hc.1) (mem_Iic.mp hc.2)))
      rcases this with h | h
      · rw [indicator_of_notMem h, zero_mul]
      · rw [indicator_of_notMem h, mul_zero]
  rw [h2, integral_indicator measurableSet_Iic, integral_const_mul, integral_exp_mul_Iic (by positivity)]
  have hm : -|x - y| = 2 * m - x - y := by
    rcases le_total x y with h | h
    · rw [show m = x from min_eq_left h, abs_of_nonpos (by linarith)]; ring
    · rw [show m = y from min_eq_right h, abs_of_nonneg (by linarith)]; ring
  have hexp : -|x - y| / σ = -(σ⁻¹ * x) + -(σ⁻¹ * y) + 2 * σ⁻¹ * m := by
    rw [hm]; field_simp; ring
  rw [hexp, Real.exp_add, Real.exp_add]
  field_simp

end StatFormal.LaplaceH1
