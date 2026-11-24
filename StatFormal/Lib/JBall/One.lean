import StatFormal.Lib.JBall.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The ball-averaged cosine in dimension one (library, untrusted)

In `ℝ¹ = EuclideanSpace ℝ (Fin 1)` the unit ball is `(−1, 1)` under the measure-preserving
coordinate `v ↦ v 0`, so `j₁(y) = ½ ∫_{−1}^{1} cos(yt) dt = sin y / y` for `y ≠ 0`
(`jBall_one_eq`). For `y ≥ 1`, `sin y / y ≤ sin 1` (`sin_div_le_sin_one`): on `[1, π]` by
concavity of `sin` on `[0, π]` (the chord from `0` to `y` lies below the graph at `1`), and on
`(π, ∞)` since `sin y / y ≤ 1/y < 1/2 < 5/6 < sin 1`. Hence `sup_{y ≥ 1} j₁(y) = sin 1`
(`sSup_jBall_one_Ici_one`) and `c₁ = 1 − sin 1`.
-/

noncomputable section
open MeasureTheory Set

set_option linter.style.longLine false

namespace StatFormal.JBall

open StatFormal.Wave31tp (jBall)

local notation "E" d => EuclideanSpace ℝ (Fin d)

/-- The coordinate `v ↦ v 0` of `ℝ¹` as a measurable equivalence onto `ℝ`. -/
def coord1 : (E 1) ≃ᵐ ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm.trans (MeasurableEquiv.funUnique (Fin 1) ℝ)

lemma coord1_apply (v : E 1) : coord1 v = v 0 := rfl

/-- The coordinate of `ℝ¹` is measure preserving. -/
lemma measurePreserving_coord1 : MeasurePreserving coord1 :=
  (volume_preserving_funUnique (Fin 1) ℝ).comp (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 1))

/-- The unit ball of `ℝ¹` is the preimage of `(−1, 1)` under the coordinate. -/
lemma unitBall_one_eq : Metric.ball (0 : E 1) 1 = coord1 ⁻¹' Ioo (-1) 1 := by
  ext v
  simp only [mem_ball_zero_iff, mem_preimage, coord1_apply, mem_Ioo, EuclideanSpace.norm_eq, Fin.sum_univ_one,
    Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs, abs_lt]

lemma volume_unitBall_one : volume (Metric.ball (0 : E 1) 1) = ENNReal.ofReal 2 := by
  rw [unitBall_one_eq, measurePreserving_coord1.measure_preimage measurableSet_Ioo.nullMeasurableSet,
    Real.volume_Ioo]
  norm_num

/-- Integrals of `f(v₁)` over the unit ball of `ℝ¹` are integrals over `[−1, 1]`. -/
lemma integral_unitBall_one (f : ℝ → ℝ) :
    ∫ v in Metric.ball (0 : E 1) 1, f (v 0) = ∫ t in (-1 : ℝ)..1, f t := by
  rw [unitBall_one_eq, intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]
  exact measurePreserving_coord1.setIntegral_preimage_emb coord1.measurableEmbedding f (Ioo (-1) 1)

/-- `j₁(y) = sin y / y` for `y ≠ 0`. -/
theorem jBall_one_eq {y : ℝ} (hy : y ≠ 0) : jBall 1 y = Real.sin y / y := by
  rw [jBall_def, volume_unitBall_one, ENNReal.toReal_ofReal (by norm_num),
    integral_unitBall_one (fun t => Real.cos (y * t)),
    intervalIntegral.integral_comp_mul_left (fun t => Real.cos t) hy, integral_cos]
  simp only [mul_neg, mul_one, Real.sin_neg, smul_eq_mul]
  field_simp
  ring

/-- `sin y / y ≤ sin 1` for `y ≥ 1`. -/
theorem sin_div_le_sin_one {y : ℝ} (hy : 1 ≤ y) : Real.sin y / y ≤ Real.sin 1 := by
  have hy0 : 0 < y := by linarith
  rcases le_or_gt y Real.pi with hyπ | hyπ
  · -- concavity of `sin` on `[0, π]`: `1 = (1/y) • y + (1 − 1/y) • 0`
    have ha : (0 : ℝ) ≤ 1 / y := by positivity
    have hb : (0 : ℝ) ≤ 1 - 1 / y := by rw [sub_nonneg, div_le_one hy0]; exact hy
    have h := strictConcaveOn_sin_Icc.concaveOn.2 (⟨hy0.le, hyπ⟩ : y ∈ Icc 0 Real.pi)
      (⟨le_rfl, Real.pi_pos.le⟩ : (0 : ℝ) ∈ Icc 0 Real.pi) ha hb (by ring)
    simp only [smul_eq_mul, Real.sin_zero, mul_zero, add_zero, one_div_mul_cancel hy0.ne'] at h
    rw [div_eq_inv_mul, ← one_div]
    exact h
  · have h1 : Real.sin y / y ≤ 1 / y := div_le_div_of_nonneg_right (Real.sin_le_one y) hy0.le
    have h2 : 1 / y < 1 / 2 := one_div_lt_one_div_of_lt two_pos (by linarith [Real.two_le_pi])
    have h3 := Real.sin_gt_sub_cube (x := 1) one_pos
    norm_num at h3
    linarith

/-- `sup_{y ≥ 1} j₁(y) = sin 1`, attained at `y = 1`. -/
theorem isGreatest_jBall_one : IsGreatest (jBall 1 '' Ici 1) (Real.sin 1) := by
  refine ⟨⟨1, mem_Ici.2 le_rfl, by rw [jBall_one_eq one_ne_zero, div_one]⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [jBall_one_eq (zero_lt_one.trans_le hy).ne']
  exact sin_div_le_sin_one hy

theorem sSup_jBall_one_Ici_one : sSup (jBall 1 '' Ici 1) = Real.sin 1 :=
  isGreatest_jBall_one.csSup_eq

end StatFormal.JBall
