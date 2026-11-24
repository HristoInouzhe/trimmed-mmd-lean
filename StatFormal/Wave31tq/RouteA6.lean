import StatFormal.Wave31tq.RouteA2
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Wave 31tq, route A: Q6 `sobolev_needs` (untrusted proof file)

`k̂₀` is integrable (Q2's `kHat_integrable`, from L13), so a lower bound `c(1 + |ξ|²)^{−s} ≤ k̂₀` makes `(1 + |ξ|²)^{−s}` integrable on
`V`. In polar form (Mathlib's `integrable_fun_norm_addHaar`, `d ≥ 1`) `y^{d−1}(1 + y²)^{−s}` is integrable on `(0, ∞)`, hence on `(1, ∞)`
`y^{d−1−2s}` is integrable (`AngularFourier.min_mul_rpow_le_one_add_sq_rpow_neg`), which forces `d − 1 − 2s < −1`
(`integrableOn_Ioi_rpow_iff`), i.e. `s > d/2`. The two exponent inequalities follow by arithmetic.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace StatFormal.Wave31tq.RouteA

open StatFormal.AngularFourier

/-- If `(1 + |ξ|²)^{−s}` is integrable on a nonzero finite-dimensional inner-product space `V`, then `dim V < 2s`. -/
theorem finrank_lt_of_integrable_rpow_neg {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {s : ℝ} (hd : 0 < Module.finrank ℝ V)
    (h : Integrable (fun ξ : V => (1 + ‖ξ‖ ^ 2) ^ (-s))) : (Module.finrank ℝ V : ℝ) < 2 * s := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos hd
  set d := Module.finrank ℝ V with hd_def
  have h1 := (integrable_fun_norm_addHaar (volume : Measure V) (f := fun r : ℝ => (1 + r ^ 2) ^ (-s))).1 h
  have h2 := h1.mono_set (Ioi_subset_Ioi zero_le_one)
  set m : ℝ := min 1 ((2 : ℝ) ^ (-s)) with hm_def
  have hm : 0 < m := lt_min one_pos (by positivity)
  have h3 : IntegrableOn (fun y : ℝ => y ^ ((d : ℝ) - 1 - 2 * s)) (Ioi 1) := by
    refine (h2.const_mul m⁻¹).mono' ?_ ?_
    · exact ((measurable_id.pow_const _).aestronglyMeasurable)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y (hy : 1 < y)
      have hy0 : 0 < y := by linarith
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hy0.le _)]
      have hsplit : y ^ ((d : ℝ) - 1 - 2 * s) = y ^ (d - 1) * y ^ (-2 * s) := by
        rw [show (d : ℝ) - 1 - 2 * s = ((d - 1 : ℕ) : ℝ) + (-2 * s) by
          rw [Nat.cast_sub (by omega), Nat.cast_one]; ring, Real.rpow_add hy0, Real.rpow_natCast]
      have hlow := min_mul_rpow_le_one_add_sq_rpow_neg (s := s) hy.le
      have hyd : 0 ≤ y ^ (d - 1) := by positivity
      rw [hsplit, smul_eq_mul]
      calc y ^ (d - 1) * y ^ (-2 * s) = m⁻¹ * (y ^ (d - 1) * (m * y ^ (-2 * s))) := by
            field_simp
        _ ≤ m⁻¹ * (y ^ (d - 1) * (1 + y ^ 2) ^ (-s)) := by gcongr
  have h4 := (integrableOn_Ioi_rpow_iff one_pos).1 h3
  linarith

theorem sobolev_needs_route : Claims.sobolev_needs := by
  intro V _ _ _ _ _ k₀ c s hd hc hi hpd hc0 hlow
  have hk := kHat_integrable hc hi hpd
  have hint : Integrable (fun ξ : V => (1 + ‖ξ‖ ^ 2) ^ (-s)) := by
    refine (hk.const_mul c⁻¹).mono' ?_ (Eventually.of_forall fun ξ => ?_)
    · exact ((measurable_const.add (measurable_norm.pow_const 2)).pow_const (-s)).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _), le_inv_mul_iff₀ hc0]
      exact hlow ξ
  have hlt := finrank_lt_of_integrable_rpow_neg hd hint
  have hd0 : (0 : ℝ) ≤ Module.finrank ℝ V := Nat.cast_nonneg _
  refine ⟨by linarith, by linarith, ?_⟩
  exact div_lt_div_of_pos_left two_pos (by positivity) (by linarith)

end StatFormal.Wave31tq.RouteA
