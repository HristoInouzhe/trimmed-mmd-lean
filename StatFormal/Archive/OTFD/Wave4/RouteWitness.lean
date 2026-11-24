import StatFormal.Archive.OTFD.Wave4.Statements

/-!
# Route: C `lem:neural-witness-ball`

Fix `u ∈ S`, `D = ‖T(u) − Q(u)‖`, `e = (T(u) − Q(u))/D`. For `v ∈ B(u + re, r/4)`:
`3r/4 ≤ ⟨e, v − u⟩ ≤ ‖v − u‖ ≤ 5r/4`, and monotonicity of `T` gives
`‖T(v) − Q(v)‖ ‖v − u‖ ≥ ⟨T(v) − Q(v), v − u⟩ ≥ D(3r/4) − ω(5r/4)‖v − u‖`, hence
`‖T(v) − Q(v)‖ ≥ 3D/5 − ω(5r/4)` on the ball. Integrating over the ball (inside `O`):
`m (3D/5 − ω)_+² ≤ 𝓡 ≤ R`, so `D ≤ (5/3)(ω + √(R/m))`. The lower integral needs no
measurability of `T` or `Q`.
-/

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace ENNReal

namespace StatFormal.OTFD.Wave4

theorem neural_witness_ball : Claims.neural_witness_ball := by
  intro K μ S O T Q ω r m R _hS _hO _hSO _hQ hT hr hthick hωmono hmod hm hball hR u hu
  set D := ‖T u - Q u‖ with hD
  set w0 := ω (5 * r / 4) with hw0
  have hu_th : u ∈ Metric.cthickening (5 * r / 4) S :=
    Metric.self_subset_cthickening S hu
  have hω0 : 0 ≤ ω 0 := by
    have := hmod u hu_th u hu_th
    simpa using this
  have hw0nn : 0 ≤ w0 :=
    hω0.trans (hωmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 (by positivity)) (by positivity))
  have hsq : 0 ≤ Real.sqrt (R / m) := Real.sqrt_nonneg _
  by_cases hc : 3 * D / 5 - w0 ≤ 0
  · nlinarith
  push_neg at hc
  set c := 3 * D / 5 - w0 with hcdef
  have hDpos : 0 < D := by nlinarith
  set e : EuclideanSpace ℝ (Fin K) := D⁻¹ • (T u - Q u) with he
  have he1 : ‖e‖ = 1 := by
    rw [he, norm_smul, norm_inv, norm_norm, ← hD, inv_mul_cancel₀ hDpos.ne']
  have heTQ : T u - Q u = D • e := by
    rw [he, smul_smul, mul_inv_cancel₀ hDpos.ne', one_smul]
  -- the pointwise lower bound on the ball
  have hlow : ∀ v ∈ Metric.ball (u + r • e) (r / 4), c ≤ ‖T v - Q v‖ := by
    intro v hv
    rw [Metric.mem_ball, dist_eq_norm] at hv
    have hdecomp : v - u = r • e + (v - (u + r • e)) := by abel
    have hinner : 3 * r / 4 ≤ ⟪e, v - u⟫_ℝ := by
      rw [hdecomp, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, he1]
      have := real_inner_le_norm e (v - (u + r • e))
      have h2 : -‖v - (u + r • e)‖ ≤ ⟪e, v - (u + r • e)⟫_ℝ := by
        have := abs_real_inner_le_norm e (v - (u + r • e))
        rw [he1, one_mul] at this
        linarith [neg_abs_le ⟪e, v - (u + r • e)⟫_ℝ]
      nlinarith
    have hnorm_le : ‖v - u‖ ≤ 5 * r / 4 := by
      rw [hdecomp]
      calc ‖r • e + (v - (u + r • e))‖ ≤ ‖r • e‖ + ‖v - (u + r • e)‖ := norm_add_le _ _
        _ ≤ r + r / 4 := by
          rw [norm_smul, he1, mul_one, Real.norm_of_nonneg hr.le]; linarith
        _ = 5 * r / 4 := by ring
    have hnorm_ge : 3 * r / 4 ≤ ‖v - u‖ := by
      have := real_inner_le_norm e (v - u)
      rw [he1, one_mul] at this
      linarith
    have hv_th : v ∈ Metric.cthickening (5 * r / 4) S :=
      Metric.mem_cthickening_of_dist_le v u _ S hu (by rw [dist_eq_norm]; exact hnorm_le)
    have hvO : v ∈ O := hthick hv_th
    have huO : u ∈ O := hthick hu_th
    have hmono := hT v hvO u huO
    have hQ : ‖Q u - Q v‖ ≤ w0 := by
      refine (hmod u hu_th v hv_th).trans ?_
      apply hωmono (Set.mem_Ici.2 (norm_nonneg _)) (Set.mem_Ici.2 (by positivity))
      rw [norm_sub_rev]; exact hnorm_le
    have hsplit : ⟪T v - Q v, v - u⟫_ℝ =
        ⟪T v - T u, v - u⟫_ℝ + ⟪T u - Q u, v - u⟫_ℝ + ⟪Q u - Q v, v - u⟫_ℝ := by
      rw [← inner_add_left, ← inner_add_left]; congr 1; abel
    have h3 : ⟪T u - Q u, v - u⟫_ℝ = D * ⟪e, v - u⟫_ℝ := by
      rw [heTQ, inner_smul_left]; simp
    have h4 : -(w0 * ‖v - u‖) ≤ ⟪Q u - Q v, v - u⟫_ℝ := by
      have := abs_real_inner_le_norm (Q u - Q v) (v - u)
      have h5 : ‖Q u - Q v‖ * ‖v - u‖ ≤ w0 * ‖v - u‖ :=
        mul_le_mul_of_nonneg_right hQ (norm_nonneg _)
      linarith [neg_abs_le ⟪Q u - Q v, v - u⟫_ℝ]
    have h6 : ⟪T v - Q v, v - u⟫_ℝ ≤ ‖T v - Q v‖ * ‖v - u‖ := real_inner_le_norm _ _
    have hkey : D * (3 * r / 4) - w0 * ‖v - u‖ ≤ ‖T v - Q v‖ * ‖v - u‖ := by
      have := mul_le_mul_of_nonneg_left hinner hDpos.le
      linarith
    have hdpos : 0 < ‖v - u‖ := by linarith
    -- divide by ‖v − u‖ ≤ 5r/4
    have : 3 * D / 5 * ‖v - u‖ ≤ D * (3 * r / 4) := by nlinarith
    have h7 : (3 * D / 5 - w0) * ‖v - u‖ ≤ ‖T v - Q v‖ * ‖v - u‖ := by nlinarith
    exact le_of_mul_le_mul_right h7 hdpos
  -- integrate over the ball
  have hballO : Metric.ball (u + r • e) (r / 4) ⊆ O := by
    intro v hv
    apply hthick
    apply Metric.mem_cthickening_of_dist_le v u _ S hu
    rw [Metric.mem_ball] at hv
    calc dist v u ≤ dist v (u + r • e) + dist (u + r • e) u := dist_triangle _ _ _
      _ ≤ r / 4 + r := by
        refine add_le_add hv.le ?_
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, he1, mul_one, Real.norm_of_nonneg hr.le]
      _ = 5 * r / 4 := by ring
  have hint : ENNReal.ofReal (c ^ 2) * ENNReal.ofReal m ≤ ENNReal.ofReal R := by
    calc ENNReal.ofReal (c ^ 2) * ENNReal.ofReal m
        ≤ ENNReal.ofReal (c ^ 2) * μ (Metric.ball (u + r • e) (r / 4)) :=
          mul_le_mul_right (hball u hu e he1) _
      _ = ∫⁻ _ in Metric.ball (u + r • e) (r / 4), ENNReal.ofReal (c ^ 2) ∂μ :=
          (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ v in Metric.ball (u + r • e) (r / 4), ENNReal.ofReal (‖T v - Q v‖ ^ 2) ∂μ := by
          refine setLIntegral_mono' Metric.isOpen_ball.measurableSet fun v hv => ?_
          exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hc.le (hlow v hv) 2)
      _ ≤ ∫⁻ v in O, ENNReal.ofReal (‖T v - Q v‖ ^ 2) ∂μ := lintegral_mono_set hballO
      _ ≤ ENNReal.ofReal R := hR
  rw [← ENNReal.ofReal_mul (sq_nonneg c), ENNReal.ofReal_le_ofReal_iff'] at hint
  have hcm : c ^ 2 * m ≤ R := by
    rcases hint with h | h
    · exact h
    · exfalso; have : 0 < c ^ 2 * m := by positivity
      linarith
  have hcsq : c ≤ Real.sqrt (R / m) := by
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ hm]; exact hcm
  linarith

end StatFormal.OTFD.Wave4
