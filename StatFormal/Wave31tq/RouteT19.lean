import StatFormal.Wave31tq.RouteT20b

/-!
# Wave 31tq, route T (Q19): Proposition S4.14 (untrusted)

`newupperone_of (h1 : Claims.tv_density) (h4 : Claims.bochner_angular) : Claims.newupperone`. The one-sided trimmings
`P′ = min(p, q) + (p − q)₊ 1_{(x₀, x₀+w_P]}`, `Q′ = min(p, q) + (q − p)₊ 1_{(x₀−w_Q, x₀]}` with `w_P, w_Q ≤ W_ε` from the
intermediate value theorem (`MomentTrim.exists_one_sided_pair`) have mass `1 − α⋆ + ε` (so `ε ≤ α⋆`), `|ν| ≤ 2ε`,
`supp ν ⊆ [x₀ − W_ε, x₀ + W_ε]` and `ν(ℝ) = 0`; then `D̄_{α⋆−ε} ≤ ‖∫ φ dν‖` (`MomentTrim.uPath_le_of_le`), and eq:newbochner
(Q4) with eq:newmomentdecay at `N = 1` (Q18) and `k̂₀ ≤ C|ξ|^{−2s}` give
`‖∫ φ dν‖² ≤ (2π)⁻¹C(2ε)² ∫ min(1, ξ²W²)|ξ|^{−2s} dξ`, the integral being `W^{2s−1}(2/(3−2s) + 2/(2s−1))`
(`MomentTrim.integral_minPow_scale`, `MomentTrim.integral_minSq`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace StatFormal.Wave31tq.RouteT

open StatFormal.MomentTrim

/-- The integral of Proposition S4.14 at scale `W > 0`, and its integrability. -/
theorem integral_minSq_scale {s W : ℝ} (hs : 1 / 2 < s) (hs3 : s < 3 / 2) (hW : 0 < W) :
    Integrable (fun ξ : ℝ => min 1 (ξ ^ 2 * W ^ 2) * |ξ| ^ (-2 * s)) ∧
      ∫ ξ : ℝ, min 1 (ξ ^ 2 * W ^ 2) * |ξ| ^ (-2 * s) = W ^ (2 * s - 1) * (2 / (3 - 2 * s) + 2 / (2 * s - 1)) := by
  have e : ∀ ξ : ℝ, min 1 (ξ ^ 2 * W ^ 2) * |ξ| ^ (-2 * s) = min 1 ((W * ξ) ^ (2 * 1) / 1) * |ξ| ^ (-2 * s) := by
    intro ξ; rw [mul_one, div_one, mul_pow, mul_comm (W ^ 2)]
  have e2 : ∀ v : ℝ, min 1 (v ^ (2 * 1) / 1) * |v| ^ (-2 * s) = min 1 (v ^ 2) * |v| ^ (-2 * s) := by
    intro v; rw [mul_one, div_one]
  simp_rw [e]
  refine ⟨integrable_minPow_scale 1 one_pos hs (by push_cast; linarith) hW, ?_⟩
  rw [integral_minPow_scale 1 1 s hW]
  simp_rw [e2]
  rw [integral_minSq hs hs3]

/-- Q19 `newupperone` (Proposition S4.14), from Q1(b) and Q4. -/
theorem newupperone_of (h1 : Claims.tv_density) (h4 : Claims.bochner_angular) : Claims.newupperone := by
  intro H _ _ _ φ k₀ C s P Q _ _ p q x₀ ℓ' r r₀ hk hki hg hC hs hs3 hkb hpm hqm hp0 hq0 hP hQ hℓ hr hr₀ hR hL ε hε
  dsimp only
  have hε0 := hε.1
  obtain ⟨hpi, -⟩ := density_integrable hpm hp0 hP
  obtain ⟨hqi, -⟩ := density_integrable hqm hq0 hQ
  obtain ⟨hW0, -, -⟩ := width_facts hℓ hr hr₀ hε0 hε.2
  obtain ⟨fP, fQ, hp, hm, ht⟩ := exists_one_sided_pair hpm hqm hp0 hq0 hpi hqi hℓ hr hr₀ hR hL hε0 hε.2
  obtain ⟨P', Q', hP'le, hQ'le, hmP, hmQ, htv, hsupp, hmom⟩ := pair_measures h1 hpm hqm hp0 hq0 hP hQ ht
  have hJs := integral_minSq_scale hs hs3 hW0
  set W := ((r + 1) * ε / ℓ') ^ (1 / (r + 1)) with hWdef
  have hmin := integral_min_eq h1 hpm hqm hp0 hq0 hP hQ
  have htv1 : StatFormal.Distances.tvDist P Q ≤ 1 := by
    have := integral_nonneg (f := fun x => min (p x) (q x)) (μ := volume) (fun x => le_min (hp0 x) (hq0 x))
    linarith
  have hεα : ε ≤ StatFormal.Distances.tvDist P Q := by
    have h := Measure.le_iff'.mp hP'le univ
    rw [hmP, measure_univ] at h
    have := ENNReal.ofReal_le_one.mp h
    linarith
  obtain ⟨hJi, hJ⟩ := hJs
  set J := 2 / (3 - 2 * s) + 2 / (2 * s - 1) with hJdef
  have hJ0 : 0 ≤ J := by
    have h1' : 0 < 3 - 2 * s := by linarith
    have h2' : 0 < 2 * s - 1 := by linarith
    positivity
  refine ⟨hεα, ?_, hJ⟩
  -- the explicit trimming bound
  have hu : StatFormal.Wave31ti.uPath φ P Q (StatFormal.Distances.tvDist P Q - ε) ≤
      ‖∫ x, φ x ∂(P' : Measure ℝ) - ∫ x, φ x ∂(Q' : Measure ℝ)‖ :=
    uPath_le_of_le φ P Q (P' : Measure ℝ) (Q' : Measure ℝ) hP'le hQ'le (by linarith)
      (by rw [hmP]; congr 1; ring) (by rw [hmQ]; congr 1; ring)
  -- eq:newmomentdecay with `N = 1`
  have hd : ∀ ξ, ‖ftMeasA (P' : Measure ℝ) ξ - ftMeasA (Q' : Measure ℝ) ξ‖ ≤ 2 * ε * min 1 (|ξ| * W) := by
    intro ξ
    rw [← ftSigned_sub]
    refine (momentdecay_signed _ x₀ W 1 hW0.le le_rfl hsupp hmom ξ).trans ?_
    rw [pow_one, Nat.factorial_one, Nat.cast_one, div_one]
    exact mul_le_mul_of_nonneg_right (ENNReal.toReal_le_of_le_ofReal (by positivity) htv)
      (le_min zero_le_one (by positivity))
  -- eq:newbochner with the majorant `C (2ε)² min(1, ξ²W²) |ξ|^{−2s}`
  set B : ℝ → ℝ := fun ξ => C * (2 * ε) ^ 2 * (min 1 (ξ ^ 2 * W ^ 2) * |ξ| ^ (-2 * s)) with hB
  have hBi : Integrable B := hJi.const_mul _
  have hpt : ∀ᵐ ξ, kHat k₀ ξ * ‖ftMeasA (P' : Measure ℝ) ξ - ftMeasA (Q' : Measure ℝ) ξ‖ ^ 2 ≤ B ξ := by
    have hne : ∀ᵐ ξ : ℝ, ξ ≠ 0 := compl_mem_ae_iff.mpr (measure_singleton 0)
    filter_upwards [hne] with ξ hξ
    have hm0 : 0 ≤ |ξ| * W := by positivity
    have hd2 : ‖ftMeasA (P' : Measure ℝ) ξ - ftMeasA (Q' : Measure ℝ) ξ‖ ^ 2 ≤ (2 * ε) ^ 2 * min 1 (ξ ^ 2 * W ^ 2) := by
      calc ‖ftMeasA (P' : Measure ℝ) ξ - ftMeasA (Q' : Measure ℝ) ξ‖ ^ 2 ≤ (2 * ε * min 1 (|ξ| * W)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (hd ξ) 2
        _ = (2 * ε) ^ 2 * min 1 (ξ ^ 2 * W ^ 2) := by rw [mul_pow (2 * ε), min_one_sq hm0, mul_pow |ξ| W 2, sq_abs]
    calc kHat k₀ ξ * ‖ftMeasA (P' : Measure ℝ) ξ - ftMeasA (Q' : Measure ℝ) ξ‖ ^ 2
        ≤ (C * |ξ| ^ (-2 * s)) * ((2 * ε) ^ 2 * min 1 (ξ ^ 2 * W ^ 2)) :=
          mul_le_mul (hkb ξ hξ) hd2 (sq_nonneg _) (mul_nonneg hC.le (Real.rpow_nonneg (abs_nonneg _) _))
      _ = B ξ := by simp only [hB]; ring
  have hsq := norm_sq_le_of_majorant h4 φ k₀ hk hki hg (P' : Measure ℝ) (Q' : Measure ℝ) B hBi hpt
  have hBint : ∫ ξ, B ξ = C * (2 * ε) ^ 2 * (W ^ (2 * s - 1) * J) := by
    rw [hB, integral_const_mul, hJ]
  rw [hBint] at hsq
  have hCJ : 0 ≤ C / (2 * Real.pi) * J := by positivity
  refine hu.trans (le_of_sq_le_sq' (norm_nonneg _) (by positivity) (hsq.trans (le_of_eq ?_)))
  have hW2 : (W ^ (s - 1 / 2)) ^ 2 = W ^ (2 * s - 1) := by
    rw [← Real.rpow_natCast (W ^ (s - 1 / 2)), ← Real.rpow_mul hW0.le]
    congr 1; push_cast; ring
  rw [mul_pow (2 * ε * W ^ (s - 1 / 2)) (√(C / (2 * Real.pi) * J)) 2, Real.sq_sqrt hCJ,
    mul_pow (2 * ε) (W ^ (s - 1 / 2)) 2, hW2]
  field_simp

end StatFormal.Wave31tq.RouteT
