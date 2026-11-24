import StatFormal.Wave31tu.RouteTPr
import StatFormal.Lib.LaplaceRate.Orders

/-!
# Wave 31tu route T: Theorem 5.11 in the printed `O` form and the grid reading (S4 :985-987; abs :11-13, §1 :84-88, §5 :8-10, :322-323;
untrusted proof material)

* `rate_i_of_pr`: Y19 (i) from Y18 (Pr) (i) with the same constant: `(log(n∨m))^{1/4}L^{1/2} ≤ L^{3/4}` as `L ≥ log(n∨m)`.
* `rate_ii_of_pr`: Y19 (ii) from Y18 (Pr) (ii): `{(log(n∨m))^{1/2}L/(n∧m)}^{4/9} ≤ L^{2/3}(n∧m)^{−4/9}`.
* `grid_of_rate`: Y22 from Y19 (i) at the mesh `h = (n∧m)^{−1/2}` with at most `n∧m` levels: `1 ≤ L^{3/4}` and
  `v_min^{−2}{L_δ^{1/2} + (log(2J/η))^{1/2}} ≤ v_min^{−2}(L_δ^{1/2} + √2)L^{3/4}` (`log(2J/η) ≤ log 2 + L ≤ 2L`).
* `laplace_rate_i_of`, `laplace_rate_ii_of`, `laplace_rate_grid_of`: with the hypotheses of the (G) theorems.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set

namespace StatFormal.Wave31tu.RouteT

open StatFormal.Wave30tz StatFormal.Wave31tl StatFormal.LaplaceRate

/-- **Y19 (i)** from Y18 (Pr) (i) (S4 :985-987). -/
theorem rate_i_of_pr (hpr : Claims.laplace_const_pr_i) : Claims.laplace_rate_i := by
  intro σ P Q _ _ p q x₀ ℓ₀ rs cs hσ hcross hpx hexp hcond
  obtain ⟨C, hC, hall⟩ := hpr σ P Q p q x₀ ℓ₀ rs cs hσ hcross hpx hexp hcond
  refine ⟨C, hC, fun H _ _ _ _ φ hφ J n m α δ s2 η h R hgrid hα0 hJ hδ0 hδ1 hs20 hs24 hη0 hη1 hrun hdef hN10 hmesh => ?_⟩
  obtain ⟨E, hEm, hEp, hEsub⟩ := hall H φ hφ J n m α δ s2 η h R hgrid hα0 hJ hδ0 hδ1 hs20 hs24 hη0 hη1 hrun hdef hN10 hmesh
  refine ⟨E, hEm, hEp, fun z hz => ?_⟩
  obtain ⟨h1, h2⟩ := hEsub hz
  refine ⟨le_trans ?_ h1, h2⟩
  obtain ⟨hN, -, -, hlM, hLlM, -⟩ := setting_facts hN10 hη0 hη1
  have hL : 0 < Real.log (((max n m : ℕ) : ℝ) / η) := by linarith
  have hsN : 0 < √((min n m : ℕ) : ℝ) := Real.sqrt_pos.2 (by linarith)
  have key := quarter_mul_half_le (by linarith) hLlM hL
  have hY : 0 ≤ s2⁻¹ * (√(Real.log (1 / δ)) + √(Real.log (2 * J / η))) := by positivity
  have e1 : C * ((Real.log ((max n m : ℕ) : ℝ)) ^ (1 / 4 : ℝ) * (Real.log (((max n m : ℕ) : ℝ) / η)) ^ (1 / 2 : ℝ) +
      s2⁻¹ * (√(Real.log (1 / δ)) + √(Real.log (2 * J / η)))) / √((min n m : ℕ) : ℝ) ≤
      C * ((Real.log (((max n m : ℕ) : ℝ) / η)) ^ (3 / 4 : ℝ) / √((min n m : ℕ) : ℝ) +
        s2⁻¹ * (√(Real.log (1 / δ)) + √(Real.log (2 * J / η))) / √((min n m : ℕ) : ℝ)) := by
    rw [← add_div, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) hsN.le) hC.le
  linarith

/-- **Y19 (ii)** from Y18 (Pr) (ii) (S4 :985-987). -/
theorem rate_ii_of_pr (hpr : Claims.laplace_const_pr_ii) : Claims.laplace_rate_ii := by
  intro σ P Q _ _ p q x₀ ℓ₀ C' hσ hcross hpx hexp hsum
  obtain ⟨C, hC, hall⟩ := hpr σ P Q p q x₀ ℓ₀ C' hσ hcross hpx hexp hsum
  refine ⟨C, hC, fun H _ _ _ _ φ hφ J n m α δ s2 η h R hgrid hα0 hJ hδ0 hδ1 hs20 hs24 hη0 hη1 hrun hdef hN10 hmesh => ?_⟩
  obtain ⟨E, hEm, hEp, hEsub⟩ := hall H φ hφ J n m α δ s2 η h R hgrid hα0 hJ hδ0 hδ1 hs20 hs24 hη0 hη1 hrun hdef hN10 hmesh
  refine ⟨E, hEm, hEp, fun z hz => ?_⟩
  obtain ⟨h1, h2⟩ := hEsub hz
  refine ⟨le_trans ?_ h1, h2⟩
  obtain ⟨hN, -, -, hlM, hLlM, -⟩ := setting_facts hN10 hη0 hη1
  have hL : 0 < Real.log (((max n m : ℕ) : ℝ) / η) := by linarith
  have key := half_mul_div_rpow_le (by linarith) hLlM hL (by linarith : (0 : ℝ) < ((min n m : ℕ) : ℝ))
  have e1 := mul_le_mul_of_nonneg_left key hC.le
  linarith

/-- **Y22** from Y19 (i): a grid with at most `n∧m` levels and mesh `(n∧m)^{−1/2}` below `α⋆`. -/
theorem grid_of_rate (hrate : Claims.laplace_rate_i) : Claims.laplace_rate_grid := by
  intro σ P Q _ _ p q x₀ ℓ₀ rs cs δ s2 η hσ hcross hpx hexp hcond hδ0 hδ1 hs20 hs24 hη0 hη1
  obtain ⟨C₁, hC₁, hall⟩ := hrate σ P Q p q x₀ ℓ₀ rs cs hσ hcross hpx hexp hcond
  set B := s2⁻¹ * (√(Real.log (1 / δ)) + √2) with hBdef
  have hB : 0 ≤ B := by positivity
  refine ⟨1 + C₁ + C₁ * B, by positivity, fun H _ _ _ _ φ hφ J n m α R hgrid hα0 hJ hJN hrun hdef hN10 hmesh => ?_⟩
  obtain ⟨E, hEm, hEp, hEsub⟩ := hall H φ hφ J n m α δ s2 η (1 / √((min n m : ℕ) : ℝ)) R hgrid hα0 hJ hδ0 hδ1 hs20 hs24
    hη0 hη1 hrun hdef hN10 hmesh
  refine ⟨E, hEm, hEp, fun z hz => ?_⟩
  obtain ⟨h1, h2⟩ := hEsub hz
  refine ⟨le_trans ?_ h1, h2⟩
  obtain ⟨hN, hMN, hM, hlM, hLlM, -⟩ := setting_facts hN10 hη0 hη1
  set N := ((min n m : ℕ) : ℝ) with hNdef
  set M := ((max n m : ℕ) : ℝ) with hMdef
  set L := Real.log (M / η) with hLdef
  have hL1 : 1 ≤ L := hlM.trans hLlM
  have hsN : 0 < √N := Real.sqrt_pos.2 (by linarith)
  have hL34 : 1 ≤ L ^ (3 / 4 : ℝ) := one_le_rpow_three_quarters hL1
  have hJM : (J : ℝ) ≤ M := by
    have : (J : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast hJN
    linarith
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hlogJ : Real.log (2 * J / η) ≤ 2 * L := by
    have h1 : Real.log (2 * J / η) ≤ Real.log (2 * M / η) :=
      Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by linarith) hη0.le)
    have h2 : Real.log (2 * M / η) = Real.log 2 + L := by
      rw [hLdef, mul_div_assoc, Real.log_mul (by norm_num) (by positivity)]
    have h3 : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
    linarith
  have hsq : √(Real.log (2 * J / η)) ≤ √2 * L ^ (3 / 4 : ℝ) := by
    calc √(Real.log (2 * J / η)) ≤ √(2 * L) := Real.sqrt_le_sqrt hlogJ
      _ = √2 * √L := Real.sqrt_mul (by norm_num) L
      _ ≤ √2 * L ^ (3 / 4 : ℝ) := mul_le_mul_of_nonneg_left (sqrt_le_rpow_three_quarters hL1) (by positivity)
  have hY : s2⁻¹ * (√(Real.log (1 / δ)) + √(Real.log (2 * J / η))) ≤ B * L ^ (3 / 4 : ℝ) := by
    have hd : √(Real.log (1 / δ)) ≤ √(Real.log (1 / δ)) * L ^ (3 / 4 : ℝ) :=
      le_mul_of_one_le_right (Real.sqrt_nonneg _) hL34
    have : √(Real.log (1 / δ)) + √(Real.log (2 * J / η)) ≤ (√(Real.log (1 / δ)) + √2) * L ^ (3 / 4 : ℝ) := by
      linarith
    calc s2⁻¹ * (√(Real.log (1 / δ)) + √(Real.log (2 * J / η))) ≤ s2⁻¹ * ((√(Real.log (1 / δ)) + √2) * L ^ (3 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left this (inv_nonneg.2 hs20.le)
      _ = B * L ^ (3 / 4 : ℝ) := by rw [hBdef]; ring
  have hsum : 1 + C₁ * (L ^ (3 / 4 : ℝ) + s2⁻¹ * (√(Real.log (1 / δ)) + √(Real.log (2 * J / η)))) ≤
      (1 + C₁ + C₁ * B) * L ^ (3 / 4 : ℝ) := by
    have := mul_le_mul_of_nonneg_left hY hC₁.le
    nlinarith
  have e : 1 / √N + C₁ * (L ^ (3 / 4 : ℝ) / √N + s2⁻¹ * (√(Real.log (1 / δ)) + √(Real.log (2 * J / η))) / √N) =
      (1 + C₁ * (L ^ (3 / 4 : ℝ) + s2⁻¹ * (√(Real.log (1 / δ)) + √(Real.log (2 * J / η))))) / √N := by
    field_simp
  have key : 1 / √N + C₁ * (L ^ (3 / 4 : ℝ) / √N + s2⁻¹ * (√(Real.log (1 / δ)) + √(Real.log (2 * J / η))) / √N) ≤
      (1 + C₁ + C₁ * B) * L ^ (3 / 4 : ℝ) / √N := by
    rw [e]; exact div_le_div_of_nonneg_right hsum hsN.le
  linarith

/-- **Y19 (i)**, `thm:laplacerate` (i). -/
theorem laplace_rate_i_of (h4 : Claims.lap_intervals) (h8 : Claims.condR_facts) (h10 : Claims.lap_clip)
    (h15 : Claims.lap_fitted) (h16 : Claims.lap_bets) (h17 : Claims.lap_rescale) : Claims.laplace_rate_i :=
  rate_i_of_pr (laplace_const_pr_i_of h4 h8 h10 h15 h16 h17)

/-- **Y19 (ii)**, `thm:laplacerate` (ii). -/
theorem laplace_rate_ii_of (h4 : Claims.lap_intervals) (h10 : Claims.lap_clip) (h15 : Claims.lap_fitted)
    (h16 : Claims.lap_bets) (h17 : Claims.lap_rescale) : Claims.laplace_rate_ii :=
  rate_ii_of_pr (laplace_const_pr_ii_of h4 h10 h15 h16 h17)

/-- **Y22**, the abstract, §1 and §5 readings. -/
theorem laplace_rate_grid_of (h4 : Claims.lap_intervals) (h8 : Claims.condR_facts) (h10 : Claims.lap_clip)
    (h15 : Claims.lap_fitted) (h16 : Claims.lap_bets) (h17 : Claims.lap_rescale) : Claims.laplace_rate_grid :=
  grid_of_rate (laplace_rate_i_of h4 h8 h10 h15 h16 h17)

end StatFormal.Wave31tu.RouteT
