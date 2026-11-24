import StatFormal.Wave31tu.Statements
import StatFormal.Lib.FixedPoint.Basic

set_option linter.style.longLine false

/-!
# Wave31tu, chunk F: the arithmetic of Proposition S4.27 (`prop:lapfitted`, S4 :1293-1340)

Pure real-number statements; the probabilistic and RKHS inputs (Lemmas S4.21, S4.22, S4.25, S4.26 and `eq:lappop`) enter as real
hypotheses. With `e₄ = ε^{1/4}`:

* `epsFitI_pos`, `epsFitII_pos`: `ε_fit > 0` (its last term is positive when `n′ ∧ m′ ≥ 1`);
* `fixed_point_i` (case (i)): the first three terms of `ε_fit` give `|Δ⋆| ≤ a + c_V^{−1/2}ϖ + c_V^{−1}bε^{−1/4} < κ₀ε/4`, so
  `y ≥ c_Vε^{5/4}/2` and `b ≤ y/4`; the weighted AM–GM inequality and the fourth term (`(ϖ/√y)^5 ≤ ε`) solve the fixed-point
  inequality `N̂y + T̂ ≤ ε + a + ϖN̂^{1/2}T̂^{3/10} + bN̂` as `N̂y/4 + 7T̂/10 ≤ 3ε`, so `N̂ ≤ 24c_V^{−1}ε^{−1/4}`, `T̂ ≤ 5ε`, and then
  `|Δ⋆| + Δ̂ ≤ 2a + 9c_V^{−1/2}ϖ + 25c_V^{−1}bε^{−1/4} ≤ κ₀ε/4` (each of `a, ϖ, b` contributes at most `κ₀ε/12`);
* `fixed_point_ii` (case (ii)): the same with `ϖ′N̂^{1/2} ≤ N̂y/4 + ϖ′²/y`, `ϖ′²/y ≤ ε`, `N̂ ≤ 12c_V^{−1}ε^{−1/4}`, `T̂ ≤ 3ε`,
  `1 + √12 < 5`.
-/

noncomputable section

namespace StatFormal.Wave31tu.RouteF

open StatFormal.FixedPoint

/-- `ε_fit > 0` in case (i). -/
theorem epsFitI_pos {κ cv a ϖ b : ℝ} {nm : ℕ} (hκ : 0 < κ) (hcv : 0 < cv) (hnm : 1 ≤ nm) :
    0 < epsFitI κ cv a ϖ b nm := by
  have hnm' : (0 : ℝ) < nm := by exact_mod_cast hnm
  have : 0 < (1920 / (κ * cv ^ 2 * nm)) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  exact this.trans_le (le_max_right _ _)

/-- `ε_fit > 0` in case (ii). -/
theorem epsFitII_pos {κ cv a ϖ b : ℝ} {nm : ℕ} (hκ : 0 < κ) (hcv : 0 < cv) (hnm : 1 ≤ nm) :
    0 < epsFitII κ cv a ϖ b nm := by
  have hnm' : (0 : ℝ) < nm := by exact_mod_cast hnm
  have : 0 < (576 / (κ * cv ^ 2 * nm)) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  exact this.trans_le (le_max_right _ _)

/-- `√(24 · 5^{3/5}) ≤ 8`. -/
theorem sqrt_24_five_le : √(24 * (5 : ℝ) ^ (3 / 5 : ℝ)) ≤ 8 := by
  have h : 24 * (5 : ℝ) ^ (3 / 5 : ℝ) ≤ 8 ^ 2 := by
    have := five_rpow_three_fifths_le; nlinarith
  calc √(24 * (5 : ℝ) ^ (3 / 5 : ℝ)) ≤ √(8 ^ 2) := Real.sqrt_le_sqrt h
    _ = 8 := Real.sqrt_sq (by norm_num)

/-- `√12 ≤ 4`. -/
theorem sqrt_12_le : √(12 : ℝ) ≤ 4 := by
  calc √(12 : ℝ) ≤ √(4 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
    _ = 4 := Real.sqrt_sq (by norm_num)

/-- **The fixed point, case (i)** (S4 :1306-1333). Real-number form: `Ns = max(‖φ⋆‖, ½)`, `Ts = err(φ⋆)`, `Δs = Δ⋆`, `Nh = N̂`,
`Th = T̂`, `Δh = Δ̂`; `hΔs`, `hΔh` are Lemma S4.25(b), `hy` is Lemma S4.22(iii), `hi` is Lemma S4.22(i). -/
theorem fixed_point_i {κ cv a ϖ b ε Ns Ts Δs Nh Th Δh y : ℝ} {nm : ℕ}
    (hκ0 : 0 < κ) (hκ1 : κ < 1) (hcv : 0 < cv) (hϖ : 0 ≤ ϖ) (hb : 0 ≤ b) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hfit : epsFitI κ cv a ϖ b nm ≤ ε)
    (hNs0 : 0 ≤ Ns) (hNs : Ns * (cv * ε ^ (1 / 4 : ℝ)) ≤ 1) (hTs0 : 0 ≤ Ts) (hTs : Ts ≤ ε)
    (hΔs : |Δs| ≤ a + ϖ * Ns ^ (1 / 2 : ℝ) * Ts ^ (3 / 10 : ℝ) + b * Ns)
    (hy : |Δs| ≤ κ * ε / 4 → cv * ε ^ (5 / 4 : ℝ) / 2 ≤ y)
    (hNh0 : 0 ≤ Nh) (hTh0 : 0 ≤ Th) (hi : Nh * y + Th ≤ ε + Δh)
    (hΔh : |Δh| ≤ a + ϖ * Nh ^ (1 / 2 : ℝ) * Th ^ (3 / 10 : ℝ) + b * Nh) :
    cv * ε ^ (5 / 4 : ℝ) / 2 ≤ y ∧ Nh * (cv * ε ^ (1 / 4 : ℝ)) ≤ 24 ∧ Th ≤ 5 * ε ∧ |Δs| + Δh ≤ κ * ε / 4 := by
  simp only [epsFitI, max_le_iff] at hfit
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩ := hfit
  set e4 := ε ^ (1 / 4 : ℝ) with he4def
  have he4 : 0 < e4 := rpow_quarter_pos hε
  have hκε : 0 < κ * ε := mul_pos hκ0 hε
  have hκεle : κ * ε ≤ ε := mul_le_of_le_one_left hε.le hκ1.le
  -- the first three terms
  have ha : a ≤ κ * ε / 24 := by
    rw [div_le_iff₀ hκ0] at h1; linarith only [h1]
  have hsc : 0 < √cv := Real.sqrt_pos.2 hcv
  have hϖc : ϖ / √cv ≤ κ * ε / 108 := by
    rw [div_le_iff₀ (mul_pos hκ0 hsc)] at h2
    rw [div_le_iff₀ hsc]; linarith only [h2]
  have h3' : 300 * b / (κ * cv) ≤ ε * e4 := by
    rw [← rpow_five_quarters hε]
    exact le_rpow_of_rpow_le (by positivity) (by norm_num) (by norm_num) h3
  have hbe : b ≤ κ * cv * (ε * e4) / 300 := by
    rw [div_le_iff₀ (mul_pos hκ0 hcv)] at h3'; linarith only [h3']
  have hbc : b / (cv * e4) ≤ κ * ε / 300 := by
    rw [div_le_iff₀ (mul_pos hcv he4)]; linarith only [hbe]
  -- the population fluctuation
  have hps : Ns ^ (1 / 2 : ℝ) * Ts ^ (3 / 10 : ℝ) ≤ 1 / √cv := by
    have := sqrt_mul_rpow_le (K := 1) (L := 1) hNs0 hTs0 hcv hε hε1 zero_le_one hNs (by linarith only [hTs])
    rwa [Real.one_rpow, mul_one, Real.sqrt_one] at this
  have hϖs : ϖ * Ns ^ (1 / 2 : ℝ) * Ts ^ (3 / 10 : ℝ) ≤ ϖ / √cv := by
    calc ϖ * Ns ^ (1 / 2 : ℝ) * Ts ^ (3 / 10 : ℝ) = ϖ * (Ns ^ (1 / 2 : ℝ) * Ts ^ (3 / 10 : ℝ)) := mul_assoc _ _ _
      _ ≤ ϖ * (1 / √cv) := mul_le_mul_of_nonneg_left hps hϖ
      _ = ϖ / √cv := by ring
  have hNs' : Ns ≤ 1 / (cv * e4) := by rw [le_div_iff₀ (mul_pos hcv he4)]; exact hNs
  have hbs : b * Ns ≤ b / (cv * e4) := by
    calc b * Ns ≤ b * (1 / (cv * e4)) := mul_le_mul_of_nonneg_left hNs' hb
      _ = b / (cv * e4) := by ring
  have hΔs' : |Δs| ≤ a + ϖ / √cv + b / (cv * e4) := by linarith only [hΔs, hϖs, hbs]
  have hΔs4 : |Δs| ≤ κ * ε / 4 := by linarith only [hΔs', ha, hϖc, hbc, hκε]
  -- `y ≥ c_V ε^{5/4}/2` and `b ≤ y/4`
  have hy1 := hy hΔs4
  have hy' : cv * (ε * e4) / 2 ≤ y := by rw [← rpow_five_quarters hε]; exact hy1
  have hX : 0 < cv * (ε * e4) := by positivity
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy'
  have hby : b ≤ y / 4 := by
    have : κ * (cv * (ε * e4)) ≤ cv * (ε * e4) := mul_le_of_le_one_left hX.le hκ1.le
    linarith only [this, hbe, hy', hX]
  -- the fixed point
  have hW := fifth_power_le hϖ hcv hε hy1 h4
  have hamgm := amgm_half_three_tenths_fifth hNh0 hTh0 hϖ hy0
  have hbN : b * Nh ≤ y / 4 * Nh := mul_le_mul_of_nonneg_right hby hNh0
  have hΔh1 : Δh ≤ |Δh| := le_abs_self _
  have hfp : Nh * y / 4 + 7 * Th / 10 ≤ 3 * ε := by
    linarith only [hi, hΔh1, hΔh, hamgm, hbN, ha, hW, hκεle, hε]
  have hNy0 : 0 ≤ Nh * y := mul_nonneg hNh0 hy0.le
  have hNy : Nh * y ≤ 12 * ε := by linarith only [hfp, hTh0]
  have hTh5 : Th ≤ 5 * ε := by linarith only [hfp, hNy0, hε]
  have hNh24 : Nh * (cv * e4) ≤ 24 := by
    have h1 : Nh * (cv * (ε * e4) / 2) ≤ Nh * y := mul_le_mul_of_nonneg_left hy' hNh0
    have h2 : Nh * (cv * e4) * ε ≤ 24 * ε := by linarith only [h1, hNy]
    exact le_of_mul_le_mul_right h2 hε
  -- the fitted fluctuation
  have hph : Nh ^ (1 / 2 : ℝ) * Th ^ (3 / 10 : ℝ) ≤ 8 / √cv := by
    have := sqrt_mul_rpow_le (K := 24) (L := 5) hNh0 hTh0 hcv hε hε1 (by norm_num) hNh24 hTh5
    exact this.trans (div_le_div_of_nonneg_right sqrt_24_five_le hsc.le)
  have hϖh : ϖ * Nh ^ (1 / 2 : ℝ) * Th ^ (3 / 10 : ℝ) ≤ 8 * (ϖ / √cv) := by
    rw [mul_assoc]
    calc ϖ * (Nh ^ (1 / 2 : ℝ) * Th ^ (3 / 10 : ℝ)) ≤ ϖ * (8 / √cv) := mul_le_mul_of_nonneg_left hph hϖ
      _ = 8 * (ϖ / √cv) := by ring
  have hNh' : Nh ≤ 24 / (cv * e4) := by rw [le_div_iff₀ (mul_pos hcv he4)]; exact hNh24
  have hbh : b * Nh ≤ 24 * (b / (cv * e4)) := by
    calc b * Nh ≤ b * (24 / (cv * e4)) := mul_le_mul_of_nonneg_left hNh' hb
      _ = 24 * (b / (cv * e4)) := by ring
  refine ⟨hy1, hNh24, hTh5, ?_⟩
  linarith only [hΔs', hΔh1, hΔh, hϖh, hbh, ha, hϖc, hbc]

/-- **The fixed point, case (ii)** (S4 :1335-1340). Real-number form, with Lemma S4.25(a) in `hΔs`, `hΔh`. -/
theorem fixed_point_ii {κ cv a ϖ b ε Ns Δs Nh Th Δh y : ℝ} {nm : ℕ}
    (hκ0 : 0 < κ) (hκ1 : κ < 1) (hcv : 0 < cv) (hϖ : 0 ≤ ϖ) (hb : 0 ≤ b) (hε : 0 < ε)
    (hfit : epsFitII κ cv a ϖ b nm ≤ ε)
    (hNs0 : 0 ≤ Ns) (hNs : Ns * (cv * ε ^ (1 / 4 : ℝ)) ≤ 1)
    (hΔs : |Δs| ≤ a + ϖ * Ns ^ (1 / 2 : ℝ) + b * Ns)
    (hy : |Δs| ≤ κ * ε / 4 → cv * ε ^ (5 / 4 : ℝ) / 2 ≤ y)
    (hNh0 : 0 ≤ Nh) (hTh0 : 0 ≤ Th) (hi : Nh * y + Th ≤ ε + Δh)
    (hΔh : |Δh| ≤ a + ϖ * Nh ^ (1 / 2 : ℝ) + b * Nh) :
    cv * ε ^ (5 / 4 : ℝ) / 2 ≤ y ∧ Nh * (cv * ε ^ (1 / 4 : ℝ)) ≤ 12 ∧ Th ≤ 3 * ε ∧ |Δs| + Δh ≤ κ * ε / 4 := by
  simp only [epsFitII, max_le_iff] at hfit
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, -⟩ := hfit
  set e8 := ε ^ (1 / 8 : ℝ) with he8def
  have he8 : 0 < e8 := Real.rpow_pos_of_pos hε _
  have he4 : ε ^ (1 / 4 : ℝ) = e8 ^ 2 := rpow_quarter_eq_sq hε.le
  have h54 : ε ^ (5 / 4 : ℝ) = ε * e8 ^ 2 := by rw [rpow_five_quarters hε, he4]
  rw [he4] at hNs ⊢
  rw [h54] at hy ⊢
  have hκε : 0 < κ * ε := mul_pos hκ0 hε
  have hκεle : κ * ε ≤ ε := mul_le_of_le_one_left hε.le hκ1.le
  have hsc : 0 < √cv := Real.sqrt_pos.2 hcv
  have hcvsq : √cv ^ 2 = cv := Real.sq_sqrt hcv.le
  -- the first three terms
  have ha : a ≤ κ * ε / 24 := by
    rw [div_le_iff₀ hκ0] at h1; linarith only [h1]
  have h2' : 60 * ϖ / (κ * √cv) ≤ ε * e8 := by
    rw [← rpow_nine_eighths hε]
    exact le_rpow_of_rpow_le (by positivity) (by norm_num) (by norm_num) h2
  have hϖe : ϖ ≤ κ * √cv * (ε * e8) / 60 := by
    rw [div_le_iff₀ (mul_pos hκ0 hsc)] at h2'; linarith only [h2']
  have h3' : 156 * b / (κ * cv) ≤ ε * e8 ^ 2 := by
    rw [← h54]
    exact le_rpow_of_rpow_le (by positivity) (by norm_num) (by norm_num) h3
  have hbe : b ≤ κ * cv * (ε * e8 ^ 2) / 156 := by
    rw [div_le_iff₀ (mul_pos hκ0 hcv)] at h3'; linarith only [h3']
  -- the population fluctuation
  have hsNs : √Ns * (√cv * e8) ≤ 1 := by
    have := sqrt_mul_le_of_mul_le hNs0 hcv he8 hNs; rwa [Real.sqrt_one] at this
  have hϖs : ϖ * Ns ^ (1 / 2 : ℝ) ≤ κ * ε / 60 := by
    rw [rpow_half_eq_sqrt]
    calc ϖ * √Ns ≤ κ * √cv * (ε * e8) / 60 * √Ns := mul_le_mul_of_nonneg_right hϖe (Real.sqrt_nonneg _)
      _ = κ * ε / 60 * (√Ns * (√cv * e8)) := by ring
      _ ≤ κ * ε / 60 * 1 := mul_le_mul_of_nonneg_left hsNs (by positivity)
      _ = κ * ε / 60 := mul_one _
  have hbs : b * Ns ≤ κ * ε / 156 := by
    calc b * Ns ≤ κ * cv * (ε * e8 ^ 2) / 156 * Ns := mul_le_mul_of_nonneg_right hbe hNs0
      _ = κ * ε / 156 * (Ns * (cv * e8 ^ 2)) := by ring
      _ ≤ κ * ε / 156 * 1 := mul_le_mul_of_nonneg_left hNs (by positivity)
      _ = κ * ε / 156 := mul_one _
  have hΔs4 : |Δs| ≤ κ * ε / 4 := by linarith only [hΔs, hϖs, hbs, ha, hκε]
  -- `y ≥ c_V ε^{5/4}/2` and `b ≤ y/4`
  have hy1 := hy hΔs4
  have hX : 0 < cv * (ε * e8 ^ 2) := by positivity
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy1
  have hby : b ≤ y / 4 := by
    have : κ * (cv * (ε * e8 ^ 2)) ≤ cv * (ε * e8 ^ 2) := mul_le_of_le_one_left hX.le hκ1.le
    linarith only [this, hbe, hy1, hX]
  -- the fixed point
  have hϖ2 : ϖ ^ 2 / y ≤ ε := by
    rw [div_le_iff₀ hy0]
    have hsq : ϖ ^ 2 ≤ (κ * √cv * (ε * e8) / 60) ^ 2 := pow_le_pow_left₀ hϖ hϖe 2
    have hexp : (κ * √cv * (ε * e8) / 60) ^ 2 = κ ^ 2 / 1800 * (ε * (cv * (ε * e8 ^ 2) / 2)) := by
      rw [show (κ * √cv * (ε * e8) / 60) ^ 2 = κ ^ 2 * √cv ^ 2 * ε ^ 2 * e8 ^ 2 / 3600 by ring, hcvsq]; ring
    have hk2 : κ ^ 2 / 1800 ≤ 1 := by
      have : κ ^ 2 ≤ 1 := pow_le_one₀ hκ0.le hκ1.le
      linarith only [this]
    have hpos : 0 ≤ ε * (cv * (ε * e8 ^ 2) / 2) := by positivity
    calc ϖ ^ 2 ≤ κ ^ 2 / 1800 * (ε * (cv * (ε * e8 ^ 2) / 2)) := hexp ▸ hsq
      _ ≤ 1 * (ε * (cv * (ε * e8 ^ 2) / 2)) := mul_le_mul_of_nonneg_right hk2 hpos
      _ ≤ ε * y := by rw [one_mul]; exact mul_le_mul_of_nonneg_left hy1 hε.le
  have hamgm := amgm_sqrt (ϖ := ϖ) hNh0 hy0
  rw [← rpow_half_eq_sqrt] at hamgm
  have hbN : b * Nh ≤ y / 4 * Nh := mul_le_mul_of_nonneg_right hby hNh0
  have hΔh1 : Δh ≤ |Δh| := le_abs_self _
  have hfp : Nh * y / 2 + Th ≤ 3 * ε := by
    linarith only [hi, hΔh1, hΔh, hamgm, hbN, ha, hϖ2, hκεle, hε]
  have hNy0 : 0 ≤ Nh * y := mul_nonneg hNh0 hy0.le
  have hNy : Nh * y ≤ 6 * ε := by linarith only [hfp, hTh0]
  have hTh3 : Th ≤ 3 * ε := by linarith only [hfp, hNy0, hε]
  have hNh12 : Nh * (cv * e8 ^ 2) ≤ 12 := by
    have h1 : Nh * (cv * (ε * e8 ^ 2) / 2) ≤ Nh * y := mul_le_mul_of_nonneg_left hy1 hNh0
    have h2 : Nh * (cv * e8 ^ 2) * ε ≤ 12 * ε := by linarith only [h1, hNy]
    exact le_of_mul_le_mul_right h2 hε
  -- the fitted fluctuation
  have hsNh' : √Nh * (√cv * e8) ≤ √12 := sqrt_mul_le_of_mul_le hNh0 hcv he8 hNh12
  have hϖh : ϖ * Nh ^ (1 / 2 : ℝ) ≤ √12 * (κ * ε / 60) := by
    rw [rpow_half_eq_sqrt]
    calc ϖ * √Nh ≤ κ * √cv * (ε * e8) / 60 * √Nh := mul_le_mul_of_nonneg_right hϖe (Real.sqrt_nonneg _)
      _ = κ * ε / 60 * (√Nh * (√cv * e8)) := by ring
      _ ≤ κ * ε / 60 * √12 := mul_le_mul_of_nonneg_left hsNh' (by positivity)
      _ = √12 * (κ * ε / 60) := mul_comm _ _
  have hbh : b * Nh ≤ 12 * (κ * ε / 156) := by
    calc b * Nh ≤ κ * cv * (ε * e8 ^ 2) / 156 * Nh := mul_le_mul_of_nonneg_right hbe hNh0
      _ = κ * ε / 156 * (Nh * (cv * e8 ^ 2)) := by ring
      _ ≤ κ * ε / 156 * 12 := mul_le_mul_of_nonneg_left hNh12 (by positivity)
      _ = 12 * (κ * ε / 156) := mul_comm _ _
  have h12 : √12 * (κ * ε / 60) ≤ 4 * (κ * ε / 60) := mul_le_mul_of_nonneg_right sqrt_12_le (by positivity)
  refine ⟨hy1, hNh12, hTh3, ?_⟩
  linarith only [hΔs, hϖs, hbs, hΔh1, hΔh, hϖh, hbh, h12, ha]

end StatFormal.Wave31tu.RouteF
