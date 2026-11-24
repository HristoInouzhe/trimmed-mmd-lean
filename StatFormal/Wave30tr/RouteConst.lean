import StatFormal.Wave30tr.RouteEvents

/-!
# Route: the constants of Theorem A (untrusted proof material)

* `ek_le`: `e_k = E|σ_1+⋯+σ_k|/k ≤ √k/k = k^{−1/2}` (Jensen, `radE_abs_sum_rsign_le`).
* `thmA_compare`, `thmA_compare_half`: `τ_A(α,δ) ≤ τ_A(α,δ/2) ≤ τ_{n,m}(α,δ)` for `D ∈ [0,2κ]`, from
  `√s ≤ n^{−1/2} + m^{−1/2}`, `e_k ≤ k^{−1/2}` and `D√(sL/2) ≤ κ√(2L')√s` for `L ≤ L' = log(4/δ)` (the NOTE's
  "Comparison" paragraph).
* `tauA_scale`: `τ_A(α,δ) = βτ_A(0,δ)`, hence nonnegative and nondecreasing on `[0,1)`.
-/

noncomputable section
open Real

namespace StatFormal.Wave30tr

open StatFormal.Concentration

theorem ek_le : Claims.ek_le := by
  intro k hk
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.2 (by omega)
  rw [ek_eq_radE]
  calc radE (fun σ : Fin k → Bool => |∑ i, rsign (σ i)|) / k ≤ √k / k :=
        div_le_div_of_nonneg_right radE_abs_sum_rsign_le hkpos.le
    _ = 1 / √k := by rw [Real.sqrt_div_self']

theorem ek_le_inv_sqrt {k : ℕ} (hk : 1 ≤ k) : ek k ≤ 1 / √(k : ℝ) := ek_le k hk

/-- `√(1/n + 1/m) ≤ 1/√n + 1/√m`. -/
theorem sqrt_sNM_le {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    √(StatFormal.Wave30tp.sNM n m) ≤ 1 / √(n : ℝ) + 1 / √(m : ℝ) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.2 (by omega)
  have ha : 0 < 1 / √(n : ℝ) := by positivity
  have hb : 0 < 1 / √(m : ℝ) := by positivity
  have hsq : StatFormal.Wave30tp.sNM n m ≤ (1 / √(n : ℝ) + 1 / √(m : ℝ)) ^ 2 := by
    have e1 : (1 / √(n : ℝ)) ^ 2 = 1 / n := by rw [div_pow, Real.sq_sqrt hnpos.le, one_pow]
    have e2 : (1 / √(m : ℝ)) ^ 2 = 1 / m := by rw [div_pow, Real.sq_sqrt hmpos.le, one_pow]
    unfold StatFormal.Wave30tp.sNM
    nlinarith [mul_pos ha hb]
  calc √(StatFormal.Wave30tp.sNM n m) ≤ √((1 / √(n : ℝ) + 1 / √(m : ℝ)) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = 1 / √(n : ℝ) + 1 / √(m : ℝ) := Real.sqrt_sq (by positivity)

/-- The comparison, for any `0 ≤ L ≤ L₄ = log(2/(δ/2))`. -/
theorem inner_le_tau {κ D α δ L : ℝ} {n m : ℕ} (hD0 : 0 ≤ D) (hD : D ≤ 2 * κ) (hα1 : α < 1)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hL0 : 0 ≤ L) (hL : L ≤ Real.log (2 / (δ / 2))) :
    1 / (1 - α) * (2 * κ * √(StatFormal.Wave30tp.sNM n m) + 2 * κ * (ek n + ek m) +
        D * √(StatFormal.Wave30tp.sNM n m * L / 2)) ≤ StatFormal.TrimmedMMD.tau κ α δ n m := by
  have hκ0 : 0 ≤ κ := by linarith
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.2 (by omega)
  have hβ : 0 ≤ 1 / (1 - α) := div_nonneg zero_le_one (by linarith)
  set L₄ := Real.log (2 / (δ / 2)) with hL₄
  have hL₄0 : 0 ≤ L₄ := hL0.trans hL
  set s := StatFormal.Wave30tp.sNM n m with hs
  have hs0 : 0 ≤ s := (StatFormal.Wave30tp.sNM_pos hn hm).le
  set a := 1 / √(n : ℝ) with ha
  set b := 1 / √(m : ℝ) with hb
  have hsab : √s ≤ a + b := sqrt_sNM_le hn hm
  have hen : ek n ≤ a := ek_le n hn
  have hem : ek m ≤ b := ek_le m hm
  have hDterm : D * √(s * L / 2) ≤ κ * (√(2 * L₄ / n) + √(2 * L₄ / m)) := by
    have h1 : D * √(s * L / 2) ≤ 2 * κ * √(s * L / 2) :=
      mul_le_mul_of_nonneg_right hD (Real.sqrt_nonneg _)
    have h2 : 2 * √(s * L / 2) = √(2 * L * s) := by
      rw [show 2 * L * s = 2 ^ 2 * (s * L / 2) by ring, Real.sqrt_mul (by norm_num),
        Real.sqrt_sq (by norm_num)]
    have h3 : √(2 * L * s) ≤ √(2 * L₄) * √s := by
      rw [← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have h4 : √(2 * L₄) * √s ≤ √(2 * L₄) * (a + b) :=
      mul_le_mul_of_nonneg_left hsab (Real.sqrt_nonneg _)
    have h5 : √(2 * L₄) * (a + b) = √(2 * L₄ / n) + √(2 * L₄ / m) := by
      rw [Real.sqrt_div (by positivity), Real.sqrt_div (by positivity), ha, hb]; ring
    calc D * √(s * L / 2) ≤ 2 * κ * √(s * L / 2) := h1
      _ = κ * √(2 * L * s) := by rw [← h2]; ring
      _ ≤ κ * (√(2 * L₄) * (a + b)) :=
          mul_le_mul_of_nonneg_left (h3.trans h4) hκ0
      _ = κ * (√(2 * L₄ / n) + √(2 * L₄ / m)) := by rw [h5]
  have hinner : 2 * κ * √s + 2 * κ * (ek n + ek m) + D * √(s * L / 2) ≤
      κ * (4 / √(n : ℝ) + √(2 * L₄ / n)) + κ * (4 / √(m : ℝ) + √(2 * L₄ / m)) := by
    have e1 : 2 * κ * √s ≤ 2 * κ * (a + b) := mul_le_mul_of_nonneg_left hsab (by positivity)
    have e2 : 2 * κ * (ek n + ek m) ≤ 2 * κ * (a + b) :=
      mul_le_mul_of_nonneg_left (add_le_add hen hem) (by positivity)
    have e3 : κ * (4 / √(n : ℝ) + √(2 * L₄ / n)) + κ * (4 / √(m : ℝ) + √(2 * L₄ / m)) =
        4 * κ * (a + b) + κ * (√(2 * L₄ / n) + √(2 * L₄ / m)) := by rw [ha, hb]; ring
    rw [e3]
    linarith
  calc 1 / (1 - α) * (2 * κ * √s + 2 * κ * (ek n + ek m) + D * √(s * L / 2))
      ≤ 1 / (1 - α) * (κ * (4 / √(n : ℝ) + √(2 * L₄ / n)) + κ * (4 / √(m : ℝ) + √(2 * L₄ / m))) :=
        mul_le_mul_of_nonneg_left hinner hβ
    _ = StatFormal.TrimmedMMD.tau κ α δ n m := by
        unfold StatFormal.TrimmedMMD.tau StatFormal.TrimmedMMD.rn; rw [hL₄]; ring

theorem thmA_compare : Claims.thmA_compare := by
  intro κ D α δ n m hD0 hD _ hα1 hδ0 hδ1 hn hm
  have hL0 := StatFormal.Wave30tp.log_inv_nonneg hδ0 hδ1
  have hL : Real.log (1 / δ) ≤ Real.log (2 / (δ / 2)) :=
    Real.log_le_log (by positivity) (by rw [div_div_eq_mul_div]; gcongr; norm_num)
  exact inner_le_tau hD0 hD hα1 hn hm hL0 hL

theorem thmA_compare_half : Claims.thmA_compare_half := by
  intro κ D α δ n m hD0 hD _ hα1 hδ0 hδ1 hn hm
  have hL0 : 0 ≤ Real.log (1 / (δ / 2)) :=
    StatFormal.Wave30tp.log_inv_nonneg (by positivity) (by linarith)
  have hL : Real.log (1 / (δ / 2)) ≤ Real.log (2 / (δ / 2)) :=
    Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) (by positivity))
  exact inner_le_tau hD0 hD hα1 hn hm hL0 hL

theorem tauA_zero_nonneg {κ D δ : ℝ} {n m : ℕ} (hκ : 0 ≤ κ) (hD : 0 ≤ D) :
    0 ≤ tauA κ D 0 δ n m := by
  have := ek_nonneg n; have := ek_nonneg m
  unfold tauA; positivity

theorem tauA_scale : Claims.tauA_scale := by
  intro κ D δ n m hκ hD _ _ _ _
  have h0 := tauA_zero_nonneg (δ := δ) (n := n) (m := m) hκ hD
  refine ⟨fun α _ => tauA_eq_mul, ?_, ?_⟩
  · intro α hα α' hα' hle
    simp only
    rw [tauA_eq_mul, tauA_eq_mul (α := α')]
    exact mul_le_mul_of_nonneg_right (StatFormal.Wave30tp.beta_mono hα'.2 hle) h0
  · intro α hα
    rw [tauA_eq_mul]
    have : 0 < 1 - α := by linarith [hα.2]
    exact mul_nonneg (by positivity) h0

end StatFormal.Wave30tr
