import StatFormal.Archive.Wave30az.Statements
import StatFormal.Archive.ICL.Cond.Proofs

/-!
# Route — ICL `lem:cond-osc` (the i.i.d. risk) and `lem:cond-metric` (fixed floor, norm form, ball)

* `cond_osc_iid`: centre the loss at `B_L/2` (`Σ_J (p_J − q_J) = 0`), then the certified i.i.d. TV conjunct of
  `cond_osc_ii` and `tanh x ≤ x`.
* `cond_metric_fixed`: the softmax ratio bound (both directions) survives a common floor `ε ∈ [0,1)`.
* `cond_metric_norm`: the certified `cond_metric` with `v = ‖θ − θ'‖ ≥ ‖τ − τ'‖_∞`, `|ε − ε'| ≤ ‖θ − θ'‖`.
* `cond_metric_ball`: coordinatewise `|τ_l − τ_max/2| ≤ τ_max/2`, `|ε − ½| ≤ ½ − ε_min`.
-/

set_option linter.style.longLine false

noncomputable section
open Finset

namespace StatFormal.Wave30az

open StatFormal.ICL.Cond (iidLaw wRetr tv1)

theorem cond_osc_iid : Claims.cond_osc_iid := by
  intro n M w w' Δ BL L hM hMn hw hw' hws hws' hΔ hL
  have hn : 0 < n := by omega
  have hBL : 0 ≤ BL := (hL fun _ => ⟨0, hn⟩).1.trans (hL fun _ => ⟨0, hn⟩).2
  have hii := StatFormal.ICL.Cond.cond_osc_ii n M w w' Δ BL (fun _ => 0) hM hMn hw hw' hws hws' hΔ
    (fun _ => ⟨le_rfl, hBL⟩)
  obtain ⟨-, h2, -, h4⟩ := hii
  refine ⟨?_, h4⟩
  set p := iidLaw w M
  set q := iidLaw w' M
  have hsum0 : ∑ J, (p J - q J) = 0 := by
    rw [sum_sub_distrib, StatFormal.ICL.Cond.iidLaw_sum w M hws, StatFormal.ICL.Cond.iidLaw_sum w' M hws',
      sub_self]
  have heq : StatFormal.Wave12c.Giid w M L - StatFormal.Wave12c.Giid w' M L =
      ∑ J, (p J - q J) * (L J - BL / 2) := by
    have : ∑ J, (p J - q J) * (L J - BL / 2) =
        ∑ J, (p J * L J - q J * L J) - BL / 2 * ∑ J, (p J - q J) := by
      rw [mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun J _ => ?_
      ring
    rw [this, hsum0, mul_zero, sub_zero, sum_sub_distrib]
    rfl
  rw [heq]
  calc |∑ J, (p J - q J) * (L J - BL / 2)|
      ≤ ∑ J, |(p J - q J) * (L J - BL / 2)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ J, |p J - q J| * (BL / 2) := by
        apply sum_le_sum
        intro J _
        rw [abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        rw [abs_le]
        constructor <;> linarith [(hL J).1, (hL J).2]
    _ = BL * tv1 univ p q := by
        unfold tv1
        rw [← sum_mul]
        ring
    _ ≤ BL * Real.tanh (M * Δ / 2) := mul_le_mul_of_nonneg_left h2 hBL

/-- The fixed-floor core: a common floor `ε ∈ [0,1)` preserves the two-sided softmax ratio bound. -/
lemma fixed_core {n : ℕ} (j : Fin n) (g g' : Fin n → ℝ) (ε μ a : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hμ : 0 ≤ μ)
    (hg : ∀ k, a ≤ g k - g' k ∧ g k - g' k ≤ a + μ) :
    |Real.log ((1 - ε) * (Real.exp (g j) / ∑ k, Real.exp (g k)) + ε / n) -
      Real.log ((1 - ε) * (Real.exp (g' j) / ∑ k, Real.exp (g' k)) + ε / n)| ≤ μ := by
  have hN : (0 : ℝ) < n := Nat.cast_pos.mpr (Fin.pos j)
  set σ := Real.exp (g j) / ∑ k, Real.exp (g k) with hσ_def
  set σ' := Real.exp (g' j) / ∑ k, Real.exp (g' k) with hσ'_def
  have hσ : 0 < σ := div_pos (Real.exp_pos _) (sum_pos (fun k _ => Real.exp_pos _) ⟨j, mem_univ j⟩)
  have hσ' : 0 < σ' :=
    div_pos (Real.exp_pos _) (sum_pos (fun k _ => Real.exp_pos _) ⟨j, mem_univ j⟩)
  have hs1 : σ ≤ Real.exp μ * σ' := StatFormal.ICL.Cond.softmax_ratio g g' a μ hg j
  have hs2 : σ' ≤ Real.exp μ * σ :=
    StatFormal.ICL.Cond.softmax_ratio g' g (-a - μ) μ
      (fun k => ⟨by linarith [(hg k).2], by linarith [(hg k).1]⟩) j
  have hc : 0 ≤ ε / n := div_nonneg hε0 hN.le
  have hE : 1 ≤ Real.exp μ := Real.one_le_exp hμ
  have hw : ∀ r : ℝ, 0 < r → 0 < (1 - ε) * r + ε / n := fun r hr => by
    have : 0 < (1 - ε) * r := mul_pos (by linarith) hr
    linarith
  have hmul : ∀ r r' : ℝ, 0 < r' → r ≤ Real.exp μ * r' →
      (1 - ε) * r + ε / n ≤ Real.exp μ * ((1 - ε) * r' + ε / n) := by
    intro r r' hr' h
    have f1 := mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ 1 - ε)
    have f2 := mul_le_mul_of_nonneg_right hE hc
    nlinarith
  rw [abs_sub_le_iff]
  exact ⟨StatFormal.ICL.Cond.log_sub_le_of_le_exp_mul (hw σ hσ) (hw σ' hσ') (hmul σ σ' hσ' hs1),
    StatFormal.ICL.Cond.log_sub_le_of_le_exp_mul (hw σ' hσ') (hw σ hσ) (hmul σ' σ hσ hs2)⟩

theorem cond_metric_fixed : Claims.cond_metric_fixed := by
  intro n d xs x diam v ε τ τ' s s' j hdiam hv hv0 hε0 hε1
  have hN : ∀ k, 0 ≤ ∑ l, (x l - xs k l) ^ 2 := fun k => sum_nonneg fun l _ => sq_nonneg _
  refine ⟨?_, ?_⟩
  · unfold wRetr
    refine fixed_core j (fun k => -(1 / 2) * ∑ l, τ l * (x l - xs k l) ^ 2)
      (fun k => -(1 / 2) * ∑ l, τ' l * (x l - xs k l) ^ 2) ε (diam ^ 2 * v)
      (-(diam ^ 2 * v) / 2) hε0 hε1 (mul_nonneg (sq_nonneg _) hv0) ?_
    intro k
    have e : -(1 / 2) * ∑ l, τ l * (x l - xs k l) ^ 2 - -(1 / 2) * ∑ l, τ' l * (x l - xs k l) ^ 2 =
        -(1 / 2) * ∑ l, (τ l - τ' l) * (x l - xs k l) ^ 2 := by
      rw [← mul_sub, ← sum_sub_distrib]
      congr 1
      refine sum_congr rfl fun l _ => ?_
      ring
    have hb : |∑ l, (τ l - τ' l) * (x l - xs k l) ^ 2| ≤ diam ^ 2 * v := by
      calc |∑ l, (τ l - τ' l) * (x l - xs k l) ^ 2| ≤ ∑ l, |(τ l - τ' l) * (x l - xs k l) ^ 2| :=
            abs_sum_le_sum_abs _ _
        _ ≤ ∑ l, v * (x l - xs k l) ^ 2 := by
            refine sum_le_sum fun l _ => ?_
            rw [abs_mul, abs_of_nonneg (sq_nonneg (x l - xs k l))]
            exact mul_le_mul_of_nonneg_right (hv l) (sq_nonneg _)
        _ = v * ∑ l, (x l - xs k l) ^ 2 := by rw [mul_sum]
        _ ≤ v * diam ^ 2 := mul_le_mul_of_nonneg_left (hdiam k) hv0
        _ = diam ^ 2 * v := mul_comm _ _
    rw [e]
    have := abs_le.1 hb
    constructor <;> linarith [this.1, this.2]
  · unfold wRetr
    have e : ∀ k, -(1 / 2) * ∑ l, s * (x l - xs k l) ^ 2 - -(1 / 2) * ∑ l, s' * (x l - xs k l) ^ 2 =
        (1 / 2) * ((s' - s) * ∑ l, (x l - xs k l) ^ 2) := by
      intro k
      rw [← mul_sum, ← mul_sum]
      ring
    have hμ : 0 ≤ (1 / 2) * diam ^ 2 * |s - s'| := by positivity
    rcases le_total s s' with hss | hss
    · refine fixed_core j (fun k => -(1 / 2) * ∑ l, s * (x l - xs k l) ^ 2)
        (fun k => -(1 / 2) * ∑ l, s' * (x l - xs k l) ^ 2) ε
        ((1 / 2) * diam ^ 2 * |s - s'|) 0 hε0 hε1 hμ ?_
      intro k
      rw [e k, abs_of_nonpos (by linarith : s - s' ≤ 0)]
      have := mul_le_mul_of_nonneg_left (hdiam k) (by linarith : (0 : ℝ) ≤ s' - s)
      have := mul_nonneg (by linarith : (0 : ℝ) ≤ s' - s) (hN k)
      constructor <;> nlinarith
    · refine fixed_core j (fun k => -(1 / 2) * ∑ l, s * (x l - xs k l) ^ 2)
        (fun k => -(1 / 2) * ∑ l, s' * (x l - xs k l) ^ 2) ε
        ((1 / 2) * diam ^ 2 * |s - s'|) (-((1 / 2) * diam ^ 2 * |s - s'|)) hε0 hε1 hμ ?_
      intro k
      rw [e k, abs_of_nonneg (by linarith : 0 ≤ s - s')]
      have := mul_le_mul_of_nonpos_left (hdiam k) (by linarith : s' - s ≤ 0)
      have := mul_nonpos_of_nonpos_of_nonneg (by linarith : s' - s ≤ 0) (hN k)
      constructor <;> nlinarith

theorem cond_metric_norm : Claims.cond_metric_norm := by
  intro n d xs x diam εmin τ τ' ε ε' j hεmin hεmin2 hdiam hτ hτ' h1 h2 h3 h4
  set N := Real.sqrt (∑ l, (τ l - τ' l) ^ 2 + (ε - ε') ^ 2) with hNdef
  have hS : 0 ≤ ∑ l, (τ l - τ' l) ^ 2 := sum_nonneg fun l _ => sq_nonneg _
  have hτN : ∀ l, |τ l - τ' l| ≤ N := by
    intro l
    rw [← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    have := single_le_sum (f := fun l => (τ l - τ' l) ^ 2) (fun l _ => sq_nonneg _) (mem_univ l)
    nlinarith [sq_nonneg (ε - ε')]
  have hεN : |ε - ε'| ≤ N := by
    rw [← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    linarith
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  have hm := StatFormal.ICL.Cond.cond_metric n d xs x diam εmin N τ τ' ε ε' j hεmin hεmin2 hdiam hτ hτ' hτN hN0
    h1 h2 h3 h4
  calc _ ≤ diam ^ 2 * N + |ε - ε'| / εmin := hm
    _ ≤ diam ^ 2 * N + N / εmin := by gcongr
    _ = (diam ^ 2 + 1 / εmin) * N := by ring

theorem cond_metric_ball : Claims.cond_metric_ball := by
  intro d τmax εmin τ ε hτmax hεmin hεmin2 hτ h1 h2
  have hl : ∀ l, (τ l - τmax / 2) ^ 2 ≤ (τmax / 2) ^ 2 := by
    intro l
    have := hτ l
    nlinarith [this.1, this.2]
  have hs : ∑ l, (τ l - τmax / 2) ^ 2 ≤ d * (τmax / 2) ^ 2 := by
    calc ∑ l, (τ l - τmax / 2) ^ 2 ≤ ∑ _l : Fin d, (τmax / 2) ^ 2 := sum_le_sum fun l _ => hl l
      _ = d * (τmax / 2) ^ 2 := by simp
  have he : (ε - 1 / 2) ^ 2 ≤ ((1 - 2 * εmin) / 2) ^ 2 := by nlinarith
  refine ⟨?_, ?_⟩
  · have h4 : (1 / 2 : ℝ) = Real.sqrt (1 / 4) := by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h4, ← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    nlinarith
  · gcongr
    nlinarith

end StatFormal.Wave30az
