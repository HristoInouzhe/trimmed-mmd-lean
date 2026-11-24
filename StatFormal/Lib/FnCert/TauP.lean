import StatFormal.Wave30tp.Statements
import StatFormal.Wave30tr.Proofs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Prod

set_option linter.style.longLine false

/-!
# Closed forms of the analytic thresholds `τ^P` and `τ^A` (library)

Library component (untrusted). Facts about the closed-form threshold `Wave30tp.tauP` of Theorem P
(`v√s + D√(s log(1/δ)/2)` at `α = 0`, `T₁ + ρ̄T₂` for `α ≠ 0`, `s = 1/n + 1/m`) and `Wave30tr.tauA` of Theorem A:

* `tauP_jump_lower`, `tauP_zero_lt_jump`: for `α ∈ (0,1)`, `τ^P(α) ≥ v√s + D√(s log(6/δ)/2)`, which is `> τ^P(0)` when `D > 0`
  (the logarithm `log(6/δ)` replaces `log(1/δ)`): the jump at `0+`;
* `exists_tauP_ge`: `τ^P(α) ≥ D` for some `α ∈ [1/2, 1)` (`β = (1−α)⁻¹` large), so `τ^P(α) → ∞` as `α → 1` in the sense needed;
* `tendsto_sNM`, `tendsto_cNM`, `tendsto_ek`, `tendsto_tauP`, `tendsto_tauA`: as `n, m → ∞` (the product filter), `s, c, e_n → 0`, and
  `τ^P(α), τ^A(α, δ) → 0` at every fixed `α ∈ [0,1)` and `δ ∈ (0,1)`.
-/

noncomputable section
open Filter Topology Set

namespace StatFormal.FnCert

open StatFormal.Wave30tp

/-- `s = 1/n + 1/m > 0` for `n, m ≥ 1`. -/
theorem sNM_pos {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) : 0 < sNM n m := by
  unfold sNM
  have : (0 : ℝ) < n := by exact_mod_cast hn
  have : (0 : ℝ) < m := by exact_mod_cast hm
  positivity

/-- `c = max(1/n, 1/m) ≥ 0`. -/
theorem cNM_nonneg (n m : ℕ) : 0 ≤ cNM n m := by
  unfold cNM
  exact le_max_of_le_left (by positivity)

/-- `T₂ ≥ 0` for `α ≤ 1`, `δ ∈ (0, 6]`. -/
theorem T2_nonneg {α δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 6) (n m : ℕ) : 0 ≤ T2 α δ n m := by
  unfold T2
  have hL : 0 ≤ Real.log (6 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  exact add_nonneg (Real.sqrt_nonneg _) (div_nonneg (mul_nonneg (cNM_nonneg n m) hL) (by norm_num))

/-- **The jump at `0+`, lower side**: for `α ∈ (0,1)`, `τ^P(α) ≥ v√s + D√(s log(6/δ)/2)` (`β = (1−α)⁻¹ ≥ 1`, `ρ̄T₂ ≥ 0`). -/
theorem tauP_jump_lower {D v ρbar α δ : ℝ} (hD : 0 ≤ D) (hv : 0 ≤ v) (hρ : 0 ≤ ρbar) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hα0 : 0 < α) (hα1 : α < 1) (n m : ℕ) :
    v * √(sNM n m) + D * √(sNM n m * Real.log (6 / δ) / 2) ≤ tauP D v ρbar α δ n m := by
  have hs : 0 ≤ sNM n m := by unfold sNM; positivity
  unfold tauP
  rw [if_neg hα0.ne']
  have hβ : 1 ≤ 1 / (1 - α) := by rw [le_div_iff₀ (by linarith)]; linarith
  have h1 : v * √(sNM n m) ≤ √(1 / (1 - α) * v ^ 2 * sNM n m) := by
    have e : v * √(sNM n m) = √(v ^ 2 * sNM n m) := by
      rw [Real.sqrt_mul (sq_nonneg v), Real.sqrt_sq hv]
    rw [e]
    refine Real.sqrt_le_sqrt ?_
    have : 0 ≤ v ^ 2 * sNM n m := mul_nonneg (sq_nonneg v) hs
    nlinarith
  have h2 : D * √(sNM n m * Real.log (6 / δ) / 2) ≤ 1 / (1 - α) * D * √(sNM n m * Real.log (6 / δ) / 2) := by
    have : 0 ≤ D * √(sNM n m * Real.log (6 / δ) / 2) := mul_nonneg hD (Real.sqrt_nonneg _)
    rw [mul_assoc]
    nlinarith
  have h3 : 0 ≤ ρbar * T2 α δ n m := mul_nonneg hρ (T2_nonneg hδ0 (by linarith) n m)
  unfold T1
  linarith

/-- **The jump at `0+`**: `τ^P(0) < v√s + D√(s log(6/δ)/2)` when `D > 0` and `n, m ≥ 1`. -/
theorem tauP_zero_lt_jump {D v ρbar δ : ℝ} (hD : 0 < D) (hδ0 : 0 < δ) (hδ1 : δ < 1) {n m : ℕ} (hn : 1 ≤ n)
    (hm : 1 ≤ m) :
    tauP D v ρbar 0 δ n m < v * √(sNM n m) + D * √(sNM n m * Real.log (6 / δ) / 2) := by
  unfold tauP
  rw [if_pos rfl]
  have hs := sNM_pos hn hm
  have hL1 : 0 < Real.log (1 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  have hlt : Real.log (1 / δ) < Real.log (6 / δ) :=
    Real.log_lt_log (by positivity) (by rw [div_lt_div_iff_of_pos_right hδ0]; norm_num)
  have hsq : √(sNM n m * Real.log (1 / δ) / 2) < √(sNM n m * Real.log (6 / δ) / 2) :=
    Real.sqrt_lt_sqrt (by positivity) (by nlinarith)
  nlinarith

/-- `τ^P(α) ≥ D` at some `α ∈ [1/2, 1)` (`α = 1 − min(a, 1/2)`, `a = √(s log(6/δ)/2)`, so `β a ≥ 1`). -/
theorem exists_tauP_ge {D v ρbar δ : ℝ} (hD : 0 ≤ D) (hv : 0 ≤ v) (hρ : 0 ≤ ρbar) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    ∃ α ∈ Ico (1 / 2 : ℝ) 1, D ≤ tauP D v ρbar α δ n m := by
  have hs := sNM_pos hn hm
  have hL6 : 0 < Real.log (6 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  set a := √(sNM n m * Real.log (6 / δ) / 2) with ha
  have ha0 : 0 < a := Real.sqrt_pos.2 (by positivity)
  set e := min a (1 / 2) with he
  have he0 : 0 < e := lt_min ha0 (by norm_num)
  have he1 : e ≤ 1 / 2 := min_le_right _ _
  have hea : e ≤ a := min_le_left _ _
  refine ⟨1 - e, ⟨by linarith, by linarith⟩, ?_⟩
  have hα0 : 0 < 1 - e := by linarith
  have hα1 : 1 - e < 1 := by linarith
  have hT := tauP_jump_lower hD hv hρ hδ0 hδ1 hα0 hα1 n m
  unfold tauP
  rw [if_neg hα0.ne']
  unfold T1
  have hβ : 1 / (1 - (1 - e)) = 1 / e := by ring_nf
  rw [hβ]
  have hβa : 1 ≤ 1 / e * a := by rw [one_div, inv_mul_eq_div, le_div_iff₀ he0]; linarith
  have hDle : D ≤ 1 / e * D * a := by
    have : 1 / e * D * a = D * (1 / e * a) := by ring
    rw [this]; nlinarith
  have h3 : 0 ≤ ρbar * T2 (1 - e) δ n m := mul_nonneg hρ (T2_nonneg hδ0 (by linarith) n m)
  have h1 : 0 ≤ √(1 / e * v ^ 2 * sNM n m) := Real.sqrt_nonneg _
  rw [← ha]
  linarith

/-! ### Limits as `n, m → ∞` -/

theorem tendsto_inv_nat_fst : Tendsto (fun p : ℕ × ℕ => 1 / (p.1 : ℝ)) (atTop ×ˢ atTop) (𝓝 0) :=
  (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp tendsto_fst

theorem tendsto_inv_nat_snd : Tendsto (fun p : ℕ × ℕ => 1 / (p.2 : ℝ)) (atTop ×ˢ atTop) (𝓝 0) :=
  (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp tendsto_snd

/-- `s = 1/n + 1/m → 0`. -/
theorem tendsto_sNM : Tendsto (fun p : ℕ × ℕ => sNM p.1 p.2) (atTop ×ˢ atTop) (𝓝 0) := by
  have h := tendsto_inv_nat_fst.add tendsto_inv_nat_snd
  rw [add_zero] at h
  exact h

/-- `c = max(1/n, 1/m) → 0`. -/
theorem tendsto_cNM : Tendsto (fun p : ℕ × ℕ => cNM p.1 p.2) (atTop ×ˢ atTop) (𝓝 0) := by
  have h := tendsto_inv_nat_fst.max tendsto_inv_nat_snd
  rw [max_self] at h
  exact h

/-- `√(a s) → 0` for a constant `a`. -/
theorem tendsto_sqrt_mul_sNM (a b : ℝ) :
    Tendsto (fun p : ℕ × ℕ => √(a * sNM p.1 p.2 * b)) (atTop ×ˢ atTop) (𝓝 0) := by
  have h := ((tendsto_sNM.const_mul a).mul_const b).sqrt
  simpa using h

/-- `e_k ≥ 0`. -/
theorem ek_nonneg (k : ℕ) : 0 ≤ StatFormal.Wave30tr.ek k := by
  unfold StatFormal.Wave30tr.ek
  refine div_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => abs_nonneg _)) (Nat.cast_nonneg k)

/-- `e_k → 0` (from the certified `e_k ≤ k^{−1/2}`). -/
theorem tendsto_ek : Tendsto StatFormal.Wave30tr.ek atTop (𝓝 0) := by
  have hup : Tendsto (fun k : ℕ => √(1 / (k : ℝ))) atTop (𝓝 0) := by
    have := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).sqrt
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup (Eventually.of_forall ek_nonneg) ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  have h := StatFormal.Wave30tr.ek_le k hk
  rw [Real.sqrt_div' 1 (Nat.cast_nonneg k), Real.sqrt_one] at *
  exact h

/-- `τ^P(α) → 0` as `n, m → ∞`, at every fixed `α ∈ [0,1)`, `δ > 0`. -/
theorem tendsto_tauP (D v ρbar α δ : ℝ) :
    Tendsto (fun p : ℕ × ℕ => tauP D v ρbar α δ p.1 p.2) (atTop ×ˢ atTop) (𝓝 0) := by
  by_cases hα : α = 0
  · simp only [tauP, hα, if_true]
    have h1 := (tendsto_sNM.sqrt).const_mul v
    have h2 := (tendsto_sqrt_mul_sNM 1 (Real.log (1 / δ) / 2)).const_mul D
    have h := h1.add h2
    simp only [Real.sqrt_zero, mul_zero, add_zero] at h
    refine h.congr fun p => ?_
    congr 3
    ring
  · simp only [tauP, hα, if_false]
    have h1 := tendsto_sqrt_mul_sNM (1 / (1 - α) * v ^ 2) 1
    have h2 := (tendsto_sqrt_mul_sNM 1 (Real.log (6 / δ) / 2)).const_mul (1 / (1 - α) * D)
    have h3 := tendsto_sqrt_mul_sNM (2 * (1 / (1 - α) - 1)) (Real.log (6 / δ))
    have h4 := (tendsto_cNM.mul_const (Real.log (6 / δ))).div_const 3
    have h := h1.add (h2.add ((h3.add h4).const_mul ρbar))
    simp only [mul_zero, zero_mul, zero_div, add_zero] at h
    refine h.congr fun p => ?_
    unfold T1 T2
    simp only [mul_one, one_mul]
    ring_nf

/-- `τ^A(α, δ) → 0` as `n, m → ∞`, at every fixed `α` and `δ`. -/
theorem tendsto_tauA (κ D α δ : ℝ) :
    Tendsto (fun p : ℕ × ℕ => StatFormal.Wave30tr.tauA κ D α δ p.1 p.2) (atTop ×ˢ atTop) (𝓝 0) := by
  have he : Tendsto (fun p : ℕ × ℕ => StatFormal.Wave30tr.ek p.1 + StatFormal.Wave30tr.ek p.2) (atTop ×ˢ atTop) (𝓝 0) := by
    have := (tendsto_ek.comp tendsto_fst).add (tendsto_ek.comp tendsto_snd)
    simpa using this
  have h1 := (tendsto_sNM.sqrt).const_mul (2 * κ)
  have h2 := he.const_mul (2 * κ)
  have h3 := (tendsto_sqrt_mul_sNM 1 (Real.log (1 / δ) / 2)).const_mul D
  have h := ((h1.add h2).add h3).const_mul (1 / (1 - α))
  simp only [Real.sqrt_zero, mul_zero, add_zero] at h
  refine h.congr fun p => ?_
  unfold StatFormal.Wave30tr.tauA
  simp only [one_mul]
  ring_nf

end StatFormal.FnCert
