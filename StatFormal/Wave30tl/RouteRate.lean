import StatFormal.Wave30tl.RouteCrossing

/-!
# Wave 30tl — "The rate condition cannot be dropped" (untrusted proof route)

`log(2/(δ/2)) = log 4 + n` at `δ = e^{−n}`, so `τ_{n,n}(α, e^{−n}) = 2κ/(1−α)·(4/√n + √(2(log 4 + n)/n))`; the chain is elementary.
`D̂ ≤ 2κ ≤ τ(0)` puts `0` in the crossing set, so `α̂ = 0`; then `{|α̂ − α*| ≤ e}` is empty for `e < α*`.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace StatFormal.Wave30tl

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional

theorem log_four_div_exp (n : ℕ) : Real.log (4 / Real.exp (-(n : ℝ))) = Real.log 4 + n := by
  rw [Real.log_div (by norm_num) (Real.exp_pos _).ne', Real.log_exp]; ring

theorem log_two_div_half_exp (n : ℕ) : Real.log (2 / (Real.exp (-(n : ℝ)) / 2)) = Real.log 4 + n := by
  have : (2 : ℝ) / (Real.exp (-(n : ℝ)) / 2) = 4 / Real.exp (-(n : ℝ)) := by
    have := (Real.exp_pos (-(n : ℝ))).ne'
    field_simp; norm_num
  rw [this, log_four_div_exp]

theorem tau_exp_eq (κ α : ℝ) (n : ℕ) :
    tau κ α (Real.exp (-(n : ℝ))) n n =
      2 * (κ / (1 - α) * (4 / √(n : ℝ) + √(2 * (Real.log 4 + n) / n))) := by
  unfold tau rn
  rw [log_two_div_half_exp]; ring

theorem one_le_sqrt_rate {n : ℕ} (hn : 1 ≤ n) : √2 < √(2 * (Real.log 4 + n) / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hl : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine Real.sqrt_lt_sqrt (by norm_num) ?_
  rw [lt_div_iff₀ hn']
  nlinarith

theorem one_lt_sqrt_two' : (1 : ℝ) < √2 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

theorem chain_le {κ α : ℝ} (hκ : 0 ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1) {n : ℕ} :
    2 * κ * √(2 * (Real.log 4 + n) / n) ≤ tau κ α (Real.exp (-(n : ℝ))) n n := by
  rw [tau_exp_eq]
  have hc : κ ≤ κ / (1 - α) := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  have hs := Real.sqrt_nonneg (2 * (Real.log 4 + n) / n)
  have h4 : 0 ≤ 4 / √(n : ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hc hs, mul_nonneg (hκ.trans hc) h4]

theorem two_kappa_le_tau_exp {κ α : ℝ} (hκ : 0 ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1) {n : ℕ} (hn : 1 ≤ n) :
    2 * κ ≤ tau κ α (Real.exp (-(n : ℝ))) n n := by
  have h1 := chain_le hκ hα0 hα1 (n := n)
  have h2 : 1 ≤ √(2 * (Real.log 4 + n) / n) := (one_lt_sqrt_two'.trans (one_le_sqrt_rate hn)).le
  nlinarith

theorem ratecond_schedule : Claims.ratecond_schedule := by
  have hf : ∀ n : ℕ, 1 ≤ n → Real.log (1 / Real.exp (-(n : ℝ))) / (min n n : ℕ) = 1 := by
    intro n hn
    have hn' : (n : ℝ) ≠ 0 := by
      have : (0 : ℝ) < n := by exact_mod_cast hn
      exact this.ne'
    rw [min_self, one_div, Real.log_inv, Real.log_exp, neg_neg, div_self hn']
  refine ⟨Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop, fun n hn => ?_, ?_⟩
  · refine ⟨Real.exp_pos _, Real.exp_lt_one_iff.2 ?_, hf n hn⟩
    have : (0 : ℝ) < n := by exact_mod_cast hn
    linarith
  · intro h0
    have h1 : Tendsto (fun n : ℕ => Real.log (1 / Real.exp (-(n : ℝ))) / (min n n : ℕ)) atTop (𝓝 1) :=
      tendsto_const_nhds.congr' (eventually_atTop.2 ⟨1, fun n hn => (hf n hn).symm⟩)
    have := tendsto_nhds_unique h0 h1
    norm_num at this

theorem ratecond_chain : Claims.ratecond_chain := by
  intro κ α n hκ hn hα0 hα1
  rw [log_four_div_exp]
  refine ⟨chain_le hκ.le hα0 hα1, ?_, ?_⟩
  · have := one_le_sqrt_rate hn
    nlinarith
  · nlinarith [one_lt_sqrt_two']

theorem alphaHat_exp_zero {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {φ : 𝒳 → H} {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ) {n : ℕ} (hn : 1 ≤ n) (x y : Fin n → 𝒳) :
    alphaHat (Demp φ x y) (fun α => tau κ α (Real.exp (-(n : ℝ))) n n) = 0 := by
  have hκ0 : 0 ≤ κ := kappa_nonneg_of hκ (x ⟨0, hn⟩)
  have h0 : (0 : ℝ) ∈ crossSet (Demp φ x y) (fun α => tau κ α (Real.exp (-(n : ℝ))) n n) :=
    ⟨⟨le_rfl, one_pos⟩, (Demp_le_two_kappa hκ hn hn x y 0 ⟨le_rfl, one_pos⟩).trans
      (two_kappa_le_tau_exp hκ0 le_rfl one_pos hn)⟩
  exact le_antisymm (csInf_le (crossSet_bddBelow _ _) h0) (alphaHat_nonneg ⟨0, h0⟩)

theorem ratecond_zero : Claims.ratecond_zero := by
  intro 𝒳 H _ _ _ _ _ φ κ n hφ hκ hn x y
  exact ⟨Demp_le_two_kappa hκ hn hn x y, alphaHat_exp_zero hκ hn x y⟩

theorem ratecond_noconv : Claims.ratecond_noconv := by
  intro 𝒳 H _ _ _ _ _ P Q _ _ φ κ hφ hκ htv e he het
  rintro ⟨E, -, hE, hlim⟩
  have hzero : ∀ n, 1 ≤ n → ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin n => Q)) (E n) = 0 := by
    intro n hn
    have : E n = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun z hz => ?_
      have h := hE n hz
      simp only [mem_setOf_eq, alphaHat_exp_zero hκ hn z.1 z.2, zero_sub, abs_neg] at h
      rw [abs_of_nonneg (StatFormal.Distances.tvDist_nonneg P Q)] at h
      linarith
    rw [this, measure_empty]
  have h0 : Tendsto (fun n => ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin n => Q)) (E n))
      atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (eventually_atTop.2 ⟨1, fun n hn => (hzero n hn).symm⟩)
  have := tendsto_nhds_unique h0 hlim
  exact zero_ne_one this

end StatFormal.Wave30tl
