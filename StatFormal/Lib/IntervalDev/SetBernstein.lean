import StatFormal.Lib.Bernstein.Bernstein

set_option linter.style.longLine false

/-!
# Bernstein's inequality for the empirical frequency of a set

For a probability `ν`, a measurable set `G` with `p = ν(G)`, `n ≥ 1` i.i.d. draws and `L ≥ 0`, the empirical frequency
`P̃(G) = (1/n)#{i : ω_i ∈ G}` (here `sampleMean (G.indicator 1) ω`) satisfies the one-sided bounds
`P(P̃(G) − p ≥ √(2pL/n) + L/(3n)) ≤ e^{−L}` and `P(p − P̃(G) ≥ √(2pL/n) + L/(3n)) ≤ e^{−L}`.

They are the certified one-sided Bernstein inequality (`StatFormal.Bernstein.bernstein`, Maurer–Pontil form) applied
to `1_G` and to `1_{Gᶜ} = 1 − 1_G`, at `δ = e^{−L}`, with the variance `p(1 − p) ≤ p` (the pattern of the certified
`Wave30h.reldev_bound` for half-lines, here for any measurable set).

## Main results

* `popMean_indicator`, `popVar_indicator`, `sampleMean_indicator_compl`;
* `prob_lower_dev_le`, `prob_upper_dev_le`.
-/

noncomputable section
open MeasureTheory Set Real

namespace StatFormal.IntervalDev

open StatFormal.Bernstein

variable {β : Type*} [MeasurableSpace β]

omit [MeasurableSpace β] in
theorem indicator_one_mem_Icc (G : Set β) (x : β) : G.indicator (1 : β → ℝ) x ∈ Icc (0 : ℝ) 1 := by
  by_cases h : x ∈ G <;> simp [h]

omit [MeasurableSpace β] in
theorem sampleMean_indicator_compl {n : ℕ} (hn : 0 < n) (G : Set β) (ω : Fin n → β) :
    sampleMean (Gᶜ.indicator (1 : β → ℝ)) ω = 1 - sampleMean (G.indicator 1) ω := by
  simp only [sampleMean]
  have h : ∀ i, Gᶜ.indicator (1 : β → ℝ) (ω i) = 1 - G.indicator 1 (ω i) := fun i => by
    by_cases hi : ω i ∈ G <;> simp [hi]
  simp_rw [h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have : (n : ℝ) ≠ 0 := by positivity
  field_simp

theorem popMean_indicator (ν : Measure β) {G : Set β} (hG : MeasurableSet G) :
    popMean ν (G.indicator 1) = ν.real G := by
  rw [popMean, integral_indicator_one hG]

theorem popVar_indicator (ν : Measure β) [IsProbabilityMeasure ν] {G : Set β} (hG : MeasurableSet G) :
    popVar ν (G.indicator 1) = ν.real G * (1 - ν.real G) := by
  rw [popVar, popMean_indicator ν hG]
  have e : (fun u => (G.indicator (1 : β → ℝ) u - ν.real G) ^ 2) =
      fun u => G.indicator (1 : β → ℝ) u * (1 - 2 * ν.real G) + ν.real G ^ 2 := by
    funext u; by_cases h : u ∈ G <;> simp [h] <;> ring
  have hint : Integrable (G.indicator (1 : β → ℝ)) ν := (integrable_const (1 : ℝ)).indicator hG
  rw [e, integral_add (hint.mul_const _) (integrable_const _), integral_mul_const,
    integral_indicator_one hG, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  ring

/-- **Lower deviation of an empirical frequency**: `P(p − P̃(G) ≥ √(2pL/n) + L/(3n)) ≤ e^{−L}`. -/
theorem prob_lower_dev_le (ν : Measure β) [IsProbabilityMeasure ν] {G : Set β} (hG : MeasurableSet G)
    {n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 ≤ L) :
    (Measure.pi fun _ : Fin n => ν).real
      {ω | √(2 * ν.real G * L / n) + L / (3 * n) ≤ ν.real G - sampleMean (G.indicator 1) ω} ≤ exp (-L) := by
  have hg : Measurable (G.indicator (1 : β → ℝ)) := measurable_const.indicator hG
  have hδ0 : 0 < exp (-L) := exp_pos _
  have hδ1 : exp (-L) ≤ 1 := exp_le_one_iff.2 (by linarith)
  have hlog : log (1 / exp (-L)) = L := by rw [one_div, ← exp_neg, neg_neg, log_exp]
  have hB := bernstein ν hg (indicator_one_mem_Icc G) hn hδ0 hδ1
  rw [hlog, popVar_indicator ν hG, popMean_indicator ν hG] at hB
  refine le_trans (measureReal_mono fun ω hω => ?_) hB
  simp only [mem_ofPred_eq] at hω ⊢
  have hp0 : 0 ≤ ν.real G := measureReal_nonneg
  have hp1 : ν.real G ≤ 1 := measureReal_le_one
  refine le_trans (add_le_add_left (Real.sqrt_le_sqrt ?_) _) hω
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  nlinarith [mul_nonneg (mul_nonneg hp0 hp0) hL]

/-- **Upper deviation of an empirical frequency**: `P(P̃(G) − p ≥ √(2pL/n) + L/(3n)) ≤ e^{−L}`. -/
theorem prob_upper_dev_le (ν : Measure β) [IsProbabilityMeasure ν] {G : Set β} (hG : MeasurableSet G)
    {n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 ≤ L) :
    (Measure.pi fun _ : Fin n => ν).real
      {ω | √(2 * ν.real G * L / n) + L / (3 * n) ≤ sampleMean (G.indicator 1) ω - ν.real G} ≤ exp (-L) := by
  have hg : Measurable (Gᶜ.indicator (1 : β → ℝ)) := measurable_const.indicator hG.compl
  have hδ0 : 0 < exp (-L) := exp_pos _
  have hδ1 : exp (-L) ≤ 1 := exp_le_one_iff.2 (by linarith)
  have hlog : log (1 / exp (-L)) = L := by rw [one_div, ← exp_neg, neg_neg, log_exp]
  have hB := bernstein ν hg (indicator_one_mem_Icc Gᶜ) hn hδ0 hδ1
  rw [hlog, popVar_indicator ν hG.compl, popMean_indicator ν hG.compl, measureReal_compl hG,
    probReal_univ] at hB
  simp_rw [sampleMean_indicator_compl hn] at hB
  refine le_trans (measureReal_mono fun ω hω => ?_) hB
  simp only [mem_ofPred_eq] at hω ⊢
  have hp0 : 0 ≤ ν.real G := measureReal_nonneg
  have hp1 : ν.real G ≤ 1 := measureReal_le_one
  have e : 1 - ν.real G - (1 - sampleMean (G.indicator 1) ω) = sampleMean (G.indicator 1) ω - ν.real G := by
    ring
  rw [e]
  refine le_trans (add_le_add_left (Real.sqrt_le_sqrt ?_) _) hω
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  nlinarith [mul_nonneg (mul_nonneg hp0 hp0) hL]

end StatFormal.IntervalDev
