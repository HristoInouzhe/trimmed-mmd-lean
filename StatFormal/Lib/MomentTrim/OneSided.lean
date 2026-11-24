import StatFormal.Lib.MomentTrim.Pair
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IntermediateValue

/-!
# One-sided explicit trimmings of a density pair vanishing to order `r` (library, untrusted)

If `p − q ≥ ℓ′(x − x₀)^r` a.e. on `(x₀, x₀ + r₀)` and `q − p ≥ ℓ′(x₀ − x)^r` a.e. on `(x₀ − r₀, x₀)`, then for
`0 < ε ≤ ℓ′r₀^{r+1}/(r+1)` and `W = {(r+1)ε/ℓ′}^{1/(r+1)}` the continuous nondecreasing maps `w ↦ ∫_{x₀}^{x₀+w} (p − q)₊` and
`w ↦ ∫_{x₀−w}^{x₀} (q − p)₊` reach `ε` at some `w_P, w_Q ≤ W` (intermediate value theorem; at `w = W` they are at least
`ℓ′W^{r+1}/(r+1) = ε`). The trimmings `P′ = min(p, q) + (p − q)₊ 1_{(x₀, x₀+w_P]}`, `Q′ = min(p, q) + (q − p)₊ 1_{(x₀−w_Q, x₀]}`
form a trimming pair at scale `W` with `M = 2ε`, `N = 1` and `e = ε` (the proof of Proposition S4.14 of the trimmed-mmd
supplement, S4 :768-776).

* `exists_one_sided_widths`: the widths `w_P, w_Q ∈ [0, W]`;
* `exists_one_sided_pair`: the trimming pair.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set

namespace StatFormal.MomentTrim

/-- `∫_{x₀}^{x₀+w} ℓ′(x − x₀)^r dx = ℓ′w^{r+1}/(r+1)` for `w ≥ 0`, `r > 0`. -/
lemma integral_rpow_right (ℓ' r x₀ w : ℝ) (hr : 0 < r) :
    ∫ x in x₀..(x₀ + w), ℓ' * (x - x₀) ^ r = ℓ' * (w ^ (r + 1) / (r + 1)) := by
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_right (fun x => x ^ r),
    integral_rpow (Or.inl (by linarith)), sub_self, add_sub_cancel_left, Real.zero_rpow (by linarith : (0 : ℝ) < r + 1).ne',
    sub_zero]

/-- `∫_{x₀−w}^{x₀} ℓ′(x₀ − x)^r dx = ℓ′w^{r+1}/(r+1)` for `w ≥ 0`, `r > 0`. -/
lemma integral_rpow_left (ℓ' r x₀ w : ℝ) (hr : 0 < r) :
    ∫ x in (x₀ - w)..x₀, ℓ' * (x₀ - x) ^ r = ℓ' * (w ^ (r + 1) / (r + 1)) := by
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left (fun x => x ^ r),
    integral_rpow (Or.inl (by linarith)), sub_self, sub_sub_cancel, Real.zero_rpow (by linarith : (0 : ℝ) < r + 1).ne',
    sub_zero]

/-- The width `W = {(r+1)ε/ℓ′}^{1/(r+1)}`: `W > 0`, `ℓ′W^{r+1}/(r+1) = ε` and `W ≤ r₀` when `ε ≤ ℓ′r₀^{r+1}/(r+1)`. -/
lemma width_facts {ℓ' r r₀ ε : ℝ} (hℓ : 0 < ℓ') (hr : 0 < r) (hr₀ : 0 < r₀) (hε : 0 < ε)
    (hεr : ε ≤ ℓ' * r₀ ^ (r + 1) / (r + 1)) :
    0 < ((r + 1) * ε / ℓ') ^ (1 / (r + 1)) ∧
      ℓ' * ((((r + 1) * ε / ℓ') ^ (1 / (r + 1))) ^ (r + 1) / (r + 1)) = ε ∧
      ((r + 1) * ε / ℓ') ^ (1 / (r + 1)) ≤ r₀ := by
  have hr1 : 0 < r + 1 := by linarith
  have ha : 0 < (r + 1) * ε / ℓ' := by positivity
  refine ⟨Real.rpow_pos_of_pos ha _, ?_, ?_⟩
  · rw [one_div, Real.rpow_inv_rpow ha.le hr1.ne']
    field_simp
  · have h1 : (r + 1) * ε / ℓ' ≤ r₀ ^ (r + 1) := by
      rw [div_le_iff₀ hℓ]
      rw [le_div_iff₀ hr1] at hεr
      linarith
    calc ((r + 1) * ε / ℓ') ^ (1 / (r + 1)) ≤ (r₀ ^ (r + 1)) ^ (1 / (r + 1)) :=
          Real.rpow_le_rpow ha.le h1 (by positivity)
      _ = r₀ := by rw [one_div, Real.rpow_rpow_inv hr₀.le hr1.ne']

/-- **The widths.** Under the one-sided lower bounds, `∫_{x₀}^{x₀+w_P} (p − q)₊ = ε = ∫_{x₀−w_Q}^{x₀} (q − p)₊` for some
`w_P, w_Q ∈ [0, W]`. -/
theorem exists_one_sided_widths {p q : ℝ → ℝ} (hpi : Integrable p) (hqi : Integrable q) {x₀ ℓ' r r₀ ε : ℝ}
    (hℓ : 0 < ℓ') (hr : 0 < r) (hr₀ : 0 < r₀)
    (hR : ∀ᵐ x ∂volume, x ∈ Ioo x₀ (x₀ + r₀) → ℓ' * (x - x₀) ^ r ≤ p x - q x)
    (hL : ∀ᵐ x ∂volume, x ∈ Ioo (x₀ - r₀) x₀ → ℓ' * (x₀ - x) ^ r ≤ q x - p x)
    (hε : 0 < ε) (hεr : ε ≤ ℓ' * r₀ ^ (r + 1) / (r + 1)) :
    ∃ wP wQ : ℝ, wP ∈ Icc 0 (((r + 1) * ε / ℓ') ^ (1 / (r + 1))) ∧ wQ ∈ Icc 0 (((r + 1) * ε / ℓ') ^ (1 / (r + 1))) ∧
      ∫ x in x₀..(x₀ + wP), max (p x - q x) 0 = ε ∧ ∫ x in (x₀ - wQ)..x₀, max (q x - p x) 0 = ε := by
  obtain ⟨hW0, hWε, hWr⟩ := width_facts hℓ hr hr₀ hε hεr
  set W := ((r + 1) * ε / ℓ') ^ (1 / (r + 1)) with hW
  have hdP : Integrable (fun x => max (p x - q x) 0) := (hpi.sub hqi).pos_part
  have hdQ : Integrable (fun x => max (q x - p x) 0) := (hqi.sub hpi).pos_part
  have hcP : Continuous fun w => ∫ x in x₀..(x₀ + w), max (p x - q x) 0 :=
    (intervalIntegral.continuous_primitive (fun a b => hdP.intervalIntegrable) x₀).comp (continuous_const.add continuous_id)
  have hcQ : Continuous fun w => ∫ x in (x₀ - w)..x₀, max (q x - p x) 0 := by
    have : (fun w => ∫ x in (x₀ - w)..x₀, max (q x - p x) 0) = fun w => -∫ x in x₀..(x₀ - w), max (q x - p x) 0 := by
      funext w; rw [intervalIntegral.integral_symm]
    rw [this]
    exact ((intervalIntegral.continuous_primitive (fun a b => hdQ.intervalIntegrable) x₀).comp
      (continuous_const.sub continuous_id)).neg
  have hne : ∀ a : ℝ, ∀ᵐ x ∂volume, x ≠ a := fun a => compl_mem_ae_iff.mpr (measure_singleton a)
  -- the right side reaches `ε` at `W`
  have hPW : ε ≤ ∫ x in x₀..(x₀ + W), max (p x - q x) 0 := by
    rw [← hWε, ← integral_rpow_right ℓ' r x₀ W hr]
    refine intervalIntegral.integral_mono_ae_restrict (by linarith)
      ((continuousOn_const.mul ((by fun_prop : Continuous fun x : ℝ => x - x₀).continuousOn.rpow_const
        fun _ _ => Or.inr hr.le)).intervalIntegrable_of_Icc (by linarith)) hdP.intervalIntegrable ?_
    refine (ae_restrict_iff' measurableSet_Icc).mpr ?_
    filter_upwards [hR, hne x₀, hne (x₀ + W)] with x hx h1 h2 hxI
    have hlt1 : x₀ < x := lt_of_le_of_ne hxI.1 (Ne.symm h1)
    have hlt2 : x < x₀ + W := lt_of_le_of_ne hxI.2 h2
    exact (hx ⟨hlt1, by linarith⟩).trans (le_max_left _ _)
  have hQW : ε ≤ ∫ x in (x₀ - W)..x₀, max (q x - p x) 0 := by
    rw [← hWε, ← integral_rpow_left ℓ' r x₀ W hr]
    refine intervalIntegral.integral_mono_ae_restrict (by linarith)
      ((continuousOn_const.mul ((by fun_prop : Continuous fun x : ℝ => x₀ - x).continuousOn.rpow_const
        fun _ _ => Or.inr hr.le)).intervalIntegrable_of_Icc (by linarith)) hdQ.intervalIntegrable ?_
    refine (ae_restrict_iff' measurableSet_Icc).mpr ?_
    filter_upwards [hL, hne x₀, hne (x₀ - W)] with x hx h1 h2 hxI
    have hlt1 : x < x₀ := lt_of_le_of_ne hxI.2 h1
    have hlt2 : x₀ - W < x := lt_of_le_of_ne hxI.1 (Ne.symm h2)
    exact (hx ⟨by linarith, hlt1⟩).trans (le_max_left _ _)
  obtain ⟨wP, hwP, hwPε⟩ := intermediate_value_Icc hW0.le hcP.continuousOn
    (show ε ∈ Icc (∫ x in x₀..(x₀ + 0), max (p x - q x) 0) (∫ x in x₀..(x₀ + W), max (p x - q x) 0) by
      rw [add_zero, intervalIntegral.integral_same]; exact ⟨hε.le, hPW⟩)
  obtain ⟨wQ, hwQ, hwQε⟩ := intermediate_value_Icc hW0.le hcQ.continuousOn
    (show ε ∈ Icc (∫ x in (x₀ - 0)..x₀, max (q x - p x) 0) (∫ x in (x₀ - W)..x₀, max (q x - p x) 0) by
      rw [sub_zero, intervalIntegral.integral_same]; exact ⟨hε.le, hQW⟩)
  exact ⟨wP, wQ, hwP, hwQ, hwPε, hwQε⟩

/-- **The one-sided trimming pair** (Proposition S4.14): at scale `W`, with `M = 2ε`, `N = 1`, `e = ε`. -/
theorem exists_one_sided_pair {p q : ℝ → ℝ} (hpm : Measurable p) (hqm : Measurable q) (hp0 : ∀ x, 0 ≤ p x)
    (hq0 : ∀ x, 0 ≤ q x) (hpi : Integrable p) (hqi : Integrable q) {x₀ ℓ' r r₀ ε : ℝ}
    (hℓ : 0 < ℓ') (hr : 0 < r) (hr₀ : 0 < r₀)
    (hR : ∀ᵐ x ∂volume, x ∈ Ioo x₀ (x₀ + r₀) → ℓ' * (x - x₀) ^ r ≤ p x - q x)
    (hL : ∀ᵐ x ∂volume, x ∈ Ioo (x₀ - r₀) x₀ → ℓ' * (x₀ - x) ^ r ≤ q x - p x)
    (hε : 0 < ε) (hεr : ε ≤ ℓ' * r₀ ^ (r + 1) / (r + 1)) :
    ∃ fP fQ hp hm : ℝ → ℝ,
      IsTrimmingPair p q x₀ (((r + 1) * ε / ℓ') ^ (1 / (r + 1))) (2 * ε) 1 fP fQ hp hm ε := by
  obtain ⟨wP, wQ, hwP, hwQ, hP, hQ⟩ := exists_one_sided_widths hpi hqi hℓ hr hr₀ hR hL hε hεr
  set dP : ℝ → ℝ := fun x => max (p x - q x) 0 with hdPdef
  set dQ : ℝ → ℝ := fun x => max (q x - p x) 0 with hdQdef
  have hdPi : Integrable dP := (hpi.sub hqi).pos_part
  have hdQi : Integrable dQ := (hqi.sub hpi).pos_part
  set aP : ℝ → ℝ := (Ioc x₀ (x₀ + wP)).indicator dP with haP
  set aQ : ℝ → ℝ := (Ioc (x₀ - wQ) x₀).indicator dQ with haQ
  have haP0 : ∀ x, 0 ≤ aP x := fun x => indicator_nonneg (fun y _ => le_max_right _ _) x
  have haQ0 : ∀ x, 0 ≤ aQ x := fun x => indicator_nonneg (fun y _ => le_max_right _ _) x
  have haPle : ∀ x, aP x ≤ dP x := fun x => indicator_le_self' (fun y _ => le_max_right _ _) x
  have haQle : ∀ x, aQ x ≤ dQ x := fun x => indicator_le_self' (fun y _ => le_max_right _ _) x
  have haPi : Integrable aP := hdPi.indicator measurableSet_Ioc
  have haQi : Integrable aQ := hdQi.indicator measurableSet_Ioc
  have haPm : Measurable aP := ((hpm.sub hqm).max measurable_const).indicator measurableSet_Ioc
  have haQm : Measurable aQ := ((hqm.sub hpm).max measurable_const).indicator measurableSet_Ioc
  have hIP : ∫ x, aP x = ε := by
    rw [haP, integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le (by linarith [hwP.1]), hP]
  have hIQ : ∫ x, aQ x = ε := by
    rw [haQ, integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le (by linarith [hwQ.1]), hQ]
  have hmni : Integrable (fun x => min (p x) (q x)) :=
    hpi.mono' (hpm.min hqm).aestronglyMeasurable (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hp0 x) (hq0 x))]; exact min_le_left _ _)
  refine ⟨fun x => min (p x) (q x) + aP x, fun x => min (p x) (q x) + aQ x, aP, aQ, ?_⟩
  refine
    { meas_fP := (hpm.min hqm).add haPm
      meas_fQ := (hpm.min hqm).add haQm
      meas_hp := haPm
      meas_hm := haQm
      fP_nonneg := fun x => add_nonneg (le_min (hp0 x) (hq0 x)) (haP0 x)
      fQ_nonneg := fun x => add_nonneg (le_min (hp0 x) (hq0 x)) (haQ0 x)
      hp_nonneg := haP0
      hm_nonneg := haQ0
      fP_le := fun x => ?_
      fQ_le := fun x => ?_
      add_eq := fun x => by ring
      support := fun x hx => ⟨?_, ?_⟩
      int_hp := haPi
      int_hm := haQi
      mass_h := by rw [hIP, hIQ]; linarith
      moments := fun j hj => ?_
      mass_fP := by rw [integral_add hmni haPi, hIP]
      mass_fQ := by rw [integral_add hmni haQi, hIQ] }
  · beta_reduce
    have := haPle x
    simp only [hdPdef] at this
    rcases le_total (p x) (q x) with h | h
    · rw [max_eq_right (by linarith)] at this; linarith [min_le_left (p x) (q x)]
    · rw [max_eq_left (by linarith)] at this; rw [min_eq_right h]; linarith
  · beta_reduce
    have := haQle x
    simp only [hdQdef] at this
    rcases le_total (q x) (p x) with h | h
    · rw [max_eq_right (by linarith)] at this; linarith [min_le_right (p x) (q x)]
    · rw [max_eq_left (by linarith)] at this; rw [min_eq_left h]; linarith
  · refine indicator_of_notMem (fun h => hx ⟨by linarith [h.1, hwP.1, hwP.2], by linarith [h.2, hwP.2]⟩) _
  · refine indicator_of_notMem (fun h => hx ⟨by linarith [h.1, hwQ.2], by linarith [h.2, hwQ.1, hwQ.2]⟩) _
  · have hj0 : j = 0 := by omega
    subst hj0
    simp only [pow_zero, one_mul, hIP, hIQ]

end StatFormal.MomentTrim
