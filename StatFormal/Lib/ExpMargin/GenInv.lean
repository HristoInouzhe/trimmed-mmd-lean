import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The generalized inverse of an exponential margin (library, untrusted)

For `ω : ℝ → ℝ` nondecreasing on `[0, a]` with `ω(ε) ≥ exp(−c′/ε)` on `(0, ε₀]`, `0 < ε₀ ≤ a`, `c′ > 0`, the generalized inverse
`ω^←(t) = sup{ε ∈ [0, a] : ω(ε) ≤ t}` (an `sSup` of a set bounded by `a`) is controlled by the margin (trimmed-mmd, proof of
Proposition S4.8 (ii): "every `ε ∈ [0, α⋆]` with `ω(ε) ≤ t` has `ε < ε₀`, and then, if `ε > 0`, `exp(−c′/ε) ≤ t`, that is,
`ε ≤ c′/log(1/t)`; so `ω^←(t) ≤ c′/log(1/t)`"):

* `sSup_le_of_le_exp`: `ω^←(t) ≤ x` whenever `x > 0`, `t ≤ exp(−c′/x)` and `t < ω(ε₀)`;
* `sSup_le_of_le_exp_of_lt`: the same with `x < ε₀` in place of `t < ω(ε₀)`;
* `sSup_le_div_log`: the printed form `ω^←(t) ≤ c′/log(1/t)` for `0 < t < min{1, ω(ε₀)}`;
* `exp_neg_div_div_log`: `exp(−c′/(c/log M)) = M^{−c′/c}` for `M > 0` (the threshold `c/log M` in terms of a power of `M`).
-/

set_option linter.style.longLine false

noncomputable section

namespace StatFormal.ExpMargin

open Set Real

/-- **The generalized inverse of an exponential margin, core form.** If `ω` is nondecreasing on `[0, a]`, `exp(−c′/e) ≤ ω(e)` on
`(0, ε₀]` with `0 < ε₀ ≤ a` and `c′ > 0`, then for `x > 0` and `t ≤ exp(−c′/x)`, `t < ω(ε₀)`:
`sup{e ∈ [0, a] : ω(e) ≤ t} ≤ x`. -/
theorem sSup_le_of_le_exp {ω : ℝ → ℝ} {a ε₀ c' x t : ℝ} (hmono : MonotoneOn ω (Icc 0 a)) (hε₀ : 0 < ε₀) (hε₀a : ε₀ ≤ a)
    (hc' : 0 < c') (hlow : ∀ e ∈ Ioc (0 : ℝ) ε₀, Real.exp (-c' / e) ≤ ω e) (hx : 0 < x) (ht : t ≤ Real.exp (-c' / x))
    (ht0 : t < ω ε₀) : sSup {e | e ∈ Icc (0 : ℝ) a ∧ ω e ≤ t} ≤ x := by
  refine Real.sSup_le (fun e he => ?_) hx.le
  obtain ⟨⟨he0, hea⟩, het⟩ := he
  refine le_of_not_gt fun hxe => ?_
  rcases le_or_gt e ε₀ with heε | heε
  · have h1 : Real.exp (-c' / e) ≤ Real.exp (-c' / x) := ((hlow e ⟨hx.trans hxe, heε⟩).trans het).trans ht
    rw [Real.exp_le_exp, neg_div, neg_div, neg_le_neg_iff] at h1
    have h2 : c' / e < c' / x := div_lt_div_of_pos_left hc' hx hxe
    linarith
  · have h1 : ω ε₀ ≤ ω e := hmono ⟨hε₀.le, hε₀a⟩ ⟨he0, hea⟩ heε.le
    linarith

/-- **The generalized inverse of an exponential margin**, with the threshold below `ε₀`: for `0 < x < ε₀` and `t ≤ exp(−c′/x)`,
`sup{e ∈ [0, a] : ω(e) ≤ t} ≤ x` (then `t < exp(−c′/ε₀) ≤ ω(ε₀)` automatically). -/
theorem sSup_le_of_le_exp_of_lt {ω : ℝ → ℝ} {a ε₀ c' x t : ℝ} (hmono : MonotoneOn ω (Icc 0 a)) (hε₀ : 0 < ε₀)
    (hε₀a : ε₀ ≤ a) (hc' : 0 < c') (hlow : ∀ e ∈ Ioc (0 : ℝ) ε₀, Real.exp (-c' / e) ≤ ω e) (hx : 0 < x) (hxε : x < ε₀)
    (ht : t ≤ Real.exp (-c' / x)) : sSup {e | e ∈ Icc (0 : ℝ) a ∧ ω e ≤ t} ≤ x := by
  refine sSup_le_of_le_exp hmono hε₀ hε₀a hc' hlow hx ht ?_
  have h1 : Real.exp (-c' / x) < Real.exp (-c' / ε₀) := by
    rw [Real.exp_lt_exp, neg_div, neg_div, neg_lt_neg_iff]
    exact div_lt_div_of_pos_left hc' hx hxε
  exact (ht.trans_lt h1).trans_le (hlow ε₀ ⟨hε₀, le_rfl⟩)

/-- **`ω^←(t) ≤ c′/log(1/t)`** (proof of Proposition S4.8 (ii) of the trimmed-mmd supplement), for `0 < t < 1` and `t < ω(ε₀)`. -/
theorem sSup_le_div_log {ω : ℝ → ℝ} {a ε₀ c' t : ℝ} (hmono : MonotoneOn ω (Icc 0 a)) (hε₀ : 0 < ε₀) (hε₀a : ε₀ ≤ a)
    (hc' : 0 < c') (hlow : ∀ e ∈ Ioc (0 : ℝ) ε₀, Real.exp (-c' / e) ≤ ω e) (ht0 : 0 < t) (ht1 : t < 1) (htω : t < ω ε₀) :
    sSup {e | e ∈ Icc (0 : ℝ) a ∧ ω e ≤ t} ≤ c' / Real.log (1 / t) := by
  have hL : 0 < Real.log (1 / t) := Real.log_pos (one_lt_one_div ht0 ht1)
  refine sSup_le_of_le_exp hmono hε₀ hε₀a hc' hlow (div_pos hc' hL) ?_ htω
  have hl0 : Real.log t ≠ 0 := (Real.log_neg ht0 ht1).ne
  have hc0 : c' ≠ 0 := hc'.ne'
  have h1 : -c' / (c' / Real.log (1 / t)) = Real.log t := by
    rw [one_div, Real.log_inv, div_div_eq_mul_div]
    field_simp
  rw [h1, Real.exp_log ht0]

/-- `exp(−c′/(c/log M)) = M^{−c′/c}` for `M > 0`: the threshold `x = c/log M` corresponds to `t = M^{−c′/c}`. -/
theorem exp_neg_div_div_log {c' c M : ℝ} (hM : 0 < M) :
    Real.exp (-c' / (c / Real.log M)) = M ^ (-(c' / c)) := by
  rw [Real.rpow_def_of_pos hM]
  congr 1
  rw [div_div_eq_mul_div]
  ring

end StatFormal.ExpMargin
