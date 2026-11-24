import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The Laplace kernel as a Green function: the test-function identity and the discrete second difference

Library component (trimmed-mmd, Proposition 5.10 (iii), the printed step "`(1 − σ²∂²_x)e^{−|x|/σ} = 2σδ₀` in the sense of
distributions"). Untrusted library code. No distribution theory is used.

## Main results

* `exp_abs_second_diff_le`, `exp_abs_second_diff_eq`: for `s ≥ 0`, `e^{−|u+s|} + e^{−|u−s|} ≤ (e^{s} + e^{−s})e^{−|u|}`, with
  equality when `s ≤ |u|` (the discrete second difference of the profile);
* `laplace_second_diff_le`, `laplace_second_diff_eq`: the same for `k(x,y) = e^{−|x−y|/σ}`:
  `k(x+h,y) + k(x−h,y) − 2k(x,y) ≤ 2(cosh(h/σ) − 1)k(x,y)`, with equality when `|x − y| ≥ h`;
* `laplace_green_identity`: for `σ > 0` and every `C²` function `ψ` with compact support,
  `∫ e^{−|x|/σ}(ψ(x) − σ²ψ″(x)) dx = 2σψ(0)` (the fundamental theorem of calculus on the two half-lines with the
  antiderivatives `−σe^{−x/σ}(ψ + σψ′)` and `σe^{x/σ}(ψ − σψ′)`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Real

namespace StatFormal.ExcessRamp

/-! ### The discrete second difference -/

/-- Equality in the discrete second difference of the profile `e^{−|u|}` when `0 ≤ s ≤ |u|`:
`e^{−|u+s|} + e^{−|u−s|} = (e^{s} + e^{−s})e^{−|u|}`. -/
theorem exp_abs_second_diff_eq {u s : ℝ} (hs : 0 ≤ s) (hsu : s ≤ |u|) :
    exp (-|u + s|) + exp (-|u - s|) = (exp s + exp (-s)) * exp (-|u|) := by
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu] at hsu
    have e1 : exp (-|u + s|) = exp (-u) * exp (-s) := by
      rw [abs_of_nonneg (by linarith : 0 ≤ u + s), ← exp_add]; ring_nf
    have e2 : exp (-|u - s|) = exp (-u) * exp s := by
      rw [abs_of_nonneg (by linarith : 0 ≤ u - s), ← exp_add]; ring_nf
    have e3 : exp (-|u|) = exp (-u) := by rw [abs_of_nonneg hu]
    rw [e1, e2, e3]; ring
  · rw [abs_of_nonpos hu] at hsu
    have e1 : exp (-|u + s|) = exp u * exp s := by
      rw [abs_of_nonpos (by linarith : u + s ≤ 0), neg_neg, exp_add]
    have e2 : exp (-|u - s|) = exp u * exp (-s) := by
      rw [abs_of_nonpos (by linarith : u - s ≤ 0), neg_neg, ← exp_add]; ring_nf
    have e3 : exp (-|u|) = exp u := by rw [abs_of_nonpos hu, neg_neg]
    rw [e1, e2, e3]; ring

/-- **The discrete second difference of the profile `e^{−|u|}`**: `e^{−|u+s|} + e^{−|u−s|} ≤ (e^{s} + e^{−s})e^{−|u|}` for
`s ≥ 0`. -/
theorem exp_abs_second_diff_le (u : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    exp (-|u + s|) + exp (-|u - s|) ≤ (exp s + exp (-s)) * exp (-|u|) := by
  rcases le_total s |u| with hsu | hsu
  · exact (exp_abs_second_diff_eq hs hsu).le
  have h1 : 0 ≤ u + s := by linarith [neg_abs_le u]
  have h2 : u - s ≤ 0 := by linarith [le_abs_self u]
  rw [abs_of_nonneg h1, abs_of_nonpos h2, neg_neg]
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu]
    have e1 : exp (-(u + s)) = exp (-s) * exp (-u) := by rw [← exp_add]; ring_nf
    have e2 : exp (u - s) ≤ exp s * exp (-u) := by
      rw [← exp_add]; exact exp_le_exp.2 (by linarith)
    nlinarith
  · rw [abs_of_nonpos hu, neg_neg]
    have e1 : exp (u - s) = exp (-s) * exp u := by rw [← exp_add]; ring_nf
    have e2 : exp (-(u + s)) ≤ exp s * exp u := by
      rw [← exp_add]; exact exp_le_exp.2 (by linarith)
    nlinarith

/-- The rescaling `−|x ± h − y|/σ = −|(x−y)/σ ± h/σ|`. -/
lemma neg_abs_div_add {σ : ℝ} (hσ : 0 < σ) (x y h : ℝ) : -|x + h - y| / σ = -|(x - y) / σ + h / σ| := by
  rw [← add_div, abs_div, abs_of_pos hσ, show x - y + h = x + h - y by ring, neg_div]

lemma neg_abs_div_sub {σ : ℝ} (hσ : 0 < σ) (x y h : ℝ) : -|x - h - y| / σ = -|(x - y) / σ - h / σ| := by
  rw [← sub_div, abs_div, abs_of_pos hσ, show x - y - h = x - h - y by ring, neg_div]

lemma neg_abs_div {σ : ℝ} (hσ : 0 < σ) (x y : ℝ) : -|x - y| / σ = -|(x - y) / σ| := by
  rw [abs_div, abs_of_pos hσ, neg_div]

/-- **The discrete second difference of the Laplace kernel**:
`k(x+h,y) + k(x−h,y) − 2k(x,y) ≤ 2(cosh(h/σ) − 1)k(x,y)` for `k(x,y) = e^{−|x−y|/σ}` and `h ≥ 0`. -/
theorem laplace_second_diff_le {σ : ℝ} (hσ : 0 < σ) (x y : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    exp (-|x + h - y| / σ) + exp (-|x - h - y| / σ) - 2 * exp (-|x - y| / σ) ≤
      2 * (cosh (h / σ) - 1) * exp (-|x - y| / σ) := by
  rw [neg_abs_div_add hσ, neg_abs_div_sub hσ, neg_abs_div hσ, cosh_eq]
  have := exp_abs_second_diff_le ((x - y) / σ) (div_nonneg hh hσ.le)
  linarith

/-- Equality in `laplace_second_diff_le` when `|x − y| ≥ h`. -/
theorem laplace_second_diff_eq {σ : ℝ} (hσ : 0 < σ) (x y : ℝ) {h : ℝ} (hh : 0 ≤ h) (hxy : h ≤ |x - y|) :
    exp (-|x + h - y| / σ) + exp (-|x - h - y| / σ) - 2 * exp (-|x - y| / σ) =
      2 * (cosh (h / σ) - 1) * exp (-|x - y| / σ) := by
  rw [neg_abs_div_add hσ, neg_abs_div_sub hσ, neg_abs_div hσ, cosh_eq]
  have hsu : h / σ ≤ |(x - y) / σ| := by
    rw [abs_div, abs_of_pos hσ]; exact div_le_div_of_nonneg_right hxy hσ.le
  have := exp_abs_second_diff_eq (div_nonneg hh hσ.le) hsu
  linarith

/-! ### The test-function identity -/

/-- The antiderivative on `[0, ∞)`: `d/dx[−σe^{−x/σ}(ψ + σψ′)] = e^{−x/σ}(ψ − σ²ψ″)`. -/
lemma hasDerivAt_green_right {σ : ℝ} (hσ : 0 < σ) {ψ : ℝ → ℝ} (h1 : Differentiable ℝ ψ)
    (h2 : Differentiable ℝ (deriv ψ)) (x : ℝ) :
    HasDerivAt (fun x => -σ * (exp (-x / σ) * (ψ x + σ * deriv ψ x)))
      (exp (-x / σ) * (ψ x - σ ^ 2 * deriv (deriv ψ) x)) x := by
  have he : HasDerivAt (fun x => exp (-x / σ)) (exp (-x / σ) * (-1 / σ)) x := by
    have := ((hasDerivAt_id x).neg.div_const σ).exp
    simpa using this
  have hp : HasDerivAt (fun x => ψ x + σ * deriv ψ x) (deriv ψ x + σ * deriv (deriv ψ) x) x :=
    (h1 x).hasDerivAt.add ((h2 x).hasDerivAt.const_mul σ)
  have := (he.mul hp).const_mul (-σ)
  convert this using 1
  field_simp
  ring

/-- The antiderivative on `(−∞, 0]`: `d/dx[σe^{x/σ}(ψ − σψ′)] = e^{x/σ}(ψ − σ²ψ″)`. -/
lemma hasDerivAt_green_left {σ : ℝ} (hσ : 0 < σ) {ψ : ℝ → ℝ} (h1 : Differentiable ℝ ψ)
    (h2 : Differentiable ℝ (deriv ψ)) (x : ℝ) :
    HasDerivAt (fun x => σ * (exp (x / σ) * (ψ x - σ * deriv ψ x)))
      (exp (x / σ) * (ψ x - σ ^ 2 * deriv (deriv ψ) x)) x := by
  have he : HasDerivAt (fun x => exp (x / σ)) (exp (x / σ) * (1 / σ)) x := by
    have := ((hasDerivAt_id x).div_const σ).exp
    simpa using this
  have hp : HasDerivAt (fun x => ψ x - σ * deriv ψ x) (deriv ψ x - σ * deriv (deriv ψ) x) x :=
    (h1 x).hasDerivAt.sub ((h2 x).hasDerivAt.const_mul σ)
  have := (he.mul hp).const_mul σ
  convert this using 1
  field_simp
  ring

/-- **The Laplace kernel is the Green function of `1 − σ²∂²`**, tested against `C²` functions with compact support:
`∫ e^{−|x|/σ}(ψ(x) − σ²ψ″(x)) dx = 2σψ(0)`. -/
theorem laplace_green_identity {σ : ℝ} (hσ : 0 < σ) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ) :
    ∫ x, exp (-|x| / σ) * (ψ x - σ ^ 2 * deriv (deriv ψ) x) = 2 * σ * ψ 0 := by
  have h1 : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have h2 : Differentiable ℝ (deriv ψ) := hψ.differentiable_deriv_two
  have h2' : ContDiff ℝ (1 + 1) ψ := by norm_num; exact hψ
  have h3 : Continuous (deriv (deriv ψ)) := (ContDiff.deriv' h2').continuous_deriv_one
  set I : ℝ → ℝ := fun x => exp (-|x| / σ) * (ψ x - σ ^ 2 * deriv (deriv ψ) x) with hI
  have hIc : Continuous I :=
    ((continuous_abs.neg.div_const σ).rexp).mul (h1.continuous.sub (continuous_const.mul h3))
  -- a radius outside of which everything vanishes
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  set R' := |R| + 1 with hR'
  have hR'pos : 0 < R' := by positivity
  have hout : ∀ x, R' ≤ |x| → ψ x = 0 ∧ deriv ψ x = 0 ∧ deriv (deriv ψ) x = 0 := by
    intro x hx
    have hnot : x ∉ tsupport ψ := fun hmem => by
      have := hR hmem
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
      linarith [le_abs_self R]
    refine ⟨image_eq_zero_of_notMem_tsupport hnot,
      image_eq_zero_of_notMem_tsupport fun hm => hnot (tsupport_deriv_subset hm),
      image_eq_zero_of_notMem_tsupport fun hm => hnot (tsupport_deriv_subset (tsupport_deriv_subset hm))⟩
  have hIout : ∀ x, x ∉ Ioc (-R') R' → I x = 0 := by
    intro x hx
    have hx' : R' ≤ |x| := by
      simp only [mem_Ioc, not_and_or, not_lt, not_le] at hx
      rcases hx with hx | hx
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    obtain ⟨e1, -, e3⟩ := hout x hx'
    simp only [hI, e1, e3, mul_zero, sub_zero]
  have hwhole : ∫ x, I x = ∫ x in (-R')..R', I x := by
    rw [intervalIntegral.integral_of_le (by linarith), setIntegral_eq_integral_of_forall_compl_eq_zero hIout]
  rw [hwhole, ← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hIc.intervalIntegrable _ _)
    (hIc.intervalIntegrable _ _)]
  -- the right half-line
  have hright : ∫ x in (0 : ℝ)..R', I x = σ * (ψ 0 + σ * deriv ψ 0) := by
    have hcongr : ∫ x in (0 : ℝ)..R', I x = ∫ x in (0 : ℝ)..R', exp (-x / σ) * (ψ x - σ ^ 2 * deriv (deriv ψ) x) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [uIcc_of_le hR'pos.le] at hx
      simp only [hI, abs_of_nonneg hx.1]
    rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_green_right hσ h1 h2 x)
      (((continuous_neg.div_const σ).rexp.mul (h1.continuous.sub (continuous_const.mul h3))).intervalIntegrable _ _)]
    obtain ⟨e1, e2, -⟩ := hout R' (by rw [abs_of_pos hR'pos])
    simp only [e1, e2, neg_zero, zero_div, exp_zero]
    ring
  have hleft : ∫ x in (-R')..0, I x = σ * (ψ 0 - σ * deriv ψ 0) := by
    have hcongr : ∫ x in (-R')..0, I x = ∫ x in (-R')..0, exp (x / σ) * (ψ x - σ ^ 2 * deriv (deriv ψ) x) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [uIcc_of_le (by linarith)] at hx
      simp only [hI, abs_of_nonpos hx.2, neg_neg]
    rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_green_left hσ h1 h2 x)
      (((continuous_id.div_const σ).rexp.mul (h1.continuous.sub (continuous_const.mul h3))).intervalIntegrable _ _)]
    obtain ⟨e1, e2, -⟩ := hout (-R') (by rw [abs_neg, abs_of_pos hR'pos])
    simp only [e1, e2, zero_div, exp_zero]
    ring
  rw [hright, hleft]
  ring

end StatFormal.ExcessRamp
