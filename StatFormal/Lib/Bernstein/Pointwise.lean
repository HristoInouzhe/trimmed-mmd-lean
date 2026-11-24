import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Pointwise exponential inequalities for Bernstein-type bounds

Library component F.B (part 1). Untrusted library code: no `Statements.lean` is involved.

## Main results

* `exp_le_quad_of_nonpos`: `exp y ≤ 1 + y + y²/2` for `y ≤ 0`;
* `exp_le_subgamma_of_nonneg`: `exp y ≤ 1 + y + y² / (2 (1 − y/3))` for `0 ≤ y < 3` (power series,
  `(n+2)! ≥ 2·3ⁿ`);
* `exp_mul_le_bernstein`: for `x ≤ 1` and `0 ≤ λ < 3`,
  `exp (λ x) ≤ 1 + λ x + λ² x² / (2 (1 − λ/3))` — the pointwise inequality behind Bernstein's
  moment-generating-function bound.
-/

noncomputable section
open Real

namespace StatFormal.Bernstein

/-- `exp y ≤ 1 + y + y²/2` for `y ≤ 0`. -/
theorem exp_le_quad_of_nonpos {y : ℝ} (hy : y ≤ 0) : exp y ≤ 1 + y + y ^ 2 / 2 := by
  let f : ℝ → ℝ := fun t => 1 + t + t ^ 2 / 2 - exp t
  have hd : ∀ t, HasDerivAt f (1 + t - exp t) t := fun t => by
    have h1 := (((hasDerivAt_id t).const_add 1).add
      ((hasDerivAt_pow 2 t).div_const 2)).sub (hasDerivAt_exp t)
    convert h1 using 1
    · ext u; simp [f]
    · simp
  have hanti : Antitone f := by
    refine antitone_of_deriv_nonpos (fun t => (hd t).differentiableAt) fun t => ?_
    rw [(hd t).deriv]
    linarith [add_one_le_exp t]
  have := hanti hy
  simp only [f] at this
  norm_num at this
  linarith

private theorem two_mul_three_pow_le_factorial (n : ℕ) : 2 * 3 ^ n ≤ (n + 2).factorial := by
  induction n with
  | zero => simp [Nat.factorial]
  | succ n ih =>
    rw [Nat.factorial_succ, pow_succ]
    have : 3 ≤ n + 1 + 2 := by omega
    calc 2 * (3 ^ n * 3) = 3 * (2 * 3 ^ n) := by ring
      _ ≤ (n + 1 + 2) * (n + 2).factorial := Nat.mul_le_mul this ih

/-- `exp y ≤ 1 + y + y² / (2 (1 − y/3))` for `0 ≤ y < 3`. -/
theorem exp_le_subgamma_of_nonneg {y : ℝ} (hy0 : 0 ≤ y) (hy3 : y < 3) :
    exp y ≤ 1 + y + y ^ 2 / (2 * (1 - y / 3)) := by
  have hs : HasSum (fun n : ℕ => y ^ n / n.factorial) (exp y) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp y
  have hs2 := (hasSum_nat_add_iff' 2).2 hs
  have h01 : ∑ i ∈ Finset.range 2, y ^ i / (i.factorial : ℝ) = 1 + y := by
    simp [Finset.sum_range_succ]
  rw [h01] at hs2
  have hr0 : 0 ≤ y / 3 := by positivity
  have hr1 : y / 3 < 1 := by linarith
  have hg := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (y ^ 2 / 2)
  have hle := hasSum_le (fun n => ?_) hs2 hg
  · have hden : (y ^ 2 / 2) * (1 - y / 3)⁻¹ = y ^ 2 / (2 * (1 - y / 3)) := by
      field_simp
    linarith
  · have hfac : (2 : ℝ) * 3 ^ n ≤ ((n + 2).factorial : ℝ) := by
      exact_mod_cast two_mul_three_pow_le_factorial n
    have hpos : (0 : ℝ) < 2 * 3 ^ n := by positivity
    rw [div_pow, show y ^ 2 / 2 * (y ^ n / 3 ^ n) = y ^ (n + 2) / (2 * 3 ^ n) by
      rw [pow_add]; field_simp]
    exact div_le_div_of_nonneg_left (by positivity) hpos hfac

/-- **Bernstein's pointwise inequality**: for `x ≤ 1` and `0 ≤ λ < 3`,
`exp (λ x) ≤ 1 + λ x + λ² x² / (2 (1 − λ/3))`. -/
theorem exp_mul_le_bernstein {l x : ℝ} (hl0 : 0 ≤ l) (hl3 : l < 3) (hx : x ≤ 1) :
    exp (l * x) ≤ 1 + l * x + l ^ 2 * x ^ 2 / (2 * (1 - l / 3)) := by
  have hc : 0 < 1 - l / 3 := by linarith
  have hc1 : 1 - l / 3 ≤ 1 := by linarith
  rcases le_total x 0 with h | h
  · have h1 := exp_le_quad_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hl0 h)
    have h2 : (l * x) ^ 2 / 2 ≤ l ^ 2 * x ^ 2 / (2 * (1 - l / 3)) := by
      rw [mul_pow]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    linarith
  · have hy0 : 0 ≤ l * x := mul_nonneg hl0 h
    have hyl : l * x ≤ l := by nlinarith
    have h1 := exp_le_subgamma_of_nonneg hy0 (by linarith)
    have h2 : (l * x) ^ 2 / (2 * (1 - l * x / 3)) ≤ l ^ 2 * x ^ 2 / (2 * (1 - l / 3)) := by
      rw [mul_pow]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    linarith

end StatFormal.Bernstein
