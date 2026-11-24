import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Exponential

/-!
# Exponential tail bounds with an enlarged constant (library, untrusted)

`t ↦ Ce^{−t/C}` increases with `C` (`exp_tail_mono`), and a bounded extra mass `2` on `{t < 2r}` is absorbed by the constant
`C + 2r + 2e` (`exp_tail_add_two_le`: `Ce^{−t/C} + 2 ≤ (C + 2r + 2e)e^{−t/(C + 2r + 2e)}` for `0 < t ≤ 2r`), by
`e^{−t/D} ≥ 1 − 2r/D` and `(2r + 2e)(C + 2e) ≥ 2(C + 2r + 2e)`. Used for the tail constant of the perturbed pair of Lemma S4.28
of the trimmed-mmd supplement.
-/

set_option linter.style.longLine false

noncomputable section

namespace StatFormal.LocalLower

/-- `Ce^{−t/C} ≤ De^{−t/D}` for `0 < C ≤ D`, `t ≥ 0`. -/
theorem exp_tail_mono {C D t : ℝ} (hC : 0 < C) (hCD : C ≤ D) (ht : 0 ≤ t) :
    C * Real.exp (-t / C) ≤ D * Real.exp (-t / D) := by
  have hD : 0 < D := hC.trans_le hCD
  have h1 : -t / C ≤ -t / D := by
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left ht hC hCD
  exact mul_le_mul hCD (Real.exp_le_exp.2 h1) (Real.exp_pos _).le hD.le

/-- `Ce^{−t/C} + 2 ≤ (C + 2r + 2e)e^{−t/(C + 2r + 2e)}` for `C > 0` and `0 < t ≤ 2r`. -/
theorem exp_tail_add_two_le {C r t : ℝ} (hC : 0 < C) (ht : 0 < t) (htr : t ≤ 2 * r) :
    C * Real.exp (-t / C) + 2 ≤
      (C + 2 * r + 2 * Real.exp 1) * Real.exp (-t / (C + 2 * r + 2 * Real.exp 1)) := by
  have he : 1 ≤ Real.exp 1 := by
    have := Real.add_one_le_exp 1; linarith
  have hr : 0 < r := by linarith
  set D := C + 2 * r + 2 * Real.exp 1 with hDdef
  have hD : 0 < D := by rw [hDdef]; linarith
  have hCD : C ≤ D := by rw [hDdef]; linarith
  have h1 := exp_tail_mono hC hCD ht.le
  have h1' : C * Real.exp (-t / C) ≤ C * Real.exp (-t / D) := by
    have : -t / C ≤ -t / D := by
      rw [neg_div, neg_div, neg_le_neg_iff]
      exact div_le_div_of_nonneg_left ht.le hC hCD
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 this) hC.le
  -- `e^{−t/D} ≥ 1 − 2r/D`
  have h2 : 1 - 2 * r / D ≤ Real.exp (-t / D) := by
    have := Real.add_one_le_exp (-t / D)
    have : t / D ≤ 2 * r / D := div_le_div_of_nonneg_right htr hD.le
    rw [neg_div] at *
    linarith
  -- `(2r + 2e)(1 − 2r/D) ≥ 2`
  have h3 : 2 ≤ (2 * r + 2 * Real.exp 1) * (1 - 2 * r / D) := by
    have e1 : (2 * r + 2 * Real.exp 1) * (1 - 2 * r / D) = (2 * r + 2 * Real.exp 1) * (C + 2 * Real.exp 1) / D := by
      field_simp
      rw [hDdef]; ring
    rw [e1, le_div_iff₀ hD, hDdef]
    nlinarith [mul_nonneg hr.le hC.le, mul_le_mul_of_nonneg_left he hC.le, mul_le_mul_of_nonneg_left he hr.le]
  have h4 : 2 ≤ (2 * r + 2 * Real.exp 1) * Real.exp (-t / D) := by
    refine h3.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  calc C * Real.exp (-t / C) + 2 ≤ C * Real.exp (-t / D) + (2 * r + 2 * Real.exp 1) * Real.exp (-t / D) :=
        add_le_add h1' h4
    _ = D * Real.exp (-t / D) := by rw [hDdef]; ring

end StatFormal.LocalLower
