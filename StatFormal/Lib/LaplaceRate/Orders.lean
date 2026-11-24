import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option linter.style.longLine false

/-!
# Absorbing a smaller logarithm in a larger one (library, untrusted)

For `0 ≤ a ≤ L`, `L > 0` (trimmed-mmd, S4 :985-987: "as `η < 1`, `L_{n,m} ≥ log(n∨m)`, so `(log(n∨m))^{1/4}L_{n,m}^{1/2} ≤ L_{n,m}^{3/4}`
and `(log(n∨m))^{1/2}L_{n,m} ≤ L_{n,m}^{3/2}`"):

* `quarter_mul_half_le`: `a^{1/4}L^{1/2} ≤ L^{3/4}`;
* `half_mul_div_rpow_le`: `(a^{1/2}L/N)^{4/9} ≤ L^{2/3}N^{−4/9}` for `N > 0`;
* `sqrt_le_rpow_three_quarters`, `one_le_rpow_three_quarters`: `√L ≤ L^{3/4}` and `1 ≤ L^{3/4}` for `L ≥ 1`.
-/

noncomputable section

namespace StatFormal.LaplaceRate

/-- `a^{1/4}L^{1/2} ≤ L^{3/4}` for `0 ≤ a ≤ L`, `L > 0`. -/
theorem quarter_mul_half_le {a L : ℝ} (ha : 0 ≤ a) (haL : a ≤ L) (hL : 0 < L) :
    a ^ (1 / 4 : ℝ) * L ^ (1 / 2 : ℝ) ≤ L ^ (3 / 4 : ℝ) := by
  have h1 : a ^ (1 / 4 : ℝ) ≤ L ^ (1 / 4 : ℝ) := Real.rpow_le_rpow ha haL (by norm_num)
  calc a ^ (1 / 4 : ℝ) * L ^ (1 / 2 : ℝ) ≤ L ^ (1 / 4 : ℝ) * L ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hL.le _)
    _ = L ^ (3 / 4 : ℝ) := by rw [← Real.rpow_add hL]; norm_num

/-- `(a^{1/2}L/N)^{4/9} ≤ L^{2/3}N^{−4/9}` for `0 ≤ a ≤ L`, `L > 0`, `N > 0`. -/
theorem half_mul_div_rpow_le {a L N : ℝ} (ha : 0 ≤ a) (haL : a ≤ L) (hL : 0 < L) (hN : 0 < N) :
    (a ^ (1 / 2 : ℝ) * L / N) ^ (4 / 9 : ℝ) ≤ L ^ (2 / 3 : ℝ) * N ^ (-(4 / 9 : ℝ)) := by
  have h1 : a ^ (1 / 2 : ℝ) * L ≤ L ^ (3 / 2 : ℝ) := by
    calc a ^ (1 / 2 : ℝ) * L ≤ L ^ (1 / 2 : ℝ) * L :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ha haL (by norm_num)) hL.le
      _ = L ^ (3 / 2 : ℝ) := by
          conv_lhs => rw [show L ^ (1 / 2 : ℝ) * L = L ^ (1 / 2 : ℝ) * L ^ (1 : ℝ) by rw [Real.rpow_one]]
          rw [← Real.rpow_add hL]; norm_num
  calc (a ^ (1 / 2 : ℝ) * L / N) ^ (4 / 9 : ℝ) ≤ (L ^ (3 / 2 : ℝ) / N) ^ (4 / 9 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right h1 hN.le) (by norm_num)
    _ = L ^ (2 / 3 : ℝ) * N ^ (-(4 / 9 : ℝ)) := by
        rw [Real.div_rpow (Real.rpow_nonneg hL.le _) hN.le, ← Real.rpow_mul hL.le, Real.rpow_neg hN.le, div_eq_mul_inv]
        norm_num

/-- `√L ≤ L^{3/4}` for `L ≥ 1`. -/
theorem sqrt_le_rpow_three_quarters {L : ℝ} (hL : 1 ≤ L) : √L ≤ L ^ (3 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)

/-- `1 ≤ L^{3/4}` for `L ≥ 1`. -/
theorem one_le_rpow_three_quarters {L : ℝ} (hL : 1 ≤ L) : 1 ≤ L ^ (3 / 4 : ℝ) := Real.one_le_rpow hL (by norm_num)

end StatFormal.LaplaceRate
