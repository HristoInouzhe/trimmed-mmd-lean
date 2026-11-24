import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option linter.style.longLine false

/-!
# Real inequalities for fixed-point arguments with fractional powers (library)

Library component (untrusted). Elementary inequalities used to solve a fixed-point inequality of the form
`N y + T ≤ ε + a + ϖ N^{1/2} T^{3/10} + b N` for the unknowns `N, T ≥ 0` (trimmed-mmd, Proposition S4.27).

* `le_rpow_of_rpow_le`: from `X^p ≤ ε` (`X ≥ 0`, `p > 0`) and `p q = 1`, `X ≤ ε^q` (undoing a fractional power);
* `rpow_quarter_pos`, `rpow_quarter_le_one`, `rpow_five_quarters`, `rpow_three_halves`, `rpow_nine_eighths`:
  `ε^{1/4}`, `ε^{5/4} = ε ε^{1/4}`, `ε^{3/2} = ε (ε^{1/4})²`, `ε^{9/8} = ε ε^{1/8}`, `ε^{1/4} = (ε^{1/8})²`;
* `sqrt_mul_rpow_le`: if `N c ε^{1/4} ≤ K` and `0 ≤ T ≤ Lε` with `0 < ε ≤ 1`, then `N^{1/2} T^{3/10} ≤ √(K L^{3/5}) / √c`;
* `amgm_half_three_tenths_fifth`: the weighted arithmetic–geometric mean inequality with weights `1/2, 3/10, 1/5`, in the form
  `ϖ N^{1/2} T^{3/10} ≤ N y/2 + 3T/10 + (ϖ/√y)^5/5` (`y > 0`);
* `amgm_sqrt`: `ϖ √N ≤ N y/4 + ϖ²/y` (`y > 0`);
* `fifth_power_le`: if `(2/c)^{20/33} ϖ^{40/33} ≤ ε` and `y ≥ c ε^{5/4}/2`, then `(ϖ/√y)^5 ≤ ε`;
* `five_rpow_three_fifths_le`: `5^{3/5} ≤ 8/3`;
* `sqrt_mul_le_of_mul_le`: `N c e² ≤ K` gives `√N · √c e ≤ √K`;
* `cap_le`: the own-term fraction `1/(m D g) ≤ 2Kκ/C` from the last term of `ε_fit`;
* `loss_le`: the loss `max(a_o,b_o) T/(1 − a_o − b_o) ≤ κε/4` of moving cut points inward by fractions `a_o, b_o ≤ β`.
-/

noncomputable section

namespace StatFormal.FixedPoint

open Real

/-- **Undoing a fractional power.** If `X ≥ 0`, `p > 0`, `q ≥ 0`, `p q = 1` and `X^p ≤ ε`, then `X ≤ ε^q`. -/
theorem le_rpow_of_rpow_le {X ε p q : ℝ} (hX : 0 ≤ X) (hq : 0 ≤ q) (hpq : p * q = 1) (h : X ^ p ≤ ε) :
    X ≤ ε ^ q := by
  have h1 : (X ^ p) ^ q = X := by rw [← Real.rpow_mul hX, hpq, Real.rpow_one]
  calc X = (X ^ p) ^ q := h1.symm
    _ ≤ ε ^ q := Real.rpow_le_rpow (Real.rpow_nonneg hX p) h hq

/-- `ε^{1/4} > 0` for `ε > 0`. -/
theorem rpow_quarter_pos {ε : ℝ} (hε : 0 < ε) : 0 < ε ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hε _

/-- `ε^{1/4} ≤ 1` for `0 ≤ ε ≤ 1`. -/
theorem rpow_quarter_le_one {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) : ε ^ (1 / 4 : ℝ) ≤ 1 :=
  Real.rpow_le_one hε hε1 (by norm_num)

/-- `ε^{5/4} = ε · ε^{1/4}` for `ε > 0`. -/
theorem rpow_five_quarters {ε : ℝ} (hε : 0 < ε) : ε ^ (5 / 4 : ℝ) = ε * ε ^ (1 / 4 : ℝ) := by
  rw [show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num, Real.rpow_add hε, Real.rpow_one]

/-- `ε^{3/2} = ε · (ε^{1/4})²` for `ε > 0`. -/
theorem rpow_three_halves {ε : ℝ} (hε : 0 < ε) : ε ^ (3 / 2 : ℝ) = ε * (ε ^ (1 / 4 : ℝ)) ^ 2 := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 4 + 1 / 4 by norm_num, Real.rpow_add hε, Real.rpow_add hε, Real.rpow_one]
  ring

/-- `ε^{9/8} = ε · ε^{1/8}` for `ε > 0`. -/
theorem rpow_nine_eighths {ε : ℝ} (hε : 0 < ε) : ε ^ (9 / 8 : ℝ) = ε * ε ^ (1 / 8 : ℝ) := by
  rw [show (9 / 8 : ℝ) = 1 + 1 / 8 by norm_num, Real.rpow_add hε, Real.rpow_one]

/-- `ε^{1/4} = (ε^{1/8})²` for `ε ≥ 0`. -/
theorem rpow_quarter_eq_sq {ε : ℝ} (hε : 0 ≤ ε) : ε ^ (1 / 4 : ℝ) = (ε ^ (1 / 8 : ℝ)) ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hε]; norm_num

/-- `ε^{-1/4} = (ε^{1/4})⁻¹` for `ε ≥ 0`. -/
theorem rpow_neg_quarter {ε : ℝ} (hε : 0 ≤ ε) : ε ^ (-(1 / 4 : ℝ)) = (ε ^ (1 / 4 : ℝ))⁻¹ :=
  Real.rpow_neg hε _

/-- `(x^{1/2})² = x` for `x ≥ 0`. -/
theorem rpow_half_sq {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

/-- `x^{1/2} = √x`. -/
theorem rpow_half_eq_sqrt (x : ℝ) : x ^ (1 / 2 : ℝ) = √x := (Real.sqrt_eq_rpow x).symm

/-- `5^{3/5} ≤ 8/3`, as `5³ = 125 ≤ (8/3)⁵`. -/
theorem five_rpow_three_fifths_le : (5 : ℝ) ^ (3 / 5 : ℝ) ≤ 8 / 3 := by
  have h0 : (0 : ℝ) ≤ (5 : ℝ) ^ (3 / 5 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have h5 : ((5 : ℝ) ^ (3 / 5 : ℝ)) ^ (5 : ℕ) = 125 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  by_contra hcon
  push Not at hcon
  have : ((8 : ℝ) / 3) ^ (5 : ℕ) < ((5 : ℝ) ^ (3 / 5 : ℝ)) ^ (5 : ℕ) :=
    pow_lt_pow_left₀ hcon (by norm_num) (by norm_num)
  rw [h5] at this
  norm_num at this

/-- **The product `N^{1/2} T^{3/10}` under a norm bound and an error bound.** If `N, T ≥ 0`, `c > 0`, `0 < ε ≤ 1`,
`N · c ε^{1/4} ≤ K` and `T ≤ Lε` (`L ≥ 0`), then `N^{1/2} T^{3/10} ≤ √(K L^{3/5}) / √c`: the square of the left side is
`N T^{3/5} ≤ K L^{3/5} ε^{3/5 − 1/4}/c ≤ K L^{3/5}/c`. -/
theorem sqrt_mul_rpow_le {N T c ε K L : ℝ} (hN : 0 ≤ N) (hT : 0 ≤ T) (hc : 0 < c) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hL : 0 ≤ L) (hNK : N * (c * ε ^ (1 / 4 : ℝ)) ≤ K) (hTL : T ≤ L * ε) :
    N ^ (1 / 2 : ℝ) * T ^ (3 / 10 : ℝ) ≤ √(K * L ^ (3 / 5 : ℝ)) / √c := by
  have he4 : 0 < ε ^ (1 / 4 : ℝ) := rpow_quarter_pos hε
  have hA0 : 0 ≤ N ^ (1 / 2 : ℝ) * T ^ (3 / 10 : ℝ) := mul_nonneg (Real.rpow_nonneg hN _) (Real.rpow_nonneg hT _)
  -- the square of the left side
  have hsq : (N ^ (1 / 2 : ℝ) * T ^ (3 / 10 : ℝ)) ^ 2 = N * T ^ (3 / 5 : ℝ) := by
    rw [mul_pow, rpow_half_sq hN, ← Real.rpow_natCast (T ^ (3 / 10 : ℝ)), ← Real.rpow_mul hT]; norm_num
  -- `T^{3/5} ≤ L^{3/5} ε^{3/5}` and `ε^{3/5} = ε^{1/4} ε^{7/20} ≤ ε^{1/4}`
  have hT35 : T ^ (3 / 5 : ℝ) ≤ L ^ (3 / 5 : ℝ) * ε ^ (3 / 5 : ℝ) := by
    rw [← Real.mul_rpow hL hε.le]; exact Real.rpow_le_rpow hT hTL (by norm_num)
  have he35 : ε ^ (3 / 5 : ℝ) ≤ ε ^ (1 / 4 : ℝ) := by
    rw [show (3 / 5 : ℝ) = 1 / 4 + 7 / 20 by norm_num, Real.rpow_add hε]
    have : ε ^ (7 / 20 : ℝ) ≤ 1 := Real.rpow_le_one hε.le hε1 (by norm_num)
    nlinarith
  have hL35 : 0 ≤ L ^ (3 / 5 : ℝ) := Real.rpow_nonneg hL _
  have hK : 0 ≤ K := le_trans (mul_nonneg hN (mul_nonneg hc.le he4.le)) hNK
  -- `N T^{3/5} ≤ K L^{3/5}/c`
  have hmain : N * T ^ (3 / 5 : ℝ) ≤ K * L ^ (3 / 5 : ℝ) / c := by
    rw [le_div_iff₀ hc]
    have h1 : N * T ^ (3 / 5 : ℝ) ≤ N * (L ^ (3 / 5 : ℝ) * ε ^ (1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left (hT35.trans (mul_le_mul_of_nonneg_left he35 hL35)) hN
    have h2 : N * (L ^ (3 / 5 : ℝ) * ε ^ (1 / 4 : ℝ)) * c = L ^ (3 / 5 : ℝ) * (N * (c * ε ^ (1 / 4 : ℝ))) := by ring
    calc N * T ^ (3 / 5 : ℝ) * c ≤ N * (L ^ (3 / 5 : ℝ) * ε ^ (1 / 4 : ℝ)) * c := mul_le_mul_of_nonneg_right h1 hc.le
      _ = L ^ (3 / 5 : ℝ) * (N * (c * ε ^ (1 / 4 : ℝ))) := h2
      _ ≤ L ^ (3 / 5 : ℝ) * K := mul_le_mul_of_nonneg_left hNK hL35
      _ = K * L ^ (3 / 5 : ℝ) := by ring
  rw [← Real.sqrt_div' _ hc.le]
  calc N ^ (1 / 2 : ℝ) * T ^ (3 / 10 : ℝ) = √((N ^ (1 / 2 : ℝ) * T ^ (3 / 10 : ℝ)) ^ 2) := (Real.sqrt_sq hA0).symm
    _ ≤ √(K * L ^ (3 / 5 : ℝ) / c) := Real.sqrt_le_sqrt (hsq ▸ hmain)

/-- **Weighted arithmetic–geometric mean inequality** with weights `1/2, 3/10, 1/5`, applied to `u = N y`, `v = T`,
`w = (ϖ/√y)^5`: `ϖ N^{1/2} T^{3/10} ≤ N y/2 + 3T/10 + (ϖ/√y)^5/5` for `N, T, ϖ ≥ 0` and `y > 0`
(`u^{1/2} w^{1/5} = N^{1/2} √y · ϖ/√y`). -/
theorem amgm_half_three_tenths_fifth {N T ϖ y : ℝ} (hN : 0 ≤ N) (hT : 0 ≤ T) (hϖ : 0 ≤ ϖ) (hy : 0 < y) :
    ϖ * N ^ (1 / 2 : ℝ) * T ^ (3 / 10 : ℝ) ≤ N * y / 2 + 3 * T / 10 + (ϖ / √y) ^ 5 / 5 := by
  have hsy : 0 < √y := Real.sqrt_pos.2 hy
  have hw : 0 ≤ ϖ / √y := div_nonneg hϖ hsy.le
  have h := Real.geom_mean_le_arith_mean3_weighted (w₁ := 1 / 2) (w₂ := 3 / 10) (w₃ := 1 / 5) (p₁ := N * y) (p₂ := T)
    (p₃ := (ϖ / √y) ^ 5) (by norm_num) (by norm_num) (by norm_num) (mul_nonneg hN hy.le) hT (pow_nonneg hw 5)
    (by norm_num)
  have h1 : (N * y) ^ (1 / 2 : ℝ) = N ^ (1 / 2 : ℝ) * √y := by
    rw [Real.mul_rpow hN hy.le, rpow_half_eq_sqrt y]
  have h3 : ((ϖ / √y) ^ 5) ^ (1 / 5 : ℝ) = ϖ / √y := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hw]; norm_num
  rw [h1, h3] at h
  have hlhs : N ^ (1 / 2 : ℝ) * √y * T ^ (3 / 10 : ℝ) * (ϖ / √y) = ϖ * N ^ (1 / 2 : ℝ) * T ^ (3 / 10 : ℝ) := by
    field_simp
  rw [hlhs] at h
  linarith

/-- **Arithmetic–geometric mean, case (ii) form**: `ϖ √N ≤ N y/4 + ϖ²/y` for `N ≥ 0`, `y > 0`. -/
theorem amgm_sqrt {N ϖ y : ℝ} (hN : 0 ≤ N) (hy : 0 < y) : ϖ * √N ≤ N * y / 4 + ϖ ^ 2 / y := by
  have hs : (√N) ^ 2 = N := Real.sq_sqrt hN
  rw [div_add_div _ _ (by norm_num : (4 : ℝ) ≠ 0) hy.ne', le_div_iff₀ (by positivity)]
  have key : 0 ≤ (√N * y - 2 * ϖ) ^ 2 := sq_nonneg _
  have expand : (√N * y - 2 * ϖ) ^ 2 = (√N) ^ 2 * y * y - ϖ * √N * (4 * y) + 4 * ϖ ^ 2 := by ring
  rw [expand, hs] at key
  linarith

/-- **The fourth term of `ε_fit`.** If `ϖ ≥ 0`, `c > 0`, `ε > 0`, `c ε^{5/4}/2 ≤ y` and `(2/c)^{20/33} ϖ^{40/33} ≤ ε`, then
`(ϖ/√y)^5 ≤ ε`: raising the hypothesis to the power `33/40` gives `ϖ ≤ (c/2)^{1/2} ε^{33/40}`, and `√y ≥ (c/2)^{1/2} ε^{5/8}`,
so `ϖ/√y ≤ ε^{1/5}`. -/
theorem fifth_power_le {ϖ c ε y : ℝ} (hϖ : 0 ≤ ϖ) (hc : 0 < c) (hε : 0 < ε) (hy : c * ε ^ (5 / 4 : ℝ) / 2 ≤ y)
    (h4 : (2 / c) ^ (20 / 33 : ℝ) * ϖ ^ (40 / 33 : ℝ) ≤ ε) : (ϖ / √y) ^ 5 ≤ ε := by
  have hc2 : 0 < 2 / c := by positivity
  have hZ0 : 0 ≤ (2 / c) ^ (20 / 33 : ℝ) * ϖ ^ (40 / 33 : ℝ) :=
    mul_nonneg (Real.rpow_nonneg hc2.le _) (Real.rpow_nonneg hϖ _)
  have hZ : ((2 / c) ^ (20 / 33 : ℝ) * ϖ ^ (40 / 33 : ℝ)) ^ (33 / 40 : ℝ) = (2 / c) ^ (1 / 2 : ℝ) * ϖ := by
    rw [Real.mul_rpow (Real.rpow_nonneg hc2.le _) (Real.rpow_nonneg hϖ _), ← Real.rpow_mul hc2.le,
      ← Real.rpow_mul hϖ]
    norm_num
  have hϖle : (2 / c) ^ (1 / 2 : ℝ) * ϖ ≤ ε ^ (33 / 40 : ℝ) := by
    rw [← hZ]; exact Real.rpow_le_rpow hZ0 h4 (by norm_num)
  -- `√y ≥ (c/2)^{1/2} ε^{5/8}`
  have hcε : 0 < c * ε ^ (5 / 4 : ℝ) / 2 := by have := Real.rpow_pos_of_pos hε (5 / 4 : ℝ); positivity
  have hy0 : 0 < y := hcε.trans_le hy
  have hsy : (c / 2) ^ (1 / 2 : ℝ) * ε ^ (5 / 8 : ℝ) ≤ √y := by
    have : (c / 2) ^ (1 / 2 : ℝ) * ε ^ (5 / 8 : ℝ) = (c * ε ^ (5 / 4 : ℝ) / 2) ^ (1 / 2 : ℝ) := by
      rw [show c * ε ^ (5 / 4 : ℝ) / 2 = c / 2 * ε ^ (5 / 4 : ℝ) by ring,
        Real.mul_rpow (by positivity) (Real.rpow_nonneg hε.le _), ← Real.rpow_mul hε.le]
      norm_num
    rw [this, ← rpow_half_eq_sqrt]
    exact Real.rpow_le_rpow hcε.le hy (by norm_num)
  -- `(2/c)^{1/2} (c/2)^{1/2} = 1`
  have hprod : (2 / c) ^ (1 / 2 : ℝ) * (c / 2) ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.mul_rpow hc2.le (by positivity), show 2 / c * (c / 2) = 1 by field_simp, Real.one_rpow]
  have hpos1 : 0 < (2 / c) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hc2 _
  have hpos2 : 0 < (c / 2) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have he58 : 0 < ε ^ (5 / 8 : ℝ) := Real.rpow_pos_of_pos hε _
  -- `ϖ ≤ (c/2)^{1/2} ε^{33/40} = (c/2)^{1/2} ε^{5/8} ε^{1/5} ≤ √y ε^{1/5}`
  have hϖ2 : ϖ ≤ (c / 2) ^ (1 / 2 : ℝ) * ε ^ (33 / 40 : ℝ) := by
    have : ϖ = (c / 2) ^ (1 / 2 : ℝ) * ((2 / c) ^ (1 / 2 : ℝ) * ϖ) := by
      rw [← mul_assoc, mul_comm ((c / 2) ^ (1 / 2 : ℝ)), hprod, one_mul]
    rw [this]; exact mul_le_mul_of_nonneg_left hϖle hpos2.le
  have hsplit : ε ^ (33 / 40 : ℝ) = ε ^ (5 / 8 : ℝ) * ε ^ (1 / 5 : ℝ) := by
    rw [← Real.rpow_add hε]; norm_num
  have he15 : 0 < ε ^ (1 / 5 : ℝ) := Real.rpow_pos_of_pos hε _
  have hratio : ϖ / √y ≤ ε ^ (1 / 5 : ℝ) := by
    rw [div_le_iff₀ (Real.sqrt_pos.2 hy0)]
    calc ϖ ≤ (c / 2) ^ (1 / 2 : ℝ) * ε ^ (5 / 8 : ℝ) * ε ^ (1 / 5 : ℝ) := by rw [mul_assoc, ← hsplit]; exact hϖ2
      _ ≤ √y * ε ^ (1 / 5 : ℝ) := mul_le_mul_of_nonneg_right hsy he15.le
      _ = ε ^ (1 / 5 : ℝ) * √y := mul_comm _ _
  have h15 : (ε ^ (1 / 5 : ℝ)) ^ 5 = ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]; norm_num
  calc (ϖ / √y) ^ 5 ≤ (ε ^ (1 / 5 : ℝ)) ^ 5 :=
        pow_le_pow_left₀ (div_nonneg hϖ (Real.sqrt_nonneg _)) hratio 5
    _ = ε := h15

/-- **A square-root bound from a scaled bound.** If `N ≥ 0`, `c, e > 0` and `N · c e² ≤ K`, then `√N · √c e ≤ √K`. -/
theorem sqrt_mul_le_of_mul_le {N c e K : ℝ} (hN : 0 ≤ N) (hc : 0 < c) (he : 0 < e) (h : N * (c * e ^ 2) ≤ K) :
    √N * (√c * e) ≤ √K := by
  have : √N * (√c * e) = √(N * (c * e ^ 2)) := by
    rw [Real.sqrt_mul hN, Real.sqrt_mul hc.le, Real.sqrt_sq he.le]
  rw [this]; exact Real.sqrt_le_sqrt h

/-- **Loss of moving the cut points inward.** If `0 ≤ a_o ≤ β`, `b_o ≤ β` with `4β ≤ 1`, `βL ≤ κ/8` (`κ > 0`) and
`T ≤ Lε` (`ε > 0`), then `max(a_o,b_o) T/(1 − a_o − b_o) ≤ κε/4` (the denominator is at least `1/2`). -/
theorem loss_le {ao bo β L κ ε T : ℝ} (hao : 0 ≤ ao) (haβ : ao ≤ β) (hbβ : bo ≤ β) (h4β : 4 * β ≤ 1)
    (hβL : β * L ≤ κ / 8) (hκ : 0 < κ) (hε : 0 < ε) (hT : T ≤ L * ε) :
    max ao bo * T / (1 - ao - bo) ≤ κ * ε / 4 := by
  have hden : 1 / 2 ≤ 1 - ao - bo := by linarith
  have hm0 : 0 ≤ max ao bo := le_max_of_le_left hao
  have hmβ : max ao bo ≤ β := max_le haβ hbβ
  have hnum : max ao bo * T ≤ κ * ε / 8 := by
    rcases le_or_gt T 0 with hT0 | hT0
    · have : max ao bo * T ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hm0 hT0
      have : 0 ≤ κ * ε / 8 := by positivity
      linarith
    · calc max ao bo * T ≤ β * (L * ε) := mul_le_mul hmβ hT hT0.le (hm0.trans hmβ)
        _ = β * L * ε := by ring
        _ ≤ κ / 8 * ε := mul_le_mul_of_nonneg_right hβL hε.le
        _ = κ * ε / 8 := by ring
  rw [div_le_iff₀ (by linarith)]
  have : 0 ≤ κ * ε := by positivity
  nlinarith

/-- **The own-term fraction from a lower bound on `D g`.** Let `κ, c, ε, C > 0`, `1 ≤ ν ≤ m` (sample sizes), `c ε^{5/4}/2 ≤ y ≤ D`,
`g > 0` with `(1/g) · c ε^{1/4} ≤ K` (a norm bound for `1/g`), and `(C/(κ c² ν))^{2/3} ≤ ε`. Then `1/(m D g) ≤ 2Kκ/C`: indeed
`D g ≥ y g ≥ c² ε^{3/2}/(2K)` and `C ≤ κ c² ν ε^{3/2}`. -/
theorem cap_le {κ c ε y D g K C : ℝ} {ν m : ℕ} (hκ : 0 < κ) (hc : 0 < c) (hε : 0 < ε) (hC : 0 < C) (hν : 1 ≤ ν)
    (hνm : ν ≤ m) (h5 : (C / (κ * c ^ 2 * ν)) ^ (2 / 3 : ℝ) ≤ ε) (hy : c * ε ^ (5 / 4 : ℝ) / 2 ≤ y) (hDy : y ≤ D)
    (hg : 0 < g) (hK : 1 / g * (c * ε ^ (1 / 4 : ℝ)) ≤ K) : 1 / (m * D * g) ≤ 2 * K * κ / C := by
  set e4 := ε ^ (1 / 4 : ℝ) with he4def
  have he4 : 0 < e4 := rpow_quarter_pos hε
  have hν0 : (0 : ℝ) < ν := by exact_mod_cast hν
  have hνm' : (ν : ℝ) ≤ m := by exact_mod_cast hνm
  have hm0 : (0 : ℝ) < m := hν0.trans_le hνm'
  rw [rpow_five_quarters hε] at hy
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy
  have hD0 : 0 < D := hy0.trans_le hDy
  -- `c e4 ≤ K g`
  have hgK : c * e4 ≤ K * g := by
    rw [one_div, inv_mul_eq_div, div_le_iff₀ hg] at hK; exact hK
  have hK0 : 0 < K := by
    have : 0 < K * g := lt_of_lt_of_le (by positivity) hgK
    exact pos_of_mul_pos_left this hg.le
  -- `C ≤ κ c² ν ε e4²`
  have hX : 0 ≤ C / (κ * c ^ 2 * ν) := by positivity
  have h5' := le_rpow_of_rpow_le hX (by norm_num : (0 : ℝ) ≤ 3 / 2) (by norm_num) h5
  rw [rpow_three_halves hε, div_le_iff₀ (by positivity)] at h5'
  rw [div_le_div_iff₀ (by positivity) hC, one_mul]
  calc C ≤ ε * e4 ^ 2 * (κ * c ^ 2 * ν) := h5'
    _ = 2 * κ * ν * (c * (ε * e4) / 2) * (c * e4) := by ring
    _ ≤ 2 * κ * m * D * (K * g) := by
        have h1 : c * (ε * e4) / 2 ≤ D := hy.trans hDy
        have h2 : 2 * κ * ν ≤ 2 * κ * m := by nlinarith
        have h3 : 0 ≤ c * (ε * e4) / 2 := by positivity
        calc 2 * κ * ν * (c * (ε * e4) / 2) * (c * e4) ≤ 2 * κ * m * D * (c * e4) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact mul_le_mul h2 h1 h3 (by positivity)
          _ ≤ 2 * κ * m * D * (K * g) := mul_le_mul_of_nonneg_left hgK (by positivity)
    _ = 2 * K * κ * (m * D * g) := by ring

end StatFormal.FixedPoint
