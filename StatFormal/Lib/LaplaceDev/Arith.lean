import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option linter.style.longLine false

/-!
# Square-root and power inequalities for localized deviation bounds (library, untrusted)

Real-number facts used to collect the constants of a deviation bound for functions of the Laplace RKHS on the line
(trimmed-mmd, Lemma S4.25), stated for arbitrary reals:

* `sqrt_add_le_sqrt_add_sqrt`: `√(a + b) ≤ √a + √b` for `a, b ≥ 0`;
* `sqrt_two_mul_add_sqrt_two_mul_le`: `√(2u) + √(2v) ≤ 2√(u + v)` for `u, v ≥ 0`;
* `sqrt_sqrt_eq_rpow`, `sqrt_eq_rpow_half`, `rpow_neg_half_eq`: `√√K = K^{1/4}`, `√N = N^{1/2}`, `x^{−1/2} = 1/√x`;
* `width_pos`, `width_le`, `width_sqrt_mul_le`, `sqrt_div_width_le`, `sqrt_div_width_le'`: for `0 < T ≤ 2`, `0 < r ≤ 1` and the width
  `w = min(r, T^{2/5})`: `0 < w ≤ r`, `w^{3/4} = √(w√w) ≤ T^{3/10}`, `(T/w)^{1/2} ≤ 2^{1/5}T^{3/10}/√r` and `(T/w)^{1/2} ≤ (2/r)^{1/2}`
  (the balance of the width in the proof of Lemma S4.25 (b), with the correction F3 of the refereed check).
-/

noncomputable section

namespace StatFormal.LaplaceDev

/-- `√(a + b) ≤ √a + √b` for `a, b ≥ 0`. -/
theorem sqrt_add_le_sqrt_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : √(a + b) ≤ √a + √b := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

/-- `√(2u) + √(2v) ≤ 2√(u + v)` for `u, v ≥ 0`. -/
theorem sqrt_two_mul_add_sqrt_two_mul_le {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    √(2 * u) + √(2 * v) ≤ 2 * √(u + v) := by
  have h1 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * u)
  have h2 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * v)
  have h3 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ u + v)
  have a0 := Real.sqrt_nonneg (2 * u)
  have b0 := Real.sqrt_nonneg (2 * v)
  have s0 := Real.sqrt_nonneg (u + v)
  nlinarith [sq_nonneg (√(2 * u) - √(2 * v)), sq_nonneg (√(2 * u) + √(2 * v) - 2 * √(u + v))]

/-- `√N = N^{1/2}`. -/
theorem sqrt_eq_rpow_half (x : ℝ) : √x = x ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow x

/-- `√√K = K^{1/4}` for `K ≥ 0`. -/
theorem sqrt_sqrt_eq_rpow {K : ℝ} (hK : 0 ≤ K) : √(√K) = K ^ (1 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hK]
  norm_num

/-- `x^{−1/2} = 1/√x` for `x ≥ 0`. -/
theorem rpow_neg_half_eq {x : ℝ} (hx : 0 ≤ x) : x ^ (-(1 / 2 : ℝ)) = 1 / √x := by
  rw [Real.rpow_neg hx, Real.sqrt_eq_rpow]
  exact (one_div _).symm

/-- `√(T^a) = T^{a/2}` for `T ≥ 0`. -/
theorem sqrt_rpow {T : ℝ} (hT : 0 ≤ T) (a : ℝ) : √(T ^ a) = T ^ (a / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT]
  ring_nf

/-- The width is positive. -/
theorem width_pos {T r : ℝ} (hT : 0 < T) (hr : 0 < r) : 0 < min r (T ^ (2 / 5 : ℝ)) :=
  lt_min hr (Real.rpow_pos_of_pos hT _)

/-- The width is at most `r`. -/
theorem width_le (T r : ℝ) : min r (T ^ (2 / 5 : ℝ)) ≤ r := min_le_left _ _

/-- `w^{3/4} = √(w√w) ≤ T^{3/10}` for `w = min(r, T^{2/5})`. -/
theorem width_sqrt_mul_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r) :
    √(min r (T ^ (2 / 5 : ℝ)) * √(min r (T ^ (2 / 5 : ℝ)))) ≤ T ^ (3 / 10 : ℝ) := by
  set w := min r (T ^ (2 / 5 : ℝ)) with hw
  have hw0 : 0 < w := width_pos hT hr
  have hwT : w ≤ T ^ (2 / 5 : ℝ) := min_le_right _ _
  have hsw : √w ≤ T ^ (1 / 5 : ℝ) := by
    calc √w ≤ √(T ^ (2 / 5 : ℝ)) := Real.sqrt_le_sqrt hwT
      _ = T ^ (1 / 5 : ℝ) := by rw [sqrt_rpow hT.le]; norm_num
  have hprod : w * √w ≤ T ^ (3 / 5 : ℝ) := by
    calc w * √w ≤ T ^ (2 / 5 : ℝ) * T ^ (1 / 5 : ℝ) :=
          mul_le_mul hwT hsw (Real.sqrt_nonneg _) (Real.rpow_nonneg hT.le _)
      _ = T ^ (3 / 5 : ℝ) := by rw [← Real.rpow_add hT]; norm_num
  calc √(w * √w) ≤ √(T ^ (3 / 5 : ℝ)) := Real.sqrt_le_sqrt hprod
    _ = T ^ (3 / 10 : ℝ) := by rw [sqrt_rpow hT.le]; norm_num

/-- `(T/w)^{1/2} ≤ 2^{1/5}T^{3/10}/√r` for `w = min(r, T^{2/5})`, `0 < T ≤ 2`, `0 < r ≤ 1`. -/
theorem sqrt_div_width_le {T r : ℝ} (hT : 0 < T) (hT2 : T ≤ 2) (hr : 0 < r) (hr1 : r ≤ 1) :
    √(T / min r (T ^ (2 / 5 : ℝ))) ≤ 2 ^ (1 / 5 : ℝ) * T ^ (3 / 10 : ℝ) / √r := by
  have hsr0 : 0 < √r := Real.sqrt_pos.mpr hr
  have hsr1 : √r ≤ 1 := Real.sqrt_le_one.mpr hr1
  have h2 : (1 : ℝ) ≤ 2 ^ (1 / 5 : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
  have hT3 : 0 ≤ T ^ (3 / 10 : ℝ) := Real.rpow_nonneg hT.le _
  rcases le_total r (T ^ (2 / 5 : ℝ)) with h | h
  · rw [min_eq_left h, Real.sqrt_div hT.le, le_div_iff₀ hsr0, div_mul_cancel₀ _ hsr0.ne']
    have hTs : √T = T ^ (1 / 5 : ℝ) * T ^ (3 / 10 : ℝ) := by
      rw [← Real.rpow_add hT, Real.sqrt_eq_rpow]; norm_num
    rw [hTs]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hT.le hT2 (by norm_num)) hT3
  · rw [min_eq_right h]
    have hq : T / T ^ (2 / 5 : ℝ) = T ^ (3 / 5 : ℝ) := by
      rw [show (3 / 5 : ℝ) = 1 - 2 / 5 by norm_num, Real.rpow_sub hT, Real.rpow_one]
    rw [hq, sqrt_rpow hT.le, show (3 / 5 : ℝ) / 2 = 3 / 10 by norm_num, le_div_iff₀ hsr0]
    calc T ^ (3 / 10 : ℝ) * √r ≤ T ^ (3 / 10 : ℝ) * 1 := mul_le_mul_of_nonneg_left hsr1 hT3
      _ ≤ 2 ^ (1 / 5 : ℝ) * T ^ (3 / 10 : ℝ) := by nlinarith

/-- `(T/w)^{1/2} ≤ (2/r)^{1/2}` for `w = min(r, T^{2/5})`, `0 < T ≤ 2`, `0 < r ≤ 1`. -/
theorem sqrt_div_width_le' {T r : ℝ} (hT : 0 < T) (hT2 : T ≤ 2) (hr : 0 < r) (hr1 : r ≤ 1) :
    √(T / min r (T ^ (2 / 5 : ℝ))) ≤ √(2 / r) := by
  apply Real.sqrt_le_sqrt
  rcases le_total r (T ^ (2 / 5 : ℝ)) with h | h
  · rw [min_eq_left h]
    exact div_le_div_of_nonneg_right hT2 hr.le
  · rw [min_eq_right h]
    have hq : T / T ^ (2 / 5 : ℝ) = T ^ (3 / 5 : ℝ) := by
      rw [show (3 / 5 : ℝ) = 1 - 2 / 5 by norm_num, Real.rpow_sub hT, Real.rpow_one]
    rw [hq]
    calc T ^ (3 / 5 : ℝ) ≤ 2 ^ (3 / 5 : ℝ) := Real.rpow_le_rpow hT.le hT2 (by norm_num)
      _ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 / 1 := by norm_num
      _ ≤ 2 / r := div_le_div_of_nonneg_left (by norm_num) hr hr1

end StatFormal.LaplaceDev
