import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option linter.style.longLine false

/-!
# Powers below one and the orders of fixed-point thresholds (library, untrusted)

Real-number facts for reading the orders of the terms of a threshold `max{a, b^{4/5}, ϖ^{40/33}, …}` built from deviation constants of
order `u = K^{1/4}(c/N)^{1/2} ≤ 1` (trimmed-mmd, proof of Theorem S4.19, S4 :1372-1381):

* `rpow_le_self_of_le_one`, `self_le_rpow_of_le_one`: `u^p ≤ u` for `p ≥ 1` and `u ≤ u^p` for `p ≤ 1`, when `0 ≤ u ≤ 1`;
* `mul_sq_rpow_le`: `(a·u²)^p ≤ a^p·u^q` for `2p ≥ q`, `q ≥ 0`, `0 ≤ u ≤ 1`;
* `mul_rpow_le`: `(a·u)^p ≤ a^p·u^q` for `p ≥ q ≥ 0`, `0 ≤ u ≤ 1`;
* `sqrt_div_le_of_fifth`, `one_div_le_of_fifth`: `√(c/x) ≤ √5·√(c/N)` and `1/x ≤ 5/N` for `x ≥ N/5 > 0`;
* `rpow_neg_two_thirds_le`: `N^{−2/3} ≤ K^{1/4}√(c/N)` for `N, c, K ≥ 1`;
* `div_rpow_two_thirds_le`: `(a/x)^{2/3} ≤ (5a)^{2/3}·N^{−2/3}` for `x ≥ N/5 > 0`, `a ≥ 0`;
* `sq_quarter_sqrt`: `(K^{1/4}√(c/N))² = K^{1/2}·c/N`.
-/

noncomputable section

namespace StatFormal.LaplaceRate

/-- `u^p ≤ u` for `0 ≤ u ≤ 1` and `p ≥ 1`. -/
theorem rpow_le_self_of_le_one {u p : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hp : 1 ≤ p) : u ^ p ≤ u := by
  have := Real.rpow_le_rpow_of_exponent_ge' hu0 hu1 zero_le_one hp
  rwa [Real.rpow_one] at this

/-- `u ≤ u^p` for `0 ≤ u ≤ 1` and `0 ≤ p ≤ 1`. -/
theorem self_le_rpow_of_le_one {u p : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : u ≤ u ^ p := by
  have := Real.rpow_le_rpow_of_exponent_ge' hu0 hu1 hp0 hp1
  rwa [Real.rpow_one] at this

/-- `(a·u²)^p ≤ a^p·u^q` for `a ≥ 0`, `0 ≤ u ≤ 1`, `0 ≤ q ≤ 2p`. -/
theorem mul_sq_rpow_le {a u p q : ℝ} (ha : 0 ≤ a) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hq : 0 ≤ q) (hpq : q ≤ 2 * p) :
    (a * u ^ 2) ^ p = a ^ p * u ^ (2 * p) ∧ (a * u ^ 2) ^ p ≤ a ^ p * u ^ q := by
  have e : (a * u ^ 2) ^ p = a ^ p * u ^ (2 * p) := by
    rw [Real.mul_rpow ha (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hu0]; norm_num
  refine ⟨e, ?_⟩
  rw [e]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge' hu0 hu1 hq hpq) (Real.rpow_nonneg ha _)

/-- `(a·u)^p ≤ a^p·u^q` for `a ≥ 0`, `0 ≤ u ≤ 1`, `0 ≤ q ≤ p`. -/
theorem mul_rpow_le {a u p q : ℝ} (ha : 0 ≤ a) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hq : 0 ≤ q) (hpq : q ≤ p) :
    (a * u) ^ p ≤ a ^ p * u ^ q := by
  rw [Real.mul_rpow ha hu0]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge' hu0 hu1 hq hpq) (Real.rpow_nonneg ha _)

/-- `√(c/x) ≤ √5·√(c/N)` for `x ≥ N/5 > 0`, `c ≥ 0`. -/
theorem sqrt_div_le_of_fifth {c x N : ℝ} (hc : 0 ≤ c) (hN : 0 < N) (hx : N / 5 ≤ x) : √(c / x) ≤ √5 * √(c / N) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  rw [← Real.sqrt_mul (by norm_num)]
  refine Real.sqrt_le_sqrt ?_
  rw [div_le_iff₀ hx0]
  have : 5 * (c / N) * x = c * (5 * x / N) := by ring
  rw [this]
  refine le_mul_of_one_le_right hc ?_
  rw [le_div_iff₀ hN]; linarith

/-- `1/x ≤ 5/N` for `x ≥ N/5 > 0`. -/
theorem one_div_le_of_fifth {x N : ℝ} (hN : 0 < N) (hx : N / 5 ≤ x) : 1 / x ≤ 5 / N := by
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  rw [div_le_div_iff₀ hx0 hN]; linarith

/-- `N^{−2/3} ≤ K^{1/4}√(c/N)` for `N, c, K ≥ 1`. -/
theorem rpow_neg_two_thirds_le {N c K : ℝ} (hN : 1 ≤ N) (hc : 1 ≤ c) (hK : 1 ≤ K) :
    N ^ (-(2 / 3 : ℝ)) ≤ K ^ (1 / 4 : ℝ) * √(c / N) := by
  have hN0 : 0 < N := by linarith
  have h1 : N ^ (-(2 / 3 : ℝ)) ≤ N ^ (-(1 / 2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
  have h2 : N ^ (-(1 / 2 : ℝ)) ≤ √(c / N) := by
    rw [Real.rpow_neg hN0.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_inv]
    exact Real.sqrt_le_sqrt (by rw [inv_eq_one_div]; exact div_le_div_of_nonneg_right hc hN0.le)
  have h3 : √(c / N) ≤ K ^ (1 / 4 : ℝ) * √(c / N) :=
    le_mul_of_one_le_left (Real.sqrt_nonneg _) (Real.one_le_rpow hK (by norm_num))
  linarith

/-- `(a/x)^{2/3} ≤ (5a)^{2/3}·N^{−2/3}` for `x ≥ N/5 > 0`, `a ≥ 0`. -/
theorem div_rpow_two_thirds_le {a x N : ℝ} (ha : 0 ≤ a) (hN : 0 < N) (hx : N / 5 ≤ x) :
    (a / x) ^ (2 / 3 : ℝ) ≤ (5 * a) ^ (2 / 3 : ℝ) * N ^ (-(2 / 3 : ℝ)) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hb : a / x ≤ 5 * a * N⁻¹ := by
    rw [div_le_iff₀ hx0]
    have : 5 * a * N⁻¹ * x = a * (5 * x / N) := by field_simp
    rw [this]
    refine le_mul_of_one_le_right ha ?_
    rw [le_div_iff₀ hN]; linarith
  calc (a / x) ^ (2 / 3 : ℝ) ≤ (5 * a * N⁻¹) ^ (2 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) hb (by norm_num)
    _ = (5 * a) ^ (2 / 3 : ℝ) * N ^ (-(2 / 3 : ℝ)) := by
      rw [Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hN.le, Real.rpow_neg hN.le]

/-- `(K^{1/4}√(c/N))² = K^{1/2}·(c/N)` for `K ≥ 0`, `c/N ≥ 0`. -/
theorem sq_quarter_sqrt {K c N : ℝ} (hK : 0 ≤ K) (hcN : 0 ≤ c / N) :
    (K ^ (1 / 4 : ℝ) * √(c / N)) ^ 2 = K ^ (1 / 2 : ℝ) * (c / N) := by
  rw [mul_pow, Real.sq_sqrt hcN, ← Real.rpow_natCast, ← Real.rpow_mul hK]; norm_num

end StatFormal.LaplaceRate
