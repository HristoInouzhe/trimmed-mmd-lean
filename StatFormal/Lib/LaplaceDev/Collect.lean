import StatFormal.Lib.LaplaceDev.Arith

set_option linter.style.longLine false

/-!
# Collecting the constants of the deviation bound (library, untrusted)

The arithmetic that turns the one-sample bounds of `OneSample.lean` into the printed constants of Lemma S4.25 of trimmed-mmd
(at bandwidth `1`), for every `ε, ζ, N ≥ 0`, `K ≥ 1`:

* `collect_a`: `(2ε)^{1/2} + ζ + (2(2K^{1/2}N+1)ε)^{1/2} + (2K^{1/2}N+1)ζ + 2π + 2ε^{1/2} + 2ζ
  ≤ 5ε^{1/2} + 4ζ + 2π + 2K^{1/4}N^{1/2}ε^{1/2} + 6K^{1/2}ζN` (as `√2 + √2 + 2 ≤ 5`, `2K^{1/2}N ≤ 6K^{1/2}N`);
* `collect_b`: with `0 < T ≤ 2`, `0 < r ≤ 1`, `c > 0`, `p ≥ 0` and the width `w = min(r, T^{2/5})`, the bound with
  `B₁ = pw` on the short intervals and `B₂ = T/(cw)` on the middle ones is at most
  `(4 + 2(2p)^{1/2} + 4(cr)^{−1/2})ε^{1/2} + 7ζ + 2π + 2{(2√2p)^{1/2} + 2^{1/5}(2√2/(cr))^{1/2}}K^{1/4}N^{1/2}T^{3/10}ε^{1/2}
  + 6K^{1/2}ζN`
  (the re-derived coefficients: `√2 + 2 + 2√(2p) + 4(cr)^{−1/2} ≤ A₀`, `1 + 2(√2N + √2K^{1/2}N + 2) + 2 ≤ 7 + 6K^{1/2}N`,
  `w^{3/4} ≤ T^{3/10}`, `(T/w)^{1/2} ≤ 2^{1/5}r^{−1/2}T^{3/10}` and `≤ (2/r)^{1/2}`).
-/

noncomputable section

namespace StatFormal.LaplaceDev

/-- The constants of Lemma S4.25 (a), one sample. -/
theorem collect_a {ε ζ N K π : ℝ} (hε : 0 ≤ ε) (hζ : 0 ≤ ζ) (hN : 0 ≤ N) (hK : 1 ≤ K) :
    √(2 * ε) + ζ + (√(2 * (2 * √K * N + 1) * 1 * ε) + (2 * √K * N + 1) * ζ) + (2 * π + 2 * √ε + 2 * ζ) ≤
      5 * √ε + 4 * ζ + 2 * π + 2 * √(√K) * √N * √ε + 6 * √K * ζ * N := by
  have hsK : 0 ≤ √K := Real.sqrt_nonneg K
  have h1 : √(2 * (2 * √K * N + 1) * 1 * ε) ≤ 2 * √(√K) * √N * √ε + √2 * √ε := by
    rw [show 2 * (2 * √K * N + 1) * 1 * ε = 4 * √K * N * ε + 2 * ε by ring]
    refine (sqrt_add_le_sqrt_add_sqrt (by positivity) (by positivity)).trans (le_of_eq ?_)
    congr 1
    · rw [show 4 * √K * N * ε = (2 * √(√K) * √N * √ε) ^ 2 by
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hsK, Real.sq_sqrt hN, Real.sq_sqrt hε]; ring]
      exact Real.sqrt_sq (by positivity)
    · exact Real.sqrt_mul (by norm_num) ε
  have h2 : √(2 * ε) = √2 * √ε := Real.sqrt_mul (by norm_num) ε
  have h3 : √2 ≤ 3 / 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h4 : 0 ≤ √ε := Real.sqrt_nonneg ε
  have h5 : 0 ≤ √K * ζ * N := by positivity
  have h6 : √2 * √ε ≤ 3 / 2 * √ε := mul_le_mul_of_nonneg_right h3 h4
  rw [h2]
  nlinarith

/-- The constants of Lemma S4.25 (b), one sample, with the width `w = min(r, T^{2/5})`. -/
theorem collect_b {ε ζ N K T r c p π : ℝ} (hε : 0 ≤ ε) (hζ : 0 ≤ ζ) (hN : 0 ≤ N) (hK : 1 ≤ K) (hT : 0 < T)
    (hT2 : T ≤ 2) (hr : 0 < r) (hr1 : r ≤ 1) (hc : 0 < c) (hp : 0 ≤ p) :
    √(2 * ε) + ζ +
        2 * (√(2 * (√(2 * min r (T ^ (2 / 5 : ℝ))) * N + 1) * (p * min r (T ^ (2 / 5 : ℝ))) * ε) +
          (√(2 * min r (T ^ (2 / 5 : ℝ))) * N + 1) * ζ) +
        2 * (√(2 * (√(2 * K) * N + 1) * (T / (c * min r (T ^ (2 / 5 : ℝ)))) * ε) + (√(2 * K) * N + 1) * ζ) +
        (2 * π + 2 * √ε + 2 * ζ) ≤
      (4 + 2 * √(2 * p) + 4 / √(c * r)) * √ε + 7 * ζ + 2 * π +
        2 * (√(2 * √2 * p) + 2 ^ (1 / 5 : ℝ) * √(2 * √2 / (c * r))) * √(√K) * √N * T ^ (3 / 10 : ℝ) * √ε +
        6 * √K * ζ * N := by
  have hsK2 : √(2 * K) = √2 * √K := Real.sqrt_mul (by norm_num) K
  rw [hsK2]
  set w := min r (T ^ (2 / 5 : ℝ)) with hwdef
  have hw0 : 0 < w := width_pos hT hr
  have hwr : w ≤ r := width_le T r
  have hw1 : w ≤ 1 := hwr.trans hr1
  have hsw := width_sqrt_mul_le hT hr
  have hA := sqrt_div_width_le hT hT2 hr hr1
  have hA' := sqrt_div_width_le' hT hT2 hr hr1
  rw [← hwdef] at hsw hA hA'
  have hT3 : 0 ≤ T ^ (3 / 10 : ℝ) := Real.rpow_nonneg hT.le _
  have h25 : (0 : ℝ) ≤ 2 ^ (1 / 5 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hsε := Real.sqrt_nonneg ε
  have hsN := Real.sqrt_nonneg N
  have hsK := Real.sqrt_nonneg K
  have hsK1 : 1 ≤ √K := Real.one_le_sqrt.mpr hK
  have hssK1 : 1 ≤ √(√K) := Real.one_le_sqrt.mpr hsK1
  have hs2 : √2 ≤ 3 / 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs20 : 0 ≤ √2 := Real.sqrt_nonneg 2
  have hcr : 0 < c * r := mul_pos hc hr
  have hscr : 0 < √(c * r) := Real.sqrt_pos.mpr hcr
  -- the short intervals
  have s1 : √(2 * (√(2 * w) * N + 1) * (p * w) * ε) ≤
      √(2 * √2 * p) * √N * √ε * T ^ (3 / 10 : ℝ) + √(2 * p) * √ε := by
    have e : 2 * (√(2 * w) * N + 1) * (p * w) * ε =
        (√(2 * √2 * p) * √N * √ε * √(w * √w)) ^ 2 + 2 * p * w * ε := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) w, mul_pow, mul_pow, mul_pow,
        Real.sq_sqrt (show (0 : ℝ) ≤ 2 * √2 * p by positivity), Real.sq_sqrt hN, Real.sq_sqrt hε,
        Real.sq_sqrt (show (0 : ℝ) ≤ w * √w by positivity)]
      ring
    rw [e]
    refine (sqrt_add_le_sqrt_add_sqrt (by positivity) (by positivity)).trans (add_le_add ?_ ?_)
    · rw [Real.sqrt_sq (by positivity)]
      exact mul_le_mul_of_nonneg_left hsw (by positivity)
    · rw [← Real.sqrt_mul (show (0 : ℝ) ≤ 2 * p by positivity) ε]
      apply Real.sqrt_le_sqrt
      have := mul_le_mul_of_nonneg_left hw1 (mul_nonneg hp hε)
      nlinarith
  -- the middle intervals
  have hsq : √(2 * √2 / (c * r)) = √(2 * √2 / c) / √r := by
    rw [← div_div, Real.sqrt_div' _ hr.le]
  have hb2 : √(2 / c) * √(2 / r) = 2 / √(c * r) := by
    rw [← Real.sqrt_mul (by positivity) (2 / r), div_mul_div_comm, Real.sqrt_div' _ hcr.le,
      Real.sqrt_mul_self (by norm_num)]
  have s2 : √(2 * (√2 * √K * N + 1) * (T / (c * w)) * ε) ≤
      2 ^ (1 / 5 : ℝ) * √(2 * √2 / (c * r)) * √(√K) * √N * T ^ (3 / 10 : ℝ) * √ε + 2 / √(c * r) * √ε := by
    have e : 2 * (√2 * √K * N + 1) * (T / (c * w)) * ε =
        (√(2 * √2 / c) * √(√K) * √N * √(T / w) * √ε) ^ 2 + (√(2 / c) * √(T / w) * √ε) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow,
        Real.sq_sqrt (show (0 : ℝ) ≤ 2 * √2 / c by positivity), Real.sq_sqrt hsK, Real.sq_sqrt hN,
        Real.sq_sqrt (show (0 : ℝ) ≤ T / w by positivity), Real.sq_sqrt hε,
        Real.sq_sqrt (show (0 : ℝ) ≤ 2 / c by positivity)]
      field_simp
    rw [e]
    refine (sqrt_add_le_sqrt_add_sqrt (by positivity) (by positivity)).trans (add_le_add ?_ ?_)
    · rw [Real.sqrt_sq (by positivity)]
      calc √(2 * √2 / c) * √(√K) * √N * √(T / w) * √ε ≤
            √(2 * √2 / c) * √(√K) * √N * (2 ^ (1 / 5 : ℝ) * T ^ (3 / 10 : ℝ) / √r) * √ε := by gcongr
        _ = 2 ^ (1 / 5 : ℝ) * √(2 * √2 / (c * r)) * √(√K) * √N * T ^ (3 / 10 : ℝ) * √ε := by
          rw [hsq]; ring
    · rw [Real.sqrt_sq (by positivity), ← hb2]
      calc √(2 / c) * √(T / w) * √ε ≤ √(2 / c) * √(2 / r) * √ε := by gcongr
        _ = _ := by ring
  -- the variation bound on the short intervals
  have s3 : (√(2 * w) * N + 1) * ζ ≤ (√2 * N + 1) * ζ := by
    have : √(2 * w) ≤ √2 := Real.sqrt_le_sqrt (by linarith)
    have := mul_le_mul_of_nonneg_right this hN
    nlinarith
  -- collecting
  have f1 : √(2 * ε) = √2 * √ε := Real.sqrt_mul (by norm_num) ε
  have f2 : √(2 * √2 * p) * √N * √ε * T ^ (3 / 10 : ℝ) ≤ √(2 * √2 * p) * √(√K) * √N * T ^ (3 / 10 : ℝ) * √ε := by
    have h0 : 0 ≤ √(2 * √2 * p) * √N * √ε * T ^ (3 / 10 : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left hssK1 h0
    linarith
  have f3 : √2 * N * ζ + √2 * √K * N * ζ ≤ 3 * √K * N * ζ := by
    have hNζ : 0 ≤ N * ζ := mul_nonneg hN hζ
    have h1 := mul_le_mul_of_nonneg_left hsK1 (mul_nonneg hs20 hNζ)
    have h2 := mul_le_mul_of_nonneg_right hs2 (mul_nonneg hsK hNζ)
    linarith
  have f4 : √2 * √ε ≤ 2 * √ε := mul_le_mul_of_nonneg_right (by linarith) hsε
  have f5 : 4 / √(c * r) * √ε = 2 * (2 / √(c * r) * √ε) := by ring
  rw [f1]
  linarith [s1, s2, s3, f2, f3, f4, f5]

end StatFormal.LaplaceDev
