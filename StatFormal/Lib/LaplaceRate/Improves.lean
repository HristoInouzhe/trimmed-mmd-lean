import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds

set_option linter.style.longLine false

/-!
# Logarithmic factors against powers (library, untrusted)

Real-number facts for reading rates "up to powers of `log(n∨m)`" (trimmed-mmd, Theorem 5.11 and the sentence of §5 that compares it
with Theorem 5.7):

* `rpow_le_add_one`: `x^p ≤ x + 1` for `x ≥ 0`, `0 ≤ p ≤ 1`;
* `one_lt_log_ten`, `one_le_log_of_ten_le`: `1 < log 10`, so `log M ≥ 1` for `M ≥ 10`;
* `log_div_le_mul_log`: `log(M/η) ≤ (1 + log(1/η)/log M₀)·log M` for `M ≥ M₀ > 1`, `0 < η ≤ 1` (the factor `L_{n,m}` is a constant
  multiple of `log(n∨m)`);
* `log_div_le_rpow`: `log(M/η) ≤ (90k + log(1/η))·N^{1/90}` for `1 ≤ M ≤ N^k`, `N ≥ 1`, `0 < η ≤ 1` (comparable sample sizes);
* `const_le_rpow_of_le`: `T ≤ N^{1/27}` once `N ≥ T^{27}`;
* `log_bound_i`, `log_bound_ii`: the two bounds of Theorem 5.11 as a power of `log M` times the polynomial factor;
* `small_i`, `small_ii`: both bounds are at most `ε N^{−2/5}` once `N^{1/27} ≥ C(A + 1 + B)/ε`.
-/

noncomputable section

namespace StatFormal.LaplaceRate

open Real

/-- `x^p ≤ x + 1` for `x ≥ 0` and `0 ≤ p ≤ 1`. -/
theorem rpow_le_add_one {x p : ℝ} (hx : 0 ≤ x) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : x ^ p ≤ x + 1 := by
  rcases le_total x 1 with h | h
  · have : x ^ p ≤ 1 := Real.rpow_le_one hx h hp0
    linarith
  · have : x ^ p ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hp1
    rw [Real.rpow_one] at this
    linarith

/-- `1 < log 10`. -/
theorem one_lt_log_ten : 1 < Real.log 10 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  exact Real.exp_one_lt_d9.trans (by norm_num)

/-- `log M ≥ 1` for `M ≥ 10`. -/
theorem one_le_log_of_ten_le {M : ℝ} (hM : 10 ≤ M) : 1 ≤ Real.log M :=
  one_lt_log_ten.le.trans (Real.log_le_log (by norm_num) hM)

/-- `log(M/η) ≤ (1 + log(1/η)/log M₀)·log M` for `M ≥ M₀ > 1` and `0 < η ≤ 1`. -/
theorem log_div_le_mul_log {M M₀ η : ℝ} (hM₀ : 1 < M₀) (hM : M₀ ≤ M) (hη0 : 0 < η) (hη1 : η ≤ 1) :
    Real.log (M / η) ≤ (1 + Real.log (1 / η) / Real.log M₀) * Real.log M := by
  have hM0 : 0 < M := by linarith
  have hl0 : 0 < Real.log M₀ := Real.log_pos hM₀
  have hlM : Real.log M₀ ≤ Real.log M := Real.log_le_log (by linarith) hM
  have he : 0 ≤ Real.log (1 / η) := Real.log_nonneg (by rw [le_div_iff₀ hη0]; linarith)
  have hsplit : Real.log (M / η) = Real.log M + Real.log (1 / η) := by
    rw [div_eq_mul_one_div M η, Real.log_mul hM0.ne' (by positivity)]
  rw [hsplit, add_mul, one_mul]
  have : Real.log (1 / η) ≤ Real.log (1 / η) / Real.log M₀ * Real.log M := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl0]
    exact mul_le_mul_of_nonneg_left hlM he
  linarith

/-- `log(M/η) ≤ (90k + log(1/η))·N^{1/90}` for `1 ≤ M ≤ N^k`, `N ≥ 1`, `k ≥ 0`, `0 < η ≤ 1`. -/
theorem log_div_le_rpow {M N k η : ℝ} (hN : 1 ≤ N) (hM1 : 1 ≤ M) (hMN : M ≤ N ^ k) (hk : 0 ≤ k) (hη0 : 0 < η)
    (hη1 : η ≤ 1) : Real.log (M / η) ≤ (90 * k + Real.log (1 / η)) * N ^ (1 / 90 : ℝ) := by
  have hN0 : 0 < N := by linarith
  have hM0 : 0 < M := by linarith
  have he : 0 ≤ Real.log (1 / η) := Real.log_nonneg (by rw [le_div_iff₀ hη0]; linarith)
  have hsplit : Real.log (M / η) = Real.log M + Real.log (1 / η) := by
    rw [div_eq_mul_one_div M η, Real.log_mul hM0.ne' (by positivity)]
  have hlogM : Real.log M ≤ k * Real.log N := by
    calc Real.log M ≤ Real.log (N ^ k) := Real.log_le_log hM0 hMN
      _ = k * Real.log N := Real.log_rpow hN0 k
  have hlogN : Real.log N ≤ 90 * N ^ (1 / 90 : ℝ) := by
    have := Real.log_le_rpow_div hN0.le (by norm_num : (0 : ℝ) < 1 / 90)
    calc Real.log N ≤ N ^ (1 / 90 : ℝ) / (1 / 90) := this
      _ = 90 * N ^ (1 / 90 : ℝ) := by ring
  have hpow : 1 ≤ N ^ (1 / 90 : ℝ) := Real.one_le_rpow hN (by norm_num)
  rw [hsplit]
  have h1 : Real.log M ≤ 90 * k * N ^ (1 / 90 : ℝ) := by
    calc Real.log M ≤ k * Real.log N := hlogM
      _ ≤ k * (90 * N ^ (1 / 90 : ℝ)) := mul_le_mul_of_nonneg_left hlogN hk
      _ = 90 * k * N ^ (1 / 90 : ℝ) := by ring
  have h2 : Real.log (1 / η) ≤ Real.log (1 / η) * N ^ (1 / 90 : ℝ) := by nlinarith
  nlinarith

/-- `T ≤ N^{1/27}` once `N ≥ T^{27}` (`T ≥ 0`). -/
theorem const_le_rpow_of_le {T N : ℝ} (hT : 0 ≤ T) (hN : T ^ (27 : ℝ) ≤ N) : T ≤ N ^ (1 / 27 : ℝ) := by
  have h := Real.rpow_le_rpow (Real.rpow_nonneg hT _) hN (by norm_num : (0 : ℝ) ≤ 1 / 27)
  rwa [← Real.rpow_mul hT, show (27 : ℝ) * (1 / 27) = 1 by norm_num, Real.rpow_one] at h

/-- Theorem 5.11 (i) up to a power of `log M`: for `0 ≤ L ≤ k·lM`, `k ≥ 1`, `lM ≥ 1`, `B ≥ 0`, `C ≥ 0`, `N > 0`,
`C(L^{3/4}/√N + B/√N) ≤ C(k + B)·lM^{3/4}/√N`. -/
theorem log_bound_i {C k B L lM N : ℝ} (hC : 0 ≤ C) (hk : 1 ≤ k) (hB : 0 ≤ B) (hL0 : 0 ≤ L) (hL : L ≤ k * lM)
    (hlM : 1 ≤ lM) (hN : 0 < N) :
    C * (L ^ (3 / 4 : ℝ) / √N + B / √N) ≤ C * (k + B) * lM ^ (3 / 4 : ℝ) / √N := by
  have hsN : 0 < √N := Real.sqrt_pos.2 hN
  have hl0 : 0 ≤ lM := by linarith
  have h1 : L ^ (3 / 4 : ℝ) ≤ k * lM ^ (3 / 4 : ℝ) := by
    calc L ^ (3 / 4 : ℝ) ≤ (k * lM) ^ (3 / 4 : ℝ) := Real.rpow_le_rpow hL0 hL (by norm_num)
      _ = k ^ (3 / 4 : ℝ) * lM ^ (3 / 4 : ℝ) := Real.mul_rpow (by linarith) hl0
      _ ≤ k * lM ^ (3 / 4 : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hl0 _)
        have := Real.rpow_le_rpow_of_exponent_le hk (by norm_num : (3 / 4 : ℝ) ≤ 1)
        rwa [Real.rpow_one] at this
  have h2 : B ≤ B * lM ^ (3 / 4 : ℝ) := le_mul_of_one_le_right hB (Real.one_le_rpow hlM (by norm_num))
  have h3 : L ^ (3 / 4 : ℝ) + B ≤ (k + B) * lM ^ (3 / 4 : ℝ) := by nlinarith
  calc C * (L ^ (3 / 4 : ℝ) / √N + B / √N) = C * ((L ^ (3 / 4 : ℝ) + B) / √N) := by rw [add_div]
    _ ≤ C * ((k + B) * lM ^ (3 / 4 : ℝ) / √N) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h3 hsN.le) hC
    _ = C * (k + B) * lM ^ (3 / 4 : ℝ) / √N := by ring

/-- Theorem 5.11 (ii) up to a power of `log M`: for `0 ≤ L ≤ k·lM`, `k ≥ 1`, `lM ≥ 1`, `B ≥ 0`, `C ≥ 0`, `N ≥ 1`,
`C(L^{2/3}N^{−4/9} + B/√N) ≤ C(k + B)·lM^{2/3}N^{−4/9}`. -/
theorem log_bound_ii {C k B L lM N : ℝ} (hC : 0 ≤ C) (hk : 1 ≤ k) (hB : 0 ≤ B) (hL0 : 0 ≤ L) (hL : L ≤ k * lM)
    (hlM : 1 ≤ lM) (hN : 1 ≤ N) :
    C * (L ^ (2 / 3 : ℝ) * N ^ (-(4 / 9 : ℝ)) + B / √N) ≤ C * (k + B) * lM ^ (2 / 3 : ℝ) * N ^ (-(4 / 9 : ℝ)) := by
  have hN0 : 0 < N := by linarith
  have hl0 : 0 ≤ lM := by linarith
  have h1 : L ^ (2 / 3 : ℝ) ≤ k * lM ^ (2 / 3 : ℝ) := by
    calc L ^ (2 / 3 : ℝ) ≤ (k * lM) ^ (2 / 3 : ℝ) := Real.rpow_le_rpow hL0 hL (by norm_num)
      _ = k ^ (2 / 3 : ℝ) * lM ^ (2 / 3 : ℝ) := Real.mul_rpow (by linarith) hl0
      _ ≤ k * lM ^ (2 / 3 : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hl0 _)
        have := Real.rpow_le_rpow_of_exponent_le hk (by norm_num : (2 / 3 : ℝ) ≤ 1)
        rwa [Real.rpow_one] at this
  have h2 : B ≤ B * lM ^ (2 / 3 : ℝ) := le_mul_of_one_le_right hB (Real.one_le_rpow hlM (by norm_num))
  have h3 : 1 / √N ≤ N ^ (-(4 / 9 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hN0.le]
    exact Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
  have hp : 0 ≤ N ^ (-(4 / 9 : ℝ)) := Real.rpow_nonneg hN0.le _
  have hlp : 0 ≤ lM ^ (2 / 3 : ℝ) := Real.rpow_nonneg hl0 _
  have h4 : B / √N ≤ B * N ^ (-(4 / 9 : ℝ)) := by
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left h3 hB
  have h5 : L ^ (2 / 3 : ℝ) * N ^ (-(4 / 9 : ℝ)) + B / √N ≤ (k + B) * lM ^ (2 / 3 : ℝ) * N ^ (-(4 / 9 : ℝ)) := by
    have : L ^ (2 / 3 : ℝ) * N ^ (-(4 / 9 : ℝ)) ≤ k * lM ^ (2 / 3 : ℝ) * N ^ (-(4 / 9 : ℝ)) :=
      mul_le_mul_of_nonneg_right h1 hp
    have : B * N ^ (-(4 / 9 : ℝ)) ≤ B * lM ^ (2 / 3 : ℝ) * N ^ (-(4 / 9 : ℝ)) := mul_le_mul_of_nonneg_right h2 hp
    nlinarith
  calc C * (L ^ (2 / 3 : ℝ) * N ^ (-(4 / 9 : ℝ)) + B / √N)
      ≤ C * ((k + B) * lM ^ (2 / 3 : ℝ) * N ^ (-(4 / 9 : ℝ))) := mul_le_mul_of_nonneg_left h5 hC
    _ = C * (k + B) * lM ^ (2 / 3 : ℝ) * N ^ (-(4 / 9 : ℝ)) := by ring

/-- `N^a ≤ N^b` packaged for `N ≥ 1`. -/
private theorem rpow_mono_exp {N a b : ℝ} (hN : 1 ≤ N) (h : a ≤ b) : N ^ a ≤ N ^ b :=
  Real.rpow_le_rpow_of_exponent_le hN h

/-- Theorem 5.11 (i) is `o(N^{−2/5})` for comparable sizes: for `C > 0`, `ε > 0`, `A, B ≥ 0`, `N ≥ 1`, `0 ≤ L ≤ A·N^{1/90}` and
`C(A + 1 + B)/ε ≤ N^{1/27}`: `C(L^{3/4}/√N + B/√N) ≤ εN^{−2/5}`. -/
theorem small_i {C ε A B L N : ℝ} (hC : 0 < C) (hε : 0 < ε) (hA : 0 ≤ A) (hB : 0 ≤ B) (hN : 1 ≤ N) (hL0 : 0 ≤ L)
    (hL : L ≤ A * N ^ (1 / 90 : ℝ)) (hT : C * (A + 1 + B) / ε ≤ N ^ (1 / 27 : ℝ)) :
    C * (L ^ (3 / 4 : ℝ) / √N + B / √N) ≤ ε * N ^ (-(2 / 5 : ℝ)) := by
  have hN0 : 0 < N := by linarith
  have hq : 0 ≤ N ^ (1 / 90 : ℝ) := Real.rpow_nonneg hN0.le _
  have h1 : L ^ (3 / 4 : ℝ) ≤ (A + 1) * N ^ (1 / 120 : ℝ) := by
    calc L ^ (3 / 4 : ℝ) ≤ (A * N ^ (1 / 90 : ℝ)) ^ (3 / 4 : ℝ) := Real.rpow_le_rpow hL0 hL (by norm_num)
      _ = A ^ (3 / 4 : ℝ) * N ^ (1 / 120 : ℝ) := by
        rw [Real.mul_rpow hA hq, ← Real.rpow_mul hN0.le]; norm_num
      _ ≤ (A + 1) * N ^ (1 / 120 : ℝ) :=
        mul_le_mul_of_nonneg_right (rpow_le_add_one hA (by norm_num) (by norm_num)) (Real.rpow_nonneg hN0.le _)
  have h2 : B ≤ B * N ^ (1 / 120 : ℝ) := le_mul_of_one_le_right hB (Real.one_le_rpow hN (by norm_num))
  have hsum : L ^ (3 / 4 : ℝ) + B ≤ (A + 1 + B) * N ^ (1 / 120 : ℝ) := by nlinarith
  have hsq : √N = N ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow N
  have hCT : C * (A + 1 + B) ≤ ε * N ^ (1 / 27 : ℝ) := by
    rw [div_le_iff₀ hε] at hT; linarith
  have hpos : 0 < N ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hN0 _
  calc C * (L ^ (3 / 4 : ℝ) / √N + B / √N) = C * (L ^ (3 / 4 : ℝ) + B) * N ^ (-(1 / 2 : ℝ)) := by
        rw [hsq, Real.rpow_neg hN0.le]; field_simp
    _ ≤ C * ((A + 1 + B) * N ^ (1 / 120 : ℝ)) * N ^ (-(1 / 2 : ℝ)) := by
        gcongr
    _ = C * (A + 1 + B) * (N ^ (1 / 120 : ℝ) * N ^ (-(1 / 2 : ℝ))) := by ring
    _ ≤ ε * N ^ (1 / 27 : ℝ) * (N ^ (1 / 120 : ℝ) * N ^ (-(1 / 2 : ℝ))) := by
        gcongr
    _ = ε * N ^ ((1 / 27 : ℝ) + 1 / 120 + -(1 / 2)) := by
        rw [Real.rpow_add hN0, Real.rpow_add hN0]; ring
    _ ≤ ε * N ^ (-(2 / 5 : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN (by norm_num)) hε.le

/-- Theorem 5.11 (ii) is `o(N^{−2/5})` for comparable sizes: for `C > 0`, `ε > 0`, `A, B ≥ 0`, `N ≥ 1`, `0 ≤ L ≤ A·N^{1/90}` and
`C(A + 1 + B)/ε ≤ N^{1/27}`: `C(L^{2/3}N^{−4/9} + B/√N) ≤ εN^{−2/5}`. -/
theorem small_ii {C ε A B L N : ℝ} (hC : 0 < C) (hε : 0 < ε) (hA : 0 ≤ A) (hB : 0 ≤ B) (hN : 1 ≤ N) (hL0 : 0 ≤ L)
    (hL : L ≤ A * N ^ (1 / 90 : ℝ)) (hT : C * (A + 1 + B) / ε ≤ N ^ (1 / 27 : ℝ)) :
    C * (L ^ (2 / 3 : ℝ) * N ^ (-(4 / 9 : ℝ)) + B / √N) ≤ ε * N ^ (-(2 / 5 : ℝ)) := by
  have hN0 : 0 < N := by linarith
  have hq : 0 ≤ N ^ (1 / 90 : ℝ) := Real.rpow_nonneg hN0.le _
  have h1 : L ^ (2 / 3 : ℝ) ≤ (A + 1) * N ^ (1 / 135 : ℝ) := by
    calc L ^ (2 / 3 : ℝ) ≤ (A * N ^ (1 / 90 : ℝ)) ^ (2 / 3 : ℝ) := Real.rpow_le_rpow hL0 hL (by norm_num)
      _ = A ^ (2 / 3 : ℝ) * N ^ (1 / 135 : ℝ) := by
        rw [Real.mul_rpow hA hq, ← Real.rpow_mul hN0.le]; norm_num
      _ ≤ (A + 1) * N ^ (1 / 135 : ℝ) :=
        mul_le_mul_of_nonneg_right (rpow_le_add_one hA (by norm_num) (by norm_num)) (Real.rpow_nonneg hN0.le _)
  have h3 : 1 / √N ≤ N ^ (1 / 135 : ℝ) * N ^ (-(4 / 9 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hN0.le, ← Real.rpow_add hN0]
    exact Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
  have h4 : B / √N ≤ B * (N ^ (1 / 135 : ℝ) * N ^ (-(4 / 9 : ℝ))) := by
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left h3 hB
  have hp : 0 ≤ N ^ (-(4 / 9 : ℝ)) := Real.rpow_nonneg hN0.le _
  have hsum : L ^ (2 / 3 : ℝ) * N ^ (-(4 / 9 : ℝ)) + B / √N ≤
      (A + 1 + B) * (N ^ (1 / 135 : ℝ) * N ^ (-(4 / 9 : ℝ))) := by
    have : L ^ (2 / 3 : ℝ) * N ^ (-(4 / 9 : ℝ)) ≤ (A + 1) * N ^ (1 / 135 : ℝ) * N ^ (-(4 / 9 : ℝ)) :=
      mul_le_mul_of_nonneg_right h1 hp
    nlinarith
  have hCT : C * (A + 1 + B) ≤ ε * N ^ (1 / 27 : ℝ) := by
    rw [div_le_iff₀ hε] at hT; linarith
  have hpp : 0 ≤ N ^ (1 / 135 : ℝ) * N ^ (-(4 / 9 : ℝ)) := by positivity
  calc C * (L ^ (2 / 3 : ℝ) * N ^ (-(4 / 9 : ℝ)) + B / √N)
      ≤ C * ((A + 1 + B) * (N ^ (1 / 135 : ℝ) * N ^ (-(4 / 9 : ℝ)))) := mul_le_mul_of_nonneg_left hsum hC.le
    _ = C * (A + 1 + B) * (N ^ (1 / 135 : ℝ) * N ^ (-(4 / 9 : ℝ))) := by ring
    _ ≤ ε * N ^ (1 / 27 : ℝ) * (N ^ (1 / 135 : ℝ) * N ^ (-(4 / 9 : ℝ))) := mul_le_mul_of_nonneg_right hCT hpp
    _ = ε * N ^ ((1 / 27 : ℝ) + 1 / 135 + -(4 / 9)) := by
        rw [Real.rpow_add hN0, Real.rpow_add hN0]; ring
    _ = ε * N ^ (-(2 / 5 : ℝ)) := by norm_num

end StatFormal.LaplaceRate
