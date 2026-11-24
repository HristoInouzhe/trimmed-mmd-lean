import StatFormal.Lib.CrossLaws.Gauss
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The likelihood-ratio condition for Gaussian location pairs and two-component mixtures (library, untrusted)

For `t ∈ ℝ`, `|tanh t| ≥ min(1,|t|)/5`, written without division as `min(1,|t|)/5·(eᵗ + e⁻ᵗ) ≤ |eᵗ − e⁻ᵗ|`
(`min_mul_cosh_le_abs_sinh`). For the two-component Gaussian pair `p = wφ₀ + (1−w)φ_a`, `q = wφ₀ + (1−w)φ_{−a}`
(`φ_m` the `N(m,1)` density, `0 ≤ w < 1`, `a > 0`), `φ_{±a}(x) = φ₀(x)e^{−a²/2}e^{±ax}` (`gpdf_shift`), so
`|p − q| = (1−w)e^{−a²/2}φ₀|e^{ax} − e^{−ax}|` and `p + q ≤ φ₀(e^{ax} + e^{−ax})(w + (1−w)e^{−a²/2})`, which gives
`c·min(1,|x|)·(p + q) ≤ |p − q|` for every `x` with the explicit constant
`c = (1−w)e^{−a²/2}min(1,a)/(5(w + (1−w)e^{−a²/2}))` (`gaussPair_ratio_lower`, `gaussPairConst_pos`). The case `w = 0` is the
location pair `N(±a,1)`. Used for the simulated pairs of the trimmed-mmd paper (the shift `N(±1,1)` and the mixture
`0.8N(0,1) + 0.2N(±1.5,1)`) and their likelihood-ratio condition (5.1).
-/

set_option linter.style.longLine false

noncomputable section
open ProbabilityTheory

namespace StatFormal.CrossExamples

/-- `min(1,t)/5·(eᵗ + e⁻ᵗ) ≤ eᵗ − e⁻ᵗ` for `t ≥ 0` (from `e^{2t} ≥ 1 + 2t` and `e^{2t} ≤ e² < 9` on `[0,1]`). -/
theorem min_mul_cosh_le_sinh_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    min 1 t / 5 * (Real.exp t + Real.exp (-t)) ≤ Real.exp t - Real.exp (-t) := by
  have hu : 0 < Real.exp t := Real.exp_pos t
  have huv : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
  have h2 : 1 + 2 * t ≤ Real.exp t ^ 2 := by
    rw [sq, ← Real.exp_add]; linarith [Real.add_one_le_exp (t + t)]
  have hm0 : 0 ≤ min 1 t := le_min zero_le_one ht
  have key : min 1 t / 5 * (Real.exp t ^ 2 + 1) ≤ Real.exp t ^ 2 - 1 := by
    rcases le_total t 1 with h1 | h1
    · rw [min_eq_right h1]
      have h9 : Real.exp t ^ 2 ≤ 9 := by
        have h3 : Real.exp t ≤ Real.exp 1 := Real.exp_le_exp.2 h1
        have he : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
        nlinarith [Real.exp_pos 1]
      nlinarith
    · rw [min_eq_left h1]
      nlinarith
  have hexp : (Real.exp t - Real.exp (-t) - min 1 t / 5 * (Real.exp t + Real.exp (-t))) * Real.exp t =
      Real.exp t ^ 2 - 1 - min 1 t / 5 * (Real.exp t ^ 2 + 1) := by
    linear_combination (-(1 + min 1 t / 5)) * huv
  have h0 : 0 ≤ Real.exp t - Real.exp (-t) - min 1 t / 5 * (Real.exp t + Real.exp (-t)) := by
    have : 0 * Real.exp t ≤ (Real.exp t - Real.exp (-t) - min 1 t / 5 * (Real.exp t + Real.exp (-t))) * Real.exp t := by
      rw [hexp, zero_mul]; linarith
    exact le_of_mul_le_mul_right this hu
  linarith

/-- **`|tanh t| ≥ min(1,|t|)/5`**: `min(1,|t|)/5·(eᵗ + e⁻ᵗ) ≤ |eᵗ − e⁻ᵗ|` for every real `t`. -/
theorem min_mul_cosh_le_abs_sinh (t : ℝ) :
    min 1 |t| / 5 * (Real.exp t + Real.exp (-t)) ≤ |Real.exp t - Real.exp (-t)| := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht, abs_of_nonneg (by linarith [Real.exp_le_exp.2 (show -t ≤ t by linarith)])]
    exact min_mul_cosh_le_sinh_of_nonneg ht
  · have h := min_mul_cosh_le_sinh_of_nonneg (neg_nonneg.2 ht)
    rw [neg_neg, add_comm (Real.exp (-t))] at h
    rw [abs_of_nonpos ht, abs_of_nonpos (by linarith [Real.exp_le_exp.2 (show t ≤ -t by linarith)])]
    linarith

/-- `φ_a(x) = φ₀(x)e^{−a²/2}e^{ax}` for the `N(a,1)` density `φ_a = gaussianPDFReal a 1`. -/
theorem gpdf_shift (a x : ℝ) :
    gaussianPDFReal a 1 x = gaussianPDFReal 0 1 x * Real.exp (-a ^ 2 / 2) * Real.exp (a * x) := by
  rw [CrossLaws.gpdf_eq, CrossLaws.gpdf_eq, mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
  congr 2
  ring

/-- `min(1,a)·min(1,|x|) ≤ min(1,|ax|)` for `a > 0`. -/
theorem min_mul_min_le {a : ℝ} (ha : 0 < a) (x : ℝ) : min 1 a * min 1 |x| ≤ min 1 |a * x| := by
  have h1 : min 1 a ≤ 1 := min_le_left _ _
  have h2 : min 1 |x| ≤ 1 := min_le_left _ _
  have h3 : min 1 a ≤ a := min_le_right _ _
  have h4 : min 1 |x| ≤ |x| := min_le_right _ _
  have h5 : 0 ≤ min 1 a := le_min zero_le_one ha.le
  have h6 : 0 ≤ min 1 |x| := le_min zero_le_one (abs_nonneg x)
  rw [abs_mul, abs_of_pos ha]
  refine le_min ?_ ?_
  · nlinarith
  · exact mul_le_mul h3 h4 h6 ha.le

/-- The constant `c = (1−w)e^{−a²/2}min(1,a)/(5(w + (1−w)e^{−a²/2}))` of the two-component Gaussian pair. -/
def gaussPairConst (w a : ℝ) : ℝ :=
  (1 - w) * Real.exp (-a ^ 2 / 2) * min 1 a / (5 * (w + (1 - w) * Real.exp (-a ^ 2 / 2)))

/-- `gaussPairConst w a > 0` for `0 ≤ w < 1`, `a > 0`. -/
theorem gaussPairConst_pos {w a : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) (ha : 0 < a) : 0 < gaussPairConst w a := by
  have h1 : 0 < 1 - w := by linarith
  have hk := Real.exp_pos (-a ^ 2 / 2)
  have hm : 0 < min 1 a := lt_min one_pos ha
  unfold gaussPairConst
  have : 0 < w + (1 - w) * Real.exp (-a ^ 2 / 2) := by positivity
  positivity

/-- **The likelihood-ratio bound for the two-component Gaussian pair** `p = wφ₀ + (1−w)φ_a`, `q = wφ₀ + (1−w)φ_{−a}`
(`0 ≤ w < 1`, `a > 0`; `w = 0` is the location pair `N(±a,1)`): `c·min(1,|x|)·(p(x) + q(x)) ≤ |p(x) − q(x)|` for every `x`,
with `c = gaussPairConst w a`. -/
theorem gaussPair_ratio_lower {p q : ℝ → ℝ} {w a : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) (ha : 0 < a)
    (hp : ∀ x, p x = w * gaussianPDFReal 0 1 x + (1 - w) * gaussianPDFReal a 1 x)
    (hq : ∀ x, q x = w * gaussianPDFReal 0 1 x + (1 - w) * gaussianPDFReal (-a) 1 x) (x : ℝ) :
    gaussPairConst w a * min 1 |x| * (p x + q x) ≤ |p x - q x| := by
  set g := gaussianPDFReal 0 1 x with hg
  set k := Real.exp (-a ^ 2 / 2) with hk
  set E := Real.exp (a * x) with hE
  set F := Real.exp (-(a * x)) with hF
  have hg0 : 0 < g := gaussianPDFReal_pos 0 1 x one_ne_zero
  have hk0 : 0 < k := Real.exp_pos _
  have h1w : 0 < 1 - w := by linarith
  have hpa : gaussianPDFReal a 1 x = g * k * E := gpdf_shift a x
  have hna : gaussianPDFReal (-a) 1 x = g * k * F := by
    rw [gpdf_shift, neg_sq, neg_mul]
  have hpx : p x = w * g + (1 - w) * (g * k * E) := by rw [hp, hpa]
  have hqx : q x = w * g + (1 - w) * (g * k * F) := by rw [hq, hna]
  have hS : 2 ≤ E + F := by
    have := Real.add_one_le_exp (a * x); have := Real.add_one_le_exp (-(a * x)); linarith
  have hbase := min_mul_cosh_le_abs_sinh (a * x)
  rw [← hE, ← hF] at hbase
  have hmm := min_mul_min_le ha x
  set D := w + (1 - w) * k with hD
  have hD0 : 0 < D := by positivity
  set n := min 1 |x| with hn
  have hn0 : 0 ≤ n := le_min zero_le_one (abs_nonneg x)
  set m1 := min 1 a with hm1
  have hm10 : 0 < m1 := lt_min one_pos ha
  have hc0 : 0 ≤ gaussPairConst w a := (gaussPairConst_pos hw0 hw1 ha).le
  have hdiff : |p x - q x| = (1 - w) * k * g * |E - F| := by
    rw [hpx, hqx, show w * g + (1 - w) * (g * k * E) - (w * g + (1 - w) * (g * k * F)) =
      (1 - w) * k * g * (E - F) by ring, abs_mul, abs_of_nonneg (by positivity)]
  have hsum : p x + q x ≤ g * (E + F) * D := by
    rw [hpx, hqx, hD]
    have : 2 * w ≤ w * (E + F) := by nlinarith
    nlinarith
  calc gaussPairConst w a * n * (p x + q x) ≤ gaussPairConst w a * n * (g * (E + F) * D) :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg hc0 hn0)
    _ = (1 - w) * k * g * (m1 * n / 5 * (E + F)) := by
        unfold gaussPairConst
        rw [← hk, ← hD, ← hm1]
        field_simp
    _ ≤ (1 - w) * k * g * (min 1 |a * x| / 5 * (E + F)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have : 0 ≤ E + F := by linarith
        exact mul_le_mul_of_nonneg_right (by linarith) this
    _ ≤ (1 - w) * k * g * |E - F| := mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = |p x - q x| := hdiff.symm

end StatFormal.CrossExamples
