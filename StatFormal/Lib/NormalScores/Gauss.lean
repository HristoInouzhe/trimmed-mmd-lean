import StatFormal.Lib.MatchedGrid.GaussQuantile
import Mathlib.Probability.Moments.Basic

/-!
# Elementary facts about the standard normal quantile (library, `lem:scores`)

With `Φ = cdf N(0,1)`, `Φ⁻¹` the Tau Ceti quantile, `φ` the density and `m(u) = min(u, 1 − u)`:

* `tail_le`: the Chernoff bound `1 − Φ(y) ≤ exp(−y²/2)` for `y ≥ 0`;
* `phi_quantile_ge`: `m(u)/√(2π) ≤ φ(Φ⁻¹(u))` on `(0,1)` (a derivative-free substitute for the Mills ratio);
* `quantile_sq_le`: `Φ⁻¹(u)² ≤ −2 log m(u)` on `(0,1)`;
* `cdf_sub_ge`: `(b − a) min(φ(a), φ(b)) ≤ Φ(b) − Φ(a)` for `a ≤ b` (the density is quasi-concave);
* `quantile_sub_le`: `c·min(m(u), m(v))·|Φ⁻¹(v) − Φ⁻¹(u)| ≤ |v − u|` with `c = 1/√(2π)` (mean-value bound).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Real
open scoped ENNReal NNReal

namespace StatFormal.NormalScores

open StatFormal.Wave23c (Φn Φn_strictMono Φn_continuous Φn_neg Φn_pos Φn_lt_one Φn_add_Ioi)
open StatFormal.Foundations.MatchedGrid (Φq Φn_Φq Φq_Φn Φq_half Φq_one_sub gauss_Ioc)

/-- `m(u) = min(u, 1 − u)`. -/
def mm (u : ℝ) : ℝ := min u (1 - u)

/-- The standard normal density. -/
abbrev φd (y : ℝ) : ℝ := gaussianPDFReal 0 1 y

/-- The constant `c = 1/√(2π)`. -/
abbrev cG : ℝ := (√(2 * π))⁻¹

lemma cG_pos : 0 < cG := by positivity

lemma φd_eq (y : ℝ) : φd y = cG * exp (-y ^ 2 / 2) := by
  simp [φd, gaussianPDFReal, cG]

lemma φd_neg (y : ℝ) : φd (-y) = φd y := by
  rw [φd_eq, φd_eq, neg_sq]

lemma mm_le_left (u : ℝ) : mm u ≤ u := min_le_left _ _

lemma mm_le_right (u : ℝ) : mm u ≤ 1 - u := min_le_right _ _

lemma mm_one_sub (u : ℝ) : mm (1 - u) = mm u := by
  unfold mm; rw [sub_sub_cancel, min_comm]

lemma mm_pos {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : 0 < mm u := lt_min hu.1 (by linarith [hu.2])

lemma abs_mm_sub_le (u v : ℝ) : |mm u - mm v| ≤ |u - v| := by
  unfold mm
  refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le le_rfl ?_)
  rw [show 1 - u - (1 - v) = -(u - v) by ring, abs_neg]

/-- **Chernoff bound** for the standard normal upper tail. -/
lemma tail_le {y : ℝ} (hy : 0 ≤ y) : 1 - Φn y ≤ exp (-y ^ 2 / 2) := by
  have h1 : 1 - Φn y = (gaussianReal 0 1).real (Ioi y) := by linarith [Φn_add_Ioi y]
  have h2 : (gaussianReal 0 1).real (Ioi y) ≤ (gaussianReal 0 1).real {x | y ≤ id x} :=
    measureReal_mono (fun x (hx : y < x) => le_of_lt hx)
  have h3 := measure_ge_le_exp_mul_mgf (μ := gaussianReal 0 1) (X := id) (t := y) y hy
    (integrable_exp_mul_gaussianReal y)
  rw [mgf_id_gaussianReal] at h3
  calc 1 - Φn y ≤ _ := h1.le.trans h2
    _ ≤ _ := h3
    _ = exp (-y ^ 2 / 2) := by rw [← Real.exp_add]; congr 1; push_cast; ring

lemma quantile_nonpos {u : ℝ} (h0 : 0 < u) (h : u ≤ 1 / 2) : Φq u ≤ 0 := by
  rw [← Φq_half]
  exact Measure.monotoneOn_quantile _ ⟨h0, by linarith⟩ ⟨by norm_num, by norm_num⟩ h

/-- For `u ∈ (0, ½]`, `u ≤ exp(−Φ⁻¹(u)²/2)`. -/
lemma le_exp_quantile {u : ℝ} (h0 : 0 < u) (h : u ≤ 1 / 2) : u ≤ exp (-Φq u ^ 2 / 2) := by
  have hz := quantile_nonpos h0 h
  have e1 : Φn (Φq u) = u := Φn_Φq h0 (by linarith)
  have e2 := Φn_neg (-Φq u)
  rw [neg_neg] at e2
  have e3 := tail_le (y := -Φq u) (by linarith)
  rw [neg_sq] at e3
  linarith

lemma phi_quantile_ge_low {u : ℝ} (h0 : 0 < u) (h : u ≤ 1 / 2) : cG * u ≤ φd (Φq u) := by
  rw [φd_eq]
  exact mul_le_mul_of_nonneg_left (le_exp_quantile h0 h) cG_pos.le

lemma quantile_sq_le_low {u : ℝ} (h0 : 0 < u) (h : u ≤ 1 / 2) : Φq u ^ 2 ≤ -2 * log u := by
  have := Real.log_le_log h0 (le_exp_quantile h0 h)
  rw [Real.log_exp] at this
  linarith

/-- `m(u)/√(2π) ≤ φ(Φ⁻¹(u))` on `(0, 1)`. -/
lemma phi_quantile_ge {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : cG * mm u ≤ φd (Φq u) := by
  rcases le_or_gt u (1 / 2) with h | h
  · exact (mul_le_mul_of_nonneg_left (mm_le_left u) cG_pos.le).trans (phi_quantile_ge_low hu.1 h)
  · have hp0 : 0 < 1 - u := by linarith [hu.2]
    have e : Φq u = -Φq (1 - u) := by
      have := Φq_one_sub (p := 1 - u) hp0 (by linarith [hu.1])
      rwa [sub_sub_cancel] at this
    rw [e, φd_neg]
    exact (mul_le_mul_of_nonneg_left (mm_le_right u) cG_pos.le).trans
      (phi_quantile_ge_low hp0 (by linarith))

/-- `Φ⁻¹(u)² ≤ −2 log m(u)` on `(0, 1)`. -/
lemma quantile_sq_le {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : Φq u ^ 2 ≤ -2 * log (mm u) := by
  rcases le_or_gt u (1 / 2) with h | h
  · have : mm u = u := min_eq_left (by linarith)
    rw [this]; exact quantile_sq_le_low hu.1 h
  · have hp0 : 0 < 1 - u := by linarith [hu.2]
    have e : Φq u = -Φq (1 - u) := by
      have := Φq_one_sub (p := 1 - u) hp0 (by linarith [hu.1])
      rwa [sub_sub_cancel] at this
    have : mm u = 1 - u := min_eq_right (by linarith)
    rw [this, e, neg_sq]
    exact quantile_sq_le_low hp0 (by linarith)

lemma φd_ge_min {a b x : ℝ} (hax : a ≤ x) (hxb : x ≤ b) : min (φd a) (φd b) ≤ φd x := by
  rw [φd_eq, φd_eq, φd_eq]
  rcases le_total 0 x with hx | hx
  · refine (min_le_right _ _).trans (mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) cG_pos.le)
    nlinarith
  · refine (min_le_left _ _).trans (mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) cG_pos.le)
    nlinarith

/-- `(b − a) min(φ(a), φ(b)) ≤ Φ(b) − Φ(a)` for `a ≤ b`. -/
lemma cdf_sub_ge {a b : ℝ} (hab : a ≤ b) : (b - a) * min (φd a) (φd b) ≤ Φn b - Φn a := by
  have hm0 : 0 ≤ min (φd a) (φd b) := le_min (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _)
  have hΦ : 0 ≤ Φn b - Φn a := sub_nonneg.2 (Φn_strictMono.monotone hab)
  have key : ENNReal.ofReal (min (φd a) (φd b)) * volume (Ioc a b) ≤ gaussianReal 0 1 (Ioc a b) := by
    rw [gaussianReal_apply 0 one_ne_zero, ← setLIntegral_const]
    exact setLIntegral_mono (measurable_gaussianPDF 0 1) fun x hx =>
      ENNReal.ofReal_le_ofReal (φd_ge_min hx.1.le hx.2)
  rw [gauss_Ioc, Real.volume_Ioc, ← ENNReal.ofReal_mul hm0] at key
  rw [mul_comm]
  exact (ENNReal.ofReal_le_ofReal_iff hΦ).1 key

lemma quantile_sub_le_of_le {u v : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1) (huv : u ≤ v) :
    cG * min (mm u) (mm v) * (Φq v - Φq u) ≤ v - u := by
  have hab : Φq u ≤ Φq v := Measure.monotoneOn_quantile _ hu hv huv
  have h1 := cdf_sub_ge hab
  rw [Φn_Φq hv.1 hv.2, Φn_Φq hu.1 hu.2] at h1
  have h2 : cG * min (mm u) (mm v) ≤ min (φd (Φq u)) (φd (Φq v)) := by
    rw [mul_min_of_nonneg _ _ cG_pos.le]
    exact min_le_min (phi_quantile_ge hu) (phi_quantile_ge hv)
  calc cG * min (mm u) (mm v) * (Φq v - Φq u) ≤ min (φd (Φq u)) (φd (Φq v)) * (Φq v - Φq u) :=
        mul_le_mul_of_nonneg_right h2 (sub_nonneg.2 hab)
    _ = (Φq v - Φq u) * min (φd (Φq u)) (φd (Φq v)) := mul_comm _ _
    _ ≤ v - u := h1

/-- The mean-value bound `c·min(m(u), m(v))·|Φ⁻¹(v) − Φ⁻¹(u)| ≤ |v − u|`. -/
lemma quantile_sub_le {u v : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1) :
    cG * min (mm u) (mm v) * |Φq v - Φq u| ≤ |v - u| := by
  rcases le_total u v with h | h
  · have hab : Φq u ≤ Φq v := Measure.monotoneOn_quantile _ hu hv h
    rw [abs_of_nonneg (sub_nonneg.2 hab), abs_of_nonneg (sub_nonneg.2 h)]
    exact quantile_sub_le_of_le hu hv h
  · have hab : Φq v ≤ Φq u := Measure.monotoneOn_quantile _ hv hu h
    rw [abs_of_nonpos (sub_nonpos.2 hab), abs_of_nonpos (sub_nonpos.2 h), neg_sub, neg_sub, min_comm]
    exact quantile_sub_le_of_le hv hu h

end StatFormal.NormalScores
