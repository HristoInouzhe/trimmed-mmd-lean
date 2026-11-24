import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Eventual inequalities for a logarithmic rate (library, untrusted)

Real-number facts for the step of the proof of Proposition S4.8 (ii) of the trimmed-mmd supplement: "`t_{n,m} ≤ C_t(log n/n)^{1/2}`
… `log(1/t_{n,m}) ≥ ½ log n − ½ log log n − log C_t`, which exceeds `(c′/c) log n` for all large `n`, because `c′/c < ½`", in the
equivalent form `C √((A + b log M)/M) ≤ M^{−θ}` for `θ < ½` and all large `M`:

* `eventually_lt_log`: `a < log M` for all large `M`;
* `eventually_mul_add_log_le_rpow`: `K(A + b log M) ≤ M^γ` for all large `M`, any `K, A, b` and `γ > 0`
  (Mathlib's `isLittleO_log_rpow_atTop`);
* `eventually_sqrt_log_div_le_rpow`: `K √((A + b log M)/M) ≤ M^{−θ}` for all large `M`, `K ≥ 0`, `θ < ½`.
-/

set_option linter.style.longLine false

noncomputable section

namespace StatFormal.ExpMargin

open Real Filter

/-- `a < log M` for all large `M`. -/
theorem eventually_lt_log (a : ℝ) : ∀ᶠ M : ℝ in atTop, a < Real.log M :=
  Real.tendsto_log_atTop.eventually_gt_atTop a

/-- `K(A + b log M) ≤ M^γ` for all large `M`, for any constants `K, A, b` and `γ > 0`. -/
theorem eventually_mul_add_log_le_rpow (K A b : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ M : ℝ in atTop, K * (A + b * Real.log M) ≤ M ^ γ := by
  set C := |K| * |b| + 1 with hC
  have hC0 : 0 < C := by positivity
  have h1 := (isLittleO_log_rpow_atTop hγ).bound (c := 1 / (2 * C)) (by positivity)
  have h2 := (tendsto_rpow_atTop hγ).eventually_ge_atTop (2 * |K * A|)
  have h3 := eventually_gt_atTop (0 : ℝ)
  filter_upwards [h1, h2, h3] with M hM1 hM2 hM3
  have hMγ : 0 ≤ M ^ γ := Real.rpow_nonneg hM3.le γ
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hMγ] at hM1
  have e0 : K * (A + b * Real.log M) = K * A + K * b * Real.log M := by ring
  have e1 : K * A ≤ |K * A| := le_abs_self _
  have e2 : K * b * Real.log M ≤ |K| * |b| * |Real.log M| := by
    rw [← abs_mul, ← abs_mul]; exact le_abs_self _
  have e3 : |K| * |b| * |Real.log M| ≤ |K| * |b| * (1 / (2 * C) * M ^ γ) :=
    mul_le_mul_of_nonneg_left hM1 (by positivity)
  have e4 : |K| * |b| * (1 / (2 * C) * M ^ γ) ≤ C * (1 / (2 * C) * M ^ γ) :=
    mul_le_mul_of_nonneg_right (by rw [hC]; linarith) (by positivity)
  have e5 : C * (1 / (2 * C) * M ^ γ) = M ^ γ / 2 := by field_simp
  linarith

/-- **`K √((A + b log M)/M) ≤ M^{−θ}` for all large `M`**, for `K ≥ 0`, any `A, b`, and `θ < ½`. -/
theorem eventually_sqrt_log_div_le_rpow {K : ℝ} (hK : 0 ≤ K) (A b : ℝ) {θ : ℝ} (hθ : θ < 1 / 2) :
    ∀ᶠ M : ℝ in atTop, K * √((A + b * Real.log M) / M) ≤ M ^ (-θ) := by
  have hγ : 0 < 1 - 2 * θ := by linarith
  filter_upwards [eventually_mul_add_log_le_rpow (K ^ 2) A b hγ, eventually_gt_atTop (0 : ℝ)] with M hM hM0
  have hr : 0 ≤ M ^ (-θ) := Real.rpow_nonneg hM0.le _
  have hsq : K * √((A + b * Real.log M) / M) = √(K ^ 2 * ((A + b * Real.log M) / M)) := by
    rw [Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq hK]
  have hpow : (M ^ (-θ)) ^ 2 * M = M ^ (1 - 2 * θ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM0.le, ← Real.rpow_add_one hM0.ne']
    congr 1
    push_cast
    ring
  rw [hsq, ← Real.sqrt_sq hr]
  apply Real.sqrt_le_sqrt
  rw [← mul_div_assoc, div_le_iff₀ hM0, hpow]
  exact hM

end StatFormal.ExpMargin
