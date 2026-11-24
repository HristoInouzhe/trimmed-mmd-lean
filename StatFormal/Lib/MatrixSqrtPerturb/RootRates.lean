import StatFormal.Lib.MatrixSqrtPerturb.Basic
import StatFormal.Lib.MatrixSqrtPerturb.BigOPCalc
import StatFormal.Archive.Wave24f.Statements

/-!
# `O_P` rates for matrix square roots and inverse square roots (untrusted library)

For Hermitian random matrices `R̂_n` with `‖R̂_n − R‖_op = O_P(n^{-1/2})` and `λ • 1 ≤ R` (`λ > 0`):
* `bigOP_sqrt_sub`: `‖R̂_n^{1/2} − R^{1/2}‖_op = O_P(n^{-1/2})`;
* `bigOP_invSqrt_sub`: `‖R̂_n^{-1/2} − R^{-1/2}‖_op = O_P(n^{-1/2})` (frozen `invSqrt`; junk where `R̂_n` is singular,
  which only happens off the event `‖R̂_n − R‖ ≤ λ/2`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator

namespace StatFormal.MatrixSqrtPerturb

open StatFormal.Wave9b (BigOP)

lemma norm_le_of_enorm_le {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ‖M‖ₑ ≤ ENNReal.ofReal c) : ‖M‖ ≤ c := by
  rwa [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff hc] at h

lemma bigOP_sqrt_sub {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
    {R : Matrix (Fin d) (Fin d) ℝ} {Rh : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hR : lam • (1 : Matrix (Fin d) (Fin d) ℝ) ≤ R) (hRh : ∀ n ω, (Rh n ω).IsHermitian)
    (hO : BigOP P (fun n => 1 / Real.sqrt n) (fun n ω => ‖Rh n ω - R‖ₑ)) :
    BigOP P (fun n => 1 / Real.sqrt n) (fun n ω => ‖CFC.sqrt (Rh n ω) - CFC.sqrt R‖ₑ) := by
  refine bigOP_of_le_on rate_nonneg rate_tendsto hO (bigOP_zero _) (δ := lam / 2)
    (C := (Real.sqrt lam)⁻¹) (by positivity) 0 fun n _ ω hsmall => ?_
  have hnorm := norm_le_of_enorm_le (by positivity) hsmall
  have hB0 : 0 ≤ Rh n ω := le_trans (by
    rw [Matrix.nonneg_iff_posSemidef]; exact Matrix.PosSemidef.one.smul (by linarith))
    (half_le_of_near hR (hRh n ω) hnorm)
  have h1 := norm_sqrt_sub_le hlam hR hB0
  rw [norm_sub_rev, norm_sub_rev R] at h1
  rw [add_zero, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (h1.trans (le_of_eq ?_))
  rw [div_eq_inv_mul]

lemma bigOP_invSqrt_sub {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
    {R : Matrix (Fin d) (Fin d) ℝ} {Rh : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hR : lam • (1 : Matrix (Fin d) (Fin d) ℝ) ≤ R) (hRh : ∀ n ω, (Rh n ω).IsHermitian)
    (hO : BigOP P (fun n => 1 / Real.sqrt n) (fun n ω => ‖Rh n ω - R‖ₑ)) :
    BigOP P (fun n => 1 / Real.sqrt n)
      (fun n ω => ‖StatFormal.Wave24f.invSqrt (Rh n ω) - StatFormal.Wave24f.invSqrt R‖ₑ) := by
  refine bigOP_of_le_on rate_nonneg rate_tendsto hO (bigOP_zero _) (δ := lam / 2)
    (C := (Real.sqrt (lam / 2))⁻¹ * (Real.sqrt lam)⁻¹ * (Real.sqrt lam)⁻¹) (by positivity) 0
    fun n _ ω hsmall => ?_
  have hnorm := norm_le_of_enorm_le (by positivity) hsmall
  have h1 := norm_inv_sqrt_sub_le hlam hR (hRh n ω) hnorm
  change ‖(CFC.sqrt (Rh n ω))⁻¹ - (CFC.sqrt R)⁻¹‖ₑ ≤ _
  rw [add_zero, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (h1.trans (le_of_eq ?_))
  ring

end StatFormal.MatrixSqrtPerturb
