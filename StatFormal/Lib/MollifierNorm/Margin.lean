import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Mollifiers and the margin arithmetic of the Sobolev corollary (library, untrusted)

* `exists_mollifier`: on a finite-dimensional real inner-product space there is a smooth probability density supported in the
  closed unit ball (a normalized `ContDiffBump` with radii `1/2 < 1`).
* `exists_nat_four_mul_gt`: for every `s` there is `m ∈ ℕ` with `4m > 2s − 1`.
* `margin_rpow_eq`: the balance of error and norm in the proof of Corollary S4.11 of trimmed-mmd: with the width
  `w = (ε/A)^{1/(r+1)}`, `c^{1/2}(ε/2)/{K w^{1−2s}}^{1/2} = c^{1/2}/(2K^{1/2}) · A^{1−γ} · ε^γ`, `γ = 1 + (2s−1)/{2(r+1)}`.
* `log_div_le_rpow`: `log⁺(4C/ε) ≤ (C/(2ℓ))^β/β · (ε/(8ℓ))^{−β}`, the logarithmic radius is dominated by a power of `1/ε`.
-/

noncomputable section
open MeasureTheory Set Metric
open scoped ContDiff

namespace StatFormal.MollifierNorm

/-- **A mollifier**: a smooth nonnegative function of integral one supported in the closed unit ball. -/
theorem exists_mollifier (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] :
    ∃ b : V → ℝ, ContDiff ℝ ∞ b ∧ (∀ x, 0 ≤ b x) ∧ ∫ x, b x = 1 ∧ Function.support b ⊆ closedBall 0 1 := by
  let f : ContDiffBump (0 : V) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  refine ⟨f.normed volume, f.contDiff_normed (n := ⊤), f.nonneg_normed, f.integral_normed, ?_⟩
  rw [f.support_normed_eq]
  exact ball_subset_closedBall

/-- For every real `s` there is a natural `m` with `2s − 1 < 4m`. -/
theorem exists_nat_four_mul_gt (s : ℝ) : ∃ m : ℕ, 2 * s - 1 < 4 * m := by
  obtain ⟨m, hm⟩ := exists_nat_gt s
  refine ⟨m, ?_⟩
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

/-- **The balance of the corollary**: with `w = (ε/A)^{1/(r+1)}` and `γ = 1 + (2s−1)/(2(r+1))`,
`√c (ε/2) / √(K w^{1−2s}) = √c/(2√K) · A^{1−γ} · ε^γ`. -/
theorem margin_rpow_eq {c K A s r ε : ℝ} (hK : 0 < K) (hA : 0 < A) (hr : 0 < r) (hε : 0 < ε) :
    √c * (ε / 2) / √(K * ((ε / A) ^ (1 / (r + 1))) ^ (1 - 2 * s)) =
      √c / (2 * √K) * A ^ (1 - (1 + (2 * s - 1) / (2 * (r + 1)))) * ε ^ (1 + (2 * s - 1) / (2 * (r + 1))) := by
  have hεA : 0 < ε / A := div_pos hε hA
  set t : ℝ := (1 - 2 * s) / (2 * (r + 1)) with ht
  have h1 : √(K * ((ε / A) ^ (1 / (r + 1))) ^ (1 - 2 * s)) = √K * (ε / A) ^ t := by
    rw [Real.sqrt_mul hK.le, ← Real.rpow_mul hεA.le, Real.sqrt_eq_rpow ((ε / A) ^ _), ← Real.rpow_mul hεA.le]
    congr 2
    rw [ht]; field_simp
  have h2 : 1 - (1 + (2 * s - 1) / (2 * (r + 1))) = t := by rw [ht]; field_simp; ring
  have h3 : 1 + (2 * s - 1) / (2 * (r + 1)) = 1 - t := by rw [ht]; field_simp; ring
  rw [h1, h2, h3, Real.div_rpow hε.le hA.le, Real.rpow_sub hε, Real.rpow_one]
  have : 0 < ε ^ t := Real.rpow_pos_of_pos hε t
  have : 0 < A ^ t := Real.rpow_pos_of_pos hA t
  have : 0 < √K := Real.sqrt_pos.2 hK
  field_simp

/-- **The logarithmic radius is dominated by a power**: for `C, ℓ, β, ε > 0`,
`max 0 (log(4C/ε)) ≤ (C/(2ℓ))^β / β · (ε/(8ℓ))^{−β}`. -/
theorem log_div_le_rpow {C ℓ β ε : ℝ} (hC : 0 < C) (hℓ : 0 < ℓ) (hβ : 0 < β) (hε : 0 < ε) :
    max 0 (Real.log (4 * C / ε)) ≤ (C / (2 * ℓ)) ^ β / β * (ε / (8 * ℓ)) ^ (-β) := by
  have hx : 0 < 4 * C / ε := by positivity
  have hrhs : (4 * C / ε) ^ β / β = (C / (2 * ℓ)) ^ β / β * (ε / (8 * ℓ)) ^ (-β) := by
    have h48 : 4 * C / ε = C / (2 * ℓ) * (ε / (8 * ℓ))⁻¹ := by field_simp; ring
    rw [h48, Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow (by positivity),
      ← Real.rpow_neg (by positivity)]
    ring
  rw [← hrhs]
  exact max_le (by positivity) (Real.log_le_rpow_div hx.le hβ)

end StatFormal.MollifierNorm
