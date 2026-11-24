import StatFormal.Wave31tq.Statements
import StatFormal.Wave31tp.Proofs
import StatFormal.Lib.MomentTrim.Signed

/-!
# Wave 31tq, route T (Q18): eq:newmomentdecay in the angular convention (untrusted)

`Claims.momentdecay_angular`. (a) The Jordan parts `ν⁺, ν⁻` of `ν` are carried by `[x₀ − W, x₀ + W]` (`|ν| = ν⁺ + ν⁻`) and
have equal moments (`sMoment ν x₀ j = 0`), so the certified L5 `Wave31tp.moment_decay` applies at the frequency `ξ/2π`.
(b) `ν⁺ + Q′ = ν⁻ + P′` (`Lib/MomentTrim/Signed`), so the transforms add up (`integral_jordan_sub` with the bounded
character `x ↦ 𝐞(−xξ/2π)`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped FourierTransform InnerProductSpace

namespace StatFormal.Wave31tq.RouteT

open StatFormal.Wave31tp

/-- The character `x ↦ 𝐞(−⟪x, ξ⟫)` is integrable against every finite measure on `ℝ`. -/
theorem integrable_char (μ : Measure ℝ) [IsFiniteMeasure μ] (ξ : ℝ) :
    Integrable (fun x : ℝ => (𝐞 (-⟪x, ξ⟫_ℝ) : ℂ)) μ := by
  refine Integrable.of_bound ?_ 1 (ae_of_all _ fun x => by simp)
  exact (Continuous.aestronglyMeasurable (by simp only [Real.fourierChar_apply]; fun_prop))

/-- `ftMeasA` of the Jordan parts of `μ₁ − μ₂`: `ν̂⁺ − ν̂⁻ = μ̂₁ − μ̂₂`. -/
theorem ftSigned_sub (μ₁ μ₂ : Measure ℝ) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] (ξ : ℝ) :
    ftSigned (μ₁.toSignedMeasure - μ₂.toSignedMeasure) ξ = ftMeasA μ₁ ξ - ftMeasA μ₂ ξ := by
  unfold ftSigned ftMeasA ftMeas
  exact MomentTrim.integral_jordan_sub μ₁ μ₂ (integrable_char μ₁ _) (integrable_char μ₂ _)

/-- `2π · |ξ/2π| = |ξ|`. -/
theorem two_pi_abs_inv_smul (ξ : ℝ) : 2 * Real.pi * |(2 * Real.pi)⁻¹ • ξ| = |ξ| := by
  rw [smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr (by positivity : (0 : ℝ) < 2 * Real.pi)), ← mul_assoc,
    mul_inv_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0), one_mul]

/-- Q18 (a): the moment-decay bound for a signed measure through its Jordan parts. -/
theorem momentdecay_signed (ν : SignedMeasure ℝ) (x₀ W : ℝ) (N : ℕ) (hW : 0 ≤ W) (hN : 1 ≤ N)
    (hsupp : ν.totalVariation (Icc (x₀ - W) (x₀ + W))ᶜ = 0) (hmom : ∀ j < N, sMoment ν x₀ j = 0) (ξ : ℝ) :
    ‖ftSigned ν ξ‖ ≤ (ν.totalVariation univ).toReal * min 1 ((|ξ| * W) ^ N / N.factorial) := by
  set νp := ν.toJordanDecomposition.posPart
  set νn := ν.toJordanDecomposition.negPart
  have hsupp' : νp (Icc (x₀ - W) (x₀ + W))ᶜ + νn (Icc (x₀ - W) (x₀ + W))ᶜ = 0 := by
    rw [← Measure.add_apply]; exact hsupp
  rw [add_eq_zero] at hsupp'
  have hmom' : ∀ j < N, ∫ x, (x - x₀) ^ j ∂νp = ∫ x, (x - x₀) ^ j ∂νn := fun j hj =>
    sub_eq_zero.mp (hmom j hj)
  have h := Wave31tp.moment_decay νp νn x₀ W N hW hN hsupp'.1 hsupp'.2 hmom' ((2 * Real.pi)⁻¹ • ξ)
  rw [two_pi_abs_inv_smul] at h
  have htv : (ν.totalVariation univ).toReal = νp.real univ + νn.real univ := by
    rw [SignedMeasure.totalVariation, Measure.add_apply, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    rfl
  rw [htv]
  exact h

/-- Q18 `momentdecay_angular`. -/
theorem momentdecay_angular_route : Claims.momentdecay_angular := by
  refine ⟨fun ν x₀ W N hW hN hsupp hmom ξ => momentdecay_signed ν x₀ W N hW hN hsupp hmom ξ, ?_⟩
  intro P' Q' _ _
  funext ξ
  exact ftSigned_sub P' Q' ξ

end StatFormal.Wave31tq.RouteT
