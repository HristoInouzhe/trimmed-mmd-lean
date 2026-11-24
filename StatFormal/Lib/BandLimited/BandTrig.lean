import StatFormal.Wave31tq.Statements
import StatFormal.Lib.BandLimited.TrigInt
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The band-limited function `h(t) = cos(t/2)/(π² − t²)` as a trigonometric integral (library, untrusted)

With `a = 1/(4π)` (`bandA`), product-to-sum and `∫_{−a}^{a} cos(kw) dw = 2 sin(ka)/k`:

* `∫_{−a}^{a} cos(2πtw) cos(2π²w) dw = h(t)` (with the continuous value `h(±π) = 1/(4π)`, the frozen `Wave31tq.bandH`);
* `∫_{−a}^{a} sin(2πtw) sin(2π²w) dw = t h(t)/π`;
* `∫_{−a}^{a} cos²(2π²w) dw = ∫_{−a}^{a} sin²(2π²w) dw = a` (`sin(4π²a) = sin π = 0`).

Consequences: `h` is continuous, even, and `|h| ≤ 2a = 1/(2π)`. In Mathlib's convention (`𝓕 f(t) = ∫ e^{−2πiwt} f(w) dw`) these
are the transforms of `w ↦ cos(2π²w)` and `w ↦ −2π² sin(2π²w)` on `[−a, a]` (the paper's `ĥ(ξ) = cos(πξ)` on `[−1/2, 1/2]` and
its derivative, at `ξ = 2πw`). Used for Q15 of the trimmed-MMD formalization (S4 :664-670).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set

namespace StatFormal.BandLimited

open StatFormal.Wave31tq

/-- The half-width `a = 1/(4π)` of the band in Mathlib's frequency variable. -/
def bandA : ℝ := (4 * Real.pi)⁻¹

theorem bandA_pos : 0 < bandA := by unfold bandA; positivity

/-- `2π²a = π/2`. -/
theorem two_pi_sq_mul_bandA : 2 * Real.pi ^ 2 * bandA = Real.pi / 2 := by
  unfold bandA; field_simp; ring

/-- `∫_{−a}^{a} cos(kw) dw` at `k = 4π²` vanishes (`sin π = 0`). -/
theorem integral_cos_four_pi_sq : ∫ w in -bandA..bandA, Real.cos (4 * Real.pi ^ 2 * w) = 0 := by
  rw [integral_cos_mul_symm (by positivity), show 4 * Real.pi ^ 2 * bandA = Real.pi by unfold bandA; field_simp,
    Real.sin_pi]
  simp

/-- The two cosine integrals of the product-to-sum formulas, at `t ≠ ±π`. -/
theorem integral_cos_sub (t : ℝ) (ht : t ≠ Real.pi) :
    ∫ w in -bandA..bandA, Real.cos (2 * Real.pi * (t - Real.pi) * w) = -Real.cos (t / 2) / (Real.pi * (t - Real.pi)) := by
  have hk : 2 * Real.pi * (t - Real.pi) ≠ 0 := mul_ne_zero (by positivity) (sub_ne_zero.2 ht)
  rw [integral_cos_mul_symm hk, show 2 * Real.pi * (t - Real.pi) * bandA = t / 2 - Real.pi / 2 by unfold bandA; field_simp; ring,
    Real.sin_sub_pi_div_two]
  have : t - Real.pi ≠ 0 := sub_ne_zero.2 ht
  field_simp

theorem integral_cos_add (t : ℝ) (ht : t ≠ -Real.pi) :
    ∫ w in -bandA..bandA, Real.cos (2 * Real.pi * (t + Real.pi) * w) = Real.cos (t / 2) / (Real.pi * (t + Real.pi)) := by
  have htp : t + Real.pi ≠ 0 := fun h => ht (by linarith)
  have hk : 2 * Real.pi * (t + Real.pi) ≠ 0 := mul_ne_zero (by positivity) htp
  rw [integral_cos_mul_symm hk, show 2 * Real.pi * (t + Real.pi) * bandA = t / 2 + Real.pi / 2 by unfold bandA; field_simp; ring,
    Real.sin_add_pi_div_two]
  field_simp

/-- At `t = π` (resp. `t = −π`) the integral `∫ cos(2π(t ∓ π)w)` is `2a`, and `∫ cos(2π(t ± π)w) = 0`. -/
theorem integral_cos_sub_at_pi : ∫ w in -bandA..bandA, Real.cos (2 * Real.pi * (Real.pi - Real.pi) * w) = 2 * bandA := by
  rw [sub_self, mul_zero]; exact integral_cos_zero_mul_symm _

theorem integral_cos_add_at_pi : ∫ w in -bandA..bandA, Real.cos (2 * Real.pi * (Real.pi + Real.pi) * w) = 0 := by
  rw [show 2 * Real.pi * (Real.pi + Real.pi) = 4 * Real.pi ^ 2 by ring]; exact integral_cos_four_pi_sq

theorem integral_cos_sub_at_neg_pi : ∫ w in -bandA..bandA, Real.cos (2 * Real.pi * (-Real.pi - Real.pi) * w) = 0 := by
  have : ∀ w, Real.cos (2 * Real.pi * (-Real.pi - Real.pi) * w) = Real.cos (4 * Real.pi ^ 2 * w) := fun w => by
    rw [← Real.cos_neg]; ring_nf
  simp_rw [this]; exact integral_cos_four_pi_sq

theorem integral_cos_add_at_neg_pi : ∫ w in -bandA..bandA, Real.cos (2 * Real.pi * (-Real.pi + Real.pi) * w) = 2 * bandA := by
  rw [neg_add_cancel, mul_zero]; exact integral_cos_zero_mul_symm _

/-- Continuity of the cosines (for interval integrability). -/
theorem intervalIntegrable_cos_mul (k : ℝ) : IntervalIntegrable (fun w => Real.cos (k * w)) volume (-bandA) bandA :=
  (by fun_prop : Continuous fun w => Real.cos (k * w)).intervalIntegrable _ _

/-- `cos(2πtw) cos(2π²w) = (cos(2π(t−π)w) + cos(2π(t+π)w))/2`. -/
theorem cos_mul_cos_band (t w : ℝ) :
    Real.cos (2 * Real.pi * t * w) * Real.cos (2 * Real.pi ^ 2 * w) =
      (Real.cos (2 * Real.pi * (t - Real.pi) * w) + Real.cos (2 * Real.pi * (t + Real.pi) * w)) / 2 := by
  rw [show 2 * Real.pi * (t - Real.pi) * w = 2 * Real.pi * t * w - 2 * Real.pi ^ 2 * w by ring,
    show 2 * Real.pi * (t + Real.pi) * w = 2 * Real.pi * t * w + 2 * Real.pi ^ 2 * w by ring, Real.cos_sub, Real.cos_add]
  ring

/-- `sin(2πtw) sin(2π²w) = (cos(2π(t−π)w) − cos(2π(t+π)w))/2`. -/
theorem sin_mul_sin_band (t w : ℝ) :
    Real.sin (2 * Real.pi * t * w) * Real.sin (2 * Real.pi ^ 2 * w) =
      (Real.cos (2 * Real.pi * (t - Real.pi) * w) - Real.cos (2 * Real.pi * (t + Real.pi) * w)) / 2 := by
  rw [show 2 * Real.pi * (t - Real.pi) * w = 2 * Real.pi * t * w - 2 * Real.pi ^ 2 * w by ring,
    show 2 * Real.pi * (t + Real.pi) * w = 2 * Real.pi * t * w + 2 * Real.pi ^ 2 * w by ring, Real.cos_sub, Real.cos_add]
  ring

/-- `t² = π²` iff `t = π` or `t = −π`. -/
theorem sq_eq_pi_sq_iff (t : ℝ) : t ^ 2 = Real.pi ^ 2 ↔ t = Real.pi ∨ t = -Real.pi := sq_eq_sq_iff_eq_or_eq_neg

/-- **`h` as a cosine integral**: `∫_{−a}^{a} cos(2πtw) cos(2π²w) dw = h(t)`. -/
theorem integral_cos_cos_band (t : ℝ) :
    ∫ w in -bandA..bandA, Real.cos (2 * Real.pi * t * w) * Real.cos (2 * Real.pi ^ 2 * w) = bandH t := by
  simp_rw [cos_mul_cos_band]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add (intervalIntegrable_cos_mul _) (intervalIntegrable_cos_mul _)]
  unfold bandH
  by_cases h1 : t = Real.pi
  · subst h1
    rw [ite_eq_left rfl, integral_cos_sub_at_pi, integral_cos_add_at_pi]; unfold bandA; ring
  by_cases h2 : t = -Real.pi
  · subst h2
    rw [ite_eq_left (by ring), integral_cos_sub_at_neg_pi, integral_cos_add_at_neg_pi]; unfold bandA; ring
  rw [ite_eq_right (fun h => ((sq_eq_pi_sq_iff t).1 h).elim h1 h2), integral_cos_sub t h1, integral_cos_add t h2]
  have hm : t - Real.pi ≠ 0 := sub_ne_zero.2 h1
  have hp : t + Real.pi ≠ 0 := fun h => h2 (by linarith)
  have hd : Real.pi ^ 2 - t ^ 2 ≠ 0 := fun h => by
    have : (t - Real.pi) * (t + Real.pi) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · exact hm h
    · exact hp h
  field_simp
  ring

/-- **`t h(t)/π` as a sine integral**: `∫_{−a}^{a} sin(2πtw) sin(2π²w) dw = t h(t)/π`. -/
theorem integral_sin_sin_band (t : ℝ) :
    ∫ w in -bandA..bandA, Real.sin (2 * Real.pi * t * w) * Real.sin (2 * Real.pi ^ 2 * w) = t * bandH t / Real.pi := by
  simp_rw [sin_mul_sin_band]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub (intervalIntegrable_cos_mul _) (intervalIntegrable_cos_mul _)]
  unfold bandH
  by_cases h1 : t = Real.pi
  · subst h1
    rw [ite_eq_left rfl, integral_cos_sub_at_pi, integral_cos_add_at_pi]; unfold bandA; field_simp; ring
  by_cases h2 : t = -Real.pi
  · subst h2
    rw [ite_eq_left (by ring), integral_cos_sub_at_neg_pi, integral_cos_add_at_neg_pi]; unfold bandA; field_simp; ring
  rw [ite_eq_right (fun h => ((sq_eq_pi_sq_iff t).1 h).elim h1 h2), integral_cos_sub t h1, integral_cos_add t h2]
  have hm : t - Real.pi ≠ 0 := sub_ne_zero.2 h1
  have hp : t + Real.pi ≠ 0 := fun h => h2 (by linarith)
  have hd : Real.pi ^ 2 - t ^ 2 ≠ 0 := fun h => by
    have : (t - Real.pi) * (t + Real.pi) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · exact hm h
    · exact hp h
  field_simp
  ring

/-- `∫_{−a}^{a} cos²(2π²w) dw = a`. -/
theorem integral_cos_sq_band : ∫ w in -bandA..bandA, Real.cos (2 * Real.pi ^ 2 * w) ^ 2 = bandA := by
  have : ∀ w, Real.cos (2 * Real.pi ^ 2 * w) ^ 2 = (1 + Real.cos (4 * Real.pi ^ 2 * w)) / 2 := fun w => by
    rw [Real.cos_sq, show 2 * (2 * Real.pi ^ 2 * w) = 4 * Real.pi ^ 2 * w by ring]; ring
  simp_rw [this]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add intervalIntegrable_const (intervalIntegrable_cos_mul _),
    integral_cos_four_pi_sq]
  simp

/-- `∫_{−a}^{a} sin²(2π²w) dw = a`. -/
theorem integral_sin_sq_band : ∫ w in -bandA..bandA, Real.sin (2 * Real.pi ^ 2 * w) ^ 2 = bandA := by
  have : ∀ w, Real.sin (2 * Real.pi ^ 2 * w) ^ 2 = (1 - Real.cos (4 * Real.pi ^ 2 * w)) / 2 := fun w => by
    rw [Real.sin_sq, Real.cos_sq, show 2 * (2 * Real.pi ^ 2 * w) = 4 * Real.pi ^ 2 * w by ring]; ring
  simp_rw [this]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub intervalIntegrable_const (intervalIntegrable_cos_mul _),
    integral_cos_four_pi_sq]
  simp

/-- `h` is continuous (a parametric integral of a continuous function). -/
theorem continuous_bandH : Continuous bandH := by
  have h : bandH = fun t => ∫ w in -bandA..bandA, Real.cos (2 * Real.pi * t * w) * Real.cos (2 * Real.pi ^ 2 * w) :=
    funext fun t => (integral_cos_cos_band t).symm
  rw [h]
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) _ _

/-- `h` is even. -/
theorem bandH_neg (t : ℝ) : bandH (-t) = bandH t := by
  unfold bandH
  rw [neg_sq, neg_div, Real.cos_neg]

/-- `|h| ≤ 2a = 1/(2π)`. -/
theorem abs_bandH_le (t : ℝ) : |bandH t| ≤ 2 * bandA := by
  rw [← integral_cos_cos_band t]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := -bandA) (b := bandA) (C := 1)
    (f := fun w => Real.cos (2 * Real.pi * t * w) * Real.cos (2 * Real.pi ^ 2 * w)) (fun w _ => by
      rw [Real.norm_eq_abs, abs_mul]
      simpa using mul_le_mul (Real.abs_cos_le_one (2 * Real.pi * t * w)) (Real.abs_cos_le_one (2 * Real.pi ^ 2 * w))
        (abs_nonneg _) zero_le_one)
  rw [Real.norm_eq_abs] at this
  have hA := bandA_pos
  rw [show |bandA - -bandA| = 2 * bandA by rw [abs_of_pos (by linarith)]; ring] at this
  linarith

end StatFormal.BandLimited
