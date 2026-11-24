import StatFormal.Lib.MomentTrim.Construction

/-!
# Local facts at a crossing point (library, untrusted)

For `e = p − q` continuous at `x₀` with `e ≥ 0` a.e. to the right and `e ≤ 0` a.e. to the left of `x₀`, `e(x₀) = 0`; if moreover
`e′(x₀) = ℓ₀ > 0`, then `e(x) ≥ (ℓ₀/2)(x − x₀)` on `(x₀, x₀ + δ)` and `−e(x) ≥ (ℓ₀/2)(x₀ − x)` on `(x₀ − δ, x₀)` for some `δ > 0`
(the "`p − q ≥ (ℓ₀/2)(x − x₀)` on the right, symmetric on the left" of the proof of Proposition 5.5, S4 :837-843 of the
trimmed-mmd supplement, which makes Proposition S4.14 apply with `r = 1`).

* `eq_zero_of_signs`: `e(x₀) = 0`;
* `exists_linear_lower`: the two one-sided linear lower bounds.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology

namespace StatFormal.MomentTrim

/-- A function continuous at `x₀`, nonnegative a.e. to the right and nonpositive a.e. to the left of `x₀`, vanishes at `x₀`. -/
theorem eq_zero_of_signs {e : ℝ → ℝ} {x₀ : ℝ} (hc : ContinuousAt e x₀) (hR : ∀ᵐ x ∂volume, x₀ < x → 0 ≤ e x)
    (hL : ∀ᵐ x ∂volume, x < x₀ → e x ≤ 0) : e x₀ = 0 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · -- `e < 0` near `x₀`, against `e ≥ 0` a.e. on the right
    obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.mp hc (-e x₀ / 2) (by linarith)
    have hnull : volume (Ioo x₀ (x₀ + δ)) = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hR] with x hx hmem
      have h1 := hx hmem.1
      have h2 := h (x := x) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hmem.1, hmem.2])
      rw [Real.dist_eq, abs_lt] at h2
      linarith [h2.2]
    rw [Real.volume_Ioo] at hnull
    exact (ENNReal.ofReal_pos.mpr (by linarith : (0 : ℝ) < x₀ + δ - x₀)).ne' hnull
  · -- `e > 0` near `x₀`, against `e ≤ 0` a.e. on the left
    obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.mp hc (e x₀ / 2) (by linarith)
    have hnull : volume (Ioo (x₀ - δ) x₀) = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hL] with x hx hmem
      have h1 := hx hmem.2
      have h2 := h (x := x) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hmem.1, hmem.2])
      rw [Real.dist_eq, abs_lt] at h2
      linarith [h2.1]
    rw [Real.volume_Ioo] at hnull
    exact (ENNReal.ofReal_pos.mpr (by linarith : (0 : ℝ) < x₀ - (x₀ - δ))).ne' hnull

/-- **One-sided linear lower bounds** from `e(x₀) = 0` and `e′(x₀) = ℓ₀ > 0`. -/
theorem exists_linear_lower {e : ℝ → ℝ} {x₀ ℓ₀ : ℝ} (hd : HasDerivAt e ℓ₀ x₀) (he : e x₀ = 0) (hℓ : 0 < ℓ₀) :
    ∃ δ > 0, (∀ x ∈ Ioo x₀ (x₀ + δ), ℓ₀ / 2 * (x - x₀) ≤ e x) ∧ (∀ x ∈ Ioo (x₀ - δ) x₀, ℓ₀ / 2 * (x₀ - x) ≤ -e x) := by
  obtain ⟨δ, hδ, h⟩ := exists_deriv_bound hd he (half_pos hℓ)
  refine ⟨δ, hδ, fun x hx => ?_, fun x hx => ?_⟩
  · have h1 := h x (by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2])
    rw [abs_of_pos (by linarith [hx.1] : 0 < x - x₀), abs_le] at h1
    linarith [h1.1]
  · have h1 := h x (by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2])
    rw [abs_of_neg (by linarith [hx.2] : x - x₀ < 0), abs_le] at h1
    linarith [h1.2]

end StatFormal.MomentTrim
