import StatFormal.Wave31tp.Statements
import StatFormal.Lib.FourierOps.Dilate
import Mathlib.Analysis.Distribution.FourierMultiplier

/-!
# The Fourier transform of iterated Laplacians (library, untrusted)

For a smooth compactly supported `b : V → ℂ` on a finite-dimensional real inner-product space and `m ∈ ℕ`,
`𝓕 (Δ^m b)(ξ) = (−4π²‖ξ‖²)^m 𝓕 b(ξ)` (Folland, *Real Analysis*, Thm 8.22), hence for `ξ ≠ 0` the decay bound
`‖𝓕 b(ξ)‖ ≤ ‖Δ^m b‖₁ (4π²‖ξ‖²)^{−m}`. Here `Δ` is Mathlib's Laplacian on functions (`InnerProductSpace.instLaplacian`).

Route: `b` is a Schwartz function (`HasCompactSupport.toSchwartzMap`); on Schwartz space Mathlib proves
`Δ g = −(2π)² 𝓕⁻(‖·‖² 𝓕 g)` (`SchwartzMap.laplacian_eq_fourierMultiplierCLM`); the Schwartz and function Laplacians agree
pointwise (`SchwartzMap.laplacian_apply`), and so do the Schwartz and function Fourier transforms (`SchwartzMap.fourier_coe`).
-/

noncomputable section
open MeasureTheory FourierTransform SchwartzMap Laplacian
open scoped InnerProductSpace RealInnerProductSpace ContDiff

set_option linter.unusedSectionVars false

namespace StatFormal.FourierOps

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

/-- **Fourier transform of the Laplacian of a Schwartz function**: `𝓕 (Δ g)(ξ) = −4π²‖ξ‖² 𝓕 g(ξ)`. -/
theorem fourier_laplacian_schwartz (g : 𝓢(V, ℂ)) (ξ : V) :
    𝓕 (⇑((Laplacian.laplacian : 𝓢(V, ℂ) → 𝓢(V, ℂ)) g) : V → ℂ) ξ = ((-4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) * 𝓕 (⇑g : V → ℂ) ξ := by
  rw [← fourier_coe, ← fourier_coe, laplacian_eq_fourierMultiplierCLM, fourierMultiplierCLM_apply, fourier_smul,
    fourier_fourierInv_eq, smul_apply, smulLeftCLM_apply_apply (Function.hasTemperateGrowth_norm_sq V)]
  rw [Complex.real_smul, Complex.real_smul]
  push_cast
  ring

/-- Iterating: `𝓕 (Δ^m g)(ξ) = (−4π²‖ξ‖²)^m 𝓕 g(ξ)` for a Schwartz `g`. -/
theorem fourier_laplacian_iterate_schwartz (g : 𝓢(V, ℂ)) (m : ℕ) (ξ : V) :
    𝓕 (⇑((Laplacian.laplacian : 𝓢(V, ℂ) → 𝓢(V, ℂ))^[m] g) : V → ℂ) ξ =
      (((-4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ m : ℝ) : ℂ) * 𝓕 (⇑g : V → ℂ) ξ := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', fourier_laplacian_schwartz, ih, pow_succ]
    push_cast
    ring

/-- The Schwartz Laplacian of a Schwartz function, iterated, agrees with the function Laplacian iterated. -/
theorem coe_laplacian_iterate (g : 𝓢(V, ℂ)) (m : ℕ) :
    (⇑((Laplacian.laplacian : 𝓢(V, ℂ) → 𝓢(V, ℂ))^[m] g) : V → ℂ) =
      (Laplacian.laplacian : (V → ℂ) → (V → ℂ))^[m] ⇑g := by
  induction m with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    funext x
    exact laplacian_apply _ x

/-- **Fourier transform of iterated Laplacians** of a smooth compactly supported function:
`𝓕 (Δ^m b)(ξ) = (−4π²‖ξ‖²)^m 𝓕 b(ξ)`. -/
theorem fourier_laplacian_iterate {b : V → ℂ} (hb : ContDiff ℝ ∞ b) (hbs : HasCompactSupport b) (m : ℕ) (ξ : V) :
    𝓕 ((Laplacian.laplacian : (V → ℂ) → (V → ℂ))^[m] b) ξ =
      (((-4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ m : ℝ) : ℂ) * 𝓕 b ξ := by
  have h := fourier_laplacian_iterate_schwartz (hbs.toSchwartzMap hb) m ξ
  rwa [coe_laplacian_iterate] at h

/-- **Decay of the Fourier transform** of a smooth compactly supported function: for `ξ ≠ 0`,
`‖𝓕 b(ξ)‖ ≤ ‖Δ^m b‖₁ · (4π²‖ξ‖²)^{−m}`. -/
theorem norm_fourier_le_laplacian {b : V → ℂ} (hb : ContDiff ℝ ∞ b) (hbs : HasCompactSupport b) (m : ℕ) {ξ : V}
    (hξ : ξ ≠ 0) :
    ‖𝓕 b ξ‖ ≤ (∫ x, ‖((Laplacian.laplacian : (V → ℂ) → (V → ℂ))^[m] b) x‖) *
      ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2)⁻¹) ^ m := by
  set a : ℝ := 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 with ha
  have ha0 : 0 < a := by
    have : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    positivity
  have hL := norm_fourier_le_integral_norm ((Laplacian.laplacian : (V → ℂ) → (V → ℂ))^[m] b) ξ
  rw [fourier_laplacian_iterate hb hbs m ξ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    show -4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 = -a by rw [ha]; ring, neg_pow, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    one_mul, abs_of_pos (pow_pos ha0 m)] at hL
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos ha0 m), mul_comm]
  exact hL

end StatFormal.FourierOps
