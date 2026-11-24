import StatFormal.Lib.RKHSReg.Smooth
import StatFormal.Lib.TIKernel.Spectra

/-!
# Gaussian RKHS functions are smooth and vanish at infinity (library, untrusted)

On a finite-dimensional real inner-product space `V`, the Gaussian profile `e^{−‖x‖²/(2σ²)}` has spectral density
`(2πσ²)^{d/2} e^{−2π²σ²‖ξ‖²}` (`TIKernel.specDens_gauss_eq`), all of whose moments are finite: from `y^m/m! ≤ e^y` at
`y = (b/2) t`, `t^m e^{−bt} ≤ m! (2/b)^m e^{−(b/2)t}` (`pow_mul_exp_neg_le`), and `e^{−c‖ξ‖²}` is integrable on `V`
(`integrable_exp_neg_mul_sq_norm`, from Mathlib's complex Gaussian on inner-product spaces). Hence, for every feature map `φ`
with the Gaussian Gram function, every `x ↦ ⟪g, φ x⟫` is `C^∞` (`gauss_smooth_facts`; Steinwart–Christmann Cor. 4.36) and
tends to `0` at infinity (`gauss_regular_facts`, with `rkhs_vanish_facts`).
-/

noncomputable section
open MeasureTheory Filter Topology Set FourierTransform Complex
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace RealInnerProductSpace ContDiff

set_option linter.unusedSectionVars false

namespace StatFormal.RKHSReg

open StatFormal.Wave31tp StatFormal.TIKernel

/-- Polynomial times Gaussian decay: `t^m e^{−bt} ≤ m! (2/b)^m e^{−(b/2)t}` for `b > 0`, `t ≥ 0`. -/
lemma pow_mul_exp_neg_le {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) (m : ℕ) :
    t ^ m * Real.exp (-b * t) ≤ (m.factorial : ℝ) * (2 / b) ^ m * Real.exp (-(b / 2) * t) := by
  have h := Real.pow_div_factorial_le_exp (x := b / 2 * t) (by positivity) m
  have hf : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast m.factorial_pos
  rw [div_le_iff₀ hf, mul_pow] at h
  have key : t ^ m ≤ (m.factorial : ℝ) * (2 / b) ^ m * Real.exp (b / 2 * t) := by
    have e : t ^ m = (2 / b) ^ m * ((b / 2) ^ m * t ^ m) := by
      rw [← mul_assoc, ← mul_pow, div_mul_div_comm, mul_comm 2 b, div_self (by positivity), one_pow, one_mul]
    rw [e]
    calc (2 / b) ^ m * ((b / 2) ^ m * t ^ m) ≤ (2 / b) ^ m * (Real.exp (b / 2 * t) * (m.factorial : ℝ)) := by gcongr
      _ = (m.factorial : ℝ) * (2 / b) ^ m * Real.exp (b / 2 * t) := by ring
  calc t ^ m * Real.exp (-b * t) ≤ ((m.factorial : ℝ) * (2 / b) ^ m * Real.exp (b / 2 * t)) * Real.exp (-b * t) := by gcongr
    _ = (m.factorial : ℝ) * (2 / b) ^ m * Real.exp (-(b / 2) * t) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

/-- The Gaussian `e^{−b‖v‖²}`, `b > 0`, is integrable on `V`. -/
lemma integrable_exp_neg_mul_sq_norm {b : ℝ} (hb : 0 < b) : Integrable (fun v : V => Real.exp (-b * ‖v‖ ^ 2)) := by
  have hb' : 0 < ((b : ℂ)).re := by rw [Complex.ofReal_re]; exact hb
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V) hb' 0 0).re
  refine h.congr (Eventually.of_forall fun v => ?_)
  simp only [inner_zero_left, Complex.ofReal_zero, mul_zero, add_zero, RCLike.re_to_complex]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.exp_ofReal_re]

/-- **Gaussian moments on `V`**: `‖ξ‖^{2m} e^{−b‖ξ‖²}` is integrable for `b > 0`. -/
lemma integrable_norm_pow_mul_exp {b : ℝ} (hb : 0 < b) (m : ℕ) :
    Integrable (fun ξ : V => ‖ξ‖ ^ (2 * m) * Real.exp (-b * ‖ξ‖ ^ 2)) := by
  refine ((integrable_exp_neg_mul_sq_norm (V := V) (half_pos hb)).const_mul ((m.factorial : ℝ) * (2 / b) ^ m)).mono'
    (by fun_prop : Continuous (fun ξ : V => ‖ξ‖ ^ (2 * m) * Real.exp (-b * ‖ξ‖ ^ 2))).aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), pow_mul]
  exact pow_mul_exp_neg_le hb (by positivity) m

/-- **All moments of the Gaussian spectral density are finite.** -/
lemma integrable_moment_gauss {σ : ℝ} (hσ : 0 < σ) (m : ℕ) :
    Integrable (fun ξ : V => ‖ξ‖ ^ (2 * m) * specDens (fun x : V => Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) ξ) := by
  have h := (integrable_norm_pow_mul_exp (V := V) (b := 2 * Real.pi ^ 2 * σ ^ 2) (by positivity) m).const_mul
    ((2 * Real.pi * σ ^ 2) ^ ((Module.finrank ℝ V : ℝ) / 2))
  refine h.congr (Eventually.of_forall fun ξ => ?_)
  simp only
  rw [specDens_gauss_eq hσ, show -2 * Real.pi ^ 2 * σ ^ 2 * ‖ξ‖ ^ 2 = -(2 * Real.pi ^ 2 * σ ^ 2) * ‖ξ‖ ^ 2 by ring]
  ring

section Gauss

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] {φ : V → H} {σ : ℝ}

/-- **Gaussian RKHS functions are `C^∞`** (Steinwart–Christmann Cor. 4.36; Wave31tp L24 (b)). -/
theorem gauss_smooth_facts (hσ : 0 < σ) (hφ : ∀ x y, ⟪φ x, φ y⟫ = Real.exp (-‖x - y‖ ^ 2 / (2 * σ ^ 2))) (g : H) :
    ContDiff ℝ ∞ (fun x => ⟪g, φ x⟫) :=
  rkhs_smooth_infty (k₀ := fun z : V => Real.exp (-‖z‖ ^ 2 / (2 * σ ^ 2))) hφ (gauss_continuous σ) (gauss_integrable hσ)
    (integrable_moment_gauss hσ) g

/-- **Gaussian RKHS functions are `C^∞` and vanish at infinity** (Remark S5.6 of trimmed-mmd; Wave31tp L30 on any `V`). -/
theorem gauss_regular_facts (hσ : 0 < σ) (hφ : ∀ x y, ⟪φ x, φ y⟫ = Real.exp (-‖x - y‖ ^ 2 / (2 * σ ^ 2))) (g : H) :
    ContDiff ℝ ∞ (fun x => ⟪g, φ x⟫) ∧ Tendsto (fun x => ⟪g, φ x⟫) (comap (fun x => ‖x‖) atTop) (𝓝 0) :=
  ⟨gauss_smooth_facts hσ hφ g,
    rkhs_vanish_facts (k₀ := fun z : V => Real.exp (-‖z‖ ^ 2 / (2 * σ ^ 2))) hφ (gauss_continuous σ)
      (gauss_integrable hσ) g⟩

end Gauss

end StatFormal.RKHSReg
