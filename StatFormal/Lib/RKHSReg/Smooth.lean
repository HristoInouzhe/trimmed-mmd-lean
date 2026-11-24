import StatFormal.Lib.RKHSReg.Rep
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# Regularity of RKHS functions of a translation-invariant kernel (library, untrusted)

Let `k₀ : V → ℝ` be continuous and integrable, `s = specDens k₀`, and `φ : V → H` a feature map with
`⟪φ x, φ y⟫ = k₀ (x − y)`. By `exists_fourier_weight`, every `f(x) = ⟪g, φ x⟫` is `Re 𝓕 h` with `h ∈ L¹` carrying the
weighted integrability of `s`. Hence:

* **Smoothness from spectral moments** (`rkhs_smooth_facts`; Steinwart–Christmann, Cor. 4.36, in its spectral form): if
  `‖ξ‖^{2m} s(ξ)` is integrable, then every `f` is `C^m`. Indeed `‖ξ‖^{2n} ≤ 1 + ‖ξ‖^{2m}` for `n ≤ m`, so `‖ξ‖^n ‖h‖` is
  integrable for `n ≤ m`, and Mathlib's `Real.contDiff_fourier` differentiates under the integral. All moments finite give
  `C^∞` (`rkhs_smooth_infty`).
* **Decay at infinity** (`rkhs_vanish_facts`; Riemann–Lebesgue, Steinwart–Christmann Lemma 4.23 for `C₀` kernels): every `f`
  tends to `0` along `comap ‖·‖ atTop = cocompact V` (`tendsto_integral_exp_inner_smul_cocompact`).
-/

noncomputable section
open MeasureTheory Filter Topology Set FourierTransform Complex
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace RealInnerProductSpace ContDiff

set_option linter.unusedSectionVars false

namespace StatFormal.RKHSReg

open StatFormal.Wave31tp StatFormal.TIKernel

/-- `t^n ≤ 1 + t^m` for `t ≥ 0` and `n ≤ m`. -/
lemma pow_le_one_add_pow {t : ℝ} (ht : 0 ≤ t) {n m : ℕ} (hnm : n ≤ m) : t ^ n ≤ 1 + t ^ m := by
  rcases le_total t 1 with h | h
  · exact (pow_le_one₀ ht h).trans (le_add_of_nonneg_right (pow_nonneg ht m))
  · exact (pow_le_pow_right₀ h hnm).trans (le_add_of_nonneg_left zero_le_one)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

/-- **Lower spectral moments**: if `s ≥ 0` and `‖ξ‖^{2m} s` are integrable, so is `(‖ξ‖^n)² s` for every `n ≤ m`. -/
lemma integrable_lower_moment {s : V → ℝ} (hsm : Measurable s) (hs0 : ∀ ξ, 0 ≤ s ξ) (hsi : Integrable s) {m n : ℕ}
    (hnm : n ≤ m) (hm : Integrable (fun ξ => ‖ξ‖ ^ (2 * m) * s ξ)) :
    Integrable (fun ξ => (‖ξ‖ ^ n) ^ 2 * s ξ) := by
  refine (hsi.add hm).mono' ((((continuous_norm.pow n).pow 2).measurable.mul hsm).aestronglyMeasurable)
    (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (hs0 ξ)), ← pow_mul, mul_comm n 2]
  have := pow_le_one_add_pow (norm_nonneg ξ) (Nat.mul_le_mul_left 2 hnm)
  simp only [Pi.add_apply]
  nlinarith [hs0 ξ]

/-- `comap ‖·‖ atTop` is the cocompact filter of a finite-dimensional space. -/
lemma comap_norm_atTop_eq_cocompact : comap (fun x : V => ‖x‖) atTop = cocompact V := by
  rw [← Metric.cobounded_eq_cocompact]
  exact comap_norm_atTop

section Reg

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {φ : V → H} {k₀ : V → ℝ} (hφ : ∀ x y, ⟪φ x, φ y⟫ = k₀ (x - y)) (hc : Continuous k₀) (hi : Integrable k₀)
include hφ hc hi

/-- **Spectral moments of order `2m` make every RKHS function `C^m`** (Wave31tp L24 (a)). -/
theorem rkhs_smooth_facts {m : ℕ} (hm : Integrable (fun ξ => ‖ξ‖ ^ (2 * m) * specDens k₀ ξ)) (g : H) :
    ContDiff ℝ m (fun x => ⟪g, φ x⟫) := by
  obtain ⟨hsc, -, hs0, hsi, -, -⟩ := feature_exists_facts hc hi (gram_posdef hφ)
  obtain ⟨h, -, hw, hrep⟩ := exists_fourier_weight hφ hc hi g
  have hfun : (fun x => ⟪g, φ x⟫) = fun x => (𝓕 h x).re := funext hrep
  rw [hfun]
  have hF : ContDiff ℝ (m : ℕ∞) (𝓕 h) := Real.contDiff_fourier fun n hn =>
    hw (fun ξ => ‖ξ‖ ^ n) (continuous_norm.pow n).measurable
      (integrable_lower_moment hsc.measurable hs0 hsi (by exact_mod_cast hn) hm)
  exact Complex.reCLM.contDiff.comp hF

/-- **All spectral moments finite make every RKHS function `C^∞`.** -/
theorem rkhs_smooth_infty (hm : ∀ m : ℕ, Integrable (fun ξ => ‖ξ‖ ^ (2 * m) * specDens k₀ ξ)) (g : H) :
    ContDiff ℝ ∞ (fun x => ⟪g, φ x⟫) :=
  contDiff_infty.2 fun m => rkhs_smooth_facts hφ hc hi (hm m) g

/-- **RKHS functions of an integrable profile vanish at infinity** (Riemann–Lebesgue; Wave31tp L26). -/
theorem rkhs_vanish_facts (g : H) : Tendsto (fun x => ⟪g, φ x⟫) (comap (fun x => ‖x‖) atTop) (𝓝 0) := by
  obtain ⟨h, -, -, hrep⟩ := exists_fourier_weight hφ hc hi g
  have hfun : (fun x => ⟪g, φ x⟫) = fun x => (𝓕 h x).re := funext hrep
  rw [hfun, comap_norm_atTop_eq_cocompact]
  have hRL : Tendsto (𝓕 h) (cocompact V) (𝓝 0) := tendsto_integral_exp_inner_smul_cocompact h
  have h0 := (Complex.continuous_re.tendsto 0).comp hRL
  rw [Complex.zero_re] at h0
  exact h0

end Reg

end StatFormal.RKHSReg
