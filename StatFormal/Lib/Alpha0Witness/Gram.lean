import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Feature maps through their Gram function: continuity and mean embeddings (library)

Library component (untrusted). `φ : X → H` a feature map into a real inner-product space, `k(a, x) = ⟪φ a, φ x⟫` its Gram function.

* `norm_sub_eq_sqrt_gram`: `‖φ x − φ a‖ = √(k(x,x) − 2k(x,a) + k(a,a))`;
* `continuous_of_gram`: a feature map with a continuous Gram function is continuous (so, on a second-countable space, strongly
  measurable);
* `inner_integral_left`, `inner_integral_integral`: for an integrable `φ`, `⟪∫ φ dP, w⟫ = ∫ ⟪φ a, w⟫ dP(a)` and
  `⟪∫ φ dP, ∫ φ dQ⟫ = ∫∫ k(a,b) dQ(b) dP(a)`;
* `inner_meanEmb_sub`, `norm_sq_meanEmb_sub`: the witness function `⟪μ_P − μ_Q, φ z⟫ = ∫ k(a,z) dP − ∫ k(b,z) dQ` and
  `‖μ_P − μ_Q‖² = ∫∫ k dP dP − 2 ∫∫ k dQ dP + ∫∫ k dQ dQ` (the kernel form of the squared MMD).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Alpha0Witness

variable {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `‖φ x − φ a‖ = √(k(x,x) − 2k(x,a) + k(a,a))`. -/
theorem norm_sub_eq_sqrt_gram (φ : X → H) (x a : X) :
    ‖φ x - φ a‖ = √(⟪φ x, φ x⟫_ℝ - 2 * ⟪φ x, φ a⟫_ℝ + ⟪φ a, φ a⟫_ℝ) := by
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, ← norm_sub_sq_real, Real.sqrt_sq (norm_nonneg _)]

/-- **A feature map with a continuous Gram function is continuous.** -/
theorem continuous_of_gram [TopologicalSpace X] {φ : X → H} (hk : Continuous fun p : X × X => ⟪φ p.1, φ p.2⟫_ℝ) :
    Continuous φ := by
  rw [continuous_iff_continuousAt]
  intro a
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hc : Continuous fun x => √(⟪φ x, φ x⟫_ℝ - 2 * ⟪φ x, φ a⟫_ℝ + ⟪φ a, φ a⟫_ℝ) := by
    have h1 : Continuous fun x => ⟪φ x, φ x⟫_ℝ := hk.comp (continuous_id.prodMk continuous_id)
    have h2 : Continuous fun x => ⟪φ x, φ a⟫_ℝ := hk.comp (continuous_id.prodMk continuous_const)
    exact ((h1.sub (continuous_const.mul h2)).add continuous_const).sqrt
  have h0 : √(⟪φ a, φ a⟫_ℝ - 2 * ⟪φ a, φ a⟫_ℝ + ⟪φ a, φ a⟫_ℝ) = 0 := by
    rw [show ⟪φ a, φ a⟫_ℝ - 2 * ⟪φ a, φ a⟫_ℝ + ⟪φ a, φ a⟫_ℝ = 0 by ring, Real.sqrt_zero]
  have ht := hc.tendsto a
  rw [h0] at ht
  exact ht.congr fun x => (norm_sub_eq_sqrt_gram φ x a).symm

section Integral

variable [MeasurableSpace X] [CompleteSpace H]

/-- `⟪∫ φ dP, w⟫ = ∫ ⟪φ a, w⟫ dP(a)` for integrable `φ`. -/
theorem inner_integral_left {P : Measure X} {φ : X → H} (hφ : Integrable φ P) (w : H) :
    ⟪∫ a, φ a ∂P, w⟫_ℝ = ∫ a, ⟪φ a, w⟫_ℝ ∂P := by
  rw [real_inner_comm, ← integral_inner hφ w]
  exact integral_congr_ae (ae_of_all _ fun a => real_inner_comm _ _)

/-- `⟪∫ φ dP, ∫ φ dQ⟫ = ∫∫ ⟪φ a, φ b⟫ dQ(b) dP(a)` for integrable `φ`. -/
theorem inner_integral_integral {P Q : Measure X} {φ : X → H} (hP : Integrable φ P) (hQ : Integrable φ Q) :
    ⟪∫ a, φ a ∂P, ∫ b, φ b ∂Q⟫_ℝ = ∫ a, ∫ b, ⟪φ a, φ b⟫_ℝ ∂Q ∂P := by
  rw [inner_integral_left hP]
  exact integral_congr_ae (ae_of_all _ fun a => (integral_inner hQ (φ a)).symm)

/-- The witness function of the mean-embedding difference: `⟪μ_P − μ_Q, φ z⟫ = ∫ k(a,z) dP(a) − ∫ k(b,z) dQ(b)`. -/
theorem inner_meanEmb_sub {P Q : Measure X} {φ : X → H} (hP : Integrable φ P) (hQ : Integrable φ Q) (z : X) :
    ⟪(∫ a, φ a ∂P) - ∫ b, φ b ∂Q, φ z⟫_ℝ = (∫ a, ⟪φ a, φ z⟫_ℝ ∂P) - ∫ b, ⟪φ b, φ z⟫_ℝ ∂Q := by
  rw [inner_sub_left, inner_integral_left hP, inner_integral_left hQ]

/-- The kernel form of the squared MMD: `‖μ_P − μ_Q‖² = ∫∫ k dP dP − 2 ∫∫ k dQ dP + ∫∫ k dQ dQ`. -/
theorem norm_sq_meanEmb_sub {P Q : Measure X} {φ : X → H} (hP : Integrable φ P) (hQ : Integrable φ Q) :
    ‖(∫ a, φ a ∂P) - ∫ b, φ b ∂Q‖ ^ 2 =
      (∫ a, ∫ a', ⟪φ a, φ a'⟫_ℝ ∂P ∂P) - 2 * (∫ a, ∫ b, ⟪φ a, φ b⟫_ℝ ∂Q ∂P) + ∫ b, ∫ b', ⟪φ b, φ b'⟫_ℝ ∂Q ∂Q := by
  rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_integral_integral hP hP,
    inner_integral_integral hP hQ, inner_integral_integral hQ hQ]

end Integral

end StatFormal.Alpha0Witness
