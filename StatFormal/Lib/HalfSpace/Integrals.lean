import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
# Two integral facts for explicit density pairs (library, untrusted)

* `integral_indicator_inner_sub_eq_zero`: on a finite-dimensional real inner-product space, for a ball `B(c₀, r)` whose centre lies
  on the hyperplane `⟪x, e⟫ = a`, `∫_{B(c₀, r)} (⟪x, e⟫ − a) dx = 0`: the point reflection `x ↦ 2c₀ − x` preserves Lebesgue
  measure (`integral_sub_left_eq_self`; Haar measure is negation invariant, `IsAddHaarMeasure.isNegInvariant_of_regular`), maps
  the ball to itself, and changes the sign of `⟪x, e⟫ − a`;
* `withDensity_ofReal_univ`, `measureReal_withDensity_ofReal`: for an integrable nonnegative `p`, the measure `p · μ` has mass
  `∫ p dμ` and `(p · μ)(A) = ∫_A p dμ` on measurable sets (`ofReal_integral_eq_lintegral_ofReal`).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Metric
open scoped InnerProductSpace RealInnerProductSpace ENNReal

namespace StatFormal.HalfSpace

/-- **Odd affine function over a centred ball**: if `⟪c₀, e⟫ = a`, then `∫ 1_{B(c₀, r)}(x) (⟪x, e⟫ − a) dx = 0`. -/
theorem integral_indicator_inner_sub_eq_zero {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {e c₀ : V} {a : ℝ} (hc : ⟪c₀, e⟫_ℝ = a) (r : ℝ) :
    ∫ x, (ball c₀ r).indicator (fun x => ⟪x, e⟫_ℝ - a) x = 0 := by
  set f : V → ℝ := (ball c₀ r).indicator (fun x => ⟪x, e⟫_ℝ - a)
  have hodd : ∀ x, f (c₀ + c₀ - x) = -f x := fun x => by
    have hmem : c₀ + c₀ - x ∈ ball c₀ r ↔ x ∈ ball c₀ r := by
      simp only [mem_ball, dist_eq_norm]
      rw [show c₀ + c₀ - x - c₀ = -(x - c₀) by abel, norm_neg]
    by_cases hx : x ∈ ball c₀ r
    · simp only [f, indicator_of_mem hx, indicator_of_mem (hmem.2 hx), inner_sub_left, inner_add_left, hc]
      ring
    · simp only [f, indicator_of_notMem hx, indicator_of_notMem (fun h => hx (hmem.1 h)), neg_zero]
  have h := integral_sub_left_eq_self f (volume : Measure V) (c₀ + c₀)
  simp only [hodd, integral_neg] at h
  linarith

variable {α : Type*} [MeasurableSpace α]

/-- The mass of `p · μ` for an integrable nonnegative `p` is `∫ p dμ`. -/
theorem withDensity_ofReal_univ (μ : Measure α) {p : α → ℝ} (hpi : Integrable p μ) (hp0 : ∀ x, 0 ≤ p x) :
    (μ.withDensity fun x => ENNReal.ofReal (p x)) univ = ENNReal.ofReal (∫ x, p x ∂μ) := by
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hpi (Filter.Eventually.of_forall hp0)]

/-- `(p · μ)(A) = ∫_A p dμ` (as real numbers) for an integrable nonnegative `p` and a measurable `A`. -/
theorem measureReal_withDensity_ofReal (μ : Measure α) {p : α → ℝ} (hpi : Integrable p μ) (hp0 : ∀ x, 0 ≤ p x)
    {A : Set α} (hA : MeasurableSet A) :
    (μ.withDensity fun x => ENNReal.ofReal (p x)).real A = ∫ x in A, p x ∂μ := by
  rw [measureReal_def, withDensity_apply _ hA,
    ← ofReal_integral_eq_lintegral_ofReal hpi.integrableOn (Filter.Eventually.of_forall hp0),
    ENNReal.toReal_ofReal (setIntegral_nonneg hA fun x _ => hp0 x)]

end StatFormal.HalfSpace
