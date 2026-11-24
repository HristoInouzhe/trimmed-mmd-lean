import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Lebesgue densities of probability measures (library, untrusted)

If `P = μ.withDensity (ofReal ∘ p)` with `p` measurable and nonnegative and `P` is a probability measure, then `p` is
`μ`-integrable with `∫ p dμ = 1`; and for densities `p, q` of two probability measures, `∫ |p − q| = 2 ∫ (p − q)₊`
(the total variation measure has twice the mass of the positive part). Also: the set integral of a nonnegative integrable
function is the real value of the `withDensity` measure of the set.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.BandLimited

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A density of a probability measure is integrable with integral `1`. -/
theorem integrable_and_integral_of_density {P : Measure α} [IsProbabilityMeasure P] {p : α → ℝ} (hp : Measurable p)
    (hp0 : ∀ x, 0 ≤ p x) (hP : P = μ.withDensity fun x => ENNReal.ofReal (p x)) :
    Integrable p μ ∧ ∫ x, p x ∂μ = 1 := by
  have hl : ∫⁻ x, ENNReal.ofReal (p x) ∂μ = 1 := by
    have h := measure_univ (μ := P)
    rw [hP, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
    exact h
  have hnn : 0 ≤ᵐ[μ] p := ae_of_all _ hp0
  refine ⟨⟨hp.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2 (by rw [hl]; exact ENNReal.one_lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hp.aestronglyMeasurable, hl, ENNReal.toReal_one]

/-- For densities of two probability measures, `∫ |p − q| = 2 ∫ (p − q)₊`. -/
theorem integral_abs_sub_of_densities {P Q : Measure α} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {p q : α → ℝ}
    (hp : Measurable p) (hq : Measurable q) (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hP : P = μ.withDensity fun x => ENNReal.ofReal (p x)) (hQ : Q = μ.withDensity fun x => ENNReal.ofReal (q x)) :
    ∫ x, |p x - q x| ∂μ = 2 * ∫ x, max (p x - q x) 0 ∂μ := by
  obtain ⟨hpi, hp1⟩ := integrable_and_integral_of_density hp hp0 hP
  obtain ⟨hqi, hq1⟩ := integrable_and_integral_of_density hq hq0 hQ
  have hmax : Integrable (fun x => max (p x - q x) 0) μ := (hpi.sub hqi).pos_part
  have hpt : (fun x => |p x - q x|) = fun x => 2 * max (p x - q x) 0 - (p x - q x) := by
    funext x
    rcases le_total (p x - q x) 0 with h | h
    · rw [abs_of_nonpos h, max_eq_right h]; ring
    · rw [abs_of_nonneg h, max_eq_left h]; ring
  have hpq : Integrable (fun x => p x - q x) μ := hpi.sub hqi
  rw [hpt, integral_sub (hmax.const_mul 2) hpq, integral_const_mul, integral_sub hpi hqi, hp1, hq1]
  ring

/-- The real value of `μ.withDensity (ofReal ∘ g)` on a measurable set is the set integral of `g ≥ 0` (integrable). -/
theorem withDensity_real_eq_setIntegral {g : α → ℝ} (hg : Integrable g μ) (hg0 : ∀ x, 0 ≤ g x) {s : Set α}
    (hs : MeasurableSet s) :
    ((μ.withDensity fun x => ENNReal.ofReal (g x)) s).toReal = ∫ x in s, g x ∂μ := by
  rw [withDensity_apply _ hs, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg0) hg.aestronglyMeasurable.restrict]

end StatFormal.BandLimited
