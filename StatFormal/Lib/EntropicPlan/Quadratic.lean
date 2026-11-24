import StatFormal.Lib.EntropicPlan.Basic
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
import Mathlib.Analysis.MeanInequalitiesPow

set_option linter.style.longLine false

/-!
# The quadratic cost and second moments (library)

Library component (Wave 30r, SB `lem:sharp`). Untrusted library code.

Setting: a normed group `E` with its Borel σ-algebra, the cost `‖x − y‖²` in `ℝ≥0∞`.

* `enorm_sub_sq_le`: `‖x − y‖² ≤ 2(‖x‖² + ‖y‖²)`.
* `lintegral_enorm_sq_ne_top`, `hasFiniteMoment_two_iff`: `HasFiniteMoment 2 ν` (Tau Ceti) iff `∫ ‖y‖² dν < ∞`.
* `lintegral_sqdist_prod_ne_top`: for `R, ν ∈ 𝒫₂`, `∫ ‖x − y‖² d(R ⊗ ν) < ∞`, so the entropic library
  (`EntropicPlan.Basic`) applies to the quadratic cost on non-compact supports.
* `lintegral_enorm_sq_fst_le`: for any coupling, `∫ ‖x‖² dR ≤ 2(∫ ‖x − y‖² dπ + ∫ ‖y‖² dν)`; hence if `R ∉ 𝒫₂` and
  `ν ∈ 𝒫₂`, every coupling has infinite quadratic cost (`lintegral_sqdist_eq_top`).
-/

noncomputable section
open MeasureTheory TauCeti Set
open scoped ENNReal NNReal

namespace StatFormal.Foundations.EntropicPlan

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

lemma add_sq_le_two_mul (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  have h := ENNReal.rpow_add_le_mul_rpow_add_rpow a b (p := 2) (by norm_num)
  simp only [ENNReal.rpow_two] at h
  norm_num at h
  exact h

lemma enorm_sub_sq_le (x y : E) : ‖x - y‖ₑ ^ 2 ≤ 2 * (‖x‖ₑ ^ 2 + ‖y‖ₑ ^ 2) :=
  (pow_le_pow_left₀ (by simp) (enorm_sub_le) 2).trans (add_sq_le_two_mul _ _)

lemma enorm_sq_le (x y : E) : ‖x‖ₑ ^ 2 ≤ 2 * (‖x - y‖ₑ ^ 2 + ‖y‖ₑ ^ 2) := by
  have h : ‖x‖ₑ ≤ ‖x - y‖ₑ + ‖y‖ₑ := by
    calc ‖x‖ₑ = ‖(x - y) + y‖ₑ := by rw [sub_add_cancel]
      _ ≤ ‖x - y‖ₑ + ‖y‖ₑ := enorm_add_le _ _
  exact (pow_le_pow_left₀ (by simp) h 2).trans (add_sq_le_two_mul _ _)

lemma hasFiniteMoment_two_iff {ν : Measure E} [IsFiniteMeasure ν] :
    HasFiniteMoment 2 ν ↔ ∫⁻ y, ‖y‖ₑ ^ 2 ∂ν ≠ ∞ := by
  rw [hasFiniteMoment_iff_lintegral_edist_rpow_ne_top two_ne_zero ENNReal.ofNat_ne_top 0 ν]
  have : ∀ y : E, edist 0 y ^ (2 : ℝ≥0∞).toReal = ‖y‖ₑ ^ 2 := fun y => by
    rw [edist_comm, edist_zero_right]
    norm_num
  simp_rw [this]

lemma lintegral_enorm_sq_ne_top {ν : Measure E} [IsFiniteMeasure ν] (h : HasFiniteMoment 2 ν) :
    ∫⁻ y, ‖y‖ₑ ^ 2 ∂ν ≠ ∞ :=
  hasFiniteMoment_two_iff.1 h

/-- For laws with finite second moments the quadratic cost is integrable against the product. -/
theorem lintegral_sqdist_prod_ne_top {R ν : Measure E} [IsProbabilityMeasure R] [IsProbabilityMeasure ν]
    (hR : HasFiniteMoment 2 R) (hν : HasFiniteMoment 2 ν) :
    ∫⁻ z, ‖z.1 - z.2‖ₑ ^ 2 ∂(R.prod ν) ≠ ∞ := by
  have hπ := isCoupling_prod R ν
  have hm : Measurable fun x : E => ‖x‖ₑ ^ 2 := measurable_enorm.pow_const 2
  refine ne_top_of_le_ne_top ?_ (lintegral_mono fun z => enorm_sub_sq_le z.1 z.2)
  have hm1 : Measurable fun z : E × E => ‖z.1‖ₑ ^ 2 := hm.comp measurable_fst
  rw [lintegral_const_mul' _ _ ENNReal.ofNat_ne_top, lintegral_add_left hm1]
  have h1 : ∫⁻ z, ‖z.1‖ₑ ^ 2 ∂(R.prod ν) = ∫⁻ x, ‖x‖ₑ ^ 2 ∂R := hπ.lintegral_comp_fst hm.aemeasurable
  have h2 : ∫⁻ z, ‖z.2‖ₑ ^ 2 ∂(R.prod ν) = ∫⁻ y, ‖y‖ₑ ^ 2 ∂ν := hπ.lintegral_comp_snd hm.aemeasurable
  rw [h1, h2]
  exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top
    (ENNReal.add_ne_top.2 ⟨lintegral_enorm_sq_ne_top hR, lintegral_enorm_sq_ne_top hν⟩)

/-- For any coupling, `∫ ‖x‖² dR ≤ 2 (∫ ‖x − y‖² dπ + ∫ ‖y‖² dν)`. -/
theorem lintegral_enorm_sq_fst_le {R ν : Measure E} {π : Measure (E × E)} (hπ : IsCoupling π R ν) :
    ∫⁻ x, ‖x‖ₑ ^ 2 ∂R ≤ 2 * (∫⁻ z, ‖z.1 - z.2‖ₑ ^ 2 ∂π + ∫⁻ y, ‖y‖ₑ ^ 2 ∂ν) := by
  have hm : Measurable fun x : E => ‖x‖ₑ ^ 2 := measurable_enorm.pow_const 2
  have h1 : ∫⁻ z, ‖z.1‖ₑ ^ 2 ∂π = ∫⁻ x, ‖x‖ₑ ^ 2 ∂R := hπ.lintegral_comp_fst hm.aemeasurable
  have h2 : ∫⁻ z, ‖z.2‖ₑ ^ 2 ∂π = ∫⁻ y, ‖y‖ₑ ^ 2 ∂ν := hπ.lintegral_comp_snd hm.aemeasurable
  have hm2 : Measurable fun z : E × E => ‖z.2‖ₑ ^ 2 := hm.comp measurable_snd
  rw [← h1, ← h2, ← lintegral_add_right _ hm2,
    ← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
  exact lintegral_mono fun z => enorm_sq_le z.1 z.2

/-- If `R ∉ 𝒫₂` and `ν ∈ 𝒫₂` (finite measures), every coupling has infinite quadratic cost. -/
theorem lintegral_sqdist_eq_top {R ν : Measure E} [IsFiniteMeasure R] [IsFiniteMeasure ν]
    {π : Measure (E × E)} (hπ : IsCoupling π R ν) (hR : ¬ HasFiniteMoment 2 R) (hν : HasFiniteMoment 2 ν) :
    ∫⁻ z, ‖z.1 - z.2‖ₑ ^ 2 ∂π = ∞ := by
  by_contra h
  apply hR
  refine hasFiniteMoment_two_iff.2 (ne_top_of_le_ne_top ?_ (lintegral_enorm_sq_fst_le hπ))
  exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.add_ne_top.2 ⟨h, lintegral_enorm_sq_ne_top hν⟩)

end StatFormal.Foundations.EntropicPlan
