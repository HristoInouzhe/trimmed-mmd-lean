import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# The support of a measure with a density continuous on an open set (library, untrusted)

Let `U` be open in a topological space `X` carrying a measure `μ` that charges nonempty open sets
(`IsOpenPosMeasure`), and let `p : X → ℝ` be continuous on `U`. For the measure
`ν = μ.withDensity (ofReal ∘ U.indicator p)` and `x ∈ U` (`mem_support_withDensity_indicator_iff`):

`x ∈ supp ν ↔ x ∈ closure {y ∈ U | p y > 0}`.

A closure point has every neighbourhood meeting the open set `{y ∈ U | p y > 0}` in a nonempty
open set, of positive `μ`-measure, on which the density is positive; a point of `U` off the
closure has the open neighbourhood `U \ closure {p > 0}` on which the density vanishes. No sign
condition on `p` is needed (negative values are clipped by `ENNReal.ofReal`), and `ν` may be
infinite.
-/

noncomputable section
open MeasureTheory Set Topology
open scoped ENNReal

namespace StatFormal.GaussMix

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- The indicator of an open set times a function continuous on it is measurable. -/
lemma measurable_indicator_of_continuousOn {U : Set X} {p : X → ℝ} (hU : IsOpen U)
    (hp : ContinuousOn p U) : Measurable (U.indicator p) := by
  classical
  rw [← piecewise_eq_indicator]
  exact hp.measurable_piecewise continuousOn_const hU.measurableSet

/-- **Support of a density continuous on an open set**: inside `U`, the support of
`μ.withDensity (ofReal ∘ U.indicator p)` is the closure of `{y ∈ U | 0 < p y}`. -/
theorem mem_support_withDensity_indicator_iff (μ : Measure X) [μ.IsOpenPosMeasure] {U : Set X}
    {p : X → ℝ} (hU : IsOpen U) (hp : ContinuousOn p U) {x : X} (hx : x ∈ U) :
    x ∈ (μ.withDensity fun y => ENNReal.ofReal (U.indicator p y)).support ↔
      x ∈ closure {y | y ∈ U ∧ 0 < p y} := by
  have hf : Measurable fun y => ENNReal.ofReal (U.indicator p y) :=
    ENNReal.measurable_ofReal.comp (measurable_indicator_of_continuousOn hU hp)
  rw [Measure.mem_support_iff_forall]
  constructor
  · intro h
    by_contra hcl
    -- `O = U \ closure {p > 0}` is an open neighbourhood of `x` on which the density vanishes
    have hO : IsOpen (U ∩ (closure {y | y ∈ U ∧ 0 < p y})ᶜ) :=
      hU.inter isClosed_closure.isOpen_compl
    have hpos := h _ (hO.mem_nhds ⟨hx, hcl⟩)
    rw [withDensity_apply _ hO.measurableSet] at hpos
    refine hpos.ne' ?_
    rw [setLIntegral_congr_fun hO.measurableSet (g := fun _ => 0) fun y hy => ?_, lintegral_zero]
    have hpy : p y ≤ 0 := by
      by_contra hlt
      exact hy.2 (subset_closure ⟨hy.1, lt_of_not_ge hlt⟩)
    simp only [indicator_of_mem hy.1, ENNReal.ofReal_eq_zero.2 hpy]
  · intro h N hN
    obtain ⟨W, hWN, hWo, hxW⟩ := mem_nhds_iff.1 hN
    -- `O = U ∩ {p > 0} ∩ W` is open, nonempty, and the density is positive on it
    have hO : IsOpen (U ∩ p ⁻¹' Ioi 0 ∩ W) := (hp.isOpen_inter_preimage hU isOpen_Ioi).inter hWo
    obtain ⟨y, hyW, hyU, hy0⟩ := mem_closure_iff.1 h W hWo hxW
    have hOne : (U ∩ p ⁻¹' Ioi 0 ∩ W).Nonempty := ⟨y, ⟨hyU, hy0⟩, hyW⟩
    have hOW : U ∩ p ⁻¹' Ioi 0 ∩ W ⊆ N := inter_subset_right.trans hWN
    refine lt_of_lt_of_le ?_ (measure_mono hOW)
    rw [withDensity_apply _ hO.measurableSet, lintegral_pos_iff_support hf,
      Measure.restrict_apply' hO.measurableSet]
    have hsub : U ∩ p ⁻¹' Ioi 0 ∩ W ⊆
        Function.support fun y => ENNReal.ofReal (U.indicator p y) := by
      rintro z ⟨⟨hzU, hz0⟩, -⟩
      simp only [Function.mem_support, indicator_of_mem hzU, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact hz0
    rw [inter_eq_right.2 hsub]
    exact hO.measure_pos μ hOne

end StatFormal.GaussMix
