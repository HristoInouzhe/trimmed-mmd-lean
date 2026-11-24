import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option linter.style.longLine false

/-!
# The layer cake formula for `[0,1]`-valued functions

A documented wrapper of Mathlib's layer cake formula (`Integrable.integral_eq_integral_meas_lt`,
`Mathlib/MeasureTheory/Integral/Layercake.lean`) for functions with values in `[0,1]` on a finite
measure space:

* `integral_eq_intervalIntegral_meas_lt`: `∫ h dμ = ∫_0^1 μ{h > s} ds` for `AEMeasurable h` with
  `0 ≤ h ≤ 1`.

On `(1,∞)` the level sets `{h > s}` are empty, so Mathlib's integral over `(0,∞)` reduces to `(0,1]`.
-/

noncomputable section
open MeasureTheory Set

namespace StatFormal.Indicatrix

/-- **Layer cake on `[0,1]`.** For a finite measure `μ` and an a.e.-measurable `h` with values in
`[0,1]`, `∫ h dμ = ∫_0^1 μ{x : s < h x} ds` (real-valued measures of the strict upper level sets). -/
theorem integral_eq_intervalIntegral_meas_lt {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {h : α → ℝ} (hm : AEMeasurable h μ) (h0 : ∀ x, 0 ≤ h x)
    (h1 : ∀ x, h x ≤ 1) :
    ∫ x, h x ∂μ = ∫ s in (0 : ℝ)..1, μ.real {x | s < h x} := by
  have hint : Integrable h μ := Integrable.of_mem_Icc 0 1 hm (ae_of_all _ fun x => ⟨h0 x, h1 x⟩)
  rw [hint.integral_eq_integral_meas_lt (ae_of_all _ h0),
    intervalIntegral.integral_of_le zero_le_one]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self ?_
  intro s hs
  have hs1 : 1 < s := by
    rcases hs with ⟨hs0, hs1⟩
    simp only [mem_Ioi] at hs0
    simp only [mem_Ioc, not_and, not_le] at hs1
    exact hs1 hs0
  have : {x | s < h x} = ∅ := by
    ext x; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
    exact (h1 x).trans hs1.le
  simp [this]

end StatFormal.Indicatrix
