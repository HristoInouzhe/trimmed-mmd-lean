import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# A finitely supported law has no density bounded below (library, untrusted)

* `exists_null_preimage_pos_density`: if `P(Sᶜ) = 0` for a finite set `S`, then for any `f`, any `r, c > 0` and any `g ≥ c` on
  `I = [t − r, t + r]`, the measurable set `A = I \ f(S)` has `P(f⁻¹A) = 0` but `∫⁻_A g > 0` (`A` has Lebesgue measure `2r`).
  So the law of `f` under `P` has no density bounded below by `c` on `I`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.TVFacts

/-- **A finitely supported law has no density bounded below on an interval.** If `P(Sᶜ) = 0` for a finite `S`, `0 < r`, `0 < c` and
`c ≤ g` on `[t − r, t + r]` (`g` measurable), then `A = [t − r, t + r] \ f(S)` is a measurable subset of the interval with
`P(f⁻¹A) = 0` and `0 < ∫⁻_A ofReal g`. -/
theorem exists_null_preimage_pos_density {𝒳 : Type*} [MeasurableSpace 𝒳] (P : Measure 𝒳) (S : Finset 𝒳)
    (hS : P (↑S : Set 𝒳)ᶜ = 0) (f : 𝒳 → ℝ) {t r c : ℝ} (hr : 0 < r) (hc : 0 < c) {g : ℝ → ℝ} (hg : Measurable g)
    (hgc : ∀ s ∈ Icc (t - r) (t + r), c ≤ g s) :
    ∃ A : Set ℝ, MeasurableSet A ∧ A ⊆ Icc (t - r) (t + r) ∧ P (f ⁻¹' A) = 0 ∧
      0 < ∫⁻ s in A, ENNReal.ofReal (g s) := by
  classical
  set B : Set ℝ := ↑(S.image f) with hB
  have hBfin : B.Finite := (S.image f).finite_toSet
  have hBm : MeasurableSet B := hBfin.measurableSet
  refine ⟨Icc (t - r) (t + r) \ B, measurableSet_Icc.diff hBm, diff_subset, ?_, ?_⟩
  · refine measure_mono_null (fun x hx => ?_) hS
    simp only [mem_preimage, mem_diff] at hx
    intro hxS
    exact hx.2 (by rw [hB, Finset.coe_image]; exact mem_image_of_mem f hxS)
  · have hvol : volume (Icc (t - r) (t + r) \ B) = ENNReal.ofReal (2 * r) := by
      rw [measure_diff_null (hBfin.measure_zero volume), Real.volume_Icc]
      congr 1
      ring
    have hmono : ∫⁻ _ in Icc (t - r) (t + r) \ B, ENNReal.ofReal c ≤ ∫⁻ s in Icc (t - r) (t + r) \ B, ENNReal.ofReal (g s) :=
      setLIntegral_mono hg.ennreal_ofReal fun s hs => ENNReal.ofReal_le_ofReal (hgc s hs.1)
    refine lt_of_lt_of_le ?_ hmono
    rw [setLIntegral_const, hvol]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 hc).ne' (ENNReal.ofReal_pos.2 (by linarith)).ne'

end StatFormal.TVFacts
