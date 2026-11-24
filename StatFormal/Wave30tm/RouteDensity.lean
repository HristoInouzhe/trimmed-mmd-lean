import StatFormal.Wave30tm.Statements
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

set_option linter.style.longLine false

/-!
# Wave 30tm — encoding check: `P ≤ 2 • λ|_{[0,1]}` iff a Lebesgue density `f ≤ 2` vanishing off `[0,1]`
(untrusted proof file)

`2 • λ|_{[0,1]} = λ.withDensity (1_{[0,1]} · 2)`. If `P ≤` this, then `P ≪ λ`, `P = λ.withDensity (dP/dλ)` and
`dP/dλ ≤ 1_{[0,1]} · 2` a.e.; the version `f = 1_{[0,1]} · min(dP/dλ, 2)` is bounded by `2` everywhere, vanishes off
`[0,1]` and is a.e. equal to `dP/dλ`. The converse is monotonicity of `withDensity`.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.Wave30tm

theorem two_smul_restrict_eq_withDensity :
    (2 : ℝ≥0∞) • volume.restrict (Icc (0 : ℝ) 1) =
      volume.withDensity ((Icc (0 : ℝ) 1).indicator fun _ => (2 : ℝ≥0∞)) := by
  rw [withDensity_indicator measurableSet_Icc, withDensity_const]

theorem density2_iff_route : Claims.density2_iff := by
  intro P
  rw [Density2, two_smul_restrict_eq_withDensity]
  set I := Icc (0 : ℝ) 1 with hI
  set h : ℝ → ℝ≥0∞ := I.indicator fun _ => (2 : ℝ≥0∞) with hh
  constructor
  · rintro ⟨hP, hle⟩
    refine ⟨hP, ?_⟩
    have hac : P ≪ volume := by
      have h1 : P ≪ volume.withDensity h := Measure.absolutelyContinuous_of_le hle
      exact h1.trans (withDensity_absolutelyContinuous _ _)
    set g := P.rnDeriv volume with hg
    have hgm : Measurable g := Measure.measurable_rnDeriv _ _
    have hPg : volume.withDensity g = P := Measure.withDensity_rnDeriv_eq P volume hac
    have hgh : g ≤ᵐ[volume] h := by
      refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite hgm fun s hs _ => ?_
      rw [← withDensity_apply _ hs, ← withDensity_apply _ hs, hPg]
      exact Measure.le_iff'.1 hle s
    set f : ℝ → ℝ≥0∞ := I.indicator fun x => min (g x) 2 with hf
    have hfm : Measurable f := (hgm.min measurable_const).indicator measurableSet_Icc
    have hfg : f =ᵐ[volume] g := by
      filter_upwards [hgh] with x hx
      by_cases hxI : x ∈ I
      · simp only [hh, Set.indicator_of_mem hxI] at hx
        simp only [hf, Set.indicator_of_mem hxI]
        exact min_eq_left hx
      · simp only [hh, Set.indicator_of_notMem hxI] at hx
        simp only [hf, Set.indicator_of_notMem hxI]
        exact (le_antisymm hx zero_le).symm
    refine ⟨f, hfm, fun x => ?_, fun x hx => ?_, ?_⟩
    · by_cases hxI : x ∈ I
      · simp only [hf, Set.indicator_of_mem hxI]; exact min_le_right _ _
      · simp only [hf, Set.indicator_of_notMem hxI]; exact zero_le
    · simp only [hf, Set.indicator_of_notMem hx]
    · rw [← hPg]; exact (withDensity_congr_ae hfg).symm
  · rintro ⟨hP, f, -, hf2, hf0, rfl⟩
    refine ⟨hP, withDensity_mono (Filter.Eventually.of_forall fun x => ?_)⟩
    by_cases hxI : x ∈ I
    · simp only [hh, Set.indicator_of_mem hxI]; exact hf2 x
    · simp only [hh, Set.indicator_of_notMem hxI, hf0 x hxI, le_refl]

end StatFormal.Wave30tm
