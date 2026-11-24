import StatFormal.Wave31th.Statements
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Wave 31th, route: a density from two-sided bounds on the law (untrusted proof file)

`qdensity_of_bounds`: if `c λ(A) ≤ P(f⁻¹A) ≤ C λ(A)` for every Borel `A ⊆ [t−r, t+r]` (`c > 0`), then the law of `f` under `P` has on the
window a density with values in `[c, max c C]` (`QDensity P f t r c (max c C)`): the Radon–Nikodym derivative of the restriction of the
image measure to the window with respect to Lebesgue measure restricted to the window, clamped to `[c, max c C]` (it lies in `[c, C]`
almost everywhere). Also: `QDensity` and `QDensityLower` are monotone in the half-width, and `QDensity` implies `QDensityLower`.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatFormal.Wave31th

open StatFormal.Wave12c

/-- A density from two-sided bounds. -/
lemma qdensity_of_bounds {𝒳 : Type*} [MeasurableSpace 𝒳] {P : Measure 𝒳} {f : 𝒳 → ℝ} (hf : Measurable f)
    {t r c C : ℝ} (hc : 0 < c)
    (hbd : ∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc (t - r) (t + r) →
      ENNReal.ofReal c * volume A ≤ P (f ⁻¹' A) ∧ P (f ⁻¹' A) ≤ ENNReal.ofReal C * volume A) :
    QDensity P f t r c (max c C) := by
  classical
  set W := Icc (t - r) (t + r) with hW
  set μ : Measure ℝ := volume.restrict W with hμ
  set ν : Measure ℝ := (Measure.map f P).restrict W with hν
  have hμfin : μ univ ≠ ∞ := by
    rw [hμ, Measure.restrict_apply_univ, hW, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have : IsFiniteMeasure μ := ⟨lt_top_iff_ne_top.2 hμfin⟩
  have hνle : ∀ S, MeasurableSet S → ν S ≤ ENNReal.ofReal C * μ S := fun S hS => by
    rw [hν, hμ, Measure.restrict_apply hS, Measure.restrict_apply hS,
      Measure.map_apply hf (hS.inter measurableSet_Icc)]
    exact (hbd (S ∩ W) (hS.inter measurableSet_Icc) inter_subset_right).2
  have hνge : ∀ S, MeasurableSet S → ENNReal.ofReal c * μ S ≤ ν S := fun S hS => by
    rw [hν, hμ, Measure.restrict_apply hS, Measure.restrict_apply hS,
      Measure.map_apply hf (hS.inter measurableSet_Icc)]
    exact (hbd (S ∩ W) (hS.inter measurableSet_Icc) inter_subset_right).1
  have hνfin : IsFiniteMeasure ν :=
    ⟨lt_of_le_of_lt (hνle univ MeasurableSet.univ)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hμfin))⟩
  have hac : ν ≪ μ := by
    intro s hs0
    obtain ⟨t', hts, ht'm, ht'0⟩ := exists_measurable_superset_of_null hs0
    have h1 := hνle t' ht'm
    rw [ht'0, mul_zero] at h1
    exact measure_mono_null hts (le_antisymm h1 zero_le)
  set g₀ := ν.rnDeriv μ with hg₀
  have hg₀m : Measurable g₀ := Measure.measurable_rnDeriv _ _
  have hdens : μ.withDensity g₀ = ν := Measure.withDensity_rnDeriv_eq ν μ hac
  have hS : ∀ S, MeasurableSet S → ∫⁻ x in S, g₀ x ∂μ = ν S := fun S hS => by
    rw [← withDensity_apply _ hS, hdens]
  have hup : ∀ᵐ x ∂μ, g₀ x ≤ ENNReal.ofReal C := by
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite hg₀m fun S hS' _ => ?_
    rw [hS S hS', setLIntegral_const]
    exact hνle S hS'
  have hlo : ∀ᵐ x ∂μ, ENNReal.ofReal c ≤ g₀ x := by
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite measurable_const fun S hS' _ => ?_
    rw [hS S hS', setLIntegral_const]
    exact hνge S hS'
  have hupW : ∀ᵐ x ∂volume.restrict W, g₀ x ≤ ENNReal.ofReal C := hup
  have hloW : ∀ᵐ x ∂volume.restrict W, ENNReal.ofReal c ≤ g₀ x := hlo
  set g : ℝ → ℝ := fun s => max c (min (max c C) (g₀ s).toReal) with hg
  have hgm : Measurable g := measurable_const.max (measurable_const.min hg₀m.ennreal_toReal)
  refine ⟨g, hgm, fun s _ => ⟨le_max_left _ _, max_le (le_max_left _ _) (min_le_left _ _)⟩, fun A hA hAW => ?_⟩
  have hAμ : μ.restrict A = volume.restrict A := by
    rw [hμ, Measure.restrict_restrict hA, inter_eq_left.2 hAW]
  have h1 : P (f ⁻¹' A) = ν A := by
    rw [hν, Measure.restrict_apply hA, inter_eq_left.2 hAW, Measure.map_apply hf hA]
  rw [h1, ← hS A hA, hAμ]
  refine lintegral_congr_ae ?_
  have hupA : ∀ᵐ x ∂volume.restrict A, g₀ x ≤ ENNReal.ofReal C := ae_restrict_of_ae_restrict_of_subset hAW hupW
  have hloA : ∀ᵐ x ∂volume.restrict A, ENNReal.ofReal c ≤ g₀ x := ae_restrict_of_ae_restrict_of_subset hAW hloW
  filter_upwards [hupA, hloA] with x hx1 hx2
  have hne : g₀ x ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hx1
  have hCpos : 0 ≤ C := by
    by_contra hCneg
    push Not at hCneg
    have h3 := hx2.trans hx1
    rw [ENNReal.ofReal_of_nonpos hCneg.le] at h3
    exact absurd (ENNReal.ofReal_pos.2 hc) (not_lt.2 h3)
  have hr1 : (g₀ x).toReal ≤ C := ENNReal.toReal_le_of_le_ofReal hCpos hx1
  have hr2 : c ≤ (g₀ x).toReal := by
    have := ENNReal.toReal_mono hne hx2
    rwa [ENNReal.toReal_ofReal hc.le] at this
  have hgx : g x = (g₀ x).toReal := by
    simp only [hg]
    rw [min_eq_right (hr1.trans (le_max_right _ _)), max_eq_right hr2]
  rw [hgx, ENNReal.ofReal_toReal hne]

/-- `QDensity` survives shrinking the window. -/
lemma QDensity_mono' {𝒳 : Type*} [MeasurableSpace 𝒳] {P : Measure 𝒳} {f : 𝒳 → ℝ} {t r r' c C : ℝ}
    (hr : r' ≤ r) (hQ : QDensity P f t r c C) : QDensity P f t r' c C := by
  obtain ⟨g, hg, hb, hP⟩ := hQ
  have hsub : Icc (t - r') (t + r') ⊆ Icc (t - r) (t + r) := Icc_subset_Icc (by linarith) (by linarith)
  exact ⟨g, hg, fun s hs => hb s (hsub hs), fun A hA hAI => hP A hA (hAI.trans hsub)⟩

/-- `QDensityLower` survives shrinking the window. -/
lemma QDensityLower_mono' {𝒳 : Type*} [MeasurableSpace 𝒳] {P : Measure 𝒳} {f : 𝒳 → ℝ} {t r r' c : ℝ}
    (hr : r' ≤ r) (hQ : QDensityLower P f t r c) : QDensityLower P f t r' c := by
  obtain ⟨g, hg, hb, hP⟩ := hQ
  have hsub : Icc (t - r') (t + r') ⊆ Icc (t - r) (t + r) := Icc_subset_Icc (by linarith) (by linarith)
  exact ⟨g, hg, fun s hs => hb s (hsub hs), fun A hA hAI => hP A hA (hAI.trans hsub)⟩

/-- `QDensity` gives `QDensityLower`. -/
lemma QDensityLower_of_QDensity {𝒳 : Type*} [MeasurableSpace 𝒳] {P : Measure 𝒳} {f : 𝒳 → ℝ} {t r c C : ℝ}
    (hQ : QDensity P f t r c C) : QDensityLower P f t r c := by
  obtain ⟨g, hg, hb, hP⟩ := hQ
  exact ⟨g, hg, fun s hs => (hb s hs).1, hP⟩

end StatFormal.Wave31th
