import StatFormal.Wave31ti.Statements

/-!
# Explicit trimmings bound the rescaled path (library, untrusted)

If `P′ ≤ P` and `Q′ ≤ Q` are finite measures of equal mass `1 − α`, `0 ≤ α < 1`, then `P′/(1−α)` and `Q′/(1−α)` are
`α`-trimmings of `P` and `Q` (their densities `dP′/dP ≤ 1` divided by `1 − α` are at most `1/(1−α)`), so their embeddings lie in
the regions `𝒞_{α,k}(P)`, `𝒞_{α,k}(Q)` and
`D̄_α = (1−α) D_α(P, Q) ≤ ‖∫ φ dP′ − ∫ φ dQ′‖` (S4 :747-748 of the trimmed-mmd supplement: "nonnegative measures `P′ ≤ P` and
`Q′ ≤ Q` of equal mass `1 − α` give `D̄_α ≤ ‖∫ φ d(P′ − Q′)‖`"). Adapted from the certified `Wave30tx.mem_region_of_trimSet`
(Radon–Nikodym density of a sub-measure).

* `mem_region_of_le`: `(1−α)⁻¹ ∫ φ dP′ ∈ region φ α P`;
* `Dpop_nonneg`: `0 ≤ D_α`;
* `uPath_le_of_le`: the bound on `uPath φ P Q α = (1−α) D_α`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set

namespace StatFormal.MomentTrim

open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The normalised embedding of a sub-measure `P′ ≤ P` of mass `1 − α` lies in the region `𝒞_{α,k}(P)`. -/
theorem mem_region_of_le (φ : 𝒳 → H) (P P' : Measure 𝒳) [IsProbabilityMeasure P] [IsFiniteMeasure P'] (hle : P' ≤ P)
    {α : ℝ} (hα1 : α < 1) (hmass : P' univ = ENNReal.ofReal (1 - α)) :
    (1 - α)⁻¹ • ∫ x, φ x ∂P' ∈ region φ α P := by
  have h1α : 0 < 1 - α := by linarith
  have hac : P' ≪ P := Measure.absolutelyContinuous_of_le hle
  set g : 𝒳 → ℝ := fun x => (1 - α)⁻¹ * min (P'.rnDeriv P x).toReal 1 with hg
  have hgm : Measurable g := measurable_const.mul ((Measure.measurable_rnDeriv P' P).ennreal_toReal.min measurable_const)
  have hae : ∀ᵐ x ∂P, min (P'.rnDeriv P x).toReal 1 = (P'.rnDeriv P x).toReal := by
    filter_upwards [Measure.rnDeriv_le_one_of_le hle] with x hx
    refine min_eq_left ?_
    have : P'.rnDeriv P x ≤ 1 := hx
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
  refine ⟨g, hgm, fun x => ⟨?_, ?_⟩, ?_, ?_⟩
  · exact mul_nonneg (inv_nonneg.mpr h1α.le) (le_min ENNReal.toReal_nonneg zero_le_one)
  · rw [one_div]
    exact mul_le_of_le_one_right (inv_nonneg.mpr h1α.le) (min_le_right _ _)
  · have h2 : ∫ x, g x ∂P = (1 - α)⁻¹ * ∫ x, (P'.rnDeriv P x).toReal ∂P := by
      rw [← integral_const_mul]
      exact integral_congr_ae (hae.mono fun x hx => by simp only [hg, hx])
    rw [h2, Measure.integral_toReal_rnDeriv hac, measureReal_def, hmass, ENNReal.toReal_ofReal h1α.le,
      inv_mul_cancel₀ h1α.ne']
  · have h2 : ∫ x, g x • φ x ∂P = (1 - α)⁻¹ • ∫ x, (P'.rnDeriv P x).toReal • φ x ∂P := by
      rw [← integral_smul]
      exact integral_congr_ae (hae.mono fun x hx => by simp only [hg, hx, smul_smul])
    rw [h2, integral_rnDeriv_smul hac]

/-- `D_α(P, Q) ≥ 0` (an infimum of norms). -/
theorem Dpop_nonneg (φ : 𝒳 → H) (P Q : Measure 𝒳) (α : ℝ) : 0 ≤ Dpop φ P Q α := by
  unfold Dpop setDist
  refine Real.sInf_nonneg fun r hr => ?_
  obtain ⟨a, _, b, _, rfl⟩ := hr
  exact norm_nonneg _

/-- **Explicit trimmings bound the rescaled path.** If `P′ ≤ P`, `Q′ ≤ Q` are finite measures of mass `1 − α`, `0 ≤ α < 1`,
then `(1 − α) D_α(P, Q) ≤ ‖∫ φ dP′ − ∫ φ dQ′‖`. -/
theorem uPath_le_of_le (φ : 𝒳 → H) (P Q P' Q' : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    [IsFiniteMeasure P'] [IsFiniteMeasure Q'] (hP : P' ≤ P) (hQ : Q' ≤ Q) {α : ℝ} (hα1 : α < 1)
    (hmP : P' univ = ENNReal.ofReal (1 - α)) (hmQ : Q' univ = ENNReal.ofReal (1 - α)) :
    StatFormal.Wave31ti.uPath φ P Q α ≤ ‖∫ x, φ x ∂P' - ∫ x, φ x ∂Q'‖ := by
  have h1α : 0 < 1 - α := by linarith
  have hA := mem_region_of_le φ P P' hP hα1 hmP
  have hB := mem_region_of_le φ Q Q' hQ hα1 hmQ
  have hD : Dpop φ P Q α ≤ ‖(1 - α)⁻¹ • ∫ x, φ x ∂P' - (1 - α)⁻¹ • ∫ x, φ x ∂Q'‖ := by
    unfold Dpop setDist
    refine csInf_le ⟨0, fun r hr => ?_⟩ ⟨_, hA, _, hB, rfl⟩
    obtain ⟨a, _, b, _, rfl⟩ := hr
    exact norm_nonneg _
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h1α)] at hD
  unfold StatFormal.Wave31ti.uPath
  calc (1 - α) * Dpop φ P Q α ≤ (1 - α) * ((1 - α)⁻¹ * ‖∫ x, φ x ∂P' - ∫ x, φ x ∂Q'‖) :=
        mul_le_mul_of_nonneg_left hD h1α.le
    _ = ‖∫ x, φ x ∂P' - ∫ x, φ x ∂Q'‖ := by rw [← mul_assoc, mul_inv_cancel₀ h1α.ne', one_mul]

end StatFormal.MomentTrim
