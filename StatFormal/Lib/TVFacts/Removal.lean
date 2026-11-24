import StatFormal.Lib.TVFacts.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Trimmings as renormalised removals (library, untrusted)

A trimming of a probability measure `P` at level `α ∈ [0,1)` is a law `g·P` with `0 ≤ g ≤ (1−α)⁻¹`. Equivalently it is obtained from
`P` by removing a sub-measure `ν ≤ P` of mass at most `α` and renormalising: `(P − ν)/(1 − ν(𝒳))`.

## Main results

* `smul_withDensity_ofReal_le`: `c g ≤ 1` gives `c • (g·P) ≤ P`;
* `isProbabilityMeasure_withDensity_ofReal`: `g ≥ 0` integrable with `∫ g dP = 1` gives a probability measure `g·P`;
* `eq_of_tvDist_eq_zero`: `TV(P,Q) = 0` forces `P = Q` (finite measures);
* `smul_le_smul_of_le`: `c ≤ c'` gives `c • R ≤ c' • R`;
* `exists_removal_of_density`: a density `0 ≤ g ≤ (1−α)⁻¹` with `∫ g dP = 1` is `(P − ν)/(1 − ν(𝒳))` for `ν = P − (1−α)g·P`, of mass `α`;
* `exists_density_of_removal`: conversely `(P − ν)/(1 − ν(𝒳))` for `ν ≤ P` of mass `≤ α < 1` has a density
  `(1 − ν(𝒳))⁻¹ min{1, d(P − ν)/dP} ∈ [0, (1−α)⁻¹]` with integral `1`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.TVFacts

open StatFormal.Distances

variable {α : Type*} [MeasurableSpace α]

/-- If `0 ≤ c` and `c g ≤ 1` pointwise (`g` measurable), then `ofReal c • P.withDensity (ofReal ∘ g) ≤ P`. -/
theorem smul_withDensity_ofReal_le (P : Measure α) {g : α → ℝ} (hg : Measurable g) {c : ℝ} (hc : 0 ≤ c)
    (hcg : ∀ x, c * g x ≤ 1) : ENNReal.ofReal c • P.withDensity (fun x => ENNReal.ofReal (g x)) ≤ P := by
  rw [← withDensity_smul _ hg.ennreal_ofReal]
  calc P.withDensity (ENNReal.ofReal c • fun x => ENNReal.ofReal (g x)) ≤ P.withDensity 1 := by
        refine withDensity_mono (ae_of_all _ fun x => ?_)
        simp only [Pi.smul_apply, smul_eq_mul, Pi.one_apply]
        rw [← ENNReal.ofReal_mul hc]
        exact ENNReal.ofReal_le_one.2 (hcg x)
    _ = P := withDensity_one

/-- A nonnegative integrable density of integral one gives a probability measure. -/
theorem isProbabilityMeasure_withDensity_ofReal (P : Measure α) {g : α → ℝ} (hgi : Integrable g P) (hg0 : ∀ x, 0 ≤ g x)
    (hg1 : ∫ x, g x ∂P = 1) : IsProbabilityMeasure (P.withDensity fun x => ENNReal.ofReal (g x)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ hg0), hg1, ENNReal.ofReal_one]

/-- Total variation zero forces equality (finite measures). -/
theorem eq_of_tvDist_eq_zero {P Q : Measure α} [IsFiniteMeasure P] [IsFiniteMeasure Q] (h : tvDist P Q = 0) : P = Q := by
  refine Measure.ext fun A hA => ?_
  have h1 := abs_measureReal_sub_le_tvDist (μ := P) (ν := Q) hA
  rw [h] at h1
  have h2 : P.real A = Q.real A := by linarith [abs_nonneg (P.real A - Q.real A), abs_le.1 h1]
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top P A) (measure_ne_top Q A)).1 h2

/-- Monotonicity of `c ↦ c • R`. -/
theorem smul_le_smul_of_le (R : Measure α) {c c' : ℝ≥0∞} (h : c ≤ c') : c • R ≤ c' • R :=
  Measure.le_iff'.2 fun s => by
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul_left h _

/-- **A trimming is a renormalised removal.** For a probability measure `P`, `0 ≤ α < 1` and a measurable `g` with
`0 ≤ g ≤ (1−α)⁻¹`, `∫ g dP = 1`, the measure `ν = P − (1−α)·(g·P)` satisfies `ν ≤ P`, `ν(𝒳) = α`, and
`g·P = (1 − ν(𝒳))⁻¹ • (P − ν)`. -/
theorem exists_removal_of_density (P : Measure α) [IsProbabilityMeasure P] {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    {g : α → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1 / (1 - a)) (hgi : ∫ x, g x ∂P = 1) :
    ∃ ν : Measure α, ν ≤ P ∧ ν.real univ = a ∧
      P.withDensity (fun x => ENNReal.ofReal (g x)) = (ENNReal.ofReal (1 - ν.real univ))⁻¹ • (P - ν) := by
  have hs : 0 < 1 - a := by linarith
  set μ := P.withDensity fun x => ENNReal.ofReal (g x) with hμ
  have hint : Integrable g P :=
    Integrable.of_mem_Icc 0 (1 / (1 - a)) hg.aemeasurable (ae_of_all _ fun x => ⟨hg0 x, hg1 x⟩)
  have hμprob : IsProbabilityMeasure μ := isProbabilityMeasure_withDensity_ofReal P hint hg0 hgi
  have hcg : ∀ x, (1 - a) * g x ≤ 1 := fun x => by
    have := mul_le_mul_of_nonneg_left (hg1 x) hs.le
    rwa [mul_one_div_cancel hs.ne'] at this
  have hXP : ENNReal.ofReal (1 - a) • μ ≤ P := smul_withDensity_ofReal_le P hg hs.le hcg
  set X := ENNReal.ofReal (1 - a) • μ with hX
  have : IsFiniteMeasure X := isFiniteMeasure_of_le P hXP
  obtain ⟨ν, hν⟩ : ∃ ν, ν = P - X := ⟨_, rfl⟩
  have hνP : ν ≤ P := hν ▸ Measure.sub_le
  have : IsFiniteMeasure ν := isFiniteMeasure_of_le P hνP
  have hsum : ν + X = P := hν ▸ Measure.sub_add_cancel_of_le hXP
  have hXu : X univ = ENNReal.ofReal (1 - a) := by
    rw [hX, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  have hνu : ν.real univ = a := by
    have h1 := congrArg (fun m : Measure α => m.real univ) hsum
    simp only [probReal_univ] at h1
    rw [measureReal_def, Measure.add_apply, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at h1
    change ν.real univ + X.real univ = 1 at h1
    have h2 : X.real univ = 1 - a := by
      rw [measureReal_def, hXu, ENNReal.toReal_ofReal hs.le]
    linarith
  have hPν : P - ν = X := by
    rw [← hsum, add_comm]
    exact Measure.add_sub_cancel
  refine ⟨ν, hνP, hνu, ?_⟩
  rw [hPν, hνu, hX, smul_smul, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hs).ne' ENNReal.ofReal_ne_top, one_smul]

/-- **A renormalised removal is a trimming.** For a probability measure `P`, `ν ≤ P` with `ν(𝒳) ≤ α < 1`, the law
`(1 − ν(𝒳))⁻¹ • (P − ν)` is `g·P` for a measurable `g` with `0 ≤ g ≤ (1−α)⁻¹` and `∫ g dP = 1`. -/
theorem exists_density_of_removal (P : Measure α) [IsProbabilityMeasure P] {a : ℝ} (ha1 : a < 1) {ν : Measure α}
    (hνP : ν ≤ P) (hνa : ν.real univ ≤ a) :
    ∃ g : α → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x ∧ g x ≤ 1 / (1 - a)) ∧ ∫ x, g x ∂P = 1 ∧
      (ENNReal.ofReal (1 - ν.real univ))⁻¹ • (P - ν) = P.withDensity (fun x => ENNReal.ofReal (g x)) := by
  have : IsFiniteMeasure ν := isFiniteMeasure_of_le P hνP
  set s := ν.real univ with hsdef
  have hs0 : 0 ≤ s := measureReal_nonneg
  have hs1 : 0 < 1 - s := by linarith
  set Y := P - ν with hY
  have hYP : Y ≤ P := Measure.sub_le
  have : IsFiniteMeasure Y := isFiniteMeasure_of_le P hYP
  have hac : Y ≪ P := Measure.absolutelyContinuous_of_le hYP
  set h : α → ℝ := fun x => min 1 (Y.rnDeriv P x).toReal with hh
  have hhm : Measurable h := measurable_const.min (Measure.measurable_rnDeriv Y P).ennreal_toReal
  have hh0 : ∀ x, 0 ≤ h x := fun x => le_min zero_le_one ENNReal.toReal_nonneg
  have hh1 : ∀ x, h x ≤ 1 := fun x => min_le_left _ _
  have hYh : Y = P.withDensity fun x => ENNReal.ofReal (h x) := by
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq Y P hac]
    refine withDensity_congr_ae ?_
    filter_upwards [Measure.rnDeriv_le_one_of_le hYP] with x hx
    have hx' : Y.rnDeriv P x ≤ 1 := hx
    have hne : Y.rnDeriv P x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hx'
    have hle : (Y.rnDeriv P x).toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hx')
    simp only [hh, min_eq_right hle, ENNReal.ofReal_toReal hne]
  have hhi : Integrable h P :=
    Integrable.of_mem_Icc 0 1 hhm.aemeasurable (ae_of_all _ fun x => ⟨hh0 x, hh1 x⟩)
  have hYu : Y.real univ = 1 - s := by
    rw [hY, measureReal_def, Measure.sub_apply MeasurableSet.univ hνP, measure_univ,
      ENNReal.toReal_sub_of_le ((Measure.le_iff'.1 hνP univ).trans_eq measure_univ) ENNReal.one_ne_top]
    simp [hsdef, measureReal_def]
  have hint_h : ∫ x, h x ∂P = 1 - s := by
    rw [← hYu, hYh, measureReal_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hhi (ae_of_all _ hh0), ENNReal.toReal_ofReal (integral_nonneg hh0)]
  refine ⟨fun x => (1 - s)⁻¹ * h x, measurable_const.mul hhm, fun x => ⟨mul_nonneg (inv_nonneg.2 hs1.le) (hh0 x), ?_⟩, ?_, ?_⟩
  · have h1 : (1 - s)⁻¹ ≤ (1 - a)⁻¹ := inv_anti₀ (by linarith) (by linarith)
    calc (1 - s)⁻¹ * h x ≤ (1 - s)⁻¹ * 1 := mul_le_mul_of_nonneg_left (hh1 x) (inv_nonneg.2 hs1.le)
      _ ≤ 1 / (1 - a) := by rw [mul_one, one_div]; exact h1
  · rw [integral_const_mul, hint_h, inv_mul_cancel₀ hs1.ne']
  · rw [hYh, ← withDensity_smul _ hhm.ennreal_ofReal]
    congr 1
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← ENNReal.ofReal_inv_of_pos hs1, ← ENNReal.ofReal_mul (inv_nonneg.2 hs1.le)]

end StatFormal.TVFacts
