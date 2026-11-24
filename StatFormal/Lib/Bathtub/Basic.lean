import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Continuity

/-!
# The bathtub principle

Library component (robust equality, JASA, `lem:lindsay`, density-bounded class). Untrusted library code.

## Main results

* `exists_level_measure_eq`: for a bounded measurable `D` with no level set of positive measure on a set `K` of
  finite measure, every value `0 < a ≤ μ K` is attained as `μ (K ∩ {θ < D})` for some `θ`;
* `bathtub_integral_le`: if `μ (K ∩ {θ < D}) = 1/M` and `ν` is a probability measure with `ν ≤ M • μ|_K`, then
  `∫ D dν ≤ M ∫_{K ∩ {θ < D}} D dμ`;
* `bathtub_mem` / `bathtub_integral_eq`: the extremal measure `M • μ|_{K ∩ {θ < D}}` is such a probability measure
  and attains the bound.
-/

set_option linter.style.longLine false
set_option linter.style.show false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.Bathtub

variable {X : Type*} [MeasurableSpace X]

/-- Level-set intermediate value theorem. -/
theorem exists_level_measure_eq (μ : Measure X) {K : Set X} (hK : MeasurableSet K) (hKfin : μ K ≠ ∞)
    {D : X → ℝ} (hD : Measurable D) {C : ℝ} (hC : ∀ x, |D x| ≤ C)
    (hlev : ∀ t : ℝ, μ (K ∩ {x | D x = t}) = 0) {a : ℝ≥0∞} (ha0 : 0 < a) (haK : a ≤ μ K) :
    ∃ θ : ℝ, μ (K ∩ {x | θ < D x}) = a := by
  set F : ℝ → ℝ≥0∞ := fun t => μ (K ∩ {x | t < D x}) with hFdef
  have hFanti : Antitone F := fun s t hst =>
    measure_mono (inter_subset_inter_right _ fun x (hx : t < D x) => lt_of_le_of_lt hst hx)
  set S : Set ℝ := {t | a ≤ F t}
  have hbdd : BddAbove S := by
    refine ⟨C, fun t (ht : a ≤ F t) => ?_⟩
    by_contra h
    push_neg at h
    have : F t = 0 := by
      have : K ∩ {x | t < D x} = ∅ := by
        ext x
        simp only [mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_lt]
        intro _
        exact ((le_abs_self _).trans (hC x)).trans h.le
      simp [hFdef, this]
    exact absurd (ht.trans_eq this) (not_le.2 ha0)
  have hne : S.Nonempty := by
    refine ⟨-C - 1, ?_⟩
    show a ≤ F (-C - 1)
    have : K ∩ {x | -C - 1 < D x} = K := by
      refine inter_eq_left.2 fun x _ => ?_
      have := neg_abs_le (D x)
      have := hC x
      show -C - 1 < D x
      linarith
    simp only [hFdef, this]
    exact haK
  set θ := sSup S
  refine ⟨θ, le_antisymm ?_ ?_⟩
  · -- right continuity: `F θ ≤ a`
    have hU : K ∩ {x | θ < D x} = ⋃ k : ℕ, K ∩ {x | θ + 1 / ((k : ℝ) + 1) < D x} := by
      ext x
      simp only [mem_inter_iff, mem_setOf_eq, mem_iUnion]
      constructor
      · rintro ⟨hxK, hx⟩
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
        exact ⟨k, hxK, by linarith⟩
      · rintro ⟨k, hxK, hk⟩
        refine ⟨hxK, lt_trans ?_ hk⟩
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
    have hmono : Monotone fun k : ℕ => K ∩ {x | θ + 1 / ((k : ℝ) + 1) < D x} := by
      intro i j hij
      refine inter_subset_inter_right _ fun x (hx : θ + 1 / ((i : ℝ) + 1) < D x) => ?_
      show θ + 1 / ((j : ℝ) + 1) < D x
      have : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) := by
        gcongr
      linarith
    have ht := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rw [← hU] at ht
    refine le_of_tendsto' ht fun k => ?_
    show F (θ + 1 / ((k : ℝ) + 1)) ≤ a
    by_contra h
    push_neg at h
    have hmem : θ + 1 / ((k : ℝ) + 1) ∈ S := h.le
    have := le_csSup hbdd hmem
    have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    linarith
  · -- left continuity, using that the level set `{D = θ}` is null
    have hI : K ∩ {x | θ ≤ D x} = ⋂ k : ℕ, K ∩ {x | θ - 1 / ((k : ℝ) + 1) < D x} := by
      ext x
      simp only [mem_inter_iff, mem_setOf_eq, mem_iInter]
      constructor
      · rintro ⟨hxK, hx⟩ k
        refine ⟨hxK, lt_of_lt_of_le ?_ hx⟩
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
      · intro h
        refine ⟨(h 0).1, ?_⟩
        by_contra hx
        push_neg at hx
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
        have := (h k).2
        linarith
    have hanti : Antitone fun k : ℕ => K ∩ {x | θ - 1 / ((k : ℝ) + 1) < D x} := by
      intro i j hij
      refine inter_subset_inter_right _ fun x (hx : θ - 1 / ((j : ℝ) + 1) < D x) => ?_
      show θ - 1 / ((i : ℝ) + 1) < D x
      have : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) := by
        gcongr
      linarith
    have hmeas : ∀ k : ℕ, NullMeasurableSet (K ∩ {x | θ - 1 / ((k : ℝ) + 1) < D x}) μ := fun k =>
      (hK.inter (measurableSet_lt measurable_const hD)).nullMeasurableSet
    have ht := tendsto_measure_iInter_atTop (μ := μ) hmeas hanti
      ⟨0, ne_top_of_le_ne_top hKfin (measure_mono inter_subset_left)⟩
    rw [← hI] at ht
    have h1 : a ≤ μ (K ∩ {x | θ ≤ D x}) := by
      refine ge_of_tendsto' ht fun k => ?_
      show a ≤ F (θ - 1 / ((k : ℝ) + 1))
      have hlt : θ - 1 / ((k : ℝ) + 1) < sSup S := by
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
      obtain ⟨t, htS, ht⟩ := exists_lt_of_lt_csSup hne hlt
      exact htS.trans (hFanti ht.le)
    refine h1.trans ?_
    calc μ (K ∩ {x | θ ≤ D x}) ≤ μ (K ∩ {x | θ < D x} ∪ K ∩ {x | D x = θ}) := by
          refine measure_mono fun x ⟨hxK, hx⟩ => ?_
          rcases (show θ ≤ D x from hx).lt_or_eq with h | h
          · exact Or.inl ⟨hxK, h⟩
          · exact Or.inr ⟨hxK, h.symm⟩
      _ ≤ μ (K ∩ {x | θ < D x}) + μ (K ∩ {x | D x = θ}) := measure_union_le _ _
      _ = F θ := by rw [hlev θ, add_zero]

/-- The bathtub inequality. -/
theorem bathtub_integral_le (μ : Measure X) {K : Set X} (hK : MeasurableSet K) (hKfin : μ K ≠ ∞)
    {D : X → ℝ} (hD : Measurable D) {C : ℝ} (hC : ∀ x, |D x| ≤ C) {M θ : ℝ} (hM : 0 < M)
    (hθ : μ (K ∩ {x | θ < D x}) = ENNReal.ofReal (1 / M)) (ν : Measure X) [IsProbabilityMeasure ν]
    (hν : ν ≤ ENNReal.ofReal M • μ.restrict K) :
    ∫ x, D x ∂ν ≤ M * ∫ x in K ∩ {x | θ < D x}, D x ∂μ := by
  set T := K ∩ {x | θ < D x}
  have hTmeas : MeasurableSet T := hK.inter (measurableSet_lt measurable_const hD)
  have hTfin : μ T ≠ ∞ := ne_top_of_le_ne_top hKfin (measure_mono inter_subset_left)
  have : IsFiniteMeasure (μ.restrict K) := ⟨by rw [Measure.restrict_apply_univ]; exact hKfin.lt_top⟩
  have : IsFiniteMeasure (μ.restrict T) := ⟨by rw [Measure.restrict_apply_univ]; exact hTfin.lt_top⟩
  have hDint : ∀ (ρ : Measure X) [IsFiniteMeasure ρ], Integrable D ρ := fun ρ _ =>
    Integrable.of_bound hD.aestronglyMeasurable C (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hC x)
  set g : X → ℝ := fun x => max (D x - θ) 0
  have hgm : Measurable g := (hD.sub measurable_const).max measurable_const
  have hgint : ∀ (ρ : Measure X) [IsFiniteMeasure ρ], Integrable g ρ := fun ρ _ =>
    Integrable.of_bound hgm.aestronglyMeasurable (C + |θ|) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      have h1 := hC x
      have h2 := abs_le.1 h1
      have h3 := abs_le.1 (le_refl |θ|)
      rw [abs_le]
      constructor
      · have : 0 ≤ g x := le_max_right _ _
        have : 0 ≤ |θ| := abs_nonneg θ
        linarith
      · show max (D x - θ) 0 ≤ C + |θ|
        refine max_le (by linarith) (by have := abs_nonneg θ; linarith))
  have hg_eq : g = {x | θ < D x}.indicator (fun x => D x - θ) := by
    funext x
    by_cases hx : θ < D x
    · rw [indicator_of_mem (show x ∈ {x | θ < D x} from hx)]
      exact max_eq_left (by linarith)
    · rw [indicator_of_notMem (show x ∉ {x | θ < D x} from hx)]
      exact max_eq_right (by push_neg at hx; linarith)
  have hθr : μ.real T = 1 / M := by
    rw [measureReal_def, hθ, ENNReal.toReal_ofReal (by positivity)]
  calc ∫ x, D x ∂ν = ∫ x, (D x - θ) ∂ν + θ := by
        rw [integral_sub (hDint ν) (integrable_const θ)]
        simp
    _ ≤ ∫ x, g x ∂ν + θ := by
        refine add_le_add_left ?_ θ
        exact integral_mono ((hDint ν).sub (integrable_const θ)) (hgint ν) fun x => le_max_left _ _
    _ ≤ ∫ x, g x ∂(ENNReal.ofReal M • μ.restrict K) + θ := by
        refine add_le_add_left ?_ θ
        exact integral_mono_measure hν (Eventually.of_forall fun x => le_max_right _ _)
          ((hgint (μ.restrict K)).smul_measure ENNReal.ofReal_ne_top)
    _ = M * ∫ x in T, (D x - θ) ∂μ + θ := by
        rw [integral_smul_measure, ENNReal.toReal_ofReal hM.le, smul_eq_mul, hg_eq,
          integral_indicator (measurableSet_lt measurable_const hD),
          Measure.restrict_restrict (measurableSet_lt measurable_const hD), inter_comm]
    _ = M * (∫ x in T, D x ∂μ - θ * (1 / M)) + θ := by
        rw [integral_sub (hDint _) (integrable_const θ), setIntegral_const, hθr, smul_eq_mul,
          mul_comm (1 / M)]
    _ = M * ∫ x in T, D x ∂μ := by
        field_simp
        ring

/-- The extremal measure `M • μ|_{K ∩ {θ < D}}` is a probability measure below `M • μ|_K`. -/
theorem bathtub_mem (μ : Measure X) {K : Set X} {D : X → ℝ} {M θ : ℝ} (hM : 0 < M)
    (hθ : μ (K ∩ {x | θ < D x}) = ENNReal.ofReal (1 / M)) :
    IsProbabilityMeasure (ENNReal.ofReal M • μ.restrict (K ∩ {x | θ < D x})) ∧
      ENNReal.ofReal M • μ.restrict (K ∩ {x | θ < D x}) ≤ ENNReal.ofReal M • μ.restrict K := by
  refine ⟨⟨?_⟩, ?_⟩
  · rw [Measure.smul_apply, Measure.restrict_apply_univ, hθ, smul_eq_mul,
      ← ENNReal.ofReal_mul hM.le, mul_one_div_cancel hM.ne', ENNReal.ofReal_one]
  · refine Measure.le_iff.2 fun s _ => ?_
    simp only [Measure.smul_apply, smul_eq_mul]
    gcongr
    exact inter_subset_left

/-- The extremal measure attains the bathtub bound. -/
theorem bathtub_integral_eq (μ : Measure X) {S : Set X} {D : X → ℝ} {M : ℝ} (hM : 0 < M) :
    ∫ x, D x ∂(ENNReal.ofReal M • μ.restrict S) = M * ∫ x in S, D x ∂μ := by
  rw [integral_smul_measure, ENNReal.toReal_ofReal hM.le, smul_eq_mul]

end StatFormal.Bathtub
