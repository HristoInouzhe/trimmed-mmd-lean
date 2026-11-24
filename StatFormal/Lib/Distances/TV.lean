import TauCeti.InformationTheory.KullbackLeibler.Pinsker
import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Total variation distance

Library component F.H (part 1). Untrusted library code: no `Statements.lean` is involved.

## Convention

`tvDist μ ν := ⨆ A measurable, |μ.real A - ν.real A|` — the *usual* total-variation distance, with
values in `[0, 1]` for probability measures. This is syntactically the same definition as
`StatFormal.SBFairness.Stability.tv` (`Measure.real μ s` is by definition `(μ s).toReal`); see
`StatFormal/Foundations/Distances/Bridge.lean` for the `rfl` bridge. For non-finite measures the
`iSup` may be unbounded and then is the junk value `0`; every substantive lemma assumes finiteness.

Mathlib's `(μ.toSignedMeasure - ν.toSignedMeasure).totalVariation univ` is **twice** `tvDist`
(`tvDist_eq_totalVariation_div_two`).

## Main results

* `tvDist_nonneg`, `tvDist_comm`, `tvDist_self`, `tvDist_le_one`, `tvDist_triangle`;
* `abs_measureReal_sub_le_tvDist`, `measureReal_ge_sub_tvDist` (Le Cam event bound);
* `tvDist_eq_totalVariation_div_two` (equal-mass finite measures), `..._of_prob`;
* `abs_integral_sub_le_mul_tvDist`: `|∫ f dμ - ∫ f dν| ≤ (b - a) * tvDist μ ν` for measurable
  `f` with values in `[a, b]` (proved via the Hahn decomposition);
* `tvDist_map_le` (data processing for measurable maps);
* `tvDist_le_sqrt_klDiv` (Pinsker, `tvDist μ ν ≤ √(KL/2)` when `KL ≠ ⊤`).
-/

noncomputable section
open MeasureTheory InformationTheory Set
open scoped ENNReal

namespace StatFormal.Distances

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Total variation distance `sup_A |μ(A) − ν(A)|` over measurable `A` (finite measures). -/
def tvDist (μ ν : Measure α) : ℝ :=
  ⨆ A : {A : Set α // MeasurableSet A}, |μ.real A.1 - ν.real A.1|

instance nonempty_measurableSubtype : Nonempty {A : Set α // MeasurableSet A} :=
  ⟨⟨∅, MeasurableSet.empty⟩⟩

variable {μ ν ρ : Measure α}

theorem tvDist_nonneg (μ ν : Measure α) : 0 ≤ tvDist μ ν :=
  Real.iSup_nonneg fun _ => abs_nonneg _

theorem tvDist_comm (μ ν : Measure α) : tvDist μ ν = tvDist ν μ := by
  simp only [tvDist, abs_sub_comm]

@[simp] theorem tvDist_self (μ : Measure α) : tvDist μ μ = 0 := by
  simp [tvDist]

theorem bddAbove_tvDist [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    BddAbove (Set.range fun A : {A : Set α // MeasurableSet A} => |μ.real A.1 - ν.real A.1|) := by
  refine ⟨μ.real univ + ν.real univ, ?_⟩
  rintro _ ⟨A, rfl⟩
  have h1 : μ.real A.1 ≤ μ.real univ := measureReal_mono (subset_univ _)
  have h2 : ν.real A.1 ≤ ν.real univ := measureReal_mono (subset_univ _)
  have h3 : 0 ≤ μ.real A.1 := measureReal_nonneg
  have h4 : 0 ≤ ν.real A.1 := measureReal_nonneg
  rw [abs_le]; constructor <;> linarith

theorem abs_measureReal_sub_le_tvDist [IsFiniteMeasure μ] [IsFiniteMeasure ν] {A : Set α}
    (hA : MeasurableSet A) : |μ.real A - ν.real A| ≤ tvDist μ ν :=
  le_ciSup (f := fun A : {A : Set α // MeasurableSet A} => |μ.real A.1 - ν.real A.1|)
    bddAbove_tvDist ⟨A, hA⟩

theorem tvDist_le_of_forall {c : ℝ} (h : ∀ A, MeasurableSet A → |μ.real A - ν.real A| ≤ c) :
    tvDist μ ν ≤ c :=
  ciSup_le fun A => h A.1 A.2

theorem tvDist_le_one [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : tvDist μ ν ≤ 1 := by
  refine tvDist_le_of_forall fun A _ => ?_
  have h1 : μ.real A ≤ 1 := (measureReal_mono (subset_univ A)).trans_eq probReal_univ
  have h2 : ν.real A ≤ 1 := (measureReal_mono (subset_univ A)).trans_eq probReal_univ
  have h3 : 0 ≤ μ.real A := measureReal_nonneg
  have h4 : 0 ≤ ν.real A := measureReal_nonneg
  rw [abs_le]; constructor <;> linarith

theorem tvDist_triangle [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ρ] :
    tvDist μ ρ ≤ tvDist μ ν + tvDist ν ρ := by
  refine tvDist_le_of_forall fun A hA => ?_
  calc |μ.real A - ρ.real A| ≤ |μ.real A - ν.real A| + |ν.real A - ρ.real A| :=
        abs_sub_le _ _ _
    _ ≤ tvDist μ ν + tvDist ν ρ :=
        add_le_add (abs_measureReal_sub_le_tvDist hA) (abs_measureReal_sub_le_tvDist hA)

/-- **Le Cam event bound**: `μ(A) ≥ ν(A) − TV(μ, ν)`. -/
theorem measureReal_ge_sub_tvDist [IsFiniteMeasure μ] [IsFiniteMeasure ν] {A : Set α}
    (hA : MeasurableSet A) : ν.real A - tvDist μ ν ≤ μ.real A := by
  have h1 := abs_measureReal_sub_le_tvDist (μ := μ) (ν := ν) hA
  have h2 := neg_abs_le (μ.real A - ν.real A)
  linarith

/-! ### Bridge with Mathlib's signed-measure total variation -/

private theorem real_le_of_le {A : Set α} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {c : ℝ≥0∞}
    (hc : c ≠ ∞) (h : μ A ≤ ν A + c) : μ.real A ≤ ν.real A + c.toReal := by
  have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top ν A, hc⟩) h
  rwa [ENNReal.toReal_add (measure_ne_top ν A) hc] at this

/-- For finite measures of equal mass, Mathlib's total variation of `μ - ν` on `univ` is twice
`tvDist μ ν`. -/
theorem tvDist_eq_totalVariation_div_two [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmass : μ univ = ν univ) :
    tvDist μ ν = ((μ.toSignedMeasure - ν.toSignedMeasure).totalVariation univ).toReal / 2 := by
  set T := (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation univ with hT
  have hTfin : T ≠ ∞ := measure_ne_top _ _
  have hT' : (ν.toSignedMeasure - μ.toSignedMeasure).totalVariation univ = T := by
    rw [hT, ← neg_sub, SignedMeasure.totalVariation_neg]
  apply le_antisymm
  · have hT2 : T ≤ 2 * (T / 2) := by
      rw [ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top]
    have hT2' : (ν.toSignedMeasure - μ.toSignedMeasure).totalVariation univ ≤ 2 * (T / 2) := by
      rw [hT']; exact hT2
    have h1 : ∀ A, MeasurableSet A → μ A ≤ ν A + T / 2 :=
      (Measure.totalVariation_toSignedMeasure_sub_univ_le_two_mul_iff hmass).1 hT2
    have h2 : ∀ A, MeasurableSet A → ν A ≤ μ A + T / 2 :=
      (Measure.totalVariation_toSignedMeasure_sub_univ_le_two_mul_iff hmass.symm).1 hT2'
    have hhalf : (T / 2).toReal = T.toReal / 2 := by
      rw [ENNReal.toReal_div]; simp
    have hc : T / 2 ≠ ∞ := ENNReal.div_ne_top hTfin two_ne_zero
    refine tvDist_le_of_forall fun A hA => ?_
    have e1 : μ.real A ≤ ν.real A + (T / 2).toReal := real_le_of_le hc (h1 A hA)
    have e2 : ν.real A ≤ μ.real A + (T / 2).toReal := real_le_of_le hc (h2 A hA)
    rw [hhalf] at e1 e2
    rw [abs_le]; constructor <;> linarith
  · set d := tvDist μ ν
    have hd : 0 ≤ d := tvDist_nonneg μ ν
    have hev : ∀ A, MeasurableSet A → μ A ≤ ν A + ENNReal.ofReal d := by
      intro A hA
      have h := abs_measureReal_sub_le_tvDist (μ := μ) (ν := ν) hA
      have h' : μ.real A ≤ ν.real A + d := by
        have := le_abs_self (μ.real A - ν.real A); linarith
      rw [← ofReal_measureReal (measure_ne_top μ A), ← ofReal_measureReal (measure_ne_top ν A),
        ← ENNReal.ofReal_add measureReal_nonneg hd]
      exact ENNReal.ofReal_le_ofReal h'
    have hle := (Measure.totalVariation_toSignedMeasure_sub_univ_le_two_mul_iff hmass).2 hev
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top) hle
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hd] at this
    simp only [ENNReal.toReal_ofNat] at this
    rw [← hT] at this
    linarith

theorem tvDist_eq_totalVariation_div_two_of_prob [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    tvDist μ ν = ((μ.toSignedMeasure - ν.toSignedMeasure).totalVariation univ).toReal / 2 :=
  tvDist_eq_totalVariation_div_two (by simp)

/-! ### Integral bound -/

/-- One-sided integral bound: for measurable `0 ≤ g ≤ c`, `∫ g dμ − ∫ g dν ≤ c · TV(μ, ν)`. -/
theorem integral_sub_le_mul_tvDist_of_nonneg [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {g : α → ℝ} (hg : Measurable g) {c : ℝ} (hc : 0 ≤ c) (hg0 : ∀ x, 0 ≤ g x)
    (hgc : ∀ x, g x ≤ c) : ∫ x, g x ∂μ - ∫ x, g x ∂ν ≤ c * tvDist μ ν := by
  obtain ⟨s, hs, hs₁, hs₂⟩ := hahn_decomposition μ ν
  have hint : ∀ ρ : Measure α, IsFiniteMeasure ρ → Integrable g ρ := fun ρ _ =>
    Integrable.of_mem_Icc 0 c hg.aemeasurable (ae_of_all _ fun x => ⟨hg0 x, hgc x⟩)
  have hleS : ν.restrict s ≤ μ.restrict s := by
    refine Measure.le_iff.2 fun t ht => ?_
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
    exact hs₁ _ (ht.inter hs) inter_subset_right
  have hleSc : μ.restrict sᶜ ≤ ν.restrict sᶜ := by
    refine Measure.le_iff.2 fun t ht => ?_
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
    exact hs₂ _ (ht.inter hs.compl) inter_subset_right
  -- the part on `sᶜ`
  have hSc : ∫ x in sᶜ, g x ∂μ ≤ ∫ x in sᶜ, g x ∂ν :=
    integral_mono_measure hleSc (ae_of_all _ hg0) (hint _ inferInstance)
  -- the part on `s`
  set D := μ.restrict s - ν.restrict s with hD
  have hDfin : IsFiniteMeasure D := isFiniteMeasure_of_le _ Measure.sub_le
  have hdecomp : D + ν.restrict s = μ.restrict s := Measure.sub_add_cancel_of_le hleS
  have hS : ∫ x in s, g x ∂μ = ∫ x, g x ∂D + ∫ x in s, g x ∂ν := by
    conv_lhs => rw [← hdecomp]
    exact integral_add_measure (hint _ hDfin) (hint _ inferInstance)
  have hDint : ∫ x, g x ∂D ≤ c * D.real univ := by
    calc ∫ x, g x ∂D ≤ ∫ _x, c ∂D :=
          integral_mono (hint _ hDfin) (integrable_const c) hgc
      _ = c * D.real univ := by rw [integral_const, smul_eq_mul, mul_comm]
  have hDuniv : D.real univ = μ.real s - ν.real s := by
    rw [measureReal_def, hD, Measure.sub_apply MeasurableSet.univ hleS,
      Measure.restrict_apply_univ, Measure.restrict_apply_univ,
      ENNReal.toReal_sub_of_le (hs₁ s hs subset_rfl) (measure_ne_top μ s)]
    rfl
  have hts : μ.real s - ν.real s ≤ tvDist μ ν :=
    (le_abs_self _).trans (abs_measureReal_sub_le_tvDist hs)
  rw [← integral_add_compl hs (hint μ inferInstance),
    ← integral_add_compl hs (hint ν inferInstance), hS]
  rw [hDuniv] at hDint
  nlinarith

/-- **Integral bound**: for measurable `f` with values in `[a, b]` and probability measures,
`|∫ f dμ − ∫ f dν| ≤ (b − a) · TV(μ, ν)`. -/
theorem abs_integral_sub_le_mul_tvDist [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : α → ℝ} (hf : Measurable f) {a b : ℝ} (hfab : ∀ x, f x ∈ Icc a b) :
    |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ (b - a) * tvDist μ ν := by
  have : Nonempty α := nonempty_of_isProbabilityMeasure μ
  have hab : a ≤ b := let x := Classical.arbitrary α; (hfab x).1.trans (hfab x).2
  have hint : ∀ ρ : Measure α, IsProbabilityMeasure ρ → Integrable f ρ := fun ρ _ =>
    Integrable.of_mem_Icc a b hf.aemeasurable (ae_of_all _ hfab)
  have hshift : ∀ ρ : Measure α, IsProbabilityMeasure ρ →
      ∫ x, (f x - a) ∂ρ = ∫ x, f x ∂ρ - a := fun ρ _ => by
    rw [integral_sub (hint ρ inferInstance) (integrable_const a), integral_const, probReal_univ,
      one_smul]
  have hg : Measurable fun x => f x - a := hf.sub measurable_const
  have hg0 : ∀ x, 0 ≤ f x - a := fun x => sub_nonneg.2 (hfab x).1
  have hgc : ∀ x, f x - a ≤ b - a := fun x => sub_le_sub_right (hfab x).2 a
  have h1 := integral_sub_le_mul_tvDist_of_nonneg (μ := μ) (ν := ν) hg (sub_nonneg.2 hab) hg0 hgc
  have h2 := integral_sub_le_mul_tvDist_of_nonneg (μ := ν) (ν := μ) hg (sub_nonneg.2 hab) hg0 hgc
  rw [hshift μ inferInstance, hshift ν inferInstance] at h1 h2
  rw [tvDist_comm] at h2
  rw [abs_le]; constructor <;> linarith

/-! ### Data processing -/

/-- **Data processing** for total variation under a measurable map. -/
theorem tvDist_map_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] {f : α → β} (hf : Measurable f) :
    tvDist (μ.map f) (ν.map f) ≤ tvDist μ ν := by
  refine tvDist_le_of_forall fun A hA => ?_
  simp only [measureReal_def, Measure.map_apply hf hA]
  exact abs_measureReal_sub_le_tvDist (hf hA)

/-- Total variation is invariant under measurable equivalences. -/
theorem tvDist_map_measurableEquiv [IsFiniteMeasure μ] [IsFiniteMeasure ν] (e : α ≃ᵐ β) :
    tvDist (μ.map e) (ν.map e) = tvDist μ ν := by
  refine le_antisymm (tvDist_map_le e.measurable) ?_
  have h := tvDist_map_le (μ := μ.map e) (ν := ν.map e) e.symm.measurable
  rwa [MeasurableEquiv.map_symm_map, MeasurableEquiv.map_symm_map] at h

/-! ### Pinsker -/

/-- **Pinsker's inequality** in the `tvDist` normalisation: `TV(μ, ν) ≤ √(KL(μ‖ν)/2)` whenever the
relative entropy is finite. -/
theorem tvDist_le_sqrt_klDiv [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : klDiv μ ν ≠ ∞) : tvDist μ ν ≤ √((klDiv μ ν).toReal / 2) := by
  refine tvDist_le_of_forall fun A hA => ?_
  have hp := TauCeti.two_mul_sq_measureReal_sub_le_klDiv (μ := μ) (ν := ν) hA
  rw [ENNReal.ofReal_le_iff_le_toReal h] at hp
  exact Real.abs_le_sqrt (by linarith)

end StatFormal.Distances
