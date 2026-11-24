import TauCeti.Probability.Quantile

/-!
# Probability integral transform facts for an atomless law (library, `lem:scores`)

For an atomless probability law `F` on `ℝ` with distribution function `F(·) = cdf F`:
* `ae_cdf_mem_Ioo`: `F(y) ∈ (0, 1)` for `F`-a.e. `y`;
* `measure_lt_cdf_le`: `F{y < y₀ : F(y₀) ≤ F(y)} = 0` (no mass strictly inside a plateau to the left of `y₀`);
* `ae_le_iff_cdf_le`: for a fixed finite sample `x`, `F`-a.e. `y` has `x_i ≤ y ↔ F(x_i) ≤ F(y)` for all `i`
  (so `F_n(y) = G_n(F(y))` with `G_n` the empirical distribution function of the `F(x_i)`);
* `lintegral_comp_cdf`: `∫⁻ f(F(y)) dF(y) = ∫⁻_{[0,1]} f` (Tau Ceti's probability integral transform).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatFormal.NormalScores

lemma measurable_cdf' (F : Measure ℝ) : Measurable (cdf F) := (cdf F).mono.measurable

variable (F : Measure ℝ) [IsProbabilityMeasure F] [NullSingletonClass F]

lemma ae_cdf_mem_Ioo : ∀ᵐ z ∂F, cdf F z ∈ Ioo (0 : ℝ) 1 := by
  have h : ∀ᵐ s ∂(F.map (cdf F)), s ∈ Ioo (0 : ℝ) 1 := by
    rw [Measure.cdf_map_eq_volume_restrict, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [(((countable_singleton (1 : ℝ)).insert 0)).ae_notMem volume] with s hs hsI
    refine ⟨lt_of_le_of_ne hsI.1 ?_, lt_of_le_of_ne hsI.2 ?_⟩
    · intro h0; exact hs (by simp [← h0])
    · intro h1; exact hs (by simp [h1])
  exact ae_of_ae_map (measurable_cdf' F).aemeasurable h

lemma measure_cdf_lt (c : ℝ) (hc : c ∈ Icc (0 : ℝ) 1) : F {y | cdf F y < c} = ENNReal.ofReal c := by
  have : {y | cdf F y < c} = cdf F ⁻¹' Iio c := rfl
  rw [this, ← Measure.map_apply (measurable_cdf' F) measurableSet_Iio, Measure.cdf_map_eq_volume_restrict,
    Measure.restrict_apply measurableSet_Iio]
  have e : Iio c ∩ Icc (0 : ℝ) 1 = Ico 0 c := by
    ext x; simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_Ico]
    constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, (h2.trans_le hc.2).le⟩
  rw [e, Real.volume_Ico, sub_zero]

/-- No mass strictly to the left of `y₀` on the plateau of `cdf F` at level `F(y₀)`. -/
lemma measure_lt_cdf_le (y0 : ℝ) : F {y | y < y0 ∧ cdf F y0 ≤ cdf F y} = 0 := by
  set T := {y | cdf F y < cdf F y0} with hT
  have hTsub : T ⊆ Iio y0 := fun y hy => by
    by_contra h
    exact absurd (monotone_cdf F (not_lt.1 h)) (not_le.2 hy)
  have hTm : MeasurableSet T := measurableSet_lt (measurable_cdf' F) measurable_const
  have hS : {y | y < y0 ∧ cdf F y0 ≤ cdf F y} ⊆ Iio y0 \ T := fun y hy => ⟨hy.1, not_lt.2 hy.2⟩
  have hIio : F (Iio y0) = ENNReal.ofReal (cdf F y0) := by
    rw [measure_congr Iio_ae_eq_Iic, ← ofReal_cdf]
  have hTv : F T = ENNReal.ofReal (cdf F y0) :=
    measure_cdf_lt F _ ⟨cdf_nonneg F y0, cdf_le_one F y0⟩
  refine le_antisymm ((measure_mono hS).trans ?_) bot_le
  rw [measure_sdiff hTsub hTm.nullMeasurableSet (measure_ne_top _ _), hIio, hTv, tsub_self]

/-- For a fixed finite sample, `F`-a.e. `y` has `x_i ≤ y ↔ F(x_i) ≤ F(y)` for every `i`. -/
lemma ae_le_iff_cdf_le {n : ℕ} (x : Fin n → ℝ) : ∀ᵐ y ∂F, ∀ i, (x i ≤ y ↔ cdf F (x i) ≤ cdf F y) := by
  rw [ae_all_iff]
  intro i
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_lt_cdf_le F (x i))] with y hy
  refine ⟨fun h => monotone_cdf F h, fun h => ?_⟩
  by_contra h'
  exact hy ⟨not_le.1 h', h⟩

/-- The probability integral transform in integral form. -/
lemma lintegral_comp_cdf {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f (cdf F y) ∂F = ∫⁻ u in Icc (0 : ℝ) 1, f u := by
  rw [← lintegral_map hf (measurable_cdf' F), Measure.cdf_map_eq_volume_restrict]

end StatFormal.NormalScores
