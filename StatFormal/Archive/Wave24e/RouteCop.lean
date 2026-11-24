import StatFormal.Archive.Wave24e.Statements

/-!
# Route — SB `cor:field-cop` (untrusted)

* `S_μ^{-1}(S_μ x) = x` `μ`-a.e.: coordinatewise, Tau Ceti's `quantile_cdf_ae` (quantile of the cdf is the identity
  almost everywhere, for every law on `ℝ`), pulled back along the coordinate maps; hence also
  `S_μ(S_μ^{-1} u) = u` for `C_μ`-a.e. `u`.
* Uniform marginals of `C_μ`: the probability integral transform (`cdf_map_eq_volume_restrict`, atomless marginal).
* Exactness: `(S_ν^{-1} ∘ S_R)_#R = (S_ν^{-1})_#(S_ν)_#ν = ν`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter

namespace StatFormal.Wave24e

open StatFormal.Wave9b (Standardises)

variable {d : ℕ}

lemma measurable_coord (k : Fin d) : Measurable fun y : EuclideanSpace ℝ (Fin d) => y k :=
  (measurable_pi_apply k).comp (WithLp.measurable_ofLp (p := 2) (X := Fin d → ℝ))

lemma measurable_copStd (μ : Measure (EuclideanSpace ℝ (Fin d))) : Measurable (copStd μ) :=
  (WithLp.measurable_toLp (p := 2) (X := Fin d → ℝ)).comp
    (Measurable.of_eval fun k => (cdf _).mono.measurable.comp (measurable_coord k))

lemma measurable_copInv (μ : Measure (EuclideanSpace ℝ (Fin d))) : Measurable (copInv μ) :=
  (WithLp.measurable_toLp (p := 2) (X := Fin d → ℝ)).comp
    (Measurable.of_eval fun k => (MeasureTheory.Measure.measurable_quantile _).comp (measurable_coord k))

lemma copInv_copStd_ae (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] :
    ∀ᵐ x ∂μ, copInv μ (copStd μ x) = x := by
  have hk : ∀ k, ∀ᵐ x ∂μ, (μ.map fun y : EuclideanSpace ℝ (Fin d) => y k).quantile
      (cdf (μ.map fun y : EuclideanSpace ℝ (Fin d) => y k) (x k)) = x k := by
    intro k
    have h := MeasureTheory.Measure.quantile_cdf_ae (μ.map fun y : EuclideanSpace ℝ (Fin d) => y k)
    exact ae_of_ae_map (measurable_coord k).aemeasurable h
  rw [← ae_all_iff] at hk
  filter_upwards [hk] with x hx
  ext k
  simp only [copInv, copStd]
  exact hx k

theorem field_cop_standardises : Claims.field_cop_standardises := by
  intro d μ _ hatom
  refine ⟨fun k => ?_, measurable_copStd μ, measurable_copInv μ, rfl, copInv_copStd_ae μ, ?_⟩
  · haveI : NullSingletonClass (μ.map fun y : EuclideanSpace ℝ (Fin d) => y k) := ⟨hatom k⟩
    rw [Measure.map_map (measurable_coord k) (measurable_copStd μ)]
    have : (fun u : EuclideanSpace ℝ (Fin d) => u k) ∘ copStd μ =
        cdf (μ.map fun y : EuclideanSpace ℝ (Fin d) => y k) ∘ fun y => y k := by
      funext x; simp [copStd]
    rw [this, ← Measure.map_map (cdf _).mono.measurable (measurable_coord k)]
    exact MeasureTheory.Measure.cdf_map_eq_volume_restrict _
  · have hmeas : MeasurableSet {u : EuclideanSpace ℝ (Fin d) | copStd μ (copInv μ u) = u} :=
      measurableSet_eq_fun ((measurable_copStd μ).comp (measurable_copInv μ)) measurable_id
    rw [ae_map_iff (measurable_copStd μ).aemeasurable hmeas]
    filter_upwards [copInv_copStd_ae μ] with x hx
    simp only [mem_setOf_eq, hx]

theorem field_cop_exact : Claims.field_cop_exact := by
  intro d R ν _ _ _ _ hcop
  rw [← Measure.map_map (measurable_copInv ν) (measurable_copStd R), hcop,
    Measure.map_map (measurable_copInv ν) (measurable_copStd ν)]
  calc ν.map (copInv ν ∘ copStd ν) = ν.map id :=
        Measure.map_congr (by filter_upwards [copInv_copStd_ae ν] with x hx; exact hx)
    _ = ν := Measure.map_id

end StatFormal.Wave24e
