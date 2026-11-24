import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

/-!
# The `h`-transform of a reference measure by a function of a statistic, and the KL chain rule

Setting: `R` a probability measure on `Ω`, `Y : Ω → β` measurable, `R' = R ∘ Y⁻¹`, `π ≪ R'` a probability measure on `β`.
The `h`-transform `htrans R Y π = R.withDensity ((dπ/dR') ∘ Y)` keeps the conditional law of `R` given `Y` and
replaces the law of `Y` by `π` (the "mixture of the reference bridges" when `Y = (X₀, X₁)`).

* `htrans_map`: `(htrans R Y π) ∘ Y⁻¹ = π`; `htrans_map_pair`: the joint law of `(Y, F)` is
  `(R ∘ (Y, F)⁻¹).withDensity ((dπ/dR') ∘ fst)`.
* `klDiv_htrans`: `KL(htrans R Y π ‖ R) = KL(π ‖ R')`.
* `eq_htrans_of_klDiv_le`: if `KL(P ‖ R) < ∞` and `KL(P ‖ R) ≤ KL(P ∘ Y⁻¹ ‖ R')` (equality in the data-processing
  inequality), then `P = htrans R Y (P ∘ Y⁻¹)` (proof: `KL(P ‖ R) = KL(P ‖ htrans) + KL(P ∘ Y⁻¹ ‖ R')`).
* `map_withDensity_comp`: `(λ.withDensity (f ∘ ψ)).map ψ = (λ.map ψ).withDensity f`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set InformationTheory
open scoped ENNReal

set_option linter.style.longLine false

namespace StatFormal.SchrodingerPath

variable {Ω β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace γ]

/-- The `h`-transform of `R` by the density of `π` with respect to the law of `Y`. -/
def htrans (R : Measure Ω) (Y : Ω → β) (π : Measure β) : Measure Ω :=
  R.withDensity (fun ω => π.rnDeriv (R.map Y) (Y ω))

lemma map_withDensity_comp {L : Measure γ} {ψ : γ → β} (hψ : Measurable ψ) {f : β → ℝ≥0∞} (hf : Measurable f) :
    (L.withDensity (f ∘ ψ)).map ψ = (L.map ψ).withDensity f := by
  ext s hs
  rw [Measure.map_apply hψ hs, withDensity_apply _ (hψ hs), withDensity_apply _ hs,
    setLIntegral_map hs hf hψ]
  rfl

variable {R : Measure Ω} [IsProbabilityMeasure R] {Y : Ω → β}

lemma htrans_map (hY : Measurable Y) {π : Measure β} [IsFiniteMeasure π] (hπ : π ≪ R.map Y) :
    (htrans R Y π).map Y = π := by
  have h := map_withDensity_comp (L := R) hY (Measure.measurable_rnDeriv π (R.map Y))
  unfold htrans
  change (R.withDensity ((π.rnDeriv (R.map Y)) ∘ Y)).map Y = π
  rw [h, Measure.withDensity_rnDeriv_eq _ _ hπ]

omit [IsProbabilityMeasure R] in
lemma htrans_map_pair (hY : Measurable Y) {F : Ω → γ} (hF : Measurable F) (π : Measure β) :
    (htrans R Y π).map (fun ω => (Y ω, F ω)) =
      (R.map (fun ω => (Y ω, F ω))).withDensity (fun p => π.rnDeriv (R.map Y) p.1) := by
  have hYF : Measurable (fun ω => (Y ω, F ω)) := hY.prodMk hF
  have h := map_withDensity_comp (L := R) hYF
    ((Measure.measurable_rnDeriv π (R.map Y)).comp measurable_fst)
  unfold htrans
  exact h

lemma isProbabilityMeasure_htrans (hY : Measurable Y) {π : Measure β} [IsProbabilityMeasure π]
    (hπ : π ≪ R.map Y) : IsProbabilityMeasure (htrans R Y π) := by
  have h := htrans_map hY hπ
  have : IsProbabilityMeasure ((htrans R Y π).map Y) := by rw [h]; infer_instance
  exact Measure.isProbabilityMeasure_of_map hY.aemeasurable

omit [IsProbabilityMeasure R] in
lemma htrans_ac (π : Measure β) : htrans R Y π ≪ R := withDensity_absolutelyContinuous _ _

lemma rnDeriv_htrans (hY : Measurable Y) (π : Measure β) :
    (htrans R Y π).rnDeriv R =ᵐ[R] fun ω => π.rnDeriv (R.map Y) (Y ω) :=
  Measure.rnDeriv_withDensity R ((Measure.measurable_rnDeriv π (R.map Y)).comp hY)

lemma llr_htrans (hY : Measurable Y) {π : Measure β} [IsProbabilityMeasure π] (hπ : π ≪ R.map Y) :
    llr (htrans R Y π) R =ᵐ[htrans R Y π] fun ω => llr π (R.map Y) (Y ω) := by
  have := isProbabilityMeasure_htrans hY hπ
  filter_upwards [htrans_ac (R := R) (Y := Y) π (rnDeriv_htrans hY π)] with ω hω
  simp only [llr_def, hω]

/-- `KL(htrans R Y π ‖ R) = KL(π ‖ R ∘ Y⁻¹)`. -/
theorem klDiv_htrans (hY : Measurable Y) {π : Measure β} [IsProbabilityMeasure π] (hπ : π ≪ R.map Y) :
    klDiv (htrans R Y π) R = klDiv π (R.map Y) := by
  have hP := isProbabilityMeasure_htrans hY hπ
  have hmap := htrans_map hY hπ
  have hllr := llr_htrans hY hπ
  have hm : Measurable (llr π (R.map Y)) := measurable_llr _ _
  have hint : Integrable (llr (htrans R Y π) R) (htrans R Y π) ↔ Integrable (llr π (R.map Y)) π := by
    have h := integrable_map_measure (μ := htrans R Y π) hm.aestronglyMeasurable hY.aemeasurable
    rw [hmap] at h
    rw [integrable_congr hllr]
    exact h.symm
  by_cases hi : Integrable (llr π (R.map Y)) π
  · rw [klDiv_of_ac_of_integrable (htrans_ac π) (hint.2 hi), klDiv_of_ac_of_integrable hπ hi,
      integral_congr_ae hllr]
    congr 1
    rw [← integral_map hY.aemeasurable hm.aestronglyMeasurable, hmap]
    simp [measureReal_def]
  · rw [klDiv_of_not_integrable (mt hint.1 hi), klDiv_of_not_integrable hi]

/-- Equality in the data-processing inequality forces the `h`-transform form. -/
theorem eq_htrans_of_klDiv_le (hY : Measurable Y) {P : Measure Ω} [IsProbabilityMeasure P]
    (hfin : klDiv P R ≠ ∞) (hle : klDiv P R ≤ klDiv (P.map Y) (R.map Y)) :
    P = htrans R Y (P.map Y) := by
  obtain ⟨hPR, hint⟩ := klDiv_ne_top_iff.1 hfin
  set π := P.map Y with hπdef
  set g := π.rnDeriv (R.map Y)
  set P' := htrans R Y π
  have hπR : π ≪ R.map Y := hPR.map hY
  have hP' : IsProbabilityMeasure P' := isProbabilityMeasure_htrans hY hπR
  have hπint : Integrable (llr π (R.map Y)) π := integrable_llr_map hPR hY hint
  -- `g ∘ Y` is positive and finite `P`-a.e.
  have hgpos : ∀ᵐ ω ∂P, 0 < g (Y ω) := ae_of_ae_map hY.aemeasurable (Measure.rnDeriv_pos hπR)
  have hgfin : ∀ᵐ ω ∂P, g (Y ω) ≠ ∞ :=
    ae_of_ae_map hY.aemeasurable (hπR.ae_le (Measure.rnDeriv_ne_top π (R.map Y)))
  -- `P ≪ P'`
  have hPP' : P ≪ P' := by
    refine Measure.AbsolutelyContinuous.mk fun A hA h0 => ?_
    rw [show P' = R.withDensity (fun ω => g (Y ω)) from rfl, withDensity_apply _ hA] at h0
    have h0' := (lintegral_eq_zero_iff (f := fun ω => g (Y ω)) (μ := R.restrict A)
      ((Measure.measurable_rnDeriv _ _).comp hY)).1 h0
    have h1 : ∀ᵐ ω ∂R, ω ∈ A → g (Y ω) = 0 := (ae_restrict_iff' hA).1 h0'
    have h2 : ∀ᵐ ω ∂P, ω ∉ A := by
      filter_upwards [hPR.ae_le h1, hgpos] with ω h1 h2 hωA
      exact (h2.ne' (h1 hωA)).elim
    exact measure_eq_zero_iff_ae_notMem.2 h2
  -- the chain rule for the densities, `P`-a.e.
  have hmul : ∀ᵐ ω ∂P, P.rnDeriv P' ω * g (Y ω) = P.rnDeriv R ω := by
    filter_upwards [hPR.ae_le (Measure.rnDeriv_mul_rnDeriv (κ := R) hPP'),
      hPR.ae_le (rnDeriv_htrans (R := R) hY π)] with ω h1 h2
    rw [← h1, Pi.mul_apply, h2]
  have hllr : llr P P' =ᵐ[P] fun ω => llr P R ω - llr π (R.map Y) (Y ω) := by
    filter_upwards [hmul, hgpos, hgfin, Measure.rnDeriv_pos hPP', hPP'.ae_le (Measure.rnDeriv_ne_top P P')]
      with ω h1 h2 h3 h4 h5
    simp only [llr_def]
    rw [← h1, ENNReal.toReal_mul, Real.log_mul (ENNReal.toReal_pos h4.ne' h5).ne'
      (ENNReal.toReal_pos h2.ne' h3).ne']
    ring
  have hcomp : Integrable (fun ω => llr π (R.map Y) (Y ω)) P :=
    (integrable_map_measure (measurable_llr _ _).aestronglyMeasurable hY.aemeasurable).1 hπint
  have hint' : Integrable (llr P P') P := (integrable_congr hllr).2 (hint.sub hcomp)
  have hI : ∫ ω, llr π (R.map Y) (Y ω) ∂P = ∫ y, llr π (R.map Y) y ∂π :=
    (integral_map hY.aemeasurable (measurable_llr _ _).aestronglyMeasurable).symm
  have hval : klDiv P P' = ENNReal.ofReal (∫ ω, llr P R ω ∂P - ∫ y, llr π (R.map Y) y ∂π) := by
    rw [klDiv_of_ac_of_integrable hPP' hint', integral_congr_ae hllr, integral_sub hint hcomp, hI]
    simp [measureReal_def]
  have hA : klDiv P R = ENNReal.ofReal (∫ ω, llr P R ω ∂P) := by
    rw [klDiv_of_ac_of_integrable hPR hint]; simp [measureReal_def]
  have hB : klDiv π (R.map Y) = ENNReal.ofReal (∫ y, llr π (R.map Y) y ∂π) := by
    rw [klDiv_of_ac_of_integrable hπR hπint]; simp [measureReal_def]
  have hBnn : 0 ≤ ∫ y, llr π (R.map Y) y ∂π := by
    have := integral_llr_add_sub_measure_univ_nonneg hπR hπint
    simpa [measureReal_def] using this
  rw [hA, hB, ENNReal.ofReal_le_ofReal_iff hBnn] at hle
  have h0 : klDiv P P' = 0 := by
    rw [hval]; exact ENNReal.ofReal_eq_zero.2 (by linarith)
  exact klDiv_eq_zero_iff.1 h0

end StatFormal.SchrodingerPath
