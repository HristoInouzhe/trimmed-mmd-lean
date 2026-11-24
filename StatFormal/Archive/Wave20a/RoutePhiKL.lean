import StatFormal.Archive.Wave20a.Statements
import StatFormal.Archive.Wave20a.RoutePhi
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Route — ICL `lem:phi` (iii), (iv) (untrusted)

* (iii) `K⋆ν = ρ_ν λ` is a probability measure (Tonelli); `P₀ = (K⋆ν).withDensity (p₀/ρ_ν)` (`withDensity_mul`),
  so `llr(P₀, K⋆ν) = log p₀ − log ρ_ν` `P₀`-a.e. (`p₀ > 0` `P₀`-a.e.), integrable; integrate and use
  `∫ g dP₀ = ∫ p₀ g dλ`.
* (iv) `ν ↦ ρ_ν(z)` is weakly continuous (`K(z,·)` bounded continuous on compact `𝒵`); `𝒫(𝒵)` is metrizable
  (Lévy–Prokhorov), so sequential continuity suffices and dominated convergence applies (`log ρ` bounded); `𝒫(𝒵)`
  is compact (Prokhorov), so a continuous `Φ` attains its minimum.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology InformationTheory
open scoped ENNReal

namespace StatFormal.Wave20a

theorem phi_kl : Claims.phi_kl := by
  intro Z _ Kk Kmin Kmax P₀ ν lam _ _ _ p₀ hK hdens hp₀m hp₀ hP₀ hent
  set ρ := rhoC Kk ν
  have hρ := rho_bounds hK ν
  have hρpos : ∀ z, 0 < ρ z := rho_pos hK ν
  have hρm : Measurable ρ := rho_meas hK ν
  set Q := lam.withDensity (fun z => ENNReal.ofReal (ρ z))
  -- `Q` is a probability measure
  have hKint : ∀ z', Integrable (fun z => Kk z z') lam := fun z' => by
    by_contra h
    have := integral_undef h
    rw [hdens z'] at this; exact one_ne_zero this
  have hQuniv : Q univ = 1 := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    have e1 : ∀ z, ENNReal.ofReal (ρ z) = ∫⁻ z', ENNReal.ofReal (Kk z z') ∂ν := fun z => by
      show ENNReal.ofReal (∫ z', Kk z z' ∂ν) = _
      rw [ofReal_integral_eq_lintegral_ofReal (kb_int hK ν z)
        (Eventually.of_forall fun z' => hK.1.le.trans (hK.2.2 z z').1)]
    simp_rw [e1]
    rw [lintegral_lintegral_swap (f := fun z z' => ENNReal.ofReal (Kk z z'))
      (ENNReal.measurable_ofReal.comp hK.2.1).aemeasurable]
    have e2 : ∀ z', ∫⁻ z, ENNReal.ofReal (Kk z z') ∂lam = 1 := fun z' => by
      rw [← ofReal_integral_eq_lintegral_ofReal (hKint z')
        (Eventually.of_forall fun z => hK.1.le.trans (hK.2.2 z z').1), hdens z', ENNReal.ofReal_one]
    simp_rw [e2]; simp
  have hQ : IsProbabilityMeasure Q := ⟨hQuniv⟩
  -- densities
  have hgm : Measurable fun z => ENNReal.ofReal (p₀ z / ρ z) := (hp₀m.div hρm).ennreal_ofReal
  have hP₀Q : P₀ = Q.withDensity (fun z => ENNReal.ofReal (p₀ z / ρ z)) := by
    rw [hP₀, ← withDensity_mul _ hρm.ennreal_ofReal hgm]
    congr 1; funext z
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (hρpos z).le, mul_div_cancel₀ _ (hρpos z).ne']
  have hac : P₀ ≪ Q := by rw [hP₀Q]; exact withDensity_absolutelyContinuous _ _
  have hrn : P₀.rnDeriv Q =ᵐ[Q] fun z => ENNReal.ofReal (p₀ z / ρ z) := by
    rw [hP₀Q]; exact Measure.rnDeriv_withDensity Q hgm
  -- `p₀ > 0` `P₀`-a.e.
  have hp₀pos : ∀ᵐ z ∂P₀, 0 < p₀ z := by
    rw [hP₀, ae_withDensity_iff hp₀m.ennreal_ofReal]
    refine Eventually.of_forall fun z hz => lt_of_le_of_ne (hp₀ z) fun h => hz ?_
    rw [← h, ENNReal.ofReal_zero]
  have hllr : llr P₀ Q =ᵐ[P₀] fun z => Real.log (p₀ z) - Real.log (ρ z) := by
    filter_upwards [hac.ae_le hrn, hp₀pos] with z hz hpz
    rw [llr, hz, ENNReal.toReal_ofReal (div_nonneg (hp₀ z) (hρpos z).le),
      Real.log_div hpz.ne' (hρpos z).ne']
  -- integrability
  have hfin : ∀ᵐ z ∂lam, ENNReal.ofReal (p₀ z) < ∞ := Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hlogp : Integrable (fun z => Real.log (p₀ z)) P₀ := by
    rw [hP₀, integrable_withDensity_iff_integrable_smul' hp₀m.ennreal_ofReal hfin]
    simpa [ENNReal.toReal_ofReal (hp₀ _), smul_eq_mul] using hent
  have hlogρ : Integrable (fun z => Real.log (ρ z)) P₀ := logrho_int hK ν P₀
  have hint : Integrable (llr P₀ Q) P₀ := (hlogp.sub hlogρ).congr hllr.symm
  refine ⟨klDiv_ne_top hac hint, ?_⟩
  rw [toReal_klDiv hac hint, integral_congr_ae hllr, integral_sub hlogp hlogρ]
  have hQr : Q.real univ = 1 := by simp [Measure.real, hQuniv]
  have hPr : P₀.real univ = 1 := by simp [Measure.real]
  rw [hQr, hPr]
  have hH : ∫ z, Real.log (p₀ z) ∂P₀ = ∫ z, p₀ z * Real.log (p₀ z) ∂lam := by
    rw [hP₀, integral_withDensity_eq_integral_toReal_smul hp₀m.ennreal_ofReal hfin]
    simp [ENNReal.toReal_ofReal (hp₀ _), smul_eq_mul]
  rw [hH, PhiC]
  ring

theorem phi_continuous : Claims.phi_continuous := by
  intro Z _ _ _ _ Kk Kmin Kmax P₀ _ hK hKc
  have hKz : ∀ z, Continuous (Kk z) := fun z => hKc.comp (continuous_const.prodMk continuous_id)
  -- pointwise continuity of the coverage
  have hρc : ∀ z, Continuous fun ν : ProbabilityMeasure Z => rhoC Kk (ν : Measure Z) z := by
    intro z
    rw [continuous_iff_continuousAt]
    intro ν
    have := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto (μs := id) (F := 𝓝 ν) (μ := ν)).1
      tendsto_id (BoundedContinuousFunction.mkOfCompact ⟨Kk z, hKz z⟩)
    simpa [rhoC, ContinuousAt] using this
  have hcont : Continuous fun ν : ProbabilityMeasure Z => PhiC Kk P₀ (ν : Measure Z) := by
    rw [continuous_iff_seqContinuous]
    intro νs ν hν
    unfold PhiC
    refine Tendsto.neg ?_
    refine tendsto_integral_of_dominated_convergence (fun _ => max |Real.log Kmin| |Real.log Kmax|)
      (fun n => (logrho_int hK (νs n : Measure Z) P₀).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun z => ?_) (Eventually.of_forall fun z => ?_)
    · rw [Real.norm_eq_abs]
      have hb := rho_bounds hK (νs n : Measure Z) z
      exact abs_le_max_abs_abs (Real.log_le_log hK.1 hb.1) (Real.log_le_log (rho_pos hK _ z) hb.2)
    · exact ((Real.continuousAt_log (rho_pos hK (ν : Measure Z) z).ne').tendsto).comp
        (((hρc z).tendsto ν).comp hν)
  refine ⟨hcont, ?_⟩
  haveI : Nonempty (ProbabilityMeasure Z) := ⟨⟨P₀, inferInstance⟩⟩
  obtain ⟨νs, -, hmin⟩ := isCompact_univ.exists_isMinOn univ_nonempty hcont.continuousOn
  exact ⟨νs, fun ν => hmin (mem_univ ν)⟩

end StatFormal.Wave20a
