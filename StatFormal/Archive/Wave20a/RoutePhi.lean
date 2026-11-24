import StatFormal.Archive.Wave20a.Statements
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Route — ICL `lem:phi` (i), (ii) (untrusted)

* `ρ_ν` is linear in `ν` and takes values in `[K_min, K_max]`; `log ρ` is bounded measurable, hence integrable.
* (i) concavity of `log`; equal coverage: the midpoint has `∫ (log ρ_m − ½log ρ₁ − ½log ρ₂) dP₀ ≤ 0` with a
  nonnegative integrand, so the integrand vanishes a.e., and strict concavity forces `ρ₁ = ρ₂` there.
* (ii) on `[0,1]`, `Φ(ν_t) = −∫ log(ρ + t(κ − ρ)) dP₀`, `κ = K(·,z')`; differentiate under the integral on a ball
  where `ρ + t(κ − ρ) ≥ K_min/2`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.Wave20a

section PhiAux
variable {Z : Type*} [MeasurableSpace Z] {Kk : Z → Z → ℝ} {Kmin Kmax : ℝ}

lemma kb_meas_right (hK : KernelBounds Kk Kmin Kmax) (z : Z) : Measurable (Kk z) :=
  hK.2.1.comp (measurable_const.prodMk measurable_id)

lemma kb_meas_left (hK : KernelBounds Kk Kmin Kmax) (z' : Z) : Measurable fun z => Kk z z' :=
  hK.2.1.comp (measurable_id.prodMk measurable_const)

lemma kb_int (hK : KernelBounds Kk Kmin Kmax) (ν : Measure Z) [IsFiniteMeasure ν] (z : Z) :
    Integrable (Kk z) ν :=
  Integrable.of_bound (kb_meas_right hK z).aestronglyMeasurable (max |Kmin| |Kmax|)
    (Eventually.of_forall fun z' => by
      rw [Real.norm_eq_abs]
      exact abs_le_max_abs_abs (hK.2.2 z z').1 (hK.2.2 z z').2)

lemma rho_bounds (hK : KernelBounds Kk Kmin Kmax) (ν : Measure Z) [IsProbabilityMeasure ν] (z : Z) :
    Kmin ≤ rhoC Kk ν z ∧ rhoC Kk ν z ≤ Kmax := by
  constructor
  · have := integral_mono (integrable_const Kmin) (kb_int hK ν z) fun z' => (hK.2.2 z z').1
    simpa [rhoC] using this
  · have := integral_mono (kb_int hK ν z) (integrable_const Kmax) fun z' => (hK.2.2 z z').2
    simpa [rhoC] using this

lemma rho_pos (hK : KernelBounds Kk Kmin Kmax) (ν : Measure Z) [IsProbabilityMeasure ν] (z : Z) :
    0 < rhoC Kk ν z := hK.1.trans_le (rho_bounds hK ν z).1

lemma rho_meas (hK : KernelBounds Kk Kmin Kmax) (ν : Measure Z) [IsFiniteMeasure ν] :
    Measurable (rhoC Kk ν) := by
  have : StronglyMeasurable (Function.uncurry Kk) := hK.2.1.stronglyMeasurable
  exact (this.integral_prod_right' (ν := ν) |>.measurable)

lemma logrho_int (hK : KernelBounds Kk Kmin Kmax) (ν : Measure Z) [IsProbabilityMeasure ν]
    (P₀ : Measure Z) [IsFiniteMeasure P₀] : Integrable (fun z => Real.log (rhoC Kk ν z)) P₀ :=
  Integrable.of_bound (rho_meas hK ν).log.aestronglyMeasurable (max |Real.log Kmin| |Real.log Kmax|)
    (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]
      have hb := rho_bounds hK ν z
      exact abs_le_max_abs_abs (Real.log_le_log hK.1 hb.1) (Real.log_le_log (rho_pos hK ν z) hb.2))

/-- Mixtures: `ρ_{(1−t)ν₁ + tν₂} = (1−t)ρ₁ + tρ₂`. -/
lemma rho_mix (hK : KernelBounds Kk Kmin Kmax) (ν₁ ν₂ : Measure Z) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (z : Z) :
    rhoC Kk (ENNReal.ofReal (1 - t) • ν₁ + ENNReal.ofReal t • ν₂) z =
      (1 - t) * rhoC Kk ν₁ z + t * rhoC Kk ν₂ z := by
  unfold rhoC
  rw [integral_add_measure ((kb_int hK ν₁ z).smul_measure ENNReal.ofReal_ne_top)
    ((kb_int hK ν₂ z).smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal h0, smul_eq_mul, smul_eq_mul]

lemma mix_isProb (ν₁ ν₂ : Measure Z) [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] {t : ℝ}
    (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    IsProbabilityMeasure (ENNReal.ofReal (1 - t) • ν₁ + ENNReal.ofReal t • ν₂) := by
  constructor
  simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, measure_univ, smul_eq_mul,
    mul_one]
  rw [← ENNReal.ofReal_add (by linarith) h0]; simp

end PhiAux

theorem phi_convex : Claims.phi_convex := by
  intro Z _ Kk Kmin Kmax P₀ ν₁ ν₂ _ _ _ t hK h0 h1
  haveI := mix_isProb ν₁ ν₂ h0 h1
  unfold PhiC
  have hpt : ∀ z, (1 - t) * Real.log (rhoC Kk ν₁ z) + t * Real.log (rhoC Kk ν₂ z) ≤
      Real.log (rhoC Kk (ENNReal.ofReal (1 - t) • ν₁ + ENNReal.ofReal t • ν₂) z) := by
    intro z
    rw [rho_mix hK ν₁ ν₂ h0 h1]
    have := strictConcaveOn_log_Ioi.concaveOn.2 (mem_Ioi.2 (rho_pos hK ν₁ z)) (mem_Ioi.2 (rho_pos hK ν₂ z))
      (by linarith : 0 ≤ 1 - t) h0 (by ring)
    simpa [smul_eq_mul] using this
  have hI : Integrable (fun z => (1 - t) * Real.log (rhoC Kk ν₁ z) + t * Real.log (rhoC Kk ν₂ z)) P₀ :=
    ((logrho_int hK ν₁ P₀).const_mul (1 - t)).add ((logrho_int hK ν₂ P₀).const_mul t)
  have hi := integral_mono hI (logrho_int hK _ P₀) hpt
  have hs : ∫ z, ((1 - t) * Real.log (rhoC Kk ν₁ z) + t * Real.log (rhoC Kk ν₂ z)) ∂P₀ =
      (1 - t) * ∫ z, Real.log (rhoC Kk ν₁ z) ∂P₀ + t * ∫ z, Real.log (rhoC Kk ν₂ z) ∂P₀ := by
    rw [integral_add ((logrho_int hK ν₁ P₀).const_mul _) ((logrho_int hK ν₂ P₀).const_mul _),
      integral_const_mul, integral_const_mul]
  rw [hs] at hi
  linarith

theorem phi_same_coverage : Claims.phi_same_coverage := by
  intro Z _ Kk Kmin Kmax P₀ _ C ν₁ ν₂ hK hCp hCc h₁ h₂ hmin₁ hmin₂
  haveI := hCp ν₁ h₁
  haveI := hCp ν₂ h₂
  have h12 : PhiC Kk P₀ ν₁ = PhiC Kk P₀ ν₂ := le_antisymm (hmin₁ ν₂ h₂) (hmin₂ ν₁ h₁)
  set m := ENNReal.ofReal (1 - 1 / 2) • ν₁ + ENNReal.ofReal (1 / 2) • ν₂
  have hmC : m ∈ C := hCc ν₁ h₁ ν₂ h₂ (1 / 2) (by norm_num) (by norm_num)
  haveI hm : IsProbabilityMeasure m := hCp m hmC
  have hm1 := hmin₁ m hmC
  set g : Z → ℝ := fun z => Real.log (rhoC Kk m z) - (1 / 2 * Real.log (rhoC Kk ν₁ z) +
    1 / 2 * Real.log (rhoC Kk ν₂ z))
  have hconc : ∀ z, 1 / 2 * Real.log (rhoC Kk ν₁ z) + 1 / 2 * Real.log (rhoC Kk ν₂ z) ≤
      Real.log (rhoC Kk m z) := by
    intro z
    rw [rho_mix hK ν₁ ν₂ (by norm_num) (by norm_num)]
    have := strictConcaveOn_log_Ioi.concaveOn.2 (mem_Ioi.2 (rho_pos hK ν₁ z)) (mem_Ioi.2 (rho_pos hK ν₂ z))
      (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simp only [smul_eq_mul] at this
    norm_num at this ⊢
    exact this
  have hg0 : 0 ≤ᵐ[P₀] g := Eventually.of_forall fun z => sub_nonneg.2 (hconc z)
  have hI2 : Integrable (fun z => 1 / 2 * Real.log (rhoC Kk ν₁ z) + 1 / 2 * Real.log (rhoC Kk ν₂ z)) P₀ :=
    ((logrho_int hK ν₁ P₀).const_mul _).add ((logrho_int hK ν₂ P₀).const_mul _)
  have hgi : Integrable g P₀ := (logrho_int hK m P₀).sub hI2
  have hint : ∫ z, g z ∂P₀ = 0 := by
    apply le_antisymm _ (integral_nonneg_of_ae hg0)
    have e1 : ∫ z, g z ∂P₀ = ∫ z, Real.log (rhoC Kk m z) ∂P₀ -
        (1 / 2 * ∫ z, Real.log (rhoC Kk ν₁ z) ∂P₀ + 1 / 2 * ∫ z, Real.log (rhoC Kk ν₂ z) ∂P₀) := by
      simp only [g]
      rw [integral_sub (logrho_int hK m P₀) hI2, integral_add ((logrho_int hK ν₁ P₀).const_mul _)
        ((logrho_int hK ν₂ P₀).const_mul _), integral_const_mul, integral_const_mul]
    rw [e1]
    unfold PhiC at hm1 h12
    linarith
  have hg_ae := (integral_eq_zero_iff_of_nonneg_ae hg0 hgi).1 hint
  filter_upwards [hg_ae] with z hz
  by_contra hne
  have hlt := strictConcaveOn_log_Ioi.2 (mem_Ioi.2 (rho_pos hK ν₁ z)) (mem_Ioi.2 (rho_pos hK ν₂ z)) hne
    (by norm_num : (0 : ℝ) < 1 - 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have : g z = 0 := hz
  simp only [g] at this
  rw [rho_mix hK ν₁ ν₂ (by norm_num) (by norm_num)] at this
  simp only [smul_eq_mul] at hlt
  norm_num at hlt this
  linarith

theorem phi_first_variation : Claims.phi_first_variation := by
  intro Z _ Kk Kmin Kmax P₀ ν _ _ z' hK
  set ρ := rhoC Kk ν
  set κ : Z → ℝ := fun z => Kk z z'
  have hρ := rho_bounds hK ν
  have hκm : Measurable κ := kb_meas_left hK z'
  have hρm : Measurable ρ := rho_meas hK ν
  -- the formula on `[0,1]`
  set F : ℝ → ℝ := fun t => -∫ z, Real.log (ρ z + t * (κ z - ρ z)) ∂P₀
  have hEq : EqOn (fun t : ℝ => PhiC Kk P₀ (ENNReal.ofReal (1 - t) • ν + ENNReal.ofReal t • Measure.dirac z'))
      F (Icc 0 1) := by
    intro t ht
    simp only [PhiC, F]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only
    rw [rho_mix hK ν (Measure.dirac z') ht.1 ht.2]
    congr 1
    simp only [rhoC, ρ, κ]
    rw [integral_dirac' _ _ (kb_meas_right hK z).stronglyMeasurable]
    ring
  -- differentiate `F` at `0`
  set ε := Kmin / (2 * (|Kmax - Kmin| + 1))
  have hε : 0 < ε := div_pos hK.1 (by positivity)
  have hdiff_bd : ∀ z, |κ z - ρ z| ≤ |Kmax - Kmin| := fun z => by
    have h1 := hK.2.2 z z'; have h2 := hρ z
    exact (abs_sub_le_iff.2 ⟨by simp only [κ, ρ]; linarith [h1.2, h2.1],
      by simp only [κ, ρ]; linarith [h1.1, h2.2]⟩).trans (le_abs_self _)
  have hlow : ∀ z, ∀ t ∈ Metric.ball (0 : ℝ) ε, Kmin / 2 ≤ ρ z + t * (κ z - ρ z) := by
    intro z t ht
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
    have h1 : |t * (κ z - ρ z)| ≤ ε * |Kmax - Kmin| := by
      rw [abs_mul]; exact mul_le_mul ht.le (hdiff_bd z) (abs_nonneg _) hε.le
    have h2 : ε * |Kmax - Kmin| ≤ Kmin / 2 := by
      simp only [ε]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [abs_nonneg (Kmax - Kmin), hK.1]
    have := neg_abs_le (t * (κ z - ρ z))
    linarith [(hρ z).1]
  set F' : ℝ → Z → ℝ := fun t z => (κ z - ρ z) / (ρ z + t * (κ z - ρ z))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P₀)
    (F := fun t z => Real.log (ρ z + t * (κ z - ρ z))) (F' := F') (x₀ := 0)
    (bound := fun _ => |Kmax - Kmin| / (Kmin / 2)) (Metric.ball_mem_nhds 0 hε)
    (Eventually.of_forall fun t => (hρm.add (measurable_const.mul (hκm.sub hρm))).log.aestronglyMeasurable)
    (by simpa using logrho_int hK ν P₀)
    ((hκm.sub hρm).div (hρm.add (measurable_const.mul (hκm.sub hρm)))).aestronglyMeasurable
    (Eventually.of_forall fun z t ht => by
      simp only [F', Real.norm_eq_abs, abs_div]
      have hl := hlow z t ht
      rw [abs_of_pos (by linarith [hK.1] : 0 < ρ z + t * (κ z - ρ z))]
      exact div_le_div₀ (abs_nonneg _) (hdiff_bd z) (by linarith [hK.1]) hl)
    (integrable_const _)
    (Eventually.of_forall fun z t ht => by
      have hl := hlow z t ht
      have hpos : ρ z + t * (κ z - ρ z) ≠ 0 := by linarith [hK.1]
      have := ((hasDerivAt_id t).mul_const (κ z - ρ z)).const_add (ρ z)
      simp only [id, one_mul] at this
      have := this.log hpos
      simpa [F', div_eq_mul_inv, mul_comm] using this)
  have hF : HasDerivAt F (-∫ z, F' 0 z ∂P₀) 0 := key.2.neg
  have hval : -∫ z, F' 0 z ∂P₀ = 1 - ∫ z, Kk z z' / rhoC Kk ν z ∂P₀ := by
    have hi1 : Integrable (fun z => κ z / ρ z) P₀ :=
      Integrable.of_bound (hκm.div hρm).aestronglyMeasurable (max |Kmin| |Kmax| / Kmin)
        (Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs, abs_div, abs_of_pos (rho_pos hK ν z)]
          exact div_le_div₀ (by positivity) (abs_le_max_abs_abs (hK.2.2 z z').1 (hK.2.2 z z').2) hK.1 (hρ z).1)
    have : ∀ z, F' 0 z = κ z / ρ z - 1 := fun z => by
      simp only [F', zero_mul, add_zero]
      rw [sub_div, div_self (rho_pos hK ν z).ne']
    simp_rw [this]
    rw [integral_sub hi1 (integrable_const _)]
    simp [κ, ρ]
  rw [hval] at hF
  exact hF.hasDerivWithinAt.congr_of_mem hEq ⟨le_refl 0, zero_le_one⟩

end StatFormal.Wave20a
