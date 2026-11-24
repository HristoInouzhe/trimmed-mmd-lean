import StatFormal.Lib.SemiDiscrete.Dual
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.Data.EReal.Operations

/-!
# Semi-discrete entropic OT: the optimal plan and strong duality (component F.C′, part 2)

Setting as in `StatFormal.Foundations.SemiDiscrete.Dual`. For `f ∈ ℝ^k` put
`φ_f(i, y) = (f_i + g_f(y) − c_i(y))/ε` (`phiPot`) and `γ_f = (μ ⊗ Q).tilted φ_f` (`gammaStar`),
i.e. `dγ_f/d(μ⊗Q) = e^{φ_f}` since `∫ e^{φ_f} d(μ⊗Q) = 1` by definition of `g_f`.

Main results:
* `gammaStar_isProb`, `gammaStar_map_snd`: `γ_f` is a probability measure with second marginal `Q`
  (for every `f`);
* `gammaStar_map_fst`: if `f` satisfies the first-order condition (`foc_Jdual`), the first marginal
  of `γ_f` is `muDisc a`;
* `gammaStar_objective`: then `∫ c dγ_f + ε KL(γ_f ‖ μ⊗Q) = J_Q(f)` in `EReal`
  (`log dγ_f/d(μ⊗Q) = φ_f`);
* `strong_duality`: there is a maximiser `f*` of `J_Q` and a coupling `γ*` of `(μ, Q)` with
  `∫ c dγ* + ε KL(γ*‖μ⊗Q) = J_Q(f*) = max_f J_Q(f)`;
* `Theta` (the entropic OT value, an `sInf` over couplings in `EReal`) and `theta_eq_Jdual`:
  together with weak duality (`Claims.semidual_weak`, taken as a hypothesis), `Θ(Q) = J_Q(f*)`
  and the infimum is attained.
-/

noncomputable section
open Finset MeasureTheory
open scoped ENNReal
open StatFormal.RobustEquality.Semidual

namespace StatFormal.Foundations.SemiDiscrete

/-- The log-density `φ_f(i, y) = (f_i + g_f(y) − c_i(y))/ε` of the optimal plan. -/
def phiPot {K : Type*} {k : ℕ} (ε : ℝ) (a f : Fin k → ℝ) (c : Fin k → K → ℝ) :
    Fin k × K → ℝ :=
  fun z => (f z.1 + gsoft ε a f c z.2 - c z.1 z.2) / ε

/-- The candidate plan `γ_f = e^{φ_f} · (μ ⊗ Q)` (as a tilted measure). -/
def gammaStar {K : Type*} [MeasurableSpace K] {k : ℕ} (ε : ℝ) (a : Fin k → ℝ)
    (c : Fin k → K → ℝ) (Q : Measure K) (f : Fin k → ℝ) : Measure (Fin k × K) :=
  ((muDisc a).prod Q).tilted (phiPot ε a f c)

/-- The entropic OT value `Θ(Q) = inf_{γ ∈ Π(μ,Q)} {∫ c dγ + ε KL(γ‖μ⊗Q)}` (in `EReal`). -/
def Theta {K : Type*} [MeasurableSpace K] {k : ℕ} (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (Q : Measure K) : EReal :=
  sInf {v | ∃ γ : Measure (Fin k × K), IsProbabilityMeasure γ ∧ γ.map Prod.fst = muDisc a ∧
    γ.map Prod.snd = Q ∧
    v = ((∫ z, c z.1 z.2 ∂γ : ℝ) : EReal) +
      (ε : EReal) * StatFormal.RobustEquality.klRef γ ((muDisc a).prod Q)}

section muDisc

variable {k : ℕ}

lemma isProb_muDisc {a : Fin k → ℝ} (ha : ∀ i, 0 < a i) (hsum : ∑ i, a i = 1) :
    IsProbabilityMeasure (muDisc a) := by
  constructor
  simp only [muDisc, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (ha i).le), hsum, ENNReal.ofReal_one]

lemma integral_muDisc' {a : Fin k → ℝ} (ha : ∀ i, 0 < a i) (φ : Fin k → ℝ) :
    ∫ i, φ i ∂(muDisc a) = ∑ i, a i * φ i := by
  unfold muDisc
  rw [integral_finsetSum_measure
    (fun i _ => Integrable.of_finite.smul_measure ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (ha i).le, smul_eq_mul]

lemma lintegral_muDisc (a : Fin k → ℝ) (F : Fin k → ℝ≥0∞) :
    ∫⁻ i, F i ∂(muDisc a) = ∑ i, ENNReal.ofReal (a i) * F i := by
  unfold muDisc
  rw [lintegral_finsetSum_measure]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

lemma muDisc_singleton (a : Fin k → ℝ) (i : Fin k) :
    muDisc a {i} = ENNReal.ofReal (a i) := by
  simp only [muDisc, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply, Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end muDisc

section Plan

variable {K : Type*} [MeasurableSpace K] {k : ℕ} {ε B : ℝ} {a : Fin k → ℝ} {c : Fin k → K → ℝ}
  {Q : Measure K}

lemma SDHyp.measurable_cost (h : SDHyp ε a c B) : Measurable (fun z : Fin k × K => c z.1 z.2) :=
  measurable_from_prod_countable_right fun i => h.hc i

lemma SDHyp.measurable_phiPot (h : SDHyp ε a c B) (f : Fin k → ℝ) :
    Measurable (phiPot ε a f c) := by
  refine measurable_from_prod_countable_right fun i => ?_
  have hg := h.measurable_gsoft f
  have hci := h.hc i
  change Measurable fun y => (f i + gsoft ε a f c y - c i y) / ε
  fun_prop

lemma SDHyp.abs_phiPot_le (h : SDHyp ε a c B) (f : Fin k → ℝ) (z : Fin k × K) :
    |phiPot ε a f c z| ≤ (‖f‖ + (‖f‖ + B) + B) / ε := by
  unfold phiPot
  rw [abs_div, abs_of_pos h.hε]
  refine div_le_div_of_nonneg_right ?_ h.hε.le
  calc |f z.1 + gsoft ε a f c z.2 - c z.1 z.2|
      ≤ |f z.1| + |gsoft ε a f c z.2| + |c z.1 z.2| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ _ := by
        gcongr
        exacts [abs_apply_le_norm f _, h.abs_gsoft_le f _, h.hB _ _]

/-- For each `y`, `Σ_i a_i e^{φ_f(i,y)} = 1` (definition of `g_f`). -/
lemma SDHyp.sum_exp_phiPot (h : SDHyp ε a c B) (f : Fin k → ℝ) (y : K) :
    ∑ i, a i * Real.exp (phiPot ε a f c (i, y)) = 1 := by
  have hS := sum_exp_pos h.hk h.ha (fun j => (f j - c j y) / ε)
  have hexp : ∀ i, Real.exp (phiPot ε a f c (i, y)) =
      Real.exp ((f i - c i y) / ε) / ∑ j, a j * Real.exp ((f j - c j y) / ε) := by
    intro i
    have : phiPot ε a f c (i, y) =
        (f i - c i y) / ε - Real.log (∑ j, a j * Real.exp ((f j - c j y) / ε)) := by
      simp only [phiPot, gsoft]
      field_simp [h.hε.ne']
      ring
    rw [this, Real.exp_sub, Real.exp_log hS]
  simp_rw [hexp, ← mul_div_assoc]
  rw [← Finset.sum_div, div_self hS.ne']

lemma SDHyp.integrable_exp_phiPot (h : SDHyp ε a c B) (f : Fin k → ℝ) (μ : Measure (Fin k × K))
    [IsFiniteMeasure μ] : Integrable (fun z => Real.exp (phiPot ε a f c z)) μ :=
  integrable_exp_of_le (h.measurable_phiPot f) _ fun z =>
    (le_abs_self _).trans (h.abs_phiPot_le f z)

lemma SDHyp.integral_exp_phiPot (h : SDHyp ε a c B) [IsProbabilityMeasure Q] (f : Fin k → ℝ) :
    ∫ z, Real.exp (phiPot ε a f c z) ∂((muDisc a).prod Q) = 1 := by
  have := isProb_muDisc h.ha h.hsum
  rw [integral_prod_symm _ (h.integrable_exp_phiPot f _)]
  simp_rw [integral_muDisc' h.ha, h.sum_exp_phiPot f]
  simp

lemma SDHyp.gammaStar_apply (h : SDHyp ε a c B) [IsProbabilityMeasure Q] (f : Fin k → ℝ)
    {s : Set (Fin k × K)} (hs : MeasurableSet s) :
    gammaStar ε a c Q f s =
      ∫⁻ y, ∑ i, ENNReal.ofReal (a i) *
        s.indicator (fun z => ENNReal.ofReal (Real.exp (phiPot ε a f c z))) (i, y) ∂Q := by
  have := isProb_muDisc h.ha h.hsum
  rw [gammaStar, tilted_apply' _ _ hs, h.integral_exp_phiPot f]
  simp_rw [div_one]
  rw [← lintegral_indicator hs, lintegral_prod_symm']
  · simp_rw [lintegral_muDisc]
  · exact (ENNReal.measurable_ofReal.comp (h.measurable_phiPot f).exp).indicator hs

theorem SDHyp.gammaStar_isProb (h : SDHyp ε a c B) [IsProbabilityMeasure Q] (f : Fin k → ℝ) :
    IsProbabilityMeasure (gammaStar ε a c Q f) := by
  have := isProb_muDisc h.ha h.hsum
  exact isProbabilityMeasure_tilted (h.integrable_exp_phiPot f _)

/-- The second marginal of `γ_f` is `Q`, for every `f`. -/
theorem SDHyp.gammaStar_map_snd (h : SDHyp ε a c B) [IsProbabilityMeasure Q] (f : Fin k → ℝ) :
    (gammaStar ε a c Q f).map Prod.snd = Q := by
  ext A hA
  rw [Measure.map_apply measurable_snd hA, h.gammaStar_apply f (measurable_snd hA),
    ← lintegral_indicator_one hA]
  refine lintegral_congr fun y => ?_
  by_cases hy : y ∈ A
  · simp only [Set.indicator_of_mem (show (_, y) ∈ Prod.snd ⁻¹' A from hy),
      Set.indicator_of_mem hy, Pi.one_apply]
    rw [Finset.sum_congr rfl fun i _ => (ENNReal.ofReal_mul (h.ha i).le).symm,
      ← ENNReal.ofReal_sum_of_nonneg (fun i _ => (mul_pos (h.ha i) (Real.exp_pos _)).le),
      h.sum_exp_phiPot f y, ENNReal.ofReal_one]
  · simp [hy]

/-- Under the first-order condition, the first marginal of `γ_f` is `μ = muDisc a`. -/
theorem SDHyp.gammaStar_map_fst (h : SDHyp ε a c B) [IsProbabilityMeasure Q] {f : Fin k → ℝ}
    (hfoc : ∀ i, ∫ y, Real.exp ((f i + gsoft ε a f c y - c i y) / ε) ∂Q = 1) :
    (gammaStar ε a c Q f).map Prod.fst = muDisc a := by
  rw [Measure.ext_iff_singleton]
  intro i
  rw [Measure.map_apply measurable_fst (measurableSet_singleton i),
    h.gammaStar_apply f (measurable_fst (measurableSet_singleton i)), muDisc_singleton]
  have hpt : ∀ y, (∑ j, ENNReal.ofReal (a j) *
      (Prod.fst ⁻¹' {i}).indicator (fun z => ENNReal.ofReal (Real.exp (phiPot ε a f c z))) (j, y))
      = ENNReal.ofReal (a i) * ENNReal.ofReal (Real.exp (phiPot ε a f c (i, y))) := by
    intro y
    rw [Finset.sum_eq_single i]
    · rw [Set.indicator_of_mem (show (i, y) ∈ Prod.fst ⁻¹' {i} from rfl)]
    · intro j _ hj
      rw [Set.indicator_of_notMem (show (j, y) ∉ Prod.fst ⁻¹' {i} from hj), mul_zero]
    · simp
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← ofReal_integral_eq_lintegral_ofReal]
  · simp only [phiPot] at hfoc ⊢
    rw [hfoc i, ENNReal.ofReal_one, mul_one]
  · exact integrable_exp_of_le ((h.measurable_phiPot f).comp measurable_prodMk_left)
      _ fun y => (le_abs_self _).trans (h.abs_phiPot_le f (i, y))
  · exact Filter.Eventually.of_forall fun y => (Real.exp_pos _).le

/-- Primal value of `γ_f` at a critical point: `∫ c dγ_f + ε KL(γ_f ‖ μ⊗Q) = J_Q(f)`. -/
theorem SDHyp.gammaStar_objective (h : SDHyp ε a c B) [IsProbabilityMeasure Q] {f : Fin k → ℝ}
    (hfoc : ∀ i, ∫ y, Real.exp ((f i + gsoft ε a f c y - c i y) / ε) ∂Q = 1) :
    ((∫ z, c z.1 z.2 ∂(gammaStar ε a c Q f) : ℝ) : EReal) +
        (ε : EReal) * StatFormal.RobustEquality.klRef (gammaStar ε a c Q f) ((muDisc a).prod Q) =
      (Jdual ε a c Q f : EReal) := by
  have := isProb_muDisc h.ha h.hsum
  set ν := (muDisc a).prod Q
  set γ := gammaStar ε a c Q f
  have hγ : IsProbabilityMeasure γ := h.gammaStar_isProb f
  have hexp := h.integrable_exp_phiPot f ν
  have hac : γ ≪ ν := tilted_absolutelyContinuous ν _
  have hll : llr γ ν =ᵐ[γ]
      fun z => phiPot ε a f c z - Real.log (∫ z, Real.exp (phiPot ε a f c z) ∂ν) :=
    hac.ae_le (log_rnDeriv_tilted_left_self hexp)
  rw [h.integral_exp_phiPot f, Real.log_one] at hll
  simp_rw [sub_zero] at hll
  have hφint : Integrable (phiPot ε a f c) γ :=
    integrable_of_abs_le (h.measurable_phiPot f) _ (h.abs_phiPot_le f)
  have hint : Integrable (llr γ ν) γ := (integrable_congr hll).mpr hφint
  have hval : ∫ z, llr γ ν z ∂γ = ∫ z, phiPot ε a f c z ∂γ := integral_congr_ae hll
  -- marginal integrals
  have hfst := h.gammaStar_map_fst hfoc
  have hsnd := h.gammaStar_map_snd (Q := Q) f
  have i1 : Integrable (fun z : Fin k × K => f z.1) γ :=
    integrable_of_abs_le (Measurable.of_discrete.comp measurable_fst) _
      fun z => abs_apply_le_norm f z.1
  have i2 : Integrable (fun z : Fin k × K => gsoft ε a f c z.2) γ :=
    integrable_of_abs_le ((h.measurable_gsoft f).comp measurable_snd) _
      fun z => h.abs_gsoft_le f z.2
  have i3 : Integrable (fun z : Fin k × K => c z.1 z.2) γ :=
    integrable_of_abs_le h.measurable_cost B fun z => h.hB _ _
  have e1 : ∫ z, f z.1 ∂γ = ∑ i, a i * f i := by
    rw [← integral_map measurable_fst.aemeasurable Measurable.of_discrete.aestronglyMeasurable,
      hfst, integral_muDisc' h.ha]
  have e2 : ∫ z, gsoft ε a f c z.2 ∂γ = ∫ y, gsoft ε a f c y ∂Q := by
    rw [← integral_map measurable_snd.aemeasurable (h.measurable_gsoft f).aestronglyMeasurable,
      hsnd]
  have hφ : ∫ z, phiPot ε a f c z ∂γ =
      ((∑ i, a i * f i) + (∫ y, gsoft ε a f c y ∂Q) - ∫ z, c z.1 z.2 ∂γ) / ε := by
    have i12 : Integrable (fun z : Fin k × K => f z.1 + gsoft ε a f c z.2) γ := i1.add i2
    simp only [phiPot]
    rw [integral_div, integral_sub i12 i3, integral_add i1 i2, e1, e2]
  unfold StatFormal.RobustEquality.klRef
  rw [ite_eq_left ⟨hac, hint⟩, hval, hφ, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_eq_coe_iff]
  unfold Jdual
  field_simp [h.hε.ne']
  ring

/-- **Strong duality** (semi-discrete, `lem:semidual` (i)): `J_Q` has a maximiser `f*`, and the plan
`γ* = e^{φ_{f*}}(μ⊗Q)` is a coupling of `(μ, Q)` whose primal value equals `J_Q(f*) = max_f J_Q`. -/
theorem strong_duality (h : SDHyp ε a c B) (Q : Measure K) [IsProbabilityMeasure Q] :
    ∃ fs : Fin k → ℝ, (∀ f, Jdual ε a c Q f ≤ Jdual ε a c Q fs) ∧
      ∃ γ : Measure (Fin k × K), IsProbabilityMeasure γ ∧ γ.map Prod.fst = muDisc a ∧
        γ.map Prod.snd = Q ∧
        ((∫ z, c z.1 z.2 ∂γ : ℝ) : EReal) +
            (ε : EReal) * StatFormal.RobustEquality.klRef γ ((muDisc a).prod Q) =
          (Jdual ε a c Q fs : EReal) := by
  obtain ⟨fs, hmax⟩ := exists_max_Jdual h Q
  have hfoc := foc_Jdual h hmax
  exact ⟨fs, hmax, gammaStar ε a c Q fs, h.gammaStar_isProb fs, h.gammaStar_map_fst hfoc,
    h.gammaStar_map_snd fs, h.gammaStar_objective hfoc⟩

/-- The supremum of `J_Q` over `ℝ^k` (in `EReal`) is attained at any maximiser. -/
theorem iSup_Jdual_eq {fs : Fin k → ℝ} (hmax : ∀ f, Jdual ε a c Q f ≤ Jdual ε a c Q fs) :
    (⨆ f, (Jdual ε a c Q f : EReal)) = (Jdual ε a c Q fs : EReal) :=
  le_antisymm (iSup_le fun f => EReal.coe_le_coe_iff.mpr (hmax f))
    (le_iSup (fun f => (Jdual ε a c Q f : EReal)) fs)

end Plan

section Theta

variable {K : Type} [MeasurableSpace K] {k : ℕ} {ε B : ℝ} {a : Fin k → ℝ} {c : Fin k → K → ℝ}

/-- **`Θ(Q) = max_f J_Q(f)`**, given weak duality (`Claims.semidual_weak`, proved elsewhere): the
coupling values have least element `J_Q(f*)` for any maximiser `f*` (attained by `γ*`). -/
theorem isLeast_Theta (hweak : Claims.semidual_weak) (h : SDHyp ε a c B) (Q : Measure K)
    [IsProbabilityMeasure Q] {fs : Fin k → ℝ} (hmax : ∀ f, Jdual ε a c Q f ≤ Jdual ε a c Q fs) :
    IsLeast {v | ∃ γ : Measure (Fin k × K), IsProbabilityMeasure γ ∧ γ.map Prod.fst = muDisc a ∧
      γ.map Prod.snd = Q ∧
      v = ((∫ z, c z.1 z.2 ∂γ : ℝ) : EReal) +
        (ε : EReal) * StatFormal.RobustEquality.klRef γ ((muDisc a).prod Q)}
      (Jdual ε a c Q fs : EReal) := by
  have hfoc := foc_Jdual h hmax
  refine ⟨⟨gammaStar ε a c Q fs, h.gammaStar_isProb fs, h.gammaStar_map_fst hfoc,
    h.gammaStar_map_snd fs, (h.gammaStar_objective hfoc).symm⟩, ?_⟩
  rintro v ⟨γ, hγ, hfst, hsnd, rfl⟩
  exact hweak K k a fs c Q γ ε h.hε h.ha h.hsum h.hc ⟨B, h.hB⟩ hfst hsnd

theorem Theta_eq_Jdual (hweak : Claims.semidual_weak) (h : SDHyp ε a c B) (Q : Measure K)
    [IsProbabilityMeasure Q] {fs : Fin k → ℝ} (hmax : ∀ f, Jdual ε a c Q f ≤ Jdual ε a c Q fs) :
    Theta ε a c Q = (Jdual ε a c Q fs : EReal) :=
  (isLeast_Theta hweak h Q hmax).isGLB.sInf_eq

/-- `Θ(Q) = sup_f J_Q(f)`, the supremum being attained. -/
theorem Theta_eq_iSup (hweak : Claims.semidual_weak) (h : SDHyp ε a c B) (Q : Measure K)
    [IsProbabilityMeasure Q] :
    Theta ε a c Q = ⨆ f, (Jdual ε a c Q f : EReal) := by
  obtain ⟨fs, hmax⟩ := exists_max_Jdual h Q
  rw [Theta_eq_Jdual hweak h Q hmax, iSup_Jdual_eq hmax]

end Theta

end StatFormal.Foundations.SemiDiscrete
