import StatFormal.Archive.Wave23c.Statements
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Route — R `thm:elliptical`, part 1: `Φ`, `F₁` and the one-dimensional projections (untrusted)

* `Φ = cdf N(0,1)`: positive, `< 1`, strictly increasing (Lebesgue `≪ N(0,1)`), continuous (no atoms: the left limit
  of a Stieltjes function at `a` misses exactly the mass of `{a}`), symmetric (`N(0,1)` is invariant under `−`).
* `F₁(t) = E Φ(t/√W)`: dominated convergence (continuity, limits), strict positivity of integrals.
* `elliptical_proj`: `⟨v, G⟩ ∼ N(0, σ_v²)` (Gaussianity of `G`), independent of `W`; Fubini over the law of `W`.
* `elliptical_atomless`: the same computation for `{√W ⟨v,G⟩ = s}`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave23c

/-- The standard normal distribution function. -/
abbrev Φn (t : ℝ) : ℝ := cdf (gaussianReal 0 1) t

section Phi

lemma vol_ac_gauss : (volume : Measure ℝ) ≪ gaussianReal 0 1 :=
  gaussianReal_absolutelyContinuous' 0 one_ne_zero

lemma gauss_pos_of_vol {s : Set ℝ} (hs : volume s ≠ 0) : gaussianReal 0 1 s ≠ 0 :=
  fun h => hs (vol_ac_gauss h)

lemma gauss_singleton (a : ℝ) : gaussianReal 0 1 {a} = 0 := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  exact measure_singleton a

lemma Φn_pos (t : ℝ) : 0 < Φn t := by
  have h1 := ofReal_cdf (μ := gaussianReal 0 1) t
  have h2 : gaussianReal 0 1 (Iic t) ≠ 0 := gauss_pos_of_vol (by simp)
  rw [← h1] at h2
  exact ENNReal.ofReal_pos.1 (pos_iff_ne_zero.2 h2)

lemma Φn_add_Ioi (t : ℝ) : Φn t + (gaussianReal 0 1).real (Ioi t) = 1 := by
  rw [Φn, cdf_eq_real, ← measureReal_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi, Iic_union_Ioi,
    probReal_univ]

lemma Φn_lt_one (t : ℝ) : Φn t < 1 := by
  have h := Φn_add_Ioi t
  have h2 : gaussianReal 0 1 (Ioi t) ≠ 0 := gauss_pos_of_vol (by simp)
  have h3 : 0 < (gaussianReal 0 1).real (Ioi t) :=
    ENNReal.toReal_pos h2 (measure_ne_top _ _)
  linarith

lemma Φn_strictMono : StrictMono Φn := by
  intro s t hst
  have h1 : (gaussianReal 0 1).real (Iic t) = (gaussianReal 0 1).real (Iic s) +
      (gaussianReal 0 1).real (Ioc s t) := by
    rw [← measureReal_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc, Iic_union_Ioc_eq_Iic hst.le]
  have h2 : gaussianReal 0 1 (Ioc s t) ≠ 0 := gauss_pos_of_vol (by simp [hst])
  have h3 : 0 < (gaussianReal 0 1).real (Ioc s t) := ENNReal.toReal_pos h2 (measure_ne_top _ _)
  simp only [Φn, cdf_eq_real]
  linarith

lemma Φn_continuous : Continuous Φn := by
  rw [continuous_iff_continuousAt]
  intro a
  have hmono : Monotone (cdf (gaussianReal 0 1)) := (cdf (gaussianReal 0 1)).mono
  rw [hmono.continuousAt_iff_leftLim_eq_rightLim, (cdf (gaussianReal 0 1)).rightLim_eq]
  have h1 := (cdf (gaussianReal 0 1)).measure_singleton a
  rw [measure_cdf, gauss_singleton] at h1
  have h2 : cdf (gaussianReal 0 1) a - Function.leftLim (cdf (gaussianReal 0 1)) a ≤ 0 :=
    ENNReal.ofReal_eq_zero.1 h1.symm
  exact le_antisymm (hmono.leftLim_le le_rfl) (by linarith)

lemma Φn_neg (t : ℝ) : Φn (-t) = 1 - Φn t := by
  have hmap : (gaussianReal 0 1).map (fun x => -x) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg, neg_zero]
  have h1 : (gaussianReal 0 1).real (Iic (-t)) = (gaussianReal 0 1).real (Ici t) := by
    conv_lhs => rw [← hmap]
    rw [map_measureReal_apply measurable_neg measurableSet_Iic]
    congr 1; ext x; simp
  have h2 : (gaussianReal 0 1).real (Ici t) = (gaussianReal 0 1).real (Ioi t) := by
    rw [← Ioi_insert, ← singleton_union, measureReal_union (by simp) measurableSet_Ioi, measureReal_def,
      gauss_singleton]
    simp
  have h3 := Φn_add_Ioi t
  simp only [Φn, cdf_eq_real] at h3 ⊢
  linarith

end Phi

section F1

variable {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr] {W : Ω → ℝ}

lemma measurable_Φn : Measurable Φn := Φn_continuous.measurable

lemma integrable_Φn_comp (hW : Measurable W) (t : ℝ) :
    Integrable (fun ω => Φn (t / Real.sqrt (W ω))) Pr :=
  Integrable.of_bound (measurable_Φn.comp (measurable_const.div hW.sqrt)).aestronglyMeasurable 1
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_pos (Φn_pos _)]; exact (Φn_lt_one _).le)

lemma integral_pos_of_ae_pos' {f : Ω → ℝ} (hf : ∀ᵐ ω ∂Pr, 0 < f ω) (hfi : Integrable f Pr) :
    0 < ∫ ω, f ω ∂Pr := by
  rw [integral_pos_iff_support_of_nonneg_ae (hf.mono fun _ h => h.le) hfi]
  by_contra h
  push_neg at h
  have h0 : Pr (Function.support f) = 0 := le_antisymm h bot_le
  have : ∀ᵐ ω ∂Pr, ω ∉ Function.support f := measure_eq_zero_iff_ae_notMem.1 h0
  have hfalse : ∀ᵐ ω ∂Pr, False := by
    filter_upwards [this, hf] with ω h1 h2
    exact h1 (Function.mem_support.2 h2.ne')
  have := measure_univ (μ := Pr)
  rw [ae_iff] at hfalse
  simp at hfalse

lemma ellF1_eq (t : ℝ) : ellF1 Pr W t = ∫ ω, Φn (t / Real.sqrt (W ω)) ∂Pr := rfl

lemma continuous_ellF1 (hW : Measurable W) : Continuous (ellF1 Pr W) := by
  refine continuous_of_dominated (F := fun t ω => Φn (t / Real.sqrt (W ω))) (bound := fun _ => 1)
    (fun t => (integrable_Φn_comp hW t).aestronglyMeasurable) (fun t => ae_of_all _ fun ω => ?_)
    (integrable_const 1) (ae_of_all _ fun ω => Φn_continuous.comp (continuous_id.div_const _))
  rw [Real.norm_eq_abs, abs_of_pos (Φn_pos _)]; exact (Φn_lt_one _).le

lemma ellF1_neg (hW : Measurable W) (t : ℝ) : ellF1 Pr W (-t) = 1 - ellF1 Pr W t := by
  rw [ellF1_eq, ellF1_eq]
  have : (fun ω => Φn (-t / Real.sqrt (W ω))) = fun ω => 1 - Φn (t / Real.sqrt (W ω)) := by
    funext ω; rw [neg_div, Φn_neg]
  rw [this, integral_sub (integrable_const 1) (integrable_Φn_comp hW t), integral_const, probReal_univ,
    one_smul]

lemma ellF1_pos (hW : Measurable W) (t : ℝ) : 0 < ellF1 Pr W t :=
  integral_pos_of_ae_pos' (ae_of_all _ fun _ => Φn_pos _) (integrable_Φn_comp hW t)

lemma ellF1_lt_one (hW : Measurable W) (t : ℝ) : ellF1 Pr W t < 1 := by
  have := ellF1_pos (Pr := Pr) hW (-t)
  rw [ellF1_neg hW] at this
  linarith

lemma strictMono_ellF1 (hW : Measurable W) (hpos : ∀ᵐ ω ∂Pr, 0 < W ω) : StrictMono (ellF1 Pr W) := by
  intro s t hst
  have hd : 0 < ∫ ω, (Φn (t / Real.sqrt (W ω)) - Φn (s / Real.sqrt (W ω))) ∂Pr := by
    refine integral_pos_of_ae_pos' ?_ ((integrable_Φn_comp hW t).sub (integrable_Φn_comp hW s))
    filter_upwards [hpos] with ω hω
    have : s / Real.sqrt (W ω) < t / Real.sqrt (W ω) :=
      div_lt_div_of_pos_right hst (Real.sqrt_pos.2 hω)
    linarith [Φn_strictMono this]
  rw [integral_sub (integrable_Φn_comp hW t) (integrable_Φn_comp hW s)] at hd
  rw [ellF1_eq, ellF1_eq]; linarith

lemma tendsto_ellF1_atBot (hW : Measurable W) (hpos : ∀ᵐ ω ∂Pr, 0 < W ω) :
    Tendsto (ellF1 Pr W) atBot (𝓝 0) := by
  have := tendsto_integral_filter_of_dominated_convergence (μ := Pr) (l := atBot)
    (F := fun t ω => Φn (t / Real.sqrt (W ω))) (f := fun _ => 0) (fun _ => 1)
    (Eventually.of_forall fun t => (integrable_Φn_comp hW t).aestronglyMeasurable)
    (Eventually.of_forall fun t => ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (Φn_pos _)]; exact (Φn_lt_one _).le)
    (integrable_const 1) (by
      filter_upwards [hpos] with ω hω
      exact (tendsto_cdf_atBot (μ := gaussianReal 0 1)).comp
        (tendsto_id.atBot_div_const (Real.sqrt_pos.2 hω)))
  rw [integral_zero] at this
  exact this

lemma tendsto_ellF1_atTop (hW : Measurable W) (hpos : ∀ᵐ ω ∂Pr, 0 < W ω) :
    Tendsto (ellF1 Pr W) atTop (𝓝 1) := by
  have := tendsto_integral_filter_of_dominated_convergence (μ := Pr) (l := atTop)
    (F := fun t ω => Φn (t / Real.sqrt (W ω))) (f := fun _ => 1) (fun _ => 1)
    (Eventually.of_forall fun t => (integrable_Φn_comp hW t).aestronglyMeasurable)
    (Eventually.of_forall fun t => ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (Φn_pos _)]; exact (Φn_lt_one _).le)
    (integrable_const 1) (by
      filter_upwards [hpos] with ω hω
      exact (tendsto_cdf_atTop (μ := gaussianReal 0 1)).comp
        (tendsto_id.atTop_div_const (Real.sqrt_pos.2 hω)))
  rw [integral_const, probReal_univ, one_smul] at this
  exact this

end F1

theorem elliptical_F1 : Claims.elliptical_F1 := by
  intro Ω H _ _ _ _ _ Pr G W h
  have := h.prob
  exact ⟨continuous_ellF1 h.meas_W, strictMono_ellF1 h.meas_W h.pos_W, ellF1_neg h.meas_W,
    fun t => ⟨ellF1_pos h.meas_W t, ellF1_lt_one h.meas_W t⟩, tendsto_ellF1_atBot h.meas_W h.pos_W,
    tendsto_ellF1_atTop h.meas_W h.pos_W⟩

section Proj

variable {Ω H : Type*} [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H] {Pr : Measure Ω} {G : Ω → H} {W : Ω → ℝ}

lemma EllSetting.measurable_proj (h : EllSetting Pr G W) (v : H) : Measurable fun ω => ⟪v, G ω⟫_ℝ :=
  (continuous_const.inner continuous_id).measurable.comp h.meas_G

lemma EllSetting.law_proj (h : EllSetting Pr G W) (v : H) :
    Pr.map (fun ω => ⟪v, G ω⟫_ℝ) = gaussianReal 0 (Var[fun ω => ⟪v, G ω⟫_ℝ; Pr]).toNNReal := by
  have := h.prob
  have := h.gauss
  have hL := IsGaussian.map_eq_gaussianReal (μ := Pr.map G) (innerSL ℝ v)
  have hLm : Measurable (innerSL ℝ v) := (innerSL ℝ v).continuous.measurable
  rw [Measure.map_map hLm h.meas_G] at hL
  have hmean : ∫ x, innerSL ℝ v x ∂(Pr.map G) = 0 := by
    rw [integral_map h.meas_G.aemeasurable hLm.aestronglyMeasurable]
    exact h.centred v
  have hvar : Var[innerSL ℝ v; Pr.map G] = Var[fun ω => ⟪v, G ω⟫_ℝ; Pr] := by
    rw [variance_map hLm.aemeasurable h.meas_G.aemeasurable]
    rfl
  rw [hmean, hvar] at hL
  exact hL

lemma EllSetting.law_proj' (h : EllSetting Pr G W) {v : H} (hv : v ≠ 0) :
    Pr.map (fun ω => ⟪v, G ω⟫_ℝ) = (gaussianReal 0 1).map (fun t => projSd Pr G v * t) := by
  rw [h.law_proj, gaussianReal_map_const_mul, mul_zero]
  congr 1
  ext
  simp only [projSd, Real.coe_toNNReal _ (variance_nonneg _ _), NNReal.coe_mul, NNReal.coe_mk,
    NNReal.coe_one, mul_one]
  rw [Real.sq_sqrt (variance_nonneg _ _)]

lemma projSd_pos (h : EllSetting Pr G W) {v : H} (hv : v ≠ 0) : 0 < projSd Pr G v :=
  Real.sqrt_pos.2 (h.inj v hv)

lemma EllSetting.ae_map_pos (h : EllSetting Pr G W) : ∀ᵐ w ∂(Pr.map W), 0 < w :=
  (ae_map_iff h.meas_W.aemeasurable measurableSet_Ioi).2 h.pos_W

lemma EllSetting.prod_law (h : EllSetting Pr G W) (v : H) :
    Pr.map (fun ω => (W ω, ⟪v, G ω⟫_ℝ)) = (Pr.map W).prod (Pr.map fun ω => ⟪v, G ω⟫_ℝ) := by
  have := h.prob
  have hind : IndepFun W (fun ω => ⟪v, G ω⟫_ℝ) Pr :=
    h.indep.comp measurable_id (continuous_const.inner continuous_id).measurable
  exact (indepFun_iff_map_prod_eq_prod_map_map h.meas_W.aemeasurable
    (h.measurable_proj v).aemeasurable).1 hind

/-- `P(√W ⟨v, G⟩ ≤ c) = F₁(c/σ_v)`. -/
lemma EllSetting.prob_le (h : EllSetting Pr G W) {v : H} (hv : v ≠ 0) (c : ℝ) :
    Pr {ω | Real.sqrt (W ω) * ⟪v, G ω⟫_ℝ ≤ c} = ENNReal.ofReal (ellF1 Pr W (c / projSd Pr G v)) := by
  have := h.prob
  set σ := projSd Pr G v with hσ
  have hσp : 0 < σ := projSd_pos h hv
  have hS : MeasurableSet {p : ℝ × ℝ | Real.sqrt p.1 * p.2 ≤ c} :=
    measurableSet_le (measurable_fst.sqrt.mul measurable_snd) measurable_const
  have hWY : Measurable fun ω => (W ω, ⟪v, G ω⟫_ℝ) := h.meas_W.prodMk (h.measurable_proj v)
  have e1 : Pr {ω | Real.sqrt (W ω) * ⟪v, G ω⟫_ℝ ≤ c} =
      (Pr.map fun ω => (W ω, ⟪v, G ω⟫_ℝ)) {p : ℝ × ℝ | Real.sqrt p.1 * p.2 ≤ c} := by
    rw [Measure.map_apply hWY hS]; rfl
  rw [e1, h.prod_law, Measure.prod_apply hS]
  have hslice : ∀ w : ℝ, 0 < w → (Pr.map fun ω => ⟪v, G ω⟫_ℝ) (Prod.mk w ⁻¹' {p : ℝ × ℝ | Real.sqrt p.1 * p.2 ≤ c})
      = ENNReal.ofReal (Φn (c / σ / Real.sqrt w)) := by
    intro w hw
    have hsw : 0 < Real.sqrt w := Real.sqrt_pos.2 hw
    rw [h.law_proj' hv, Measure.map_apply (measurable_const_mul σ) (measurableSet_preimage measurable_prodMk_left hS)]
    have : (fun t => σ * t) ⁻¹' (Prod.mk w ⁻¹' {p : ℝ × ℝ | Real.sqrt p.1 * p.2 ≤ c}) =
        Iic (c / σ / Real.sqrt w) := by
      ext t
      simp only [mem_preimage, mem_ofPred_eq, mem_Iic]
      rw [div_div, le_div_iff₀ (mul_pos hσp hsw)]
      constructor <;> intro h' <;> nlinarith
    rw [this, ← ofReal_cdf]
  rw [lintegral_congr_ae (h.ae_map_pos.mono fun w hw => hslice w hw)]
  have hm : Measurable fun w : ℝ => ENNReal.ofReal (Φn (c / σ / Real.sqrt w)) :=
    ENNReal.measurable_ofReal.comp (measurable_Φn.comp (measurable_const.div measurable_id.sqrt))
  rw [lintegral_map hm h.meas_W]
  rw [ellF1_eq, ofReal_integral_eq_lintegral_ofReal (integrable_Φn_comp h.meas_W _)
    (ae_of_all _ fun _ => (Φn_pos _).le)]

theorem _root_.StatFormal.Wave23c.elliptical_proj : Claims.elliptical_proj := by
  intro Ω H _ _ _ _ _ Pr G W h v hv x
  have hX : Measurable fun ω => Real.sqrt (W ω) • G ω := h.meas_W.sqrt.smul h.meas_G
  have hset : MeasurableSet {z : H | ⟪v, z - x⟫_ℝ ≤ 0} :=
    measurableSet_le ((continuous_const.inner (continuous_id.sub continuous_const)).measurable)
      measurable_const
  rw [ellLaw, Measure.map_apply hX hset, ← h.prob_le hv]
  congr 1
  ext ω
  simp only [mem_preimage, mem_setOf_eq, inner_sub_right, inner_smul_right]
  constructor <;> intro h' <;> linarith

theorem _root_.StatFormal.Wave23c.elliptical_atomless : Claims.elliptical_atomless := by
  intro Ω H _ _ _ _ _ Pr G W h v hv s
  have := h.prob
  have hX : Measurable fun ω => Real.sqrt (W ω) • G ω := h.meas_W.sqrt.smul h.meas_G
  have hset : MeasurableSet {z : H | ⟪v, z⟫_ℝ = s} :=
    measurableSet_eq_fun ((continuous_const.inner continuous_id).measurable) measurable_const
  rw [ellLaw, Measure.map_apply hX hset]
  have hS : MeasurableSet {p : ℝ × ℝ | Real.sqrt p.1 * p.2 = s} :=
    measurableSet_eq_fun (measurable_fst.sqrt.mul measurable_snd) measurable_const
  have hWY : Measurable fun ω => (W ω, ⟪v, G ω⟫_ℝ) := h.meas_W.prodMk (h.measurable_proj v)
  have e1 : Pr ((fun ω => Real.sqrt (W ω) • G ω) ⁻¹' {z : H | ⟪v, z⟫_ℝ = s}) =
      (Pr.map fun ω => (W ω, ⟪v, G ω⟫_ℝ)) {p : ℝ × ℝ | Real.sqrt p.1 * p.2 = s} := by
    rw [Measure.map_apply hWY hS]
    congr 1; ext ω; simp [inner_smul_right]
  rw [e1, h.prod_law, Measure.prod_apply hS]
  have hnull : NullSingletonClass (Pr.map fun ω => ⟪v, G ω⟫_ℝ) := by
    rw [h.law_proj]
    exact nullSingletonClass_gaussianReal (by
      rw [ne_eq, Real.toNNReal_eq_zero, not_le]; exact h.inj v hv)
  refine (lintegral_congr_ae (h.ae_map_pos.mono fun w hw => ?_)).trans lintegral_zero
  have : Prod.mk w ⁻¹' {p : ℝ × ℝ | Real.sqrt p.1 * p.2 = s} = {s / Real.sqrt w} := by
    ext y
    simp only [mem_preimage, mem_setOf_eq, mem_singleton_iff]
    rw [eq_div_iff (Real.sqrt_pos.2 hw).ne']
    constructor <;> intro h' <;> linarith
  rw [this]
  exact measure_singleton _

end Proj

end StatFormal.Wave23c
