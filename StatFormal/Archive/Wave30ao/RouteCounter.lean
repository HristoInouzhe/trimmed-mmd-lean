import StatFormal.Archive.Wave30ao.RouteClaims

/-!
# Route — `rem:convention` as printed ("both marginals absolutely continuous") is false (untrusted)

`μ = p · Leb` on `ℝ¹`, `p(x) = 1/(x log² x)` on `(0, e⁻¹)`: a probability density (antiderivative `−1/log x`),
supported in `[0, 1]` (so `μ ∈ 𝒫₂`), with `p log p ≥ 1/(2x(−log x))` near `0` (antiderivative `−log(−log x)`, unbounded),
so `(log p)⁺ ∉ L¹(μ)` while `(log p)⁻ ∈ L¹(μ)` (library `negPart_integrable_P2`): `Ent(μ) = −∞`. With `ν = N(0,1)`,
`plan_literal` makes the printed objective `+∞` on every coupling, and the certified Wave 29t `equiv_static_ac_d`
(which needs `ass:ac` only for `ν`) gives a unique Sinkhorn-normalised plan.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology InformationTheory TauCeti ProbabilityTheory

namespace StatFormal.Wave30ao

open StatFormal.Wave29t (isoGauss acHyps_isoG equiv_static_ac_d)
open StatFormal.Wave29g (IsEntPlanD)

local notation "E" d => EuclideanSpace ℝ (Fin d)

namespace Counter

def cE : ℝ := Real.exp (-1)
def fd (x : ℝ) : ℝ := (Ioo 0 cE).indicator (fun x => 1 / (x * Real.log x ^ 2)) x
def gF (x : ℝ) : ℝ := -(Real.log x)⁻¹

lemma cE_pos : 0 < cE := Real.exp_pos _
lemma cE_lt_one : cE < 1 := by unfold cE; rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by norm_num)

lemma log_le_neg_one {x : ℝ} (h0 : 0 < x) (h : x ≤ cE) : Real.log x ≤ -1 := by
  have := Real.log_le_log h0 h; simpa [cE] using this

lemma hasDeriv_gF {x : ℝ} (hx0 : 0 < x) (hl : Real.log x ≠ 0) :
    HasDerivAt gF (1 / (x * Real.log x ^ 2)) x := by
  have h := ((Real.hasDerivAt_log hx0.ne').inv hl).neg
  show HasDerivAt (fun y => -(Real.log y)⁻¹) _ x
  convert h using 1
  field_simp

lemma gF_contAt0 : ContinuousAt gF 0 := by
  rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
  have h0 : gF 0 = 0 := by simp [gF]
  rw [h0]
  have := (tendsto_inv_atBot_zero.comp Real.tendsto_log_nhdsNE_zero).neg
  unfold gF
  simpa [Function.comp_def] using this

lemma gF_cont : ContinuousOn gF (Icc 0 cE) := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with h | h
  · subst h; exact gF_contAt0.continuousWithinAt
  · have hl : Real.log x ≠ 0 := by linarith [log_le_neg_one h hx.2]
    exact (hasDeriv_gF h hl).continuousAt.continuousWithinAt

lemma gF_deriv : ∀ x ∈ Ioo 0 cE, HasDerivAt gF (1 / (x * Real.log x ^ 2)) x := fun x hx =>
  hasDeriv_gF hx.1 (by linarith [log_le_neg_one hx.1 hx.2.le])

lemma integrableOn_f : IntegrableOn (fun x : ℝ => 1 / (x * Real.log x ^ 2)) (Ioc 0 cE) :=
  intervalIntegral.integrableOn_deriv_of_nonneg gF_cont gF_deriv fun x hx => by
    have := hx.1; positivity

lemma integral_f : ∫ x in (0 : ℝ)..cE, 1 / (x * Real.log x ^ 2) = 1 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le cE_pos.le gF_cont gF_deriv
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le cE_pos.le).2 integrableOn_f)]
  simp [gF, cE]

lemma measurable_fd : Measurable fd :=
  Measurable.indicator (by fun_prop) measurableSet_Ioo

lemma fd_nonneg (x : ℝ) : 0 ≤ fd x := by
  unfold fd
  by_cases hx : x ∈ Ioo 0 cE
  · rw [indicator_of_mem hx]; have := hx.1; positivity
  · rw [indicator_of_notMem hx]

lemma integrable_fd : Integrable fd :=
  (integrable_indicator_iff measurableSet_Ioo).2 (integrableOn_f.mono_set Ioo_subset_Ioc_self)

lemma integral_fd : ∫ x, fd x = 1 := by
  unfold fd
  rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le cE_pos.le, integral_f]

lemma lintegral_fd : ∫⁻ x, ENNReal.ofReal (fd x) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal integrable_fd (Eventually.of_forall fd_nonneg), integral_fd,
    ENNReal.ofReal_one]

/-! Non-integrability of `f log f` near `0`. -/

def δ : ℝ := Real.exp (-64)
def hh (x : ℝ) : ℝ := 1 / (x * (-Real.log x))
def HH (x : ℝ) : ℝ := -Real.log (-Real.log x)

lemma hasDeriv_HH {x : ℝ} (hx0 : 0 < x) (hl : Real.log x < 0) : HasDerivAt HH (hh x) x := by
  have h := ((Real.hasDerivAt_log hx0.ne').neg.log (by simp only [Pi.neg_apply]; linarith)).neg
  show HasDerivAt (fun y => -Real.log (-Real.log y)) _ x
  convert h using 1
  simp only [hh, Pi.neg_apply]
  have : Real.log x ≠ 0 := hl.ne
  field_simp

lemma δ_lt_cE : δ < cE := by unfold δ cE; rw [Real.exp_lt_exp]; norm_num

lemma not_integrableOn_hh : ¬ IntegrableOn hh (Ioc 0 δ) := by
  intro hI
  set I := ∫ x in Ioc 0 δ, hh x
  have hpos : ∀ x ∈ Ioc 0 δ, 0 ≤ hh x := fun x hx => by
    have : Real.log x < 0 := Real.log_neg hx.1 (lt_of_le_of_lt hx.2 (δ_lt_cE.trans cE_lt_one))
    unfold hh
    have := hx.1
    have : 0 < -Real.log x := by linarith
    positivity
  have key : ∀ M : ℝ, 5 ≤ M → M - Real.log 64 ≤ I := by
    intro M hM
    set a := Real.exp (-Real.exp M)
    have ha0 : 0 < a := Real.exp_pos _
    have h64 : (64 : ℝ) ≤ Real.exp M := by
      have := Real.add_one_le_exp M
      have h2 := Real.exp_le_exp.2 hM
      have h3 : (64 : ℝ) ≤ Real.exp 5 := by
        have := Real.exp_one_gt_d9
        have h5 : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
        rw [h5]; nlinarith [pow_le_pow_left₀ (by norm_num) this.le 5]
      linarith
    have haδ : a ≤ δ := by unfold δ; rw [Real.exp_le_exp]; linarith
    have hderiv : ∀ x ∈ Ioo a δ, HasDerivAt HH (hh x) x := fun x hx =>
      hasDeriv_HH (ha0.trans hx.1) (Real.log_neg (ha0.trans hx.1) (hx.2.trans (δ_lt_cE.trans cE_lt_one)))
    have hcont : ContinuousOn HH (Icc a δ) := fun x hx =>
      (hasDeriv_HH (ha0.trans_le hx.1) (Real.log_neg (ha0.trans_le hx.1)
        (lt_of_le_of_lt hx.2 (δ_lt_cE.trans cE_lt_one)))).continuousAt.continuousWithinAt
    have hsub : Ioc a δ ⊆ Ioc 0 δ := Ioc_subset_Ioc_left ha0.le
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le haδ hcont hderiv
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le haδ).2 (hI.mono_set hsub))
    rw [intervalIntegral.integral_of_le haδ] at hint
    have hmono : ∫ x in Ioc a δ, hh x ≤ I :=
      setIntegral_mono_set hI (ae_restrict_of_forall_mem measurableSet_Ioc hpos) hsub.eventuallyLE
    have e1 : HH δ = -Real.log 64 := by simp [HH, δ]
    have e2 : HH a = -M := by simp [HH, a]
    rw [e1, e2] at hint
    linarith
  have := key (max 5 (I + Real.log 64 + 1)) (le_max_left _ _)
  linarith [le_max_right 5 (I + Real.log 64 + 1)]

lemma four_log_le {u : ℝ} (hu : 64 ≤ u) : 4 * Real.log u ≤ u := by
  have hu0 : 0 < u := by linarith
  have hs := Real.sqrt_pos.2 hu0
  have h1 := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt hu0.le] at h1
  have h2 := Real.sq_sqrt hu0.le
  have h8 : 8 ≤ Real.sqrt u := by
    rw [show (8 : ℝ) = Real.sqrt 64 by rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hu
  nlinarith

theorem not_integrable_flogf : ¬ Integrable (fun x => fd x * Real.log (fd x)) := by
  intro hI
  apply not_integrableOn_hh
  refine Integrable.mono' ((hI.integrableOn (s := Ioc 0 δ)).const_mul 2) (Measurable.aestronglyMeasurable (by unfold hh; fun_prop)) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => ?_
  have hx0 := hx.1
  have hxc : x ∈ Ioo 0 cE := ⟨hx0, lt_of_le_of_lt hx.2 δ_lt_cE⟩
  have hL : Real.log x ≤ -64 := by
    have := Real.log_le_log hx0 hx.2; simpa [δ] using this
  set u := -Real.log x with hu
  have hu64 : 64 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  have hf : fd x = 1 / (x * u ^ 2) := by
    rw [fd, indicator_of_mem hxc, hu, neg_sq]
  have hlog : Real.log (fd x) = u - 2 * Real.log u := by
    rw [hf, one_div, Real.log_inv, Real.log_mul hx0.ne' (by positivity), Real.log_pow]
    push_cast; rw [hu]; ring
  rw [hlog, hf]
  have hhx : hh x = 1 / (x * u) := by simp [hh, hu]
  rw [hhx, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have k := four_log_le hu64
  have hk : 0 < 1 / (x * u ^ 2) := by positivity
  have e : 1 / (x * u) = 1 / (x * u ^ 2) * u := by field_simp
  rw [e]
  nlinarith [mul_nonneg hk.le (sub_nonneg.2 k)]


/-! ### The measure on `ℝ¹ = EuclideanSpace ℝ (Fin 1)` -/



def φe : (E 1) ≃ᵐ ℝ := (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm.trans (MeasurableEquiv.funUnique (Fin 1) ℝ)

lemma φe_mp : MeasurePreserving φe volume volume :=
  (volume_preserving_funUnique (Fin 1) ℝ).comp (PiLp.volume_preserving_ofLp (Fin 1))

lemma norm_sq_φe (x : E 1) : ‖x‖ ^ 2 = (φe x) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_one, Real.norm_eq_abs, sq_abs]
  rfl

def μc : Measure (E 1) := volume.withDensity (fun x => ENNReal.ofReal (fd (φe x)))

lemma measurable_dens : Measurable (fun x : E 1 => ENNReal.ofReal (fd (φe x))) :=
  (measurable_fd.comp φe.measurable).ennreal_ofReal

instance : IsProbabilityMeasure μc := by
  constructor
  rw [μc, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    φe_mp.lintegral_comp_emb φe.measurableEmbedding (fun t => ENNReal.ofReal (fd t)), lintegral_fd]

lemma μc_ac : μc ≪ volume := withDensity_absolutelyContinuous _ _

lemma μc_P2 : Integrable (fun x : E 1 => ‖x‖ ^ 2) μc := by
  refine Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop) ?_
  rw [μc, ae_withDensity_iff measurable_dens]
  refine Eventually.of_forall fun x hx => ?_
  have hpos : fd (φe x) ≠ 0 := fun h => hx (by rw [h, ENNReal.ofReal_zero])
  have hmem : φe x ∈ Ioo 0 cE := by
    by_contra h; exact hpos (by rw [fd, indicator_of_notMem h])
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_sq_φe]
  have := hmem.1; have := hmem.2; have := cE_lt_one
  nlinarith

lemma logDensity_μc : logDensity μc =ᵐ[μc] fun x => Real.log (fd (φe x)) := by
  have h := Measure.rnDeriv_withDensity (volume : Measure (E 1)) measurable_dens
  filter_upwards [μc_ac.ae_le h] with x hx
  simp only [logDensity]
  rw [show μc = volume.withDensity (fun x => ENNReal.ofReal (fd (φe x))) from rfl, hx,
    ENNReal.toReal_ofReal (fd_nonneg _)]

lemma μc_not_fin : ¬ HasFiniteEnt μc := by
  rintro ⟨-, hI⟩
  rw [integrable_congr logDensity_μc, μc,
    integrable_withDensity_iff_integrable_smul' measurable_dens (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hI
  simp only [ENNReal.toReal_ofReal (fd_nonneg _), smul_eq_mul] at hI
  exact not_integrable_flogf ((φe_mp.integrable_comp_emb φe.measurableEmbedding
    (g := fun t => fd t * Real.log (fd t))).1 hI)

end Counter

open Counter in
theorem convention_counter : Claims.convention_counter := by
  obtain ⟨hq, hq0, hνq, hlog, hν2⟩ := acHyps_isoG 1
  have hνac : isoGauss 1 1 ≪ volume := by rw [hνq]; exact withDensity_absolutelyContinuous _ _
  have hνf : HasFiniteEnt (isoGauss 1 1) := by
    refine ⟨hνac, hlog.congr ?_⟩
    have h := Measure.rnDeriv_withDensity (volume : Measure (E 1)) hq.ennreal_ofReal
    rw [← hνq] at h
    filter_upwards [hνac.ae_le h] with y hy
    simp [logDensity, hy, ENNReal.toReal_ofReal (hq0 y)]
  have hneg : Integrable (fun x => max (-logDensity μc x) 0) μc :=
    StatFormal.DiffEntropy.negPart_integrable_P2 μc_ac μc_P2
  have hposn : ¬ Integrable (fun x => max (logDensity μc x) 0) μc := fun hp =>
    μc_not_fin ⟨μc_ac, StatFormal.DiffEntropy.integrable_of_pos_neg
      (measurable_llr _ _).aestronglyMeasurable hp hneg⟩
  refine ⟨μc, isoGauss 1 1, inferInstance, inferInstance, μc_P2, hν2, μc_ac, hνac, hνf, μc_not_fin, hneg, hposn,
    fun ε hε => ?_⟩
  have htop : ∀ π : Measure ((E 1) × (E 1)), IsCoupling π μc (isoGauss 1 1) → entObj ε π = ⊤ :=
    (plan_literal 1 ε μc (isoGauss 1 1) hε inferInstance inferInstance μc_P2 hν2).2 (fun h => μc_not_fin h.1)
  refine ⟨htop, ?_, fun ⟨π, hπ⟩ => hπ.2.1 (htop π hπ.1), ?_⟩
  · simp only [entCost, iInf_eq_top]
    exact htop
  · exact (equiv_static_ac_d 1 ε μc (isoGauss 1 1) _ hε inferInstance inferInstance hq hq0 hνq hlog μc_P2
      hν2).2.2.2.2


end StatFormal.Wave30ao
