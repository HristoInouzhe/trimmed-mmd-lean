import StatFormal.Archive.Wave21a.RouteCommon
import StatFormal.Lib.Tax.Tax
import StatFormal.Lib.SemiDiscrete.HeldOut

/-!
# Route — JASA `prop:tax` (untrusted)

* (a) bound: `ϰ(β) ≤ KL(U ‖ N(0, β²) ∗ δ₀) = KL(U ‖ N(0, β²)) = log(√(2π)β) + E U²/(2β²)`, `E U² = 1/12`
  (densities: `klRef_withDensity`); `ϰ ≥ 0` (`klRef ≥ 0` between probability laws).
* (a) monotonicity: `N(0, β'²) ∗ m = N(0, β²) ∗ (N(0, β'² − β²) ∗ m)` (`conv_assoc`, `gaussianReal_conv_gaussianReal`).
* (c): Hoeffding's lower tail for the bounded `g` (`hoeffding_lower_fintype`), then (b) (the hypothesis).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatFormal.Wave21a

open StatFormal.RobustEquality

instance boxU_isProb : IsProbabilityMeasure boxU := by
  constructor
  simp only [boxU, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc]
  norm_num

lemma boxU_eq_withDensity :
    boxU = volume.withDensity fun x => ENNReal.ofReal ((Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ => (1 : ℝ)) x) := by
  rw [boxU, ← withDensity_indicator_one measurableSet_Icc]
  congr 1
  funext x
  by_cases hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)
  · rw [indicator_of_mem hx, indicator_of_mem hx]; simp
  · rw [indicator_of_notMem hx, indicator_of_notMem hx]; simp

lemma integral_box_sq : ∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), x ^ 2 = 1 / 12 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num), integral_pow]
  norm_num

/-- `KL(U[−½,½] ‖ N(0, v)) = log √(2πv) + 1/(24 v)`. -/
lemma klRef_boxU_gaussian {v : ℝ≥0} (hv : v ≠ 0) :
    klRef boxU (gaussianReal 0 v) =
      ((Real.log (√(2 * Real.pi * v)) + 1 / (24 * (v : ℝ)) : ℝ) : EReal) := by
  have hvpos : (0 : ℝ) < v := by positivity
  set s := Icc (-(1 / 2 : ℝ)) (1 / 2)
  set p : ℝ → ℝ := fun x => s.indicator (fun _ => (1 : ℝ)) x
  have hp : Measurable p := measurable_const.indicator measurableSet_Icc
  have hq : Measurable (gaussianPDFReal 0 v) := measurable_gaussianPDFReal 0 v
  have hfun : (fun x => p x * Real.log (p x / gaussianPDFReal 0 v x)) =
      s.indicator fun x => Real.log (√(2 * Real.pi * v)) + x ^ 2 / (2 * v) := by
    funext x
    by_cases hx : x ∈ s
    · simp only [p, indicator_of_mem hx, one_mul, one_div]
      rw [Real.log_inv, gaussianPDFReal_def]
      rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_inv, Real.log_exp]
      ring
    · simp [p, indicator_of_notMem hx]
  have hint : Integrable (fun x => p x * Real.log (p x / gaussianPDFReal 0 v x)) volume := by
    rw [hfun, integrable_indicator_iff measurableSet_Icc]
    exact (Continuous.integrableOn_Icc (by fun_prop))
  rw [boxU_eq_withDensity, gaussianReal_of_var_ne_zero 0 hv, gaussianPDF_def]
  rw [klRef_withDensity volume hp hq (fun x => indicator_nonneg (fun _ _ => zero_le_one) x) (fun x => (gaussianPDFReal_nonneg 0 v x))
    (fun x _ => gaussianPDFReal_pos 0 v x hv) hint]
  congr 1
  rw [hfun, integral_indicator measurableSet_Icc]
  rw [integral_add (Continuous.integrableOn_Icc (continuous_const))
    ((Continuous.integrableOn_Icc (by fun_prop)))]
  rw [setIntegral_const, integral_div, integral_box_sq]
  simp only [s, Measure.real, Real.volume_Icc]
  norm_num
  field_simp
  ring

/-- `prop:tax`(a), point-mass bound. -/
theorem tax_a_bound : Claims.tax_a_bound := by
  intro β hβ
  have hv : (β ^ 2).toNNReal ≠ 0 := by
    simp only [ne_eq, Real.toNNReal_eq_zero, not_le]; positivity
  constructor
  · refine le_iInf₂ fun m hm => ?_
    exact StatFormal.Foundations.Tax.klRef_nonneg_of_prob _ _
  · refine (iInf₂_le (Measure.dirac 0) (inferInstance : IsProbabilityMeasure (Measure.dirac (0 : ℝ)))).trans ?_
    rw [Measure.conv_dirac, show (fun y : ℝ => y + 0) = id from funext fun y => add_zero y, Measure.map_id,
      klRef_boxU_gaussian hv]
    rw [Real.coe_toNNReal _ (by positivity)]
    have h1 : √(2 * Real.pi * β ^ 2) = √(2 * Real.pi) * β := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hβ.le]
    rw [h1]

/-- `prop:tax`(a), monotonicity. -/
theorem tax_a_mono : Claims.tax_a_mono := by
  intro β hβ β' hβ' hle
  simp only [mem_Ioi] at hβ hβ'
  refine le_iInf₂ fun m hm => ?_
  haveI := hm
  have hsplit : gaussianReal 0 (β' ^ 2).toNNReal ∗ m =
      gaussianReal 0 (β ^ 2).toNNReal ∗ (gaussianReal 0 (β' ^ 2 - β ^ 2).toNNReal ∗ m) := by
    rw [← Measure.conv_assoc, gaussianReal_conv_gaussianReal, add_zero]
    congr 2
    rw [← Real.toNNReal_add (by positivity) (by nlinarith)]
    congr 1; ring
  rw [hsplit]
  refine iInf₂_le (gaussianReal 0 (β' ^ 2 - β ^ 2).toNNReal ∗ m) ?_
  infer_instance

/-- `prop:tax`(c), conditional on (b). -/
theorem tax_c : Claims.tax_c := by
  intro Y K _ _ Prec _ 𝒩 P g gm gp a n hn ha0 ha1 hg hgr htax
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨y0⟩ := nonempty_of_isProbabilityMeasure Prec
  have hb : 0 ≤ gp - gm := by linarith [(hgr y0).1, (hgr y0).2]
  have hgI : ∀ y, g y ∈ Icc gm (gm + (gp - gm)) := fun y => ⟨(hgr y).1, by linarith [(hgr y).2]⟩
  have hind : iIndepFun (fun (j : Fin n) (w : Fin n → Y) => w j) (Measure.pi fun _ : Fin n => Prec) :=
    iIndepFun_pi (X := fun _ => id) fun _ => aemeasurable_id
  obtain ⟨hmeas, hprob⟩ := hoeff_event (P := Prec) (μ := Measure.pi fun _ : Fin n => Prec) hg hb hgI
    (Y := fun j w => w j) (fun j => measurable_pi_apply j) hind
    (fun j => (measurePreserving_eval (fun _ : Fin n => Prec) j).map_eq) ha0 ha1
  simp only [Fintype.card_fin] at hmeas hprob
  refine ⟨_, hmeas, hprob, fun y hy => ?_⟩
  exact htax.trans (EReal.coe_le_coe_iff.2 hy)

section Limit

/-- The uniform law on `J ⊆ ℝ`. -/
def unifR (J : Set ℝ) : Measure ℝ := (volume J)⁻¹ • volume.restrict J

/-- The `ℝ≥0∞` density `P{x : y − x ∈ J} / |J|` of `P ∗ U_J`. -/
def jitDR (P : Measure ℝ) (J : Set ℝ) (y : ℝ) : ℝ≥0∞ := P {x | y - x ∈ J} / volume J

lemma measurable_jitDR (P : Measure ℝ) [SFinite P] {J : Set ℝ} (hJ : MeasurableSet J) :
    Measurable (jitDR P J) :=
  (measurable_measure_prodMk_right (hJ.preimage (measurable_snd.sub measurable_fst) :
    MeasurableSet {p : ℝ × ℝ | p.2 - p.1 ∈ J})).div_const _

lemma unifR_isProb {J : Set ℝ} (hJ0 : volume J ≠ 0) (hJf : volume J ≠ ⊤) : IsProbabilityMeasure (unifR J) := by
  constructor
  simp only [unifR, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hJ0 hJf

/-- `P ∗ U_J = p̃ · Leb`. -/
lemma conv_unifR_eq (P : Measure ℝ) [IsProbabilityMeasure P] {J : Set ℝ} (hJ : MeasurableSet J)
    (hJ0 : volume J ≠ 0) :
    P ∗ unifR J = volume.withDensity (jitDR P J) := by
  haveI : SFinite (unifR J) := by unfold unifR; infer_instance
  ext A hA
  rw [withDensity_apply _ hA, ← lintegral_indicator_one hA,
    Measure.lintegral_conv (measurable_one.indicator hA)]
  have hin : ∀ x : ℝ, ∫⁻ u, A.indicator 1 (x + u) ∂(unifR J) =
      (volume J)⁻¹ * ∫⁻ y, A.indicator 1 y * J.indicator 1 (y - x) := by
    intro x
    rw [unifR, lintegral_smul_measure, smul_eq_mul]
    congr 1
    rw [← lintegral_indicator hJ]
    have := lintegral_add_left_eq_self (μ := (volume : Measure ℝ))
      (fun y => A.indicator 1 y * J.indicator 1 (y - x)) x
    rw [← this]
    congr 1
    funext u
    simp only [add_sub_cancel_left]
    by_cases hu : u ∈ J
    · rw [indicator_of_mem hu, indicator_of_mem hu, Pi.one_apply, mul_one]
    · rw [indicator_of_notMem hu, indicator_of_notMem hu, mul_zero]
  simp_rw [hin]
  have hF : Measurable fun p : ℝ × ℝ => A.indicator (1 : ℝ → ℝ≥0∞) p.2 * J.indicator 1 (p.2 - p.1) :=
    ((measurable_one.indicator hA).comp measurable_snd).mul
      ((measurable_one.indicator hJ).comp (measurable_snd.sub measurable_fst))
  have hinv : (volume J)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hJ0
  calc ∫⁻ x, (volume J)⁻¹ * (∫⁻ y, A.indicator 1 y * J.indicator 1 (y - x) ∂volume) ∂P
      = (volume J)⁻¹ * ∫⁻ x, (∫⁻ y, A.indicator 1 y * J.indicator 1 (y - x) ∂volume) ∂P :=
        lintegral_const_mul' _ _ hinv
    _ = (volume J)⁻¹ * ∫⁻ y, (∫⁻ x, A.indicator 1 y * J.indicator 1 (y - x) ∂P) ∂volume := by
        rw [lintegral_lintegral_swap hF.aemeasurable]
    _ = (volume J)⁻¹ * ∫⁻ y, A.indicator 1 y * P {x | y - x ∈ J} := by
        congr 1
        refine lintegral_congr fun y => ?_
        rw [lintegral_const_mul' _ _ (by by_cases hy : y ∈ A <;> simp [hy])]
        congr 1
        have hm : MeasurableSet {x : ℝ | y - x ∈ J} := hJ.preimage (measurable_const.sub measurable_id)
        rw [← lintegral_indicator_one hm]
        congr 1
    _ = ∫⁻ y in A, jitDR P J y := by
        rw [← lintegral_indicator hA, ← lintegral_const_mul' _ _ hinv]
        refine lintegral_congr fun y => ?_
        by_cases hy : y ∈ A
        · simp only [indicator_of_mem hy, Pi.one_apply, one_mul, jitDR, div_eq_mul_inv, mul_comm]
        · simp [indicator_of_notMem hy]

/-- **The smoothed-box bound**: for `0 < β < 1`, `ϰ(β) ≤ −log((1 − β)/(1 + 2√β))` (mixing law `U[−a, a]`,
`a = ½ + √β`, and Chebyshev for `N(0, β²)` at `√β`). -/
lemma varkappa_le_smooth {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    varkappa β ≤ ((-Real.log ((1 - β) / (1 + 2 * √β)) : ℝ) : EReal) := by
  set s := √β with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.2 hβ0
  have hss : s ^ 2 = β := Real.sq_sqrt hβ0.le
  set a := 1 / 2 + s
  have ha0 : 0 < a := by positivity
  set J := Icc (-a) a
  have hJm : MeasurableSet J := measurableSet_Icc
  have hJvol : volume J = ENNReal.ofReal (1 + 2 * s) := by
    simp only [J, Real.volume_Icc]; congr 1; simp only [a]; ring
  have hJ0 : volume J ≠ 0 := by rw [hJvol]; simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hJf : volume J ≠ ⊤ := by rw [hJvol]; exact ENNReal.ofReal_ne_top
  haveI : IsProbabilityMeasure (unifR J) := unifR_isProb hJ0 hJf
  set v := (β ^ 2).toNNReal
  set G := gaussianReal 0 v
  -- Chebyshev
  have hcheb : G {w | s ≤ |w|} ≤ ENNReal.ofReal β := by
    have h := meas_ge_le_variance_div_sq (μ := G) (memLp_id_gaussianReal 2) hs0
    have hmean : ∫ x, x ∂G = 0 := integral_id_gaussianReal
    have hvar : variance id G = v := variance_id_gaussianReal
    rw [hvar] at h
    simp only [id] at h
    rw [hmean] at h
    simp only [sub_zero] at h
    refine h.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [Real.coe_toNNReal _ (by positivity), hss]; field_simp
  set c : ℝ := (1 - β) / (1 + 2 * s)
  have hc0 : 0 < c := div_pos (by linarith) (by positivity)
  set q : ℝ → ℝ := fun y => (jitDR G J y).toReal
  have hjd_le : ∀ y, jitDR G J y ≤ (volume J)⁻¹ := fun y => by
    unfold jitDR; rw [div_eq_mul_inv]
    calc G {x | y - x ∈ J} * (volume J)⁻¹ ≤ 1 * (volume J)⁻¹ := by gcongr; exact prob_le_one
      _ = _ := one_mul _
  have hjd_ne : ∀ y, jitDR G J y ≠ ⊤ := fun y => ne_top_of_le_ne_top (ENNReal.inv_ne_top.2 hJ0) (hjd_le y)
  have hqm : Measurable q := (measurable_jitDR G hJm).ennreal_toReal
  have hq0 : ∀ y, 0 ≤ q y := fun y => ENNReal.toReal_nonneg
  have hqmax : ∀ y, q y ≤ 1 / (1 + 2 * s) := fun y => by
    have := ENNReal.toReal_mono (ENNReal.inv_ne_top.2 hJ0) (hjd_le y)
    rw [ENNReal.toReal_inv, hJvol, ENNReal.toReal_ofReal (by positivity), ← one_div] at this
    exact this
  -- the lower bound on the box
  have hqmin : ∀ y ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), c ≤ q y := by
    intro y hy
    have hsub : {w : ℝ | s ≤ |w|}ᶜ ⊆ {x | y - x ∈ J} := by
      intro w hw
      simp only [mem_compl_iff, mem_setOf_eq, not_le] at hw
      obtain ⟨hy1, hy2⟩ := hy
      rw [abs_lt] at hw
      simp only [mem_setOf_eq, J, mem_Icc, a]
      constructor <;> linarith [hw.1, hw.2]
    have hmeas : MeasurableSet {w : ℝ | s ≤ |w|} := measurableSet_le measurable_const continuous_abs.measurable
    have h1 : ENNReal.ofReal (1 - β) ≤ G {x | y - x ∈ J} := by
      calc ENNReal.ofReal (1 - β) = 1 - ENNReal.ofReal β := by
            rw [ENNReal.ofReal_sub _ hβ0.le, ENNReal.ofReal_one]
        _ ≤ 1 - G {w | s ≤ |w|} := tsub_le_tsub_left hcheb _
        _ = G {w : ℝ | s ≤ |w|}ᶜ := (prob_compl_eq_one_sub hmeas).symm
        _ ≤ _ := measure_mono hsub
    simp only [q, jitDR]
    rw [ENNReal.toReal_div, hJvol, ENNReal.toReal_ofReal (by positivity)]
    have := ENNReal.toReal_mono (measure_ne_top _ _) h1
    rw [ENNReal.toReal_ofReal (by linarith)] at this
    exact div_le_div_of_nonneg_right this (by positivity)
  -- the KL computation
  set box := Icc (-(1 / 2 : ℝ)) (1 / 2)
  set p : ℝ → ℝ := fun x => box.indicator (fun _ => (1 : ℝ)) x
  have hp : Measurable p := measurable_const.indicator measurableSet_Icc
  have hp0 : ∀ x, 0 ≤ p x := fun x => indicator_nonneg (fun _ _ => zero_le_one) x
  have hpq : ∀ x, p x ≠ 0 → 0 < q x := fun x hx => by
    by_cases hxb : x ∈ box
    · exact hc0.trans_le (hqmin x hxb)
    · simp [p, indicator_of_notMem hxb] at hx
  have hfun : (fun x => p x * Real.log (p x / q x)) = box.indicator fun x => -Real.log (q x) := by
    funext x
    by_cases hx : x ∈ box
    · simp only [p, indicator_of_mem hx, one_mul, one_div]; rw [Real.log_inv]
    · simp [p, indicator_of_notMem hx]
  have hlogb : ∀ x ∈ box, |-Real.log (q x)| ≤ |Real.log c| + |Real.log (1 / (1 + 2 * s))| := by
    intro x hx
    have h1 := hqmin x hx; have h2 := hqmax x
    have hqx : 0 < q x := hc0.trans_le h1
    rw [abs_neg, abs_le]
    constructor
    · have := Real.log_le_log hc0 h1; linarith [neg_abs_le (Real.log c), abs_nonneg (Real.log (1 / (1 + 2 * s)))]
    · have := Real.log_le_log hqx h2
      linarith [le_abs_self (Real.log (1 / (1 + 2 * s))), abs_nonneg (Real.log c)]
  have hint : Integrable (fun x => p x * Real.log (p x / q x)) volume := by
    rw [hfun, integrable_indicator_iff measurableSet_Icc]
    refine Measure.integrableOn_of_bounded (M := |Real.log c| + |Real.log (1 / (1 + 2 * s))|)
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) hqm.log.neg.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs]; exact hlogb x hx
  have hQ : G ∗ unifR J = volume.withDensity fun y => ENNReal.ofReal (q y) := by
    rw [conv_unifR_eq G hJm hJ0]; congr 1; funext y; rw [ENNReal.ofReal_toReal (hjd_ne y)]
  have hkl := klRef_withDensity volume hp hqm hp0 hq0 hpq hint
  rw [← boxU_eq_withDensity, ← hQ] at hkl
  refine (iInf₂_le (unifR J) (show IsProbabilityMeasure (unifR J) from inferInstance)).trans ?_
  change klRef boxU (G ∗ unifR J) ≤ _
  rw [hkl, EReal.coe_le_coe_iff, hfun, integral_indicator measurableSet_Icc]
  calc ∫ x in box, -Real.log (q x) ≤ ∫ x in box, -Real.log c := by
        refine setIntegral_mono_on ((integrable_indicator_iff measurableSet_Icc).1 (hfun ▸ hint))
          (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)) measurableSet_Icc
          fun x hx => ?_
        have := Real.log_le_log hc0 (hqmin x hx); linarith
    _ = -Real.log c := by
        rw [setIntegral_const]; simp only [box, Measure.real, Real.volume_Icc]; norm_num

/-- `prop:tax`(a), the limit `ϰ(β) → 0` as `β ↓ 0`. -/
theorem tax_a_lim : Claims.tax_a_lim := by
  have hf : Tendsto (fun β : ℝ => ((-Real.log ((1 - β) / (1 + 2 * √β)) : ℝ) : EReal)) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun β : ℝ => -Real.log ((1 - β) / (1 + 2 * √β))) 0 := by
      refine (ContinuousAt.log ?_ (by norm_num)).neg
      exact ((continuous_const.sub continuous_id).div (continuous_const.add
        (continuous_const.mul Real.continuous_sqrt)) fun x =>
          (by have h := Real.sqrt_nonneg x; linarith : (0 : ℝ) < 1 + 2 * √x).ne').continuousAt
    have key : Tendsto (fun β : ℝ => ((-Real.log ((1 - β) / (1 + 2 * √β)) : ℝ) : EReal)) (𝓝 0)
        (𝓝 ((-Real.log ((1 - 0) / (1 + 2 * √(0 : ℝ))) : ℝ) : EReal)) :=
      (continuous_coe_real_ereal.tendsto _).comp hc.tendsto
    have h00 : ((-Real.log ((1 - 0) / (1 + 2 * √(0 : ℝ))) : ℝ) : EReal) = 0 := by simp
    rw [h00] at key
    exact key.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hf ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with β hβ
    exact (tax_a_bound β hβ).1
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with β hβ
    exact varkappa_le_smooth hβ.1 hβ.2

end Limit

end StatFormal.Wave21a
