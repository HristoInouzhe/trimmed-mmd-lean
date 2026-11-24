import StatFormal.Lib.GaussianEOT.OT

/-!
# The static Schrödinger problem relative to `R₀₁ = μ(dx) N(x, ε)(dy)` versus Tau Ceti's entropic transport

For `ε > 0`, `μ, ν ∈ 𝒫₂(ℝ)` and `ν = q · Leb` with `log q ∈ L¹(ν)`:
* `refP_eq_withDensity`: `R₀₁ = (μ ⊗ Leb).withDensity (p_ε(y − x))`; `prod_eq_withDensity_refP`:
  `μ ⊗ ν = R₀₁.withDensity (q(y)/p_ε(y − x))`.
* `ac_refP_iff`: a coupling is `≪ R₀₁` iff it is `≪ μ ⊗ ν`.
* `klDiv_refP`: `KL(π ‖ R₀₁) < ∞ ⟺ KL(π ‖ μ ⊗ ν) < ∞` and then
  `ε KL(π ‖ R₀₁) = ∫ ½(x−y)² dπ + ε KL(π ‖ μ ⊗ ν) + ε(∫ log q dν + ½ log(2πε))`.
* `static_iff_entropic`: the minimisers of `KL(· ‖ R₀₁)` over `Π(μ,ν)` (finite value) are exactly the couplings
  attaining `entropicTransportCost (½(x−y)²) ε μ ν`, which is finite.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set InformationTheory TauCeti
open scoped ENNReal NNReal

set_option linter.style.longLine false

namespace StatFormal.SchrodingerPath

open StatFormal.Foundations.GaussianEOT (integrable_fst_of_isCoupling integrable_snd_of_isCoupling
  integral_snd_of_isCoupling)

/-- `R₀₁ = Law(x, x + √ε G)`, `x ∼ μ`. -/
def refP (ε : ℝ) (μ : Measure ℝ) : Measure (ℝ × ℝ) :=
  (μ.prod (gaussianReal 0 ε.toNNReal)).map (fun p => (p.1, p.1 + p.2))

/-- The density `p_ε(y − x)` of `R₀₁` against `μ ⊗ Leb`. -/
def refDens (ε : ℝ) (z : ℝ × ℝ) : ℝ≥0∞ := ENNReal.ofReal (gaussianPDFReal 0 ε.toNNReal (z.2 - z.1))

instance isProbabilityMeasure_refP (ε : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (refP ε μ) := by
  unfold refP; infer_instance

lemma measurable_refDens (ε : ℝ) : Measurable (refDens ε) := by
  unfold refDens
  exact ENNReal.measurable_ofReal.comp ((measurable_gaussianPDFReal 0 _).comp (by fun_prop))

theorem refP_eq_withDensity {ε : ℝ} (hε : 0 < ε) (μ : Measure ℝ) [SFinite μ] :
    refP ε μ = (μ.prod volume).withDensity (refDens ε) := by
  have hv : ε.toNNReal ≠ 0 := by simpa using hε
  have hk : Measurable (fun p : ℝ × ℝ => (p.1, p.1 + p.2)) := by fun_prop
  ext A hA
  rw [refP, Measure.map_apply hk hA, Measure.prod_apply (hk hA), withDensity_apply _ hA,
    ← lintegral_indicator hA, lintegral_prod _ ((measurable_refDens ε).indicator hA).aemeasurable]
  refine lintegral_congr fun x => ?_
  rw [gaussianReal_of_var_ne_zero 0 hv, withDensity_apply _ (measurable_prodMk_left (hk hA)),
    ← lintegral_indicator (measurable_prodMk_left (hk hA))]
  rw [← lintegral_add_left_eq_self (fun y => A.indicator (refDens ε) (x, y)) x]
  refine lintegral_congr fun s => ?_
  by_cases hs : (x, x + s) ∈ A
  · have hs' : s ∈ Prod.mk x ⁻¹' ((fun p : ℝ × ℝ => (p.1, p.1 + p.2)) ⁻¹' A) := hs
    rw [indicator_of_mem hs', indicator_of_mem hs]
    simp [refDens, gaussianPDF]
  · have hs' : s ∉ Prod.mk x ⁻¹' ((fun p : ℝ × ℝ => (p.1, p.1 + p.2)) ⁻¹' A) := hs
    rw [indicator_of_notMem hs', indicator_of_notMem hs]

variable {ε : ℝ} {μ ν : Measure ℝ} {q : ℝ → ℝ}

/-- The density `q(y)/p_ε(y − x)` of `μ ⊗ ν` against `R₀₁`. -/
def prodDens (ε : ℝ) (q : ℝ → ℝ) (z : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (q z.2 / gaussianPDFReal 0 ε.toNNReal (z.2 - z.1))

lemma measurable_prodDens (ε : ℝ) (hq : Measurable q) : Measurable (prodDens ε q) := by
  unfold prodDens
  exact ENNReal.measurable_ofReal.comp ((hq.comp measurable_snd).div
    ((measurable_gaussianPDFReal 0 _).comp (by fun_prop)))

lemma prod_eq_withDensity_vol [SFinite μ] (hν : ν = volume.withDensity (fun y => ENNReal.ofReal (q y)))
    (hq : Measurable q) :
    μ.prod ν = (μ.prod volume).withDensity (fun z => ENNReal.ofReal (q z.2)) := by
  rw [hν, prod_withDensity_right (g := fun y => ENNReal.ofReal (q y)) (ENNReal.measurable_ofReal.comp hq)]

theorem prod_eq_withDensity_refP (hε : 0 < ε) [SFinite μ]
    (hν : ν = volume.withDensity (fun y => ENNReal.ofReal (q y))) (hq : Measurable q) (_hq0 : ∀ y, 0 ≤ q y) :
    μ.prod ν = (refP ε μ).withDensity (prodDens ε q) := by
  have hv : ε.toNNReal ≠ 0 := by simpa using hε
  rw [refP_eq_withDensity hε, ← withDensity_mul _ (measurable_refDens ε) (measurable_prodDens ε hq),
    prod_eq_withDensity_vol hν hq]
  congr 1
  funext z
  have hp := gaussianPDFReal_pos 0 ε.toNNReal (z.2 - z.1) hv
  simp only [Pi.mul_apply, refDens, prodDens]
  rw [← ENNReal.ofReal_mul hp.le, mul_div_cancel₀ _ hp.ne']

lemma ae_pos_of_coupling (hν : ν = volume.withDensity (fun y => ENNReal.ofReal (q y))) (hq : Measurable q)
    {π : Measure (ℝ × ℝ)} (hπ : IsCoupling π μ ν) : ∀ᵐ z ∂π, 0 < q z.2 := by
  have h1 : ∀ᵐ y ∂ν, 0 < q y := by
    rw [hν, ae_withDensity_iff (f := fun y => ENNReal.ofReal (q y)) (ENNReal.measurable_ofReal.comp hq)]
    exact Filter.Eventually.of_forall fun y hy => by
      by_contra h; exact hy (ENNReal.ofReal_eq_zero.2 (not_lt.1 h))
  have h2 : π.map Prod.snd = ν := hπ.snd_eq
  rw [← h2] at h1
  exact ae_of_ae_map measurable_snd.aemeasurable h1

theorem ac_refP_iff (hε : 0 < ε) [IsProbabilityMeasure μ]
    (hν : ν = volume.withDensity (fun y => ENNReal.ofReal (q y))) (hq : Measurable q) (hq0 : ∀ y, 0 ≤ q y)
    {π : Measure (ℝ × ℝ)} (hπ : IsCoupling π μ ν) : π ≪ refP ε μ ↔ π ≪ μ.prod ν := by
  constructor
  · intro h
    refine Measure.AbsolutelyContinuous.mk fun A hA h0 => ?_
    rw [prod_eq_withDensity_vol hν hq, withDensity_apply _ hA] at h0
    have h0' := (lintegral_eq_zero_iff (f := fun z : ℝ × ℝ => ENNReal.ofReal (q z.2))
      (μ := (μ.prod volume).restrict A) (ENNReal.measurable_ofReal.comp (hq.comp measurable_snd))).1 h0
    have h1 : ∀ᵐ z ∂(μ.prod volume), z ∈ A → ENNReal.ofReal (q z.2) = 0 := (ae_restrict_iff' hA).1 h0'
    have hac : refP ε μ ≪ μ.prod volume := by
      rw [refP_eq_withDensity hε]; exact withDensity_absolutelyContinuous _ _
    have h2 : ∀ᵐ z ∂π, z ∉ A := by
      filter_upwards [h.ae_le (hac.ae_le h1), ae_pos_of_coupling hν hq hπ] with z h1 h2 hzA
      exact (ENNReal.ofReal_eq_zero.1 (h1 hzA)).not_gt h2
    exact measure_eq_zero_iff_ae_notMem.2 h2
  · intro h
    refine h.trans ?_
    rw [prod_eq_withDensity_refP hε hν hq hq0]
    exact withDensity_absolutelyContinuous _ _

lemma log_gaussPDF_zero (hε : 0 < ε) (u : ℝ) :
    Real.log (gaussianPDFReal 0 ε.toNNReal u) = -(Real.log (2 * Real.pi * ε) / 2) - u ^ 2 / (2 * ε) := by
  have hv : (ε.toNNReal : ℝ) = ε := Real.coe_toNNReal _ hε.le
  rw [gaussianPDFReal, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp, Real.log_inv, hv,
    Real.log_sqrt (by positivity)]
  ring

/-- The log-likelihood ratios against `R₀₁` and against `μ ⊗ ν` differ by an explicit function. -/
theorem llr_refP (hε : 0 < ε) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : ν = volume.withDensity (fun y => ENNReal.ofReal (q y))) (hq : Measurable q) (hq0 : ∀ y, 0 ≤ q y)
    {π : Measure (ℝ × ℝ)} [IsFiniteMeasure π] (hπ : IsCoupling π μ ν) (hac : π ≪ μ.prod ν) :
    llr π (refP ε μ) =ᵐ[π] fun z => llr π (μ.prod ν) z + (Real.log (q z.2) + Real.log (2 * Real.pi * ε) / 2) +
      (z.2 - z.1) ^ 2 / (2 * ε) := by
  have hv : ε.toNNReal ≠ 0 := by simpa using hε
  have hPN := prod_eq_withDensity_refP (μ := μ) hε hν hq hq0
  have hacR : π ≪ refP ε μ := (ac_refP_iff hε hν hq hq0 hπ).2 hac
  have hD : (μ.prod ν).rnDeriv (refP ε μ) =ᵐ[refP ε μ] prodDens ε q := by
    rw [hPN]; exact Measure.rnDeriv_withDensity _ (measurable_prodDens ε hq)
  have hmul := Measure.rnDeriv_mul_rnDeriv (κ := refP ε μ) hac
  filter_upwards [hacR.ae_le hmul, hacR.ae_le hD, Measure.rnDeriv_pos hac,
    hac.ae_le (Measure.rnDeriv_ne_top π (μ.prod ν)), ae_pos_of_coupling hν hq hπ] with z h1 h2 h3 h4 h5
  have hp := gaussianPDFReal_pos 0 ε.toNNReal (z.2 - z.1) hv
  simp only [llr_def]
  rw [← h1, Pi.mul_apply, h2, ENNReal.toReal_mul, prodDens, ENNReal.toReal_ofReal (div_nonneg (hq0 _) hp.le),
    Real.log_mul (ENNReal.toReal_pos h3.ne' h4).ne' (div_pos h5 hp).ne', Real.log_div h5.ne' hp.ne',
    log_gaussPDF_zero hε]
  ring

lemma integrable_sq_sub_of_coupling {π : Measure (ℝ × ℝ)} (hπ : IsCoupling π μ ν)
    (hμ2 : Integrable (fun x : ℝ => x ^ 2) μ) (hν2 : Integrable (fun y : ℝ => y ^ 2) ν) :
    Integrable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2) π := by
  have h1 := integrable_fst_of_isCoupling hπ hμ2
  have h2 := integrable_snd_of_isCoupling hπ hν2
  refine Integrable.mono' ((h1.add h2).const_mul 2) (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  show (z.1 - z.2) ^ 2 ≤ 2 * (z.1 ^ 2 + z.2 ^ 2)
  nlinarith [sq_nonneg (z.1 + z.2)]

/-- `lem:equiv`, static half. -/
theorem klDiv_refP (hε : 0 < ε) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : ν = volume.withDensity (fun y => ENNReal.ofReal (q y))) (hq : Measurable q) (hq0 : ∀ y, 0 ≤ q y)
    (hlog : Integrable (fun y => Real.log (q y)) ν) (hμ2 : Integrable (fun x : ℝ => x ^ 2) μ)
    (hν2 : Integrable (fun y : ℝ => y ^ 2) ν) {π : Measure (ℝ × ℝ)} (hπ : IsCoupling π μ ν) :
    (klDiv π (refP ε μ) ≠ ∞ ↔ klDiv π (μ.prod ν) ≠ ∞) ∧
      (klDiv π (μ.prod ν) ≠ ∞ →
        ε * (klDiv π (refP ε μ)).toReal = ∫ z, (z.1 - z.2) ^ 2 / 2 ∂π + ε * (klDiv π (μ.prod ν)).toReal +
          ε * (∫ y, Real.log (q y) ∂ν + Real.log (2 * Real.pi * ε) / 2)) := by
  have hπP : IsProbabilityMeasure π := by
    have h : π.map Prod.fst = μ := hπ.fst_eq
    have : IsProbabilityMeasure (π.map Prod.fst) := by rw [h]; infer_instance
    exact Measure.isProbabilityMeasure_of_map measurable_fst.aemeasurable
  have hsq := integrable_sq_sub_of_coupling hπ hμ2 hν2
  have hlogπ : Integrable (fun z : ℝ × ℝ => Real.log (q z.2)) π := integrable_snd_of_isCoupling hπ hlog
  have hh : Integrable (fun z : ℝ × ℝ => (Real.log (q z.2) + Real.log (2 * Real.pi * ε) / 2) +
      (z.2 - z.1) ^ 2 / (2 * ε)) π := by
    refine (hlogπ.add (integrable_const _)).add ?_
    have : (fun z : ℝ × ℝ => (z.2 - z.1) ^ 2 / (2 * ε)) = fun z => (z.1 - z.2) ^ 2 / (2 * ε) := by
      funext z; ring
    rw [this]; exact hsq.div_const _
  have key : ∀ hac : π ≪ μ.prod ν,
      (Integrable (llr π (refP ε μ)) π ↔ Integrable (llr π (μ.prod ν)) π) := by
    intro hac
    have hl := llr_refP hε hν hq hq0 hπ hac
    rw [integrable_congr hl]
    constructor
    · intro h
      have := h.sub hh
      refine this.congr (Filter.Eventually.of_forall fun z => ?_)
      simp only [Pi.sub_apply]; ring
    · intro h
      exact (h.add hh).congr (Filter.Eventually.of_forall fun z => by simp only [Pi.add_apply]; ring)
  have hiff : klDiv π (refP ε μ) ≠ ∞ ↔ klDiv π (μ.prod ν) ≠ ∞ := by
    rw [klDiv_ne_top_iff, klDiv_ne_top_iff, ac_refP_iff hε hν hq hq0 hπ]
    constructor
    · rintro ⟨hac, hi⟩; exact ⟨hac, (key hac).1 hi⟩
    · rintro ⟨hac, hi⟩; exact ⟨hac, (key hac).2 hi⟩
  refine ⟨hiff, fun hfin => ?_⟩
  obtain ⟨hac, hi⟩ := klDiv_ne_top_iff.1 hfin
  have hacR : π ≪ refP ε μ := (ac_refP_iff hε hν hq hq0 hπ).2 hac
  have hiR : Integrable (llr π (refP ε μ)) π := (key hac).2 hi
  have hsq' : Integrable (fun z : ℝ × ℝ => (z.2 - z.1) ^ 2 / (2 * ε)) π := by
    have : (fun z : ℝ × ℝ => (z.2 - z.1) ^ 2 / (2 * ε)) = fun z => (z.1 - z.2) ^ 2 / (2 * ε) := by
      funext z; ring
    rw [this]; exact hsq.div_const _
  have hlc : Integrable (fun z : ℝ × ℝ => Real.log (q z.2) + Real.log (2 * Real.pi * ε) / 2) π :=
    hlogπ.add (integrable_const _)
  have hI1 : ∫ z, (llr π (μ.prod ν) z + (Real.log (q z.2) + Real.log (2 * Real.pi * ε) / 2) +
      (z.2 - z.1) ^ 2 / (2 * ε)) ∂π =
      ∫ z, (llr π (μ.prod ν) z + (Real.log (q z.2) + Real.log (2 * Real.pi * ε) / 2)) ∂π +
        ∫ z, (z.2 - z.1) ^ 2 / (2 * ε) ∂π :=
    integral_add (f := fun z => llr π (μ.prod ν) z + (Real.log (q z.2) + Real.log (2 * Real.pi * ε) / 2))
      (g := fun z : ℝ × ℝ => (z.2 - z.1) ^ 2 / (2 * ε)) (hi.add hlc) hsq'
  have hI2 : ∫ z, (llr π (μ.prod ν) z + (Real.log (q z.2) + Real.log (2 * Real.pi * ε) / 2)) ∂π =
      ∫ z, llr π (μ.prod ν) z ∂π + ∫ z, (Real.log (q z.2) + Real.log (2 * Real.pi * ε) / 2) ∂π :=
    integral_add (f := llr π (μ.prod ν))
      (g := fun z : ℝ × ℝ => Real.log (q z.2) + Real.log (2 * Real.pi * ε) / 2) hi hlc
  have hI3 : ∫ z, (Real.log (q z.2) + Real.log (2 * Real.pi * ε) / 2) ∂π =
      ∫ y, Real.log (q y) ∂ν + Real.log (2 * Real.pi * ε) / 2 := by
    rw [integral_add (f := fun z : ℝ × ℝ => Real.log (q z.2)) hlogπ (integrable_const _),
      integral_snd_of_isCoupling hπ hlog, integral_const]
    simp
  have e1 : ∫ z, (z.2 - z.1) ^ 2 / (2 * ε) ∂π = (∫ z, (z.1 - z.2) ^ 2 / 2 ∂π) / ε := by
    rw [integral_div, integral_div]
    have : ∫ z, (z.2 - z.1) ^ 2 ∂π = ∫ z, (z.1 - z.2) ^ 2 ∂π := by
      congr 1; funext z; ring
    rw [this]; field_simp
  rw [toReal_klDiv hacR hiR, toReal_klDiv hac hi, integral_congr_ae (llr_refP hε hν hq hq0 hπ hac)]
  simp only [probReal_univ, add_sub_cancel_right]
  rw [hI1, hI2, hI3, e1]
  field_simp
  ring

/-! ### Static Schrödinger minimisers = entropic optimal plans -/

/-- The quadratic cost `½(x − y)²` (`[0,∞]`-valued, as in the frozen Wave P3b `sqCost`). -/
def halfSq (z : ℝ × ℝ) : ℝ≥0∞ := ENNReal.ofReal ((z.1 - z.2) ^ 2 / 2)

lemma lintegral_halfSq {π : Measure (ℝ × ℝ)} (h : Integrable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2) π) :
    ∫⁻ z, halfSq z ∂π = ENNReal.ofReal (∫ z, (z.1 - z.2) ^ 2 / 2 ∂π) :=
  (ofReal_integral_eq_lintegral_ofReal (h.div_const 2)
    (Filter.Eventually.of_forall fun z => by positivity)).symm

theorem static_iff_entropic (hε : 0 < ε) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : ν = volume.withDensity (fun y => ENNReal.ofReal (q y))) (hq : Measurable q) (hq0 : ∀ y, 0 ≤ q y)
    (hlog : Integrable (fun y => Real.log (q y)) ν) (hμ2 : Integrable (fun x : ℝ => x ^ 2) μ)
    (hν2 : Integrable (fun y : ℝ => y ^ 2) ν) :
    entropicTransportCost halfSq ε.toNNReal μ ν ≠ ∞ ∧
      ∀ π : Measure (ℝ × ℝ),
        (IsCoupling π μ ν ∧ klDiv π (refP ε μ) ≠ ∞ ∧
            ∀ π' : Measure (ℝ × ℝ), IsCoupling π' μ ν → klDiv π (refP ε μ) ≤ klDiv π' (refP ε μ)) ↔
          (IsCoupling π μ ν ∧
            ∫⁻ z, halfSq z ∂π + (ε.toNNReal : ℝ≥0∞) * klDiv π (μ.prod ν) =
              entropicTransportCost halfSq ε.toNNReal μ ν) := by
  set F : Measure (ℝ × ℝ) → ℝ≥0∞ := fun π => ∫⁻ z, halfSq z ∂π + (ε.toNNReal : ℝ≥0∞) * klDiv π (μ.prod ν)
  have hεc : ((ε.toNNReal : ℝ≥0∞)) ≠ 0 := by simpa using hε
  have hεt : ((ε.toNNReal : ℝ≥0∞)) ≠ ∞ := ENNReal.coe_ne_top
  have hεr : ((ε.toNNReal : ℝ≥0∞)).toReal = ε := by simp [hε.le]
  -- finiteness
  have hfin : ∀ π, IsCoupling π μ ν → (F π ≠ ∞ ↔ klDiv π (refP ε μ) ≠ ∞) := by
    intro π hπ
    have hc : ∫⁻ z, halfSq z ∂π ≠ ∞ := by
      rw [lintegral_halfSq (integrable_sq_sub_of_coupling hπ hμ2 hν2)]; exact ENNReal.ofReal_ne_top
    rw [(klDiv_refP hε hν hq hq0 hlog hμ2 hν2 hπ).1]
    simp [F, ENNReal.add_eq_top, hc, ENNReal.mul_eq_top, hεc, hεt]
  -- value
  set K := ∫ y, Real.log (q y) ∂ν + Real.log (2 * Real.pi * ε) / 2
  have hval : ∀ π, IsCoupling π μ ν → F π ≠ ∞ → (F π).toReal = ε * (klDiv π (refP ε μ)).toReal - ε * K := by
    intro π hπ hF
    have hk : klDiv π (μ.prod ν) ≠ ∞ := by
      rw [← (klDiv_refP hε hν hq hq0 hlog hμ2 hν2 hπ).1]; exact (hfin π hπ).1 hF
    have hc : ∫⁻ z, halfSq z ∂π ≠ ∞ := by
      rw [lintegral_halfSq (integrable_sq_sub_of_coupling hπ hμ2 hν2)]; exact ENNReal.ofReal_ne_top
    rw [(klDiv_refP hε hν hq hq0 hlog hμ2 hν2 hπ).2 hk]
    simp only [F]
    rw [ENNReal.toReal_add hc (ENNReal.mul_ne_top hεt hk), ENNReal.toReal_mul, hεr,
      lintegral_halfSq (integrable_sq_sub_of_coupling hπ hμ2 hν2),
      ENNReal.toReal_ofReal (integral_nonneg fun z => by positivity)]
    ring
  -- order
  have hord : ∀ π π', IsCoupling π μ ν → IsCoupling π' μ ν →
      (F π ≤ F π' ↔ klDiv π (refP ε μ) ≤ klDiv π' (refP ε μ)) := by
    intro π π' hπ hπ'
    by_cases h' : F π' = ∞
    · have : klDiv π' (refP ε μ) = ∞ := by
        by_contra hk; exact ((hfin π' hπ').2 hk) h'
      rw [h', this]; simp
    · have hk' : klDiv π' (refP ε μ) ≠ ∞ := (hfin π' hπ').1 h'
      by_cases h : F π = ∞
      · have : klDiv π (refP ε μ) = ∞ := by
          by_contra hk; exact ((hfin π hπ).2 hk) h
        rw [h, this, top_le_iff, top_le_iff]
        exact ⟨fun e => (h' e).elim, fun e => (hk' e).elim⟩
      · have hk : klDiv π (refP ε μ) ≠ ∞ := (hfin π hπ).1 h
        rw [← ENNReal.toReal_le_toReal h h', hval π hπ h, hval π' hπ' h', ← ENNReal.toReal_le_toReal hk hk']
        constructor
        · intro hle; nlinarith
        · intro hle; nlinarith
  have hETC : entropicTransportCost halfSq ε.toNNReal μ ν = ⨅ (π : Measure (ℝ × ℝ)) (_ : IsCoupling π μ ν), F π :=
    entropicTransportCost_def
  have hprod : IsCoupling (μ.prod ν) μ ν := ⟨Measure.fst_prod, Measure.snd_prod⟩
  have hne : entropicTransportCost halfSq ε.toNNReal μ ν ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (hETC ▸ iInf₂_le (μ.prod ν) hprod)
    have : klDiv (μ.prod ν) (μ.prod ν) ≠ ∞ := by rw [klDiv_self]; exact ENNReal.zero_ne_top
    exact (hfin _ hprod).2 ((klDiv_refP hε hν hq hq0 hlog hμ2 hν2 hprod).1.2 this)
  refine ⟨hne, fun π => ⟨?_, ?_⟩⟩
  · rintro ⟨hπ, hfinπ, hmin⟩
    refine ⟨hπ, le_antisymm ?_ (hETC ▸ iInf₂_le π hπ)⟩
    rw [hETC]
    exact le_iInf₂ fun π' hπ' => (hord π π' hπ hπ').2 (hmin π' hπ')
  · rintro ⟨hπ, hEq⟩
    have hF : F π ≠ ∞ := by change F π ≠ ∞; rw [show F π = _ from hEq]; exact hne
    refine ⟨hπ, (hfin π hπ).1 hF, fun π' hπ' => (hord π π' hπ hπ').1 ?_⟩
    change F π ≤ F π'
    rw [show F π = _ from hEq, hETC]
    exact iInf₂_le π' hπ'

end StatFormal.SchrodingerPath
