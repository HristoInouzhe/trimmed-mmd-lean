import StatFormal.Lib.SchrodingerPathD.Gauss
import StatFormal.Lib.SchrodingerPath.Static
import StatFormal.Lib.GaussianEOTd.Measure

/-!
# The static Schrödinger problem relative to `R₀₁ = μ(dx) N(x, εI)(dy)` on `ℝᵈ` versus Tau Ceti's entropic transport

For `ε > 0`, `μ, ν ∈ 𝒫₂(ℝᵈ)` and `ν = q · Leb` with `log q ∈ L¹(ν)`:
* `isoG_eq_withDensity`: `N(0, εI) = Leb.withDensity p_ε`, `p_ε(u) = ∏ᵢ φ_ε(uᵢ)`, `log p_ε(u) = −(d/2) log(2πε) − ‖u‖²/(2ε)`.
* `refPD_eq_withDensity`: `R₀₁ = (μ ⊗ Leb).withDensity (p_ε(y − x))`; `prod_eq_withDensity_refPD`.
* `klDiv_refPD`: `KL(π ‖ R₀₁) < ∞ ⟺ KL(π ‖ μ ⊗ ν) < ∞` and then
  `ε KL(π ‖ R₀₁) = ∫ ½‖x−y‖² dπ + ε KL(π ‖ μ ⊗ ν) + ε(∫ log q dν + (d/2) log(2πε))`.
* `static_iff_entropicD`: static minimisers (finite value) = couplings attaining `entropicTransportCost (½‖x−y‖²) ε μ ν`,
  which is finite.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set InformationTheory TauCeti
open scoped ENNReal NNReal

set_option linter.style.longLine false

namespace StatFormal.SchrodingerPathD

local notation "E" d => EuclideanSpace ℝ (Fin d)

variable {d : ℕ}

/-! ### The Lebesgue density of `N(0, εI)` -/

/-- `p_ε(u) = ∏ᵢ φ_ε(uᵢ)`. -/
def gdens (d : ℕ) (ε : ℝ) (u : E d) : ℝ := ∏ i, gaussianPDFReal 0 ε.toNNReal (u i)

lemma gdens_pos {ε : ℝ} (hε : 0 < ε) (u : E d) : 0 < gdens d ε u := by
  have hv : ε.toNNReal ≠ 0 := by simpa using hε
  exact Finset.prod_pos fun i _ => gaussianPDFReal_pos 0 _ _ hv

lemma measurable_gdens (ε : ℝ) : Measurable (gdens d ε) := by
  unfold gdens
  exact Finset.measurable_prod _ fun i _ => (measurable_gaussianPDFReal 0 _).comp (by fun_prop)

lemma log_gdens {ε : ℝ} (hε : 0 < ε) (u : E d) :
    Real.log (gdens d ε u) = -(d * Real.log (2 * Real.pi * ε) / 2) - ‖u‖ ^ 2 / (2 * ε) := by
  have hv : ε.toNNReal ≠ 0 := by simpa using hε
  rw [gdens, Real.log_prod (fun i _ => (gaussianPDFReal_pos 0 _ _ hv).ne')]
  simp_rw [StatFormal.SchrodingerPath.log_gaussPDF_zero hε]
  rw [Finset.sum_sub_distrib, EuclideanSpace.real_norm_sq_eq, Finset.sum_div]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

lemma isoG_eq_pi {s : ℝ} (hs : 0 ≤ s) :
    isoG d s = (Measure.pi fun _ : Fin d => gaussianReal 0 s.toNNReal).map (WithLp.toLp 2) := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_isoG, charFun_pi]
  simp_rw [charFun_gaussianReal]
  rw [← Complex.exp_sum]
  congr 1
  rw [show ((‖t‖ : ℂ)) ^ 2 = ((‖t‖ ^ 2 : ℝ) : ℂ) by push_cast; rfl, EuclideanSpace.real_norm_sq_eq]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp
  ring

lemma pi_gauss_withDensity {v : ℝ≥0} (hv : v ≠ 0) :
    Measure.pi (fun _ : Fin d => gaussianReal 0 v) =
      (Measure.pi fun _ : Fin d => (volume : Measure ℝ)).withDensity
        (fun x => ENNReal.ofReal (∏ i, gaussianPDFReal 0 v (x i))) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi,
    ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_fintype_prod_eq_prod (f := fun _ x => gaussianPDFReal 0 v x)
        (μ := fun i => (volume : Measure ℝ).restrict (s i)),
      ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg fun x => gaussianPDFReal_nonneg 0 v x)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [gaussianReal_apply_eq_integral 0 hv]
  · exact Integrable.fintype_prod (f := fun _ x => gaussianPDFReal 0 v x)
      (μ := fun i => (volume : Measure ℝ).restrict (s i)) (fun i => (integrable_gaussianPDFReal 0 v).restrict)
  · exact Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 v _

theorem isoG_eq_withDensity {ε : ℝ} (hε : 0 < ε) :
    isoG d ε = volume.withDensity (fun u => ENNReal.ofReal (gdens d ε u)) := by
  have hv : ε.toNNReal ≠ 0 := by simpa using hε
  rw [isoG_eq_pi hε.le, pi_gauss_withDensity hv, ← MeasurableEquiv.coe_toLp,
    StatFormal.Foundations.GaussianEOTd.map_withDensity_equiv, MeasurableEquiv.coe_toLp, ← volume_pi,
    (PiLp.volume_preserving_toLp (Fin d)).map_eq]
  rfl

/-! ### `R₀₁` and `μ ⊗ ν` as densities -/

/-- `R₀₁ = Law(x, x + √ε G)`, `x ∼ μ`, on `ℝᵈ`. -/
def refPD (ε : ℝ) (μ : Measure (E d)) : Measure ((E d) × (E d)) :=
  (μ.prod (isoG d ε)).map (fun p => (p.1, p.1 + p.2))

/-- The density `p_ε(y − x)` of `R₀₁` against `μ ⊗ Leb`. -/
def refDensD (ε : ℝ) (z : (E d) × (E d)) : ℝ≥0∞ := ENNReal.ofReal (gdens d ε (z.2 - z.1))

instance isProbabilityMeasure_refPD (ε : ℝ) (μ : Measure (E d)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (refPD ε μ) := by
  unfold refPD; infer_instance

lemma measurable_refDensD (ε : ℝ) : Measurable (refDensD (d := d) ε) := by
  unfold refDensD
  exact ENNReal.measurable_ofReal.comp ((measurable_gdens ε).comp (by fun_prop))

theorem refPD_eq_withDensity {ε : ℝ} (hε : 0 < ε) (μ : Measure (E d)) [SFinite μ] :
    refPD ε μ = (μ.prod volume).withDensity (refDensD ε) := by
  have hk : Measurable (fun p : (E d) × (E d) => (p.1, p.1 + p.2)) := by fun_prop
  ext A hA
  rw [refPD, Measure.map_apply hk hA, Measure.prod_apply (hk hA), withDensity_apply _ hA,
    ← lintegral_indicator hA, lintegral_prod _ ((measurable_refDensD ε).indicator hA).aemeasurable]
  refine lintegral_congr fun x => ?_
  rw [isoG_eq_withDensity hε, withDensity_apply _ (measurable_prodMk_left (hk hA)),
    ← lintegral_indicator (measurable_prodMk_left (hk hA))]
  rw [← lintegral_add_left_eq_self (fun y => A.indicator (refDensD ε) (x, y)) x]
  refine lintegral_congr fun s => ?_
  by_cases hs : (x, x + s) ∈ A
  · have hs' : s ∈ Prod.mk x ⁻¹' ((fun p : (E d) × (E d) => (p.1, p.1 + p.2)) ⁻¹' A) := hs
    rw [indicator_of_mem hs', indicator_of_mem hs]
    simp [refDensD]
  · have hs' : s ∉ Prod.mk x ⁻¹' ((fun p : (E d) × (E d) => (p.1, p.1 + p.2)) ⁻¹' A) := hs
    rw [indicator_of_notMem hs', indicator_of_notMem hs]

variable {ε : ℝ} {μ ν : Measure (E d)} {q : (E d) → ℝ}

/-- The density `q(y)/p_ε(y − x)` of `μ ⊗ ν` against `R₀₁`. -/
def prodDensD (ε : ℝ) (q : (E d) → ℝ) (z : (E d) × (E d)) : ℝ≥0∞ :=
  ENNReal.ofReal (q z.2 / gdens d ε (z.2 - z.1))

lemma measurable_prodDensD (ε : ℝ) (hq : Measurable q) : Measurable (prodDensD ε q) := by
  unfold prodDensD
  exact ENNReal.measurable_ofReal.comp ((hq.comp measurable_snd).div ((measurable_gdens ε).comp (by fun_prop)))

lemma prod_eq_withDensity_volD [SFinite μ] (hν : ν = volume.withDensity (fun y => ENNReal.ofReal (q y)))
    (hq : Measurable q) :
    μ.prod ν = (μ.prod volume).withDensity (fun z => ENNReal.ofReal (q z.2)) := by
  rw [hν, prod_withDensity_right (g := fun y => ENNReal.ofReal (q y)) (ENNReal.measurable_ofReal.comp hq)]

theorem prod_eq_withDensity_refPD (hε : 0 < ε) [SFinite μ]
    (hν : ν = volume.withDensity (fun y => ENNReal.ofReal (q y))) (hq : Measurable q) :
    μ.prod ν = (refPD ε μ).withDensity (prodDensD ε q) := by
  rw [refPD_eq_withDensity hε, ← withDensity_mul _ (measurable_refDensD ε) (measurable_prodDensD ε hq),
    prod_eq_withDensity_volD hν hq]
  congr 1
  funext z
  have hp := gdens_pos hε (z.2 - z.1)
  simp only [Pi.mul_apply, refDensD, prodDensD]
  rw [← ENNReal.ofReal_mul hp.le, mul_div_cancel₀ _ hp.ne']

lemma ae_pos_of_couplingD (hν : ν = volume.withDensity (fun y => ENNReal.ofReal (q y))) (hq : Measurable q)
    {π : Measure ((E d) × (E d))} (hπ : IsCoupling π μ ν) : ∀ᵐ z ∂π, 0 < q z.2 := by
  have h1 : ∀ᵐ y ∂ν, 0 < q y := by
    rw [hν, ae_withDensity_iff (f := fun y => ENNReal.ofReal (q y)) (ENNReal.measurable_ofReal.comp hq)]
    exact Filter.Eventually.of_forall fun y hy => by
      by_contra h; exact hy (ENNReal.ofReal_eq_zero.2 (not_lt.1 h))
  have h2 : π.map Prod.snd = ν := hπ.snd_eq
  rw [← h2] at h1
  exact ae_of_ae_map measurable_snd.aemeasurable h1

theorem ac_refPD_iff (hε : 0 < ε) [IsProbabilityMeasure μ]
    (hν : ν = volume.withDensity (fun y => ENNReal.ofReal (q y))) (hq : Measurable q)
    {π : Measure ((E d) × (E d))} (hπ : IsCoupling π μ ν) : π ≪ refPD ε μ ↔ π ≪ μ.prod ν := by
  constructor
  · intro h
    refine Measure.AbsolutelyContinuous.mk fun A hA h0 => ?_
    rw [prod_eq_withDensity_volD hν hq, withDensity_apply _ hA] at h0
    have h0' := (lintegral_eq_zero_iff (f := fun z : (E d) × (E d) => ENNReal.ofReal (q z.2))
      (μ := (μ.prod volume).restrict A) (ENNReal.measurable_ofReal.comp (hq.comp measurable_snd))).1 h0
    have h1 : ∀ᵐ z ∂(μ.prod volume), z ∈ A → ENNReal.ofReal (q z.2) = 0 := (ae_restrict_iff' hA).1 h0'
    have hac : refPD ε μ ≪ μ.prod volume := by
      rw [refPD_eq_withDensity hε]; exact withDensity_absolutelyContinuous _ _
    have h2 : ∀ᵐ z ∂π, z ∉ A := by
      filter_upwards [h.ae_le (hac.ae_le h1), ae_pos_of_couplingD hν hq hπ] with z h1 h2 hzA
      exact (ENNReal.ofReal_eq_zero.1 (h1 hzA)).not_gt h2
    exact measure_eq_zero_iff_ae_notMem.2 h2
  · intro h
    refine h.trans ?_
    rw [prod_eq_withDensity_refPD hε hν hq]
    exact withDensity_absolutelyContinuous _ _

/-- The log-likelihood ratios against `R₀₁` and against `μ ⊗ ν` differ by an explicit function. -/
theorem llr_refPD (hε : 0 < ε) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : ν = volume.withDensity (fun y => ENNReal.ofReal (q y))) (hq : Measurable q) (hq0 : ∀ y, 0 ≤ q y)
    {π : Measure ((E d) × (E d))} [IsFiniteMeasure π] (hπ : IsCoupling π μ ν) (hac : π ≪ μ.prod ν) :
    llr π (refPD ε μ) =ᵐ[π] fun z => llr π (μ.prod ν) z +
      (Real.log (q z.2) + d * Real.log (2 * Real.pi * ε) / 2) + ‖z.2 - z.1‖ ^ 2 / (2 * ε) := by
  have hPN := prod_eq_withDensity_refPD (μ := μ) hε hν hq
  have hacR : π ≪ refPD ε μ := (ac_refPD_iff hε hν hq hπ).2 hac
  have hD : (μ.prod ν).rnDeriv (refPD ε μ) =ᵐ[refPD ε μ] prodDensD ε q := by
    rw [hPN]; exact Measure.rnDeriv_withDensity _ (measurable_prodDensD ε hq)
  have hmul := Measure.rnDeriv_mul_rnDeriv (κ := refPD ε μ) hac
  filter_upwards [hacR.ae_le hmul, hacR.ae_le hD, Measure.rnDeriv_pos hac,
    hac.ae_le (Measure.rnDeriv_ne_top π (μ.prod ν)), ae_pos_of_couplingD hν hq hπ] with z h1 h2 h3 h4 h5
  have hp := gdens_pos hε (z.2 - z.1)
  simp only [llr_def]
  rw [← h1, Pi.mul_apply, h2, ENNReal.toReal_mul, prodDensD, ENNReal.toReal_ofReal (div_nonneg (hq0 _) hp.le),
    Real.log_mul (ENNReal.toReal_pos h3.ne' h4).ne' (div_pos h5 hp).ne', Real.log_div h5.ne' hp.ne',
    log_gdens hε]
  ring

lemma integrable_fst_of_couplingD {π : Measure ((E d) × (E d))} (hπ : IsCoupling π μ ν) {f : (E d) → ℝ}
    (hf : Integrable f μ) : Integrable (fun z => f z.1) π := by
  have h : π.map Prod.fst = μ := hπ.fst_eq
  rw [← h] at hf
  exact (integrable_map_measure hf.aestronglyMeasurable measurable_fst.aemeasurable).1 hf

lemma integrable_snd_of_couplingD {π : Measure ((E d) × (E d))} (hπ : IsCoupling π μ ν) {f : (E d) → ℝ}
    (hf : Integrable f ν) : Integrable (fun z => f z.2) π := by
  have h : π.map Prod.snd = ν := hπ.snd_eq
  rw [← h] at hf
  exact (integrable_map_measure hf.aestronglyMeasurable measurable_snd.aemeasurable).1 hf

lemma integral_snd_of_couplingD {π : Measure ((E d) × (E d))} (hπ : IsCoupling π μ ν) {f : (E d) → ℝ}
    (hf : Integrable f ν) : ∫ z, f z.2 ∂π = ∫ y, f y ∂ν := by
  have h : π.map Prod.snd = ν := hπ.snd_eq
  rw [← h] at hf ⊢
  exact (integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable).symm

lemma integrable_normsq_sub_of_coupling {π : Measure ((E d) × (E d))} (hπ : IsCoupling π μ ν)
    (hμ2 : Integrable (fun x : E d => ‖x‖ ^ 2) μ) (hν2 : Integrable (fun y : E d => ‖y‖ ^ 2) ν) :
    Integrable (fun z : (E d) × (E d) => ‖z.1 - z.2‖ ^ 2) π := by
  have h1 := integrable_fst_of_couplingD hπ hμ2
  have h2 := integrable_snd_of_couplingD hπ hν2
  refine Integrable.mono' ((h1.add h2).const_mul 2) (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change ‖z.1 - z.2‖ ^ 2 ≤ 2 * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2)
  have := norm_sub_le z.1 z.2
  have h0 : 0 ≤ ‖z.1 - z.2‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖z.1‖ - ‖z.2‖)]

/-- `lem:equiv`, static half, in `ℝᵈ`. -/
theorem klDiv_refPD (hε : 0 < ε) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : ν = volume.withDensity (fun y => ENNReal.ofReal (q y))) (hq : Measurable q) (hq0 : ∀ y, 0 ≤ q y)
    (hlog : Integrable (fun y => Real.log (q y)) ν) (hμ2 : Integrable (fun x : E d => ‖x‖ ^ 2) μ)
    (hν2 : Integrable (fun y : E d => ‖y‖ ^ 2) ν) {π : Measure ((E d) × (E d))} (hπ : IsCoupling π μ ν) :
    (klDiv π (refPD ε μ) ≠ ∞ ↔ klDiv π (μ.prod ν) ≠ ∞) ∧
      (klDiv π (μ.prod ν) ≠ ∞ →
        ε * (klDiv π (refPD ε μ)).toReal = ∫ z, ‖z.1 - z.2‖ ^ 2 / 2 ∂π + ε * (klDiv π (μ.prod ν)).toReal +
          ε * (∫ y, Real.log (q y) ∂ν + d * Real.log (2 * Real.pi * ε) / 2)) := by
  have hπP : IsProbabilityMeasure π := by
    have h : π.map Prod.fst = μ := hπ.fst_eq
    have : IsProbabilityMeasure (π.map Prod.fst) := by rw [h]; infer_instance
    exact Measure.isProbabilityMeasure_of_map measurable_fst.aemeasurable
  set K := d * Real.log (2 * Real.pi * ε) / 2
  have hsq := integrable_normsq_sub_of_coupling hπ hμ2 hν2
  have hsym : (fun z : (E d) × (E d) => ‖z.2 - z.1‖ ^ 2 / (2 * ε)) = fun z => ‖z.1 - z.2‖ ^ 2 / (2 * ε) := by
    funext z; rw [norm_sub_rev]
  have hlogπ : Integrable (fun z : (E d) × (E d) => Real.log (q z.2)) π := integrable_snd_of_couplingD hπ hlog
  have hsq' : Integrable (fun z : (E d) × (E d) => ‖z.2 - z.1‖ ^ 2 / (2 * ε)) π := by
    rw [hsym]; exact hsq.div_const _
  have hh : Integrable (fun z : (E d) × (E d) => (Real.log (q z.2) + K) + ‖z.2 - z.1‖ ^ 2 / (2 * ε)) π :=
    (hlogπ.add (integrable_const _)).add hsq'
  have key : ∀ hac : π ≪ μ.prod ν,
      (Integrable (llr π (refPD ε μ)) π ↔ Integrable (llr π (μ.prod ν)) π) := by
    intro hac
    have hl := llr_refPD hε hν hq hq0 hπ hac
    rw [integrable_congr hl]
    constructor
    · intro h
      have := h.sub hh
      refine this.congr (Filter.Eventually.of_forall fun z => ?_)
      simp only [Pi.sub_apply, K]; ring
    · intro h
      exact (h.add hh).congr (Filter.Eventually.of_forall fun z => by simp only [Pi.add_apply, K]; ring)
  have hiff : klDiv π (refPD ε μ) ≠ ∞ ↔ klDiv π (μ.prod ν) ≠ ∞ := by
    rw [klDiv_ne_top_iff, klDiv_ne_top_iff, ac_refPD_iff hε hν hq hπ]
    constructor
    · rintro ⟨hac, hi⟩; exact ⟨hac, (key hac).1 hi⟩
    · rintro ⟨hac, hi⟩; exact ⟨hac, (key hac).2 hi⟩
  refine ⟨hiff, fun hfin => ?_⟩
  obtain ⟨hac, hi⟩ := klDiv_ne_top_iff.1 hfin
  have hacR : π ≪ refPD ε μ := (ac_refPD_iff hε hν hq hπ).2 hac
  have hiR : Integrable (llr π (refPD ε μ)) π := (key hac).2 hi
  have hlc : Integrable (fun z : (E d) × (E d) => Real.log (q z.2) + K) π := hlogπ.add (integrable_const _)
  have hI1 : ∫ z, (llr π (μ.prod ν) z + (Real.log (q z.2) + K) + ‖z.2 - z.1‖ ^ 2 / (2 * ε)) ∂π =
      ∫ z, (llr π (μ.prod ν) z + (Real.log (q z.2) + K)) ∂π + ∫ z, ‖z.2 - z.1‖ ^ 2 / (2 * ε) ∂π :=
    integral_add (f := fun z => llr π (μ.prod ν) z + (Real.log (q z.2) + K))
      (g := fun z : (E d) × (E d) => ‖z.2 - z.1‖ ^ 2 / (2 * ε)) (hi.add hlc) hsq'
  have hI2 : ∫ z, (llr π (μ.prod ν) z + (Real.log (q z.2) + K)) ∂π =
      ∫ z, llr π (μ.prod ν) z ∂π + ∫ z, (Real.log (q z.2) + K) ∂π :=
    integral_add (f := llr π (μ.prod ν)) (g := fun z : (E d) × (E d) => Real.log (q z.2) + K) hi hlc
  have hI3 : ∫ z, (Real.log (q z.2) + K) ∂π = ∫ y, Real.log (q y) ∂ν + K := by
    rw [integral_add (f := fun z : (E d) × (E d) => Real.log (q z.2)) hlogπ (integrable_const _),
      integral_snd_of_couplingD hπ hlog, integral_const]
    simp
  have e1 : ∫ z, ‖z.2 - z.1‖ ^ 2 / (2 * ε) ∂π = (∫ z, ‖z.1 - z.2‖ ^ 2 / 2 ∂π) / ε := by
    rw [hsym, integral_div, integral_div]
    field_simp
  rw [toReal_klDiv hacR hiR, toReal_klDiv hac hi, integral_congr_ae (llr_refPD hε hν hq hq0 hπ hac)]
  simp only [probReal_univ, add_sub_cancel_right]
  rw [hI1, hI2, hI3, e1]
  field_simp
  ring

/-! ### Static Schrödinger minimisers = entropic optimal plans, in `ℝᵈ` -/

/-- The quadratic cost `½‖x − y‖²` (`[0,∞]`-valued, as the frozen Wave 29g `sqCostD`). -/
def halfSqD (z : (E d) × (E d)) : ℝ≥0∞ := ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)

lemma lintegral_halfSqD {π : Measure ((E d) × (E d))} (h : Integrable (fun z : (E d) × (E d) => ‖z.1 - z.2‖ ^ 2) π) :
    ∫⁻ z, halfSqD z ∂π = ENNReal.ofReal (∫ z, ‖z.1 - z.2‖ ^ 2 / 2 ∂π) :=
  (ofReal_integral_eq_lintegral_ofReal (h.div_const 2)
    (Filter.Eventually.of_forall fun z => by positivity)).symm

theorem static_iff_entropicD (hε : 0 < ε) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : ν = volume.withDensity (fun y => ENNReal.ofReal (q y))) (hq : Measurable q) (hq0 : ∀ y, 0 ≤ q y)
    (hlog : Integrable (fun y => Real.log (q y)) ν) (hμ2 : Integrable (fun x : E d => ‖x‖ ^ 2) μ)
    (hν2 : Integrable (fun y : E d => ‖y‖ ^ 2) ν) :
    entropicTransportCost halfSqD ε.toNNReal μ ν ≠ ∞ ∧
      ∀ π : Measure ((E d) × (E d)),
        (IsCoupling π μ ν ∧ klDiv π (refPD ε μ) ≠ ∞ ∧
            ∀ π' : Measure ((E d) × (E d)), IsCoupling π' μ ν → klDiv π (refPD ε μ) ≤ klDiv π' (refPD ε μ)) ↔
          (IsCoupling π μ ν ∧
            ∫⁻ z, halfSqD z ∂π + (ε.toNNReal : ℝ≥0∞) * klDiv π (μ.prod ν) =
              entropicTransportCost halfSqD ε.toNNReal μ ν) := by
  set F : Measure ((E d) × (E d)) → ℝ≥0∞ := fun π => ∫⁻ z, halfSqD z ∂π + (ε.toNNReal : ℝ≥0∞) * klDiv π (μ.prod ν)
  have hεc : ((ε.toNNReal : ℝ≥0∞)) ≠ 0 := by simpa using hε
  have hεt : ((ε.toNNReal : ℝ≥0∞)) ≠ ∞ := ENNReal.coe_ne_top
  have hεr : ((ε.toNNReal : ℝ≥0∞)).toReal = ε := by simp [hε.le]
  have hfin : ∀ π, IsCoupling π μ ν → (F π ≠ ∞ ↔ klDiv π (refPD ε μ) ≠ ∞) := by
    intro π hπ
    have hc : ∫⁻ z, halfSqD z ∂π ≠ ∞ := by
      rw [lintegral_halfSqD (integrable_normsq_sub_of_coupling hπ hμ2 hν2)]; exact ENNReal.ofReal_ne_top
    rw [(klDiv_refPD hε hν hq hq0 hlog hμ2 hν2 hπ).1]
    simp [F, ENNReal.add_eq_top, hc, ENNReal.mul_eq_top, hεc, hεt]
  set K := ∫ y, Real.log (q y) ∂ν + d * Real.log (2 * Real.pi * ε) / 2
  have hval : ∀ π, IsCoupling π μ ν → F π ≠ ∞ → (F π).toReal = ε * (klDiv π (refPD ε μ)).toReal - ε * K := by
    intro π hπ hF
    have hk : klDiv π (μ.prod ν) ≠ ∞ := by
      rw [← (klDiv_refPD hε hν hq hq0 hlog hμ2 hν2 hπ).1]; exact (hfin π hπ).1 hF
    have hc : ∫⁻ z, halfSqD z ∂π ≠ ∞ := by
      rw [lintegral_halfSqD (integrable_normsq_sub_of_coupling hπ hμ2 hν2)]; exact ENNReal.ofReal_ne_top
    rw [(klDiv_refPD hε hν hq hq0 hlog hμ2 hν2 hπ).2 hk]
    simp only [F]
    rw [ENNReal.toReal_add hc (ENNReal.mul_ne_top hεt hk), ENNReal.toReal_mul, hεr,
      lintegral_halfSqD (integrable_normsq_sub_of_coupling hπ hμ2 hν2),
      ENNReal.toReal_ofReal (integral_nonneg fun z => by positivity)]
    ring
  have hord : ∀ π π', IsCoupling π μ ν → IsCoupling π' μ ν →
      (F π ≤ F π' ↔ klDiv π (refPD ε μ) ≤ klDiv π' (refPD ε μ)) := by
    intro π π' hπ hπ'
    by_cases h' : F π' = ∞
    · have : klDiv π' (refPD ε μ) = ∞ := by
        by_contra hk; exact ((hfin π' hπ').2 hk) h'
      rw [h', this]; simp
    · have hk' : klDiv π' (refPD ε μ) ≠ ∞ := (hfin π' hπ').1 h'
      by_cases h : F π = ∞
      · have : klDiv π (refPD ε μ) = ∞ := by
          by_contra hk; exact ((hfin π hπ).2 hk) h
        rw [h, this, top_le_iff, top_le_iff]
        exact ⟨fun e => (h' e).elim, fun e => (hk' e).elim⟩
      · have hk : klDiv π (refPD ε μ) ≠ ∞ := (hfin π hπ).1 h
        rw [← ENNReal.toReal_le_toReal h h', hval π hπ h, hval π' hπ' h', ← ENNReal.toReal_le_toReal hk hk']
        constructor
        · intro hle; nlinarith
        · intro hle; nlinarith
  have hETC : entropicTransportCost halfSqD ε.toNNReal μ ν =
      ⨅ (π : Measure ((E d) × (E d))) (_ : IsCoupling π μ ν), F π :=
    entropicTransportCost_def
  have hprod : IsCoupling (μ.prod ν) μ ν := ⟨Measure.fst_prod, Measure.snd_prod⟩
  have hne : entropicTransportCost halfSqD ε.toNNReal μ ν ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (hETC ▸ iInf₂_le (μ.prod ν) hprod)
    have : klDiv (μ.prod ν) (μ.prod ν) ≠ ∞ := by rw [klDiv_self]; exact ENNReal.zero_ne_top
    exact (hfin _ hprod).2 ((klDiv_refPD hε hν hq hq0 hlog hμ2 hν2 hprod).1.2 this)
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

end StatFormal.SchrodingerPathD
