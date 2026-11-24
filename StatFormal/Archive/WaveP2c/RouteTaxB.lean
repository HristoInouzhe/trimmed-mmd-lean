import StatFormal.Archive.WaveP2c.RouteTaxProj
import StatFormal.Archive.WaveP2c.RouteTaxKL

/-!
# Route (wave P2c): JASA `prop:tax`(b), the smooth class (untrusted)

The paper's proof: per box and coordinate a near-optimal mixing law for `ϰ(b_k/s_k(y))`, projected onto `[−½,½]`
(`klRef_proj_le`) and rescaled to the box (scale invariance: `KL` is invariant under the affine bijection
`u ↦ y_k + s_k u`, which carries `N(0,β²) ∗ m` to `N(0,b_k²) ∗ m∘A⁻¹`, `b_k = s_kβ`); the product mixing law `m_y`
on `B(y) ⊆ K` and tensorization give `KL(U_{B(y)} ‖ G_b ∗ m_y) ≤ Σ_k ϰ(b_k/s_k(y)) + dη`; joint convexity for the
mixture `m* = Σ_y p_y m_y ∈ 𝒫(K)`, and the restriction to `K` does not change the paper's `KL` of a law on `K`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set Finset
open scoped ENNReal NNReal

set_option linter.style.longLine false

namespace StatFormal.WaveP2c

open StatFormal.RobustEquality (klRef)
open StatFormal.Wave21a (boxU varkappa)

/-- `KL = klRef` between probability measures (the paper's `KL` has no mass correction then). -/
lemma klRef_eq_coe_klDiv {E : Type} [MeasurableSpace E] (Γ ν : Measure E) [IsProbabilityMeasure Γ]
    [IsProbabilityMeasure ν] : klRef Γ ν = (klDiv Γ ν : EReal) := by
  rw [StatFormal.Foundations.Tax.klRef_eq_klDiv, probReal_univ]
  split_ifs with h
  · rw [h]; rfl
  · rw [sub_add_cancel]
    exact EReal.coe_ennreal_toReal h

/-- The affine bijection `u ↦ y + s u`. -/
def affEquiv (y s : ℝ) (hs : s ≠ 0) : ℝ ≃ᵐ ℝ where
  toFun u := y + s * u
  invFun x := (x - y) / s
  left_inv u := by field_simp; ring
  right_inv x := by field_simp; ring
  measurable_toFun := (measurable_const.add (measurable_const.mul measurable_id) : Measurable fun u : ℝ => y + s * u)
  measurable_invFun := ((measurable_id.sub measurable_const).div_const s : Measurable fun x : ℝ => (x - y) / s)

lemma gauss_map_mul {β s : ℝ} : (gaussianReal 0 (β ^ 2).toNNReal).map (fun u => s * u) =
    gaussianReal 0 ((s * β) ^ 2).toNNReal := by
  rw [gaussianReal_map_const_mul, mul_zero]
  congr 1
  ext
  simp only [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ (sq_nonneg _)]
  ring

/-- **One coordinate**: a mixing law on `[y − s/2, y + s/2]` with `KL(U_{[y ± s/2]} ‖ N(0,b²) ∗ m) ≤ ϰ(b/s) + η`. -/
lemma coord_law {y s b η : ℝ} (hs : 0 < s) (hb : 0 < b) (hη : 0 < η) :
    ∃ m : Measure ℝ, IsProbabilityMeasure m ∧ m (Icc (y - s / 2) (y + s / 2))ᶜ = 0 ∧
      klDiv (boxU.map fun u => y + s * u) (gaussianReal 0 (b ^ 2).toNNReal ∗ m) ≤
        ENNReal.ofReal ((varkappa (b / s)).toReal + η) := by
  set β := b / s with hβ
  have hβ0 : 0 < β := div_pos hb hs
  have hv : (β ^ 2).toNNReal ≠ 0 := by
    simp only [ne_eq, Real.toNNReal_eq_zero, not_le]; positivity
  -- `ϰ(β)` is finite
  obtain ⟨hk0, hk1⟩ := StatFormal.Wave21a.tax_a_bound β hβ0
  have hfin : varkappa β = ((varkappa β).toReal : EReal) := by
    refine (EReal.coe_toReal ?_ ?_).symm
    · exact ne_top_of_le_ne_top (EReal.coe_ne_top _) hk1
    · exact ne_bot_of_le_ne_bot (by simp) hk0
  have hlt : varkappa β < (((varkappa β).toReal + η : ℝ) : EReal) := by
    rw [hfin, EReal.coe_lt_coe_iff, EReal.toReal_coe]; linarith
  -- a near-optimal mixing law
  unfold varkappa at hlt
  obtain ⟨m₀, hlt'⟩ := iInf_lt_iff.1 hlt
  obtain ⟨hm₀, hlt''⟩ := iInf_lt_iff.1 hlt'
  have hproj := klRef_proj_le hv m₀
  set m₁ := m₀.map proj with hm₁
  have : IsProbabilityMeasure m₁ := (Measure.isProbabilityMeasure_map_iff measurable_proj.aemeasurable).2 hm₀
  have h1 : klRef boxU (gaussianReal 0 (β ^ 2).toNNReal ∗ m₁) < (((varkappa β).toReal + η : ℝ) : EReal) :=
    lt_of_le_of_lt hproj.1 hlt''
  rw [klRef_eq_coe_klDiv] at h1
  have h1' : klDiv boxU (gaussianReal 0 (β ^ 2).toNNReal ∗ m₁) ≤ ENNReal.ofReal ((varkappa β).toReal + η) := by
    have hne : klDiv boxU (gaussianReal 0 (β ^ 2).toNNReal ∗ m₁) ≠ ⊤ := by
      intro h; rw [h] at h1; exact absurd h1 (not_lt.2 le_top)
    rw [← ENNReal.ofReal_toReal hne]
    refine ENNReal.ofReal_le_ofReal ?_
    have : ((klDiv boxU (gaussianReal 0 (β ^ 2).toNNReal ∗ m₁) : ℝ≥0∞) : EReal) =
        ((klDiv boxU (gaussianReal 0 (β ^ 2).toNNReal ∗ m₁)).toReal : EReal) :=
      (EReal.coe_ennreal_toReal hne).symm
    rw [this, EReal.coe_lt_coe_iff] at h1
    exact h1.le
  -- rescale to the box
  set A := affEquiv y s hs.ne' with hA
  refine ⟨m₁.map A, (Measure.isProbabilityMeasure_map_iff A.measurable.aemeasurable).2 inferInstance, ?_, ?_⟩
  · rw [Measure.map_apply A.measurable measurableSet_Icc.compl]
    refine measure_mono_null (fun u hu => ?_) hproj.2
    simp only [Set.mem_preimage, Set.mem_compl_iff] at hu ⊢
    intro hu'
    apply hu
    obtain ⟨h1, h2⟩ := hu'
    change y + s * u ∈ Icc (y - s / 2) (y + s / 2)
    constructor <;> nlinarith
  · have hconv : (gaussianReal 0 (β ^ 2).toNNReal ∗ m₁).map A = gaussianReal 0 (b ^ 2).toNNReal ∗ m₁.map A := by
      have := map_conv_affine (gaussianReal 0 (β ^ 2).toNNReal) m₁ y s
      rw [gauss_map_mul, show s * β = b by rw [hβ]; field_simp] at this
      exact this
    have hbox : boxU.map (fun u => y + s * u) = boxU.map A := rfl
    rw [hbox, ← hconv, klDiv_map_equiv A]
    exact h1'

lemma boxU_map_prob (y s : ℝ) : IsProbabilityMeasure (boxU.map fun u => y + s * u) :=
  (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance

instance boxLaw_prob {d : ℕ} (y σ : Fin d → ℝ) : IsProbabilityMeasure (boxLaw y σ) := by
  unfold boxLaw
  have : ∀ k, IsProbabilityMeasure (boxU.map fun u => y k + σ k * u) := fun k => boxU_map_prob _ _
  infer_instance

/-- A product law whose coordinates are carried by the box intervals is carried by the box. -/
lemma pi_compl_box_eq_zero {d : ℕ} (y σ : Fin d → ℝ) (μ : Fin d → Measure ℝ) [∀ k, IsProbabilityMeasure (μ k)]
    (h : ∀ k, μ k (Icc (y k - σ k / 2) (y k + σ k / 2))ᶜ = 0) :
    Measure.pi μ (boxSet y σ)ᶜ = 0 := by
  have hm : MeasurableSet (boxSet y σ) := MeasurableSet.univ_pi fun k => measurableSet_Icc
  rw [prob_compl_eq_zero_iff hm]
  unfold boxSet
  rw [Measure.pi_pi]
  refine Finset.prod_eq_one fun k _ => ?_
  exact (prob_compl_eq_zero_iff measurableSet_Icc).1 (h k)

lemma boxLaw_compl {d : ℕ} (y σ : Fin d → ℝ) (hσ : ∀ k, 0 < σ k) : boxLaw y σ (boxSet y σ)ᶜ = 0 := by
  unfold boxLaw
  have : ∀ k, IsProbabilityMeasure (boxU.map fun u => y k + σ k * u) := fun k => boxU_map_prob _ _
  refine pi_compl_box_eq_zero y σ _ fun k => ?_
  rw [Measure.map_apply (by fun_prop) measurableSet_Icc.compl, StatFormal.Wave21a.boxU,
    Measure.restrict_apply (measurableSet_Icc.compl.preimage (by fun_prop))]
  convert measure_empty (μ := (volume : Measure ℝ))
  refine Set.eq_empty_of_forall_notMem fun u hu => ?_
  obtain ⟨hu1, hu2⟩ := hu
  apply hu1
  obtain ⟨h1, h2⟩ := hu2
  have := hσ k
  change y k + σ k * u ∈ Icc (y k - σ k / 2) (y k + σ k / 2)
  constructor <;> nlinarith

/-- **One box**: a product mixing law on `B(y)` with `KL(U_{B(y)} ‖ G_b ∗ m_y) ≤ Σ_k (ϰ(b_k/σ_k) + η)`. -/
lemma box_law {d : ℕ} (y σ b : Fin d → ℝ) (hσ : ∀ k, 0 < σ k) (hb : ∀ k, 0 < b k) {η : ℝ} (hη : 0 < η) :
    ∃ my : Measure (Fin d → ℝ), IsProbabilityMeasure my ∧ my (boxSet y σ)ᶜ = 0 ∧
      klDiv (boxLaw y σ) (gaussProd b ∗ my) ≤ ∑ k, ENNReal.ofReal ((varkappa (b k / σ k)).toReal + η) := by
  choose m hm hsupp hkl using fun k => coord_law (y := y k) (hσ k) (hb k) hη
  have : ∀ k, IsProbabilityMeasure (m k) := hm
  refine ⟨Measure.pi m, inferInstance, pi_compl_box_eq_zero y σ m hsupp, ?_⟩
  have : ∀ k, IsProbabilityMeasure (boxU.map fun u => y k + σ k * u) := fun k => boxU_map_prob _ _
  unfold gaussProd boxLaw
  rw [pi_conv_pi, klDiv_pi]
  exact Finset.sum_le_sum fun k _ => hkl k

theorem tax_b_smooth : Claims.tax_b_smooth := by
  intro d Y p s b K hp hsum hs hb hK hBK
  set T := ∑ y ∈ Y, p y * ∑ k, (varkappa (b k / s y k)).toReal with hT
  set P := boxMix Y p s with hP
  have hPprob : IsProbabilityMeasure P := by
    refine ⟨?_⟩
    simp only [hP, boxMix, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
      smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg hp, hsum, ENNReal.ofReal_one]
  have hPK : P Kᶜ = 0 := by
    simp only [hP, boxMix, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
    refine Finset.sum_eq_zero fun y hy => ?_
    rw [measure_mono_null (compl_subset_compl.2 (hBK y hy)) (boxLaw_compl y (s y) (hs y hy)), mul_zero]
  have hκ0 : ∀ y ∈ Y, ∀ k, 0 ≤ (varkappa (b k / s y k)).toReal := fun y hy k =>
    EReal.toReal_nonneg (StatFormal.Wave21a.tax_a_bound _ (div_pos (hb k) (hs y hy k))).1
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun y hy => mul_nonneg (hp y hy) (Finset.sum_nonneg fun k _ => hκ0 y hy k)
  have hPsub : P = ∑ i : {y // y ∈ Y}, ENNReal.ofReal (p i) • boxLaw (i : Fin d → ℝ) (s i) := by
    rw [hP, boxMix]; exact (Finset.sum_coe_sort Y (fun y => ENNReal.ofReal (p y) • boxLaw y (s y))).symm
  have key : ∀ η : ℝ, 0 < η → StatFormal.RobustEquality.Tax.tax (smoothClass b K) P ≤ ((T + d * η : ℝ) : EReal) := by
    intro η hη
    have hex : ∀ i : {y // y ∈ Y}, ∃ my : Measure (Fin d → ℝ), IsProbabilityMeasure my ∧
        my (boxSet (i : Fin d → ℝ) (s i))ᶜ = 0 ∧
        klDiv (boxLaw (i : Fin d → ℝ) (s i)) (gaussProd b ∗ my) ≤
          ∑ k, ENNReal.ofReal ((varkappa (b k / s i k)).toReal + η) :=
      fun i => box_law (i : Fin d → ℝ) (s i) b (hs i i.2) hb hη
    choose my hmy hmysupp hmykl using hex
    have : ∀ i, IsProbabilityMeasure (my i) := hmy
    -- the mixing law
    set mstar := ∑ i : {y // y ∈ Y}, ENNReal.ofReal (p i) • my i with hmstar
    have hpsub : ∑ i : {y // y ∈ Y}, p i = 1 := by rw [Finset.sum_coe_sort Y p]; exact hsum
    have hpsub0 : ∀ i : {y // y ∈ Y}, 0 ≤ p i := fun i => hp i i.2
    have hmstar_prob : IsProbabilityMeasure mstar := by
      refine ⟨?_⟩
      simp only [hmstar, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ, smul_eq_mul,
        mul_one]
      rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hpsub0 i, hpsub, ENNReal.ofReal_one]
    have hmstarK : mstar Kᶜ = 0 := by
      simp only [hmstar, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [measure_mono_null (compl_subset_compl.2 (hBK i i.2)) (hmysupp i), mul_zero]
    have hmem : (gaussProd b ∗ mstar).restrict K ∈ smoothClass b K := ⟨mstar, hmstar_prob, hmstarK, rfl⟩
    have htax : StatFormal.RobustEquality.Tax.tax (smoothClass b K) P ≤ klRef P ((gaussProd b ∗ mstar).restrict K) :=
      iInf₂_le _ hmem
    have : IsProbabilityMeasure (gaussProd b) := by unfold gaussProd; infer_instance
    rw [klRef_restrict P _ hK hPK, klRef_eq_coe_klDiv] at htax
    refine htax.trans ?_
    -- convexity over the recorded values
    have hconv : gaussProd b ∗ mstar = ∑ i : {y // y ∈ Y}, ENNReal.ofReal (p i) • (gaussProd b ∗ my i) :=
      conv_finsum (ι := {y // y ∈ Y}) Finset.univ (gaussProd b) (fun i => ENNReal.ofReal (p i))
        (fun _ => ENNReal.ofReal_ne_top) my
    have hstep := klDiv_finsum_le (ι := {y // y ∈ Y}) (fun i => ENNReal.ofReal (p i)) (fun _ => ENNReal.ofReal_ne_top)
      (fun i => boxLaw (i : Fin d → ℝ) (s i)) (fun i => gaussProd b ∗ my i)
    rw [← hPsub, ← hconv] at hstep
    have hbound : ∑ i : {y // y ∈ Y}, ENNReal.ofReal (p i) * klDiv (boxLaw (i : Fin d → ℝ) (s i)) (gaussProd b ∗ my i) ≤
        ENNReal.ofReal (T + d * η) := by
      calc _ ≤ ∑ i : {y // y ∈ Y}, ENNReal.ofReal (p i) * ∑ k, ENNReal.ofReal ((varkappa (b k / s i k)).toReal + η) :=
            Finset.sum_le_sum fun i _ => mul_le_mul_right (hmykl i) _
        _ = ENNReal.ofReal (∑ i : {y // y ∈ Y}, p i * ∑ k, ((varkappa (b k / s i k)).toReal + η)) := by
            rw [ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (hpsub0 i)
              (Finset.sum_nonneg fun k _ => by linarith [hκ0 i i.2 k])]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [ENNReal.ofReal_mul (hpsub0 i), ENNReal.ofReal_sum_of_nonneg fun k _ => by linarith [hκ0 i i.2 k]]
        _ = ENNReal.ofReal (T + d * η) := by
            congr 1
            simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              mul_add]
            rw [← Finset.sum_mul, hpsub, one_mul, hT, ← Finset.sum_coe_sort Y]
    have h1 := hstep.trans hbound
    calc ((klDiv P (gaussProd b ∗ mstar) : ℝ≥0∞) : EReal) ≤ ((ENNReal.ofReal (T + d * η) : ℝ≥0∞) : EReal) :=
          EReal.coe_ennreal_le_coe_ennreal_iff.2 h1
      _ = ((T + d * η : ℝ) : EReal) := by
          rw [EReal.coe_ennreal_ofReal, max_eq_left (by positivity)]
  -- let `η → 0`
  have hall : ∀ ε : ℝ, 0 < ε → StatFormal.RobustEquality.Tax.tax (smoothClass b K) P ≤ ((T + ε : ℝ) : EReal) := by
    intro ε hε
    refine (key (ε / (d + 1)) (by positivity)).trans (EReal.coe_le_coe_iff.2 ?_)
    have : (d : ℝ) * (ε / (d + 1)) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
    linarith
  induction h : StatFormal.RobustEquality.Tax.tax (smoothClass b K) P using EReal.rec with
  | bot => exact bot_le
  | top =>
    have := hall 1 one_pos
    rw [h] at this
    exact absurd this (not_le.2 (EReal.coe_lt_top _))
  | coe t =>
    refine EReal.coe_le_coe_iff.2 (le_of_forall_pos_le_add fun ε hε => ?_)
    have := hall ε hε
    rw [h] at this
    exact EReal.coe_le_coe_iff.1 this

theorem tax_c_smooth : Claims.tax_c_smooth := by
  intro d Y p s b K gm gp a n hp hsum hs hb hK hBK hn ha0 ha1 hrange
  set Prec : Measure {y // y ∈ Y} := ∑ i : {y // y ∈ Y}, ENNReal.ofReal (p i) • Measure.dirac i with hPrec
  have hpsub0 : ∀ i : {y // y ∈ Y}, 0 ≤ p i := fun i => hp i i.2
  have hpsub : ∑ i : {y // y ∈ Y}, p i = 1 := by rw [Finset.sum_coe_sort Y p]; exact hsum
  have hPrec_prob : IsProbabilityMeasure Prec := by
    refine ⟨?_⟩
    simp only [hPrec, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ, smul_eq_mul,
      mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hpsub0 i, hpsub, ENNReal.ofReal_one]
  set g : {y // y ∈ Y} → ℝ := fun i => ∑ k, (varkappa (b k / s i k)).toReal with hg
  have hint : ∫ i, g i ∂Prec = ∑ y ∈ Y, p y * ∑ k, (varkappa (b k / s y k)).toReal := by
    rw [hPrec, integral_finset_sum_measure (fun i _ => (Integrable.of_finite).smul_measure ENNReal.ofReal_ne_top)]
    simp only [integral_smul_measure, integral_dirac, smul_eq_mul, ENNReal.toReal_ofReal (hpsub0 _)]
    exact Finset.sum_coe_sort Y (fun y => p y * ∑ k, (varkappa (b k / s y k)).toReal)
  have htax := tax_b_smooth d Y p s b K hp hsum hs hb hK hBK
  rw [← hint] at htax
  exact StatFormal.Wave21a.tax_c {y // y ∈ Y} (Fin d → ℝ) Prec (smoothClass b K) (boxMix Y p s) g gm gp a n
    hn ha0 ha1 (measurable_of_countable g) (fun i => hrange i i.2) htax

end StatFormal.WaveP2c
