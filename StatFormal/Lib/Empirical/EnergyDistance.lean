import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Energy distance: definition and the one-dimensional case

For finite measures `P, Q` on a normed group `E`, the *mean interpoint distance* is
`meanDist P Q = ∫∫ ‖x - y‖ dP(x) dQ(y)` (an integral over the product measure), and the
*energy distance* is
`energyDist P Q = 2 E‖X - Y‖ - E‖X - X'‖ - E‖Y - Y'‖
               = 2 meanDist P Q - meanDist P P - meanDist Q Q`,
with `X, X' ~ P`, `Y, Y' ~ Q` independent.

Junk values: if the first moments are infinite, the Bochner integrals are `0`; every theorem
below assumes `Integrable id P` and `Integrable id Q` (finite first moments).

## Main results (on `ℝ`)
* `meanDist_eq_integral_cdf` — `E|X - Y| = ∫ (F(1 - G) + (1 - F)G) dt`.
* `energyDist_eq_two_mul_integral_cdf_sub_sq` — `ED(P, Q) = 2 ∫ (F(t) - G(t))² dt`.
* `energyDist_nonneg_real`, `energyDist_eq_zero_iff_real` — `ED ≥ 0`, with equality iff `P = Q`.

## References
* G. J. Székely, M. L. Rizzo, *Energy statistics: A class of statistics based on distances*,
  J. Statist. Plann. Inference 143 (2013), 1249–1272, §2 (eq. (2.2): the 1-D identity
  `ED = 2 ∫ (F - G)²`).
* L. Baringhaus, C. Franz, *On a new multivariate two-sample test*, J. Multivariate Anal. 88
  (2004).
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace StatFormal.Empirical

section Defs

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]

/-- Mean interpoint distance `E‖X - Y‖ = ∫ ‖x - y‖ d(P ⊗ Q)(x, y)` for independent `X ~ P`,
`Y ~ Q`. (Junk value `0` when the integrand is not integrable.) -/
noncomputable def meanDist (P Q : Measure E) : ℝ :=
  ∫ z, ‖z.1 - z.2‖ ∂(P.prod Q)

/-- **Energy distance** (Székely 2002; Baringhaus–Franz 2004):
`ED(P, Q) = 2 E‖X - Y‖ - E‖X - X'‖ - E‖Y - Y'‖`, with `X, X' ~ P`, `Y, Y' ~ Q` independent.
Meaningful under finite first moments (otherwise junk integrals `0` enter). -/
noncomputable def energyDist (P Q : Measure E) : ℝ :=
  2 * meanDist P Q - meanDist P P - meanDist Q Q

end Defs

section Real

/-- The set of `((x, y), t)` with `t` between `x` and `y` (half-open). Its sections in `t` have
Lebesgue measure `|x - y|`; its sections in `(x, y)` are `Iic t ×ˢ Ioi t ∪ Ioi t ×ˢ Iic t`. -/
def betweenSet : Set ((ℝ × ℝ) × ℝ) :=
  {p | (p.1.1 ≤ p.2 ∧ p.2 < p.1.2) ∨ (p.1.2 ≤ p.2 ∧ p.2 < p.1.1)}

lemma measurableSet_betweenSet : MeasurableSet betweenSet := by
  unfold betweenSet
  refine MeasurableSet.union ?_ ?_
  · exact (measurableSet_le measurable_fst.fst measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_fst.snd)
  · exact (measurableSet_le measurable_fst.snd measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_fst.fst)

lemma volume_section_betweenSet (z : ℝ × ℝ) :
    volume (Prod.mk z ⁻¹' betweenSet) = ENNReal.ofReal |z.1 - z.2| := by
  have : Prod.mk z ⁻¹' betweenSet = Ico (min z.1 z.2) (max z.1 z.2) := by
    ext t
    simp only [betweenSet, mem_preimage, mem_ofPred_eq, mem_Ico, min_le_iff, lt_max_iff]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨Or.inl h1, Or.inr h2⟩
      · exact ⟨Or.inr h1, Or.inl h2⟩
    · rintro ⟨h1 | h1, h2 | h2⟩
      · exact absurd (h1.trans_lt h2) (lt_irrefl _)
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
      · exact absurd (h1.trans_lt h2) (lt_irrefl _)
  rw [this, Real.volume_Ico, max_sub_min_eq_abs, abs_sub_comm]

lemma prod_section_betweenSet (P Q : Measure ℝ) [SFinite P] [SFinite Q] (t : ℝ) :
    (P.prod Q) ((fun z ↦ (z, t)) ⁻¹' betweenSet) =
      P (Iic t) * Q (Ioi t) + P (Ioi t) * Q (Iic t) := by
  have : (fun z ↦ (z, t)) ⁻¹' betweenSet = Iic t ×ˢ Ioi t ∪ Ioi t ×ˢ Iic t := by
    ext z
    simp only [betweenSet, mem_preimage, mem_ofPred_eq, mem_union, mem_prod, mem_Iic, mem_Ioi]
    tauto
  rw [this, measure_union, Measure.prod_prod, Measure.prod_prod]
  · rw [Set.disjoint_left]
    rintro z ⟨h1, -⟩ ⟨h2, -⟩
    exact absurd (mem_Iic.1 h1) (not_le.2 (mem_Ioi.1 h2))
  · exact measurableSet_Ioi.prod measurableSet_Iic

/-- Tonelli form of `E|X - Y| = ∫ (P(X ≤ t) P(Y > t) + P(X > t) P(Y ≤ t)) dt`. -/
lemma lintegral_abs_sub_eq (P Q : Measure ℝ) [SFinite P] [SFinite Q] :
    ∫⁻ z, ENNReal.ofReal |z.1 - z.2| ∂(P.prod Q) =
      ∫⁻ t, (P (Iic t) * Q (Ioi t) + P (Ioi t) * Q (Iic t)) := by
  have h1 := Measure.prod_apply (μ := P.prod Q) (ν := volume) measurableSet_betweenSet
  have h2 := Measure.prod_apply_symm (μ := P.prod Q) (ν := volume) measurableSet_betweenSet
  simp_rw [volume_section_betweenSet] at h1
  simp_rw [prod_section_betweenSet] at h2
  rw [← h1, h2]

/-- The integrand `F(t)(1 - G(t)) + (1 - F(t))G(t)` of `E|X - Y|`, `F = cdf P`, `G = cdf Q`. -/
noncomputable def cdfCross (P Q : Measure ℝ) (t : ℝ) : ℝ :=
  cdf P t * (1 - cdf Q t) + (1 - cdf P t) * cdf Q t

lemma one_sub_cdf (P : Measure ℝ) [IsProbabilityMeasure P] (t : ℝ) :
    1 - cdf P t = P.real (Ioi t) := by
  rw [cdf_eq_real, ← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]

lemma cdfCross_nonneg (P Q : Measure ℝ) (t : ℝ) : 0 ≤ cdfCross P Q t := by
  unfold cdfCross
  have h1 := cdf_nonneg P t; have h2 := cdf_le_one P t
  have h3 := cdf_nonneg Q t; have h4 := cdf_le_one Q t
  have : 0 ≤ 1 - cdf Q t := by linarith
  have : 0 ≤ 1 - cdf P t := by linarith
  positivity

lemma measurable_cdfCross (P Q : Measure ℝ) : Measurable (cdfCross P Q) := by
  unfold cdfCross
  have hP := (cdf P).mono.measurable
  have hQ := (cdf Q).mono.measurable
  fun_prop

lemma ofReal_cdfCross (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (t : ℝ) : ENNReal.ofReal (cdfCross P Q t) =
      P (Iic t) * Q (Ioi t) + P (Ioi t) * Q (Iic t) := by
  unfold cdfCross
  rw [one_sub_cdf, one_sub_cdf, cdf_eq_real, cdf_eq_real,
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul measureReal_nonneg, ENNReal.ofReal_mul measureReal_nonneg,
    ofReal_measureReal, ofReal_measureReal, ofReal_measureReal, ofReal_measureReal]

/-- **Mean interpoint distance on `ℝ` via distribution functions.** For probability measures
`P, Q` on `ℝ` with finite first moments, `E|X - Y| = ∫ (F(t)(1 - G(t)) + (1 - F(t))G(t)) dt`
(`X ~ P`, `Y ~ Q` independent, `F, G` their cdfs), and the integrand is Lebesgue integrable.
Proof: `|x - y| = λ{t between x and y}` and Tonelli. Source: Székely–Rizzo (2013), §2. -/
theorem meanDist_eq_integral_cdfCross (P Q : Measure ℝ) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hP : Integrable id P) (hQ : Integrable id Q) :
    Integrable (cdfCross P Q) ∧ meanDist P Q = ∫ t, cdfCross P Q t := by
  have hint : Integrable (fun z : ℝ × ℝ ↦ ‖z.1 - z.2‖) (P.prod Q) :=
    ((hP.comp_fst Q).sub (hQ.comp_snd P)).norm
  have hlin : ∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ∂(P.prod Q) =
      ∫⁻ t, ENNReal.ofReal (cdfCross P Q t) := by
    simp_rw [Real.norm_eq_abs, ofReal_cdfCross]
    exact lintegral_abs_sub_eq P Q
  have hfin : ∫⁻ t, ENNReal.ofReal (cdfCross P Q t) < ∞ := hlin ▸ hint.lintegral_lt_top
  have hI : Integrable (cdfCross P Q) :=
    ⟨(measurable_cdfCross P Q).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (cdfCross_nonneg P Q))).2 hfin⟩
  refine ⟨hI, ?_⟩
  rw [meanDist, integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ ↦ norm_nonneg _)
      hint.aestronglyMeasurable, hlin,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (cdfCross_nonneg P Q))
      hI.aestronglyMeasurable]

/-- The energy distance of a measure to itself is `0` (no moment assumption needed). -/
@[simp] lemma energyDist_self {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (P : Measure E) : energyDist P P = 0 := by
  unfold energyDist; ring

/-- **One-dimensional energy identity** (Székely–Rizzo 2013, eq. (2.2)). For probability
measures `P, Q` on `ℝ` with finite first moments and cdfs `F, G`,
`ED(P, Q) = 2 E|X - Y| - E|X - X'| - E|Y - Y'| = 2 ∫ (F(t) - G(t))² dt`,
and `(F - G)²` is Lebesgue integrable. -/
theorem energyDist_eq_two_mul_integral_cdf_sub_sq (P Q : Measure ℝ) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hP : Integrable id P) (hQ : Integrable id Q) :
    Integrable (fun t ↦ (cdf P t - cdf Q t) ^ 2) ∧
      energyDist P Q = 2 * ∫ t, (cdf P t - cdf Q t) ^ 2 := by
  obtain ⟨hPQi, hPQ⟩ := meanDist_eq_integral_cdfCross P Q hP hQ
  obtain ⟨hPPi, hPP⟩ := meanDist_eq_integral_cdfCross P P hP hP
  obtain ⟨hQQi, hQQ⟩ := meanDist_eq_integral_cdfCross Q Q hQ hQ
  have hfun : (fun t ↦ (cdf P t - cdf Q t) ^ 2) =
      fun t ↦ (2⁻¹ : ℝ) * (2 * cdfCross P Q t - cdfCross P P t - cdfCross Q Q t) := by
    funext t; unfold cdfCross; ring
  have hcomb : Integrable (fun t ↦ 2 * cdfCross P Q t - cdfCross P P t - cdfCross Q Q t) :=
    ((hPQi.const_mul 2).sub hPPi).sub hQQi
  refine ⟨hfun ▸ hcomb.const_mul _, ?_⟩
  have e : ∫ t, (2 * cdfCross P Q t - cdfCross P P t - cdfCross Q Q t) =
      2 * (∫ t, cdfCross P Q t) - (∫ t, cdfCross P P t) - ∫ t, cdfCross Q Q t := by
    have h1 : Integrable (fun t ↦ 2 * cdfCross P Q t - cdfCross P P t) :=
      (hPQi.const_mul 2).sub hPPi
    rw [integral_sub h1 hQQi, integral_sub (hPQi.const_mul 2) hPPi, integral_const_mul]
  rw [hfun, integral_const_mul, e, energyDist, hPQ, hPP, hQQ]
  ring

/-- **Non-negativity of the energy distance on `ℝ`.** For probability measures with finite first
moments, `ED(P, Q) ≥ 0`. Source: Székely–Rizzo (2013), Prop. 1 (case `d = 1`). -/
theorem energyDist_nonneg_real (P Q : Measure ℝ) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hP : Integrable id P) (hQ : Integrable id Q) :
    0 ≤ energyDist P Q := by
  rw [(energyDist_eq_two_mul_integral_cdf_sub_sq P Q hP hQ).2]
  have := integral_nonneg (μ := volume) (f := fun t ↦ (cdf P t - cdf Q t) ^ 2)
    fun t ↦ sq_nonneg _
  positivity

/-- Two Stieltjes functions that agree Lebesgue-a.e. agree everywhere (right-continuity). -/
lemma StieltjesFunction.eq_of_ae_eq (f g : StieltjesFunction ℝ) (h : ∀ᵐ t, f t = g t) (x : ℝ) :
    f x = g x := by
  have hf : Tendsto f (𝓝[>] x) (𝓝 (f x)) :=
    (f.right_continuous x).mono Ioi_subset_Ici_self
  have hg : Tendsto g (𝓝[>] x) (𝓝 (g x)) :=
    (g.right_continuous x).mono Ioi_subset_Ici_self
  refine tendsto_nhds_unique_of_frequently_eq hf hg ?_
  rw [Filter.frequently_iff]
  intro U hU
  obtain ⟨u, hxu, hUu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hU
  by_contra hcon
  have hnull : volume {t | ¬ f t = g t} = 0 := ae_iff.1 h
  have : volume (Ioo x u) = 0 :=
    measure_mono_null (fun t ht he ↦ hcon ⟨t, hUu ht, he⟩) hnull
  rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at this
  linarith [mem_Ioi.1 hxu]

/-- **Energy distance characterises equality on `ℝ`.** For probability measures `P, Q` on `ℝ`
with finite first moments, `ED(P, Q) = 0 ↔ P = Q`. Proof: `ED = 2 ∫ (F - G)²`, so `F = G`
a.e., hence everywhere by right-continuity, hence `P = Q`. Source: Székely–Rizzo (2013),
Prop. 1 (case `d = 1`). -/
theorem energyDist_eq_zero_iff_real (P Q : Measure ℝ) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hP : Integrable id P) (hQ : Integrable id Q) :
    energyDist P Q = 0 ↔ P = Q := by
  refine ⟨fun h0 ↦ ?_, fun h ↦ h ▸ energyDist_self P⟩
  obtain ⟨hint, heq⟩ := energyDist_eq_two_mul_integral_cdf_sub_sq P Q hP hQ
  have h1 : ∫ t, (cdf P t - cdf Q t) ^ 2 = 0 := by linarith
  rw [integral_eq_zero_iff_of_nonneg (fun t ↦ sq_nonneg _) hint] at h1
  have hae : ∀ᵐ t, cdf P t = cdf Q t := by
    filter_upwards [h1] with t ht
    have : (cdf P t - cdf Q t) ^ 2 = 0 := ht
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    linarith
  exact Measure.eq_of_cdf P Q (StieltjesFunction.ext fun x ↦
    StieltjesFunction.eq_of_ae_eq _ _ hae x)

end Real

end StatFormal.Empirical
