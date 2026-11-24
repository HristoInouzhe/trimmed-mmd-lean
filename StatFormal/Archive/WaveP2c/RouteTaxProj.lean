import StatFormal.Archive.WaveP2c.RouteTaxMeas

/-!
# Route (wave P2c): projecting mixing atoms onto the box (untrusted)

`prop:tax`(a) proof, first sentence: "Projecting mixing atoms onto `[−½,½]` increases `N(0,β²) ∗ m` pointwise on the
box, so the infimum may be taken over `𝒫([−½,½])`". Here: `N(0,v) ∗ m` has the Lebesgue density
`q_m(x) = ∫ φ_v(x − z) dm(z)` (`gauss_conv_eq`), `KL(U ‖ N(0,v) ∗ m) = −∫_{[−½,½]} log q_m` (`klRef_boxU_conv`), and
`q_{m∘proj⁻¹} ≥ q_m` on the box because `|x − proj z| ≤ |x − z|` there.
-/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set Finset
open scoped ENNReal NNReal

set_option linter.style.longLine false

namespace StatFormal.WaveP2c

open StatFormal.RobustEquality (klRef)
open StatFormal.Wave21a (boxU)

/-- The projection onto `[−½, ½]`. -/
def proj (z : ℝ) : ℝ := max (-(1 / 2)) (min (1 / 2) z)

lemma measurable_proj : Measurable proj := by unfold proj; fun_prop

lemma proj_mem (z : ℝ) : proj z ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) := by
  unfold proj; constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

lemma abs_sub_proj_le {x : ℝ} (hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) (z : ℝ) : |x - proj z| ≤ |x - z| := by
  obtain ⟨h1, h2⟩ := hx
  unfold proj
  rcases le_total z (1 / 2) with hz | hz
  · rw [min_eq_right hz]
    rcases le_total (-(1 / 2)) z with hz' | hz'
    · rw [max_eq_right hz']
    · rw [max_eq_left hz']
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
  · rw [min_eq_left hz, max_eq_right (by norm_num)]
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith

/-- The density `q_m(x) = ∫ φ_v(x − z) dm(z)`. -/
def qd (v : ℝ≥0) (m : Measure ℝ) (x : ℝ) : ℝ := ∫ z, gaussianPDFReal 0 v (x - z) ∂m

lemma gaussianPDFReal_le (v : ℝ≥0) (t : ℝ) : gaussianPDFReal 0 v t ≤ (√(2 * Real.pi * v))⁻¹ := by
  rw [gaussianPDFReal_def]
  have : Real.exp (-(t - 0) ^ 2 / (2 * v)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg t]) (by positivity)
  calc (√(2 * Real.pi * v))⁻¹ * Real.exp (-(t - 0) ^ 2 / (2 * v)) ≤ (√(2 * Real.pi * v))⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := mul_one _

lemma gaussianPDFReal_anti (v : ℝ≥0) {t t' : ℝ} (h : |t| ≤ |t'|) :
    gaussianPDFReal 0 v t' ≤ gaussianPDFReal 0 v t := by
  rw [gaussianPDFReal_def]
  simp only [sub_zero]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
  have : t ^ 2 ≤ t' ^ 2 := by
    rw [← sq_abs t, ← sq_abs t']; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

lemma integrable_gauss_shift (v : ℝ≥0) (m : Measure ℝ) [IsFiniteMeasure m] (x : ℝ) :
    Integrable (fun z => gaussianPDFReal 0 v (x - z)) m :=
  Integrable.of_mem_Icc 0 ((√(2 * Real.pi * v))⁻¹)
    ((measurable_gaussianPDFReal 0 v).comp (measurable_const.sub measurable_id)).aemeasurable
    (ae_of_all _ fun z => ⟨gaussianPDFReal_nonneg 0 v _, gaussianPDFReal_le v _⟩)

lemma measurable_qd (v : ℝ≥0) (m : Measure ℝ) [IsFiniteMeasure m] : Measurable (qd v m) := by
  unfold qd
  have hf : StronglyMeasurable (Function.uncurry fun x z : ℝ => gaussianPDFReal 0 v (x - z)) :=
    ((measurable_gaussianPDFReal 0 v).comp (measurable_fst.sub measurable_snd)).stronglyMeasurable
  exact (hf.integral_prod_right (ν := m)).measurable

lemma qd_nonneg (v : ℝ≥0) (m : Measure ℝ) (x : ℝ) : 0 ≤ qd v m x :=
  integral_nonneg fun z => gaussianPDFReal_nonneg 0 v _

/-- `N(0,v) ∗ m = q_m · Leb`. -/
theorem gauss_conv_eq {v : ℝ≥0} (hv : v ≠ 0) (m : Measure ℝ) [IsProbabilityMeasure m] :
    gaussianReal 0 v ∗ m = volume.withDensity fun x => ENNReal.ofReal (qd v m x) := by
  set g := gaussianPDF 0 v with hg
  have hgm : Measurable g := by rw [hg, gaussianPDF_def]; exact (measurable_gaussianPDFReal 0 v).ennreal_ofReal
  have hdens : ∀ x, ENNReal.ofReal (qd v m x) = ∫⁻ z, g (x - z) ∂m := by
    intro x
    unfold qd
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_gauss_shift v m x)
      (ae_of_all _ fun z => gaussianPDFReal_nonneg 0 v _)]
    simp [hg, gaussianPDF_def]
  ext A hA
  rw [withDensity_apply _ hA, ← lintegral_indicator_one hA, Measure.lintegral_conv (measurable_one.indicator hA)]
  have hin : Measurable (Function.uncurry fun (x y : ℝ) => A.indicator (1 : ℝ → ℝ≥0∞) (x + y)) :=
    (measurable_one.indicator hA).comp (measurable_fst.add measurable_snd)
  rw [gaussianReal_of_var_ne_zero 0 hv, ← hg, lintegral_withDensity_eq_lintegral_mul _ hgm
    (Measurable.lintegral_prod_right hin)]
  simp only [Pi.mul_apply]
  have hj : Measurable (Function.uncurry fun (x z : ℝ) => g x * A.indicator 1 (x + z)) :=
    (hgm.comp measurable_fst).mul ((measurable_one.indicator hA).comp (measurable_fst.add measurable_snd))
  calc ∫⁻ x, g x * ∫⁻ z, A.indicator 1 (x + z) ∂m ∂volume
      = ∫⁻ x, ∫⁻ z, g x * A.indicator 1 (x + z) ∂m ∂volume := by
        congr 1; funext x
        have hmx : Measurable fun z : ℝ => A.indicator (1 : ℝ → ℝ≥0∞) (x + z) :=
          (measurable_one.indicator hA).comp (measurable_const.add measurable_id)
        exact (lintegral_const_mul _ hmx).symm
    _ = ∫⁻ z, ∫⁻ x, g x * A.indicator 1 (x + z) ∂volume ∂m := lintegral_lintegral_swap hj.aemeasurable
    _ = ∫⁻ z, ∫⁻ x, g (x - z) * A.indicator 1 x ∂volume ∂m := by
        congr 1; funext z
        rw [← lintegral_sub_right_eq_self (fun x => g x * A.indicator 1 (x + z)) z]
        simp only [sub_add_cancel]
    _ = ∫⁻ x, ∫⁻ z, g (x - z) * A.indicator 1 x ∂m ∂volume := by
        refine (lintegral_lintegral_swap ?_).symm
        exact ((hgm.comp (measurable_fst.sub measurable_snd)).mul
          ((measurable_one.indicator hA).comp measurable_fst)).aemeasurable
    _ = ∫⁻ x in A, ∫⁻ z, g (x - z) ∂m := by
        rw [← lintegral_indicator hA]
        congr 1; funext x
        by_cases hx : x ∈ A
        · simp [hx]
        · simp [hx]
    _ = ∫⁻ x in A, ENNReal.ofReal (qd v m x) := by
        congr 1; funext x; rw [hdens]

/-- The box indicator `1_{[−½,½]}`. -/
def boxInd (x : ℝ) : ℝ := (Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ => (1 : ℝ)) x

lemma measurable_boxInd : Measurable boxInd := measurable_const.indicator measurableSet_Icc

lemma boxInd_of_mem {x : ℝ} (hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) : boxInd x = 1 := by
  unfold boxInd; exact indicator_of_mem hx _

lemma boxInd_of_notMem {x : ℝ} (hx : x ∉ Icc (-(1 / 2 : ℝ)) (1 / 2)) : boxInd x = 0 := by
  unfold boxInd; exact indicator_of_notMem hx _

/-- `q_m` is bounded below on the box. -/
lemma qd_lower (v : ℝ≥0) (hv : v ≠ 0) (m : Measure ℝ) [IsProbabilityMeasure m] :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), c ≤ qd v m x := by
  obtain ⟨R, hR⟩ : ∃ R : ℕ, m (Icc (-(R : ℝ)) R) ≠ 0 := by
    by_contra h
    push Not at h
    have hU : (⋃ n : ℕ, Icc (-(n : ℝ)) n) = univ := by
      refine Set.eq_univ_of_forall fun x => ?_
      obtain ⟨n, hn⟩ := exists_nat_ge |x|
      exact Set.mem_iUnion.2 ⟨n, by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
    have := measure_iUnion_null h
    rw [hU, measure_univ] at this
    exact one_ne_zero this
  set I := Icc (-(R : ℝ)) R
  have hIpos : 0 < m.real I := by
    rw [measureReal_def]; exact ENNReal.toReal_pos hR (measure_ne_top _ _)
  refine ⟨m.real I * gaussianPDFReal 0 v (1 / 2 + R), mul_pos hIpos (gaussianPDFReal_pos 0 v _ hv), ?_⟩
  intro x hx
  unfold qd
  have h1 : ∫ z, I.indicator (fun _ => gaussianPDFReal 0 v (1 / 2 + R)) z ∂m ≤
      ∫ z, gaussianPDFReal 0 v (x - z) ∂m := by
    refine integral_mono ((integrable_const _).indicator measurableSet_Icc) (integrable_gauss_shift v m x)
      fun z => ?_
    by_cases hz : z ∈ I
    · rw [indicator_of_mem hz]
      refine gaussianPDFReal_anti v ?_
      obtain ⟨hx1, hx2⟩ := hx
      obtain ⟨hz1, hz2⟩ := hz
      rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / 2 + R), abs_le]
      constructor <;> linarith
    · rw [indicator_of_notMem hz]; exact gaussianPDFReal_nonneg 0 v _
  rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul] at h1
  exact h1

/-- Projection increases `q_m` on the box. -/
lemma qd_proj_ge (v : ℝ≥0) (m : Measure ℝ) [IsProbabilityMeasure m] {x : ℝ}
    (hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) : qd v m x ≤ qd v (m.map proj) x := by
  unfold qd
  have hmeas : AEStronglyMeasurable (fun z => gaussianPDFReal 0 v (x - z)) (m.map proj) :=
    ((measurable_gaussianPDFReal 0 v).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  rw [integral_map measurable_proj.aemeasurable hmeas]
  refine integral_mono (integrable_gauss_shift v m x) ?_ fun z => gaussianPDFReal_anti v (abs_sub_proj_le hx z)
  exact Integrable.of_mem_Icc 0 ((√(2 * Real.pi * v))⁻¹)
    ((measurable_gaussianPDFReal 0 v).comp (measurable_const.sub measurable_proj)).aemeasurable
    (ae_of_all _ fun z => ⟨gaussianPDFReal_nonneg 0 v _, gaussianPDFReal_le v _⟩)

lemma boxU_eq : boxU = volume.withDensity fun x => ENNReal.ofReal (boxInd x) :=
  StatFormal.Wave21a.boxU_eq_withDensity

lemma box_term_eq (v : ℝ≥0) (m : Measure ℝ) :
    (fun x => boxInd x * Real.log (boxInd x / qd v m x)) =
      (Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator fun x => Real.log (1 / qd v m x) := by
  funext x
  by_cases hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)
  · rw [boxInd_of_mem hx, indicator_of_mem hx, one_mul]
  · rw [boxInd_of_notMem hx, indicator_of_notMem hx, zero_mul]

lemma integrable_box_term {v : ℝ≥0} (hv : v ≠ 0) (m : Measure ℝ) [IsProbabilityMeasure m] :
    Integrable (fun x => boxInd x * Real.log (boxInd x / qd v m x)) volume := by
  obtain ⟨c, hc, hcq⟩ := qd_lower v hv m
  rw [box_term_eq, integrable_indicator_iff measurableSet_Icc]
  refine Measure.integrableOn_of_bounded (M := |Real.log c| + |Real.log ((√(2 * Real.pi * v))⁻¹)|)
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    ((measurable_const.div (measurable_qd v m)).log).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  refine ae_of_all _ fun x hx => ?_
  have hq1 := hcq x hx
  have hq2 : qd v m x ≤ (√(2 * Real.pi * v))⁻¹ := by
    unfold qd
    calc ∫ z, gaussianPDFReal 0 v (x - z) ∂m ≤ ∫ _z, (√(2 * Real.pi * v))⁻¹ ∂m :=
          integral_mono (integrable_gauss_shift v m x) (integrable_const _) fun z => gaussianPDFReal_le v _
      _ = _ := by simp
  have hqpos : 0 < qd v m x := lt_of_lt_of_le hc hq1
  rw [Real.norm_eq_abs, one_div, Real.log_inv, abs_neg]
  have h1 : Real.log c ≤ Real.log (qd v m x) := Real.log_le_log hc hq1
  have h2 : Real.log (qd v m x) ≤ Real.log ((√(2 * Real.pi * v))⁻¹) := Real.log_le_log hqpos hq2
  rw [abs_le]
  constructor <;> linarith [neg_abs_le (Real.log c), le_abs_self (Real.log ((√(2 * Real.pi * v))⁻¹)),
    abs_nonneg (Real.log c), abs_nonneg (Real.log ((√(2 * Real.pi * v))⁻¹))]

/-- `KL(U ‖ N(0,v) ∗ m) = ∫ 1_box log(1_box / q_m)`. -/
theorem klRef_boxU_conv {v : ℝ≥0} (hv : v ≠ 0) (m : Measure ℝ) [IsProbabilityMeasure m] :
    klRef boxU (gaussianReal 0 v ∗ m) = ((∫ x, boxInd x * Real.log (boxInd x / qd v m x) : ℝ) : EReal) := by
  obtain ⟨c, hc, hcq⟩ := qd_lower v hv m
  have hp0 : ∀ x, 0 ≤ boxInd x := fun x => indicator_nonneg (fun _ _ => zero_le_one) x
  have hpq : ∀ x, boxInd x ≠ 0 → 0 < qd v m x := by
    intro x hx
    have : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) := by
      by_contra h; exact hx (indicator_of_notMem h _)
    exact lt_of_lt_of_le hc (hcq x this)
  rw [boxU_eq, gauss_conv_eq hv m]
  exact StatFormal.Wave21a.klRef_withDensity volume measurable_boxInd (measurable_qd v m) hp0 (qd_nonneg v m) hpq
    (integrable_box_term hv m)

/-- **Projection onto the box**: `KL(U ‖ N(0,v) ∗ m∘proj⁻¹) ≤ KL(U ‖ N(0,v) ∗ m)`; the projected law is carried by
`[−½, ½]`. -/
theorem klRef_proj_le {v : ℝ≥0} (hv : v ≠ 0) (m : Measure ℝ) [IsProbabilityMeasure m] :
    klRef boxU (gaussianReal 0 v ∗ m.map proj) ≤ klRef boxU (gaussianReal 0 v ∗ m) ∧
      (m.map proj) (Icc (-(1 / 2 : ℝ)) (1 / 2))ᶜ = 0 := by
  have : IsProbabilityMeasure (m.map proj) :=
    ⟨by rw [Measure.map_apply measurable_proj MeasurableSet.univ]; simp⟩
  refine ⟨?_, ?_⟩
  · rw [klRef_boxU_conv hv, klRef_boxU_conv hv, EReal.coe_le_coe_iff]
    obtain ⟨c, hc, hcq⟩ := qd_lower v hv m
    refine integral_mono (integrable_box_term hv _) (integrable_box_term hv m) fun x => ?_
    by_cases hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)
    · rw [boxInd_of_mem hx, one_mul, one_mul, one_div, one_div, Real.log_inv, Real.log_inv, neg_le_neg_iff]
      exact Real.log_le_log (lt_of_lt_of_le hc (hcq x hx)) (qd_proj_ge v m hx)
    · rw [boxInd_of_notMem hx, zero_mul, zero_mul]
  · rw [Measure.map_apply measurable_proj measurableSet_Icc.compl]
    convert measure_empty (μ := m)
    refine Set.eq_empty_of_forall_notMem fun z hz => ?_
    exact hz (proj_mem z)

end StatFormal.WaveP2c
