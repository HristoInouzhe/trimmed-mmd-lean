import StatFormal.Archive.Wave23d.Statements
import Mathlib.Analysis.InnerProductSpace.Adjoint
import StatFormal.Archive.OTFD.Wave5a.RouteDepthRegions

/-!
# Route — R `thm:student` (ii) in `ℝ^K` (untrusted)

* For `v ≠ 0`, `⟨v, √W A Z⟩ = √W ⟨A^† v, Z⟩` and `⟨w, Z⟩/‖w‖ ~ N(0,1)` (`IsGaussian.map_eq_gaussianReal`,
  variance `‖innerSL w‖² = ‖w‖²`), so `μ_K{⟨v, z⟩ ≤ c} = F_{t_ν}(c/‖A^† v‖)`. By Cauchy–Schwarz
  `⟨v, u⟩ = ⟨A^† v, A^{-1}u⟩ ≥ −‖A^† v‖ ‖A^{-1}u‖`, attained at `A^† v = −A^{-1}u`; monotonicity of `F_{t_ν}` gives
  the depth formula.
* `‖A^{-1}(√W A Z)‖ = √W ‖Z‖`, and `√W‖Z‖ ≤ r ⟺ (‖Z‖²/K)/V ≤ r²/K` for every `V` (both sides hold when `V ≤ 0`).
* `β*`: the depth regions are sublevel sets of `‖A^{-1}u‖` (monotone `F_{t_ν}`), and right-continuity of the two
  distribution functions identifies the supremum.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Real
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave23d

open StatFormal.OTFD.Wave1 (truncK regionDepth tukeyDepth)
open StatFormal.OTFD.Wave5a (betaStar depthRegion)

variable {K : ℕ} {ν : ℝ}

local notation "E" K => EuclideanSpace ℝ (Fin K)

lemma isProb_gamma (hν : 0 < ν) : IsProbabilityMeasure (gammaMeasure (ν / 2) (ν / 2)) :=
  isProbabilityMeasure_gammaMeasure (by positivity) (by positivity)

lemma gamma_Iic_zero : gammaMeasure (ν / 2) (ν / 2) (Iic 0) = 0 := by
  have h1 : gammaMeasure (ν / 2) (ν / 2) (Iio 0) = 0 := by
    rw [gammaMeasure, withDensity_apply _ measurableSet_Iio]
    exact lintegral_gammaPDF_of_nonpos le_rfl
  have h2 : gammaMeasure (ν / 2) (ν / 2) {0} = 0 :=
    (withDensity_absolutelyContinuous _ _) (Real.volume_singleton)
  refine measure_mono_null (fun x hx => ?_) (measure_union_null h1 h2)
  rcases (mem_Iic.1 hx).lt_or_eq with h | h
  · exact Or.inl h
  · exact Or.inr h

lemma measurable_tmap : Measurable fun p : ℝ × ℝ => p.1 / √p.2 :=
  measurable_fst.div measurable_snd.sqrt

lemma measurable_studentMap (A : (E K) ≃L[ℝ] (E K)) :
    Measurable fun p : (E K) × ℝ => (√p.2)⁻¹ • A p.1 :=
  (measurable_snd.sqrt.inv).smul (A.continuous.measurable.comp measurable_fst)

lemma isProb_tLaw (hν : 0 < ν) : IsProbabilityMeasure (tLaw ν) := by
  have := isProb_gamma hν
  unfold tLaw; infer_instance

lemma isProb_studentLaw (hν : 0 < ν) (A : (E K) ≃L[ℝ] (E K)) : IsProbabilityMeasure (studentLaw K ν A) := by
  have := isProb_gamma hν
  unfold studentLaw; infer_instance

/-- `⟨w, Z⟩/‖w‖ ~ N(0,1)` for `Z` standard Gaussian. -/
lemma stdGaussian_map_inner {w : E K} (hw : w ≠ 0) :
    (stdGaussian (E K)).map (fun z => ⟪w, z⟫ / ‖w‖) = gaussianReal 0 1 := by
  set L : StrongDual ℝ (E K) := ‖w‖⁻¹ • innerSL ℝ w
  have hL : (fun z => ⟪w, z⟫ / ‖w‖) = ⇑L := by
    ext z; simp [L, innerSL_apply_apply, div_eq_inv_mul]
  rw [hL, IsGaussian.map_eq_gaussianReal L, integral_strongDual_stdGaussian, variance_dual_stdGaussian]
  congr 1
  have : ‖L‖ = 1 := by
    simp only [L, norm_smul, norm_inv, norm_norm, innerSL_apply_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.2 hw)
  rw [this]; simp

/-- `t`-probabilities from the law: `tLaw(Iic x) = F_{t_ν}(x)`. -/
lemma tLaw_Iic (hν : 0 < ν) (x : ℝ) : tLaw ν (Iic x) = ENNReal.ofReal (tCDF ν x) := by
  have := isProb_tLaw hν
  rw [tCDF, cdf_eq_real, ofReal_measureReal]

/-- The adjoint of an invertible map has a right inverse. -/
lemma adjoint_symm_adjoint (A : (E K) ≃L[ℝ] (E K)) (x : E K) :
    ContinuousLinearMap.adjoint (A : (E K) →L[ℝ] (E K))
      (ContinuousLinearMap.adjoint (A.symm : (E K) →L[ℝ] (E K)) x) = x := by
  have h : (A.symm : (E K) →L[ℝ] (E K)).comp (A : (E K) →L[ℝ] (E K)) = ContinuousLinearMap.id ℝ _ := by
    ext y; simp
  have := ContinuousLinearMap.adjoint_comp (A.symm : (E K) →L[ℝ] (E K)) (A : (E K) →L[ℝ] (E K))
  rw [h, ContinuousLinearMap.adjoint_id] at this
  have := congrArg (fun T => T x) this
  simpa using this.symm

lemma inner_A (A : (E K) ≃L[ℝ] (E K)) (v x : E K) :
    ⟪v, A x⟫ = ⟪ContinuousLinearMap.adjoint (A : (E K) →L[ℝ] (E K)) v, x⟫ :=
  (ContinuousLinearMap.adjoint_inner_left (A : (E K) →L[ℝ] (E K)) x v).symm

lemma adjoint_ne_zero (A : (E K) ≃L[ℝ] (E K)) {v : E K} (hv : v ≠ 0) :
    ContinuousLinearMap.adjoint (A : (E K) →L[ℝ] (E K)) v ≠ 0 := by
  intro h
  have := inner_A A v (A.symm v)
  rw [h, inner_zero_left, ContinuousLinearEquiv.apply_symm_apply, real_inner_self_eq_norm_sq] at this
  exact hv (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this))

/-- Halfspace probabilities: `μ_K{⟨v, z⟩ ≤ c} = F_{t_ν}(c/‖A^† v‖)`. -/
lemma student_halfspace (hν : 0 < ν) (A : (E K) ≃L[ℝ] (E K)) {v : E K} (hv : v ≠ 0) (c : ℝ) :
    studentLaw K ν A {z | ⟪v, z⟫ ≤ c} =
      ENNReal.ofReal (tCDF ν (c / ‖ContinuousLinearMap.adjoint (A : (E K) →L[ℝ] (E K)) v‖)) := by
  have := isProb_gamma hν
  set w := ContinuousLinearMap.adjoint (A : (E K) →L[ℝ] (E K)) v
  have hw : w ≠ 0 := adjoint_ne_zero A hv
  have hw0 : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hmeasS : MeasurableSet {z : E K | ⟪v, z⟫ ≤ c} :=
    measurableSet_le (continuous_const.inner continuous_id).measurable measurable_const
  set g : (E K) × ℝ → ℝ × ℝ := Prod.map (fun z => ⟪w, z⟫ / ‖w‖) id
  have hg : Measurable g :=
    (((continuous_const.inner continuous_id).div_const _).measurable).prodMap measurable_id
  have hpre : (fun p : (E K) × ℝ => (√p.2)⁻¹ • A p.1) ⁻¹' {z | ⟪v, z⟫ ≤ c} =
      g ⁻¹' ((fun q : ℝ × ℝ => q.1 / √q.2) ⁻¹' Iic (c / ‖w‖)) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Iic, g, Prod.map_fst, Prod.map_snd, id,
      inner_smul_right, inner_A A v]
    rw [show ⟪w, p.1⟫ / ‖w‖ / √p.2 = (√p.2)⁻¹ * ⟪w, p.1⟫ / ‖w‖ by ring, div_le_div_iff_of_pos_right hw0]
  rw [studentLaw, Measure.map_apply (measurable_studentMap A) hmeasS, hpre,
    ← Measure.map_apply hg (measurable_tmap measurableSet_Iic)]
  have hf : Measurable (fun z : E K => ⟪w, z⟫ / ‖w‖) :=
    ((continuous_const.inner continuous_id).div_const _).measurable
  rw [show g = Prod.map (fun z => ⟪w, z⟫ / ‖w‖) id from rfl, ← Measure.map_prod_map _ _ hf measurable_id,
    stdGaussian_map_inner hw, Measure.map_id, ← Measure.map_apply measurable_tmap measurableSet_Iic]
  exact tLaw_Iic hν _

theorem student_depth_thm : Claims.student_depth := by
  intro K ν A hK hν u
  have := isProb_gamma hν
  have hset : ∀ v : E K, {z : E K | ⟪v, z - u⟫ ≤ 0} = {z | ⟪v, z⟫ ≤ ⟪v, u⟫} := by
    intro v; ext z; simp [inner_sub_right]
  unfold tukeyDepth
  simp_rw [hset]
  apply le_antisymm
  · -- the infimum is attained
    rcases eq_or_ne u 0 with rfl | hu
    · set v : E K := EuclideanSpace.single ⟨0, hK⟩ 1
      have hv : v ≠ 0 := by simp [v]
      refine (iInf₂_le v hv).trans (le_of_eq ?_)
      rw [student_halfspace hν A hv]; simp
    · set x := A.symm u
      have hx : x ≠ 0 := by simpa [x] using hu
      set v : E K := -ContinuousLinearMap.adjoint (A.symm : (E K) →L[ℝ] (E K)) x
      have hAv : ContinuousLinearMap.adjoint (A : (E K) →L[ℝ] (E K)) v = -x := by
        simp only [v, map_neg, adjoint_symm_adjoint]
      have hv : v ≠ 0 := by
        intro h; rw [h, map_zero] at hAv; exact hx (neg_eq_zero.1 hAv.symm)
      refine (iInf₂_le v hv).trans (le_of_eq ?_)
      rw [student_halfspace hν A hv, hAv, norm_neg]
      congr 2
      have hu' : u = A x := by simp [x]
      rw [hu', inner_A A v, hAv, inner_neg_left, real_inner_self_eq_norm_sq]
      have : 0 < ‖x‖ := norm_pos_iff.2 hx
      field_simp
  · refine le_iInf₂ fun v hv => ?_
    rw [student_halfspace hν A hv]
    refine ENNReal.ofReal_le_ofReal ((cdf (tLaw ν)).mono ?_)
    set w := ContinuousLinearMap.adjoint (A : (E K) →L[ℝ] (E K)) v
    have hw0 : 0 < ‖w‖ := norm_pos_iff.2 (adjoint_ne_zero A hv)
    rw [le_div_iff₀ hw0]
    have e : ⟪v, u⟫ = ⟪w, A.symm u⟫ := by
      conv_lhs => rw [show u = A (A.symm u) by simp]
      exact inner_A A v _
    rw [e]
    have := abs_real_inner_le_norm w (A.symm u)
    have := neg_abs_le ⟪w, A.symm u⟫
    nlinarith

/-! ### Content of the ellipsoids -/

lemma isProb_fLaw (hν : 0 < ν) : IsProbabilityMeasure (fLaw K ν) := by
  have := isProb_gamma hν
  unfold fLaw; infer_instance

lemma measurable_fmap : Measurable fun p : (E K) × ℝ => ‖p.1‖ ^ 2 / K / p.2 :=
  ((measurable_fst.norm.pow_const 2).div_const _).div measurable_snd

lemma fLaw_Iic (hν : 0 < ν) (x : ℝ) : fLaw K ν (Iic x) = ENNReal.ofReal (fCDF K ν x) := by
  have := isProb_fLaw (K := K) hν
  rw [fCDF, cdf_eq_real, ofReal_measureReal]

lemma student_content_aux (hK : 0 < K) (hν : 0 < ν) (A : (E K) ≃L[ℝ] (E K)) {r : ℝ} (hr : 0 ≤ r) :
    studentLaw K ν A {u | ‖A.symm u‖ ≤ r} = ENNReal.ofReal (fCDF K ν (r ^ 2 / K)) := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hmeas : MeasurableSet {u : E K | ‖A.symm u‖ ≤ r} :=
    measurableSet_le (A.symm.continuous.norm.measurable) measurable_const
  rw [studentLaw, Measure.map_apply (measurable_studentMap A) hmeas, ← fLaw_Iic hν, fLaw,
    Measure.map_apply measurable_fmap measurableSet_Iic]
  congr 1
  ext p
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Iic, map_smul, ContinuousLinearEquiv.symm_apply_apply,
    norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)]
  rcases le_or_gt p.2 0 with hv | hv
  · rw [Real.sqrt_eq_zero'.2 hv, inv_zero, zero_mul]
    have : ‖p.1‖ ^ 2 / K / p.2 ≤ 0 := div_nonpos_iff.2 (Or.inl ⟨by positivity, hv⟩)
    constructor
    · intro _; exact this.trans (by positivity)
    · intro _; exact hr
  · have hs : 0 < √p.2 := Real.sqrt_pos.2 hv
    rw [inv_mul_le_iff₀ hs, div_div, mul_comm (K : ℝ), ← div_div, div_le_div_iff_of_pos_right hK',
      div_le_iff₀ hv]
    have e : (√p.2 * r) ^ 2 = r ^ 2 * p.2 := by rw [mul_pow, Real.sq_sqrt hv.le]; ring
    constructor
    · intro h
      have := pow_le_pow_left₀ (norm_nonneg _) h 2
      linarith
    · intro h
      have h2 : ‖p.1‖ ^ 2 ≤ (√p.2 * r) ^ 2 := by linarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

theorem student_content_thm : Claims.student_content := by
  intro K ν A hK hν r hr
  exact student_content_aux hK hν A hr

/-! ### The `F` quantile -/

lemma fCDF_neg (hν : 0 < ν) {x : ℝ} (hx : x < 0) : fCDF K ν x = 0 := by
  have := isProb_gamma hν
  have h0 : fLaw K ν (Iic x) = 0 := by
    rw [fLaw, Measure.map_apply measurable_fmap measurableSet_Iic]
    refine measure_mono_null (t := univ ×ˢ Iic 0) ?_ ?_
    · intro p hp
      simp only [Set.mem_preimage, Set.mem_Iic] at hp
      refine ⟨mem_univ _, ?_⟩
      by_contra h
      simp only [Set.mem_Iic, not_le] at h
      have : 0 ≤ ‖p.1‖ ^ 2 / K / p.2 := by positivity
      linarith
    · rw [Measure.prod_prod, gamma_Iic_zero, mul_zero]
  have := fLaw_Iic (K := K) hν x
  rw [h0] at this
  have h1 : 0 ≤ fCDF K ν x := cdf_nonneg _ _
  have h2 := (ENNReal.ofReal_eq_zero.1 this.symm)
  linarith

lemma fQuant_spec (hν : 0 < ν) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    0 ≤ fQuant K ν p ∧ p ≤ fCDF K ν (fQuant K ν p) ∧ ∀ x, x < fQuant K ν p → fCDF K ν x < p := by
  have := isProb_fLaw (K := K) hν
  set S := {x | p ≤ fCDF K ν x}
  have hne : S.Nonempty := by
    obtain ⟨x, hx⟩ := ((tendsto_cdf_atTop (μ := fLaw K ν)).eventually (lt_mem_nhds hp1)).exists
    exact ⟨x, hx.le⟩
  have hlow : ∀ x ∈ S, 0 ≤ x := by
    intro x hx
    by_contra h
    push Not at h
    have := fCDF_neg (K := K) hν h
    simp only [S, Set.mem_ofPred_eq] at hx
    linarith
  have hbdd : BddBelow S := ⟨0, hlow⟩
  refine ⟨le_csInf hne hlow, ?_, ?_⟩
  · -- right-continuity
    have hrc := (cdf (fLaw K ν)).right_continuous (fQuant K ν p)
    have hev : ∀ᶠ x in 𝓝[>] (fQuant K ν p), p ≤ cdf (fLaw K ν) x := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      obtain ⟨s, hs, hsx⟩ := exists_lt_of_csInf_lt hne hx
      exact hs.trans ((cdf (fLaw K ν)).mono hsx.le)
    exact ge_of_tendsto (hrc.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)) hev
  · intro x hx
    by_contra h
    push Not at h
    exact absurd (csInf_le hbdd h) (not_le.2 hx)

/-! ### The robustness index -/

section Beta
variable (hK : 0 < K) (hν : 0 < ν) (A : (E K) ≃L[ℝ] (E K)) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
include hK hν hp hp1

lemma rp_sq : √(K * fQuant K ν p) ^ 2 / K = fQuant K ν p := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  rw [Real.sq_sqrt (mul_nonneg hK'.le (fQuant_spec hν hp hp1).1)]; field_simp

lemma content_rp : ENNReal.ofReal p ≤ studentLaw K ν A {u | ‖A.symm u‖ ≤ √(K * fQuant K ν p)} := by
  rw [student_content_aux hK hν A (Real.sqrt_nonneg _), rp_sq hK hν hp hp1]
  exact ENNReal.ofReal_le_ofReal (fQuant_spec hν hp hp1).2.1

lemma content_lt {r : ℝ} (hr : 0 ≤ r) (hrp : r < √(K * fQuant K ν p)) :
    studentLaw K ν A {u | ‖A.symm u‖ ≤ r} < ENNReal.ofReal p := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  rw [student_content_aux hK hν A hr, ENNReal.ofReal_lt_ofReal_iff hp]
  refine (fQuant_spec hν hp hp1).2.2 _ ?_
  rw [← rp_sq hK hν hp hp1]
  exact div_lt_div_of_pos_right (pow_lt_pow_left₀ hrp hr two_ne_zero) hK'

lemma depth_eq (u : E K) : tukeyDepth (studentLaw K ν A) u = ENNReal.ofReal (tCDF ν (-‖A.symm u‖)) :=
  student_depth_thm K ν A hK hν u

lemma beta_eq : betaStar (studentLaw K ν A) (ENNReal.ofReal p) =
    ENNReal.ofReal (tCDF ν (-√(K * fQuant K ν p))) := by
  set rp := √(K * fQuant K ν p)
  set β0 := ENNReal.ofReal (tCDF ν (-rp))
  have hsub : {u : E K | ‖A.symm u‖ ≤ rp} ⊆ depthRegion (studentLaw K ν A) β0 := by
    intro u hu
    simp only [depthRegion, Set.mem_ofPred_eq, depth_eq hK hν A hp hp1]
    exact ENNReal.ofReal_le_ofReal ((cdf (tLaw ν)).mono (by simp only [Set.mem_ofPred_eq] at hu; linarith))
  apply le_antisymm
  · refine sSup_le fun α hα => ?_
    simp only [Set.mem_ofPred_eq] at hα
    by_contra hlt
    push Not at hlt
    -- right-continuity of `F_t` at `−r_p`
    have hrc := (cdf (tLaw ν)).right_continuous (-rp)
    have hev : ∀ᶠ x in 𝓝[>] (-rp), ENNReal.ofReal (tCDF ν x) < α := by
      have := ((ENNReal.continuous_ofReal.tendsto _).comp
        (hrc.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self))).eventually (gt_mem_nhds hlt)
      exact this
    obtain ⟨x, hx, hxgt⟩ := (hev.and self_mem_nhdsWithin).exists
    have hD : depthRegion (studentLaw K ν A) α ⊆ {u | ‖A.symm u‖ ≤ -x} := by
      intro u hu
      simp only [depthRegion, Set.mem_ofPred_eq, depth_eq hK hν A hp hp1] at hu
      simp only [Set.mem_ofPred_eq]
      by_contra h
      push Not at h
      have : tCDF ν (-‖A.symm u‖) ≤ tCDF ν x := (cdf (tLaw ν)).mono (by linarith)
      have := ENNReal.ofReal_le_ofReal this
      exact absurd (hu.trans this) (not_le.2 hx)
    rcases lt_or_ge (-x) 0 with hneg | hnn
    · have : depthRegion (studentLaw K ν A) α = ∅ := by
        refine Set.eq_empty_of_forall_notMem fun u hu => ?_
        have : ‖A.symm u‖ ≤ -x := hD hu
        linarith [norm_nonneg (A.symm u)]
      rw [this, measure_empty] at hα
      exact absurd hα (not_le.2 (ENNReal.ofReal_pos.2 hp))
    · have hlt' := content_lt hK hν A hp hp1 hnn (by linarith)
      exact absurd (hα.trans (measure_mono hD)) (not_le.2 hlt')
  · exact le_sSup ((content_rp hK hν A hp hp1).trans (measure_mono hsub))

end Beta

theorem student_beta_thm : Claims.student_beta := by
  intro K ν A p hK hν hp hp1
  exact beta_eq hK hν A hp hp1

theorem student_region_thm : Claims.student_region := by
  intro K ν A p hK hν hp hp1
  intro Ell
  have hreg : regionDepth (studentLaw K ν A) Ell = betaStar (studentLaw K ν A) (ENNReal.ofReal p) := by
    rw [beta_eq hK hν A hp hp1]
    set rp := √(K * fQuant K ν p)
    apply le_antisymm
    · -- a boundary point `u = A (r_p e)`
      set e : E K := EuclideanSpace.single ⟨0, hK⟩ 1
      have he : ‖e‖ = 1 := by simp [e]
      set u : E K := A (rp • e)
      have hu : u ∈ Ell := by
        show ‖A.symm u‖ ≤ rp
        simp [u, norm_smul, he, abs_of_nonneg (show 0 ≤ rp from Real.sqrt_nonneg _)]
      refine (iInf₂_le u hu).trans (le_of_eq ?_)
      rw [depth_eq hK hν A hp hp1]
      simp [u, norm_smul, he, abs_of_nonneg (Real.sqrt_nonneg _), rp]
    · refine le_iInf₂ fun u hu => ?_
      rw [depth_eq hK hν A hp hp1]
      exact ENNReal.ofReal_le_ofReal ((cdf (tLaw ν)).mono (by have : ‖A.symm u‖ ≤ rp := hu; linarith))
  refine ⟨content_rp hK hν A hp hp1, hreg, fun B hB => ?_⟩
  rw [hreg]
  exact StatFormal.OTFD.Wave5a.depth_regions_optimal K _ _ B hB

end StatFormal.Wave23d
