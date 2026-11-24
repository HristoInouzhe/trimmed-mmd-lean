import StatFormal.Archive.Wave29f.Statements
import StatFormal.Lib.StudentRef.Basic
import StatFormal.Archive.WaveP2b.RouteAC
import StatFormal.Archive.WaveP2b.RouteRefsGauss
import StatFormal.Archive.Wave23d.RouteNames
import StatFormal.Archive.OTFD.Wave12a.RouteEntropic
import StatFormal.Archive.WaveP3a.RouteBand
import TauCeti.Probability.Quantile

/-!
# Route — R `thm:student` (ii) outlyingness and (iii) breakdown, in `ℝ^K` (untrusted)

* Outlyingness: under `U = (√V)⁻¹ A Z`, `‖A⁻¹U‖²/K = ‖Z‖²/(K V)` (`V ≥ 0` a.s.), whose law is the frozen `fLaw`;
  `fLaw` is atomless (Fubini: for `z ≠ 0` the section `{v : ‖z‖²/(Kv) = c}` has at most two points, and
  `N(0, I){0} = 0`), so the probability integral transform (Tau Ceti `cdf_map_eq_volume_restrict`) gives `Unif[0,1]`.
* Breakdown: the Student law is absolutely continuous (`N(0, I) ≪ Leb`, WaveP2b `gaussian_ac`, and linear
  isomorphisms preserve Lebesgue-null sets) and has a finite second moment for `ν > 2`
  (`E‖(√V)⁻¹AZ‖² ≤ E[1/V] ‖A‖² E‖Z‖²`, inverse-gamma mean); the ellipsoid is the preimage of a closed ball under
  the homeomorphism `A⁻¹`. Then the certified OTFD Wave 12a `region_bp_unconditional` (region), WaveP3a
  `band_bp_unconditional` (bands) and Wave 23d `student_region`, `student_beta` give the bounds.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave29f

open StatFormal.OTFD.WaveL1 (Euc)
open StatFormal.Wave23d (studentLaw tCDF fCDF fQuant fLaw)

section Std
variable {K : ℕ}

lemma stdGaussian_inj : ∀ v : Euc K, v ≠ 0 → 0 < Var[fun z => ⟪v, z⟫_ℝ; stdGaussian (Euc K)] := by
  intro v hv
  have h := variance_dual_stdGaussian (E := Euc K) (innerSL ℝ v)
  have hf : (fun z : Euc K => ⟪v, z⟫_ℝ) = ⇑(innerSL ℝ v) := by funext z; simp
  rw [hf, h, innerSL_apply_norm]
  exact pow_pos (norm_pos_iff.2 hv) 2

lemma stdGaussian_ac : stdGaussian (Euc K) ≪ volume :=
  StatFormal.WaveP2b.gaussian_ac _ integral_id_stdGaussian stdGaussian_inj

lemma stdGaussian_zero (hK : 0 < K) : stdGaussian (Euc K) {0} = 0 := by
  have : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  exact stdGaussian_ac (measure_singleton 0)

lemma gamma_finite_null {ν : ℝ} (s : Set ℝ) (hs : s.Finite) : gammaMeasure (ν / 2) (ν / 2) s = 0 :=
  (withDensity_absolutelyContinuous _ _) (hs.measure_zero _)

lemma gamma_Iio_zero {ν : ℝ} : gammaMeasure (ν / 2) (ν / 2) (Iio 0) = 0 := by
  rw [gammaMeasure, withDensity_apply _ measurableSet_Iio]
  exact lintegral_gammaPDF_of_nonpos le_rfl

lemma ae_snd_nonneg {ν : ℝ} :
    ∀ᵐ p ∂((stdGaussian (Euc K)).prod (gammaMeasure (ν / 2) (ν / 2))), 0 ≤ p.2 := by
  rw [ae_iff]
  have : {a : Euc K × ℝ | ¬ 0 ≤ a.2} = univ ×ˢ Iio 0 := by ext p; simp
  rw [this, Measure.prod_prod, gamma_Iio_zero, mul_zero]

/-- `F_{K,ν}` is atomless. -/
lemma fLaw_noAtoms (hK : 0 < K) {ν : ℝ} (hν : 0 < ν) : NullSingletonClass (fLaw K ν) := by
  have := Wave23d.isProb_gamma hν
  refine ⟨fun c => ?_⟩
  have hf : Measurable fun p : Euc K × ℝ => ‖p.1‖ ^ 2 / K / p.2 := Wave23d.measurable_fmap
  rw [fLaw, Measure.map_apply hf (measurableSet_singleton c), Measure.prod_apply (hf (measurableSet_singleton c))]
  have hae : ∀ᵐ z ∂(stdGaussian (Euc K)),
      gammaMeasure (ν / 2) (ν / 2) (Prod.mk z ⁻¹' ((fun p : Euc K × ℝ => ‖p.1‖ ^ 2 / K / p.2) ⁻¹' {c})) = 0 := by
    have h0 : ∀ᵐ z ∂(stdGaussian (Euc K)), z ≠ 0 := by
      rw [ae_iff]; simpa using stdGaussian_zero hK
    filter_upwards [h0] with z hz
    refine measure_mono_null (t := {0, ‖z‖ ^ 2 / K / c}) (fun v hv => ?_) (gamma_finite_null _ (by simp))
    simp only [mem_preimage, mem_singleton_iff] at hv
    by_cases hv0 : v = 0
    · exact Or.inl hv0
    · right
      have hK' : (0 : ℝ) < K := by exact_mod_cast hK
      have hn : 0 < ‖z‖ ^ 2 / K := by have := norm_pos_iff.2 hz; positivity
      have hc : c ≠ 0 := by rw [← hv]; exact div_ne_zero hn.ne' hv0
      rw [← hv, mem_singleton_iff]; field_simp
  exact (lintegral_congr_ae hae).trans lintegral_zero

end Std

/-- **Outlyingness is uniform.** -/
theorem student_outlyingness : Claims.student_outlyingness := by
  intro K ν A hK hν
  have := Wave23d.isProb_gamma hν
  have := Wave23d.isProb_fLaw (K := K) hν
  have := fLaw_noAtoms hK hν
  have hcm : Measurable (cdf (fLaw K ν)) := (cdf (fLaw K ν)).mono.measurable
  have hg : Measurable fun u : Euc K => fCDF K ν (‖A.symm u‖ ^ 2 / K) :=
    hcm.comp ((A.symm.continuous.norm.pow 2).div_const _).measurable
  rw [studentLaw, Measure.map_map hg (Wave23d.measurable_studentMap A)]
  have hae : (fun u : Euc K => fCDF K ν (‖A.symm u‖ ^ 2 / K)) ∘ (fun p : Euc K × ℝ => (√p.2)⁻¹ • A p.1)
      =ᵐ[(stdGaussian (Euc K)).prod (gammaMeasure (ν / 2) (ν / 2))]
      (cdf (fLaw K ν)) ∘ (fun p : Euc K × ℝ => ‖p.1‖ ^ 2 / K / p.2) := by
    filter_upwards [ae_snd_nonneg] with p hp
    simp only [Function.comp_apply, map_smul, ContinuousLinearEquiv.symm_apply_apply, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs, inv_pow, Real.sq_sqrt hp]
    unfold fCDF
    congr 1
    ring
  rw [Measure.map_congr hae, ← Measure.map_map hcm Wave23d.measurable_fmap]
  exact MeasureTheory.Measure.cdf_map_eq_volume_restrict (fLaw K ν)

section Break
variable {K : ℕ}

/-- The Student law is absolutely continuous. -/
lemma studentLaw_ac {ν : ℝ} (hν : 0 < ν) (A : Euc K ≃L[ℝ] Euc K) : studentLaw K ν A ≪ volume := by
  have := Wave23d.isProb_gamma hν
  refine Measure.AbsolutelyContinuous.mk fun N hN hN0 => ?_
  have hs := Wave23d.measurable_studentMap A
  rw [studentLaw, Measure.map_apply hs hN, Measure.prod_apply_symm (hs hN)]
  have hae : ∀ᵐ v ∂(gammaMeasure (ν / 2) (ν / 2)),
      stdGaussian (Euc K) ((fun z => (z, v)) ⁻¹' ((fun p : Euc K × ℝ => (√p.2)⁻¹ • A p.1) ⁻¹' N)) = 0 := by
    have hpos : ∀ᵐ v ∂(gammaMeasure (ν / 2) (ν / 2)), 0 < v := by
      rw [ae_iff]
      refine measure_mono_null (fun v hv => ?_) (Wave23d.gamma_Iic_zero (ν := ν))
      simpa using hv
    filter_upwards [hpos] with v hv
    have hc : (√v)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 hv).ne'
    set S : Euc K ≃L[ℝ] Euc K := (LinearEquiv.smulOfNeZero ℝ (Euc K) _ hc).toContinuousLinearEquiv
    have hset : (fun z => (z, v)) ⁻¹' ((fun p : Euc K × ℝ => (√p.2)⁻¹ • A p.1) ⁻¹' N) = A ⁻¹' (S ⁻¹' N) := by
      ext z; rfl
    rw [hset]
    refine stdGaussian_ac ?_
    rw [Measure.addHaar_preimage_continuousLinearEquiv, Measure.addHaar_preimage_continuousLinearEquiv, hN0,
      mul_zero, mul_zero]
  exact (lintegral_congr_ae hae).trans lintegral_zero

/-- The Student law has a finite second moment for `ν > 2`. -/
lemma studentLaw_mom2 {ν : ℝ} (hν : 2 < ν) (A : Euc K ≃L[ℝ] Euc K) :
    ∫⁻ u, ‖u‖ₑ ^ 2 ∂(studentLaw K ν A) < ⊤ := by
  have hν0 : 0 < ν := by linarith
  have := Wave23d.isProb_gamma hν0
  rw [studentLaw, lintegral_map (by fun_prop) (Wave23d.measurable_studentMap A)]
  have hle : ∀ p : Euc K × ℝ, ‖(√p.2)⁻¹ • A p.1‖ₑ ^ 2 ≤
      (‖(A : Euc K →L[ℝ] Euc K)‖ₑ ^ 2 * ‖p.1‖ₑ ^ 2) * ENNReal.ofReal p.2⁻¹ := by
    intro p
    rw [enorm_smul, mul_pow, mul_comm]
    refine mul_le_mul' ?_ ?_
    · rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) ((A : Euc K →L[ℝ] Euc K).le_opENorm p.1) 2
    · rw [Real.enorm_eq_ofReal (inv_nonneg.2 (Real.sqrt_nonneg _)), ← ENNReal.ofReal_pow
        (inv_nonneg.2 (Real.sqrt_nonneg _)), inv_pow]
      rcases le_or_gt 0 p.2 with h | h
      · rw [Real.sq_sqrt h]
      · rw [Real.sqrt_eq_zero'.2 h.le]; simp
  refine (lintegral_mono hle).trans_lt ?_
  rw [lintegral_prod_mul (f := fun x : Euc K => ‖(A : Euc K →L[ℝ] Euc K)‖ₑ ^ 2 * ‖x‖ₑ ^ 2)
    (g := fun v : ℝ => ENNReal.ofReal v⁻¹) (by fun_prop) (by fun_prop), lintegral_const_mul _ (by fun_prop),
    StatFormal.StudentRef.lintegral_inv_gammaMeasure (by linarith) (by linarith)]
  refine ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) ?_) ENNReal.ofReal_lt_top
  exact StatFormal.WaveP2b.lintegral_sq_lt_top_of_memLp IsGaussian.memLp_two_id

lemma ellipsoid_compact (A : Euc K ≃L[ℝ] Euc K) (r : ℝ) : IsCompact {u : Euc K | ‖A.symm u‖ ≤ r} := by
  have : {u : Euc K | ‖A.symm u‖ ≤ r} = A.symm.toHomeomorph ⁻¹' Metric.closedBall 0 r := by
    ext u; simp
  rw [this, Homeomorph.isCompact_preimage]
  exact isCompact_closedBall 0 r

end Break

open StatFormal.OTFD.Wave6b (EntSetting) in
theorem student_breakdown : Claims.student_breakdown := by
  intro K n ν ε p A fsel Z hK hn hν hε hpot hp hp1
  have hν0 : 0 < ν := by linarith
  have := Wave23d.isProb_studentLaw (K := K) hν0 A
  set r := √(K * fQuant K ν p)
  have hcomp := ellipsoid_compact A r
  have hne : {u : Euc K | ‖A.symm u‖ ≤ r}.Nonempty :=
    ⟨0, by simp only [mem_setOf_eq, map_zero, norm_zero]; exact Real.sqrt_nonneg _⟩
  have hset : EntSetting (studentLaw K ν A) ε fsel := ⟨hε, studentLaw_mom2 hν A, hpot⟩
  obtain ⟨hlo, hhi⟩ := StatFormal.OTFD.Wave12a.region_bp_unconditional K n (studentLaw K ν A) ε fsel Z
    {u : Euc K | ‖A.symm u‖ ≤ r} hK hn (studentLaw_ac hν0 A) hset hcomp hne
  have hreg := (StatFormal.Wave23d.student_region K ν A p hK hν0 hp hp1).2.1
  have hbeta := StatFormal.Wave23d.student_beta K ν A p hK hν0 hp hp1
  have hdepth : (StatFormal.OTFD.Wave1.regionDepth (studentLaw K ν A) {u : Euc K | ‖A.symm u‖ ≤ r}).toReal =
      tCDF ν (-r) := by
    have h0 : 0 ≤ tCDF ν (-r) := by unfold tCDF; exact cdf_nonneg _ _
    rw [hreg, hbeta, ENNReal.toReal_ofReal h0]
  rw [hdepth] at hlo hhi
  refine ⟨hcomp, hne, hlo, hhi, fun 𝒯 e hbdd hspan => ?_⟩
  obtain ⟨blo, bhi⟩ := StatFormal.WaveP3a.band_bp_unconditional K n 𝒯 (studentLaw K ν A) ε fsel Z
    {u : Euc K | ‖A.symm u‖ ≤ r} e hK hn (studentLaw_ac hν0 A) hset hcomp hne hbdd hspan
  rw [hdepth] at blo bhi
  exact ⟨blo, bhi⟩

end StatFormal.Wave29f
