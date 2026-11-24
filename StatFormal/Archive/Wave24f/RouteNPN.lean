import StatFormal.Archive.Wave24f.RouteCopbary
import TauCeti.Probability.Cdf

/-!
# Route — SB `cor:field-npn`, exactness (untrusted)

* A linear image of a Gaussian is Gaussian: `A # N(0, S) = N(0, A S Aᵀ)` (`IsGaussian.ext`: same mean `0`, and the
  covariance of the image is `⟨Aᵀu, S Aᵀv⟩`).
* With `s = R^{1/2}` (symmetric, invertible for `R ≻ 0`): `s⁻¹ R s⁻¹ = 1` and `(R_ν^{1/2} s⁻¹) R_s (R_ν^{1/2} s⁻¹)ᵀ = R_ν`.
* For the target: `y_i = G_i^{-1}(Φ(Φ^{-1}(G_i(y_i))))` for `ν`-a.e. `y` (`G_i(Y_i)` is uniform for continuous `G_i`,
  `Φ ∘ Φ^{-1} = id` a.e. on `[0, 1]`, `G_i^{-1} ∘ G_i = id` `ν_i`-a.e.; Tau Ceti), so `ν = (G^{-1} ∘ Φ) # N(0, R_ν)`.
-/

noncomputable section
open MeasureTheory Set Filter Topology ProbabilityTheory Matrix
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace

namespace StatFormal.Wave24f

open StatFormal.OTFD.WaveL1 (Euc)

variable {d : ℕ}

lemma mvG_map (A S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) :
    (multivariateGaussian 0 S).map (toEuclideanCLM (𝕜 := ℝ) A) = multivariateGaussian 0 (A * S * Aᵀ) := by
  have hS' : (A * S * Aᵀ).PosSemidef := by
    have := hS.mul_mul_conjTranspose_same A
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  refine IsGaussian.ext ?_ ?_
  · simp only [id]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id, integral_id_multivariateGaussian,
      integral_id_multivariateGaussian, map_zero]
  · ext u v
    rw [covarianceBilin_map IsGaussian.memLp_two_id, covarianceBilin_multivariateGaussian hS,
      covarianceBilin_multivariateGaussian hS', ← ContinuousLinearMap.star_eq_adjoint, ← map_star]
    simp only [ofLp_toEuclideanCLM, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, mulVec_transpose]
    rw [← dotProduct_mulVec, ← dotProduct_mulVec]

lemma sqrt_transpose (R : Matrix (Fin d) (Fin d) ℝ) : (CFC.sqrt R)ᵀ = CFC.sqrt R := by
  have h := (CFC.sqrt_nonneg R).isSelfAdjoint
  rw [IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h
  exact h

lemma sqrt_det_isUnit {R : Matrix (Fin d) (Fin d) ℝ} (hR : R.PosDef) : IsUnit (CFC.sqrt R).det := by
  have h := CFC.sqrt_mul_sqrt_self R hR.posSemidef.nonneg
  have hdet : (CFC.sqrt R).det * (CFC.sqrt R).det = R.det := by rw [← det_mul, h]
  rw [isUnit_iff_ne_zero]
  intro h0
  rw [h0, zero_mul] at hdet
  exact hR.det_pos.ne' hdet.symm

lemma invSqrt_sandwich {R : Matrix (Fin d) (Fin d) ℝ} (hR : R.PosDef) : invSqrt R * R * (invSqrt R)ᵀ = 1 := by
  have h := CFC.sqrt_mul_sqrt_self R hR.posSemidef.nonneg
  have hu := sqrt_det_isUnit hR
  have ht := sqrt_transpose R
  unfold invSqrt
  set s := CFC.sqrt R
  rw [transpose_nonsing_inv, ht, ← h, ← mul_assoc, nonsing_inv_mul _ hu, one_mul,
    mul_nonsing_inv _ hu]

lemma npn_sandwich {Rs Rν : Matrix (Fin d) (Fin d) ℝ} (hRs : Rs.PosDef) (hRν : Rν.PosSemidef) :
    (CFC.sqrt Rν * invSqrt Rs) * Rs * (CFC.sqrt Rν * invSqrt Rs)ᵀ = Rν := by
  rw [transpose_mul, sqrt_transpose]
  have := invSqrt_sandwich hRs
  calc CFC.sqrt Rν * invSqrt Rs * Rs * ((invSqrt Rs)ᵀ * CFC.sqrt Rν)
      = CFC.sqrt Rν * (invSqrt Rs * Rs * (invSqrt Rs)ᵀ) * CFC.sqrt Rν := by simp only [mul_assoc]
    _ = Rν := by rw [this, mul_one, CFC.sqrt_mul_sqrt_self Rν hRν.nonneg]

lemma measurable_zScore (μ : Measure (Euc d)) : Measurable (zScore μ) := by
  unfold zScore
  refine (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun i => ?_)
  exact (Measure.measurable_quantile _).comp ((cdf _).mono.measurable.comp (measurable_coord i))

theorem field_npn_std : Claims.field_npn_std := by
  intro d μ R hμ hR hnpn
  have hL : Measurable (toEuclideanCLM (𝕜 := ℝ) (invSqrt R)) := (toEuclideanCLM (𝕜 := ℝ) _).continuous.measurable
  have : npnStd μ R = toEuclideanCLM (𝕜 := ℝ) (invSqrt R) ∘ zScore μ := rfl
  rw [this, ← Measure.map_map hL (measurable_zScore μ), hnpn, mvG_map _ _ hR.posSemidef, invSqrt_sandwich hR]

theorem field_npn_exact : Claims.field_npn_exact := by
  intro d μs ν Rs Rν hμs hν hRs hRν hs hnu hna
  set L := toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt Rν * invSqrt Rs) with hLdef
  set h : Euc d → Euc d := fun w => WithLp.toLp 2 fun i => (marg ν i).quantile (stdPhi (w i)) with hh
  have hLm : Measurable L := L.continuous.measurable
  have hhm : Measurable h := by
    refine (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun i => ?_)
    exact (Measure.measurable_quantile _).comp ((cdf _).mono.measurable.comp (measurable_coord i))
  have e1 : npnMap μs ν Rs Rν = h ∘ L ∘ zScore μs := rfl
  have hleft : μs.map (npnMap μs ν Rs Rν) = (multivariateGaussian 0 Rν).map h := by
    rw [e1, ← Measure.map_map hhm (hLm.comp (measurable_zScore μs)), ← Measure.map_map hLm (measurable_zScore μs),
      hs, mvG_map _ _ hRs.posSemidef, npn_sandwich hRs hRν]
  rw [hleft, ← hnu, Measure.map_map hhm (measurable_zScore ν)]
  -- `h ∘ Z_ν = id` `ν`-a.e.
  have hΦ : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  have hcoord : ∀ i, ∀ᵐ y ∂ν, (marg ν i).quantile (stdPhi (stdPhiInv (cdf (marg ν i) (y i)))) = y i := by
    intro i
    have hmi : IsProbabilityMeasure (marg ν i) := by unfold marg; infer_instance
    have a1 : ∀ᵐ u ∂(volume.restrict (Icc (0 : ℝ) 1)), stdPhi (stdPhiInv u) = u :=
      Measure.cdf_quantile_ae (gaussianReal 0 1)
    rw [← Measure.cdf_map_eq_volume_restrict (marg ν i)] at a1
    have a1' := ae_of_ae_map (cdf (marg ν i)).mono.measurable.aemeasurable a1
    have a2 := Measure.quantile_cdf_ae (marg ν i)
    have a3 : ∀ᵐ t ∂(marg ν i), (marg ν i).quantile (stdPhi (stdPhiInv (cdf (marg ν i) t))) = t := by
      filter_upwards [a1', a2] with t ht1 ht2
      rw [ht1]; exact ht2
    exact ae_of_ae_map (measurable_coord i).aemeasurable a3
  have hall := ae_all_iff.2 hcoord
  have hid : (h ∘ zScore ν) =ᵐ[ν] id := by
    filter_upwards [hall] with y hy
    simp only [Function.comp_apply, hh, zScore, id]
    ext i
    exact hy i
  rw [Measure.map_congr hid, Measure.map_id]

end StatFormal.Wave24f
