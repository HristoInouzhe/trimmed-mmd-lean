import StatFormal.Archive.Wave30h.Statements
import StatFormal.Archive.Wave24f.RouteNPN
import StatFormal.Archive.Wave24e.RouteCop
import StatFormal.Archive.Wave25a.RouteCorrected
import StatFormal.Lib.MatchedGrid.GaussQuantile
import StatFormal.Lib.NormalScores.Atomless

/-!
# Route — `prop:copulatransport` (untrusted)

Write `V = M ∘ W` (`W = zScore R`), `μ_V = V_#R`, `H_i` its marginal cdfs, `G_i` those of `ν` and
`Q(y) = (G_i⁻¹(H_i(y_i)))_i` (`qmap`), so `T = Q ∘ V` and `T_#R = Q_#μ_V` (`map_copTrans`).
* (i) `marg_map_qmap`: `(Q_#μ)_i = (G_i⁻¹ ∘ H_i)_#μ_i = (G_i⁻¹)_#Unif(0,1) = G_i` (probability integral transform
  for the continuous `H_i`, inverse transform sampling; Tau Ceti).
* (ii) `copula_map_qmap`: for continuous `G_i`, `G_i(G_i⁻¹(u)) = u` on `(0,1)` and `H_i(y_i) ∈ (0,1)` a.e., so
  `copStd(Q_#μ) ∘ Q = copStd μ` `μ`-a.e. Exactness `⟸`: `μ = (copStd μ)_#μ` pushed by `copInv μ` (frozen Wave 24e
  `copInv_copStd_ae`), and `copInv μ` depends only on the marginals.
* (iii) corrected: `W_#R = N(0,A)`, the frozen certified `corrected_gaussian` gives `μ_V = N(0,B)`, whose marginals are
  `N(0,1)` (`B_ii = 1`), so `Q = (G_i⁻¹ ∘ Φ)_i` and `Q_#N(0,B) = ν` (`InNPN ν B`, as in Wave 24f `field_npn_exact`).
  Uncorrected: `μ_V = G_#N(0,A) = N(0,P)` (`mvG_map`), `H_i = cdf N(0,P_ii)`, `Φ⁻¹(H_i(t)) = t/√P_ii`, so
  `zScore(T_#R) ∘ Q = D^{-1/2}` a.e. and the scores law is `N(0, D^{-1/2} P D^{-1/2}) = N(0, corrMat P)`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Matrix
open scoped ENNReal NNReal

namespace StatFormal.Wave30h

open StatFormal.OTFD.WaveL1 (Euc)
open StatFormal.OTFD.Wave8c (mvec)
open StatFormal.Wave24e (copStd copInv measurable_copStd measurable_copInv copInv_copStd_ae measurable_coord)
open StatFormal.Wave24f (marg stdPhi stdPhiInv zScore InNPN mvG_map measurable_zScore)
open StatFormal.Wave25a (corrMap covM meanV)

namespace CopTransport

variable {d : ℕ}

/-- The re-ranking map `Q(y) = (G_i⁻¹(H_i(y_i)))_i`, `H_i` the marginal cdfs of `μ`, `G_i` those of `ν`. -/
def qmap (ν μ : Measure (Euc d)) (y : Euc d) : Euc d :=
  WithLp.toLp 2 fun i => (marg ν i).quantile (cdf (marg μ i) (y i))

lemma measurable_qmap (ν μ : Measure (Euc d)) : Measurable (qmap ν μ) :=
  (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun i =>
    (Measure.measurable_quantile _).comp ((cdf _).mono.measurable.comp (measurable_coord i)))

lemma copTrans_eq (R ν : Measure (Euc d)) (M : Euc d → Euc d) :
    copTrans R ν M = qmap ν (R.map (M ∘ zScore R)) ∘ (M ∘ zScore R) := rfl

lemma map_copTrans (R ν : Measure (Euc d)) {M : Euc d → Euc d} (hM : Measurable M) :
    R.map (copTrans R ν M) = (R.map (M ∘ zScore R)).map (qmap ν (R.map (M ∘ zScore R))) := by
  rw [copTrans_eq, ← Measure.map_map (measurable_qmap _ _) (hM.comp (measurable_zScore R))]

lemma isProb_marg (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (i : Fin d) :
    IsProbabilityMeasure (marg μ i) := by
  unfold marg; infer_instance

/-- (i): `Q_#μ` has the marginals of `ν` when the marginals of `μ` are continuous. -/
lemma marg_map_qmap (ν μ : Measure (Euc d)) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (hμ : ∀ i, NullSingletonClass (marg μ i)) (i : Fin d) : marg (μ.map (qmap ν μ)) i = marg ν i := by
  have := isProb_marg μ i
  have := isProb_marg ν i
  have := hμ i
  have hf : Measurable fun t => (marg ν i).quantile (cdf (marg μ i) t) :=
    (Measure.measurable_quantile _).comp (cdf _).mono.measurable
  calc marg (μ.map (qmap ν μ)) i
      = μ.map ((fun t => (marg ν i).quantile (cdf (marg μ i) t)) ∘ (fun x : Euc d => x i)) := by
        change (μ.map (qmap ν μ)).map (fun x : Euc d => x i) = _
        rw [Measure.map_map (measurable_coord i) (measurable_qmap ν μ)]
        rfl
    _ = (marg μ i).map fun t => (marg ν i).quantile (cdf (marg μ i) t) := by
        rw [← Measure.map_map hf (measurable_coord i)]
        rfl
    _ = marg ν i := by
        rw [show (fun t => (marg ν i).quantile (cdf (marg μ i) t)) = (marg ν i).quantile ∘ cdf (marg μ i) from rfl,
          ← Measure.map_map (Measure.measurable_quantile _) (cdf _).mono.measurable,
          Measure.cdf_map_eq_volume_restrict, Measure.restrict_congr_set Ioo_ae_eq_Icc.symm,
          Measure.map_quantile_volume_Ioo]

/-- `G(G⁻¹(u)) = u` on `(0, 1)` for a continuous `G`. -/
lemma cdf_quantile_of_mem (G : Measure ℝ) [IsProbabilityMeasure G] [NullSingletonClass G] {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) : cdf G (G.quantile u) = u := by
  refine le_antisymm ?_ (Measure.le_cdf_quantile G hu.2)
  have htend : Tendsto (cdf G) (𝓝[<] (G.quantile u)) (𝓝 (cdf G (G.quantile u))) :=
    ((Measure.continuous_cdf_of_noAtoms G).tendsto _).mono_left nhdsWithin_le_nhds
  refine le_of_tendsto htend (eventually_of_mem self_mem_nhdsWithin fun x hx => ?_)
  exact le_of_lt ((Measure.lt_quantile_iff G hu.1 hu.2).1 hx)

lemma ae_cdf_marg_mem (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (hμ : ∀ i, NullSingletonClass (marg μ i)) :
    ∀ᵐ y ∂μ, ∀ k, cdf (marg μ k) (y k) ∈ Ioo (0 : ℝ) 1 := by
  rw [ae_all_iff]
  intro k
  have := isProb_marg μ k
  have := hμ k
  exact ae_of_ae_map (measurable_coord k).aemeasurable (StatFormal.NormalScores.ae_cdf_mem_Ioo (marg μ k))

/-- (ii): the copula of `Q_#μ` is that of `μ` when the marginals of `μ` and `ν` are continuous. -/
lemma copula_map_qmap (ν μ : Measure (Euc d)) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (hμ : ∀ i, NullSingletonClass (marg μ i)) (hν : ∀ i, NullSingletonClass (marg ν i)) :
    (μ.map (qmap ν μ)).map (copStd (μ.map (qmap ν μ))) = μ.map (copStd μ) := by
  rw [Measure.map_map (measurable_copStd _) (measurable_qmap ν μ)]
  refine Measure.map_congr ?_
  filter_upwards [ae_cdf_marg_mem μ hμ] with y hy
  have hm := marg_map_qmap ν μ hμ
  simp only [Function.comp_apply, copStd]
  congr 1
  funext k
  change cdf (marg (μ.map (qmap ν μ)) k) ((marg ν k).quantile (cdf (marg μ k) (y k))) = cdf (marg μ k) (y k)
  rw [hm k]
  have := isProb_marg ν k
  have := hν k
  exact cdf_quantile_of_mem _ (hy k)

/-- Sklar: `μ = (copInv μ)_# (copStd μ)_# μ`. -/
lemma sklar (μ : Measure (Euc d)) [IsProbabilityMeasure μ] :
    (μ.map (copStd μ)).map (copInv μ) = μ := by
  rw [Measure.map_map (measurable_copInv μ) (measurable_copStd μ)]
  have h : (copInv μ ∘ copStd μ) =ᵐ[μ] id := by
    filter_upwards [copInv_copStd_ae μ] with x hx
    exact hx
  rw [Measure.map_congr h, Measure.map_id]

lemma copInv_congr {μ μ' : Measure (Euc d)} (h : ∀ i, marg μ i = marg μ' i) : copInv μ = copInv μ' := by
  funext u
  unfold copInv
  congr 1
  funext k
  have := h k
  unfold marg at this
  rw [this]

/-- `Φ⁻¹(cdf N(0, p)(t)) = t/√p` for `p > 0`. -/
lemma stdPhiInv_cdf_gaussian {p : ℝ} (hp : 0 < p) (t : ℝ) :
    stdPhiInv (cdf (gaussianReal 0 p.toNNReal) t) = t / √p := by
  have hs : 0 < √p := Real.sqrt_pos.2 hp
  have hmap : gaussianReal 0 p.toNNReal = (gaussianReal 0 1).map (fun x => √p * x) := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    congr 1
    ext
    simp [Real.sq_sqrt hp.le, hp.le]
  have hpre : (fun x => √p * x) ⁻¹' Iic t = Iic (t / √p) := by
    ext x
    simp only [mem_preimage, mem_Iic]
    rw [le_div_iff₀ hs, mul_comm]
  have hcdf : cdf (gaussianReal 0 p.toNNReal) t = cdf (gaussianReal 0 1) (t / √p) := by
    rw [cdf_eq_real, cdf_eq_real, hmap, map_measureReal_apply (by fun_prop) measurableSet_Iic, hpre]
  rw [hcdf]
  exact StatFormal.Foundations.MatchedGrid.Φq_Φn _

lemma diag_sandwich {P : Matrix (Fin d) (Fin d) ℝ} (hP : P.PosDef) :
    (diagonal fun i => 1 / √(P i i)) * P * (diagonal fun i => 1 / √(P i i))ᵀ = corrMat P := by
  ext i j
  rw [diagonal_transpose, mul_diagonal, diagonal_mul, corrMat,
    Real.sqrt_mul (hP.diag_pos (i := i)).le]
  have h1 : 0 < √(P i i) := Real.sqrt_pos.2 hP.diag_pos
  have h2 : 0 < √(P j j) := Real.sqrt_pos.2 hP.diag_pos
  field_simp

end CopTransport

open CopTransport

/-- **`prop:copulatransport`(i).** -/
theorem coptransport_marginals : Claims.coptransport_marginals := by
  intro d R ν _ _ M hM hH i
  have : IsProbabilityMeasure (R.map (M ∘ zScore R)) :=
    inferInstance
  rw [map_copTrans R ν hM]
  exact marg_map_qmap ν _ hH i

/-- **`prop:copulatransport`(ii)**, first part. -/
theorem coptransport_copula : Claims.coptransport_copula := by
  intro d R ν _ _ M hM hH hG
  have : IsProbabilityMeasure (R.map (M ∘ zScore R)) :=
    inferInstance
  rw [map_copTrans R ν hM]
  exact copula_map_qmap ν _ hH hG

/-- **`prop:copulatransport`(ii)**, second part. -/
theorem coptransport_exact_iff : Claims.coptransport_exact_iff := by
  intro d R ν M hR hν hM hH hG
  have := hν
  have := hR 0
  have := hR 1
  have h0 : IsProbabilityMeasure ((R 0).map (M 0 ∘ zScore (R 0))) :=
    inferInstance
  have h1 : IsProbabilityMeasure ((R 1).map (M 1 ∘ zScore (R 1))) :=
    inferInstance
  rw [map_copTrans (R 0) ν (hM 0), map_copTrans (R 1) ν (hM 1)]
  set μ0 := (R 0).map (M 0 ∘ zScore (R 0)) with hμ0
  set μ1 := (R 1).map (M 1 ∘ zScore (R 1)) with hμ1
  have c0 := copula_map_qmap ν μ0 (hH 0) hG
  have c1 := copula_map_qmap ν μ1 (hH 1) hG
  constructor
  · intro h
    rw [← c0, ← c1, h]
  · intro h
    rw [← c0, ← c1] at h
    have : IsProbabilityMeasure (μ0.map (qmap ν μ0)) := inferInstance
    have : IsProbabilityMeasure (μ1.map (qmap ν μ1)) := inferInstance
    have hinv : copInv (μ0.map (qmap ν μ0)) = copInv (μ1.map (qmap ν μ1)) :=
      copInv_congr fun i => (marg_map_qmap ν μ0 (hH 0) i).trans (marg_map_qmap ν μ1 (hH 1) i).symm
    calc μ0.map (qmap ν μ0) = ((μ0.map (qmap ν μ0)).map (copStd (μ0.map (qmap ν μ0)))).map
          (copInv (μ0.map (qmap ν μ0))) := (sklar _).symm
      _ = ((μ1.map (qmap ν μ1)).map (copStd (μ1.map (qmap ν μ1)))).map (copInv (μ1.map (qmap ν μ1))) := by
          rw [h, hinv]
      _ = μ1.map (qmap ν μ1) := sklar _

/-- **`prop:copulatransport`(iii)**, corrected map: exact repair. -/
theorem coptransport_corrected : Claims.coptransport_corrected := by
  intro d R ν _ _ A B M c Vh Ph _ hB hB1 hR hν hG hVh hVV hPh hPP
  set Mc := corrMap (multivariateGaussian 0 A) (fun x => M x + c) (meanV (multivariateGaussian 0 B) id) (Vh * Ph)
    with hMcdef
  have hMc : Measurable Mc := by
    have : Continuous Mc := by
      rw [hMcdef]; unfold corrMap
      fun_prop
    exact this.measurable
  have hlaw : R.map (Mc ∘ zScore R) = multivariateGaussian 0 B := by
    rw [← Measure.map_map hMc (measurable_zScore R), hR]
    exact StatFormal.Wave25a.corrected_gaussian d _ _ M c Vh Ph hVh hVV hPh hPP
  rw [map_copTrans R ν hMc, hlaw]
  have hmarg : ∀ i, marg (multivariateGaussian 0 B) i = gaussianReal 0 1 := fun i => by
    have := (measurePreserving_eval_multivariateGaussian (μ := (0 : Euc d)) hB.posSemidef (i := i)).map_eq
    change (multivariateGaussian 0 B).map (fun x : Euc d => x i) = _
    rw [this, hB1 i]
    simp
  set h : Euc d → Euc d := fun w => WithLp.toLp 2 fun i => (marg ν i).quantile (stdPhi (w i)) with hh
  have hq : qmap ν (multivariateGaussian 0 B) = h := by
    funext w
    simp only [qmap, hmarg, hh]
    rfl
  have hhm : Measurable h := by rw [← hq]; exact measurable_qmap _ _
  rw [hq, ← hν, Measure.map_map hhm (measurable_zScore ν)]
  -- `h ∘ Z_ν = id` `ν`-a.e.
  have hcoord : ∀ i, ∀ᵐ y ∂ν, (marg ν i).quantile (stdPhi (stdPhiInv (cdf (marg ν i) (y i)))) = y i := by
    intro i
    have := isProb_marg ν i
    have := hG i
    have a2 := Measure.quantile_cdf_ae (marg ν i)
    have a1 := StatFormal.NormalScores.ae_cdf_mem_Ioo (marg ν i)
    have a3 : ∀ᵐ t ∂(marg ν i), (marg ν i).quantile (stdPhi (stdPhiInv (cdf (marg ν i) t))) = t := by
      filter_upwards [a1, a2] with t ht1 ht2
      rw [show stdPhi (stdPhiInv (cdf (marg ν i) t)) = cdf (marg ν i) t from
        StatFormal.Foundations.MatchedGrid.Φn_Φq ht1.1 ht1.2]
      exact ht2
    exact ae_of_ae_map (measurable_coord i).aemeasurable a3
  have hid : (h ∘ zScore ν) =ᵐ[ν] id := by
    filter_upwards [ae_all_iff.2 hcoord] with y hy
    simp only [Function.comp_apply, hh, zScore, id]
    ext i
    exact hy i
  rw [Measure.map_congr hid, Measure.map_id]

/-- **`prop:copulatransport`(iii)**, uncorrected map: target marginals and a Gaussian copula with correlation
matrix `corrMat P`. -/
theorem coptransport_uncorrected : Claims.coptransport_uncorrected := by
  intro d R ν _ _ A G hA hR hP hG
  set P := G * A * Gᵀ with hPdef
  have hcoe : (mvec G) = ⇑(toEuclideanCLM (𝕜 := ℝ) G) := rfl
  have hM : Measurable (mvec G) := by rw [hcoe]; exact (toEuclideanCLM (𝕜 := ℝ) G).continuous.measurable
  have hlaw : R.map (mvec G ∘ zScore R) = multivariateGaussian 0 P := by
    rw [← Measure.map_map hM (measurable_zScore R), hR, hcoe, mvG_map _ _ hA.posSemidef]
  have hmarg : ∀ i, marg (multivariateGaussian 0 P) i = gaussianReal 0 (P i i).toNNReal := fun i => by
    have := (measurePreserving_eval_multivariateGaussian (μ := (0 : Euc d)) hP.posSemidef (i := i)).map_eq
    change (multivariateGaussian 0 P).map (fun x : Euc d => x i) = _
    rw [this]
    simp
  have hNSC : ∀ i, NullSingletonClass (marg (multivariateGaussian 0 P) i) := fun i => by
    rw [hmarg]
    exact nullSingletonClass_gaussianReal (Real.toNNReal_pos.2 hP.diag_pos).ne'
  have hmapT := map_copTrans R ν (M := mvec G) hM
  rw [hlaw] at hmapT
  have part1 : ∀ i, marg (R.map (copTrans R ν (mvec G))) i = marg ν i := by
    intro i
    rw [hmapT]
    exact marg_map_qmap ν _ hNSC i
  refine ⟨part1, ?_⟩
  unfold InNPN
  have hz : zScore (R.map (copTrans R ν (mvec G))) = zScore ν := by
    funext y
    unfold zScore
    congr 1
    funext i
    rw [part1 i]
  rw [hz, hmapT, Measure.map_map (measurable_zScore ν) (measurable_qmap _ _)]
  set D : Matrix (Fin d) (Fin d) ℝ := diagonal fun i => 1 / √(P i i) with hD
  have hae : (zScore ν ∘ qmap ν (multivariateGaussian 0 P)) =ᵐ[multivariateGaussian 0 P]
      ⇑(toEuclideanCLM (𝕜 := ℝ) D) := by
    filter_upwards [ae_cdf_marg_mem _ hNSC] with y hy
    ext k
    simp only [Function.comp_apply, zScore, qmap]
    change stdPhiInv (cdf (marg ν k) ((marg ν k).quantile (cdf (marg (multivariateGaussian 0 P) k) (y k)))) =
      (D *ᵥ WithLp.ofLp y) k
    have := isProb_marg ν k
    have := hG k
    rw [cdf_quantile_of_mem _ (hy k), hmarg k, stdPhiInv_cdf_gaussian hP.diag_pos, hD, mulVec_diagonal]
    ring
  rw [Measure.map_congr hae, mvG_map _ _ hP.posSemidef, diag_sandwich hP]

end StatFormal.Wave30h
