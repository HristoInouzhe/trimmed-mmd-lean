import StatFormal.Archive.Wave30h.RouteFieldCop
import StatFormal.Archive.Wave30h.RouteScores
import StatFormal.Archive.Wave30h.RouteCopTransport
import StatFormal.Lib.MatrixSqrtPerturb.RootRates
import StatFormal.Lib.NormalScores.Gauss
import StatFormal.Lib.QuantileRates.LpBridge

/-!
# Route — `cor:field-npn`, journal form (untrusted)

* (ii) `fieldnpn_fwd`: `Ŝ − S = R̂^{-1/2}(Ẑ − Z) + (R̂^{-1/2} − R^{-1/2})Z`, so
  `‖Ŝ − S‖_{L²(μ)} ≤ ‖R̂^{-1/2}‖ ‖Ẑ − Z‖_{L²(μ)} + ‖R̂^{-1/2} − R^{-1/2}‖ ‖Z‖_{L²(μ)}`;
  `‖Ẑ − Z‖²_{L²(μ)} = Σ_i ∫ (Ẑ_i − Z_i)² dμ_i = O_P((log n)²/n)` (`lem:scores` per coordinate, `scores_mse`),
  `‖R̂^{-1/2} − R^{-1/2}‖ = O_P(n^{-1/2})` (`MatrixSqrtPerturb.bigOP_invSqrt_sub`), `‖Z‖_{L²(μ)} < ∞`
  (`Z_#μ = N(0,R)`), and `‖R̂^{-1/2}‖ = O_P(1)` (`bigOP_of_lip`).
* (iii) `fieldnpn_inv`: `S'(z) = (g_i(Φ([B^{1/2}z]_i)))_i` with `g_i` the `L`-Lipschitz extension of `G_i⁻¹`
  (`AssMarg.exists_ext`); `S' = npnInv ν B` everywhere (`Φ ∈ (0,1)`), `Lip(S') ≤ L‖B^{1/2}‖` (`Φ` is `1`-Lipschitz).
  `h_n = Ŝ⁻¹ − (g_i(Φ([B̂^{1/2}z]_i)))_i`, `sup ≤ dL(ε_n + 2/n)` on the DKW ∩ support event (`sup_interpQuant_sub`);
  `k_n = (g_i(Φ([B̂^{1/2}z]_i)))_i − S'`, `Lip(k_n) ≤ L(‖B̂^{1/2}‖ + ‖B^{1/2}‖)`,
  `‖k_n‖_{L²(N(0,I))} ≤ L‖B̂^{1/2} − B^{1/2}‖ ‖id‖_{L²(N(0,I))}` (`MatrixSqrtPerturb.bigOP_sqrt_sub`).
* `fieldnpn_rate`: `fieldJ_rate` with `γ = N(0, I)`, `Standardises μ γ (npnStd μ R) (npnInv μ R)`
  (`npn_standardises`: frozen `field_npn_std`; `npnInv ∘ npnStd = id` a.e., `npnStd ∘ npnInv = id` everywhere),
  (ii) at rate `log n/√n` and (iii) at rate `1/√n ≤ log n/√n`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Matrix
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator

namespace StatFormal.Wave30h

open StatFormal.Wave9b (Standardises BigOP)
open StatFormal.OTFD.WaveL1 (Euc)
open StatFormal.OTFD.Wave8c (mvec)
open StatFormal.Wave24f (marg stdPhi stdPhiInv zScore InNPN invSqrt npnStd measurable_zScore sqrt_det_isUnit)
open StatFormal.Wave24e (measurable_coord)

namespace FieldNPN

variable {d : ℕ}

/-! ### `Φ` and the estimators -/

lemma continuous_stdPhi : Continuous stdPhi := StatFormal.Wave23c.Φn_continuous

lemma measurable_stdPhiInv : Measurable stdPhiInv := Measure.measurable_quantile _

lemma stdPhi_mem (u : ℝ) : stdPhi u ∈ Ioo (0 : ℝ) 1 :=
  ⟨StatFormal.Wave23c.Φn_pos u, StatFormal.Wave23c.Φn_lt_one u⟩

lemma stdPhi_sub_le {a b : ℝ} (hab : a ≤ b) : stdPhi b - stdPhi a ≤ b - a := by
  have hc0 := StatFormal.NormalScores.cG_pos
  have hc1 : StatFormal.NormalScores.cG ≤ 1 := by
    unfold StatFormal.NormalScores.cG
    refine inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 ?_)
    nlinarith [Real.two_le_pi]
  have key : gaussianReal 0 1 (Ioc a b) ≤ ENNReal.ofReal StatFormal.NormalScores.cG * volume (Ioc a b) := by
    rw [gaussianReal_apply 0 one_ne_zero, ← setLIntegral_const]
    refine setLIntegral_mono measurable_const fun x _ => ?_
    rw [gaussianPDF]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := StatFormal.NormalScores.φd_eq x
    simp only [StatFormal.NormalScores.φd] at h1
    rw [h1]
    have : Real.exp (-x ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x])
    nlinarith
  rw [StatFormal.Foundations.MatchedGrid.gauss_Ioc, Real.volume_Ioc, ← ENNReal.ofReal_mul hc0.le,
    ENNReal.ofReal_le_ofReal_iff (by nlinarith)] at key
  change StatFormal.Wave23c.Φn b - StatFormal.Wave23c.Φn a ≤ b - a
  nlinarith

lemma stdPhi_lipschitz : LipschitzWith 1 stdPhi := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
  have hmono : Monotone stdPhi := StatFormal.Wave23c.Φn_strictMono.monotone
  rcases le_total x y with h | h
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (hmono h)), abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h)]
    exact stdPhi_sub_le h
  · rw [abs_of_nonneg (sub_nonneg.2 (hmono h)), abs_of_nonneg (sub_nonneg.2 h)]
    exact stdPhi_sub_le h

lemma lip_mvec (A : Matrix (Fin d) (Fin d) ℝ) : LipschitzWith ‖A‖₊ (mvec A) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, coe_nnnorm]
  exact StatFormal.MatrixSqrtPerturb.norm_toEuclideanLin_le A _

lemma mvec_sub (A B : Matrix (Fin d) (Fin d) ℝ) (v : Euc d) : mvec (A - B) v = mvec A v - mvec B v := by
  simp [mvec, map_sub]

lemma mvec_sub_right (A : Matrix (Fin d) (Fin d) ℝ) (v w : Euc d) : mvec A (v - w) = mvec A v - mvec A w := by
  simp [mvec, map_sub]

lemma mvec_mul (A B : Matrix (Fin d) (Fin d) ℝ) (z : Euc d) : mvec A (mvec B z) = mvec (A * B) z := by
  simp [mvec, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

lemma mvec_one (z : Euc d) : mvec (1 : Matrix (Fin d) (Fin d) ℝ) z = z := by simp [mvec]

lemma continuous_clipN (n : ℕ) : Continuous (clipN n) := by
  unfold clipN; fun_prop

lemma measurable_zScoreHat {n : ℕ} (X : Fin n → Euc d) : Measurable (zScoreHat X) :=
  (WithLp.measurable_toLp (p := 2) (X := Fin d → ℝ)).comp (Measurable.of_eval fun i =>
    measurable_stdPhiInv.comp ((continuous_clipN n).measurable.comp
      ((interpCdf_mono _).measurable.comp (measurable_coord i))))

lemma measurable_npnStdHat {n : ℕ} (X : Fin n → Euc d) (Rh : Matrix (Fin d) (Fin d) ℝ) :
    Measurable (npnStdHat X Rh) :=
  (lip_mvec _).continuous.measurable.comp (measurable_zScoreHat X)

lemma continuous_npnInvHat {n : ℕ} (Z : Fin n → Euc d) (Bh : Matrix (Fin d) (Fin d) ℝ) :
    Continuous (npnInvHat Z Bh) := by
  unfold npnInvHat
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i =>
    (continuous_interpQuant _).comp (continuous_stdPhi.comp ?_))
  exact (EuclideanSpace.proj i).continuous.comp (lip_mvec _).continuous

lemma measurable_npnInv (μ : Measure (Euc d)) (R : Matrix (Fin d) (Fin d) ℝ) : Measurable (npnInv μ R) :=
  (WithLp.measurable_toLp (p := 2) (X := Fin d → ℝ)).comp (Measurable.of_eval fun i =>
    (Measure.measurable_quantile _).comp
      (continuous_stdPhi.comp ((EuclideanSpace.proj i).continuous.comp (lip_mvec _).continuous)).measurable)

/-! ### The population standardisation -/

lemma sqrt_mul_invSqrt {R : Matrix (Fin d) (Fin d) ℝ} (hR : R.PosDef) : CFC.sqrt R * invSqrt R = 1 := by
  unfold invSqrt; exact mul_nonsing_inv _ (sqrt_det_isUnit hR)

lemma invSqrt_mul_sqrt {R : Matrix (Fin d) (Fin d) ℝ} (hR : R.PosDef) : invSqrt R * CFC.sqrt R = 1 := by
  unfold invSqrt; exact nonsing_inv_mul _ (sqrt_det_isUnit hR)

/-- `G_i⁻¹(Φ(Φ⁻¹(G_i(x_i)))) = x_i` for `μ`-a.e. `x`. -/
lemma ae_quantile_phi_cdf (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (hat : ∀ i, NullSingletonClass (marg μ i)) :
    ∀ᵐ x ∂μ, ∀ i, (marg μ i).quantile (stdPhi (stdPhiInv (cdf (marg μ i) (x i)))) = x i := by
  rw [ae_all_iff]
  intro i
  have := CopTransport.isProb_marg μ i
  have := hat i
  have a2 := Measure.quantile_cdf_ae (marg μ i)
  have a1 := StatFormal.NormalScores.ae_cdf_mem_Ioo (marg μ i)
  have a3 : ∀ᵐ t ∂(marg μ i), (marg μ i).quantile (stdPhi (stdPhiInv (cdf (marg μ i) t))) = t := by
    filter_upwards [a1, a2] with t ht1 ht2
    rw [show stdPhi (stdPhiInv (cdf (marg μ i) t)) = cdf (marg μ i) t from
      StatFormal.Foundations.MatchedGrid.Φn_Φq ht1.1 ht1.2]
    exact ht2
  exact ae_of_ae_map (measurable_coord i).aemeasurable a3

/-- `(npnStd μ R, npnInv μ R)` standardises a nonparanormal `μ` with continuous marginals onto `N(0, I)`. -/
lemma npn_standardises {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {R : Matrix (Fin d) (Fin d) ℝ}
    (hR : R.PosDef) (hnpn : InNPN μ R) (hat : ∀ i, NullSingletonClass (marg μ i)) :
    Standardises μ (multivariateGaussian 0 1) (npnStd μ R) (npnInv μ R) := by
  have hS : Measurable (npnStd μ R) := (lip_mvec (invSqrt R)).continuous.measurable.comp (measurable_zScore μ)
  refine ⟨hS, measurable_npnInv μ R, StatFormal.Wave24f.field_npn_std _ μ R inferInstance hR hnpn, ?_, ?_⟩
  · filter_upwards [ae_quantile_phi_cdf μ hat] with x hx
    have e : mvec (CFC.sqrt R) (npnStd μ R x) = zScore μ x := by
      change mvec (CFC.sqrt R) (mvec (invSqrt R) (zScore μ x)) = _
      rw [mvec_mul, sqrt_mul_invSqrt hR, mvec_one]
    ext i
    change (marg μ i).quantile (stdPhi (mvec (CFC.sqrt R) (npnStd μ R x) i)) = x i
    rw [e]
    exact hx i
  · refine Eventually.of_forall fun z => ?_
    have hz : zScore μ (npnInv μ R z) = mvec (CFC.sqrt R) z := by
      ext i
      change stdPhiInv (cdf (marg μ i) ((marg μ i).quantile (stdPhi (mvec (CFC.sqrt R) z i)))) =
        mvec (CFC.sqrt R) z i
      have := CopTransport.isProb_marg μ i
      have := hat i
      rw [CopTransport.cdf_quantile_of_mem _ (stdPhi_mem _)]
      exact StatFormal.Foundations.MatchedGrid.Φq_Φn _
    change mvec (invSqrt R) (zScore μ (npnInv μ R z)) = z
    rw [hz, mvec_mul, invSqrt_mul_sqrt hR, mvec_one]

/-! ### `O_P` helpers -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma bigOP_sum_fin [IsProbabilityMeasure P] {r : ℕ → ℝ} (hr : ∀ n, 0 ≤ r n) {ι : Type*} (s : Finset ι)
    {Y : ι → ℕ → Ω → ℝ≥0∞} (h : ∀ k ∈ s, BigOP P r (Y k)) : BigOP P r (fun n ω => ∑ k ∈ s, Y k n ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (bigOP_zero : BigOP P r (fun _ _ => 0))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact bigOP_add hr (h a (Finset.mem_insert_self a s)) (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

lemma rate_nonneg' (n : ℕ) : 0 ≤ Real.log n / Real.sqrt n :=
  div_nonneg (Real.log_natCast_nonneg n) (Real.sqrt_nonneg _)

lemma bigOP_sqrt_of_sq [IsProbabilityMeasure P] {W Y : ℕ → Ω → ℝ≥0∞} (hWY : ∀ n ω, W n ω ^ 2 ≤ Y n ω)
    (hY : BigOP P (fun n => Real.log n ^ 2 / n) Y) : BigOP P (fun n => Real.log n / Real.sqrt n) W := by
  rw [bigOP_iff_compl (fun n => by positivity)] at hY
  rw [bigOP_iff_compl rate_nonneg']
  intro η hη
  obtain ⟨M, hM, N, hN⟩ := hY η hη
  refine ⟨√M, Real.sqrt_nonneg _, N, fun n hn => ?_⟩
  obtain ⟨A, hA, hPA, hb⟩ := hN n hn
  refine ⟨A, hA, hPA, fun ω hω => ?_⟩
  rw [← StatFormal.Foundations.QuantileRates.sq_le_sq_iff_ennreal]
  refine (hWY n ω).trans ((hb ω hω).trans (le_of_eq ?_))
  rw [← ENNReal.ofReal_pow (mul_nonneg (Real.sqrt_nonneg _) (rate_nonneg' n))]
  congr 1
  rw [mul_pow, Real.sq_sqrt hM, div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

lemma rate_le_eventually : ∀ᶠ n : ℕ in atTop, 1 / Real.sqrt n ≤ 1 * (Real.log n / Real.sqrt n) := by
  filter_upwards [eventually_ge_atTop 3] with n hn
  rw [one_mul]
  exact div_le_div_of_nonneg_right (StatFormal.NormalScores.one_le_log' hn) (Real.sqrt_nonneg _)

lemma invStdzJ_rate_mono [IsProbabilityMeasure P] {r r' : ℕ → ℝ} (hr : ∀ n, 0 ≤ r n) {C : ℝ} (hC : 0 ≤ C)
    (hrr : ∀ᶠ n in atTop, r n ≤ C * r' n) {L : ℝ≥0} {γ : Measure (Euc d)} {Sinv : Euc d → Euc d}
    {Sinvhat : ℕ → Ω → Euc d → Euc d} (h : InvStdzJ P r L γ Sinv Sinvhat) : InvStdzJ P r' L γ Sinv Sinvhat := by
  obtain ⟨S', h', k, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨S', h', k, h1, h2, h3, bigOP_rate_mono hr hC hrr h4, h5, bigOP_rate_mono hr hC hrr h6⟩

lemma norm_le_of_bigOP_event {M : ℝ} {n : ℕ} (hM : 0 ≤ M) (hn : 1 ≤ n) {A : Matrix (Fin d) (Fin d) ℝ}
    (h : ‖A‖ₑ ≤ ENNReal.ofReal (M * (1 / Real.sqrt n))) : ‖A‖ ≤ M := by
  have h1 := StatFormal.MatrixSqrtPerturb.norm_le_of_enorm_le (by positivity) h
  have h2 : 1 / Real.sqrt n ≤ 1 := StatFormal.MatrixSqrtPerturb.rate_le_one hn
  nlinarith

end FieldNPN

open FieldNPN

/-! ### (ii) -/

/-- **`cor:field-npn`(ii).** -/
theorem fieldnpn_fwd : Claims.fieldnpn_fwd := by
  intro d μ _ R lam Ω _ P _ X Rh hR hlam hlamR hnpn hat hX hind hlaw hRh hO
  have hinv := StatFormal.MatrixSqrtPerturb.bigOP_invSqrt_sub hlam hlamR hRh hO
  set iR := invSqrt R with hiR
  -- the scores error
  set W : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    eLpNorm (fun x => zScoreHat (fun j : Fin n => X j ω) x - zScore μ x) 2 μ with hWdef
  have hW : BigOP P (fun n => Real.log n / Real.sqrt n) W := by
    set Y : Fin d → ℕ → Ω → ℝ≥0∞ := fun k n ω => ∫⁻ t, ENNReal.ofReal
      ((stdPhiInv (clipN n (interpCdf (fun j : Fin n => X j ω k) t)) - stdPhiInv (cdf (marg μ k) t)) ^ 2)
        ∂(marg μ k) with hYdef
    have hY : ∀ k, BigOP P (fun n => Real.log n ^ 2 / n) (Y k) := fun k => by
      obtain ⟨hXk, hindk, hlawk⟩ := coord_iid hX hind hlaw k
      have := CopTransport.isProb_marg μ k
      have := hat k
      exact scores_mse (marg μ k) Ω P (fun j ω => X j ω k) hXk hindk hlawk
    have hsum := bigOP_sum_fin (fun n => by positivity) Finset.univ (fun k _ => hY k)
    refine bigOP_sqrt_of_sq (fun n ω => le_of_eq ?_) hsum
    have hm : Measurable fun x => zScoreHat (fun j : Fin n => X j ω) x - zScore μ x :=
      (measurable_zScoreHat _).sub (measurable_zScore μ)
    rw [hWdef]
    simp only
    have hmk : ∀ k : Fin d, Measurable fun x =>
        ENNReal.ofReal ((zScoreHat (fun j : Fin n => X j ω) x - zScore μ x) k ^ 2) := fun k =>
      ENNReal.measurable_ofReal.comp (((measurable_coord k).comp hm).pow_const 2)
    rw [StatFormal.Foundations.QuantileRates.eLpNorm_two_sq_euc hm.aestronglyMeasurable,
      lintegral_finsetSum _ fun k _ => hmk k]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hG : Measurable fun t => ENNReal.ofReal
        ((stdPhiInv (clipN n (interpCdf (fun j : Fin n => X j ω k) t)) - stdPhiInv (cdf (marg μ k) t)) ^ 2) :=
      ENNReal.measurable_ofReal.comp (((measurable_stdPhiInv.comp ((continuous_clipN n).measurable.comp
        (interpCdf_mono _).measurable)).sub (measurable_stdPhiInv.comp (cdf _).mono.measurable)).pow_const 2)
    refine Eq.trans ?_ (lintegral_map hG (measurable_coord k)).symm
    refine lintegral_congr fun x => ?_
    simp only [PiLp.sub_apply]
    rfl
  -- `‖Z‖_{L²(μ)} < ∞`
  have hZfin : eLpNorm (zScore μ) 2 μ ≠ ⊤ := by
    have h := eLpNorm_map_measure (μ := μ) (p := 2) (g := (id : Euc d → Euc d)) measurable_id.aestronglyMeasurable
      (measurable_zScore μ).aemeasurable
    rw [hnpn, Function.id_comp] at h
    rw [← h]
    exact (IsGaussian.memLp_two_id (μ := multivariateGaussian 0 R)).eLpNorm_ne_top
  set CZ : ℝ≥0 := (eLpNorm (zScore μ) 2 μ).toNNReal with hCZ
  have hr : ∀ n : ℕ, 0 ≤ Real.log n / Real.sqrt n := rate_nonneg'
  have hZterm : BigOP P (fun n => Real.log n / Real.sqrt n)
      (fun n ω => (CZ : ℝ≥0∞) * ‖invSqrt (Rh n ω) - iR‖ₑ) :=
    bigOP_rate_mono (fun n => by positivity) zero_le_one rate_le_eventually
      (bigOP_const_mul (fun n => by positivity) CZ hinv)
  refine bigOP_of_lip hr (Q := fun n ω K => ‖invSqrt (Rh n ω)‖ₑ ≤ K) ?_ ?_ hZterm hW
  · have hinvc := (bigOP_iff_compl (fun n => by positivity)).1 hinv
    intro η hη
    obtain ⟨M, hM0, N, hN⟩ := hinvc η hη
    refine ⟨‖iR‖₊ + M.toNNReal, max N 1, fun n hn => ?_⟩
    obtain ⟨A, hA, hPA, hb⟩ := hN n (le_of_max_le_left hn)
    refine ⟨A, hA, ofReal_le_of_compl_le' hA hη.le hPA, fun ω hω => ?_⟩
    have h1 : ‖invSqrt (Rh n ω) - iR‖ ≤ M := norm_le_of_bigOP_event hM0 (le_of_max_le_right hn) (hb ω hω)
    rw [enorm_eq_nnnorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, NNReal.coe_add, coe_nnnorm, coe_nnnorm,
      Real.coe_toNNReal _ hM0]
    have := norm_sub_norm_le (invSqrt (Rh n ω)) iR
    linarith
  · intro n ω K hK
    set Zh := zScoreHat (fun j : Fin n => X j ω)
    set iRh := invSqrt (Rh n ω)
    have hdec : (fun x => npnStdHat (fun j : Fin n => X j ω) (Rh n ω) x - npnStd μ R x) =
        (fun x => mvec (iRh - iR) (zScore μ x)) + (fun x => mvec iRh (Zh x - zScore μ x)) := by
      funext x
      simp only [Pi.add_apply]
      change mvec iRh (Zh x) - mvec iR (zScore μ x) = _
      rw [mvec_sub_right, mvec_sub]
      abel
    have hm1 : AEStronglyMeasurable (fun x => mvec (iRh - iR) (zScore μ x)) μ :=
      ((lip_mvec _).continuous.measurable.comp (measurable_zScore μ)).aestronglyMeasurable
    have hm2 : AEStronglyMeasurable (fun x => mvec iRh (Zh x - zScore μ x)) μ :=
      ((lip_mvec _).continuous.measurable.comp ((measurable_zScoreHat _).sub (measurable_zScore μ))).aestronglyMeasurable
    rw [hdec]
    refine (eLpNorm_add_le (by norm_num)).trans (add_le_add ?_ ?_)
    · have h := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' hm1 (g := zScore μ) (c := ‖iRh - iR‖₊)
        (Eventually.of_forall fun x => by
          rw [enorm_eq_nnnorm, enorm_eq_nnnorm, ← ENNReal.coe_mul, ENNReal.coe_le_coe, ← NNReal.coe_le_coe,
            NNReal.coe_mul, coe_nnnorm, coe_nnnorm, coe_nnnorm]
          exact StatFormal.MatrixSqrtPerturb.norm_toEuclideanLin_le _ _) 2
      refine h.trans (le_of_eq ?_)
      rw [ENNReal.smul_def, smul_eq_mul, enorm_eq_nnnorm, hCZ, ENNReal.coe_toNNReal hZfin, mul_comm]
    · have h := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' hm2 (g := fun x => Zh x - zScore μ x) (c := ‖iRh‖₊)
        (Eventually.of_forall fun x => by
          rw [enorm_eq_nnnorm, enorm_eq_nnnorm, ← ENNReal.coe_mul, ENNReal.coe_le_coe, ← NNReal.coe_le_coe,
            NNReal.coe_mul, coe_nnnorm, coe_nnnorm, coe_nnnorm]
          exact StatFormal.MatrixSqrtPerturb.norm_toEuclideanLin_le _ _) 2
      refine h.trans ?_
      rw [ENNReal.smul_def, smul_eq_mul]
      gcongr
      simpa [enorm_eq_nnnorm] using hK

/-! ### (iii) -/

/-- **`cor:field-npn`(iii).** -/
theorem fieldnpn_inv : Claims.fieldnpn_inv := by
  intro d ν _ B lam L a b Ω _ P _ Z Bh hB hlam hlamB _ hM hZ hind hlaw hBh hO
  have hprob : ∀ i, IsProbabilityMeasure (marg ν i) := fun i => CopTransport.isProb_marg ν i
  choose g hgL hgq hgc using fun i => by have := hprob i; exact (hM i).exists_ext
  set Fm : Euc d → Euc d := fun w => WithLp.toLp 2 fun i => g i (stdPhi (w i)) with hFm
  have hFmL : LipschitzWith L Fm :=
    lipschitz_coordMap (g := fun i u => g i (stdPhi u)) (L := L) fun i => by
      have := (hgL i).comp stdPhi_lipschitz
      rwa [mul_one] at this
  set sB := CFC.sqrt B with hsB
  set S' : Euc d → Euc d := fun z => Fm (mvec sB z) with hS'
  have hS'L : LipschitzWith (L * ‖sB‖₊) S' := hFmL.comp (lip_mvec sB)
  have hS'eq : ∀ z, S' z = npnInv ν B z := by
    intro z
    ext i
    change g i (stdPhi (mvec sB z i)) = (marg ν i).quantile (stdPhi (mvec (CFC.sqrt B) z i))
    exact hgq i _ (stdPhi_mem _)
  set hh : ℕ → Ω → Euc d → Euc d := fun n ω z =>
    npnInvHat (fun j : Fin n => Z j ω) (Bh n ω) z - Fm (mvec (CFC.sqrt (Bh n ω)) z) with hhh
  set kk : ℕ → Ω → Euc d → Euc d := fun n ω z => Fm (mvec (CFC.sqrt (Bh n ω)) z) - S' z with hkk
  have hsq := StatFormal.MatrixSqrtPerturb.bigOP_sqrt_sub hlam hlamB hBh hO
  refine ⟨L * ‖sB‖₊, S', hh, kk, hS'L, Eventually.of_forall hS'eq, fun n ω z => by simp only [hh, kk]; abel,
    ?_, ?_, ?_⟩
  · -- `‖h_n‖_∞ = O_P(n^{-1/2})`
    rw [bigOP_iff_compl (fun n => by positivity)]
    intro η hη
    obtain ⟨M, hM0, hA⟩ := dkw_coords hZ hind hlaw hη
    refine ⟨d * (L * (M + 2)), by positivity, 1, fun n hn => ?_⟩
    obtain ⟨A, hAm, hPA, hb⟩ := hA n hn
    set E : Set Ω := ⋂ (j : Fin n), ⋂ (i : Fin d), (fun ω => Z j ω i) ⁻¹' Icc (a i) (b i)
    have hEm : MeasurableSet E :=
      MeasurableSet.iInter fun j => MeasurableSet.iInter fun i =>
        ((measurable_coord i).comp (hZ j)) measurableSet_Icc
    have hEc : P Eᶜ = 0 := by
      simp only [E, compl_iInter]
      refine measure_iUnion_null fun j => measure_iUnion_null fun i => ?_
      have hm : Measurable fun ω => Z j ω i := (measurable_coord i).comp (hZ (j : ℕ))
      rw [← preimage_compl, ← Measure.map_apply hm measurableSet_Icc.compl, (coord_iid hZ hind hlaw i).2.2 j]
      exact (hM i).null_compl_Icc
    refine ⟨A ∩ E, hAm.inter hEm, measure_compl_inter_le.trans (by rw [hEc, add_zero]; exact hPA),
      fun ω hω => ?_⟩
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hsq' : 2 / (n : ℝ) ≤ 2 / Real.sqrt n := by
      rw [div_le_div_iff₀ hnpos (Real.sqrt_pos.2 hnpos)]
      have : Real.sqrt n ≤ n := by
        calc Real.sqrt n ≤ Real.sqrt n * Real.sqrt n := le_mul_of_one_le_left (Real.sqrt_nonneg _)
              (Real.one_le_sqrt.2 (by exact_mod_cast hn))
          _ = n := Real.mul_self_sqrt hnpos.le
      linarith
    have hcoord : ∀ z i, |hh n ω z i| ≤ L * (M + 2) * (1 / Real.sqrt n) := by
      intro z i
      simp only [hh, PiLp.sub_apply, npnInvHat, hFm]
      refine (sup_interpQuant_sub (hM i) (hgL i) (hgq i) (hgc i) hn (fun j => Z j ω i)
        (fun j => by have := hω.2; simp only [E, mem_iInter, mem_preimage] at this; exact this j i)
        (hb ω hω.1 i) _).trans ?_
      calc (L : ℝ) * (M * (1 / Real.sqrt n) + 2 / n) ≤ L * (M * (1 / Real.sqrt n) + 2 / Real.sqrt n) := by gcongr
        _ = L * (M + 2) * (1 / Real.sqrt n) := by ring
    refine iSup_le fun z => ?_
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ((norm_le_of_coord (hcoord z)).trans (le_of_eq ?_))
    ring
  · -- `Lip(k_n) = O_P(1)`
    have hsqc := (bigOP_iff_compl (fun n => by positivity)).1 hsq
    intro η hη
    obtain ⟨M, hM0, N, hN⟩ := hsqc η hη
    refine ⟨L * (‖sB‖₊ + M.toNNReal) + L * ‖sB‖₊, max N 1, fun n hn => ?_⟩
    obtain ⟨A, hA, hPA, hb⟩ := hN n (le_of_max_le_left hn)
    refine ⟨A, hA, ofReal_le_of_compl_le' hA hη.le hPA, fun ω hω => ?_⟩
    have h1 : ‖CFC.sqrt (Bh n ω) - sB‖ ≤ M := norm_le_of_bigOP_event hM0 (le_of_max_le_right hn) (hb ω hω)
    have hnorm : ‖CFC.sqrt (Bh n ω)‖₊ ≤ ‖sB‖₊ + M.toNNReal := by
      rw [← NNReal.coe_le_coe, NNReal.coe_add, coe_nnnorm, coe_nnnorm, Real.coe_toNNReal _ hM0]
      have := norm_sub_norm_le (CFC.sqrt (Bh n ω)) sB
      linarith
    have hk1 : LipschitzWith (L * ‖CFC.sqrt (Bh n ω)‖₊) (fun z => Fm (mvec (CFC.sqrt (Bh n ω)) z)) :=
      hFmL.comp (lip_mvec _)
    refine LipschitzWith.of_dist_le_mul fun z z' => ?_
    have e1 := hk1.dist_le_mul z z'
    have e2 := hS'L.dist_le_mul z z'
    have hK : ((L * ‖CFC.sqrt (Bh n ω)‖₊ : ℝ≥0) : ℝ) + ((L * ‖sB‖₊ : ℝ≥0) : ℝ) ≤
        ((L * (‖sB‖₊ + M.toNNReal) + L * ‖sB‖₊ : ℝ≥0) : ℝ) := by
      rw [← NNReal.coe_add, NNReal.coe_le_coe]
      exact add_le_add_left (mul_le_mul_of_nonneg_left hnorm bot_le) _
    calc dist (kk n ω z) (kk n ω z')
        ≤ dist (Fm (mvec (CFC.sqrt (Bh n ω)) z)) (Fm (mvec (CFC.sqrt (Bh n ω)) z')) + dist (S' z) (S' z') :=
          dist_sub_sub_le _ _ _ _
      _ ≤ ((L * ‖CFC.sqrt (Bh n ω)‖₊ : ℝ≥0) : ℝ) * dist z z' + ((L * ‖sB‖₊ : ℝ≥0) : ℝ) * dist z z' :=
          add_le_add e1 e2
      _ ≤ _ := by rw [← add_mul]; exact mul_le_mul_of_nonneg_right hK dist_nonneg
  · -- `‖k_n‖_{L²(N(0,I))} = O_P(n^{-1/2})`
    have hfin : eLpNorm (id : Euc d → Euc d) 2 (multivariateGaussian 0 1) ≠ ⊤ :=
      (IsGaussian.memLp_two_id (μ := multivariateGaussian (0 : Euc d) 1)).eLpNorm_ne_top
    set Cγ : ℝ≥0 := (eLpNorm (id : Euc d → Euc d) 2 (multivariateGaussian 0 1)).toNNReal with hCγ
    refine bigOP_mono (fun n ω => ?_) (bigOP_const_mul (fun n => by positivity) (L * Cγ) hsq)
    set c : ℝ := L * ‖CFC.sqrt (Bh n ω) - sB‖ with hc
    have hc0 : 0 ≤ c := by positivity
    have hkc : Continuous (kk n ω) :=
      (hFmL.comp (lip_mvec (CFC.sqrt (Bh n ω)))).continuous.sub hS'L.continuous
    have hpt : ∀ z, ‖kk n ω z‖ ≤ ‖(c • (id : Euc d → Euc d)) z‖ := by
      intro z
      rw [Pi.smul_apply, id, norm_smul, Real.norm_of_nonneg hc0]
      calc ‖kk n ω z‖ = dist (Fm (mvec (CFC.sqrt (Bh n ω)) z)) (Fm (mvec sB z)) := (dist_eq_norm _ _).symm
        _ ≤ L * dist (mvec (CFC.sqrt (Bh n ω)) z) (mvec sB z) := hFmL.dist_le_mul _ _
        _ = L * ‖mvec (CFC.sqrt (Bh n ω) - sB) z‖ := by rw [dist_eq_norm, mvec_sub]
        _ ≤ L * (‖CFC.sqrt (Bh n ω) - sB‖ * ‖z‖) :=
            mul_le_mul_of_nonneg_left (StatFormal.MatrixSqrtPerturb.norm_toEuclideanLin_le _ _) (NNReal.coe_nonneg L)
        _ = c * ‖z‖ := by rw [hc]; ring
    calc eLpNorm (kk n ω) 2 (multivariateGaussian 0 1)
        ≤ eLpNorm (c • (id : Euc d → Euc d)) 2 (multivariateGaussian 0 1) := eLpNorm_mono hkc.aestronglyMeasurable hpt
      _ = ‖c‖ₑ * eLpNorm (id : Euc d → Euc d) 2 (multivariateGaussian 0 1) := eLpNorm_const_smul _ _ _ _
      _ = ((L * Cγ : ℝ≥0) : ℝ≥0∞) * ‖CFC.sqrt (Bh n ω) - sB‖ₑ := by
          rw [Real.enorm_of_nonneg hc0, hc, ENNReal.ofReal_mul (NNReal.coe_nonneg L), ENNReal.ofReal_coe_nnreal,
            ofReal_norm, hCγ, ENNReal.coe_mul, ENNReal.coe_toNNReal hfin]
          ring

/-! ### The rate -/

/-- **`cor:field-npn`**, the rate. -/
theorem fieldnpn_rate : Claims.fieldnpn_rate := by
  intro d R ν A B lam L a b Ω _ P _ X Z Ah Bh hRp hνp hlam hA hlamA hnpnR hatR hB hlamB hnpnν hM hX hindX hlawX
    hZ hindZ hlawZ hAh hBh hOA hOB
  have hνat : ∀ i, NullSingletonClass (marg ν i) := fun i => by
    have hp : IsProbabilityMeasure (marg ν i) := by unfold marg; infer_instance
    refine ⟨fun t => ?_⟩
    rw [← measure_cdf (marg ν i), StieltjesFunction.measure_singleton]
    have hc := (hM i).continuous_cdf.continuousAt (x := t)
    rw [leftLim_eq_of_tendsto (hc.tendsto.mono_left nhdsWithin_le_nhds)]
    simp
  have hS : ∀ s, Standardises (R s) (multivariateGaussian 0 1) (npnStd (R s) (A s)) (npnInv (R s) (A s)) :=
    fun s => by
      have := hRp s
      exact npn_standardises (hA s) (hnpnR s) (hatR s)
  have hSν : Standardises ν (multivariateGaussian 0 1) (npnStd ν B) (npnInv ν B) := by
    have := hνp
    exact npn_standardises hB hnpnν hνat
  have hfwd : ∀ s, BigOP P (fun n => Real.log n / Real.sqrt n) fun n ω =>
      eLpNorm (fun x => npnStdHat (fun j : Fin n => X s j ω) (Ah n ω s) x - npnStd (R s) (A s) x) 2 (R s) :=
    fun s => by
      have := hRp s
      exact fieldnpn_fwd d (R s) (A s) lam Ω P (X s) (fun n ω => Ah n ω s) (hA s) hlam (hlamA s) (hnpnR s)
        (hatR s) (hX s) (hindX s) (hlawX s) (fun n ω => hAh n ω s) (hOA s)
  have := hνp
  obtain ⟨L', hinv⟩ := fieldnpn_inv d ν B lam L a b Ω P Z Bh hB hlam hlamB hnpnν hM hZ hindZ hlawZ hBh hOB
  have hinv' := invStdzJ_rate_mono (fun n => by positivity) zero_le_one rate_le_eventually hinv
  exact fieldJ_rate d R ν (multivariateGaussian 0 1) (fun s => npnStd (R s) (A s)) (fun s => npnInv (R s) (A s))
    (npnStd ν B) (npnInv ν B) Ω P (fun n ω s => npnStdHat (fun j : Fin n => X s j ω) (Ah n ω s))
    (fun n ω => npnInvHat (fun j : Fin n => Z j ω) (Bh n ω)) (fun n => Real.log n / Real.sqrt n) L' inferInstance
    rate_nonneg' hRp hνp inferInstance hS hSν (fun n ω s => measurable_npnStdHat _ _)
    (fun n ω => (continuous_npnInvHat _ _).measurable) hfwd hinv'

end StatFormal.Wave30h
