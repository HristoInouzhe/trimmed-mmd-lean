import StatFormal.Archive.Wave30h.Statements
import StatFormal.Archive.Wave24d.RouteFieldEll
import StatFormal.Lib.MatrixSqrtPerturb.SampleMoments

/-!
# Route — SB journal `cor:field-ell` (untrusted)

`μ = (z ↦ Az + b)_#γ` has `Eμ = b`, `Cov(μ) = AAᵀ ≥ λ I` (`λ > 0`, `A` invertible) and a finite fourth moment.
On the event `‖Σ̂ − Σ‖_op ≤ λ/2` (probability → 1, since `‖Σ̂ − Σ‖_op = O_P(n^{-1/2})`):
* (ii) `Ŝ − S = (Σ̂^{-1/2} − Σ^{-1/2})(x − m) + Σ̂^{-1/2}(m − m̂)`, so
  `‖Ŝ − S‖_{L²(μ)} ≤ ‖Σ̂^{-1/2} − Σ^{-1/2}‖ ‖x − m‖_{L²(μ)} + ‖Σ̂^{-1/2}‖ ‖m̂ − m‖`, with
  `‖Σ̂^{-1/2}‖ ≤ (λ/2)^{-1/2}`, `‖Σ̂^{-1/2} − Σ^{-1/2}‖ ≤ (λ/2)^{-1/2} λ^{-1} ‖Σ̂ − Σ‖`.
* (iii) `h_n = 0`, `k_n(z) = (m̂ − m) + (Σ̂^{1/2} − Σ^{1/2})z`, `Lip(k_n) = ‖Σ̂^{1/2} − Σ^{1/2}‖ ≤ λ^{-1/2}‖Σ̂ − Σ‖`,
  `‖k_n‖_{L²(γ)} ≤ ‖m̂ − m‖ + ‖Σ̂^{1/2} − Σ^{1/2}‖ ‖z‖_{L²(γ)}`; `S' = S_ν⁻¹` is `‖Σ^{1/2}‖`-Lipschitz.
* the rate: the journal `thm:field` (hypothesis `fieldJ_rate`) with (i) from the frozen Wave 24d `field_ell` at
  `W = Σ^{-1/2}` (symmetric, `W W Σ = I`, `W⁻¹ = Σ^{1/2}`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Matrix
open scoped ENNReal NNReal

namespace StatFormal.Wave30h

open StatFormal.Wave9b (Standardises BigOP LipschitzWhp)
open StatFormal.OTFD.WaveL1 (Euc)
open StatFormal.OTFD.Wave8c (mvec)
open StatFormal.Wave24d (meanVec covMat IsSpherical continuous_mvec')
open StatFormal.Wave24f (invSqrt)
open StatFormal.MatrixSqrtPerturb
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {d : ℕ}

/-! ### `mvec` algebra -/

lemma ell_mvec_sub (A B : Matrix (Fin d) (Fin d) ℝ) (v : Euc d) : mvec (A - B) v = mvec A v - mvec B v := by
  simp [mvec, map_sub]

lemma ell_mvec_add_right (A : Matrix (Fin d) (Fin d) ℝ) (v w : Euc d) : mvec A (v + w) = mvec A v + mvec A w :=
  map_add _ _ _

lemma ell_mvec_sub_right (A : Matrix (Fin d) (Fin d) ℝ) (v w : Euc d) : mvec A (v - w) = mvec A v - mvec A w :=
  map_sub _ _ _

lemma ell_norm_mvec_le (A : Matrix (Fin d) (Fin d) ℝ) (v : Euc d) : ‖mvec A v‖ ≤ ‖A‖ * ‖v‖ :=
  norm_toEuclideanLin_le A v

lemma ell_lipschitz_affine (c : Euc d) (D : Matrix (Fin d) (Fin d) ℝ) :
    LipschitzWith ‖D‖₊ (fun z => c + mvec D z) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← ell_mvec_sub_right, coe_nnnorm]
  exact ell_norm_mvec_le D _

/-- `‖x ↦ D g(x) + c‖_{L²(μ)} ≤ ‖D‖ ‖g‖_{L²(μ)} + ‖c‖` for a probability law `μ`. -/
lemma ell_eLpNorm_affine_le {μ : Measure (Euc d)} [IsProbabilityMeasure μ] (D : Matrix (Fin d) (Fin d) ℝ)
    {g : Euc d → Euc d} (hg : Continuous g) (c : Euc d) :
    eLpNorm (fun x => mvec D (g x) + c) 2 μ ≤ ENNReal.ofReal ‖D‖ * eLpNorm g 2 μ + ‖c‖ₑ := by
  have hf1 : AEStronglyMeasurable (fun x => mvec D (g x)) μ := ((continuous_mvec' D).comp hg).aestronglyMeasurable
  have hadd : eLpNorm (fun x => mvec D (g x) + c) 2 μ ≤
      eLpNorm (fun x => mvec D (g x)) 2 μ + eLpNorm (fun _ : Euc d => c) 2 μ :=
    eLpNorm_add_le (f := fun x => mvec D (g x)) (g := fun _ : Euc d => c) (by norm_num)
  refine hadd.trans (add_le_add ?_ (le_of_eq ?_))
  · have h := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul hf1 (g := g) (c := ‖D‖₊)
      (Eventually.of_forall fun x => by
        rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm, coe_nnnorm, coe_nnnorm]
        exact ell_norm_mvec_le D (g x)) 2
    refine h.trans (le_of_eq ?_)
    rw [ENNReal.smul_def, smul_eq_mul, ← coe_nnnorm D, ENNReal.ofReal_coe_nnreal]
  · rw [eLpNorm_const c two_ne_zero (IsProbabilityMeasure.ne_zero μ), measure_univ, ENNReal.one_rpow, mul_one]

/-! ### Moments of the affine image -/

section Moments
variable {γ : Measure (Euc d)} [IsProbabilityMeasure γ]

lemma ell_integrable_pow4 (h4 : ∫⁻ y, ‖y‖ₑ ^ 4 ∂γ < ⊤) : Integrable (fun x : Euc d => ‖x‖ ^ 4) γ := by
  refine ⟨(by fun_prop : Continuous fun x : Euc d => ‖x‖ ^ 4).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => by positivity)]
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun x => ?_)) h4
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

lemma ell_lintegral_sq (h4 : ∫⁻ y, ‖y‖ₑ ^ 4 ∂γ < ⊤) : ∫⁻ y, ‖y‖ₑ ^ 2 ∂γ < ⊤ := by
  have hle : ∀ y : Euc d, ‖y‖ₑ ^ 2 ≤ 1 + ‖y‖ₑ ^ 4 := by
    intro y
    rcases le_total ‖y‖ₑ 1 with h | h
    · exact le_add_right (pow_le_one₀ (zero_le) h)
    · exact le_add_left (pow_le_pow_right₀ h (by norm_num))
  calc ∫⁻ y, ‖y‖ₑ ^ 2 ∂γ ≤ ∫⁻ y, (1 + ‖y‖ₑ ^ 4) ∂γ := lintegral_mono hle
    _ = ∫⁻ y, (1 : ℝ≥0∞) ∂γ + ∫⁻ y, ‖y‖ₑ ^ 4 ∂γ := lintegral_add_left measurable_const _
    _ < ⊤ := by
        rw [lintegral_const, measure_univ, mul_one]
        exact ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, h4⟩

lemma ell_measurable_affine (A : Matrix (Fin d) (Fin d) ℝ) (b : Euc d) :
    Measurable fun z : Euc d => mvec A z + b :=
  ((continuous_mvec' A).add continuous_const).measurable

lemma ell_integrable_pow4_map (h4i : Integrable (fun x : Euc d => ‖x‖ ^ 4) γ)
    (A : Matrix (Fin d) (Fin d) ℝ) (b : Euc d) :
    Integrable (fun x : Euc d => ‖x‖ ^ 4) (γ.map fun z => mvec A z + b) := by
  rw [integrable_map_measure (by fun_prop : Continuous fun x : Euc d => ‖x‖ ^ 4).aestronglyMeasurable (ell_measurable_affine A b).aemeasurable]
  refine Integrable.mono' ((h4i.const_mul (8 * ‖A‖ ^ 4)).add (integrable_const (8 * ‖b‖ ^ 4)))
    ((by fun_prop : Continuous fun x : Euc d => ‖x‖ ^ 4).comp ((continuous_mvec' A).add continuous_const)).aestronglyMeasurable
    (Eventually.of_forall fun z => ?_)
  simp only [Function.comp_apply, Real.norm_eq_abs, abs_pow, abs_norm]
  have h1 : ‖mvec A z + b‖ ≤ ‖A‖ * ‖z‖ + ‖b‖ :=
    (norm_add_le _ _).trans (add_le_add (ell_norm_mvec_le A z) le_rfl)
  set p := ‖A‖ * ‖z‖ with hp
  set q := ‖b‖
  have hp0 : 0 ≤ p := by positivity
  have hq0 : 0 ≤ q := norm_nonneg _
  have h2 : ‖mvec A z + b‖ ^ 4 ≤ (p + q) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) h1 4
  have e1 : (p + q) ^ 2 ≤ 2 * (p ^ 2 + q ^ 2) := by nlinarith [sq_nonneg (p - q)]
  have e2 : (p ^ 2 + q ^ 2) ^ 2 ≤ 2 * (p ^ 4 + q ^ 4) := by nlinarith [sq_nonneg (p ^ 2 - q ^ 2)]
  have e3 : (p + q) ^ 4 ≤ 8 * (p ^ 4 + q ^ 4) := by
    calc (p + q) ^ 4 = ((p + q) ^ 2) ^ 2 := by ring
      _ ≤ (2 * (p ^ 2 + q ^ 2)) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) e1 2
      _ = 4 * (p ^ 2 + q ^ 2) ^ 2 := by ring
      _ ≤ 8 * (p ^ 4 + q ^ 4) := by linarith
  calc ‖mvec A z + b‖ ^ 4 ≤ 8 * (p ^ 4 + q ^ 4) := h2.trans e3
    _ = 8 * ‖A‖ ^ 4 * ‖z‖ ^ 4 + 8 * ‖b‖ ^ 4 := by rw [hp, mul_pow]; ring

/-- `E μ = b`, `Cov(μ) = AAᵀ` (the computation of the frozen Wave 24d `field_ell`, without sphericity). -/
lemma ell_affine_moments (h2 : ∫⁻ x, ‖x‖ₑ ^ 2 ∂γ < ⊤) (hmean : meanVec γ = 0) (hcov : covMat γ = 1)
    (A : Matrix (Fin d) (Fin d) ℝ) (b : Euc d) :
    meanVec (γ.map fun z => mvec A z + b) = b ∧ covMat (γ.map fun z => mvec A z + b) = A * Aᵀ := by
  set f : Euc d → Euc d := fun z => mvec A z + b with hfdef
  have hf : Measurable f := ell_measurable_affine A b
  set μ := γ.map f with hμdef
  have hm0 : ∀ j, ∫ z, z j ∂γ = 0 := by
    intro j
    have := congrArg (fun v : Euc d => v j) hmean
    simpa [meanVec] using this
  have hfi : ∀ z i, f z i = ∑ j, A i j * z j + b i := by
    intro z i; simp only [hfdef, PiLp.add_apply, StatFormal.Wave24d.mvec_apply']
  have hmeanμ : meanVec μ = b := by
    ext i
    simp only [meanVec, hμdef]
    rw [integral_map hf.aemeasurable (PiLp.continuous_apply 2 _ i).aestronglyMeasurable]
    simp only [hfi]
    rw [integral_add (integrable_finsetSum _ fun j _ => (StatFormal.Wave24d.integrable_coord h2 j).const_mul _)
      (integrable_const _),
      integral_finsetSum _ fun j _ => (StatFormal.Wave24d.integrable_coord h2 j).const_mul _]
    simp [integral_const_mul, hm0]
  have hcovγ : ∀ k l, ∫ z, z k * z l ∂γ = if k = l then 1 else 0 := by
    intro k l
    have := congrFun (congrFun hcov k) l
    simp only [covMat, hmean] at this
    simpa [Matrix.one_apply] using this
  have hcovμ : covMat μ = A * Aᵀ := by
    ext i j
    change ∫ x, (x i - meanVec μ i) * (x j - meanVec μ j) ∂μ = _
    rw [hmeanμ, hμdef, integral_map (f := fun x : Euc d => (x i - b i) * (x j - b j)) hf.aemeasurable
      (((PiLp.continuous_apply 2 _ i).sub continuous_const).mul
        ((PiLp.continuous_apply 2 _ j).sub continuous_const)).aestronglyMeasurable]
    have hexp : ∀ z : Euc d, (f z i - b i) * (f z j - b j) = ∑ k, ∑ l, (A i k * A j l) * (z k * z l) := by
      intro z
      rw [hfi, hfi, add_sub_cancel_right, add_sub_cancel_right, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    simp only [hexp]
    rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
      (StatFormal.Wave24d.integrable_coord_mul h2 k l).const_mul _, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ fun l _ => (StatFormal.Wave24d.integrable_coord_mul h2 k l).const_mul _]
    simp only [integral_const_mul, hcovγ, mul_ite, mul_one, mul_zero, Matrix.transpose_apply]
    simp [Finset.sum_ite_eq]
  exact ⟨hmeanμ, hcovμ⟩

/-- The common setting of the corollary for one member `μ = (z ↦ Az + b)_#γ`. -/
lemma ell_setting (h4 : ∫⁻ y, ‖y‖ₑ ^ 4 ∂γ < ⊤) (hmean : meanVec γ = 0) (hcov : covMat γ = 1)
    (A : Matrix (Fin d) (Fin d) ℝ) (b : Euc d) (hA : A.det ≠ 0) :
    IsProbabilityMeasure (γ.map fun z => mvec A z + b) ∧
      Integrable (fun x : Euc d => ‖x‖ ^ 4) (γ.map fun z => mvec A z + b) ∧
      ∃ lam : ℝ, 0 < lam ∧ lam • (1 : Matrix (Fin d) (Fin d) ℝ) ≤ covMat (γ.map fun z => mvec A z + b) := by
  refine ⟨inferInstance,
    ell_integrable_pow4_map (ell_integrable_pow4 h4) A b, ?_⟩
  obtain ⟨lam, hlam, hle⟩ := exists_smul_one_le_mul_transpose (isUnit_iff_ne_zero.mpr hA)
  refine ⟨lam, hlam, ?_⟩
  rw [(ell_affine_moments (ell_lintegral_sq h4) hmean hcov A b).2]; exact hle

end Moments

lemma ell_memLp_two {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    (h4 : Integrable (fun x : Euc d => ‖x‖ ^ 4) μ) : MemLp (fun x : Euc d => x) 2 μ := by
  rw [memLp_two_iff_integrable_sq_norm (by fun_prop : Continuous fun x : Euc d => x).aestronglyMeasurable]
  exact integrable_of_le_poly h4 (by fun_prop : Continuous fun x : Euc d => ‖x‖ ^ 2) (C := 1) fun x => by
    rw [abs_of_nonneg (by positivity), one_mul]; exact sq_le_one_add_pow4 ‖x‖

/-- On `‖Σ̂ − Σ‖ ≤ λ/2` the sample covariance is `≥ λ/2`, hence `≥ 0`. -/
lemma ell_scov_nonneg {Sg : Matrix (Fin d) (Fin d) ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hle : lam • (1 : Matrix (Fin d) (Fin d) ℝ) ≤ Sg) {n : ℕ} (Y : Fin n → Euc d) (hn : ‖scov Y - Sg‖ ≤ lam / 2) :
    0 ≤ scov Y :=
  le_trans (by rw [Matrix.nonneg_iff_posSemidef]; exact Matrix.PosSemidef.one.smul (by linarith))
    (half_le_of_near hle (scov_isHermitian Y) hn)

lemma ell_small {Sg : Matrix (Fin d) (Fin d) ℝ} {lam : ℝ} (hlam : 0 < lam) {n : ℕ} {Y : Fin n → Euc d}
    (h : ‖scov Y - Sg‖ₑ ≤ ENNReal.ofReal (lam / 2)) : ‖scov Y - Sg‖ ≤ lam / 2 := by
  rwa [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff (by linarith)] at h

/-! ### (ii) -/

theorem fieldell_fwd : Claims.fieldell_fwd := by
  intro d γ _ A b Ω _ P _ X h4 hmean hcov hA hX hind hlaw
  obtain ⟨hprob, h4μ, lam, hlam, hle⟩ := ell_setting h4 hmean hcov A b hA
  set μ := γ.map fun z => mvec A z + b with hμ
  set Sg := covMat μ
  set m := meanVec μ
  set W := invSqrt Sg
  have hmem : MemLp (fun x : Euc d => x - m) 2 μ := (ell_memLp_two h4μ).sub (memLp_const m)
  set C1 := (eLpNorm (fun x : Euc d => x - m) 2 μ).toReal
  have hC1 : eLpNorm (fun x : Euc d => x - m) 2 μ = ENNReal.ofReal C1 :=
    (ENNReal.ofReal_toReal hmem.eLpNorm_ne_top).symm
  have hC10 : 0 ≤ C1 := ENNReal.toReal_nonneg
  set κ := (Real.sqrt (lam / 2))⁻¹
  set K1 := κ * (Real.sqrt lam)⁻¹ * (Real.sqrt lam)⁻¹
  have hκ : 0 ≤ κ := by positivity
  have hK1 : 0 ≤ K1 := by positivity
  have hcovB := bigOP_scov h4μ hX hind hlaw
  have hmeanB := bigOP_smean h4μ hX hind hlaw
  refine bigOP_of_le_on rate_nonneg rate_tendsto hcovB hmeanB (δ := lam / 2) (C := K1 * C1 + κ) (by positivity) 0
    fun n _ ω hsmall => ?_
  set Y : Fin n → Euc d := fun j => X j ω with hY
  try dsimp only at hsmall ⊢
  have hnorm : ‖scov Y - Sg‖ ≤ lam / 2 := ell_small hlam hsmall
  have hH : (scov Y).IsHermitian := scov_isHermitian Y
  have hW1 : ‖invSqrt (scov Y)‖ ≤ κ := norm_inv_sqrt_le (by positivity) (half_le_of_near hle hH hnorm)
  have hW2 : ‖invSqrt (scov Y) - W‖ ≤ K1 * ‖scov Y - Sg‖ := by
    refine (norm_inv_sqrt_sub_le hlam hle hH hnorm).trans (le_of_eq ?_)
    simp only [K1]; ring
  have hdecomp : (fun x => ellStdHat Y x - ellStd μ x) =
      fun x => mvec (invSqrt (scov Y) - W) (x - m) + mvec (invSqrt (scov Y)) (m - smean Y) := by
    funext x
    change mvec (invSqrt (scov Y)) (x - smean Y) - mvec W (x - m) = _
    have hx : x - smean Y = (x - m) + (m - smean Y) := by abel
    rw [hx, ell_mvec_add_right, ell_mvec_sub]; abel
  rw [hdecomp]
  refine (ell_eLpNorm_affine_le (g := fun x => x - m) _ (by fun_prop) _).trans ?_
  rw [hC1]
  simp only [← ofReal_norm]
  rw [← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_add (by positivity) (norm_nonneg _),
    ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hc0 : ‖mvec (invSqrt (scov Y)) (m - smean Y)‖ ≤ κ * ‖smean Y - m‖ := by
    refine (ell_norm_mvec_le _ _).trans ?_
    rw [norm_sub_rev]
    exact mul_le_mul_of_nonneg_right hW1 (norm_nonneg _)
  have hd1 : ‖invSqrt (scov Y) - W‖ * C1 ≤ K1 * ‖scov Y - Sg‖ * C1 := mul_le_mul_of_nonneg_right hW2 hC10
  have hp1 : 0 ≤ K1 * C1 * ‖smean Y - m‖ := by positivity
  have hp2 : 0 ≤ κ * ‖scov Y - Sg‖ := by positivity
  nlinarith

/-! ### (iii) -/

theorem fieldell_inv : Claims.fieldell_inv := by
  intro d γ _ A b Ω _ P _ Z h4 hmean hcov hA hZ hind hlaw
  obtain ⟨hprob, h4ν, lam, hlam, hle⟩ := ell_setting h4 hmean hcov A b hA
  set ν := γ.map fun z => mvec A z + b with hν
  set Sg := covMat ν
  set m := meanVec ν
  set R := CFC.sqrt Sg
  have hcovB := bigOP_scov h4ν hZ hind hlaw
  have hmeanB := bigOP_smean h4ν hZ hind hlaw
  -- the root error is `O_P(n^{-1/2})`
  have hroot : BigOP P (fun n => 1 / Real.sqrt n)
      (fun n ω => ‖CFC.sqrt (scov (fun j : Fin n => Z j ω)) - R‖ₑ) := by
    refine bigOP_of_le_on rate_nonneg rate_tendsto hcovB (bigOP_zero _) (δ := lam / 2)
      (C := (Real.sqrt lam)⁻¹) (by positivity) 0 fun n _ ω hsmall => ?_
    try dsimp only at hsmall ⊢
    have hnorm := ell_small hlam hsmall
    have h1 := norm_sqrt_sub_le hlam hle (ell_scov_nonneg hlam hle _ hnorm)
    rw [norm_sub_rev, norm_sub_rev Sg] at h1
    rw [add_zero, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (h1.trans (le_of_eq ?_))
    rw [div_eq_inv_mul]
  -- the constant `‖z‖_{L²(γ)}`
  have hmemγ : MemLp (fun x : Euc d => x) 2 γ := ell_memLp_two (ell_integrable_pow4 h4)
  set C2 := (eLpNorm (fun x : Euc d => x) 2 γ).toReal
  have hC2 : eLpNorm (fun x : Euc d => x) 2 γ = ENNReal.ofReal C2 :=
    (ENNReal.ofReal_toReal hmemγ.eLpNorm_ne_top).symm
  have hC20 : 0 ≤ C2 := ENNReal.toReal_nonneg
  refine ⟨‖R‖₊, ellInv ν, fun _ _ _ => 0,
    fun n ω z => (smean (fun j : Fin n => Z j ω) - m) + mvec (CFC.sqrt (scov (fun j : Fin n => Z j ω)) - R) z,
    ell_lipschitz_affine m R, EventuallyEq.rfl, ?_, ?_, ?_, ?_⟩
  · -- the decomposition, `h_n = 0`
    intro n ω z
    change smean (fun j : Fin n => Z j ω) + mvec (CFC.sqrt (scov fun j : Fin n => Z j ω)) z - (m + mvec R z) =
      0 + ((smean (fun j : Fin n => Z j ω) - m) + mvec (CFC.sqrt (scov (fun j : Fin n => Z j ω)) - R) z)
    rw [ell_mvec_sub]; abel
  · -- `‖h_n‖_∞ = 0`
    refine bigOP_mono rate_nonneg rate_tendsto (bigOP_zero _) fun n ω => le_of_eq ?_
    simp [supNorm]
  · -- `Lip(k_n) = O_P(1)`
    intro η hη
    obtain ⟨M, N, hM⟩ := hroot η hη
    refine ⟨M.toNNReal, max N 1, fun n hn => ?_⟩
    obtain ⟨B, hBm, hPB, hBω⟩ := hM n (le_trans (le_max_left _ _) hn)
    refine ⟨B, hBm, hPB, fun ω hω => ?_⟩
    refine (ell_lipschitz_affine _ _).weaken ?_
    have h1 := hBω ω hω
    try dsimp only at h1
    rw [← ofReal_norm] at h1
    have hr1 : 1 / Real.sqrt n ≤ 1 := rate_le_one (le_trans (le_max_right _ _) hn)
    have h2 : M * (1 / Real.sqrt n) ≤ max M 0 := by
      rcases le_total M 0 with hM0 | hM0
      · have : M * (1 / Real.sqrt n) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hM0 (rate_nonneg n)
        exact this.trans (le_max_right _ _)
      · calc M * (1 / Real.sqrt n) ≤ M * 1 := mul_le_mul_of_nonneg_left hr1 hM0
          _ = M := mul_one M
          _ ≤ max M 0 := le_max_left _ _
    have h3 : ‖CFC.sqrt (scov fun j : Fin n => Z j ω) - R‖ ≤ max M 0 :=
      (ENNReal.ofReal_le_ofReal_iff (le_max_right _ _)).mp (h1.trans (ENNReal.ofReal_le_ofReal h2))
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
    exact h3
  · -- `‖k_n‖_{L²(γ)} = O_P(n^{-1/2})`
    refine bigOP_of_le_on rate_nonneg rate_tendsto hroot hmeanB (δ := 1) (C := max C2 1) one_pos 0
      fun n _ ω _ => ?_
    try dsimp only
    have hk : (fun z => (smean (fun j : Fin n => Z j ω) - m) + mvec (CFC.sqrt (scov (fun j : Fin n => Z j ω)) - R) z)
        = fun z => mvec (CFC.sqrt (scov (fun j : Fin n => Z j ω)) - R) z + (smean (fun j : Fin n => Z j ω) - m) := by
      funext z; exact add_comm _ _
    rw [hk]
    refine (ell_eLpNorm_affine_le (g := fun z => z) _ continuous_id _).trans ?_
    rw [hC2]
    simp only [← ofReal_norm]
    rw [← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_add (by positivity) (norm_nonneg _),
      ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    set a := ‖CFC.sqrt (scov fun j : Fin n => Z j ω) - R‖
    set e := ‖smean (fun j : Fin n => Z j ω) - m‖
    have ha : 0 ≤ a := norm_nonneg _
    have he : 0 ≤ e := norm_nonneg _
    have h1 : a * C2 ≤ a * max C2 1 := mul_le_mul_of_nonneg_left (le_max_left _ _) ha
    have h2 : e ≤ e * max C2 1 := le_mul_of_one_le_right he (le_max_right _ _)
    nlinarith

/-! ### The rate -/

/-- `(i)` for one member, from the frozen Wave 24d `field_ell` at `W = Σ^{-1/2}`. -/
lemma ell_standardises {γ : Measure (Euc d)} [IsProbabilityMeasure γ] (hsph : IsSpherical γ)
    (h4 : ∫⁻ y, ‖y‖ₑ ^ 4 ∂γ < ⊤) (hmean : meanVec γ = 0) (hcov : covMat γ = 1)
    (A : Matrix (Fin d) (Fin d) ℝ) (b : Euc d) (hA : A.det ≠ 0) :
    Standardises (γ.map fun z => mvec A z + b) γ (ellStd (γ.map fun z => mvec A z + b))
      (ellInv (γ.map fun z => mvec A z + b)) := by
  obtain ⟨-, -, lam, hlam, hle⟩ := ell_setting h4 hmean hcov A b hA
  set μ := γ.map fun z => mvec A z + b
  have hW : invSqrt (covMat μ) = (CFC.sqrt (covMat μ))⁻¹ := rfl
  have hWs : (invSqrt (covMat μ))ᵀ = invSqrt (covMat μ) := by rw [hW]; exact inv_sqrt_transpose _
  have hWW : invSqrt (covMat μ) * invSqrt (covMat μ) * covMat μ = 1 := by
    rw [hW]; exact inv_sqrt_mul_inv_sqrt_mul hlam hle
  have h := (StatFormal.Wave24d.field_ell d γ hsph (ell_lintegral_sq h4) hmean hcov A b hA).2.2
    (invSqrt (covMat μ)) hWs hWW
  have hinv : (fun z => mvec (invSqrt (covMat μ))⁻¹ z + meanVec μ) = ellInv μ := by
    funext z
    rw [hW, inv_inv_sqrt hlam hle, add_comm]; rfl
  rw [hinv] at h
  exact h

theorem fieldell_rate_of (hJ : Claims.fieldJ_rate) : Claims.fieldell_rate := by
  intro d γ _ A₀ b₀ A b Ω _ P _ X Z hsph h4 hmean hcov hA₀ hA hX hindX hlawX hZ hindZ hlawZ
  obtain ⟨L, hL⟩ := fieldell_inv d γ A b Ω P Z h4 hmean hcov hA hZ hindZ hlawZ
  have hRprob : ∀ s, IsProbabilityMeasure (γ.map fun z => mvec (A₀ s) z + b₀ s) := fun s =>
    (ell_setting h4 hmean hcov (A₀ s) (b₀ s) (hA₀ s)).1
  have hνprob : IsProbabilityMeasure (γ.map fun z => mvec A z + b) := (ell_setting h4 hmean hcov A b hA).1
  exact hJ d (fun s => γ.map fun z => mvec (A₀ s) z + b₀ s) (γ.map fun z => mvec A z + b) γ
    (fun s => ellStd (γ.map fun z => mvec (A₀ s) z + b₀ s)) (fun s => ellInv (γ.map fun z => mvec (A₀ s) z + b₀ s))
    (ellStd (γ.map fun z => mvec A z + b)) (ellInv (γ.map fun z => mvec A z + b)) Ω P
    (fun n ω s => ellStdHat (fun j : Fin n => X s j ω)) (fun n ω => ellInvHat (fun j : Fin n => Z j ω))
    (fun n => 1 / Real.sqrt n) L inferInstance rate_nonneg hRprob hνprob inferInstance
    (fun s => ell_standardises hsph h4 hmean hcov (A₀ s) (b₀ s) (hA₀ s))
    (ell_standardises hsph h4 hmean hcov A b hA)
    (fun n ω s => ((continuous_mvec' _).comp (continuous_id.sub continuous_const)).measurable)
    (fun n ω => (continuous_const.add (continuous_mvec' _)).measurable)
    (fun s => fieldell_fwd d γ (A₀ s) (b₀ s) Ω P (X s) h4 hmean hcov (hA₀ s) (hX s) (hindX s) (hlawX s))
    hL

end StatFormal.Wave30h

