import StatFormal.Archive.WaveP2b.RouteGeom
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Route — a Gaussian measure on `H` with injective covariance charges no Lipschitz hypersurface (untrusted)

Let `μ` be Gaussian on a separable Hilbert space `H` with covariance form `B` injective. Write `T v` for the Riesz
vector of `B v` (`⟪T v, y⟫ = B v y`). The range of `T` is dense (its orthogonal is `ker B = 0`), so for
`A = A_w` there is `v` with `u = T v` transversal: `a(u) > L ‖p u‖`. Put `σ² = B v v > 0`, `Y = ⟪v, ·⟫`,
`W = id − (Y/σ²) u`. `(Y, W)` is a continuous linear image of a Gaussian, hence Gaussian, and uncorrelated, hence
independent (Mathlib `HasGaussianLaw.indepFun_of_covariance_inner`). As `x = W + (Y/σ²) u`, Fubini gives
`μ(A) = ∫ 𝓛(Y)({t : W + (t/σ²)u ∈ A}) d𝓛(W)`, and every slice has at most one point while `𝓛(Y) = N(·, σ²)` is
atomless. This replaces the paper's eigenbasis + block criterion (no spectral theorem needed).
-/

noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.WaveP2b

open StatFormal.OTFD.Wave1 (PellClass IsLipHyp lipHyp)

section Gauss
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- The Riesz vector of `B v`: `⟪covVec μ v, y⟫ = B v y`. -/
def covVec (μ : Measure H) (v : H) : H := (InnerProductSpace.toDual ℝ H).symm (covarianceBilin μ v)

lemma inner_covVec (μ : Measure H) (v y : H) : ⟪covVec μ v, y⟫_ℝ = covarianceBilin μ v y := by
  simp [covVec, InnerProductSpace.toDual_symm_apply]

/-- `covVec μ` as a linear map. -/
def covVecL (μ : Measure H) : H →ₗ[ℝ] H :=
  ((InnerProductSpace.toDual ℝ H).symm.toLinearEquiv.toLinearMap).comp
    (covarianceBilin μ).toLinearMap

lemma covVecL_apply (μ : Measure H) (v : H) : covVecL μ v = covVec μ v := rfl

/-- The range of `T` is dense when `B` is injective. -/
lemma dense_range_covVec (μ : Measure H) (hinj : Function.Injective (covarianceBilin μ)) (w : H) :
    w ∈ closure (Set.range (covVec μ)) := by
  have hK : (LinearMap.range (covVecL μ))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    rw [Submodule.mem_orthogonal] at hy
    have hB : covarianceBilin μ y = covarianceBilin μ 0 := by
      ext v
      have := hy (covVec μ v) ⟨v, rfl⟩
      rw [inner_covVec, covarianceBilin_comm] at this
      simpa using this
    exact hinj hB
  have htop := (Submodule.topologicalClosure_eq_top_iff).2 hK
  have hw : w ∈ (LinearMap.range (covVecL μ)).topologicalClosure := by rw [htop]; trivial
  have hw' : w ∈ ((LinearMap.range (covVecL μ)).topologicalClosure : Set H) := hw
  rw [Submodule.topologicalClosure_coe] at hw'
  have hr : ((LinearMap.range (covVecL μ) : Submodule ℝ H) : Set H) = Set.range (covVec μ) := by
    ext x; simp [covVecL_apply]
  rwa [hr] at hw'

/-- A transversal vector in the range of `T`. -/
lemma exists_transversal (μ : Measure H) (hinj : Function.Injective (covarianceBilin μ)) {w : H} (hw : w ≠ 0)
    (L : ℝ≥0) : ∃ v : H, (L : ℝ) * ‖pZ w (covVec μ v)‖ < acoef w (covVec μ v) := by
  have hw' : 0 < ‖w‖ := norm_pos_iff.2 hw
  set ε : ℝ := 1 / (2 * (2 * L + 1 / ‖w‖)) with hε
  have hden : 0 < 2 * L + 1 / ‖w‖ := by positivity
  have hεpos : 0 < ε := by positivity
  obtain ⟨u, ⟨v, rfl⟩, huw⟩ := Metric.mem_closure_iff.1 (dense_range_covVec μ hinj w) ε hεpos
  refine ⟨v, ?_⟩
  set u := covVec μ v
  have hd : ‖u - w‖ < ε := by rw [← dist_eq_norm, dist_comm]; exact huw
  -- `a(u) ≥ 1 − ε/‖w‖`
  have ha : acoef w u = 1 + acoef w (u - w) := by
    rw [← acoef_self hw, ← acoef_add]; congr 1; abel
  have ha2 : |acoef w (u - w)| ≤ ‖u - w‖ / ‖w‖ := by
    rw [acoef, abs_div, abs_of_pos (by positivity : (0:ℝ) < ‖w‖ ^ 2)]
    have hcs := abs_real_inner_le_norm (u - w) w
    calc |⟪u - w, w⟫_ℝ| / ‖w‖ ^ 2 ≤ ‖u - w‖ * ‖w‖ / ‖w‖ ^ 2 := by gcongr
      _ = ‖u - w‖ / ‖w‖ := by field_simp
  -- `‖p u‖ ≤ 2ε`
  have hp : pZ w u = pZ w (u - w) := by
    have : pZ w w = 0 := by simp [pZ, acoef_self hw]
    rw [show u = (u - w) + w by abel, pZ_add, this, add_zero]; simp
  have hp2 : ‖pZ w u‖ ≤ 2 * ‖u - w‖ := hp ▸ norm_pZ_le hw (u - w)
  have h1 : (L : ℝ) * ‖pZ w u‖ ≤ 2 * L * ε := by
    calc (L : ℝ) * ‖pZ w u‖ ≤ L * (2 * ‖u - w‖) := by gcongr
      _ ≤ L * (2 * ε) := by gcongr
      _ = 2 * L * ε := by ring
  have h2 : 1 - ε / ‖w‖ < acoef w u := by
    have : ‖u - w‖ / ‖w‖ < ε / ‖w‖ := by gcongr
    have := neg_abs_le (acoef w (u - w))
    linarith
  have h3 : 2 * L * ε + ε / ‖w‖ = 1 / 2 := by
    rw [hε]; field_simp
  linarith

/-- Cauchy–Schwarz for a positive semidefinite form: `B v v = 0 ⇒ B v y = 0`. -/
lemma covarianceBilin_eq_zero_of_self (μ : Measure H) {v : H} (hv : covarianceBilin μ v v = 0) (y : H) :
    covarianceBilin μ v y = 0 := by
  have hq : ∀ t : ℝ, 0 ≤ covarianceBilin μ y y * (t * t) + 2 * covarianceBilin μ v y * t +
      covarianceBilin μ v v := by
    intro t
    have h := covarianceBilin_self_nonneg (μ := μ) (v + t • y)
    simp only [map_add, map_smul, add_apply, smul_apply,
      smul_eq_mul] at h
    rw [covarianceBilin_comm y v] at h
    nlinarith [h]
  have hd := discrim_le_zero hq
  rw [discrim, hv] at hd
  nlinarith [sq_nonneg (covarianceBilin μ v y)]


/-- **Core.** A Gaussian measure on `H` with injective covariance gives mass `0` to every Lipschitz
hypersurface. -/
theorem gaussian_null (μ : Measure H) [IsGaussian μ] (hinj : Function.Injective (covarianceBilin μ))
    (S : Set H) (hS : IsLipHyp S) : μ S = 0 := by
  obtain ⟨w, hw, τ, ⟨L, hτ⟩, rfl⟩ := hS
  obtain ⟨v, hv⟩ := exists_transversal μ hinj hw L
  set u := covVec μ v with hu
  have hmem : MemLp id 2 μ := IsGaussian.memLp_two_id
  set σ2 := covarianceBilin μ v v with hσ2
  have hσpos : 0 < σ2 := by
    rcases (covarianceBilin_self_nonneg (μ := μ) v).lt_or_eq with h | h
    · exact h
    · exfalso
      have hu0 : u = 0 := by
        have : ⟪u, u⟫_ℝ = 0 := by
          rw [hu, inner_covVec]; exact covarianceBilin_eq_zero_of_self μ h.symm _
        exact inner_self_eq_zero.1 this
      rw [hu0] at hv
      simp [pZ, acoef] at hv
  let Lmap : H →L[ℝ] ℝ × H :=
    (innerSL ℝ v).prod (ContinuousLinearMap.id ℝ H - σ2⁻¹ • (innerSL ℝ v).smulRight u)
  have hLapply : ∀ x, Lmap x = (⟪v, x⟫_ℝ, x - (⟪v, x⟫_ℝ / σ2) • u) := by
    intro x
    simp [Lmap, div_eq_inv_mul, mul_smul]
  have hG : HasGaussianLaw (fun x => (⟪v, x⟫_ℝ, x - (⟪v, x⟫_ℝ / σ2) • u)) μ := by
    have := (IsGaussian.hasGaussianLaw_id (μ := μ)).map_fun Lmap
    simpa only [id, hLapply] using this
  have hind : IndepFun (fun x : H => ⟪v, x⟫_ℝ) (fun x => x - (⟪v, x⟫_ℝ / σ2) • u) μ := by
    refine hG.indepFun_of_covariance_inner (fun a y => ?_)
    have e1 : (fun x : H => ⟪a, ⟪v, x⟫_ℝ⟫_ℝ) = fun x => ⟪a • v, x⟫_ℝ := by
      ext x; simp [real_inner_smul_left, mul_comm]
    have e2 : (fun x : H => ⟪y, x - (⟪v, x⟫_ℝ / σ2) • u⟫_ℝ) =
        fun x => ⟪y - (⟪y, u⟫_ℝ / σ2) • v, x⟫_ℝ := by
      ext x
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
      rw [real_inner_comm x y]; ring
    rw [e1, e2, ← covarianceBilin_apply_eq_cov hmem]
    have hyu : ⟪y, u⟫_ℝ = covarianceBilin μ v y := by rw [real_inner_comm, hu, inner_covVec]
    simp only [map_smul, map_sub]
    simp only [FunLike.coe_smul, Pi.smul_apply,
      smul_eq_mul]
    rw [hyu, ← hσ2]
    field_simp
    ring
  have hYm : Measurable (fun x : H => ⟪v, x⟫_ℝ) := by fun_prop
  have hWm : Measurable (fun x : H => x - (⟪v, x⟫_ℝ / σ2) • u) := by fun_prop
  have hD : MeasurableSet {p : ℝ × H | p.2 + (p.1 / σ2) • u ∈ lipHyp w τ} :=
    ((isClosed_lipHyp hw hτ).preimage (by fun_prop)).measurableSet
  have hpre : lipHyp w τ = (fun x => (⟪v, x⟫_ℝ, x - (⟪v, x⟫_ℝ / σ2) • u)) ⁻¹'
      {p : ℝ × H | p.2 + (p.1 / σ2) • u ∈ lipHyp w τ} := by
    ext x; simp
  rw [hpre, ← Measure.map_apply (hYm.prodMk hWm) hD,
    (indepFun_iff_map_prod_eq_prod_map_map hYm.aemeasurable hWm.aemeasurable).1 hind,
    Measure.prod_apply_symm hD]
  have hcoe : (⇑(innerSL ℝ v) : H → ℝ) = fun x => ⟪v, x⟫_ℝ := by ext x; simp
  have hlaw : μ.map (fun x : H => ⟪v, x⟫_ℝ) =
      gaussianReal (∫ x, (innerSL ℝ v) x ∂μ) (Var[⇑(innerSL ℝ v); μ]).toNNReal := by
    rw [← IsGaussian.map_eq_gaussianReal (innerSL ℝ v), hcoe]
  have hvar : Var[⇑(innerSL ℝ v); μ] = σ2 := by rw [hcoe, hσ2, covarianceBilin_self hmem]
  have hne : (Var[⇑(innerSL ℝ v); μ]).toNNReal ≠ 0 := by
    rw [hvar]; exact (Real.toNNReal_pos.2 hσpos).ne'
  have := nullSingletonClass_gaussianReal (μ := ∫ x, (innerSL ℝ v) x ∂μ) hne
  have hslice : ∀ z : H, (μ.map (fun x : H => ⟪v, x⟫_ℝ)) {a : ℝ | z + (a / σ2) • u ∈ lipHyp w τ} = 0 := by
    intro z
    rw [hlaw]
    apply Set.Subsingleton.measure_zero
    intro s hs t ht
    have h := lipHyp_line_subsingleton hw hτ hv z (show s / σ2 ∈ {s : ℝ | z + s • u ∈ lipHyp w τ} from hs)
      (show t / σ2 ∈ {s : ℝ | z + s • u ∈ lipHyp w τ} from ht)
    exact (div_left_inj' hσpos.ne').1 h
  exact (lintegral_congr fun z => hslice z).trans lintegral_zero

end Gauss

end StatFormal.WaveP2b
