import StatFormal.Lib.ChiSquare.LaurentMassart
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Probability.Moments.CovarianceBilin

/-!
# Whitening a centred Gaussian vector with injective covariance

Untrusted library code: no `Statements.lean` is involved.

Let `ν` be a centred Gaussian measure on a finite-dimensional real inner product space `E` whose covariance is
injective (`Var_ν⟨v, ·⟩ > 0` for `v ≠ 0`). With `S` the covariance operator of `ν` (Mathlib `covarianceOperator`,
`⟨Sv, w⟩ = ∫ ⟨v, z⟩⟨w, z⟩ dν`), `b` an orthonormal eigenbasis of `S` and `λ_i > 0` its eigenvalues, the whitening map
`W z = (⟨b_i, z⟩/√λ_i)_i` pushes `ν` onto the standard Gaussian `N(0, I_n)` of `ℝ^n`, `n = dim E`. Consequently
`‖W Z‖² = Σ_i ⟨b_i, Z⟩²/λ_i ∼ χ²_n` for `Z ∼ ν`, and the Laurent–Massart bounds apply to it.

## Main results

* `covOp_inner`, `variance_eq_covOp`: `⟨Sv, w⟩ = Cov_ν(⟨v,·⟩, ⟨w,·⟩)`, `Var_ν⟨v,·⟩ = ⟨Sv, v⟩`;
* `eigval_pos`: the eigenvalues are positive;
* `map_whiten`: `ν.map W = stdGaussian (EuclideanSpace ℝ (Fin n))`;
* `norm_whiten_sq`: `‖W z‖² = Σ_i ⟨b_i, z⟩²/λ_i`; `covOp_whitenPre`: `S(Σ_i (⟨b_i, x⟩/λ_i) b_i) = x`;
* `map_normSq_whiten`: `‖W·‖² ∼ χ²_n` under `ν`.
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.ChiSquare

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (ν : Measure E) [IsGaussian ν]

/-- `⟨Sv, w⟩ = Cov_ν(v, w)` for a centred `ν`. -/
lemma covOp_inner (hm : ∫ z, z ∂ν = 0) (v w : E) :
    ⟪covarianceOperator ν v, w⟫ = covarianceBilin ν v w := by
  rw [covarianceOperator_inner IsGaussian.memLp_two_id, covarianceBilin_apply IsGaussian.memLp_two_id]
  simp [hm]

lemma variance_eq_covOp (hm : ∫ z, z ∂ν = 0) (v : E) :
    Var[fun z => ⟪v, z⟫; ν] = ⟪covarianceOperator ν v, v⟫ := by
  rw [covOp_inner ν hm, covarianceBilin_self IsGaussian.memLp_two_id]

omit [IsGaussian ν] in
lemma covOp_isSymmetric : (covarianceOperator ν : E →ₗ[ℝ] E).IsSymmetric :=
  isPositive_covarianceOperator.isSymmetric

/-- The orthonormal eigenbasis of the covariance operator. -/
def eigB : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E := (covOp_isSymmetric ν).eigenvectorBasis rfl

/-- The eigenvalues of the covariance operator. -/
def eigval (i : Fin (Module.finrank ℝ E)) : ℝ := (covOp_isSymmetric ν).eigenvalues rfl i

omit [IsGaussian ν] in
lemma covOp_eigB (i : Fin (Module.finrank ℝ E)) : covarianceOperator ν (eigB ν i) = eigval ν i • eigB ν i := by
  have := (covOp_isSymmetric ν).apply_eigenvectorBasis rfl i
  exact this

lemma eigval_eq (hm : ∫ z, z ∂ν = 0) (i : Fin (Module.finrank ℝ E)) :
    eigval ν i = Var[fun z => ⟪eigB ν i, z⟫; ν] := by
  rw [variance_eq_covOp ν hm, covOp_eigB, real_inner_smul_left, real_inner_self_eq_norm_sq,
    (eigB ν).orthonormal.1 i]
  ring

lemma eigval_pos (hm : ∫ z, z ∂ν = 0) (hinj : ∀ v : E, v ≠ 0 → 0 < Var[fun z => ⟪v, z⟫; ν])
    (i : Fin (Module.finrank ℝ E)) : 0 < eigval ν i := by
  rw [eigval_eq ν hm]
  exact hinj _ ((eigB ν).orthonormal.ne_zero i)

/-- The colouring map `A u = Σ_i (u_i/√λ_i) b_i` (the adjoint of the whitening map). -/
def colour : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => ∑ i, (u i / √(eigval ν i)) • eigB ν i
      map_add' := fun u u' => by simp [add_div, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c u => by simp [Finset.smul_sum, smul_smul, mul_div_assoc] }

omit [IsGaussian ν] in
lemma colour_apply (u : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    colour ν u = ∑ i, (u i / √(eigval ν i)) • eigB ν i := rfl

/-- The whitening map `W z = (⟨b_i, z⟩/√λ_i)_i`. -/
def whiten : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := ContinuousLinearMap.adjoint (colour ν)

lemma whiten_apply (z : E) (i : Fin (Module.finrank ℝ E)) : whiten ν z i = ⟪eigB ν i, z⟫ / √(eigval ν i) := by
  have h := ContinuousLinearMap.adjoint_inner_right (colour ν) (EuclideanSpace.single i 1) z
  rw [EuclideanSpace.inner_single_left] at h
  simp only [map_one, one_mul] at h
  rw [whiten, h, colour_apply, sum_inner]
  rw [Finset.sum_eq_single i]
  · simp [real_inner_smul_left]; ring
  · intro j _ hj; simp [hj]
  · simp

lemma norm_whiten_sq (hm : ∫ z, z ∂ν = 0) (hinj : ∀ v : E, v ≠ 0 → 0 < Var[fun z => ⟪v, z⟫; ν]) (z : E) :
    ‖whiten ν z‖ ^ 2 = ∑ i, ⟪eigB ν i, z⟫ ^ 2 / eigval ν i := by
  rw [EuclideanSpace.real_norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [whiten_apply, div_pow, Real.sq_sqrt (eigval_pos ν hm hinj i).le]

lemma covOp_colour_inner (hm : ∫ z, z ∂ν = 0) (hinj : ∀ v : E, v ≠ 0 → 0 < Var[fun z => ⟪v, z⟫; ν])
    (u u' : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    ⟪covarianceOperator ν (colour ν u), colour ν u'⟫ = ⟪u, u'⟫ := by
  rw [colour_apply, colour_apply, map_sum]
  simp_rw [map_smul, covOp_eigB, smul_smul]
  rw [(eigB ν).orthonormal.inner_sum, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hl := eigval_pos ν hm hinj i
  have hs : √(eigval ν i) * √(eigval ν i) = eigval ν i := Real.mul_self_sqrt hl.le
  have hs0 : 0 < √(eigval ν i) := Real.sqrt_pos.2 hl
  simp only [conj_trivial, RCLike.inner_apply]
  rw [show u.ofLp i / √(eigval ν i) * eigval ν i * (u'.ofLp i / √(eigval ν i)) =
      u'.ofLp i * u.ofLp i * (eigval ν i / (√(eigval ν i) * √(eigval ν i))) by ring, hs, div_self hl.ne', mul_one]

/-- **Whitening.** `W#ν = N(0, I_n)`. -/
theorem map_whiten (hm : ∫ z, z ∂ν = 0) (hinj : ∀ v : E, v ≠ 0 → 0 < Var[fun z => ⟪v, z⟫; ν]) :
    ν.map (whiten ν) = stdGaussian (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) := by
  refine IsGaussian.ext ?_ ?_
  · simp only [id]
    rw [integral_id_stdGaussian]
    change ∫ x, x ∂(ν.map (whiten ν)) = 0
    rw [ContinuousLinearMap.integral_id_map (IsGaussian.integrable_id) (whiten ν), hm, map_zero]
  · rw [covarianceBilin_stdGaussian]
    ext u u'
    rw [covarianceBilin_map IsGaussian.memLp_two_id, whiten, ContinuousLinearMap.adjoint_adjoint,
      ← covOp_inner ν hm, covOp_colour_inner ν hm hinj]
    rfl

/-- `‖W·‖² ∼ χ²_n` under `ν`. -/
theorem map_normSq_whiten (hm : ∫ z, z ∂ν = 0) (hinj : ∀ v : E, v ≠ 0 → 0 < Var[fun z => ⟪v, z⟫; ν]) :
    ν.map (fun z => ‖whiten ν z‖ ^ 2) = TauCeti.Probability.chiSquaredMeasure (Module.finrank ℝ E) := by
  rw [show (fun z => ‖whiten ν z‖ ^ 2) = (fun x => ‖x‖ ^ 2) ∘ whiten ν from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop), map_whiten ν hm hinj, stdGaussian_map_normSq]

/-- The preimage `y = Σ_i (⟨b_i, x⟩/λ_i) b_i` of `x` under `S`. -/
def whitenPre (x : E) : E := ∑ i, (⟪eigB ν i, x⟫ / eigval ν i) • eigB ν i

lemma covOp_whitenPre (hm : ∫ z, z ∂ν = 0) (hinj : ∀ v : E, v ≠ 0 → 0 < Var[fun z => ⟪v, z⟫; ν]) (x : E) :
    covarianceOperator ν (whitenPre ν x) = x := by
  rw [whitenPre, map_sum]
  simp_rw [map_smul, covOp_eigB, smul_smul]
  conv_rhs => rw [← (eigB ν).sum_repr' x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [div_mul_cancel₀ _ (eigval_pos ν hm hinj i).ne']

lemma inner_covOp_whitenPre (hm : ∫ z, z ∂ν = 0) (hinj : ∀ v : E, v ≠ 0 → 0 < Var[fun z => ⟪v, z⟫; ν])
    (x : E) : ⟪covarianceOperator ν (whitenPre ν x), whitenPre ν x⟫ = ‖whiten ν x‖ ^ 2 := by
  rw [covOp_whitenPre ν hm hinj, norm_whiten_sq ν hm hinj, whitenPre, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_right, real_inner_comm]; ring

end StatFormal.ChiSquare
