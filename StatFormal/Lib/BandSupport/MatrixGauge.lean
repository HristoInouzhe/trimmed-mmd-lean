import StatFormal.Archive.OTFD.Wave8c.RouteTransfer
import StatFormal.Archive.OTFD.Wave8c.RouteNaive
import Mathlib.Analysis.Matrix.Spectrum

/-!
# The `M`-gauge against the Euclidean norm: `max_{‖u‖ = 1} ‖u‖_M = λ_max(M)^{1/2}` (untrusted library)

With an orthonormal eigenvector basis `b` of the symmetric `M`, `⟨u, Mu⟩ = Σ_i λ_i ⟨b_i, u⟩²` and
`‖u‖² = Σ_i ⟨b_i, u⟩²` (Parseval), so `⟨u, Mu⟩ ≤ λ_max ‖u‖²` with equality at a top eigenvector.
-/

noncomputable section
open Matrix
open scoped InnerProductSpace RealInnerProductSpace

set_option linter.unusedSectionVars false

namespace StatFormal.BandSupport

open StatFormal.OTFD.Wave8c (mvec mnorm inner_mvec inner_mvec_symm)

variable {K : ℕ} {M : Matrix (Fin K) (Fin K) ℝ}

lemma mvec_eigenvectorBasis (hM : M.IsHermitian) (i : Fin K) :
    mvec M (hM.eigenvectorBasis i) = hM.eigenvalues i • hM.eigenvectorBasis i := by
  ext k
  simpa [mvec, Matrix.toLpLin_apply] using congrFun (hM.mulVec_eigenvectorBasis i) k

lemma inner_mvec_eq_sum (hM : M.IsHermitian) (u : EuclideanSpace ℝ (Fin K)) :
    ⟪u, mvec M u⟫ = ∑ i, hM.eigenvalues i * ⟪hM.eigenvectorBasis i, u⟫ ^ 2 := by
  rw [← hM.eigenvectorBasis.sum_inner_mul_inner u (mvec M u)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_mvec_symm hM (hM.eigenvectorBasis i) u, mvec_eigenvectorBasis hM, real_inner_smul_left,
    real_inner_comm u]
  ring

lemma norm_sq_eq_sum (b : OrthonormalBasis (Fin K) ℝ (EuclideanSpace ℝ (Fin K))) (u : EuclideanSpace ℝ (Fin K)) :
    ‖u‖ ^ 2 = ∑ i, ⟪b i, u⟫ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner u u]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm u]; ring

lemma mnorm_eq_sqrt_inner (u : EuclideanSpace ℝ (Fin K)) : mnorm M u = Real.sqrt ⟪u, mvec M u⟫ := by
  rw [inner_mvec]; rfl

/-- `⟨u, Mu⟩ ≤ λ_max ‖u‖²`. -/
lemma inner_mvec_le (hM : M.IsHermitian) [NeZero K] (u : EuclideanSpace ℝ (Fin K)) :
    ⟪u, mvec M u⟫ ≤ (⨆ i, hM.eigenvalues i) * ‖u‖ ^ 2 := by
  rw [inner_mvec_eq_sum hM, norm_sq_eq_sum hM.eigenvectorBasis, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  exact le_ciSup (Set.finite_range _).bddAbove i

/-- The top eigenvector attains it. -/
lemma exists_top_eigenvector (hM : M.IsHermitian) [NeZero K] :
    ∃ u : EuclideanSpace ℝ (Fin K), ‖u‖ = 1 ∧ ⟪u, mvec M u⟫ = ⨆ i, hM.eigenvalues i := by
  obtain ⟨i₀, hi₀⟩ := exists_eq_ciSup_of_finite (f := hM.eigenvalues)
  refine ⟨hM.eigenvectorBasis i₀, hM.eigenvectorBasis.orthonormal.1 i₀, ?_⟩
  rw [mvec_eigenvectorBasis hM, real_inner_smul_right, real_inner_self_eq_norm_sq,
    hM.eigenvectorBasis.orthonormal.1 i₀, hi₀]
  ring

end StatFormal.BandSupport
