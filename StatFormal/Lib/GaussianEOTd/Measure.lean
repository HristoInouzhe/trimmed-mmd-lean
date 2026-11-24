import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Measure-theoretic helpers for Gaussian entropic plans in `ℝᵈ`

Library component (GAUSS-EOT-d, part 1). Untrusted library code.

* `map_withDensity_equiv`: `(ρ.withDensity f).map e = (ρ.map e).withDensity (f ∘ e.symm)` for a measurable equivalence.
* `pi_withDensity`: a finite product of probability measures with densities is the product measure with the product
  density.
* `stdGaussian_map_affine`: `(stdGaussian ℝⁿ).map (x ↦ m + Mx) = N(m, M Mᵀ)` (`multivariateGaussian`).
* integrability of quadratic and linear functionals under Gaussian measures.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal NNReal RealInnerProductSpace

set_option linter.style.longLine false

namespace StatFormal.Foundations.GaussianEOTd

/-! ### Densities under measurable equivalences and finite products -/

theorem map_withDensity_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (ρ : Measure α)
    (e : α ≃ᵐ β) (f : α → ℝ≥0∞) :
    (ρ.withDensity f).map e = (ρ.map e).withDensity (f ∘ e.symm) := by
  ext s hs
  rw [e.map_apply, withDensity_apply _ (e.measurable hs), withDensity_apply _ hs,
    e.restrict_map, lintegral_map_equiv]
  refine lintegral_congr fun x => ?_
  simp

theorem pi_withDensity {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (ν : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (ν i)] (f : ∀ i, α i → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((ν i).withDensity (f i))] :
    Measure.pi (fun i => (ν i).withDensity (f i)) =
      (Measure.pi ν).withDensity (fun x => ∏ i, f i (x i)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have hind : (Set.univ.pi s).indicator (fun x : ∀ i, α i => ∏ i, f i (x i)) =
      fun x => ∏ i, (s i).indicator (f i) (x i) := by
    funext x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [hind]
  have hX := iIndepFun_pi (μ := ν) (X := fun i => (s i).indicator (f i))
    (fun i => ((hf i).indicator (hs i)).aemeasurable)
  have h := lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
    (fun i (x : ∀ i, α i) => (s i).indicator (f i) (x i)) hX
    (fun i => ((hf i).indicator (hs i)).comp (measurable_pi_apply i))
  rw [h]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), ← lintegral_indicator (hs i)]
  exact (measurePreserving_eval ν i).lintegral_comp ((hf i).indicator (hs i))

/-! ### Affine images of the standard Gaussian -/

variable {ι : Type*} [Fintype ι]

lemma posSemidef_mul_transpose (M : Matrix ι ι ℝ) : (M * Mᵀ).PosSemidef := by
  have := Matrix.posSemidef_self_mul_conjTranspose M
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this

variable [DecidableEq ι]

/-- `(stdGaussian ℝⁿ).map (x ↦ m + Mx) = N(m, M Mᵀ)`. -/
theorem stdGaussian_map_affine (m : EuclideanSpace ℝ ι) (M : Matrix ι ι ℝ) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (fun x => m + toEuclideanCLM (𝕜 := ℝ) M x) =
      multivariateGaussian m (M * Mᵀ) := by
  have hmap : (fun x => m + toEuclideanCLM (𝕜 := ℝ) M x) =
      (fun x => m + x) ∘ (toEuclideanCLM (𝕜 := ℝ) M) := rfl
  have hG : IsGaussian ((stdGaussian (EuclideanSpace ℝ ι)).map (fun x => m + toEuclideanCLM (𝕜 := ℝ) M x)) := by
    rw [hmap, ← Measure.map_map (measurable_const_add m) (by fun_prop)]
    infer_instance
  apply IsGaussian.ext
  · simp only [id]
    rw [integral_id_multivariateGaussian, integral_map (by fun_prop) (by fun_prop),
      integral_add (integrable_const _), integral_const]
    · simp [ContinuousLinearMap.integral_comp_comm _ IsGaussian.integrable_fun_id]
    · exact IsGaussian.integrable_id.comp_measurable (by fun_prop)
  · rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun ι ℝ).toBasis fun i j => ?_
    rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
      covarianceBilin_multivariateGaussian (posSemidef_mul_transpose M)]
    rw [hmap, ← Measure.map_map (measurable_const_add m) (by fun_prop), covarianceBilin_map_const_add,
      covarianceBilin_map IsGaussian.memLp_two_id, covarianceBilin_stdGaussian, innerSL_apply_apply,
      ContinuousLinearMap.adjoint_inner_left, inner_toEuclideanCLM]
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, ofLp_toEuclideanCLM, mulVec_mulVec]
    congr 3

lemma spectral_real {d : ℕ} {N : Matrix (Fin d) (Fin d) ℝ} (hH : N.IsHermitian) :
    N = (hH.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) * diagonal hH.eigenvalues *
      (hH.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)ᵀ := by
  conv_lhs => rw [hH.spectral_theorem]
  simp [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]

lemma eigU_transpose_mul {d : ℕ} {N : Matrix (Fin d) (Fin d) ℝ} (hH : N.IsHermitian) :
    (hH.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)ᵀ * (hH.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) = 1 := by
  have := Unitary.coe_star_mul_self hH.eigenvectorUnitary
  simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using this

lemma eigU_mul_transpose {d : ℕ} {N : Matrix (Fin d) (Fin d) ℝ} (hH : N.IsHermitian) :
    (hH.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) * (hH.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)ᵀ = 1 := by
  have := Unitary.coe_mul_star_self hH.eigenvectorUnitary
  simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using this

end StatFormal.Foundations.GaussianEOTd
