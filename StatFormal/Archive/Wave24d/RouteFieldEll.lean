import StatFormal.Archive.Wave24d.Statements
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Route — SB `cor:field-ell` (untrusted)

`E μ = AEγ + b = b` and `Cov(μ) = A Cov(γ) Aᵀ = AAᵀ` coordinatewise (linearity of the integral). With `W` symmetric and
`W W AAᵀ = I`, `(WA)ᵀ(WA) = Aᵀ W W A = I`, so `WA` is orthogonal and `S_μ ∘ (A· + b) = WA` pushes the spherical `γ` to
itself; `W` is invertible, so `S_μ` has the global inverse `z ↦ W⁻¹z + Eμ`. The root: spectral theorem.
-/

noncomputable section
open MeasureTheory Set Matrix
open scoped ENNReal

namespace StatFormal.Wave24d

open StatFormal.OTFD.WaveL1 (Euc)
open StatFormal.OTFD.Wave8c (mvec)

variable {d : ℕ}

lemma mvec_apply' (A : Matrix (Fin d) (Fin d) ℝ) (z : Euc d) (i : Fin d) : mvec A z i = ∑ j, A i j * z j := by
  simp [mvec, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

lemma mvec_mul (A B : Matrix (Fin d) (Fin d) ℝ) (z : Euc d) : mvec A (mvec B z) = mvec (A * B) z := by
  simp [mvec, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

lemma mvec_one (z : Euc d) : mvec (1 : Matrix (Fin d) (Fin d) ℝ) z = z := by simp [mvec]

lemma continuous_mvec' (A : Matrix (Fin d) (Fin d) ℝ) : Continuous (mvec A) :=
  LinearMap.continuous_of_finiteDimensional _

section Moments
variable {γ : Measure (Euc d)} [IsProbabilityMeasure γ]

lemma abs_coord_le (x : Euc d) (i : Fin d) : |x i| ≤ ‖x‖ := by
  have := PiLp.norm_apply_le (p := 2) x i
  simpa [Real.norm_eq_abs] using this

lemma integrable_norm_sq (h2 : ∫⁻ x, ‖x‖ₑ ^ 2 ∂γ < ⊤) : Integrable (fun x : Euc d => ‖x‖ ^ 2) γ := by
  refine ⟨(continuous_norm.pow 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => sq_nonneg _)]
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun x => ?_)) h2
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

lemma integrable_coord (h2 : ∫⁻ x, ‖x‖ₑ ^ 2 ∂γ < ⊤) (i : Fin d) : Integrable (fun x : Euc d => x i) γ := by
  refine Integrable.mono' ((integrable_norm_sq h2).add (integrable_const 1))
    ((PiLp.continuous_apply 2 _ i).aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  have := abs_coord_le x i
  show |x i| ≤ ‖x‖ ^ 2 + 1
  nlinarith [norm_nonneg x, sq_nonneg (‖x‖ - 1)]

lemma integrable_coord_mul (h2 : ∫⁻ x, ‖x‖ₑ ^ 2 ∂γ < ⊤) (i j : Fin d) :
    Integrable (fun x : Euc d => x i * x j) γ := by
  refine Integrable.mono' (integrable_norm_sq h2)
    (((PiLp.continuous_apply 2 _ i).mul (PiLp.continuous_apply 2 _ j)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have h1 := abs_coord_le x i
  have h2 := abs_coord_le x j
  nlinarith [abs_nonneg (x i), abs_nonneg (x j)]

end Moments

theorem field_ell_root : Claims.field_ell_root := by
  intro d C hC
  set U := hC.1.eigenvectorUnitary
  set ev := hC.1.eigenvalues
  have hpos : ∀ i, 0 < ev i := hC.eigenvalues_pos
  set D : Matrix (Fin d) (Fin d) ℝ := diagonal fun i => (Real.sqrt (ev i))⁻¹ with hD
  set W : Matrix (Fin d) (Fin d) ℝ := (U : Matrix (Fin d) (Fin d) ℝ) * D * star (U : Matrix (Fin d) (Fin d) ℝ)
    with hW
  have hspec : C = (U : Matrix (Fin d) (Fin d) ℝ) * diagonal ev * star (U : Matrix (Fin d) (Fin d) ℝ) := by
    have := hC.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa using this
  have hUU : star (U : Matrix (Fin d) (Fin d) ℝ) * U = 1 := Unitary.coe_star_mul_self U
  have hUU' : (U : Matrix (Fin d) (Fin d) ℝ) * star (U : Matrix (Fin d) (Fin d) ℝ) = 1 := Unitary.coe_mul_star_self U
  have hstarT : star (U : Matrix (Fin d) (Fin d) ℝ) = (U : Matrix (Fin d) (Fin d) ℝ)ᵀ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  refine ⟨W, ?_, ?_, ?_⟩
  · rw [hW, transpose_mul, transpose_mul, hstarT, transpose_transpose, hD, diagonal_transpose, ← hstarT,
      Matrix.mul_assoc]
  · have hU1 : IsUnit (star (U : Matrix (Fin d) (Fin d) ℝ)) := (Unitary.isUnit_coe (U := star U))
    have hDpos : D.PosDef := by
      rw [hD, Matrix.posDef_diagonal_iff]
      intro i; exact inv_pos.mpr (Real.sqrt_pos.mpr (hpos i))
    have := (Matrix.IsUnit.posDef_star_left_conjugate_iff hU1 (x := D)).2 hDpos
    rwa [star_star] at this
  · rw [hspec, hW]
    have hDD : D * D * diagonal ev = 1 := by
      rw [hD, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
      congr 1; funext i
      have h := hpos i
      rw [← mul_inv, ← sq, Real.sq_sqrt h.le, inv_mul_cancel₀ h.ne']
    calc (U : Matrix (Fin d) (Fin d) ℝ) * D * star (U : Matrix (Fin d) (Fin d) ℝ) *
          ((U : Matrix (Fin d) (Fin d) ℝ) * D * star (U : Matrix (Fin d) (Fin d) ℝ)) *
          ((U : Matrix (Fin d) (Fin d) ℝ) * diagonal ev * star (U : Matrix (Fin d) (Fin d) ℝ))
        = (U : Matrix (Fin d) (Fin d) ℝ) * D * (star (U : Matrix (Fin d) (Fin d) ℝ) * U) * D *
            (star (U : Matrix (Fin d) (Fin d) ℝ) * U) * diagonal ev * star (U : Matrix (Fin d) (Fin d) ℝ) := by
          simp only [Matrix.mul_assoc]
      _ = (U : Matrix (Fin d) (Fin d) ℝ) * (D * D * diagonal ev) * star (U : Matrix (Fin d) (Fin d) ℝ) := by
          rw [hUU]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [hDD, Matrix.mul_one, hUU']

theorem field_ell : Claims.field_ell := by
  intro d γ _ hsph h2 hmean hcov A b hA
  set f : Euc d → Euc d := fun z => mvec A z + b with hfdef
  have hf : Measurable f := ((continuous_mvec' A).add continuous_const).measurable
  set μ := γ.map f with hμdef
  have hm0 : ∀ j, ∫ z, z j ∂γ = 0 := by
    intro j
    have := congrArg (fun v : Euc d => v j) hmean
    simpa [meanVec] using this
  have hfi : ∀ z i, f z i = ∑ j, A i j * z j + b i := by
    intro z i; simp only [hfdef, PiLp.add_apply, mvec_apply']
  -- the mean
  have hmeanμ : meanVec μ = b := by
    ext i
    simp only [meanVec, hμdef]
    rw [integral_map hf.aemeasurable (PiLp.continuous_apply 2 _ i).aestronglyMeasurable]
    simp only [hfi]
    rw [integral_add (integrable_finsetSum _ fun j _ => (integrable_coord h2 j).const_mul _) (integrable_const _),
      integral_finsetSum _ fun j _ => (integrable_coord h2 j).const_mul _]
    simp [integral_const_mul, hm0]
  -- the covariance
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
    rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => (integrable_coord_mul h2 k l).const_mul _,
      Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ fun l _ => (integrable_coord_mul h2 k l).const_mul _]
    simp only [integral_const_mul, hcovγ, mul_ite, mul_one, mul_zero, Matrix.transpose_apply]
    simp [Finset.sum_ite_eq]
  refine ⟨hmeanμ, hcovμ, fun W hWs hWW => ?_⟩
  rw [hcovμ] at hWW
  -- `WA` is orthogonal
  have hdetW : W.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det hWW
    rw [det_mul, det_mul, h, zero_mul, zero_mul, det_one] at this
    exact zero_ne_one this
  have hWA : (W * A)ᵀ * (W * A) = 1 := by
    have hAinv : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hA)
    rw [transpose_mul, hWs]
    have h1 : A * Aᵀ * (W * W) = 1 := mul_eq_one_comm.mp (by simpa [Matrix.mul_assoc] using hWW)
    have hAA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hAinv)
    calc Aᵀ * W * (W * A) = A⁻¹ * (A * Aᵀ * (W * W)) * A := by
          simp only [← Matrix.mul_assoc, hAA, Matrix.one_mul]
      _ = 1 := by rw [h1, Matrix.mul_one, hAA]
  have hO : W * A ∈ Matrix.orthogonalGroup (Fin d) ℝ := by
    rw [Matrix.mem_orthogonalGroup_iff']
    exact hWA
  have hWu : W⁻¹ * W = 1 := Matrix.nonsing_inv_mul W (isUnit_iff_ne_zero.mpr hdetW)
  have hWu' : W * W⁻¹ = 1 := Matrix.mul_nonsing_inv W (isUnit_iff_ne_zero.mpr hdetW)
  rw [hmeanμ]
  refine ⟨((continuous_mvec' W).comp (continuous_id.sub continuous_const)).measurable,
    ((continuous_mvec' W⁻¹).add continuous_const).measurable, ?_, ?_, ?_⟩
  · have hSm : Measurable fun x : Euc d => mvec W (x - b) :=
      ((continuous_mvec' W).comp (continuous_id.sub continuous_const)).measurable
    rw [hμdef, Measure.map_map hSm hf]
    have : ((fun x => mvec W (x - b)) ∘ f) = mvec (W * A) := by
      funext z; simp only [Function.comp_apply, hfdef, add_sub_cancel_right, mvec_mul]
    rw [this]; exact hsph _ hO
  · exact Filter.Eventually.of_forall fun x => by
      simp only [mvec_mul, hWu, mvec_one, sub_add_cancel]
  · exact Filter.Eventually.of_forall fun z => by
      simp only [add_sub_cancel_right, mvec_mul, hWu', mvec_one]

end StatFormal.Wave24d
