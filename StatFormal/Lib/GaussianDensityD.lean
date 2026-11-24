import StatFormal.Lib.SchrodingerPathD.Static
import StatFormal.Lib.GaussianEOTd.Measure
import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The Lebesgue density of `N(m, B)` on `ℝᵈ` for a general covariance `B ≻ 0`

Library component (untrusted). Mathlib defines `multivariateGaussian m B` as the image of `stdGaussian` under
`x ↦ m + B^{1/2} x` (`CFC.sqrt`) and proves no density. Here:

* `mvGaussPDF m B y = ((2π)ᵈ det B)^{−1/2} exp(−½ (y − m)ᵀ B⁻¹ (y − m))`;
* `multivariateGaussian_eq_withDensity` (`B ≻ 0`): `N(m, B) = Leb.withDensity mvGaussPDF`;
* `log_mvGaussPDF`, `integrable_log_mvGaussPDF`: `log` of the density is a quadratic, integrable under `N(m, B)`;
* `integrable_normSq_mvG`: `‖y‖² ∈ L¹(N(m, B))`.

Route: `N(0, I) = Leb.withDensity p₁` (`SchrodingerPathD.isoG_eq_withDensity`), the affine equivalence
`e(x) = m + Sx`, `S = B^{1/2}`, pushes Lebesgue measure to `|det S|⁻¹ Leb` (`map_linearMap_addHaar_eq_smul_addHaar`,
translation invariance), and `|det S| = √det B` (`Matrix.det_sqrt`), `‖S⁻¹v‖² = vᵀB⁻¹v`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal NNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator

set_option linter.style.longLine false

namespace StatFormal.Foundations.GaussianDensityD

open StatFormal.SchrodingerPathD (isoG gdens gdens_pos measurable_gdens log_gdens isoG_eq_withDensity)

local notation "E" d => EuclideanSpace ℝ (Fin d)

variable {d : ℕ}

/-- The Lebesgue density of `N(m, B)`: `((2π)ᵈ det B)^{−1/2} exp(−½ (y − m)ᵀ B⁻¹ (y − m))`. -/
def mvGaussPDF (m : E d) (B : Matrix (Fin d) (Fin d) ℝ) (y : E d) : ℝ :=
  (√((2 * Real.pi) ^ d * B.det))⁻¹ * Real.exp (-(ofLp (y - m) ⬝ᵥ B⁻¹ *ᵥ ofLp (y - m)) / 2)

lemma mvGaussPDF_nonneg (m : E d) (B : Matrix (Fin d) (Fin d) ℝ) (y : E d) : 0 ≤ mvGaussPDF m B y := by
  unfold mvGaussPDF; positivity

lemma continuous_mvGaussPDF (m : E d) (B : Matrix (Fin d) (Fin d) ℝ) : Continuous (mvGaussPDF m B) := by
  unfold mvGaussPDF
  refine continuous_const.mul (Real.continuous_exp.comp ?_)
  refine (Continuous.neg ?_).div_const _
  have h1 : Continuous fun y : E d => ofLp (y - m) := (PiLp.continuous_ofLp 2 _).comp (by fun_prop)
  exact h1.dotProduct (continuous_const.matrix_mulVec h1)

lemma measurable_mvGaussPDF (m : E d) (B : Matrix (Fin d) (Fin d) ℝ) : Measurable (mvGaussPDF m B) :=
  (continuous_mvGaussPDF m B).measurable

/-! ### The square root `S = B^{1/2}` -/

section Sqrt

variable {B : Matrix (Fin d) (Fin d) ℝ}

lemma sqrt_posSemidef (B : Matrix (Fin d) (Fin d) ℝ) : (CFC.sqrt B).PosSemidef :=
  (CFC.sqrt_nonneg B).posSemidef

lemma sqrt_mul_self (hB : B.PosDef) : CFC.sqrt B * CFC.sqrt B = B :=
  CFC.sqrt_mul_sqrt_self B hB.posSemidef.nonneg

lemma sqrt_transpose (B : Matrix (Fin d) (Fin d) ℝ) : (CFC.sqrt B)ᵀ = CFC.sqrt B := by
  have h := (sqrt_posSemidef B).1
  rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h

lemma det_sqrt_eq (hB : B.PosDef) : (CFC.sqrt B).det = √B.det := by
  rw [Matrix.PosSemidef.det_sqrt hB.posSemidef, RCLike.sqrt_real]

lemma det_sqrt_pos (hB : B.PosDef) : 0 < (CFC.sqrt B).det := by
  rw [det_sqrt_eq hB]; exact Real.sqrt_pos.2 hB.det_pos

lemma sqrt_inv_mul (hB : B.PosDef) : (CFC.sqrt B)⁻¹ * CFC.sqrt B = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (det_sqrt_pos hB).ne')

lemma sqrt_mul_inv (hB : B.PosDef) : CFC.sqrt B * (CFC.sqrt B)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (det_sqrt_pos hB).ne')

lemma sqrt_inv_transpose (B : Matrix (Fin d) (Fin d) ℝ) : ((CFC.sqrt B)⁻¹)ᵀ = (CFC.sqrt B)⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, sqrt_transpose]

lemma sqrt_inv_mul_sqrt_inv (hB : B.PosDef) : (CFC.sqrt B)⁻¹ * (CFC.sqrt B)⁻¹ = B⁻¹ := by
  rw [← Matrix.mul_inv_rev, sqrt_mul_self hB]

end Sqrt

/-! ### The affine equivalence `x ↦ m + Sx` -/

/-- `x ↦ m + Sx` as a measurable equivalence, `S` invertible with inverse `Si`. -/
def affEquiv (m : E d) (S Si : Matrix (Fin d) (Fin d) ℝ) (h1 : Si * S = 1) (h2 : S * Si = 1) : (E d) ≃ᵐ (E d) where
  toFun x := m + toEuclideanCLM (𝕜 := ℝ) S x
  invFun y := toEuclideanCLM (𝕜 := ℝ) Si (y - m)
  left_inv x := by
    simp only [add_sub_cancel_left]
    rw [show toEuclideanCLM (𝕜 := ℝ) Si (toEuclideanCLM (𝕜 := ℝ) S x) = toEuclideanCLM (𝕜 := ℝ) (Si * S) x by
      simp only [map_mul]; rfl, h1, map_one]; rfl
  right_inv y := by
    simp only
    rw [show toEuclideanCLM (𝕜 := ℝ) S (toEuclideanCLM (𝕜 := ℝ) Si (y - m)) =
      toEuclideanCLM (𝕜 := ℝ) (S * Si) (y - m) by simp only [map_mul]; rfl, h2, map_one]
    simp
  measurable_toFun := by
    have : Continuous fun x : E d => m + toEuclideanCLM (𝕜 := ℝ) S x := by fun_prop
    exact this.measurable
  measurable_invFun := by
    have : Continuous fun y : E d => toEuclideanCLM (𝕜 := ℝ) Si (y - m) := by fun_prop
    exact this.measurable

lemma linearMap_det_toEuclideanCLM (S : Matrix (Fin d) (Fin d) ℝ) :
    LinearMap.det ((toEuclideanCLM (𝕜 := ℝ) S : (E d) →L[ℝ] (E d)) : (E d) →ₗ[ℝ] (E d)) = S.det := by
  rw [coe_toEuclideanCLM_eq_toEuclideanLin, toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]

/-- `Leb ∘ (x ↦ m + Sx)⁻¹ = |det S|⁻¹ Leb`. -/
theorem volume_map_aff (m : E d) {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.det ≠ 0) :
    (volume : Measure (E d)).map (fun x => m + toEuclideanCLM (𝕜 := ℝ) S x) =
      ENNReal.ofReal |S.det⁻¹| • volume := by
  have hcomp : (fun x : E d => m + toEuclideanCLM (𝕜 := ℝ) S x) =
      (fun y => m + y) ∘ ((toEuclideanCLM (𝕜 := ℝ) S : (E d) →L[ℝ] (E d)) : (E d) →ₗ[ℝ] (E d)) := rfl
  rw [hcomp, ← Measure.map_map (measurable_const_add m)
    (LinearMap.continuous_of_finiteDimensional _).measurable]
  have hL := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (E d)))
    (f := ((toEuclideanCLM (𝕜 := ℝ) S : (E d) →L[ℝ] (E d)) : (E d) →ₗ[ℝ] (E d)))
    (by rwa [linearMap_det_toEuclideanCLM])
  rw [hL, linearMap_det_toEuclideanCLM, Measure.map_smul, map_add_left_eq_self]
  exact (measurable_const_add m).aemeasurable

/-! ### The density -/

/-- The intermediate form `|det S|⁻¹ p₁(S⁻¹(y − m))`, `S = B^{1/2}`. -/
def qAux (m : E d) (B : Matrix (Fin d) (Fin d) ℝ) (y : E d) : ℝ :=
  ((CFC.sqrt B).det)⁻¹ * gdens d 1 (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt B)⁻¹ (y - m))

lemma stdGaussian_eq_isoG : stdGaussian (E d) = isoG d 1 := by
  simp [isoG]

theorem mvG_eq_withDensity_qAux {m : E d} {B : Matrix (Fin d) (Fin d) ℝ} (hB : B.PosDef) :
    multivariateGaussian m B = volume.withDensity (fun y => ENNReal.ofReal (qAux m B y)) := by
  set S := CFC.sqrt B with hSdef
  have hdet := det_sqrt_pos hB
  set e := affEquiv m S S⁻¹ (sqrt_inv_mul hB) (sqrt_mul_inv hB) with he
  have hmap : multivariateGaussian m B = (stdGaussian (E d)).map e := rfl
  rw [hmap, stdGaussian_eq_isoG, isoG_eq_withDensity one_pos,
    StatFormal.Foundations.GaussianEOTd.map_withDensity_equiv]
  have hv : (volume : Measure (E d)).map e = ENNReal.ofReal |S.det⁻¹| • volume :=
    volume_map_aff m hdet.ne'
  have hmeas : Measurable ((fun u => ENNReal.ofReal (gdens d 1 u)) ∘ e.symm) :=
    (ENNReal.measurable_ofReal.comp (measurable_gdens 1)).comp e.symm.measurable
  rw [hv, withDensity_smul_measure, ← withDensity_smul _ hmeas]
  congr 1
  funext y
  simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul, qAux]
  rw [abs_of_pos (inv_pos.2 hdet), ← ENNReal.ofReal_mul (inv_pos.2 hdet).le]
  rfl

lemma normSq_sqrtInv {B : Matrix (Fin d) (Fin d) ℝ} (hB : B.PosDef) (v : E d) :
    ‖toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt B)⁻¹ v‖ ^ 2 = ofLp v ⬝ᵥ B⁻¹ *ᵥ ofLp v := by
  set Si := (CFC.sqrt B)⁻¹ with hSi
  have hx : ∀ x : E d, ‖x‖ ^ 2 = x.ofLp ⬝ᵥ x.ofLp := fun x => by
    rw [EuclideanSpace.real_norm_sq_eq]; simp [dotProduct, sq]
  rw [hx, ofLp_toEuclideanCLM, dotProduct_mulVec, ← mulVec_transpose, hSi, sqrt_inv_transpose, mulVec_mulVec,
    sqrt_inv_mul_sqrt_inv hB, dotProduct_comm]

lemma log_qAux {m : E d} {B : Matrix (Fin d) (Fin d) ℝ} (hB : B.PosDef) (y : E d) :
    Real.log (qAux m B y) = -Real.log (CFC.sqrt B).det - (d * Real.log (2 * Real.pi * 1) / 2) -
      ‖toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt B)⁻¹ (y - m)‖ ^ 2 / (2 * 1) := by
  have hdet := det_sqrt_pos hB
  rw [qAux, Real.log_mul (inv_pos.2 hdet).ne' (gdens_pos one_pos _).ne', Real.log_inv, log_gdens one_pos]
  ring

theorem qAux_eq {m : E d} {B : Matrix (Fin d) (Fin d) ℝ} (hB : B.PosDef) (y : E d) :
    qAux m B y = mvGaussPDF m B y := by
  have hdet := det_sqrt_pos hB
  have hq : 0 < qAux m B y := mul_pos (inv_pos.2 hdet) (gdens_pos one_pos _)
  have h2π : 0 < (2 * Real.pi) ^ d := pow_pos (by positivity) d
  have hp : 0 < mvGaussPDF m B y := by
    unfold mvGaussPDF
    exact mul_pos (inv_pos.2 (Real.sqrt_pos.2 (mul_pos h2π hB.det_pos))) (Real.exp_pos _)
  refine Real.log_injOn_pos hq hp ?_
  rw [log_qAux hB, normSq_sqrtInv hB, mvGaussPDF, Real.log_mul (inv_pos.2 (Real.sqrt_pos.2 (mul_pos h2π
    hB.det_pos))).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_inv, Real.log_sqrt (mul_pos h2π hB.det_pos).le,
    Real.log_mul h2π.ne' hB.det_pos.ne', Real.log_pow, det_sqrt_eq hB, Real.log_sqrt hB.det_pos.le]
  ring_nf

/-- **The Lebesgue density of `N(m, B)`**, `B ≻ 0`. -/
theorem multivariateGaussian_eq_withDensity {m : E d} {B : Matrix (Fin d) (Fin d) ℝ} (hB : B.PosDef) :
    multivariateGaussian m B = volume.withDensity (fun y => ENNReal.ofReal (mvGaussPDF m B y)) := by
  rw [mvG_eq_withDensity_qAux hB]
  congr 1
  funext y
  rw [qAux_eq hB]

theorem log_mvGaussPDF {m : E d} {B : Matrix (Fin d) (Fin d) ℝ} (hB : B.PosDef) (y : E d) :
    Real.log (mvGaussPDF m B y) = -Real.log √((2 * Real.pi) ^ d * B.det) -
      (ofLp (y - m) ⬝ᵥ B⁻¹ *ᵥ ofLp (y - m)) / 2 := by
  have h2π : 0 < (2 * Real.pi) ^ d := pow_pos (by positivity) d
  rw [mvGaussPDF, Real.log_mul (inv_pos.2 (Real.sqrt_pos.2 (mul_pos h2π hB.det_pos))).ne' (Real.exp_pos _).ne',
    Real.log_exp, Real.log_inv]
  ring

/-- `log` of the density is integrable under `N(m, B)` (finite differential entropy). -/
theorem integrable_log_mvGaussPDF {m : E d} {B : Matrix (Fin d) (Fin d) ℝ} (hB : B.PosDef) :
    Integrable (fun y => Real.log (mvGaussPDF m B y)) (multivariateGaussian m B) := by
  set S := CFC.sqrt B with hSdef
  set e := affEquiv m S S⁻¹ (sqrt_inv_mul hB) (sqrt_mul_inv hB) with he
  have hmap : multivariateGaussian m B = (stdGaussian (E d)).map e := rfl
  have hfun : (fun y => Real.log (mvGaussPDF m B y)) = fun y => Real.log (qAux m B y) := by
    funext y; rw [qAux_eq hB]
  rw [hfun, hmap, integrable_map_equiv]
  have hcomp : ((fun y => Real.log (qAux m B y)) ∘ e) = fun x : E d =>
      -Real.log S.det - (d * Real.log (2 * Real.pi * 1) / 2) - ‖x‖ ^ 2 / (2 * 1) := by
    funext x
    simp only [Function.comp_apply]
    rw [log_qAux hB]
    congr 3
    exact congrArg norm (e.symm_apply_apply x)
  rw [hcomp]
  have h2 : Integrable (fun x : E d => ‖x‖ ^ 2) (stdGaussian (E d)) :=
    (memLp_two_iff_integrable_sq_norm (f := id) aestronglyMeasurable_id).1 IsGaussian.memLp_two_id
  exact (integrable_const _).sub (h2.div_const _)

/-- `‖y‖² ∈ L¹(N(m, B))`. -/
theorem integrable_normSq_mvG (m : E d) (B : Matrix (Fin d) (Fin d) ℝ) :
    Integrable (fun y : E d => ‖y‖ ^ 2) (multivariateGaussian m B) :=
  (memLp_two_iff_integrable_sq_norm (f := id) aestronglyMeasurable_id).1 IsGaussian.memLp_two_id

end StatFormal.Foundations.GaussianDensityD
