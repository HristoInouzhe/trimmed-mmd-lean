import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

/-!
# Perturbation of matrix square roots in the operator norm (untrusted library)

Real square matrices with the `L²` operator norm (`Matrix.Norms.L2Operator`) and the Loewner order (`MatrixOrder`);
`toEuclideanLin M` is `M` acting on `EuclideanSpace ℝ n`.

* `norm_le_of_eigen`: a Hermitian `X` has `‖X‖ ≤ c` as soon as every eigenvalue (of a unit eigenvector) is `≤ c` in
  absolute value (isometric continuous functional calculus).
* `smul_one_le_sqrt`: `λ • 1 ≤ A` gives `√λ • 1 ≤ CFC.sqrt A`.
* `norm_sqrt_sub_le`: for `λ • 1 ≤ A` (`λ > 0`) and `0 ≤ B`, `‖√A − √B‖ ≤ ‖A − B‖ / √λ`
  (`√A X + X √B = A − B` for `X = √A − √B`, tested at a unit eigenvector of `X`).
* `norm_inv_le_of_le`: `c • 1 ≤ S` (`c > 0`, `S` Hermitian) gives `‖S⁻¹‖ ≤ c⁻¹`.
* `norm_inv_sub_inv_le`: `‖S⁻¹ − T⁻¹‖ ≤ ‖S⁻¹‖ ‖T⁻¹‖ ‖S − T‖` for invertible `S`, `T`.
* `norm_invSqrt_le`, `norm_invSqrt_sub_le`: for `λ • 1 ≤ A` and Hermitian `B` with `‖B − A‖ ≤ λ/2`,
  `‖(√B)⁻¹‖ ≤ (λ/2)^{-1/2}` and `‖(√B)⁻¹ − (√A)⁻¹‖ ≤ λ^{-1/2} (λ/2)^{-1/2} ‖B − A‖ / √λ`.
-/

set_option linter.style.longLine false

noncomputable section
open Matrix WithLp
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace

namespace StatFormal.MatrixSqrtPerturb

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Quadratic forms and the operator norm -/

lemma toEuclideanLin_eq_clm (M : Matrix n n ℝ) (v : EuclideanSpace ℝ n) :
    toEuclideanLin M v = toEuclideanCLM (𝕜 := ℝ) M v := rfl

lemma lin_mul (A B : Matrix n n ℝ) (v : EuclideanSpace ℝ n) :
    toEuclideanLin (A * B) v = toEuclideanLin A (toEuclideanLin B v) := by
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

lemma lin_one (v : EuclideanSpace ℝ n) : toEuclideanLin (1 : Matrix n n ℝ) v = v := by
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply]

lemma smul_one_isHermitian (c : ℝ) : (c • (1 : Matrix n n ℝ)).IsHermitian := by
  unfold Matrix.IsHermitian; simp

lemma norm_toEuclideanLin_le (M : Matrix n n ℝ) (v : EuclideanSpace ℝ n) :
    ‖toEuclideanLin M v‖ ≤ ‖M‖ * ‖v‖ := by
  rw [toEuclideanLin_eq_clm, ← l2_opNorm_toEuclideanCLM]
  exact (toEuclideanCLM (𝕜 := ℝ) M).le_opNorm v

lemma abs_inner_le (M : Matrix n n ℝ) (v : EuclideanSpace ℝ n) :
    |⟪v, toEuclideanLin M v⟫| ≤ ‖M‖ * ‖v‖ ^ 2 := by
  refine (abs_real_inner_le_norm _ _).trans ?_
  calc ‖v‖ * ‖toEuclideanLin M v‖ ≤ ‖v‖ * (‖M‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left (norm_toEuclideanLin_le M v) (norm_nonneg _)
    _ = ‖M‖ * ‖v‖ ^ 2 := by ring

lemma inner_eq_dotProduct (M : Matrix n n ℝ) (v : EuclideanSpace ℝ n) :
    ⟪v, toEuclideanLin M v⟫ = star (ofLp v) ⬝ᵥ (M *ᵥ ofLp v) := by
  rw [toEuclideanLin_eq_clm, inner_toEuclideanCLM, star_trivial]

lemma inner_sub_smul_one (M : Matrix n n ℝ) (c : ℝ) (v : EuclideanSpace ℝ n) :
    ⟪v, toEuclideanLin (M - c • 1) v⟫ = ⟪v, toEuclideanLin M v⟫ - c * ‖v‖ ^ 2 := by
  rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, inner_sub_right, inner_smul_right,
    lin_one, real_inner_self_eq_norm_sq]

/-- The Loewner bound `c • 1 ≤ M` as a bound on the quadratic form. -/
lemma le_inner_of_le {M : Matrix n n ℝ} {c : ℝ} (h : c • (1 : Matrix n n ℝ) ≤ M) (v : EuclideanSpace ℝ n) :
    c * ‖v‖ ^ 2 ≤ ⟪v, toEuclideanLin M v⟫ := by
  have h1 := (Matrix.le_iff.mp h).dotProduct_mulVec_nonneg (ofLp v)
  rw [← inner_eq_dotProduct, inner_sub_smul_one] at h1
  linarith

lemma inner_nonneg_of_nonneg {M : Matrix n n ℝ} (h : 0 ≤ M) (v : EuclideanSpace ℝ n) :
    0 ≤ ⟪v, toEuclideanLin M v⟫ := by
  have h1 := (Matrix.nonneg_iff_posSemidef.mp h).dotProduct_mulVec_nonneg (ofLp v)
  rwa [← inner_eq_dotProduct] at h1

/-- Conversely, a Hermitian matrix whose quadratic form dominates `c‖v‖²` satisfies `c • 1 ≤ M`. -/
lemma le_of_inner {M : Matrix n n ℝ} (hM : M.IsHermitian) {c : ℝ}
    (h : ∀ v : EuclideanSpace ℝ n, c * ‖v‖ ^ 2 ≤ ⟪v, toEuclideanLin M v⟫) : c • (1 : Matrix n n ℝ) ≤ M := by
  rw [Matrix.le_iff]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · exact hM.sub (smul_one_isHermitian c)
  · have h1 := h (toLp 2 x)
    have h2 := inner_sub_smul_one M c (toLp 2 x)
    rw [inner_eq_dotProduct, ofLp_toLp] at h2
    linarith

lemma inner_symm {X : Matrix n n ℝ} (hX : X.IsHermitian) (v w : EuclideanSpace ℝ n) :
    ⟪v, toEuclideanLin X w⟫ = ⟪toEuclideanLin X v, w⟫ :=
  ((isSymmetric_toEuclideanLin_iff.mpr hX) v w).symm

/-! ### Eigenvectors and the norm of a Hermitian matrix -/

lemma exists_eigvec {X : Matrix n n ℝ} (hX : X.IsHermitian) {x : ℝ} (hx : x ∈ spectrum ℝ X) :
    ∃ v : EuclideanSpace ℝ n, ‖v‖ = 1 ∧ toEuclideanLin X v = x • v := by
  rw [hX.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  refine ⟨hX.eigenvectorBasis i, hX.eigenvectorBasis.orthonormal.1 i, ?_⟩
  apply WithLp.ofLp_injective
  rw [toEuclideanLin_eq_clm, ofLp_toEuclideanCLM, WithLp.ofLp_smul]
  exact hX.mulVec_eigenvectorBasis i

/-- The operator norm of a Hermitian matrix is bounded by any bound on its eigenvalues. -/
theorem norm_le_of_eigen {X : Matrix n n ℝ} (hX : X.IsHermitian) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ (t : ℝ) (v : EuclideanSpace ℝ n), ‖v‖ = 1 → toEuclideanLin X v = t • v → |t| ≤ c) : ‖X‖ ≤ c := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  have hid : cfc (fun x : ℝ => x) X = X := cfc_id' ℝ X
  rw [← hid]
  refine norm_cfc_le hc fun x hx => ?_
  obtain ⟨v, hv1, hv⟩ := exists_eigvec hX hx
  rw [Real.norm_eq_abs]
  exact h x v hv1 hv

/-- An eigenvalue of `X` at a unit eigenvector is its quadratic form there. -/
lemma eig_eq_inner {X : Matrix n n ℝ} {t : ℝ} {v : EuclideanSpace ℝ n} (hv1 : ‖v‖ = 1)
    (hv : toEuclideanLin X v = t • v) : ⟪v, toEuclideanLin X v⟫ = t := by
  rw [hv, inner_smul_right, real_inner_self_eq_norm_sq, hv1]; ring

/-! ### Square roots -/

lemma sqrt_isHermitian (A : Matrix n n ℝ) : (CFC.sqrt A).IsHermitian :=
  (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian

/-- `λ • 1 ≤ A` gives `√λ • 1 ≤ √A`. -/
theorem smul_one_le_sqrt {A : Matrix n n ℝ} {lam : ℝ} (hlam : 0 ≤ lam) (hA : lam • (1 : Matrix n n ℝ) ≤ A) :
    Real.sqrt lam • (1 : Matrix n n ℝ) ≤ CFC.sqrt A := by
  have hA0 : 0 ≤ A := le_trans (by
    rw [Matrix.nonneg_iff_posSemidef]; exact Matrix.PosSemidef.one.smul hlam) hA
  set S := CFC.sqrt A
  have hS : S.IsHermitian := sqrt_isHermitian A
  have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hA0
  refine le_of_inner hS fun w => ?_
  -- first on eigenvalues of `S`
  have heig : ∀ x ∈ spectrum ℝ S, Real.sqrt lam ≤ x := by
    intro x hx
    obtain ⟨v, hv1, hv⟩ := exists_eigvec hS hx
    have hx0 : 0 ≤ x := by
      rw [← eig_eq_inner hv1 hv]; exact inner_nonneg_of_nonneg (CFC.sqrt_nonneg A) v
    have hAv : toEuclideanLin A v = (x * x) • v := by
      rw [← hSS, lin_mul, hv, map_smul, hv, smul_smul]
    have h1 := le_inner_of_le hA v
    rw [eig_eq_inner hv1 hAv, hv1] at h1
    calc Real.sqrt lam ≤ Real.sqrt (x * x) := Real.sqrt_le_sqrt (by simpa using h1)
      _ = x := Real.sqrt_mul_self hx0
  have hle : algebraMap ℝ (Matrix n n ℝ) (Real.sqrt lam) ≤ S :=
    (algebraMap_le_iff_le_spectrum (ha := hS.isSelfAdjoint)).mpr heig
  rw [Algebra.algebraMap_eq_smul_one] at hle
  exact le_inner_of_le hle w

/-- **Square-root perturbation.** For `λ • 1 ≤ A` with `λ > 0` and `0 ≤ B`, `‖√A − √B‖ ≤ ‖A − B‖ / √λ`. -/
theorem norm_sqrt_sub_le {A B : Matrix n n ℝ} {lam : ℝ} (hlam : 0 < lam) (hA : lam • (1 : Matrix n n ℝ) ≤ A)
    (hB : 0 ≤ B) : ‖CFC.sqrt A - CFC.sqrt B‖ ≤ ‖A - B‖ / Real.sqrt lam := by
  have hA0 : 0 ≤ A := le_trans (by
    rw [Matrix.nonneg_iff_posSemidef]; exact Matrix.PosSemidef.one.smul hlam.le) hA
  set SA := CFC.sqrt A
  set SB := CFC.sqrt B
  set X := SA - SB
  have hX : X.IsHermitian := (sqrt_isHermitian A).sub (sqrt_isHermitian B)
  have hsl : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hid : A - B = SA * X + X * SB := by
    have h1 : SA * SA = A := CFC.sqrt_mul_sqrt_self A hA0
    have h2 : SB * SB = B := CFC.sqrt_mul_sqrt_self B hB
    simp only [X, mul_sub, sub_mul, h1, h2]; abel
  refine norm_le_of_eigen hX (div_nonneg (norm_nonneg _) hsl.le) fun t v hv1 hv => ?_
  set a := ⟪v, toEuclideanLin SA v⟫
  set b := ⟪v, toEuclideanLin SB v⟫
  have ha : Real.sqrt lam ≤ a := by
    have := le_inner_of_le (smul_one_le_sqrt hlam.le hA) v
    rwa [hv1, one_pow, mul_one] at this
  have hb : 0 ≤ b := inner_nonneg_of_nonneg (CFC.sqrt_nonneg B) v
  have hq : ⟪v, toEuclideanLin (A - B) v⟫ = t * (a + b) := by
    rw [hid, map_add, LinearMap.add_apply, inner_add_right, lin_mul, lin_mul, hv, map_smul, inner_smul_right,
      inner_symm hX v, hv, inner_smul_left]
    simp only [a, b, RCLike.conj_to_real]; ring
  have hbound := abs_inner_le (A - B) v
  rw [hq, hv1, one_pow, mul_one, abs_mul, abs_of_nonneg (by linarith : 0 ≤ a + b)] at hbound
  rw [le_div_iff₀ hsl]
  calc |t| * Real.sqrt lam ≤ |t| * (a + b) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg t)
    _ ≤ ‖A - B‖ := hbound

/-! ### Inverses -/

lemma isUnit_of_le {S : Matrix n n ℝ} (hS : S.IsHermitian) {c : ℝ} (hc : 0 < c)
    (h : c • (1 : Matrix n n ℝ) ≤ S) : IsUnit S := by
  have hpd : S.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hS fun x hx => ?_
    have h1 := le_inner_of_le h (toLp 2 x)
    rw [inner_eq_dotProduct, ofLp_toLp] at h1
    have h2 : 0 < ‖(toLp 2 x : EuclideanSpace ℝ n)‖ := by
      rw [norm_pos_iff]; intro h0; exact hx (by simpa using congrArg ofLp h0)
    nlinarith [sq_pos_of_pos h2]
  exact hpd.isUnit

/-- `c • 1 ≤ S` with `c > 0` gives `‖S⁻¹‖ ≤ c⁻¹`. -/
theorem norm_inv_le_of_le {S : Matrix n n ℝ} (hS : S.IsHermitian) {c : ℝ} (hc : 0 < c)
    (h : c • (1 : Matrix n n ℝ) ≤ S) : ‖S⁻¹‖ ≤ c⁻¹ := by
  have hu := isUnit_of_le hS hc h
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hu
  have hSi : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hdet
  refine norm_le_of_eigen hS.inv (inv_nonneg.mpr hc.le) fun t v hv1 hv => ?_
  have hv' : v = t • toEuclideanLin S v := by
    calc v = toEuclideanLin (S * S⁻¹) v := by rw [hSi, lin_one]
      _ = t • toEuclideanLin S v := by rw [lin_mul, hv, map_smul]
  have hq : 1 = t * ⟪v, toEuclideanLin S v⟫ := by
    have := congrArg (fun w => ⟪v, w⟫) hv'
    simp only [inner_smul_right, real_inner_self_eq_norm_sq, hv1] at this
    simpa using this
  have hge := le_inner_of_le h v
  rw [hv1, one_pow, mul_one] at hge
  have hpos : 0 < ⟪v, toEuclideanLin S v⟫ := lt_of_lt_of_le hc hge
  have ht : t = (⟪v, toEuclideanLin S v⟫)⁻¹ := by
    field_simp; linarith
  rw [ht, abs_of_pos (inv_pos.mpr hpos)]
  exact inv_anti₀ hc hge

/-- `S⁻¹ − T⁻¹ = S⁻¹ (T − S) T⁻¹`, so `‖S⁻¹ − T⁻¹‖ ≤ ‖S⁻¹‖ ‖T⁻¹‖ ‖S − T‖`. -/
theorem norm_inv_sub_inv_le {S T : Matrix n n ℝ} (hS : IsUnit S.det) (hT : IsUnit T.det) :
    ‖S⁻¹ - T⁻¹‖ ≤ ‖S⁻¹‖ * ‖T⁻¹‖ * ‖S - T‖ := by
  have h : S⁻¹ * (T - S) * T⁻¹ = S⁻¹ - T⁻¹ := by
    rw [mul_sub, sub_mul, Matrix.mul_assoc S⁻¹ T, Matrix.mul_nonsing_inv T hT, Matrix.mul_one,
      Matrix.nonsing_inv_mul S hS, Matrix.one_mul]
  rw [← h]
  calc ‖S⁻¹ * (T - S) * T⁻¹‖ ≤ ‖S⁻¹ * (T - S)‖ * ‖T⁻¹‖ := norm_mul_le _ _
    _ ≤ ‖S⁻¹‖ * ‖T - S‖ * ‖T⁻¹‖ := by gcongr; exact norm_mul_le _ _
    _ = ‖S⁻¹‖ * ‖T⁻¹‖ * ‖S - T‖ := by rw [norm_sub_rev]; ring

/-! ### The inverse square root near a positive definite matrix -/

/-- A Hermitian `B` within `λ/2` of `A ≥ λ` satisfies `B ≥ λ/2`. -/
theorem half_le_of_near {A B : Matrix n n ℝ} {lam : ℝ} (hA : lam • (1 : Matrix n n ℝ) ≤ A) (hB : B.IsHermitian)
    (hAB : ‖B - A‖ ≤ lam / 2) : (lam / 2) • (1 : Matrix n n ℝ) ≤ B := by
  refine le_of_inner hB fun v => ?_
  have h1 := le_inner_of_le hA v
  have h2 := abs_inner_le (B - A) v
  have h3 : ⟪v, toEuclideanLin (B - A) v⟫ = ⟪v, toEuclideanLin B v⟫ - ⟪v, toEuclideanLin A v⟫ := by
    rw [map_sub, LinearMap.sub_apply, inner_sub_right]
  rw [h3] at h2
  have h4 : ‖B - A‖ * ‖v‖ ^ 2 ≤ lam / 2 * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right hAB (sq_nonneg _)
  have := (abs_le.mp h2).1
  nlinarith

lemma sqrt_isUnit_det {A : Matrix n n ℝ} {lam : ℝ} (hlam : 0 < lam) (hA : lam • (1 : Matrix n n ℝ) ≤ A) :
    IsUnit (CFC.sqrt A).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp
    (isUnit_of_le (sqrt_isHermitian A) (Real.sqrt_pos.mpr hlam) (smul_one_le_sqrt hlam.le hA))

/-- `‖(√A)⁻¹‖ ≤ λ^{-1/2}` for `λ • 1 ≤ A`, `λ > 0`. -/
theorem norm_inv_sqrt_le {A : Matrix n n ℝ} {lam : ℝ} (hlam : 0 < lam) (hA : lam • (1 : Matrix n n ℝ) ≤ A) :
    ‖(CFC.sqrt A)⁻¹‖ ≤ (Real.sqrt lam)⁻¹ :=
  norm_inv_le_of_le (sqrt_isHermitian A) (Real.sqrt_pos.mpr hlam) (smul_one_le_sqrt hlam.le hA)

/-- **Inverse square-root perturbation.** For `λ • 1 ≤ A` (`λ > 0`) and Hermitian `B` with `‖B − A‖ ≤ λ/2`:
`‖(√B)⁻¹ − (√A)⁻¹‖ ≤ (√(λ/2))⁻¹ (√λ)⁻¹ ‖B − A‖ / √λ`. -/
theorem norm_inv_sqrt_sub_le {A B : Matrix n n ℝ} {lam : ℝ} (hlam : 0 < lam) (hA : lam • (1 : Matrix n n ℝ) ≤ A)
    (hB : B.IsHermitian) (hAB : ‖B - A‖ ≤ lam / 2) :
    ‖(CFC.sqrt B)⁻¹ - (CFC.sqrt A)⁻¹‖ ≤
      (Real.sqrt (lam / 2))⁻¹ * (Real.sqrt lam)⁻¹ * (‖B - A‖ / Real.sqrt lam) := by
  have hlam2 : 0 < lam / 2 := by linarith
  have hB2 := half_le_of_near hA hB hAB
  have hB0 : 0 ≤ B := le_trans (by
    rw [Matrix.nonneg_iff_posSemidef]; exact Matrix.PosSemidef.one.smul hlam2.le) hB2
  have h1 := norm_inv_sub_inv_le (sqrt_isUnit_det hlam2 hB2) (sqrt_isUnit_det hlam hA)
  have h2 := norm_inv_sqrt_le hlam2 hB2
  have h3 := norm_inv_sqrt_le hlam hA
  have h4 : ‖CFC.sqrt B - CFC.sqrt A‖ ≤ ‖B - A‖ / Real.sqrt lam := by
    rw [norm_sub_rev, norm_sub_rev B A]; exact norm_sqrt_sub_le hlam hA hB0
  refine h1.trans ?_
  gcongr

/-! ### Facts about `(√A)⁻¹` and Gram matrices -/

lemma sqrt_transpose (A : Matrix n n ℝ) : (CFC.sqrt A)ᵀ = CFC.sqrt A := by
  have h := sqrt_isHermitian A
  rw [← conjTranspose_eq_transpose_of_trivial]; exact h

lemma inv_sqrt_transpose (A : Matrix n n ℝ) : ((CFC.sqrt A)⁻¹)ᵀ = (CFC.sqrt A)⁻¹ := by
  rw [transpose_nonsing_inv, sqrt_transpose]

lemma inv_sqrt_mul_inv_sqrt_mul {A : Matrix n n ℝ} {lam : ℝ} (hlam : 0 < lam) (hA : lam • (1 : Matrix n n ℝ) ≤ A) :
    (CFC.sqrt A)⁻¹ * (CFC.sqrt A)⁻¹ * A = 1 := by
  have hu := sqrt_isUnit_det hlam hA
  have hA0 : 0 ≤ A := le_trans (by
    rw [Matrix.nonneg_iff_posSemidef]; exact Matrix.PosSemidef.one.smul hlam.le) hA
  calc (CFC.sqrt A)⁻¹ * (CFC.sqrt A)⁻¹ * A = (CFC.sqrt A)⁻¹ * (CFC.sqrt A)⁻¹ * (CFC.sqrt A * CFC.sqrt A) := by
        rw [CFC.sqrt_mul_sqrt_self A hA0]
    _ = 1 := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (CFC.sqrt A)⁻¹ (CFC.sqrt A), Matrix.nonsing_inv_mul _ hu,
          Matrix.one_mul, Matrix.nonsing_inv_mul _ hu]

lemma inv_inv_sqrt {A : Matrix n n ℝ} {lam : ℝ} (hlam : 0 < lam) (hA : lam • (1 : Matrix n n ℝ) ≤ A) :
    ((CFC.sqrt A)⁻¹)⁻¹ = CFC.sqrt A :=
  Matrix.nonsing_inv_nonsing_inv _ (sqrt_isUnit_det hlam hA)

lemma inner_lin_transpose (A : Matrix n n ℝ) (v w : EuclideanSpace ℝ n) :
    ⟪v, toEuclideanLin A w⟫ = ⟪toEuclideanLin Aᵀ v, w⟫ := by
  rw [← conjTranspose_eq_transpose_of_trivial, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.adjoint_inner_left]

/-- An invertible `A` has `λ • 1 ≤ A Aᵀ` for some `λ > 0` (`λ = (‖(Aᵀ)⁻¹‖ + 1)^{-2}`). -/
theorem exists_smul_one_le_mul_transpose {A : Matrix n n ℝ} (hA : IsUnit A.det) :
    ∃ lam : ℝ, 0 < lam ∧ lam • (1 : Matrix n n ℝ) ≤ A * Aᵀ := by
  set B := Aᵀ with hBdef
  have hB : IsUnit B.det := by rwa [hBdef, det_transpose]
  refine ⟨((‖B⁻¹‖ + 1) ^ 2)⁻¹, by positivity, ?_⟩
  have hH : (A * Aᵀ).IsHermitian := by
    have := Matrix.isHermitian_mul_conjTranspose_self A
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  refine le_of_inner hH fun v => ?_
  have hq : ⟪v, toEuclideanLin (A * Aᵀ) v⟫ = ‖toEuclideanLin B v‖ ^ 2 := by
    rw [lin_mul, inner_lin_transpose, real_inner_self_eq_norm_sq]
  have hinv : toEuclideanLin B⁻¹ (toEuclideanLin B v) = v := by
    rw [← lin_mul, Matrix.nonsing_inv_mul B hB, lin_one]
  have hv : ‖v‖ ≤ (‖B⁻¹‖ + 1) * ‖toEuclideanLin B v‖ := by
    calc ‖v‖ = ‖toEuclideanLin B⁻¹ (toEuclideanLin B v)‖ := by rw [hinv]
      _ ≤ ‖B⁻¹‖ * ‖toEuclideanLin B v‖ := norm_toEuclideanLin_le _ _
      _ ≤ (‖B⁻¹‖ + 1) * ‖toEuclideanLin B v‖ := by gcongr; linarith
  rw [hq]
  have hpos : 0 < (‖B⁻¹‖ + 1) ^ 2 := by positivity
  rw [inv_mul_le_iff₀ hpos]
  calc ‖v‖ ^ 2 ≤ ((‖B⁻¹‖ + 1) * ‖toEuclideanLin B v‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hv 2
    _ = (‖B⁻¹‖ + 1) ^ 2 * ‖toEuclideanLin B v‖ ^ 2 := by ring

end StatFormal.MatrixSqrtPerturb
