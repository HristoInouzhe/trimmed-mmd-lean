import StatFormal.Archive.Wave17a.Statements
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Route: NN `prop:noncentral-tube`, the Gaussian–affine core (untrusted)

* `dist(x, V)² = Σ_i ⟨b_i, x − v₀⟩²` for an orthonormal basis `(b_i)` of `W = (dir V)ᗮ` and any `v₀ ∈ V`
  (Pythagoras against the direction).
* `L x = (⟨b_i, x⟩)_i` pushes `stdGaussian E` to `stdGaussian ℝ^c` (characteristic functionals: `L` is a
  coisometry, `‖f ∘ L‖ = ‖f‖`).
* A reflection of `ℝ^c` sends `−q/σ` to `(√λ, 0, …, 0)` and preserves the standard Gaussian.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Metric
open scoped InnerProductSpace RealInnerProductSpace ENNReal

namespace StatFormal.Wave17a

section Core
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Distance to an affine subspace through the orthogonal complement of its direction. -/
lemma infDist_affine_sq (V : AffineSubspace ℝ E) {v₀ : E} (hv₀ : v₀ ∈ V) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V.directionᗮ) (x : E) :
    infDist x V ^ 2 = ∑ i, ⟪(b i : E), x - v₀⟫ ^ 2 := by
  set d := x - v₀
  set dV := V.direction.starProjection d
  set dW := d - dV
  have hdW : dW ∈ V.directionᗮ := V.direction.sub_starProjection_mem_orthogonal d
  have hdV : dV ∈ V.direction := V.direction.starProjection_apply_mem d
  have hne : (V : Set E).Nonempty := ⟨v₀, hv₀⟩
  have hdist : infDist x V = ‖dW‖ := by
    apply le_antisymm
    · have hy : dV + v₀ ∈ V := AffineSubspace.vadd_mem_of_mem_direction hdV hv₀
      refine (infDist_le_dist_of_mem hy).trans_eq ?_
      rw [dist_eq_norm]; congr 1; simp only [dW, d]; abel
    · refine (le_infDist hne).2 fun y hy => ?_
      have hk : dV - (y - v₀) ∈ V.direction := V.direction.sub_mem hdV (AffineSubspace.vsub_mem_direction hy hv₀)
      have hxy : x - y = dW + (dV - (y - v₀)) := by simp only [dW, d]; abel
      rw [dist_eq_norm, hxy]
      have h0 : ⟪dW, dV - (y - v₀)⟫ = 0 := Submodule.inner_left_of_mem_orthogonal hk hdW
      have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero dW _ h0
      rw [mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)]
      nlinarith [mul_self_nonneg ‖dV - (y - v₀)‖]
  rw [hdist]
  have hpars := b.sum_sq_norm_inner_right (⟨dW, hdW⟩ : V.directionᗮ)
  rw [show ‖dW‖ = ‖(⟨dW, hdW⟩ : V.directionᗮ)‖ from rfl, ← hpars]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, sq_abs, Submodule.coe_inner]
  congr 1
  have : ⟪(b i : E), dV⟫ = 0 := Submodule.inner_left_of_mem_orthogonal hdV (b i).2
  simp only [dW, inner_sub_right, this, sub_zero]

variable [MeasurableSpace E] [BorelSpace E]

/-- The coordinate map `x ↦ (⟨b_i, x⟩)_i` of a subspace basis. -/
def coordL {W : Submodule ℝ E} {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ W) :
    E →L[ℝ] EuclideanSpace ℝ ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 fun i => ⟪(b i : E), x⟫
      map_add' := fun x y => by ext i; simp [inner_add_right]
      map_smul' := fun c x => by ext i; simp [inner_smul_right] }

lemma coordL_apply {W : Submodule ℝ E} {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ W) (x : E) (i : ι) :
    (coordL b x) i = ⟪(b i : E), x⟫ := rfl

lemma map_coordL {W : Submodule ℝ E} {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ W) :
    (stdGaussian E).map (coordL b) = stdGaussian (EuclideanSpace ℝ ι) := by
  apply Measure.ext_of_charFunDual
  funext f
  rw [charFunDual_map, charFunDual_stdGaussian, charFunDual_stdGaussian]
  suffices hnorm : ‖f.comp (coordL b)‖ = ‖f‖ by rw [hnorm]
  -- `‖f ∘ L‖ = ‖f‖`
  set L := coordL b
  have hon : Orthonormal ℝ fun i => (b i : E) := b.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  have hL : ∀ x, ‖L x‖ ≤ ‖x‖ := by
    intro x
    have h1 := hon.sum_inner_products_le x (s := Finset.univ)
    have h2 : ‖L x‖ ^ 2 = ∑ i, ‖⟪(b i : E), x⟫‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]; rfl
    rw [← h2] at h1
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1
  have hJ : ∀ t : EuclideanSpace ℝ ι, L ((b.repr.symm t : W) : E) = t := by
    intro t
    ext i
    rw [coordL_apply, ← Submodule.coe_inner, ← OrthonormalBasis.repr_apply_apply, LinearIsometryEquiv.apply_symm_apply]
  have hJn : ∀ t : EuclideanSpace ℝ ι, ‖((b.repr.symm t : W) : E)‖ = ‖t‖ := by
    intro t; change ‖b.repr.symm t‖ = ‖t‖; exact LinearIsometryEquiv.norm_map _ _
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    calc ‖(f.comp L) x‖ = ‖f (L x)‖ := rfl
      _ ≤ ‖f‖ * ‖L x‖ := f.le_opNorm _
      _ ≤ ‖f‖ * ‖x‖ := mul_le_mul_of_nonneg_left (hL x) (norm_nonneg _)
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun t => ?_
    calc ‖f t‖ = ‖(f.comp L) ((b.repr.symm t : W) : E)‖ := by rw [ContinuousLinearMap.comp_apply, hJ]
      _ ≤ ‖f.comp L‖ * ‖((b.repr.symm t : W) : E)‖ := (f.comp L).le_opNorm _
      _ = ‖f.comp L‖ * ‖t‖ := by rw [hJn]

/-- The noncentral shift vector `(√λ, 0, …, 0)`. -/
def ncShift (c : ℕ) (lam : ℝ) : EuclideanSpace ℝ (Fin c) :=
  WithLp.toLp 2 fun i => if (i : ℕ) = 0 then Real.sqrt lam else 0

lemma ncChiSq_Iic (c : ℕ) (lam t : ℝ) :
    ncChiSq c lam (Iic t) = stdGaussian (EuclideanSpace ℝ (Fin c)) {y | ‖y + ncShift c lam‖ ^ 2 ≤ t} := by
  have hmeas : MeasurableSet {y : EuclideanSpace ℝ (Fin c) | ‖y + ncShift c lam‖ ^ 2 ≤ t} :=
    (isClosed_le (by fun_prop) continuous_const).measurableSet
  rw [← map_pi_eq_stdGaussian, Measure.map_apply (by fun_prop) hmeas, ncChiSq,
    Measure.map_apply (by fun_prop) measurableSet_Iic]
  congr 1
  ext z
  simp only [mem_preimage, mem_Iic, mem_ofPred_eq, EuclideanSpace.norm_sq_eq, ncShift, Real.norm_eq_abs, sq_abs]
  rfl

/-- Rotation invariance: the law of `‖Y + u‖²` depends on `u` only through `‖u‖`. -/
lemma stdGaussian_shift {c : ℕ} {u u' : EuclideanSpace ℝ (Fin c)} (h : ‖u‖ = ‖u'‖) (t : ℝ) :
    stdGaussian (EuclideanSpace ℝ (Fin c)) {y | ‖y + u‖ ^ 2 ≤ t} =
      stdGaussian (EuclideanSpace ℝ (Fin c)) {y | ‖y + u'‖ ^ 2 ≤ t} := by
  set R := Submodule.reflection (ℝ ∙ (u - u'))ᗮ
  have hR : R u = u' := Submodule.reflection_sub h
  have hmeas : MeasurableSet {y : EuclideanSpace ℝ (Fin c) | ‖y + u'‖ ^ 2 ≤ t} :=
    (isClosed_le (by fun_prop) continuous_const).measurableSet
  conv_rhs => rw [← stdGaussian_map R]
  rw [Measure.map_apply R.continuous.measurable hmeas]
  congr 1
  ext y
  simp only [mem_ofPred_eq, mem_preimage]
  rw [← hR, ← map_add, LinearIsometryEquiv.norm_map]

end Core

theorem noncentral_tube_affine : Claims.noncentral_tube_affine := by
  intro E _ _ _ _ _ V σ δ ⟨v₀, hv₀⟩ hσ hδ
  set K := V.direction
  set c := Module.finrank ℝ Kᗮ
  have hc : Module.finrank ℝ E - Module.finrank ℝ K = c := by
    have := K.finrank_add_finrank_orthogonal; omega
  rw [hc]
  set b := stdOrthonormalBasis ℝ Kᗮ
  set q : Fin c → ℝ := fun i => ⟪(b i : E), v₀⟫
  set u : EuclideanSpace ℝ (Fin c) := WithLp.toLp 2 fun i => -(q i / σ)
  have hlamq : infDist 0 (V : Set E) ^ 2 / σ ^ 2 = ∑ i, (q i / σ) ^ 2 := by
    rw [infDist_affine_sq V hv₀ b 0, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [zero_sub, inner_neg_right, q, div_pow, neg_sq]
  have hu : ‖u‖ ^ 2 = infDist 0 (V : Set E) ^ 2 / σ ^ 2 := by
    rw [hlamq, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [u, Real.norm_eq_abs, sq_abs]
    rw [← abs_div, sq_abs]
  set lam := infDist 0 (V : Set E) ^ 2 / σ ^ 2
  have hlam0 : 0 ≤ lam := by positivity
  have hshift : ‖u‖ = ‖ncShift c lam‖ := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), hu, EuclideanSpace.norm_sq_eq]
    rcases Nat.eq_zero_or_pos c with h0 | hpos
    · -- `c = 0`: both sides vanish
      have : lam = ∑ i : Fin c, (q i / σ) ^ 2 := hlamq
      rw [show lam = lam from rfl, this]
      simp [h0]
    · rw [Finset.sum_eq_single (⟨0, hpos⟩ : Fin c) (fun i _ hi => by
          have : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
          simp [ncShift, this]) (by simp)]
      simp [ncShift, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hlam0]
  -- the event in the Gaussian coordinates
  have hmeasE : MeasurableSet {x : E | infDist x V ≤ δ} :=
    (isClosed_le (continuous_infDist_pt _) continuous_const).measurableSet
  set t := δ ^ 2 / σ ^ 2
  have hpre : (fun z : E => σ • z) ⁻¹' {x | infDist x V ≤ δ} =
      coordL b ⁻¹' {y | ‖y + u‖ ^ 2 ≤ t} := by
    ext z
    simp only [mem_preimage, mem_ofPred_eq]
    rw [← pow_le_pow_iff_left₀ infDist_nonneg hδ.le two_ne_zero, infDist_affine_sq V hv₀ b,
      EuclideanSpace.norm_sq_eq, le_div_iff₀ (by positivity), Finset.sum_mul]
    have : ∀ i, ‖(coordL b z + u) i‖ ^ 2 * σ ^ 2 = ⟪(b i : E), σ • z - v₀⟫ ^ 2 := by
      intro i
      rw [Real.norm_eq_abs, sq_abs, PiLp.add_apply, coordL_apply]
      simp only [u, q, inner_sub_right, real_inner_smul_right]
      field_simp
      ring
    simp_rw [this]
  have hmeasS : MeasurableSet {y : EuclideanSpace ℝ (Fin c) | ‖y + u‖ ^ 2 ≤ t} :=
    (isClosed_le (by fun_prop) continuous_const).measurableSet
  have hmain : isoGauss E σ {x | infDist x V ≤ δ} = ncChiSq c lam (Iic t) := by
    rw [isoGauss, Measure.map_apply (by fun_prop) hmeasE, hpre, ← Measure.map_apply (coordL b).continuous.measurable hmeasS,
      map_coordL, ncChiSq_Iic, stdGaussian_shift hshift]
  rw [Measure.real, Measure.real, hmain]

end StatFormal.Wave17a
