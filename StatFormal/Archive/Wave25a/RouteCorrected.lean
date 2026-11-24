import StatFormal.Archive.Wave25a.Statements
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Moments.Variance

/-!
# Route — SB `prop:corrected` (untrusted)

Coordinatewise: `T̃_i − m_i = Σ_k A_{ik}(T_k − E T_k)`, so `E T̃ = m` and `Cov(T̃) = A P Aᵀ`, and with `A = V^{1/2}P^{-1/2}`
(both symmetric, `P^{-1/2} P P^{-1/2} = I`) `A P Aᵀ = V^{1/2} V^{1/2} = V`. Gaussian case: `T̃ ∘ T` is affine, so
`T̃#R` is Gaussian; two Gaussian laws whose linear functionals have equal means and variances have equal
characteristic functions.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Matrix
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave25a

variable {d : ℕ}

section Moments

variable {R : Measure (EuclideanSpace ℝ (Fin d))}

lemma integral_coordE {Y : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hY : Integrable Y R) (i : Fin d) :
    (∫ x, Y x ∂R) i = ∫ x, Y x i ∂R := by
  have h := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm hY
  simpa using h.symm

lemma memLp_coordE {Y : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hY : MemLp Y 2 R) (i : Fin d) :
    MemLp (fun x => Y x i) 2 R :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hY

lemma integrable_cprod [IsFiniteMeasure R] {Y : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hY : MemLp Y 2 R) (i j : Fin d) (a b : ℝ) :
    Integrable (fun x => (Y x i - a) * (Y x j - b)) R :=
  ((memLp_coordE hY i).sub (memLp_const a)).integrable_mul ((memLp_coordE hY j).sub (memLp_const b))

lemma corrMap_apply (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (m : EuclideanSpace ℝ (Fin d))
    (A : Matrix (Fin d) (Fin d) ℝ) (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    corrMap R T m A x i = m i + ∑ k, A i k * (T x k - meanV R T k) := by
  simp [corrMap, Matrix.mulVec, dotProduct]

/-- `T̃` as `m + L(T − E T)` with `L` continuous linear. -/
lemma corrMap_eq (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (m : EuclideanSpace ℝ (Fin d))
    (A : Matrix (Fin d) (Fin d) ℝ) :
    corrMap R T m A = fun x => m + LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A) (T x - meanV R T) := by
  funext x
  ext i
  rw [corrMap_apply]
  simp [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]

variable [IsProbabilityMeasure R]

lemma memLp_corrMap {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hT : MemLp T 2 R)
    (m : EuclideanSpace ℝ (Fin d)) (A : Matrix (Fin d) (Fin d) ℝ) : MemLp (corrMap R T m A) 2 R := by
  rw [corrMap_eq]
  exact (memLp_const m).add ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)).comp_memLp'
    (hT.sub (memLp_const _)))

lemma meanV_coord {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hT : MemLp T 2 R) (k : Fin d) :
    meanV R T k = ∫ x, T x k ∂R :=
  integral_coordE (hT.integrable one_le_two) k

lemma meanV_corrMap {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hT : MemLp T 2 R)
    (m : EuclideanSpace ℝ (Fin d)) (A : Matrix (Fin d) (Fin d) ℝ) : meanV R (corrMap R T m A) = m := by
  ext i
  rw [meanV_coord (memLp_corrMap hT m A)]
  simp_rw [corrMap_apply]
  have hk : ∀ k, Integrable (fun x => A i k * (T x k - meanV R T k)) R := fun k =>
    (((memLp_coordE hT k).integrable one_le_two).sub (integrable_const _)).const_mul _
  rw [integral_add (integrable_const _) (integrable_finsetSum _ fun k _ => hk k), integral_finsetSum _ fun k _ => hk k]
  have h0 : ∀ k, ∫ x, A i k * (T x k - meanV R T k) ∂R = 0 := fun k => by
    rw [integral_const_mul, integral_sub ((memLp_coordE hT k).integrable one_le_two) (integrable_const _),
      ← meanV_coord hT k]
    simp
  simp [h0]

lemma covM_corrMap {T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hT : MemLp T 2 R)
    (m : EuclideanSpace ℝ (Fin d)) (A : Matrix (Fin d) (Fin d) ℝ) :
    covM R (corrMap R T m A) = A * covM R T * A.transpose := by
  ext i j
  have hR : (A * covM R T * A.transpose) i j = ∑ k, ∑ l, A i k * A j l * covM R T k l := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hR]
  change ∫ x, (corrMap R T m A x i - meanV R (corrMap R T m A) i) *
      (corrMap R T m A x j - meanV R (corrMap R T m A) j) ∂R = _
  rw [meanV_corrMap hT m A]
  simp_rw [corrMap_apply, add_sub_cancel_left, Finset.sum_mul_sum]
  have hint : ∀ k l, Integrable (fun x => A i k * (T x k - meanV R T k) * (A j l * (T x l - meanV R T l))) R :=
    fun k l => by
      have := (integrable_cprod hT k l (meanV R T k) (meanV R T l)).const_mul (A i k * A j l)
      refine this.congr (ae_of_all _ fun x => ?_)
      simp only; ring
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun l _ => hint k l]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show covM R T k l = ∫ x, (T x k - meanV R T k) * (T x l - meanV R T l) ∂R from rfl, ← integral_const_mul]
  congr 1; funext x; ring

lemma inner_eq_sum (t y : EuclideanSpace ℝ (Fin d)) : ⟪t, y⟫ = ∑ i, t i * y i := by
  simp [PiLp.inner_apply, mul_comm]

/-- `Var[⟪t, Z⟫] = Σ_{ij} t_i t_j Cov(Z)_{ij}`. -/
lemma variance_inner {Z : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hZ : MemLp Z 2 R)
    (t : EuclideanSpace ℝ (Fin d)) :
    Var[fun x => ⟪t, Z x⟫; R] = ∑ i, ∑ j, t i * t j * covM R Z i j := by
  have hZi : Integrable Z R := hZ.integrable one_le_two
  have hmeas : AEMeasurable (fun x => ⟪t, Z x⟫) R :=
    (aestronglyMeasurable_const.inner hZ.aestronglyMeasurable).aemeasurable
  rw [variance_eq_integral hmeas]
  have hmean : ∫ x, ⟪t, Z x⟫ ∂R = ∑ i, t i * meanV R Z i := by
    rw [integral_inner hZi, inner_eq_sum]; rfl
  simp_rw [hmean, inner_eq_sum, ← Finset.sum_sub_distrib, sq, Finset.sum_mul_sum]
  have hint : ∀ i j, Integrable (fun x => (t i * Z x i - t i * meanV R Z i) * (t j * Z x j - t j * meanV R Z j)) R :=
    fun i j => by
      have := (integrable_cprod hZ i j (meanV R Z i) (meanV R Z j)).const_mul (t i * t j)
      refine this.congr (ae_of_all _ fun x => ?_)
      simp only; ring
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold covM
  rw [← integral_const_mul]; congr 1; funext x; ring

end Moments

lemma corrected_algebra (P Vh Ph : Matrix (Fin d) (Fin d) ℝ) (hVh : Vh.transpose = Vh) (hPh : Ph.transpose = Ph)
    (hP : Ph * P * Ph = 1) : Vh * Ph * P * (Vh * Ph).transpose = Vh * Vh := by
  rw [Matrix.transpose_mul, hVh, hPh]
  calc Vh * Ph * P * (Ph * Vh) = Vh * (Ph * P * Ph) * Vh := by simp only [Matrix.mul_assoc]
    _ = Vh * Vh := by rw [hP, Matrix.mul_one]

theorem corrected_moments : Claims.corrected_moments := by
  intro d R _ T m V Vh Ph hT hVh hV hPh hP
  refine ⟨meanV_corrMap hT m _, ?_⟩
  rw [covM_corrMap hT m, corrected_algebra _ Vh Ph hVh hPh hP, hV]

theorem corrected_gaussian : Claims.corrected_gaussian := by
  intro d R ν _ _ M c Vh Ph hVh hV hPh hP
  set T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun x => M x + c with hTdef
  have hT : MemLp T 2 R := (M.comp_memLp' IsGaussian.memLp_two_id).add (memLp_const c)
  set A := Vh * Ph
  set L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)
  set b : EuclideanSpace ℝ (Fin d) := meanV ν id + L (c - meanV R T)
  have hTt : corrMap R T (meanV ν id) A = (fun y => y + b) ∘ (L.comp M) := by
    rw [corrMap_eq]; funext x
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, b, hTdef]
    rw [show M x + c - meanV R T = M x + (c - meanV R T) by abel, map_add]
    abel
  have hmap : R.map (corrMap R T (meanV ν id) A) = (R.map (L.comp M)).map (fun y => y + b) := by
    rw [hTt, Measure.map_map (by fun_prop) (by fun_prop)]
  haveI : IsGaussian (R.map (corrMap R T (meanV ν id) A)) := by rw [hmap]; infer_instance
  have hTm : Measurable (corrMap R T (meanV ν id) A) := by rw [hTt]; fun_prop
  have hTL : MemLp (corrMap R T (meanV ν id) A) 2 R := memLp_corrMap hT _ _
  apply Measure.ext_of_charFun
  funext t
  have hmean : ∫ x, ((⟪t, x⟫ : ℝ) : ℂ) ∂(R.map (corrMap R T (meanV ν id) A)) = ∫ x, ((⟪t, x⟫ : ℝ) : ℂ) ∂ν := by
    rw [integral_complex_ofReal, integral_complex_ofReal]
    congr 1
    have hν := integral_inner (𝕜 := ℝ) (μ := ν) (IsGaussian.integrable_id) t
    simp only [id] at hν
    rw [integral_map hTm.aemeasurable (by fun_prop), integral_inner (hTL.integrable one_le_two), hν]
    congr 1
    exact meanV_corrMap hT _ _
  have hvar : Var[fun x => ⟪t, x⟫; R.map (corrMap R T (meanV ν id) A)] = Var[fun x => ⟪t, x⟫; ν] := by
    rw [variance_map (by fun_prop) hTm.aemeasurable]
    have h1 := variance_inner hTL t
    have h2 := variance_inner (R := ν) (Z := id) IsGaussian.memLp_two_id t
    simp only [Function.comp_def, id] at h1 h2 ⊢
    rw [h1, covM_corrMap hT, corrected_algebra _ Vh Ph hVh hPh hP, hV, h2]
  rw [IsGaussian.charFun_eq, IsGaussian.charFun_eq, hmean, hvar]

end StatFormal.Wave25a
