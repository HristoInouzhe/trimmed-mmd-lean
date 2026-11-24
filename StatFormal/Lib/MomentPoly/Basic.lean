import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Moment-matching polynomials on `[−T, T]` (library, untrusted)

For `T > 0` and `N : ℕ`, every vector `M ∈ ℝ^N` is the moment vector `(∫_{−T}^{T} t^j G(t) dt)_{j<N}` of exactly one real
polynomial `G` of degree `< N`; and the rescaling `H(v) = T G(Tv)` carries moments on `[−T, T]` to moments on `[−1, 1]`
(paper S4 :905-911; classically, the Gram matrix of `1, t, …, t^{N−1}` in `L²[−T, T]` is positive definite, Szegő,
*Orthogonal Polynomials*, Ch. II).

Route. A polynomial of degree `< N` with vanishing moments `j < N` has `∫ G² = Σ_j g_j ∫ t^j G = 0`, and a nonzero
polynomial is nonzero off a finite set, so `∫ G² > 0`: hence `G = 0` (`eq_zero_of_moments_eq_zero`). This makes the
moment matrix `A_{jk} = ∫ t^{j+k}` injective, hence surjective (finite dimension), which gives existence; uniqueness is the
same lemma applied to a difference. The scaling is `intervalIntegral.integral_comp_mul_left`.

* `eq_zero_of_moments_eq_zero`, `existsUnique_moments`: L28 (a);
* `integral_scale_moment`, `integral_scale_abs`: L28 (b).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Polynomial
open scoped Matrix

namespace StatFormal.MomentPoly

lemma intervalIntegrable_pow_mul_eval (G : ℝ[X]) (j : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => t ^ j * G.eval t) volume a b :=
  ((continuous_pow j).mul G.continuous).intervalIntegrable a b

/-- **Vanishing moments force `G = 0`.** A real polynomial of degree `< N` whose moments `∫_{−T}^{T} t^j G(t) dt` vanish for
every `j < N` is zero, when `T > 0`. -/
theorem eq_zero_of_moments_eq_zero {T : ℝ} (hT : 0 < T) {N : ℕ} {G : ℝ[X]} (hG : G.degree < N)
    (h : ∀ j < N, ∫ t in (-T)..T, t ^ j * G.eval t = 0) : G = 0 := by
  by_contra hne
  have hnat : G.natDegree < N := (natDegree_lt_iff_degree_lt hne).2 hG
  -- `∫ G² = Σ_j g_j ∫ t^j G = 0`
  have hsq : ∫ t in (-T)..T, G.eval t ^ 2 = 0 := by
    have e : ∀ t : ℝ, G.eval t ^ 2 = ∑ j ∈ Finset.range N, G.coeff j * (t ^ j * G.eval t) := by
      intro t
      rw [sq]
      nth_rewrite 1 [eval_eq_sum_range' hnat t]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp_rw [e]
    rw [intervalIntegral.integral_finsetSum fun j _ => (intervalIntegrable_pow_mul_eval G j _ _).const_mul _]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [intervalIntegral.integral_const_mul, h j (Finset.mem_range.mp hj), mul_zero]
  -- but `∫ G² > 0`, since `G ≠ 0` off a finite set
  have hpos : 0 < ∫ t in (-T)..T, G.eval t ^ 2 := by
    rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun t => sq_nonneg _)
      ((G.continuous.pow 2).intervalIntegrable _ _)]
    refine ⟨by linarith, ?_⟩
    have hZ : volume {x : ℝ | IsRoot G x} = 0 := (finite_setOfPred_isRoot hne).measure_zero _
    have hsub : Ioc (-T) T \ {x : ℝ | IsRoot G x} ⊆ Function.support (fun t => G.eval t ^ 2) ∩ Ioc (-T) T := by
      rintro x ⟨hx, hr⟩
      exact ⟨pow_ne_zero 2 hr, hx⟩
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [measure_sdiff_null hZ, Real.volume_Ioc]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  exact hpos.ne' hsq

/-- The polynomial `Σ_{k<N} c_k X^k` with coefficient vector `c`. -/
def ofCoeffs {N : ℕ} (c : Fin N → ℝ) : ℝ[X] := ∑ k : Fin N, C (c k) * X ^ (k : ℕ)

lemma degree_ofCoeffs_lt {N : ℕ} (c : Fin N → ℝ) : (ofCoeffs c).degree < N := degree_sum_fin_lt c

lemma eval_ofCoeffs {N : ℕ} (c : Fin N → ℝ) (t : ℝ) : (ofCoeffs c).eval t = ∑ k : Fin N, c k * t ^ (k : ℕ) := by
  simp [ofCoeffs, eval_finsetSum]

lemma coeff_ofCoeffs {N : ℕ} (c : Fin N → ℝ) (k : Fin N) : (ofCoeffs c).coeff k = c k := by
  simp [ofCoeffs, Fin.val_inj]

/-- The moment (Hankel) matrix `A_{jk} = ∫_{−T}^{T} t^{j+k} dt`. -/
def momentMatrix (T : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ := fun j k => ∫ t in (-T)..T, t ^ ((j : ℕ) + k)

/-- The moments of `Σ_k c_k X^k` are `A c`. -/
lemma moments_ofCoeffs (T : ℝ) {N : ℕ} (c : Fin N → ℝ) (j : Fin N) :
    ∫ t in (-T)..T, t ^ (j : ℕ) * (ofCoeffs c).eval t = (momentMatrix T N *ᵥ c) j := by
  simp only [eval_ofCoeffs, Finset.mul_sum, Matrix.mulVec, dotProduct, momentMatrix]
  rw [intervalIntegral.integral_finsetSum fun k _ =>
    (by fun_prop : Continuous fun t : ℝ => t ^ (j : ℕ) * (c k * t ^ (k : ℕ))).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← intervalIntegral.integral_mul_const]
  congr 1
  funext t
  ring

/-- The moment matrix is invertible on `[−T, T]`, `T > 0`: its `mulVec` is surjective. -/
lemma momentMatrix_mulVec_surjective {T : ℝ} (hT : 0 < T) (N : ℕ) :
    Function.Surjective (momentMatrix T N).mulVec := by
  refine Matrix.mulVec_surjective_iff_isUnit.mpr (Matrix.mulVec_injective_iff_isUnit.mp ?_)
  intro c c' hcc
  have h0 : ofCoeffs (c - c') = 0 := by
    refine eq_zero_of_moments_eq_zero hT (degree_ofCoeffs_lt _) fun j hj => ?_
    rw [moments_ofCoeffs T (c - c') ⟨j, hj⟩, Matrix.mulVec_sub, hcc, sub_self, Pi.zero_apply]
  funext k
  have := coeff_ofCoeffs (c - c') k
  rw [h0, coeff_zero, Pi.sub_apply] at this
  linarith

/-- **Moment matching (L28 a).** For `T > 0`, every `M : Fin N → ℝ` is the moment vector `(∫_{−T}^{T} t^j G(t) dt)_{j<N}` of
exactly one real polynomial `G` of degree `< N`. -/
theorem existsUnique_moments {T : ℝ} (hT : 0 < T) {N : ℕ} (M : Fin N → ℝ) :
    ∃! G : ℝ[X], G.degree < N ∧ ∀ j : Fin N, ∫ t in (-T)..T, t ^ (j : ℕ) * G.eval t = M j := by
  obtain ⟨c, hc⟩ := momentMatrix_mulVec_surjective hT N M
  refine ⟨ofCoeffs c, ⟨degree_ofCoeffs_lt c, fun j => by rw [moments_ofCoeffs, hc]⟩, ?_⟩
  rintro G ⟨hG, hGM⟩
  have hD : (G - ofCoeffs c).degree < N := (degree_sub_le _ _).trans_lt (max_lt hG (degree_ofCoeffs_lt c))
  refine sub_eq_zero.mp (eq_zero_of_moments_eq_zero hT hD fun j hj => ?_)
  have e : ∀ t : ℝ, t ^ j * (G - ofCoeffs c).eval t = t ^ j * G.eval t - t ^ j * (ofCoeffs c).eval t := by
    intro t; rw [eval_sub, mul_sub]
  simp_rw [e]
  rw [intervalIntegral.integral_sub (intervalIntegrable_pow_mul_eval _ _ _ _) (intervalIntegrable_pow_mul_eval _ _ _ _),
    hGM ⟨j, hj⟩, moments_ofCoeffs T c ⟨j, hj⟩, hc, sub_self]

/-- **Scaling of moments (L28 b).** With `H(v) = T G(Tv)`, `∫_{−1}^{1} v^j H(v) dv = T^{−j} ∫_{−T}^{T} t^j G(t) dt`. -/
theorem integral_scale_moment {T : ℝ} (hT : 0 < T) (G : ℝ[X]) (j : ℕ) :
    ∫ v in (-1 : ℝ)..1, v ^ j * (T * G.eval (T * v)) = T⁻¹ ^ j * ∫ t in (-T)..T, t ^ j * G.eval t := by
  have hT0 : T ≠ 0 := hT.ne'
  have e : ∀ v : ℝ, v ^ j * (T * G.eval (T * v)) = (T⁻¹ ^ j * T) * ((T * v) ^ j * G.eval (T * v)) := by
    intro v
    rw [mul_pow, inv_pow]
    field_simp
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left (fun t => t ^ j * G.eval t) hT0, mul_neg, mul_one, smul_eq_mul]
  field_simp

/-- **Scaling of the `L¹` norm (L28 b).** `∫_{−1}^{1} |T G(Tv)| dv = ∫_{−T}^{T} |G(t)| dt`. -/
theorem integral_scale_abs {T : ℝ} (hT : 0 < T) (G : ℝ[X]) :
    ∫ v in (-1 : ℝ)..1, |T * G.eval (T * v)| = ∫ t in (-T)..T, |G.eval t| := by
  have e : ∀ v : ℝ, |T * G.eval (T * v)| = T * |G.eval (T * v)| := fun v => by
    rw [abs_mul, abs_of_pos hT]
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left (fun t => |G.eval t|) hT.ne', mul_neg, mul_one, smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ hT.ne', one_mul]

end StatFormal.MomentPoly
