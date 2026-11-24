import StatFormal.Lib.MomentPoly.Basic

/-!
# A linear moment solver on `[−L, L]` with an explicit sup bound (library, untrusted)

For `N : ℕ` and `L > 0` the function `solL N L m`, a polynomial of degree `< N`, has the prescribed moments
`∫_{−L}^{L} t^j solL N L m (t) dt = m_j` for `j < N`, and on `[−L, L]`
`|solL N L m (t)| ≤ L⁻¹ · K_N · Σ_j L^{−j} |m_j|` with `K_N = Σ_k Σ_j |(A⁻¹)_{kj}|`, `A` the moment (Hankel) matrix of the
monomials on `[−1, 1]` (`MomentPoly.momentMatrix 1 N`, invertible by the certified L28). This is the map `𝒢_T` of the
proof of Proposition S4.15 of the trimmed-mmd supplement (S4 :803-815) with its operator norm made explicit: `solL N L` is
`𝒢₁` conjugated by the dilation `t = Lv` (`solL N L m (t) = L⁻¹ S₁((L^{−j} m_j)_j)(t/L)`, as in the printed
"the polynomial `v ↦ T G₀(Tv)` has moments `T^{−j} M_j(0)` on `[−1, 1]`").

* `sol1`, `sol1_moments`: the solver on `[−1, 1]`, `S₁(m) = Σ_k (A⁻¹ m)_k v^k`;
* `solL`, `solL_moments`, `continuous_solL`, `abs_solL_le`: the dilated solver, its moments, continuity and sup bound.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Polynomial
open scoped Matrix

namespace StatFormal.MomentTrim

open StatFormal.MomentPoly

/-- The coefficient vector `A⁻¹ m` of the moment problem on `[−1, 1]`. -/
def solCoeff (N : ℕ) (m : Fin N → ℝ) : Fin N → ℝ := (momentMatrix 1 N)⁻¹ *ᵥ m

/-- The solution `S₁(m)(v) = Σ_k (A⁻¹ m)_k v^k` of the moment problem on `[−1, 1]`. -/
def sol1 (N : ℕ) (m : Fin N → ℝ) (v : ℝ) : ℝ := ∑ k : Fin N, solCoeff N m k * v ^ (k : ℕ)

/-- The constant `K_N = Σ_k Σ_j |(A⁻¹)_{kj}|` (a bound for the operator norm of `𝒢₁`). -/
def solK (N : ℕ) : ℝ := ∑ k : Fin N, ∑ j : Fin N, |(momentMatrix 1 N)⁻¹ k j|

lemma solK_nonneg (N : ℕ) : 0 ≤ solK N :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma continuous_sol1 (N : ℕ) (m : Fin N → ℝ) : Continuous (sol1 N m) := by
  unfold sol1; fun_prop

/-- The moments of `S₁(m)` on `[−1, 1]` are `m`. -/
theorem sol1_moments (N : ℕ) (m : Fin N → ℝ) (j : Fin N) :
    ∫ v in (-1 : ℝ)..1, v ^ (j : ℕ) * sol1 N m v = m j := by
  have hU : IsUnit (momentMatrix 1 N) := Matrix.mulVec_surjective_iff_isUnit.mp (momentMatrix_mulVec_surjective one_pos N)
  have e : ∀ v : ℝ, sol1 N m v = (ofCoeffs (solCoeff N m)).eval v := fun v => (eval_ofCoeffs _ v).symm
  simp_rw [e]
  rw [moments_ofCoeffs 1 (solCoeff N m) j, solCoeff, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hU), Matrix.one_mulVec]

/-- `|S₁(m)(v)| ≤ K_N · max-type bound`: for `|v| ≤ 1`, `|S₁(m)(v)| ≤ K_N · B` whenever `|m_j| ≤ B` for all `j`. -/
theorem abs_sol1_le (N : ℕ) (m : Fin N → ℝ) {v B : ℝ} (hv : |v| ≤ 1) (hB : ∀ j, |m j| ≤ B) :
    |sol1 N m v| ≤ solK N * B := by
  have hB0 : ∀ j, 0 ≤ B := fun j => (abs_nonneg _).trans (hB j)
  unfold sol1 solK
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul, abs_pow]
  have hvk : |v| ^ (k : ℕ) ≤ 1 := pow_le_one₀ (abs_nonneg _) hv
  have hc : |solCoeff N m k| ≤ (∑ j : Fin N, |(momentMatrix 1 N)⁻¹ k j|) * B := by
    unfold solCoeff Matrix.mulVec dotProduct
    rw [Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hB j) (abs_nonneg _)
  calc |solCoeff N m k| * |v| ^ (k : ℕ) ≤ |solCoeff N m k| * 1 :=
        mul_le_mul_of_nonneg_left hvk (abs_nonneg _)
    _ ≤ (∑ j : Fin N, |(momentMatrix 1 N)⁻¹ k j|) * B := by rw [mul_one]; exact hc

/-- The dilated solver on `[−L, L]`: `solL N L m (t) = L⁻¹ S₁((L^{−j} m_j)_j)(t/L)`. -/
def solL (N : ℕ) (L : ℝ) (m : Fin N → ℝ) (t : ℝ) : ℝ :=
  L⁻¹ * sol1 N (fun j => (L ^ (j : ℕ))⁻¹ * m j) (t / L)

lemma continuous_solL (N : ℕ) (L : ℝ) (m : Fin N → ℝ) : Continuous (solL N L m) := by
  unfold solL
  exact continuous_const.mul ((continuous_sol1 N _).comp (continuous_id.div_const L))

/-- **Moments of the dilated solver.** For `L > 0` and `j < N`, `∫_{−L}^{L} t^j solL N L m (t) dt = m_j`. -/
theorem solL_moments (N : ℕ) {L : ℝ} (hL : 0 < L) (m : Fin N → ℝ) (j : Fin N) :
    ∫ t in (-L)..L, t ^ (j : ℕ) * solL N L m t = m j := by
  have hL0 : L ≠ 0 := hL.ne'
  set m' : Fin N → ℝ := fun j => (L ^ (j : ℕ))⁻¹ * m j
  have e : ∀ t : ℝ, t ^ (j : ℕ) * solL N L m t =
      (L ^ (j : ℕ) * L⁻¹) * ((fun v => v ^ (j : ℕ) * sol1 N m' v) (t / L)) := by
    intro t
    have ht : t ^ (j : ℕ) = L ^ (j : ℕ) * (t / L) ^ (j : ℕ) := by
      rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero _ hL0)]
    change t ^ (j : ℕ) * (L⁻¹ * sol1 N m' (t / L)) = _
    rw [ht]; ring
  simp_rw [e]
  have h := intervalIntegral.integral_comp_div (fun v => v ^ (j : ℕ) * sol1 N m' v) hL0 (a := -L) (b := L)
  rw [intervalIntegral.integral_const_mul, h, neg_div, div_self hL0, sol1_moments N m' j, smul_eq_mul]
  simp only [m']
  field_simp

/-- **Sup bound of the dilated solver.** For `L > 0` and `|t| ≤ L`,
`|solL N L m (t)| ≤ L⁻¹ · K_N · Σ_j L^{−j} |m_j|`. -/
theorem abs_solL_le (N : ℕ) {L : ℝ} (hL : 0 < L) (m : Fin N → ℝ) {t : ℝ} (ht : |t| ≤ L) :
    |solL N L m t| ≤ L⁻¹ * solK N * ∑ j : Fin N, (L ^ (j : ℕ))⁻¹ * |m j| := by
  have hv : |t / L| ≤ 1 := by rw [abs_div, abs_of_pos hL, div_le_one hL]; exact ht
  have hB : ∀ j : Fin N, |(L ^ (j : ℕ))⁻¹ * m j| ≤ ∑ i : Fin N, (L ^ (i : ℕ))⁻¹ * |m i| := by
    intro j
    rw [abs_mul, abs_of_pos (inv_pos.mpr (pow_pos hL _))]
    exact Finset.single_le_sum (f := fun i : Fin N => (L ^ (i : ℕ))⁻¹ * |m i|)
      (fun i _ => mul_nonneg (inv_nonneg.mpr (pow_nonneg hL.le _)) (abs_nonneg _)) (Finset.mem_univ j)
  unfold solL
  rw [abs_mul, abs_of_pos (inv_pos.mpr hL), mul_assoc]
  exact mul_le_mul_of_nonneg_left (abs_sol1_le N _ hv hB) (inv_nonneg.mpr hL.le)

end StatFormal.MomentTrim
