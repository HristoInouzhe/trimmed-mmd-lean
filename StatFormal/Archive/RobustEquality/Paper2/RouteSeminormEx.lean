import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.EReal.Basic
import Mathlib.Order.CompleteLattice.Basic

/-!
# Route for paper2 `thm:seminorm` (iv)(a),(c): Wasserstein and anisotropic sets on the whole space

`ε = 0`, reference of full support on `K = E` (whole space), cost `c(x₀, x) = ‖A(x − x₀)‖²` for a
continuous linear automorphism `A` of a real Hilbert space `E` (`A = id`: Wasserstein balls, (a);
`A = M^{-1/2}`: anisotropic sets with matrix `M`, (c)). The groupwise term is
`T⁰(w, λ) = λ β + sup_{u ∈ E} {⟪w,u⟫² − λ ‖A u‖²}` (per anchor; by `anchor_sup_eq` every anchor gives
the same supremum, so the average over the centre is this value), in `EReal` (it is `+∞` for small `λ`).

Main results, with `v = (A⁻¹)† w` (`= w` for (a), `= M^{1/2} w` for (c)):
* `sup_quad`: for `λ > 0`, `sup_u {⟪w,u⟫² − λ‖A u‖²} = 0` if `‖v‖² ≤ λ`, `= ⊤` otherwise;
* `inf_T0`: `inf_{λ > 0} T⁰(w, λ) = β ‖v‖²`, i.e. `N(w) = √β ‖v‖` (`√β |w|`, resp. `√β |M^{1/2} w|`).
-/

noncomputable section
open ContinuousLinearMap

namespace StatFormal.RobustEquality.Paper2.Route

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- `T⁰(w, λ) = λ β + sup_u {⟪w,u⟫² − λ‖Au‖²}`. -/
def T0full (A : E ≃L[ℝ] E) (β : ℝ) (w : E) (l : ℝ) : EReal :=
  ((l * β : ℝ) : EReal) + ⨆ u : E, (((inner ℝ w u) ^ 2 - l * ‖A u‖ ^ 2 : ℝ) : EReal)

omit [CompleteSpace E] in
/-- Every anchor gives the same supremum (translation invariance). -/
lemma anchor_sup_eq (A : E ≃L[ℝ] E) (w : E) (l : ℝ) (x₀ : E) :
    (⨆ x : E, (((inner ℝ w (x - x₀)) ^ 2 - l * ‖A (x - x₀)‖ ^ 2 : ℝ) : EReal)) =
      ⨆ u : E, (((inner ℝ w u) ^ 2 - l * ‖A u‖ ^ 2 : ℝ) : EReal) :=
  (Equiv.subRight x₀).iSup_comp (g := fun u => (((inner ℝ w u) ^ 2 - l * ‖A u‖ ^ 2 : ℝ) : EReal))

lemma inner_eq_adj (A : E ≃L[ℝ] E) (w u : E) :
    inner ℝ w u = inner ℝ ((adjoint (A.symm : E →L[ℝ] E)) w) (A u) := by
  rw [adjoint_inner_left]
  simp

theorem sup_quad (A : E ≃L[ℝ] E) (w : E) {l : ℝ} (hl : 0 < l) :
    (⨆ u : E, (((inner ℝ w u) ^ 2 - l * ‖A u‖ ^ 2 : ℝ) : EReal)) =
      if ‖(adjoint (A.symm : E →L[ℝ] E)) w‖ ^ 2 ≤ l then 0 else ⊤ := by
  obtain ⟨v, hv⟩ : ∃ v, (adjoint (A.symm : E →L[ℝ] E)) w = v := ⟨_, rfl⟩
  rw [hv]
  split_ifs with hvl
  · refine le_antisymm (iSup_le fun u => ?_) ?_
    · rw [inner_eq_adj A w u, hv]
      have h := abs_real_inner_le_norm v (A u)
      have h2 : (inner ℝ v (A u)) ^ 2 ≤ (‖v‖ * ‖A u‖) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
      have : (inner ℝ v (A u)) ^ 2 - l * ‖A u‖ ^ 2 ≤ 0 := by
        nlinarith [sq_nonneg ‖A u‖]
      exact_mod_cast this
    · have := le_iSup (fun u : E => (((inner ℝ w u) ^ 2 - l * ‖A u‖ ^ 2 : ℝ) : EReal)) 0
      simpa using this
  · push Not at hvl
    refine (EReal.eq_top_iff_forall_lt _).mpr fun M => ?_
    have hv0 : 0 < ‖v‖ ^ 2 := hl.trans hvl
    set c := ‖v‖ ^ 2 * (‖v‖ ^ 2 - l)
    have hc : 0 < c := mul_pos hv0 (by linarith)
    set t := √((|M| + 1) / c)
    have ht2 : t ^ 2 = (|M| + 1) / c := Real.sq_sqrt (by positivity)
    set u := A.symm (t • v)
    have hAu : A u = t • v := by simp [u]
    have hval : (inner ℝ w u) ^ 2 - l * ‖A u‖ ^ 2 = t ^ 2 * c := by
      rw [inner_eq_adj A w u, hv, hAu, inner_smul_right, norm_smul, real_inner_self_eq_norm_sq,
        Real.norm_eq_abs]
      simp only [mul_pow, sq_abs, c]
      ring
    have hlt : M < (inner ℝ w u) ^ 2 - l * ‖A u‖ ^ 2 := by
      rw [hval, ht2, div_mul_cancel₀ _ hc.ne']
      linarith [le_abs_self M]
    exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr hlt)
      (le_iSup (fun u : E => (((inner ℝ w u) ^ 2 - l * ‖A u‖ ^ 2 : ℝ) : EReal)) u)

/-- **(iv)(a),(c)** `inf_{λ>0} T⁰(w, λ) = β ‖(A⁻¹)† w‖²`. -/
theorem inf_T0 (A : E ≃L[ℝ] E) {β : ℝ} (hβ : 0 ≤ β) (w : E) :
    (⨅ l : Set.Ioi (0 : ℝ), T0full A β w l) =
      ((β * ‖(adjoint (A.symm : E →L[ℝ] E)) w‖ ^ 2 : ℝ) : EReal) := by
  have key : ∀ l : Set.Ioi (0 : ℝ), T0full A β w l = ((l * β : ℝ) : EReal) +
      if ‖(adjoint (A.symm : E →L[ℝ] E)) w‖ ^ 2 ≤ (l : ℝ) then 0 else ⊤ := fun l => by
    unfold T0full
    rw [sup_quad A w l.2]
  simp_rw [key]
  set N2 := ‖(adjoint (A.symm : E →L[ℝ] E)) w‖ ^ 2 with hN2
  have hN2nn : 0 ≤ N2 := sq_nonneg _
  refine le_antisymm ?_ ?_
  · rcases eq_or_lt_of_le hN2nn with h0 | hpos
    · rw [← h0, mul_zero]
      refine le_of_forall_gt_imp_ge_of_dense fun z hz => ?_
      induction z using EReal.rec with
      | bot => exact absurd hz (not_lt.mpr bot_le)
      | top => exact le_top
      | coe α =>
        have hα : 0 < α := EReal.coe_lt_coe_iff.mp hz
        have hl : 0 < α / (β + 1) := div_pos hα (by linarith)
        refine (iInf_le _ ⟨α / (β + 1), hl⟩).trans ?_
        have hc : (0 : ℝ) ≤ α / (β + 1) := hl.le
        simp only [hc, ite_true, add_zero]
        refine EReal.coe_le_coe_iff.mpr ?_
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith
    · refine (iInf_le _ ⟨N2, hpos⟩).trans ?_
      simp only [le_refl, ite_true, add_zero]
      exact le_of_eq (by rw [mul_comm])
  · refine le_iInf fun l => ?_
    by_cases hl : N2 ≤ (l : ℝ)
    · simp only [hl, ite_true, add_zero]
      refine EReal.coe_le_coe_iff.mpr ?_
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right hl hβ
    · simp only [hl, ite_false, EReal.coe_add_top]
      exact le_top

end StatFormal.RobustEquality.Paper2.Route
