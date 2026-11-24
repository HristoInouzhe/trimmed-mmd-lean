import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The Hilbert cube is strongly compact

Library component (untrusted; no `Statements.lean` involved).

For a complete orthonormal family `e` of a Hilbert space `H` and `(λ_k) ∈ ℓ²`, the cube
`{y : |⟪y, e_k⟫| ≤ λ_k ∀ k}` is compact (`isCompact_cube`). Proof: closed, and totally bounded,
because by Parseval `‖y − Σ_{k<N} ⟪e_k, y⟫ e_k‖² = Σ_{k≥N} ⟪e_k, y⟫² ≤ Σ_{k≥N} λ_k²`, while the
truncations lie in the compact image of a finite-dimensional box.
-/

open Set Filter Metric
open scoped Topology InnerProductSpace RealInnerProductSpace

namespace StatFormal.ConvexH

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `Σ_{k<N} ⟪e_k, y⟫ e_k`. -/
noncomputable def projN (e : ℕ → H) (N : ℕ) (y : H) : H := ∑ k ∈ Finset.range N, ⟪e k, y⟫ • e k

theorem norm_sub_projN_sq {e : ℕ → H} (he : Orthonormal ℝ e) (N : ℕ) (y : H) :
    ‖y - projN e N y‖ ^ 2 = ‖y‖ ^ 2 - ∑ k ∈ Finset.range N, ⟪e k, y⟫ ^ 2 := by
  have h1 : ⟪y, projN e N y⟫ = ∑ k ∈ Finset.range N, ⟪e k, y⟫ ^ 2 := by
    rw [projN, inner_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [real_inner_smul_right, real_inner_comm]; ring
  have h2 : ‖projN e N y‖ ^ 2 = ∑ k ∈ Finset.range N, ⟪e k, y⟫ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, projN, he.inner_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [sq]
  rw [norm_sub_sq_real, h1, h2]; ring

variable [CompleteSpace H]

theorem hasSum_inner_sq {e : ℕ → H} (he : Orthonormal ℝ e)
    (htot : ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure) (y : H) :
    HasSum (fun k => ⟪e k, y⟫ ^ 2) (‖y‖ ^ 2) := by
  have := (HilbertBasis.mk he htot).hasSum_inner_mul_inner y y
  simp only [HilbertBasis.coe_mk] at this
  rw [real_inner_self_eq_norm_sq] at this
  refine this.congr_fun fun k => ?_
  rw [real_inner_comm y (e k)]; ring

theorem isCompact_cube {e : ℕ → H} (he : Orthonormal ℝ e)
    (htot : ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure) {lam : ℕ → ℝ}
    (hlam : Summable fun k => lam k ^ 2) :
    IsCompact {y : H | ∀ k, |⟪y, e k⟫| ≤ lam k} := by
  set S := {y : H | ∀ k, |⟪y, e k⟫| ≤ lam k} with hS
  have hclosed : IsClosed S := by
    rw [hS, ofPred_forall]
    exact isClosed_iInter fun k => isClosed_le (by fun_prop) continuous_const
  refine TotallyBounded.isCompact_of_isClosed (Metric.totallyBounded_iff.2 fun ε hε => ?_) hclosed
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨N, hN⟩ := ((tendsto_sum_nat_add fun k => lam k ^ 2).eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < (ε / 2) ^ 2))).exists
  -- the truncations lie in a compact set
  set Φ : (Fin N → ℝ) → H := fun c => ∑ k : Fin N, c k • e k with hΦ
  have hΦc : Continuous Φ := by rw [hΦ]; fun_prop
  set A := Φ '' (Set.pi univ fun k : Fin N => Icc (-lam k) (lam k)) with hA
  have hAc : IsCompact A := (isCompact_univ_pi fun k => isCompact_Icc).image hΦc
  obtain ⟨t, htf, hcov⟩ := Metric.totallyBounded_iff.1 hAc.totallyBounded (ε / 2) hε2
  refine ⟨t, htf, fun y hy => ?_⟩
  have hpA : projN e N y ∈ A := by
    refine ⟨fun k => ⟪e k, y⟫, fun k _ => ?_, ?_⟩
    · have := hy k; rw [real_inner_comm] at this; exact abs_le.mp this
    · rw [hΦ, projN, Finset.sum_range]
  obtain ⟨z, hz, hdz⟩ := mem_iUnion₂.1 (hcov hpA)
  refine mem_iUnion₂.2 ⟨z, hz, ?_⟩
  -- tail estimate
  have hs := hasSum_inner_sq he htot y
  have htail : ‖y - projN e N y‖ ^ 2 = ∑' k, ⟪e (k + N), y⟫ ^ 2 := by
    rw [norm_sub_projN_sq he, ← hs.tsum_eq, ← hs.summable.sum_add_tsum_nat_add N]; ring
  have hle : ∑' k, ⟪e (k + N), y⟫ ^ 2 ≤ ∑' k, lam (k + N) ^ 2 := by
    refine Summable.tsum_le_tsum (fun k => ?_) ((summable_nat_add_iff N).2 hs.summable)
      ((summable_nat_add_iff N).2 hlam)
    have := hy (k + N); rw [real_inner_comm] at this
    exact sq_le_sq' (abs_le.mp this).1 (abs_le.mp this).2
  have hlt : ‖y - projN e N y‖ < ε / 2 := by
    have : ‖y - projN e N y‖ ^ 2 < (ε / 2) ^ 2 := by rw [htail]; exact hle.trans_lt hN
    exact lt_of_pow_lt_pow_left₀ 2 hε2.le this
  rw [mem_ball] at hdz ⊢
  calc dist y z ≤ dist y (projN e N y) + dist (projN e N y) z := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by rw [dist_eq_norm]; exact add_lt_add hlt hdz
    _ = ε := by ring

end StatFormal.ConvexH
