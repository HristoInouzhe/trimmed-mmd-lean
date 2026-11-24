import StatFormal.Lib.ConvexH.HilbertCube
import Mathlib.Analysis.Convex.TotallyBounded

/-!
# Truncations of a compact set have totally bounded union

Library component (untrusted; no `Statements.lean` involved).

For a complete orthonormal family `e` and a compact `T ⊆ H`, the set `T ∪ ⋃_N P_N(T)`, `P_N = projN e N` the
orthogonal projection onto `span {e_k : k < N}`, is totally bounded (`totallyBounded_union_projN`); with Mazur
(`TotallyBounded.convexHull`) its closed convex hull is compact (`isCompact_closure_convexHull_projN`). This is the
compact common range of `rem:app-common-compact-available`(ii) (otfd A).
-/

open Set Filter Metric
open scoped Topology InnerProductSpace RealInnerProductSpace

namespace StatFormal.ConvexH

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem projN_sub (e : ℕ → H) (N : ℕ) (x y : H) : projN e N (x - y) = projN e N x - projN e N y := by
  simp only [projN, inner_sub_right, sub_smul, Finset.sum_sub_distrib]

theorem norm_projN_le {e : ℕ → H} (he : Orthonormal ℝ e) (N : ℕ) (x : H) : ‖projN e N x‖ ≤ ‖x‖ := by
  have h2 : ‖projN e N x‖ ^ 2 = ∑ k ∈ Finset.range N, ⟪e k, x⟫ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, projN, he.inner_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [sq]
  have hb := he.sum_inner_products_le (s := Finset.range N) (x := x)
  have : ‖projN e N x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [h2]; refine le_trans (le_of_eq ?_) hb
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Real.norm_eq_abs, sq_abs]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this

theorem continuous_projN (e : ℕ → H) (N : ℕ) : Continuous (projN e N) := by
  unfold projN; fun_prop

variable [CompleteSpace H]

theorem tendsto_projN {e : ℕ → H} (he : Orthonormal ℝ e)
    (htot : ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure) (x : H) :
    Tendsto (fun N => projN e N x) atTop (𝓝 x) := by
  have := ((HilbertBasis.mk he htot).hasSum_repr x).tendsto_sum_nat
  simp only [HilbertBasis.repr_apply_apply, HilbertBasis.coe_mk] at this
  exact this

theorem totallyBounded_union_projN {e : ℕ → H} (he : Orthonormal ℝ e)
    (htot : ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure) {T : Set H} (hT : IsCompact T) :
    TotallyBounded (T ∪ ⋃ N, projN e N '' T) := by
  refine Metric.totallyBounded_iff.2 fun ε hε => ?_
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨t₀, ht₀T, ht₀f, hcov₀⟩ := finite_cover_balls_of_compact hT hε3
  obtain ⟨N₀, hN₀⟩ := (((eventually_all_finite ht₀f).2 fun x _ =>
    (tendsto_projN he htot x).eventually (ball_mem_nhds x hε3))).exists_forall_of_atTop
  set A := ⋃ N ∈ Finset.range N₀, projN e N '' T with hA
  have hAc : IsCompact A :=
    (Finset.range N₀).isCompact_biUnion fun N _ => hT.image (continuous_projN e N)
  obtain ⟨tA, htAf, hcovA⟩ := Metric.totallyBounded_iff.1 hAc.totallyBounded ε hε
  refine ⟨t₀ ∪ tA, ht₀f.union htAf, ?_⟩
  have hball : ∀ y, ∀ x ∈ t₀, dist y x < ε / 3 + ε / 3 → y ∈ ⋃ z ∈ t₀ ∪ tA, ball z ε := by
    intro y x hx hd
    exact mem_iUnion₂.2 ⟨x, Or.inl hx, mem_ball.2 (by linarith)⟩
  rintro y (hy | hy)
  · obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 (hcov₀ hy)
    exact hball y x hx (by rw [mem_ball] at hyx; linarith)
  · obtain ⟨N, x, hxT, rfl⟩ := mem_iUnion.1 hy
    by_cases hN : N < N₀
    · have : projN e N x ∈ A := mem_iUnion₂.2 ⟨N, Finset.mem_range.2 hN, x, hxT, rfl⟩
      obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.1 (hcovA this)
      exact mem_iUnion₂.2 ⟨z, Or.inr hz, hyz⟩
    · obtain ⟨x₀, hx₀, hxx₀⟩ := mem_iUnion₂.1 (hcov₀ hxT)
      have h1 : ‖projN e N x - projN e N x₀‖ ≤ ‖x - x₀‖ := by
        rw [← projN_sub]; exact norm_projN_le he N _
      have h2 : dist (projN e N x₀) x₀ < ε / 3 := mem_ball.1 (hN₀ N (not_lt.1 hN) x₀ hx₀)
      refine hball _ x₀ hx₀ ?_
      calc dist (projN e N x) x₀ ≤ dist (projN e N x) (projN e N x₀) + dist (projN e N x₀) x₀ :=
            dist_triangle _ _ _
        _ < ε / 3 + ε / 3 := by
          rw [dist_eq_norm]
          have : ‖x - x₀‖ < ε / 3 := by rw [← dist_eq_norm]; exact mem_ball.1 hxx₀
          linarith

theorem isCompact_closure_convexHull_projN {e : ℕ → H} (he : Orthonormal ℝ e)
    (htot : ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure) {T : Set H} (hT : IsCompact T) :
    IsCompact (closure (convexHull ℝ (T ∪ ⋃ N, projN e N '' T))) :=
  ((totallyBounded_union_projN he htot hT).convexHull.closure).isCompact_of_isClosed isClosed_closure

end StatFormal.ConvexH
