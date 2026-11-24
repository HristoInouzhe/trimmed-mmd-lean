import StatFormal.Lib.FourierOps.Mollify

/-!
# A mollified indicator equals the indicator away from the boundary (library, untrusted)

Let `G ⊆ V` be open, `E = G ∩ B(c₀, ρ)`, `b` a probability density supported in the closed unit ball and `0 < w ≤ 1`. For `x` in
the smaller ball `B(c₀, ρ − 1)` at distance more than `w` from `∂G`, the mollified indicator `f_w = 1_E ∗ b_w` equals `1_G(x)`:
the closed ball `B̄(x, w)` lies in `B(c₀, ρ)`, misses `∂G`, and, being connected, lies in the open set `G` or in the open set
`V ∖ Ḡ` (`IsPreconnected.subset_or_subset`); `f_w` is `1` or `0` accordingly (`FourierOps.mollify_smooth_facts`). This is the
geometric step of the proof of Theorem S4.10 of trimmed-mmd.
-/

noncomputable section
open MeasureTheory Set Metric
open scoped ContDiff

namespace StatFormal.MollifierNorm

open StatFormal.Wave31tp (mollify dilateR)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

/-- **Away from the boundary**: for `G` open, `x ∈ B(c₀, ρ − 1)` with `dist(x, ∂G) > w`, `0 < w ≤ 1`,
`(1_{G ∩ B(c₀,ρ)} ∗ b_w)(x) = 1_G(x)`. -/
theorem mollify_eq_indicator_of_lt_infDist {G : Set V} (hG : IsOpen G) {c₀ x : V} {ρ w : ℝ} {b : V → ℝ}
    (hb : ContDiff ℝ ∞ b) (hb0 : ∀ x, 0 ≤ b x) (hb1 : ∫ x, b x = 1) (hbs : Function.support b ⊆ closedBall 0 1)
    (hw : 0 < w) (hw1 : w ≤ 1) (hx : x ∈ ball c₀ (ρ - 1)) (hd : w < infDist x (frontier G)) :
    mollify (G ∩ ball c₀ ρ) (dilateR w b) x = G.indicator (fun _ => (1 : ℝ)) x := by
  have hE : MeasurableSet (G ∩ ball c₀ ρ) := hG.measurableSet.inter measurableSet_ball
  have hEb : Bornology.IsBounded (G ∩ ball c₀ ρ) := isBounded_ball.subset inter_subset_right
  obtain ⟨-, -, -, hone, hzero, -⟩ := FourierOps.mollify_smooth_facts hE hEb hb hb0 hb1 hbs hw
  have hball : closedBall x w ⊆ ball c₀ ρ := by
    intro y hy
    rw [mem_ball] at hx ⊢
    rw [mem_closedBall] at hy
    linarith [dist_triangle y x c₀]
  have hfr : closedBall x w ⊆ interior G ∪ (closure G)ᶜ := by
    intro y hy
    by_contra hcon
    rw [mem_union, not_or, mem_compl_iff, not_not] at hcon
    have hyf : y ∈ frontier G := ⟨hcon.2, hcon.1⟩
    have := infDist_le_dist_of_mem (x := x) hyf
    rw [mem_closedBall, dist_comm] at hy
    linarith
  have hxw : x ∈ closedBall x w := mem_closedBall_self hw.le
  rcases (convex_closedBall x w).isPreconnected.subset_or_subset isOpen_interior isClosed_closure.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset_closure) hfr with h | h
  · have hG' : closedBall x w ⊆ G := h.trans interior_subset
    rw [hone x (subset_inter hG' hball), indicator_of_mem (hG' hxw)]
  · have hxG : x ∉ G := fun hxG => h hxw (subset_closure hxG)
    rw [hzero x (eq_empty_of_forall_notMem fun y ⟨hy, hyE⟩ => h hy (subset_closure hyE.1)),
      indicator_of_notMem hxG]

end StatFormal.MollifierNorm
