import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.OrderClosed

/-!
# Half-spaces of a real inner-product space: frontier, distance to the hyperplane, translates (library, untrusted)

For a real inner-product space `V`, a vector `e` and `a ∈ ℝ`, let `G = {x | a < ⟪x, e⟫}` (an open half-space).

* `frontier_halfspace`: for `e ≠ 0`, `∂G = {x | ⟪x, e⟫ = a}`: `G` is open, its frontier lies in the hyperplane
  (`frontier_lt_subset_eq`), and every point of the hyperplane is the limit of `x + t e ∈ G` as `t ↓ 0`;
* `infDist_hyperplane`, `infDist_frontier_halfspace`: for a unit `e`, `dist(x, {⟪·, e⟫ = a}) = |⟪x, e⟫ − a|`, attained at the
  orthogonal projection `x − (⟪x, e⟫ − a) e`, and `|⟪x − y, e⟫| ≤ ‖x − y‖` (Cauchy–Schwarz) for every `y` of the hyperplane;
* `preimage_sub_halfspace`: the translate `G + h = (· − h)⁻¹' G` is the half-space `{a + ⟪h, e⟫ < ⟪x, e⟫}`;
* `symmDiff_halfspace_subset`: `G △ (G + h)` lies in the slab `min(a, a + ⟪h, e⟫) ≤ ⟪x, e⟫ ≤ max(a, a + ⟪h, e⟫)`, of width
  `|⟪h, e⟫|`;
* `symmDiff_inter_subset`: `(s ∩ t) △ (s′ ∩ t′) ⊆ ((s △ s′) ∩ t) ∪ (t ∖ t′) ∪ (t′ ∖ t)` (plain set algebra).
-/

set_option linter.style.longLine false

noncomputable section
open Set Filter Topology
open scoped InnerProductSpace RealInnerProductSpace symmDiff

namespace StatFormal.HalfSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The frontier of the open half-space `{a < ⟪x, e⟫}` (`e ≠ 0`) is the hyperplane `{⟪x, e⟫ = a}`. -/
theorem frontier_halfspace {e : V} (he : e ≠ 0) (a : ℝ) :
    frontier {x : V | a < ⟪x, e⟫_ℝ} = {x | ⟪x, e⟫_ℝ = a} := by
  have hc : Continuous fun x : V => ⟪x, e⟫_ℝ := continuous_id.inner continuous_const
  apply Subset.antisymm
  · intro x hx
    exact (frontier_lt_subset_eq (f := fun _ : V => a) (g := fun x : V => ⟪x, e⟫_ℝ) continuous_const hc hx).symm
  · intro x hx
    have hopen : IsOpen {x : V | a < ⟪x, e⟫_ℝ} := isOpen_lt continuous_const hc
    rw [frontier, hopen.interior_eq]
    simp only [mem_ofPred_eq] at hx
    refine ⟨?_, fun h => by simp only [mem_ofPred_eq] at h; linarith⟩
    have he2 : 0 < ⟪e, e⟫_ℝ := real_inner_self_pos.2 he
    have ht : Tendsto (fun t : ℝ => x + t • e) (𝓝[>] 0) (𝓝 x) := by
      have h0 : Tendsto (fun t : ℝ => x + t • e) (𝓝 0) (𝓝 (x + (0 : ℝ) • e)) :=
        (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
      rw [zero_smul, add_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [self_mem_nhdsWithin] with t ht0
    have ht0' : 0 < t := ht0
    simp only [inner_add_left, real_inner_smul_left, hx]
    nlinarith

/-- The distance from `x` to the hyperplane `{⟪·, e⟫ = a}` (`‖e‖ = 1`) is `|⟪x, e⟫ − a|`. -/
theorem infDist_hyperplane {e : V} (he : ‖e‖ = 1) (a : ℝ) (x : V) :
    Metric.infDist x {y : V | ⟪y, e⟫_ℝ = a} = |⟪x, e⟫_ℝ - a| := by
  have hee : ⟪e, e⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  have hy₀ : x - (⟪x, e⟫_ℝ - a) • e ∈ {y : V | ⟪y, e⟫_ℝ = a} := by
    simp only [mem_ofPred_eq, inner_sub_left, real_inner_smul_left, hee]; ring
  apply le_antisymm
  · calc Metric.infDist x {y : V | ⟪y, e⟫_ℝ = a} ≤ dist x (x - (⟪x, e⟫_ℝ - a) • e) :=
          Metric.infDist_le_dist_of_mem hy₀
      _ = |⟪x, e⟫_ℝ - a| := by
        rw [dist_eq_norm, sub_sub_cancel, norm_smul, Real.norm_eq_abs, he, mul_one]
  · rw [Metric.le_infDist ⟨_, hy₀⟩]
    intro y hy
    simp only [mem_ofPred_eq] at hy
    rw [← hy, ← inner_sub_left, dist_eq_norm]
    calc |⟪x - y, e⟫_ℝ| ≤ ‖x - y‖ * ‖e‖ := abs_real_inner_le_norm _ _
      _ = ‖x - y‖ := by rw [he, mul_one]

/-- `dist(x, ∂{a < ⟪·, e⟫}) = |⟪x, e⟫ − a|` for a unit vector `e`. -/
theorem infDist_frontier_halfspace {e : V} (he : ‖e‖ = 1) (a : ℝ) (x : V) :
    Metric.infDist x (frontier {x : V | a < ⟪x, e⟫_ℝ}) = |⟪x, e⟫_ℝ - a| := by
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  rw [frontier_halfspace he0, infDist_hyperplane he]

/-- The translate of a half-space: `(· − h)⁻¹' {a < ⟪·, e⟫} = {a + ⟪h, e⟫ < ⟪·, e⟫}`. -/
theorem preimage_sub_halfspace (e h : V) (a : ℝ) :
    (· - h) ⁻¹' {x : V | a < ⟪x, e⟫_ℝ} = {x | a + ⟪h, e⟫_ℝ < ⟪x, e⟫_ℝ} := by
  ext x
  simp only [mem_preimage, mem_ofPred_eq, inner_sub_left]
  constructor <;> intro h' <;> linarith

/-- `G △ (G + h)` lies in the slab between the hyperplanes `⟪·, e⟫ = a` and `⟪·, e⟫ = a + ⟪h, e⟫`. -/
theorem symmDiff_halfspace_subset (e h : V) (a : ℝ) :
    symmDiff {x : V | a < ⟪x, e⟫_ℝ} ((· - h) ⁻¹' {x : V | a < ⟪x, e⟫_ℝ}) ⊆
      {x | min a (a + ⟪h, e⟫_ℝ) ≤ ⟪x, e⟫_ℝ ∧ ⟪x, e⟫_ℝ ≤ max a (a + ⟪h, e⟫_ℝ)} := by
  rw [preimage_sub_halfspace]
  intro x hx
  simp only [Set.mem_symmDiff, mem_ofPred_eq, not_lt] at hx
  simp only [mem_ofPred_eq]
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨(min_le_left _ _).trans h1.le, h2.trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans h1.le, h2.trans (le_max_left _ _)⟩

/-- `max(a, a + t) − min(a, a + t) = |t|`. -/
theorem max_sub_min_add (a t : ℝ) : max a (a + t) - min a (a + t) = |t| := by
  rcases le_total 0 t with ht | ht
  · rw [max_eq_right (by linarith), min_eq_left (by linarith), abs_of_nonneg ht]; ring
  · rw [max_eq_left (by linarith), min_eq_right (by linarith), abs_of_nonpos ht]; ring

/-- Set algebra: `(s ∩ t) △ (s′ ∩ t′) ⊆ ((s △ s′) ∩ t) ∪ (t ∖ t′) ∪ (t′ ∖ t)`. -/
theorem symmDiff_inter_subset {α : Type*} (s s' t t' : Set α) :
    symmDiff (s ∩ t) (s' ∩ t') ⊆ (symmDiff s s' ∩ t) ∪ (t \ t') ∪ (t' \ t) := by
  intro x hx
  simp only [Set.mem_symmDiff, mem_inter_iff, mem_union, Set.mem_sdiff] at hx ⊢
  tauto

end StatFormal.HalfSpace
