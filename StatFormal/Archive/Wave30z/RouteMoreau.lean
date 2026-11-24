import StatFormal.Archive.Wave30z.Statements
import StatFormal.Archive.Wave30v.RouteDelta
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-!
# Route — wave 30z Moreau identity for `cor:boundary-linear` (untrusted)

* `metricProj_spec`: for a nonempty closed (convex) `C` in finite dimension a nearest point exists
  (`IsClosed.exists_infDist_eq_dist`, `E` is proper), so `metricProj C x` is one.
* Nearest points in a convex set are characterised by the variational inequality
  `⟪x − p, w − p⟫ ≤ 0` (`norm_eq_iInf_iff_real_inner_le_zero`), hence unique.
* Moreau: for a nonempty closed convex cone `K` with nearest point `p`, testing `w = 0, 2p` gives
  `⟪x − p, p⟫ = 0`, so `x − p ∈ K°`; and `x − p` satisfies the variational inequality for `K°`
  (`⟪p, y − (x − p)⟫ = ⟪p, y⟫ ≤ 0`), so `metricProj K° x = x − p` and
  `‖metricProj K° x‖ = ‖x − p‖ = infDist x K`.
-/

set_option linter.style.longLine false

noncomputable section
open Set Metric
open scoped InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave30z

open StatFormal.Wave30v (polarSet)

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A nearest point of a convex set is characterised by the variational inequality. -/
lemma isNearest_iff_inner_le_zero {C : Set E} (hcv : Convex ℝ C) {x p : E} (hp : p ∈ C) :
    (∀ q ∈ C, ‖x - p‖ ≤ ‖x - q‖) ↔ ∀ w ∈ C, ⟪x - p, w - p⟫ ≤ 0 := by
  have hbdd : BddBelow (range fun w : C => ‖x - w‖) := ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
  have : Nonempty C := ⟨⟨p, hp⟩⟩
  rw [← norm_eq_iInf_iff_real_inner_le_zero hcv hp]
  constructor
  · intro h
    exact le_antisymm (le_ciInf fun w => h w w.2) (ciInf_le hbdd ⟨p, hp⟩)
  · intro h q hq
    rw [h]
    exact ciInf_le hbdd ⟨q, hq⟩

/-- Nearest points of a convex set are unique. -/
lemma nearest_unique {C : Set E} (hcv : Convex ℝ C) {x a b : E} (ha : a ∈ C) (hb : b ∈ C)
    (hamin : ∀ q ∈ C, ‖x - a‖ ≤ ‖x - q‖) (hbmin : ∀ q ∈ C, ‖x - b‖ ≤ ‖x - q‖) : a = b := by
  have h1 := (isNearest_iff_inner_le_zero hcv ha).1 hamin b hb
  have h2 := (isNearest_iff_inner_le_zero hcv hb).1 hbmin a ha
  have h3 : ⟪b - a, b - a⟫ ≤ 0 := by
    have : ⟪b - a, b - a⟫ = ⟪x - a, b - a⟫ + ⟪x - b, a - b⟫ := by
      rw [show a - b = -(b - a) by abel, inner_neg_right, ← sub_eq_add_neg, ← inner_sub_left]
      congr 1
      abel
    linarith
  have h4 : b - a = 0 := by
    have := real_inner_self_nonneg (x := b - a)
    exact inner_self_eq_zero.1 (le_antisymm h3 this)
  exact (sub_eq_zero.1 h4).symm

end

/-- `metricProj C x` is a nearest point of `C` to `x` for nonempty closed convex `C` in finite
dimension. -/
theorem metricProj_spec {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (C : Set E) (hne : C.Nonempty) (hcl : IsClosed C) (_hcv : Convex ℝ C) (x : E) :
    metricProj C x ∈ C ∧ ∀ q ∈ C, ‖x - metricProj C x‖ ≤ ‖x - q‖ := by
  have h : ∃ p ∈ C, ∀ q ∈ C, ‖x - p‖ ≤ ‖x - q‖ := by
    obtain ⟨y, hy, hd⟩ := hcl.exists_infDist_eq_dist hne x
    refine ⟨y, hy, fun q hq => ?_⟩
    rw [← dist_eq_norm, ← dist_eq_norm, ← hd]
    exact infDist_le_dist_of_mem hq
  have he : metricProj C x = h.choose := by
    simp only [metricProj, h, ↓reduceDIte]
  rw [he]
  exact h.choose_spec

/-- **Moreau**: for a nonempty closed convex cone `K`, `‖Π_{K°} x‖ = dist(x, K)`. -/
theorem metricProj_polar_norm (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (K : Set E)
    (hne : K.Nonempty) (hcl : IsClosed K) (hcv : Convex ℝ K) (hcone : ∀ c : ℝ, 0 ≤ c → ∀ v ∈ K, c • v ∈ K) (x : E) :
    ‖metricProj (polarSet K) x‖ = infDist x K := by
  obtain ⟨hp, hpmin⟩ := metricProj_spec K hne hcl hcv x
  set p := metricProj K x
  have hvi := (isNearest_iff_inner_le_zero hcv hp).1 hpmin
  -- `⟪x − p, p⟫ = 0`
  have h0 : (0 : E) ∈ K := by
    obtain ⟨v, hv⟩ := hne
    simpa using hcone 0 le_rfl v hv
  have hA := hvi 0 h0
  have hB := hvi ((2 : ℝ) • p) (hcone 2 (by norm_num) p hp)
  rw [zero_sub, inner_neg_right] at hA
  rw [show (2 : ℝ) • p - p = p by rw [two_smul]; abel] at hB
  have hperp : ⟪x - p, p⟫ = 0 := le_antisymm hB (by linarith)
  -- `x − p ∈ K°`
  have hpol : x - p ∈ polarSet K := by
    intro w hw
    have := hvi w hw
    rw [inner_sub_right, hperp, sub_zero] at this
    exact this
  -- `K°` is convex, closed and nonempty
  have hpcv : Convex ℝ (polarSet K) := by
    intro a ha b hb s t hs ht _ w hw
    rw [inner_add_left, inner_smul_left, inner_smul_left]
    have h1 := ha w hw
    have h2 := hb w hw
    simp only [conj_trivial]
    nlinarith [mul_nonneg hs (neg_nonneg.2 h1), mul_nonneg ht (neg_nonneg.2 h2)]
  have hpcl : IsClosed (polarSet K) := by
    have : polarSet K = ⋂ w ∈ K, {g : E | ⟪g, w⟫ ≤ 0} := by
      ext g
      simp [polarSet]
    rw [this]
    exact isClosed_biInter fun w _ => isClosed_le (by fun_prop) continuous_const
  have hpne : (polarSet K).Nonempty := ⟨x - p, hpol⟩
  -- `x − p` is a nearest point of `K°`
  have hnear : ∀ y ∈ polarSet K, ‖x - (x - p)‖ ≤ ‖x - y‖ := by
    refine (isNearest_iff_inner_le_zero hpcv hpol).2 fun y hy => ?_
    rw [sub_sub_cancel, inner_sub_right, real_inner_comm (x - p) p, hperp, sub_zero,
      real_inner_comm]
    exact hy p hp
  obtain ⟨hq, hqmin⟩ := metricProj_spec (polarSet K) hpne hpcl hpcv x
  have hq_eq : metricProj (polarSet K) x = x - p := nearest_unique hpcv hq hpol hqmin hnear
  rw [hq_eq]
  -- `‖x − p‖ = infDist x K`
  obtain ⟨y, hy, hd⟩ := hcl.exists_infDist_eq_dist hne x
  refine le_antisymm ?_ ?_
  · rw [hd, dist_eq_norm]
    exact hpmin y hy
  · rw [← dist_eq_norm]
    exact infDist_le_dist_of_mem hp

end StatFormal.Wave30z
