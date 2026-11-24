import StatFormal.Lib.Indicatrix.Banach

set_option linter.style.longLine false

/-!
# Banach's indicatrix theorem: the equality

For `h : ℝ → ℝ` continuous on `[a,b]`, `∫⁻ #{x ∈ [a,b] : h x = s} ds = V_{[a,b]}(h)` (Banach 1925; Natanson,
*Theory of Functions of a Real Variable*, Ch. VIII §5). The inequality `≤` is `lintegral_bcount_le`
(`Banach.lean`); this file proves `≥`.

## Route

For a monotone sequence `t_0 ≤ t_1 ≤ … ≤ t_m` in `[a,b]` and a value `s` strictly between `h(t_j)` and `h(t_{j+1})`,
the intermediate value theorem gives a level point `x_j ∈ (t_j, t_{j+1})` with `h x_j = s` (it is neither endpoint,
as `h(t_j), h(t_{j+1}) ≠ s`); the open intervals `(t_j, t_{j+1})` are disjoint, so these points are distinct and
`N(s) ≥ Σ_j 1{s ∈ (h(t_j) ∧ h(t_{j+1}), h(t_j) ∨ h(t_{j+1}))}` (`sum_indicator_le_bcount`). Integrating in `s`,
`∫⁻ N ≥ Σ_j |h(t_{j+1}) − h(t_j)|`, and the supremum over partitions is the variation. No uniform continuity is
needed for this half.

## Main results

* `eVariationOn_le_lintegral_bcount`, `lintegral_bcount_eq` (Banach's indicatrix theorem).
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.Indicatrix

variable {a b : ℝ} {h : ℝ → ℝ}

/-- The open interval of values strictly between `h(u j)` and `h(u (j+1))`. -/
def valGap (h : ℝ → ℝ) (u : ℕ → ℝ) (j : ℕ) : Set ℝ :=
  Ioo (min (h (u j)) (h (u (j + 1)))) (max (h (u j)) (h (u (j + 1))))

/-- Each value strictly between `h(t_j)` and `h(t_{j+1})` is taken in the open interval `(t_j, t_{j+1})`. -/
theorem exists_level_point (hh : ContinuousOn h (Icc a b)) {u : ℕ → ℝ} (hu : Monotone u)
    (hus : ∀ i, u i ∈ Icc a b) {j : ℕ} {s : ℝ} (hs : s ∈ valGap h u j) :
    ∃ x, x ∈ Ioo (u j) (u (j + 1)) ∧ h x = s := by
  have hle : u j ≤ u (j + 1) := hu (Nat.le_succ j)
  have hc : ContinuousOn h (uIcc (u j) (u (j + 1))) := by
    rw [uIcc_of_le hle]; exact hh.mono (Icc_subset_Icc (hus j).1 (hus (j + 1)).2)
  obtain ⟨x, hx, hxs⟩ := intermediate_value_uIcc hc (Ioo_subset_Icc_self hs)
  rw [uIcc_of_le hle] at hx
  simp only [valGap, mem_Ioo, min_lt_iff, lt_max_iff] at hs
  refine ⟨x, ⟨lt_of_le_of_ne hx.1 ?_, lt_of_le_of_ne hx.2 ?_⟩, hxs⟩
  · rintro rfl
    rw [hxs] at hs
    rcases hs with ⟨h1 | h1, h2 | h2⟩ <;> linarith
  · rintro rfl
    rw [hxs] at hs
    rcases hs with ⟨h1 | h1, h2 | h2⟩ <;> linarith

/-- **Pointwise lower bound for the indicatrix**: the number of gaps `j < m` whose value interval contains `s` is at
most `N(s)`. -/
theorem sum_indicator_le_bcount (hh : ContinuousOn h (Icc a b)) {u : ℕ → ℝ} (hu : Monotone u)
    (hus : ∀ i, u i ∈ Icc a b) (m : ℕ) (s : ℝ) :
    ∑ j ∈ Finset.range m, (valGap h u j).indicator (1 : ℝ → ℝ≥0∞) s ≤ bcount h a b s := by
  classical
  set T := (Finset.range m).filter (fun j => s ∈ valGap h u j) with hT
  have hsum : ∑ j ∈ Finset.range m, (valGap h u j).indicator (1 : ℝ → ℝ≥0∞) s = (T.card : ℝ≥0∞) := by
    rw [hT, ← Finset.sum_boole]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : s ∈ valGap h u j
    · simp only [hj, ↓reduceIte, indicator_of_mem hj, Pi.one_apply]
    · simp only [hj, ↓reduceIte, indicator_of_notMem hj]
  have hex : ∀ j ∈ T, ∃ x, x ∈ Ioo (u j) (u (j + 1)) ∧ h x = s := fun j hj =>
    exists_level_point hh hu hus (Finset.mem_filter.1 hj).2
  choose! g hg using hex
  have hinj : InjOn g (T : Set ℕ) := by
    intro j hj j' hj' hjj
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h1 := (hg j hj).1.2
      have h2 := (hg j' hj').1.1
      have h3 : u (j + 1) ≤ u j' := hu hlt
      rw [hjj] at h1; linarith
    · have h1 := (hg j' hj').1.2
      have h2 := (hg j hj).1.1
      have h3 : u (j' + 1) ≤ u j := hu hlt
      rw [hjj] at h2; linarith
  have hsub : g '' (T : Set ℕ) ⊆ {x | x ∈ Icc a b ∧ h x = s} := by
    rintro _ ⟨j, hj, rfl⟩
    have hx := (hg j hj).1
    exact ⟨⟨(hus j).1.trans hx.1.le, hx.2.le.trans (hus (j + 1)).2⟩, (hg j hj).2⟩
  have hcard : (g '' (T : Set ℕ)).encard = T.card := by
    rw [hinj.encard_image, encard_coe_eq_coe_finsetCard]
  rw [hsum, bcount, ← ENat.toENNReal_coe, ← hcard]
  exact ENat.toENNReal_le.2 (encard_le_encard hsub)

/-- `∫⁻ N ≥ V_{[a,b]}(h)` for `h` continuous on `[a,b]`. -/
theorem eVariationOn_le_lintegral_bcount (hh : ContinuousOn h (Icc a b)) :
    eVariationOn h (Icc a b) ≤ ∫⁻ s, bcount h a b s := by
  unfold eVariationOn
  refine iSup_le fun ⟨m, u, hu, hus⟩ => ?_
  calc ∑ i ∈ Finset.range m, edist (h (u (i + 1))) (h (u i))
      = ∑ i ∈ Finset.range m, volume (valGap h u i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [valGap, Real.volume_Ioo, edist_dist, Real.dist_eq, max_sub_min_eq_abs, abs_sub_comm]
    _ = ∫⁻ s, ∑ i ∈ Finset.range m, (valGap h u i).indicator (1 : ℝ → ℝ≥0∞) s := by
        rw [lintegral_finsetSum (f := fun i s => (valGap h u i).indicator (1 : ℝ → ℝ≥0∞) s) _
          fun i _ => measurable_const.indicator measurableSet_Ioo]
        refine Finset.sum_congr rfl fun i _ => ?_
        exact (lintegral_indicator_one measurableSet_Ioo).symm
    _ ≤ ∫⁻ s, bcount h a b s := lintegral_mono fun s => sum_indicator_le_bcount hh hu hus m s

/-- **Banach's indicatrix theorem**: for `h` continuous on `[a,b]`, `∫⁻ #{x ∈ [a,b] : h x = s} ds = V_{[a,b]}(h)`. -/
theorem lintegral_bcount_eq (hab : a ≤ b) (hh : ContinuousOn h (Icc a b)) :
    ∫⁻ s, bcount h a b s = eVariationOn h (Icc a b) :=
  le_antisymm (lintegral_bcount_le hab hh) (eVariationOn_le_lintegral_bcount hh)

end StatFormal.Indicatrix
