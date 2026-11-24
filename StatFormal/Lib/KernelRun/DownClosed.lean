import StatFormal.Archive.TrimmedMMD.Lower.RouteLower

/-!
# The down-closed bound on sub-grids, and the larger of two lower bounds (library)

Library component (untrusted). For the down-closed bound `α̂_lo = max{α_j : every level i ≤ j rejected}` (`0` if none,
`TrimmedMMD.Lower.alphaLo`):

* `alphaLo_nonneg`: on nonnegative levels, `α̂_lo ≥ 0`;
* `alphaLo_castLE_le`: the bound read on an initial segment `α_1, …, α_J` of the grid `α_1, …, α_{J'}` (`J ≤ J'`, same rejections)
  is at most the bound of the whole grid (an index whose prefix is rejected in the segment has its prefix rejected in the grid);
* `measure_lt_max_le`: if `μ(a < A) ≤ δ` and `μ(a < B) ≤ δ`, then `μ(a < max(A, B)) ≤ 2δ` (`{a < max(A,B)} = {a < A} ∪ {a < B}`
  and subadditivity of the outer measure; no measurability needed).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Finset
open scoped ENNReal

namespace StatFormal.KernelRun

open StatFormal.TrimmedMMD.Lower

/-- On nonnegative levels the down-closed bound is nonnegative. -/
theorem alphaLo_nonneg {J : ℕ} (α : Fin J → ℝ) (rej : Fin J → Prop) (hα : ∀ j, 0 ≤ α j) : 0 ≤ alphaLo α rej := by
  classical
  unfold alphaLo
  split_ifs with h
  · obtain ⟨j, hj⟩ := h
    exact (hα j).trans (Finset.le_sup' α hj)
  · exact le_rfl

/-- **The bound read on an initial segment of the grid is at most the bound of the whole grid** (levels `≥ 0`). -/
theorem alphaLo_castLE_le {J J' : ℕ} (h : J ≤ J') (α : Fin J' → ℝ) (rej : Fin J' → Prop) (hα : ∀ j, 0 ≤ α j) :
    alphaLo (fun j : Fin J => α (Fin.castLE h j)) (fun j => rej (Fin.castLE h j)) ≤ alphaLo α rej := by
  classical
  have hlift : ∀ j : Fin J, (∀ i ≤ j, rej (Fin.castLE h i)) → ∀ i' ≤ Fin.castLE h j, rej i' := by
    intro j hj i' hi'
    have hi'J : (i' : ℕ) < J := lt_of_le_of_lt (Fin.le_iff_val_le_val.mp hi') (by simp)
    have := hj ⟨i', hi'J⟩ (Fin.le_iff_val_le_val.mpr (by simpa using Fin.le_iff_val_le_val.mp hi'))
    have e : Fin.castLE h ⟨(i' : ℕ), hi'J⟩ = i' := Fin.ext rfl
    rwa [e] at this
  conv_lhs => unfold alphaLo
  split_ifs with h1
  · refine Finset.sup'_le h1 _ fun j hj => ?_
    have hj' := (Finset.mem_filter.mp hj).2
    have hmem : Fin.castLE h j ∈ univ.filter fun j : Fin J' => ∀ i ≤ j, rej i :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlift j hj'⟩
    have hne : (univ.filter fun j : Fin J' => ∀ i ≤ j, rej i).Nonempty := ⟨_, hmem⟩
    unfold alphaLo
    rw [dite_eq_left_of_eq_true (eq_true hne)]
    exact Finset.le_sup' α hmem
  · exact alphaLo_nonneg α rej hα

/-- **The larger of two `δ`-level lower bounds is a `2δ`-level lower bound** (any measure, any functions). -/
theorem measure_lt_max_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A B : Ω → ℝ) (a δ : ℝ)
    (hA : μ {ω | a < A ω} ≤ ENNReal.ofReal δ) (hB : μ {ω | a < B ω} ≤ ENNReal.ofReal δ) :
    μ {ω | a < max (A ω) (B ω)} ≤ ENNReal.ofReal (2 * δ) := by
  have hsub : {ω | a < max (A ω) (B ω)} = {ω | a < A ω} ∪ {ω | a < B ω} := by
    ext ω; simp only [mem_ofPred_eq, mem_union, lt_max_iff]
  rw [hsub]
  refine (measure_union_le _ _).trans ((add_le_add hA hB).trans ?_)
  rcases le_or_gt 0 δ with hδ | hδ
  · rw [← ENNReal.ofReal_add hδ hδ, two_mul]
  · rw [ENNReal.ofReal_of_nonpos hδ.le, zero_add]
    exact zero_le

end StatFormal.KernelRun
