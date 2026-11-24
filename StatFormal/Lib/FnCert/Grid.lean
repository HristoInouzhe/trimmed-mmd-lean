import StatFormal.Wave31tl.Statements
import StatFormal.Archive.TrimmedMMD.Lower.Statements
import Mathlib.Probability.Notation

set_option linter.style.longLine false

/-!
# The down-closed reading of a grid, the grid floor, and complements of large events (library)

Library component (untrusted). For a grid `α : Fin J → ℝ` and rejection indicators `rej`, `TrimmedMMD.Lower.alphaLo α rej` is
`max{α_j : rej i for every i ≤ j}` (`0` if `rej 0` fails), `eq:downclosed`:

* `alphaLo_le_of_forall`: if every rejected level is `< t` and `t ≥ 0`, then `α̂ ≤ t`;
* `le_alphaLo_of_forall`: if every `i ≤ j` is rejected, `α_j ≤ α̂`; `alphaLo_nonneg'`: `α̂ ≥ 0` for a nonnegative grid;
* `forall_le_of_alphaLo_eq`: for a strictly increasing nonnegative grid, `α̂ = α_j` with `rej j` forces `rej i` for every `i ≤ j`
  ("`H_{0,α̂}` is rejected" means a down-closed run of rejections up to `α̂`);
* `exists_eq_gridFloor`: a positive grid floor `gridFloor α x` (`Wave31tl`) is a grid level `α_j ≤ x`;
* `measure_compl_le_of_ge`: `P(E) ≥ 1 − δ` gives `P(Eᶜ) ≤ δ` for a measurable `E` under a probability measure.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.FnCert

open StatFormal.TrimmedMMD.Lower

variable {J : ℕ}

/-- If every rejected level lies below `t ≥ 0`, the down-closed reading is at most `t`. -/
theorem alphaLo_le_of_forall {α : Fin J → ℝ} {rej : Fin J → Prop} {t : ℝ} (ht : 0 ≤ t) (h : ∀ j, rej j → α j < t) :
    alphaLo α rej ≤ t := by
  classical
  unfold alphaLo
  split_ifs with hne
  · exact Finset.sup'_le _ _ fun j hj => (h j ((Finset.mem_filter.1 hj).2 j le_rfl)).le
  · exact ht

/-- If every level `i ≤ j` is rejected, `α_j ≤ α̂`. -/
theorem le_alphaLo_of_forall (α : Fin J → ℝ) {rej : Fin J → Prop} (j : Fin J) (h : ∀ i ≤ j, rej i) :
    α j ≤ alphaLo α rej := by
  classical
  unfold alphaLo
  split_ifs with hF
  · exact Finset.le_sup' α (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  · exact absurd ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩⟩ hF

/-- `α̂ ≥ 0` for a nonnegative grid. -/
theorem alphaLo_nonneg' {α : Fin J → ℝ} (hα : ∀ j, 0 ≤ α j) (rej : Fin J → Prop) : 0 ≤ alphaLo α rej := by
  classical
  unfold alphaLo
  split_ifs with h
  · obtain ⟨j, hj⟩ := h
    exact (hα j).trans (Finset.le_sup' α hj)
  · exact le_rfl

/-- For a strictly increasing nonnegative grid, `α̂ = α_j` together with the rejection of `H_{0,α_j}` forces the rejection of every
`H_{0,α_i}`, `i ≤ j`. -/
theorem forall_le_of_alphaLo_eq {α : Fin J → ℝ} (hmono : StrictMono α) (hα : ∀ j, 0 ≤ α j) {rej : Fin J → Prop} {j : Fin J}
    (heq : alphaLo α rej = α j) (hrej : rej j) : ∀ i ≤ j, rej i := by
  classical
  unfold alphaLo at heq
  split_ifs at heq with hne
  · obtain ⟨j', hj', hj'eq⟩ := Finset.exists_mem_eq_sup' hne α
    rw [hj'eq] at heq
    have e : j' = j := hmono.injective heq
    rw [← e]
    exact (Finset.mem_filter.1 hj').2
  · intro i hi
    rcases lt_or_eq_of_le hi with hlt | rfl
    · have := hmono hlt
      linarith [hα i]
    · exact hrej

/-- A positive grid floor is attained at a grid level `α_j ≤ x`. -/
theorem exists_eq_gridFloor (α : Fin J → ℝ) {x : ℝ} (h : 0 < StatFormal.Wave31tl.gridFloor α x) :
    ∃ j, α j ≤ x ∧ StatFormal.Wave31tl.gridFloor α x = α j := by
  classical
  unfold StatFormal.Wave31tl.gridFloor at h ⊢
  split_ifs at h ⊢ with hne
  · obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup' hne α
    rw [hjeq] at h ⊢
    have hpos : 0 < α j := (lt_max_iff.1 h).resolve_left (lt_irrefl 0)
    exact ⟨j, (Finset.mem_filter.1 hj).2, max_eq_right hpos.le⟩
  · exact absurd h (lt_irrefl 0)

/-- Under a probability measure, `P(E) ≥ 1 − δ` for a measurable `E` gives `P(Eᶜ) ≤ δ`. -/
theorem measure_compl_le_of_ge {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {E : Set Ω}
    (hE : MeasurableSet E) {δ : ℝ} (hδ : 0 ≤ δ) (h : ENNReal.ofReal (1 - δ) ≤ μ E) : μ Eᶜ ≤ ENNReal.ofReal δ := by
  rw [prob_compl_eq_one_sub hE, tsub_le_iff_right]
  calc (1 : ℝ≥0∞) = ENNReal.ofReal (δ + (1 - δ)) := by rw [add_sub_cancel, ENNReal.ofReal_one]
    _ ≤ ENNReal.ofReal δ + ENNReal.ofReal (1 - δ) := ENNReal.ofReal_add_le
    _ ≤ ENNReal.ofReal δ + μ E := by gcongr

end StatFormal.FnCert
