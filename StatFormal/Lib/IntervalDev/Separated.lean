import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.LinearCombination

set_option linter.style.longLine false

/-!
# Deviations on unions of few intervals

Let `μ, ν` be finite measures on `ℝ` whose deviation on every interval (order-connected set) `C` is bounded as
`|ν(C) − μ(C)| ≤ √(α μ(C)) + β`. If a set `A ⊆ I` (`I` an interval) is *separated by a finite set `Z`*, in the
sense that between any two points of `I` of which exactly one is in `A` there is a point of `Z`, then `A` is a
disjoint union of at most `|Z| + 1` intervals and, by Cauchy–Schwarz,
`|ν(A) − μ(A)| ≤ √((|Z|+1) α μ(A)) + (|Z|+1) β`.

This is the component count of `lem:lapbv` (trimmed-mmd S4, Lemma S4.24): the upper level set
`{z ∈ I : h z > s}` of a function continuous on `I` is separated by the level set `{h = s}` (intermediate value
theorem), so it has at most `N(s) + 1` components.

## Main results

* `sqrt_mul_add_sqrt_le`: `√(k u) + √v ≤ √((k+1)(u+v))` for `k ≥ 1`, `u, v ≥ 0` (Cauchy–Schwarz);
* `abs_measureReal_sub_le_of_separated`: the deviation bound on a separated set (induction on `Z` by its maximum).
-/

noncomputable section
open MeasureTheory Set

namespace StatFormal.IntervalDev

/-- Cauchy–Schwarz for two terms with weights `k` and `1`: `√(k u) + √v ≤ √((k + 1)(u + v))`. -/
theorem sqrt_mul_add_sqrt_le {k u v : ℝ} (hk : 1 ≤ k) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    √(k * u) + √v ≤ √((k + 1) * (u + v)) := by
  have hk0 : 0 ≤ k := by linarith
  rw [Real.le_sqrt (by positivity) (by positivity)]
  have hp : √(k * u) ^ 2 = k * u := Real.sq_sqrt (by positivity)
  have hq : √v ^ 2 = v := Real.sq_sqrt hv
  have hp0 := Real.sqrt_nonneg (k * u)
  have hq0 := Real.sqrt_nonneg v
  have e : k * (k * v + u) - k * (2 * √(k * u) * √v) = (k * √v - √(k * u)) ^ 2 := by
    linear_combination (-k ^ 2) * hq + (-1) * hp
  have h3 : k * (2 * √(k * u) * √v) ≤ k * (k * v + u) := by
    nlinarith [sq_nonneg (k * √v - √(k * u))]
  have h4 : 2 * √(k * u) * √v ≤ k * v + u := le_of_mul_le_mul_left h3 (by linarith)
  nlinarith

/-- **Deviation on a separated set.** If every interval `C` has `|ν(C) − μ(C)| ≤ √(α μ(C)) + β`, `I` is an interval,
`A ⊆ I`, and any two points `x < y` of `I` of which exactly one lies in `A` have a point of the finite set `Z` in
`[x, y]`, then `|ν(A) − μ(A)| ≤ √((|Z|+1) α μ(A)) + (|Z|+1) β`. -/
theorem abs_measureReal_sub_le_of_separated (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {α β : ℝ} (hα : 0 ≤ α)
    (hev : ∀ C : Set ℝ, C.OrdConnected → |ν.real C - μ.real C| ≤ √(α * μ.real C) + β)
    (Z : Finset ℝ) :
    ∀ I A : Set ℝ, I.OrdConnected → A ⊆ I →
      (∀ x ∈ I, ∀ y ∈ I, x < y → (x ∈ A ↔ y ∉ A) → ∃ z ∈ Z, x ≤ z ∧ z ≤ y) →
      |ν.real A - μ.real A| ≤ √((Z.card + 1) * α * μ.real A) + (Z.card + 1) * β := by
  classical
  induction Z using Finset.induction_on_max with
  | empty =>
    intro I A hI hAI hsep
    have hA : A.OrdConnected := by
      refine ⟨fun x hx y hy w hw => ?_⟩
      by_contra hwA
      rcases eq_or_lt_of_le hw.2 with hwy | hwy
      · exact hwA (hwy ▸ hy)
      · obtain ⟨z, hz, -⟩ := hsep w (hI.out (hAI hx) (hAI hy) hw) y (hAI hy) hwy
          (by simp [hwA, hy])
        simp at hz
    simpa using hev A hA
  | insert m Z' hlt ih =>
    intro I A hI hAI hsep
    have hm : m ∉ Z' := fun h => lt_irrefl m (hlt m h)
    rw [Finset.card_insert_of_notMem hm]
    have hA₂ : (A ∩ Ici m).OrdConnected := by
      refine ⟨fun x hx y hy w hw => ?_⟩
      refine ⟨?_, hx.2.trans hw.1⟩
      by_contra hwA
      rcases eq_or_lt_of_le hw.1 with hxw | hxw
      · exact hwA (hxw ▸ hx.1)
      rcases eq_or_lt_of_le hw.2 with hwy | hwy
      · exact hwA (hwy ▸ hy.1)
      obtain ⟨z, hz, hwz, -⟩ := hsep w (hI.out (hAI hx.1) (hAI hy.1) hw) y (hAI hy.1) hwy
        (by simp [hwA, hy.1])
      have hmz : m < z := lt_of_le_of_lt hx.2 (hxw.trans_le hwz)
      rcases Finset.mem_insert.1 hz with rfl | hz'
      · exact lt_irrefl _ hmz
      · exact lt_asymm (hlt z hz') hmz
    have hsep₁ : ∀ x ∈ I ∩ Iio m, ∀ y ∈ I ∩ Iio m, x < y → (x ∈ A ∩ Iio m ↔ y ∉ A ∩ Iio m) →
        ∃ z ∈ Z', x ≤ z ∧ z ≤ y := by
      intro x hx y hy hxy hxor
      have hxor' : x ∈ A ↔ y ∉ A := by
        simpa [mem_inter_iff, hx.2, hy.2] using hxor
      obtain ⟨z, hz, hxz, hzy⟩ := hsep x hx.1 y hy.1 hxy hxor'
      rcases Finset.mem_insert.1 hz with rfl | hz'
      · exact absurd hy.2 (not_lt.2 hzy)
      · exact ⟨z, hz', hxz, hzy⟩
    have h1 := ih (I ∩ Iio m) (A ∩ Iio m) (hI.inter ordConnected_Iio)
      (inter_subset_inter_left _ hAI) hsep₁
    have h2 := hev (A ∩ Ici m) hA₂
    have hdisj : Disjoint (A ∩ Iio m) (A ∩ Ici m) :=
      disjoint_left.2 fun x hx1 hx2 => (not_le.2 (mem_Iio.1 hx1.2)) (mem_Ici.1 hx2.2)
    have hU : A = (A ∩ Iio m) ∪ (A ∩ Ici m) := by
      rw [← inter_union_distrib_left, Iio_union_Ici, inter_univ]
    have hμ : μ.real A = μ.real (A ∩ Iio m) + μ.real (A ∩ Ici m) := by
      have := measureReal_union (μ := μ) hdisj hA₂.measurableSet
      rwa [← hU] at this
    have hν : ν.real A = ν.real (A ∩ Iio m) + ν.real (A ∩ Ici m) := by
      have := measureReal_union (μ := ν) hdisj hA₂.measurableSet
      rwa [← hU] at this
    set u := α * μ.real (A ∩ Iio m)
    set v := α * μ.real (A ∩ Ici m)
    have hu : 0 ≤ u := mul_nonneg hα measureReal_nonneg
    have hv : 0 ≤ v := mul_nonneg hα measureReal_nonneg
    have hk : (1 : ℝ) ≤ (Z'.card : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) Z'.card; linarith
    have hcs := sqrt_mul_add_sqrt_le hk hu hv
    have e1 : ((Z'.card : ℝ) + 1) * α * μ.real (A ∩ Iio m) = ((Z'.card : ℝ) + 1) * u := by ring
    have e2 : (((Z'.card + 1 : ℕ) : ℝ) + 1) * α * μ.real A = ((Z'.card : ℝ) + 1 + 1) * (u + v) := by
      rw [hμ]; push_cast; ring
    rw [e1] at h1
    rw [e2, hμ, hν]
    calc |ν.real (A ∩ Iio m) + ν.real (A ∩ Ici m) - (μ.real (A ∩ Iio m) + μ.real (A ∩ Ici m))|
        = |(ν.real (A ∩ Iio m) - μ.real (A ∩ Iio m)) + (ν.real (A ∩ Ici m) - μ.real (A ∩ Ici m))| := by
          ring_nf
      _ ≤ |ν.real (A ∩ Iio m) - μ.real (A ∩ Iio m)| + |ν.real (A ∩ Ici m) - μ.real (A ∩ Ici m)| :=
          abs_add_le _ _
      _ ≤ (√(((Z'.card : ℝ) + 1) * u) + ((Z'.card : ℝ) + 1) * β) + (√v + β) := add_le_add h1 h2
      _ ≤ √(((Z'.card : ℝ) + 1 + 1) * (u + v)) + (((Z'.card + 1 : ℕ) : ℝ) + 1) * β := by
          push_cast; linarith

end StatFormal.IntervalDev
