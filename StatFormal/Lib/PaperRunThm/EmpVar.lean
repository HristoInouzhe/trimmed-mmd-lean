import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Algebra.Monoid

/-!
# The variance of a finite sample (library)

Library component (untrusted). For `v : Fin k → ℝ`, the population variance (divisor `k`, numpy's `var` with `ddof = 0`)
`V(v) = k⁻¹ Σ_i (v_i − v̄)²`, `v̄ = k⁻¹ Σ_l v_l`, written out (the frozen `Wave31tr.empVar` is this expression):

* `popVar_nonneg`: `V(v) ≥ 0`;
* `popVar_le_quarter`: `V(v) ≤ ¼` when every `v_i ∈ [0,1]` (Popoviciu's inequality for `[0,1]`: `Σ(v_i − v̄)² = Σv_i² − k v̄²
  ≤ Σv_i − k v̄² = k v̄(1 − v̄) ≤ k/4`, using `v_i² ≤ v_i`); for `k = 0` the expression is `0/0 = 0`;
* `measurable_popVar`: `v ↦ V(v)` is measurable (it is continuous).
-/

noncomputable section
open MeasureTheory

namespace StatFormal.PaperRunThm

/-- The population variance of a finite sample is nonnegative. -/
theorem popVar_nonneg {k : ℕ} (v : Fin k → ℝ) : 0 ≤ (∑ i, (v i - (∑ l, v l) / k) ^ 2) / k :=
  div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg k)

/-- Popoviciu's inequality on `[0,1]`: the population variance of a `[0,1]`-valued finite sample is at most `¼`. -/
theorem popVar_le_quarter {k : ℕ} (v : Fin k → ℝ) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) :
    (∑ i, (v i - (∑ l, v l) / k) ^ 2) / k ≤ 1 / 4 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set S := ∑ l, v l with hS
  have h1 : ∑ i, (v i - S / k) ^ 2 = ∑ i, v i ^ 2 - S ^ 2 / k := by
    have e : ∀ i, (v i - S / k) ^ 2 = v i ^ 2 - 2 * (S / k) * v i + (S / k) ^ 2 := fun i => by ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← hS]
    field_simp
    ring
  have h2 : ∑ i, v i ^ 2 ≤ S := Finset.sum_le_sum fun i _ => by nlinarith [hv i]
  rw [h1, div_le_iff₀ hk']
  have h3 : S - S ^ 2 / k ≤ 1 / 4 * k := by
    have hsq := sq_nonneg ((k : ℝ) - 2 * S)
    have : S - S ^ 2 / k = (4 * S * k - 4 * S ^ 2) / (4 * k) := by field_simp
    rw [this, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-- The population variance is a measurable (indeed continuous) function of the sample. -/
theorem measurable_popVar (k : ℕ) : Measurable fun v : Fin k → ℝ => (∑ i, (v i - (∑ l, v l) / k) ^ 2) / k := by
  have : Continuous fun v : Fin k → ℝ => (∑ i, (v i - (∑ l, v l) / k) ^ 2) / k := by fun_prop
  exact this.measurable

end StatFormal.PaperRunThm
