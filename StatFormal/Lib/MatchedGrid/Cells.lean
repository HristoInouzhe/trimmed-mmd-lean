import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Equal cells of an interval

* `restrict_Ioc_eq_sum`: `μ|_(c₀, cₙ] = Σ_{l<n} μ|_(c_l, c_{l+1}]` for a monotone `c`;
* `lintegral_Ioc_sq_mid`: `∫_{(a, a+h]} (a + h/2 − t)² dt = h³/12`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StatFormal.Foundations.MatchedGrid

lemma restrict_Ioc_eq_sum (μ : Measure ℝ) (c : ℕ → ℝ) (hc : Monotone c) (n : ℕ) :
    μ.restrict (Ioc (c 0) (c n)) = ∑ l ∈ Finset.range n, μ.restrict (Ioc (c l) (c (l + 1))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, ← Measure.restrict_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc,
      Ioc_union_Ioc_eq_Ioc (hc (Nat.zero_le n)) (hc (Nat.le_succ n))]

lemma integral_sq_mid (a h : ℝ) : ∫ t in a..a + h, (a + h / 2 - t) ^ 2 = h ^ 3 / 12 := by
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ 2), integral_pow]
  ring

lemma lintegral_Ioc_sq_mid (a : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    ∫⁻ t in Ioc a (a + h), ENNReal.ofReal ((a + h / 2 - t) ^ 2) = ENNReal.ofReal (h ^ 3 / 12) := by
  have hcont : Continuous fun t : ℝ => (a + h / 2 - t) ^ 2 := by fun_prop
  rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (Filter.Eventually.of_forall fun t => sq_nonneg _), ← intervalIntegral.integral_of_le (by linarith),
    integral_sq_mid]

end StatFormal.Foundations.MatchedGrid
