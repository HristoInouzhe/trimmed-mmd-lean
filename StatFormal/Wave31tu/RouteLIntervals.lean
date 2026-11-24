import StatFormal.Wave31tu.Statements
import StatFormal.Lib.IntervalDev.Intervals
import StatFormal.Lib.IntervalDev.Distinct

set_option linter.style.longLine false

/-!
# Wave31tu, chunk L: relative deviations for intervals (Y4, `lap_intervals`, Lemma S4.23)

* (a) the library theorem `StatFormal.IntervalDev.exists_interval_event` (probability integral transform, the
  `2(n+1)²` one-sided Bernstein events on the grid `F⁻¹[k/n, l/n]`, `F⁻¹(k/n, l/n)`, union bound, deterministic
  sandwich) at `L = log(2(n+1)²/η′)`, so that `2(n+1)²e^{−L} = η′`; the empirical frequency is the empirical law's
  value (`empirical_real_eq_sampleMean`) and `c_x = 2x + 4`;
* (b) the right-hand side of the event increases in `x` (`intervalEvent_mono`);
* (c) `StatFormal.IntervalDev.prod_pi_not_distinct_null` (independence of the coordinates, Fubini, atomlessness).
No hypothesis.
-/

noncomputable section
open MeasureTheory Set

namespace StatFormal.Wave31tu.RouteL

open StatFormal.TrimmedMMD.Concentration StatFormal.Wave30tp

/-- The empirical law of a sample charges a measurable set with its empirical frequency. -/
theorem empirical_real_eq_sampleMean {n : ℕ} (x : Fin n → ℝ) {I : Set ℝ} (hI : MeasurableSet I) :
    (empirical x).real I = StatFormal.Bernstein.sampleMean (I.indicator 1) x := by
  have h : ∀ i, (ENNReal.ofReal (1 / n) • Measure.dirac (x i)) I =
      ENNReal.ofReal (1 / n * I.indicator (1 : ℝ → ℝ) (x i)) := by
    intro i
    rw [Measure.smul_apply, Measure.dirac_apply' _ hI, smul_eq_mul]
    by_cases hxi : x i ∈ I <;> simp [hxi]
  simp only [measureReal_def, empirical, Measure.coe_finsetSum, Finset.sum_apply, h]
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => by
      have : 0 ≤ I.indicator (1 : ℝ → ℝ) (x i) := indicator_nonneg (fun _ _ => zero_le_one) _
      positivity,
    ENNReal.toReal_ofReal (Finset.sum_nonneg fun i _ => by
      have : 0 ≤ I.indicator (1 : ℝ → ℝ) (x i) := indicator_nonneg (fun _ _ => zero_le_one) _
      positivity)]
  rw [StatFormal.Bernstein.sampleMean, ← Finset.mul_sum, one_div, inv_mul_eq_div]

/-- The interval events weaken as the parameter grows. -/
theorem intervalEvent_mono (P : Measure ℝ) {n : ℕ} (x : Fin n → ℝ) {c c' : ℝ} (hcc : c ≤ c')
    (h : IntervalEvent P x c) : IntervalEvent P x c' := by
  intro I hI
  refine (h I hI).trans (add_le_add (Real.sqrt_le_sqrt ?_) ?_)
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    exact mul_le_mul_of_nonneg_left hcc (mul_nonneg zero_le_two measureReal_nonneg)
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    unfold cx; linarith

/-- Y4 `lap_intervals` (Lemma S4.23, S4 :1188-1205; (b) S4 :1351-1352; (c) S4 :1088-1089). -/
theorem lap_intervals_route : Claims.lap_intervals := by
  refine ⟨?_, fun P n x c c' _ hcc h => intervalEvent_mono P x hcc h, ?_⟩
  · intro P _ _ n η' hn hη0 hη1
    have hn0 : 0 < n := hn
    have hN : (0 : ℝ) < 2 * ((n : ℝ) + 1) ^ 2 := by positivity
    have hy : 1 < 2 * ((n : ℝ) + 1) ^ 2 / η' := by
      rw [one_lt_div hη0]
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    set L := Real.log (2 * ((n : ℝ) + 1) ^ 2 / η') with hL
    have hL0 : 0 ≤ L := (Real.log_pos hy).le
    obtain ⟨E, hEm, hEc, hEdev⟩ := StatFormal.IntervalDev.exists_interval_event P hn0 hL0
    have hexp : 2 * ((n : ℝ) + 1) ^ 2 * Real.exp (-L) = η' := by
      rw [Real.exp_neg, hL, Real.exp_log (by positivity)]
      field_simp
    rw [hexp] at hEc
    refine ⟨E, hEm, ?_, fun ω hω I hI => ?_⟩
    · have hcompl := measureReal_compl (μ := Measure.pi fun _ : Fin n => P) hEm
      rw [probReal_univ] at hcompl
      rw [← ofReal_measureReal]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    · have := hEdev ω hω I hI
      rw [empirical_real_eq_sampleMean ω hI.measurableSet]
      unfold cx
      exact this
  · intro P Q _ _ _ _ n m
    exact StatFormal.IntervalDev.prod_pi_not_distinct_null P Q n m

end StatFormal.Wave31tu.RouteL
