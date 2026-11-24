import StatFormal.Wave31tu.Statements
import StatFormal.Lib.IntervalDev.LocalDev

set_option linter.style.longLine false

/-!
# Wave31tu, chunk L: localized deviation (Y5, `lap_bv`, Lemma S4.24)

Route: the library theorem `StatFormal.IntervalDev.abs_setIntegral_sub_le_of_bv` (layer cake, the component count of
the upper level sets through Banach's indicatrix, Cauchy–Schwarz twice) with `μ = P`, `ν = P̃` the empirical law,
`α = 2x/n`, `β = c_x/n`; the interval event `IntervalEvent P x c` is its hypothesis on intervals.
No hypothesis: Y1(a) and Y2 enter through their library forms (`Indicatrix.lintegral_bcount_le`,
`Indicatrix.integral_eq_intervalIntegral_meas_lt`).
-/

noncomputable section
open MeasureTheory Set

namespace StatFormal.Wave31tu.RouteL

open StatFormal.TrimmedMMD.Concentration

/-- The empirical law of a sample is a finite measure. -/
theorem isFiniteMeasure_empirical {n : ℕ} (x : Fin n → ℝ) : IsFiniteMeasure (empirical x) := by
  constructor
  simp only [empirical, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  exact ENNReal.sum_lt_top.2 fun i _ => ENNReal.ofReal_lt_top

/-- Y5 `lap_bv` (Lemma S4.24, S4 :1207-1225). -/
theorem lap_bv_route : Claims.lap_bv := by
  intro P _ n x c hn hc hev I h V hI hIb h01 hcI hV hvar
  have := isFiniteMeasure_empirical x
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hβ : 0 ≤ cx c / n := div_nonneg (by unfold cx; linarith) hn0.le
  have hα : 0 ≤ 2 * c / n := div_nonneg (by linarith) hn0.le
  have hev' : ∀ C : Set ℝ, C.OrdConnected →
      |(empirical x).real C - P.real C| ≤ √(2 * c / n * P.real C) + cx c / n := by
    intro C hC
    have := hev C hC
    rwa [show 2 * P.real C * c / n = 2 * c / n * P.real C by ring] at this
  have key := StatFormal.IntervalDev.abs_setIntegral_sub_le_of_bv P (empirical x) hα hβ hev' hI hIb h01 hcI hV hvar
  have e1 : (V + 1) * (2 * c / n) * ∫ z in I, h z ∂P = 2 * (V + 1) * (∫ z in I, h z ∂P) * c / n := by ring
  have e2 : (V + 1) * (cx c / n) = (V + 1) * cx c / n := by ring
  rwa [e1, e2] at key

end StatFormal.Wave31tu.RouteL
