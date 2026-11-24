import StatFormal.Wave31tu.Statements
import StatFormal.Lib.Indicatrix.BanachEq

set_option linter.style.longLine false

/-!
# Wave31tu, chunk L: Banach's indicatrix theorem (Y1)

* Y1(a) `banach_indicatrix_le`: measurability of `levelCount h a b` and `∫⁻ levelCount ≤ V_{[a,b]}(h)`, from the
  library `StatFormal.Indicatrix.measurable_bcount`, `StatFormal.Indicatrix.lintegral_bcount_le` (dyadic counting
  functions and Fatou's lemma). The frozen `levelCount` and the library `bcount` are the same expression.
* Y1(b) `banach_indicatrix`: the equality, `StatFormal.Indicatrix.lintegral_bcount_eq` (the reverse inequality by the
  intermediate value theorem on each gap of a partition: `Indicatrix.eVariationOn_le_lintegral_bcount`).
No hypotheses.
-/

namespace StatFormal.Wave31tu.RouteL

theorem levelCount_eq_bcount (h : ℝ → ℝ) (a b : ℝ) :
    levelCount h a b = StatFormal.Indicatrix.bcount h a b := rfl

/-- Y1(a) `banach_indicatrix_le` (S4 :1220-1222, the half used by `lem:lapbv`). -/
theorem banach_indicatrix_le_route : Claims.banach_indicatrix_le := by
  intro h a b hab hh
  rw [levelCount_eq_bcount]
  exact ⟨StatFormal.Indicatrix.measurable_bcount hab hh, StatFormal.Indicatrix.lintegral_bcount_le hab hh⟩

/-- Y1(b) `banach_indicatrix` (S4 :1220-1222, the printed equality). -/
theorem banach_indicatrix_route : Claims.banach_indicatrix := by
  intro h a b hab hh
  rw [levelCount_eq_bcount]
  exact StatFormal.Indicatrix.lintegral_bcount_eq hab hh

end StatFormal.Wave31tu.RouteL
