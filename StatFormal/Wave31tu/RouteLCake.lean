import StatFormal.Wave31tu.Statements
import StatFormal.Lib.Indicatrix.LayerCake

set_option linter.style.longLine false

/-!
# Wave31tu, chunk L: the layer cake on `[0,1]` (Y2, `layer_cake01`)

Route: the library wrapper `StatFormal.Indicatrix.integral_eq_intervalIntegral_meas_lt` of Mathlib's
`Integrable.integral_eq_integral_meas_lt`.
-/

namespace StatFormal.Wave31tu.RouteL

/-- Y2 `layer_cake01` (S4 :1218-1219). -/
theorem layer_cake01_route : Claims.layer_cake01 := by
  intro 𝒳 _ μ _ h hm h01
  exact StatFormal.Indicatrix.integral_eq_intervalIntegral_meas_lt μ hm (fun x => (h01 x).1)
    (fun x => (h01 x).2)

end StatFormal.Wave31tu.RouteL
