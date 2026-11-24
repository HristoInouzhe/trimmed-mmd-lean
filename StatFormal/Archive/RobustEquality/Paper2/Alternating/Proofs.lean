import StatFormal.Archive.RobustEquality.Paper2.Alternating.Statements
import StatFormal.Archive.RobustEquality.Paper2.Alternating.RouteVertex
import StatFormal.Archive.RobustEquality.Paper2.Alternating.RouteW2
import StatFormal.Archive.RobustEquality.Paper2.Alternating.RouteAlternating

/-!
# Proofs: paper 2 `lem:delta-inf` (finite centres) and `thm:alternating` (corrected, with the
DEFECTS #16 counterexample and the attainment repair)

The frozen definitions are verbatim copies of the route definitions (namespace
`…Alternating.Route`), so each route theorem proves its claim by definitional unfolding.
-/

namespace StatFormal.RobustEquality.Paper2.Alternating

theorem delta_inf_W2 : Claims.delta_inf_W2 := Route.delta_inf_W2

theorem delta_inf_vertex : Claims.delta_inf_vertex := Route.delta_inf_vertex

theorem delta_inf_linear : Claims.delta_inf_linear := Route.delta_inf_linear

theorem alternating : Claims.alternating := Route.alternating

theorem alternating_counterexample : Claims.alternating_counterexample :=
  Route.alternating_counterexample

theorem alternating_attainment : Claims.alternating_attainment := Route.alternating_attainment

end StatFormal.RobustEquality.Paper2.Alternating
