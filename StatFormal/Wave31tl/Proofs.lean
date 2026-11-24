import StatFormal.Wave31tl.Statements
import StatFormal.Wave31tl.RouteO

/-!
# Wave 31tl: proofs of the frozen claims (`thm:lorate` and the prose that rides on it)

Each theorem's type is literally the frozen `Claims.*` Prop of `StatFormal/Wave31tl/Statements.lean`; the routes are
`RouteBasic`, `RouteCore`, `RouteClaims`, `RouteArith`, `RouteO`.
-/

namespace StatFormal.Wave31tl

theorem lorate_i : Claims.lorate_i := lorate_i_route
theorem lorate_ii : Claims.lorate_ii := lorate_ii_route
theorem lorate_batches : Claims.lorate_batches := lorate_batches_route
theorem lorate_iii : Claims.lorate_iii := lorate_iii_route
theorem lorate_O : Claims.lorate_O := lorate_O_route
theorem same_rate : Claims.same_rate := same_rate_route
theorem lorate_nologJ : Claims.lorate_nologJ := lorate_nologJ_route
theorem lorate_general : Claims.lorate_general := lorate_general_route

example : Claims.lorate_i := lorate_i
example : Claims.lorate_ii := lorate_ii
example : Claims.lorate_batches := lorate_batches
example : Claims.lorate_iii := lorate_iii
example : Claims.lorate_O := lorate_O
example : Claims.same_rate := same_rate
example : Claims.lorate_nologJ := lorate_nologJ
example : Claims.lorate_general := lorate_general

end StatFormal.Wave31tl
