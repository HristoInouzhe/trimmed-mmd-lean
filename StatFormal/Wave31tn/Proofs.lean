import StatFormal.Wave31tn.Statements
import StatFormal.Wave31tn.RouteS1
import StatFormal.Wave31tn.RouteS2
import StatFormal.Wave31tn.RouteS4
import StatFormal.Wave31tn.RouteS3i
import StatFormal.Wave31tn.RouteS3ii
import StatFormal.Wave31tn.RouteS3iii

/-!
# Wave 31tn: proofs of the frozen claims (S1–S4 of the AoS version of 2026-11-20)

Each theorem's type is literally the frozen `Claims.*` Prop of `StatFormal/Wave31tn/Statements.lean`; the routes are `RouteTV`,
`RouteKL`, `RouteS1`, `RouteS2`, `RouteS4`, `RouteS3i`, `RouteS3ii`, `RouteS3iii`.
-/

namespace StatFormal.Wave31tn

theorem lower2pt_tv : Claims.lower2pt_tv := RouteS1.lower2pt_tv_route
theorem lower2pt : Claims.lower2pt := RouteS1.lower2pt_route
theorem lower2pt_c : Claims.lower2pt_c := RouteS1.lower2pt_c_route
theorem twopointmargin : Claims.twopointmargin := RouteS2.twopointmargin_route
theorem nouniformrate : Claims.nouniformrate := RouteS4.nouniformrate_route
theorem minimax_i : Claims.minimax_i := RouteS3i.minimax_i_route
theorem minimax_ii : Claims.minimax_ii := RouteS3ii.minimax_ii_route
theorem minimax_iii : Claims.minimax_iii := RouteS3iii.minimax_iii_route

example : Claims.lower2pt_tv := lower2pt_tv
example : Claims.lower2pt := lower2pt
example : Claims.lower2pt_c := lower2pt_c
example : Claims.twopointmargin := twopointmargin
example : Claims.nouniformrate := nouniformrate
example : Claims.minimax_i := minimax_i
example : Claims.minimax_ii := minimax_ii
example : Claims.minimax_iii := minimax_iii

end StatFormal.Wave31tn
