import StatFormal.Wave31tm.Statements
import StatFormal.Wave31tm.RouteAlphalo

/-!
# Wave 31tm: proof of the frozen claim (`cor:alphalo`)

The theorem's type is literally the frozen `Claims.alphalo` of `StatFormal/Wave31tm/Statements.lean`; the route is `RouteAlphalo`.
-/

namespace StatFormal.Wave31tm

theorem alphalo : Claims.alphalo := alphalo_route

example : Claims.alphalo := alphalo

end StatFormal.Wave31tm
