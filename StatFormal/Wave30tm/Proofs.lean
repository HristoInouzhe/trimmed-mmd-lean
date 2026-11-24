import StatFormal.Wave30tm.Route
import StatFormal.Wave30tm.RouteDensity

set_option linter.style.longLine false

/-!
# Proofs: wave 30tm, trimmed MMD (JMLR) `thm:impossible` with the uniform density bound 2 (untrusted proof file)

Route: `Wave30tm/RouteCells.lean` (two cells per block, `P_σ`, `Q_σ` uniform on complementary halves, density `2`,
`TV = 1`), `RouteMixture.lean` (the uniform mixture over `σ` has density `1` w.r.t. `P_u^{n+m}` off collisions;
collision mass `≤ (n+m)²/K`), `Route.lean` (assembly, `K → ∞`; the implication to the long version's claim) and
`RouteDensity.lean` (the encoding check `density2_iff`).
-/

namespace StatFormal.Wave30tm

theorem impossible : Claims.impossible := impossible_route

theorem density2_iff : Claims.density2_iff := density2_iff_route

theorem impossible_implies_archived : Claims.impossible_implies_archived :=
  impossible_implies_archived_route

example : Claims.impossible := impossible
example : Claims.density2_iff := density2_iff
example : Claims.impossible_implies_archived := impossible_implies_archived

end StatFormal.Wave30tm
