import StatFormal.Wave31ta.RouteBang
import StatFormal.Wave31ta.RouteSmall
import StatFormal.Wave31ta.RouteSharp
import StatFormal.Wave31ta.RouteImpossible
import StatFormal.Wave31ta.RouteTrimrate

/-!
# Proofs: wave 31ta, trimmed-mmd (jmlr) v2 short (untrusted proof file)

Every claim of `StatFormal/Wave31ta/Statements.lean` is proved in a route file, as `theorem StatFormal.Wave31ta.<claim>`:
`RouteBang` (`bangbang_v2`, `tauV2Cpl_facts`), `RouteSmall` (`continuity_v2`, `distmax`, `uniform_event`, `cor_lower_v2`),
`RouteSharp` (`pinelis_h_form`, `sharp_le_plugin`, `sharp_cpl_counterexample`, `samplesize`), `RouteImpossible` (`impossible_two`),
`RouteTrimrate` (`quantile_of_QDensity`, `cor_trimrate_v2`). The gate checks `example : Claims.c := c` and the axioms.
-/

namespace StatFormal.Wave31ta

example : Claims.bangbang_v2 := bangbang_v2
example : Claims.continuity_v2 := continuity_v2
example : Claims.distmax := distmax
example : Claims.uniform_event := uniform_event
example : Claims.sharp_le_plugin := sharp_le_plugin
example : Claims.sharp_cpl_counterexample := sharp_cpl_counterexample
example : Claims.pinelis_h_form := pinelis_h_form
example : Claims.tauV2Cpl_facts := tauV2Cpl_facts
example : Claims.cor_lower_v2 := cor_lower_v2
example : Claims.impossible_two := impossible_two
example : Claims.quantile_of_QDensity := quantile_of_QDensity
example : Claims.cor_trimrate_v2 := cor_trimrate_v2
example : Claims.samplesize := samplesize

end StatFormal.Wave31ta
