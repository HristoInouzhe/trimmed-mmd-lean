import StatFormal.Wave30tn.RouteTrimLip
import StatFormal.Wave30tn.RouteSplitFS
import StatFormal.Wave30tn.RouteLower
import StatFormal.Wave30tn.RouteBootAny
import StatFormal.Wave30tn.RouteUnique
import StatFormal.Wave30tn.RoutePop

/-!
# Proofs: wave 30tn, trimmed MMD (JMLR) `prop:splitfs`, `eq:trimlip`, `cor:lower`, `thm:split` (restated clauses),
# `lem:unique`, `lem:popthreshold` (untrusted proof file)

Routes: `RouteTrimLip` (eq:trimlip, `L(F_n) = splitTrimLo`), `RouteSplitFS` (population identification, DKW–Massart,
prop:splitfs), `RouteLower` (cor:lower finite-sample and general regime; thm:split (i) under ass:split; `f̂ = 0`),
`RouteBootSeq` / `RouteBootAny` (thm:split (ii): the bootstrap CLT for arbitrary sizes), `RouteUnique` (lem:unique),
`RoutePop` (lem:popthreshold).
-/

namespace StatFormal.Wave30tn

theorem trimlip : Claims.trimlip := trimlip_route
theorem splitfs : Claims.splitfs := splitfs_route
theorem cor_lower_fs : Claims.cor_lower_fs := cor_lower_fs_route
theorem cor_lower_boot_any : Claims.cor_lower_boot_any := cor_lower_boot_any_route
theorem cor_lower_split_any : Claims.cor_lower_split_any := cor_lower_split_any_route
theorem split_normal_ass : Claims.split_normal_ass := split_normal_ass_route
theorem split_boot_ass : Claims.split_boot_ass := split_boot_ass_route
theorem split_zero_boot_any : Claims.split_zero_boot_any := split_zero_boot_any_route
theorem split_witness_zero : Claims.split_witness_zero := split_witness_zero_route
theorem unique_trim : Claims.unique_trim := unique_trim_route
theorem popthreshold : Claims.popthreshold := popthreshold_route

example : Claims.trimlip := trimlip
example : Claims.splitfs := splitfs
example : Claims.cor_lower_fs := cor_lower_fs
example : Claims.cor_lower_boot_any := cor_lower_boot_any
example : Claims.cor_lower_split_any := cor_lower_split_any
example : Claims.split_normal_ass := split_normal_ass
example : Claims.split_boot_ass := split_boot_ass
example : Claims.split_zero_boot_any := split_zero_boot_any
example : Claims.split_witness_zero := split_witness_zero
example : Claims.unique_trim := unique_trim
example : Claims.popthreshold := popthreshold

end StatFormal.Wave30tn
