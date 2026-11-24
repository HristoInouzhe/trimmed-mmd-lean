import StatFormal.Archive.Wave29i.Statements
import StatFormal.Archive.Wave29i.RouteChecks
import StatFormal.Archive.Wave29i.RouteConsist
import StatFormal.Archive.Wave29i.RouteConsistApprox
import StatFormal.Archive.Wave29i.RouteConsistBasic
import StatFormal.Archive.Wave29i.RouteConsistCompare
import StatFormal.Archive.Wave29i.RouteConsistPool
import StatFormal.Archive.Wave29i.RouteConsistReduction
import StatFormal.Archive.Wave29i.RouteCps
import StatFormal.Archive.Wave29i.RouteEulln
import StatFormal.Archive.Wave29i.RouteSplit
import StatFormal.Archive.Wave29i.RouteSwor

namespace StatFormal.Wave29i
example : Claims.eulln_discharged := eulln_discharged
example : Claims.swor_hessian := swor_hessian
example : Claims.swor_linear := swor_linear
example : Claims.cps_cov_fixed_prompt := cps_cov_fixed_prompt
example : Claims.cps_kl_gap_infinite := cps_kl_gap_infinite
example : Claims.consist_risk := consist_risk
example : Claims.consist_reduction := consist_reduction
example : Claims.consist_approx := consist_approx
example : Claims.consist_compare := consist_compare
example : Claims.split_pop_trimmed := split_pop_trimmed
example : Claims.split_ass_unique := split_ass_unique
example : Claims.split_asymp_normal := split_asymp_normal
example : Claims.split_coverage := split_coverage
example : Claims.split_level_boot := split_level_boot
example : Claims.split_level_discharged := split_level_discharged
end StatFormal.Wave29i
