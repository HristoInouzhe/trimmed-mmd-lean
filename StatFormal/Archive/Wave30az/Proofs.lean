import StatFormal.Archive.Wave30az.Statements
import StatFormal.Archive.Wave30az.RouteDecay
import StatFormal.Archive.Wave30az.RouteICL
import StatFormal.Archive.Wave30az.RouteNPMLE
import StatFormal.Archive.Wave30az.RouteNPMLELin
import StatFormal.Archive.Wave30az.RouteNPMLEStrong
import StatFormal.Archive.Wave30az.RouteQuantiles
import StatFormal.Archive.Wave30az.RouteRandPenalty
import StatFormal.Archive.Wave30az.RouteTrimmed
import StatFormal.Archive.Wave30az.RouteWitness

namespace StatFormal.Wave30az
example : Claims.cond_osc_iid := cond_osc_iid
example : Claims.cond_metric_fixed := cond_metric_fixed
example : Claims.cond_metric_norm := cond_metric_norm
example : Claims.cond_metric_ball := cond_metric_ball
example : Claims.decay_ge_W2 := decay_ge_W2
example : Claims.decay_equal_groups := decay_equal_groups
example : Claims.decay_eq_refuted := decay_eq_refuted
example : Claims.randpenalty_printed_one := randpenalty_printed_one
example : Claims.randpenalty_printed_trace := randpenalty_printed_trace
example : Claims.quantiles_zero_printed := quantiles_zero_printed
example : Claims.quantiles_printed_refuted := quantiles_printed_refuted
example : Claims.quantiles_closed := quantiles_closed
example : Claims.npmle_gen_duality := npmle_gen_duality
example : Claims.npmle_gen_strong := npmle_gen_strong
example : Claims.npmle_weak := npmle_weak
example : Claims.npmle_attain_refuted := npmle_attain_refuted
example : Claims.npmle_gen_convex := npmle_gen_convex
example : Claims.npmle_gen_correction := npmle_gen_correction
example : Claims.npmle_gen_programme := npmle_gen_programme
example : Claims.trimmedmean_min := trimmedmean_min
example : Claims.trimmedmean_suff := trimmedmean_suff
example : Claims.trimmedmean_unique := trimmedmean_unique
example : Claims.witnessstab_gen := witnessstab_gen
example : Claims.witnessstab_rate := witnessstab_rate
end StatFormal.Wave30az
