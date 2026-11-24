import StatFormal.Archive.Wave29i.Statements
import StatFormal.Archive.Wave29i.RouteEulln
import StatFormal.Archive.Wave29i.RouteSwor
import StatFormal.Archive.Wave29i.RouteCps
import StatFormal.Archive.Wave29i.RouteConsist
import StatFormal.Archive.Wave29i.RouteConsistCompare
import StatFormal.Archive.Wave29i.RouteSplit

/-! Critic checks (non-target): frozen + discharge ⇒ new, and a `splitAss` instance. -/

namespace StatFormal.Wave29i
-- Route checks (NOT targets): the discharges go through the frozen claims.
example : StatFormal.Wave28b.Claims.score_argmin_discharged → StatFormal.Wave11b.Claims.swor_value → eullnRisk :=
  eulln_risk_of
example : StatFormal.Wave24c.Claims.e_ulln → eullnRisk → Claims.eulln_discharged := eulln_discharged_of
example : StatFormal.Wave28f.Claims.score_hessian_ulln → StatFormal.WaveP1d.Claims.swor_derivs →
    Claims.swor_hessian := swor_hessian_of
example : StatFormal.Wave28f.Claims.score_linearization → StatFormal.WaveP1d.Claims.swor_derivs →
    Claims.swor_linear := swor_linear_of
example : StatFormal.Wave24d.Claims.icl_consistency → Claims.consist_reduction → Claims.consist_approx →
    Claims.consist_risk := consist_check
example : StatFormal.Wave22c.Claims.split_level → Claims.split_coverage → Claims.split_level_discharged :=
  split_check
-- Non-vacuity of the `ass:split` encoding.
example : splitAss (MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 1)) id (1/2) (1/2) := splitAss_uniform
end StatFormal.Wave29i
