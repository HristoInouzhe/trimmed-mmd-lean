import StatFormal.Wave30tz.RouteOrder
import StatFormal.Wave30tz.RouteElem
import StatFormal.Wave30tz.RoutePop
import StatFormal.Wave30tz.RouteFit
import StatFormal.Wave30tz.RouteBet
import StatFormal.Wave30tz.RouteKS
import StatFormal.Wave30tz.RouteExample
import StatFormal.Wave30tz.RouteValid
import StatFormal.Wave30tz.RouteUpper
import StatFormal.Wave30tz.RouteLower
import StatFormal.Wave30tz.RouteLimits

/-!
# Wave 30tz: proofs of the frozen claims (consistency of the split-sample lower bound `α̂_lo`)

Each theorem's type is literally the frozen `Claims.*` Prop of `StatFormal/Wave30tz/Statements.lean`. The Proposition 1
claims are assembled from the intermediate statements of `RouteIface.lean` (`core_lower_bound`, `dpop_antitone`, proved in
`RouteLower.lean`) and the certified upper-side claims.
-/

namespace StatFormal.Wave30tz

theorem numpy_bracket : Claims.numpy_bracket := numpy_bracket_route
theorem exact_quantile_bracket : Claims.exact_quantile_bracket := exact_quantile_bracket_route
theorem fractions_bounds : Claims.fractions_bounds := fractions_bounds_route
theorem pop_ramp : Claims.pop_ramp := pop_ramp_route
theorem pop_ramp_freeze_false : Claims.pop_ramp_freeze_false := pop_ramp_freeze_false_route
theorem pop_ramp_rkhs : Claims.pop_ramp_rkhs := pop_ramp_rkhs_route
theorem ramp_tv : Claims.ramp_tv := ramp_tv_route
theorem crit_identity : Claims.crit_identity := crit_identity_route
theorem crit_emp : Claims.crit_emp := crit_emp_route
theorem crit_uniform : Claims.crit_uniform := crit_uniform_route
theorem quantile_bracket : Claims.quantile_bracket := quantile_bracket_route
theorem order_stat_shift : Claims.order_stat_shift := order_stat_shift_route
theorem fitted_ramp : Claims.fitted_ramp := fitted_ramp_route
theorem theta_mono : Claims.theta_mono := theta_mono_route
theorem log_lower : Claims.log_lower := log_lower_route
theorem bet_power : Claims.bet_power := bet_power_route
theorem bet_power_frac : Claims.bet_power_frac := bet_power_frac_route
theorem strict_null : Claims.strict_null := strict_null_route
theorem strict_null_frac : Claims.strict_null_frac := strict_null_frac_route
theorem grid_events : Claims.grid_events := grid_events_route
theorem mesh_point : Claims.mesh_point := mesh_point_route
theorem lo_upper : Claims.lo_upper := lo_upper_route
theorem lo_lower_bound : Claims.lo_lower_bound := lo_lower_bound_route
theorem lo_strict_bound : Claims.lo_strict_bound := lo_strict_bound_route
theorem lo_lower : Claims.lo_lower := lo_lower_of core_lower_bound
theorem lo_consistency : Claims.lo_consistency := lo_consistency_of core_lower_bound lo_upper lo_strict_bound
theorem lo_exact : Claims.lo_exact := lo_exact_of core_lower_bound lo_upper lo_strict_bound
theorem lo_vanishing : Claims.lo_vanishing := lo_vanishing_of core_lower_bound lo_upper
theorem lo_refining : Claims.lo_refining := lo_refining_of core_lower_bound dpop_antitone lo_strict_bound
theorem lo_refining_kernel : Claims.lo_refining_kernel :=
  lo_refining_kernel_of core_lower_bound dpop_antitone lo_strict_bound
theorem ramp_ks : Claims.ramp_ks := ramp_ks_route
theorem alpha0_example : Claims.alpha0_example := alpha0_example_route
theorem alpha0_valid : Claims.alpha0_valid := alpha0_valid_route

end StatFormal.Wave30tz
