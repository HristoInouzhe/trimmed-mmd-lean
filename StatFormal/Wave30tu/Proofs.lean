import StatFormal.Wave30tu.RouteMain
import StatFormal.Wave30tu.RouteConsistency
import StatFormal.Wave30tu.RouteRatecond
import StatFormal.Wave30tu.Instance.Route
import StatFormal.Wave30tu.Full.Route
import StatFormal.Wave30tu.Crossing.Route

namespace StatFormal.Wave30tu
example : Claims.oneevent := oneevent
example : Claims.threshold_min := threshold_min
example : Claims.upper_valid := upper_valid
example : Claims.alphaest_wellDefined := alphaest_wellDefined
example : Claims.tauRight_spec := tauRight_spec
example : Claims.crossing := crossing
example : Claims.crossing_meas := crossing_meas
example : Claims.grid_mesh := grid_mesh
example : Claims.grid_prob := grid_prob
example : Claims.consistency_i := consistency_i
example : Claims.consistency_ii := consistency_ii
example : Claims.cor_consistency := cor_consistency
example : Claims.Demp_le_Dphi := Demp_le_Dphi
example : Claims.ratecond_closed := ratecond_closed
example : Claims.ratecond_tauA := ratecond_tauA
example : Claims.pinelis_ineq := pinelis_ineq
example : Claims.ratecond_mcd := ratecond_mcd
example : Claims.ratecond_pin := ratecond_pin
example : Claims.ratecond_sharp := ratecond_sharp
example : Claims.ratecond_zero := ratecond_zero
example : Claims.ratecond_noconv := ratecond_noconv
example : Claims.ratecond_gauss := ratecond_gauss
example : Claims.rate_eps := rate_eps
example : Claims.rate := rate
example : Claims.rate_poly := rate_poly
example : Claims.confset := confset
example : Claims.confset_width := confset_width
example : Claims.upperfs := upperfs
example : Claims.alphaHi_le := alphaHi_le
example : Claims.upperfs_interval := upperfs_interval
example : Claims.hausdorff_valid := hausdorff_valid
example : Claims.hausdorff_lower := hausdorff_lower
end StatFormal.Wave30tu

namespace StatFormal.Wave30tu.Instance
example : Claims.tauNM_threshold := tauNM_threshold
example : Claims.tauNM_oneevent := tauNM_oneevent
example : Claims.tauA_tool := tauA_tool
example : Claims.consistency_i_inst := consistency_i_inst
example : Claims.consistency_ii_inst := consistency_ii_inst
example : Claims.cor_consistency_inst := cor_consistency_inst
example : Claims.rate_inst := rate_inst
example : Claims.confset_inst := confset_inst
example : Claims.rate_poly_inst := rate_poly_inst
example : Claims.confset_width_inst := confset_width_inst
example : Claims.upperfs_inst := upperfs_inst
example : Claims.upperfs_interval_inst := upperfs_interval_inst
end StatFormal.Wave30tu.Instance

namespace StatFormal.Wave30tu.Full
example : Claims.tauFull_threshold := tauFull_threshold
example : Claims.tauFullCpl_threshold := tauFullCpl_threshold
example : Claims.tauFullGrid_threshold := tauFullGrid_threshold
example : Claims.consistency_i_full := consistency_i_full
example : Claims.consistency_ii_full := consistency_ii_full
example : Claims.cor_consistency_full := cor_consistency_full
example : Claims.rate_full := rate_full
example : Claims.confset_full := confset_full
example : Claims.upperfs_interval_full := upperfs_interval_full
example : Claims.ratecond_full := ratecond_full
example : Claims.ratecond_full_cpl := ratecond_full_cpl
example : Claims.ratecond_full_grid := ratecond_full_grid
end StatFormal.Wave30tu.Full

namespace StatFormal.Wave30tu.Crossing
example : Claims.crossing_nc := crossing_nc
example : Claims.crossing_full := crossing_full
end StatFormal.Wave30tu.Crossing
