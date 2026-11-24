import StatFormal.Archive.Wave24a.Statements
import StatFormal.Archive.Wave24a.RouteBandSat
import StatFormal.Archive.Wave24a.RouteBasebridge
import StatFormal.Archive.Wave24a.RouteConsistency
import StatFormal.Archive.Wave24a.RouteLinLip
import StatFormal.Archive.Wave24a.RouteNeural
import StatFormal.Archive.Wave24a.RouteParsimony
import StatFormal.Archive.Wave24a.RouteRandom
import StatFormal.Archive.Wave24a.RouteRkPaths
import StatFormal.Archive.Wave24a.RouteSieveRate
import StatFormal.Archive.Wave24a.RouteSmall
import StatFormal.Archive.Wave24a.RouteTcompact
import StatFormal.Archive.Wave24a.RouteUniformX

namespace StatFormal.Wave24a
example : Claims.randomisation_full := randomisation_full
example : Claims.randomisation_mc := randomisation_mc
example : Claims.jensen := jensen
example : Claims.trimSet_mono := trimSet_mono
example : Claims.sinkmono := sinkmono
example : Claims.tcompact := tcompact
example : Claims.app_hard_envelope := app_hard_envelope
example : Claims.consistency_A := consistency_A
example : Claims.consistency_B := consistency_B
example : Claims.lin_lipschitz := lin_lipschitz
example : Claims.lin_lipschitz_pell := lin_lipschitz_pell
example : Claims.band_saturation_sandwich := band_saturation_sandwich
example : Claims.conditional_uniform_x_maps := conditional_uniform_x_maps
example : Claims.conditional_uniform_x := conditional_uniform_x
example : Claims.neural_law_to_map := neural_law_to_map
example : Claims.neural_law_to_map_uniform := neural_law_to_map_uniform
example : Claims.rk_paths_mono := rk_paths_mono
example : Claims.rk_paths_labels := rk_paths_labels
example : Claims.rk_paths_consistency := rk_paths_consistency
example : Claims.parsimony_tolerance := parsimony_tolerance
example : Claims.parsimony_tolerance_tendsto := parsimony_tolerance_tendsto
example : Claims.basebridge := basebridge
example : Claims.app_bijective_rate := app_bijective_rate
example : Claims.app_entropic_rate := app_entropic_rate
end StatFormal.Wave24a
