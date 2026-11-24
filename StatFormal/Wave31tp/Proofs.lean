import StatFormal.Wave31tp.Statements
import StatFormal.Wave31tp.RouteF
import StatFormal.Wave31tp.RouteK
import StatFormal.Wave31tp.RouteG
import StatFormal.Wave31tp.RouteE
import StatFormal.Wave31tp.RouteM
import StatFormal.Wave31tp.RouteS
import StatFormal.Wave31tp.RouteV
import StatFormal.Wave31tp.RouteN
import StatFormal.Wave31tp.RouteMat
import StatFormal.Wave31tp.RouteR
import StatFormal.Wave31tp.RouteC

/-!
# Wave 31tp: proofs of the frozen claims (classical Fourier/RKHS library)

Each theorem's type is literally the frozen `Claims.*` Prop of `StatFormal/Wave31tp/Statements.lean`.
-/

namespace StatFormal.Wave31tp

theorem ft2_ae : Claims.ft2_ae := RouteF.ft2_ae_route
theorem plancherel : Claims.plancherel := RouteF.plancherel_route
theorem bochner_integrable : Claims.bochner_integrable := RouteK.bochner_integrable_route
theorem gram_profile : Claims.gram_profile := RouteK.gram_profile_route
theorem fourier_feature : Claims.fourier_feature := RouteK.fourier_feature_route
theorem feature_exists : Claims.feature_exists := RouteK.feature_exists_route
theorem ftMeas_facts : Claims.ftMeas_facts := RouteK.ftMeas_facts_route
theorem mmd_fourier : Claims.mmd_fourier := RouteK.mmd_fourier_route
theorem native_incl : Claims.native_incl := RouteK.native_incl_route
theorem sobolev_incl : Claims.sobolev_incl := RouteK.sobolev_incl_route
theorem gauss_spec : Claims.gauss_spec := RouteK.gauss_spec_route
theorem laplace_spec : Claims.laplace_spec := RouteK.laplace_spec_route
theorem gram_iso : Claims.gram_iso := RouteG.gram_iso_route
theorem gram_rep : Claims.gram_rep := RouteG.gram_rep_route
theorem gram_mmd : Claims.gram_mmd := RouteG.gram_mmd_route
theorem rkhs_canonical : Claims.rkhs_canonical := RouteG.rkhs_canonical_route

theorem taylor_cexp : Claims.taylor_cexp := RouteE.taylor_cexp_route
theorem moment_decay : Claims.moment_decay := RouteE.moment_decay_route
theorem gauss_moments : Claims.gauss_moments := RouteE.gauss_moments_route
theorem moment_poly : Claims.moment_poly := RouteE.moment_poly_route
theorem moment_poly_scale : Claims.moment_poly_scale := RouteE.moment_poly_scale_route
theorem dilate_facts : Claims.dilate_facts := RouteM.dilate_facts_route
theorem laplacian_fourier : Claims.laplacian_fourier := RouteM.laplacian_fourier_route
theorem mollify_smooth : Claims.mollify_smooth := RouteM.mollify_smooth_route
theorem mollify_cont : Claims.mollify_cont := RouteM.mollify_cont_route
theorem translation_plancherel : Claims.translation_plancherel := RouteM.translation_plancherel_route
theorem translation_indicator : Claims.translation_indicator := RouteM.translation_indicator_route
theorem jball_facts : Claims.jball_facts := RouteS.jball_facts_route
theorem jball_one : Claims.jball_one := RouteS.jball_one_route
theorem support_density : Claims.support_density := RouteS.support_density_route
theorem gaussMix_facts : Claims.gaussMix_facts := RouteS.gaussMix_facts_route
theorem gaussMix_distinct : Claims.gaussMix_distinct := RouteS.gaussMix_distinct_route

theorem sobolev_smooth_finite : Claims.sobolev_smooth_finite := RouteV.sobolev_smooth_finite_route
theorem containsSmoothCompact_of_spec : Claims.containsSmoothCompact_of_spec := RouteV.containsSmoothCompact_of_spec_route
theorem bandlimited : Claims.bandlimited := RouteV.bandlimited_route
theorem bandlimited_gauss : Claims.bandlimited_gauss := RouteV.bandlimited_gauss_route
theorem native_char : Claims.native_char := RouteN.native_char_route
theorem matern_facts : Claims.matern_facts := RouteMat.matern_facts_route
theorem matern_one : Claims.matern_one := RouteMat.matern_one_route
theorem rkhs_smooth : Claims.rkhs_smooth := RouteR.rkhs_smooth_route
theorem gauss_smooth : Claims.gauss_smooth := RouteR.gauss_smooth_route
theorem characteristic_spec : Claims.characteristic_spec := RouteR.characteristic_spec_route
theorem rkhs_vanish : Claims.rkhs_vanish := RouteR.rkhs_vanish_route
theorem gauss_regular_smooth : Claims.gauss_regular_smooth := RouteR.gauss_regular_smooth_route
theorem matern_interpolation_free : Claims.matern_interpolation_free := RouteC.matern_interpolation_free_route

end StatFormal.Wave31tp
