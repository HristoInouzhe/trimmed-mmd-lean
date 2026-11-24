import StatFormal.Wave31tr.Statements
import StatFormal.Wave31tr.RouteAlpha0
import StatFormal.Wave31tr.RouteAlpha0As
import StatFormal.Wave31tr.RouteAlpha0Ex
import StatFormal.Wave31tr.RouteAlpha0Gate
import StatFormal.Wave31tr.RouteAlpha0Rej
import StatFormal.Wave31tr.RouteCert
import StatFormal.Wave31tr.RouteCertBet
import StatFormal.Wave31tr.RouteCertTaup
import StatFormal.Wave31tr.RouteExcess
import StatFormal.Wave31tr.RouteExcessLaplace
import StatFormal.Wave31tr.RouteExcessQ
import StatFormal.Wave31tr.RouteExcessRegions
import StatFormal.Wave31tr.RouteFW
import StatFormal.Wave31tr.RouteFWFit
import StatFormal.Wave31tr.RouteFWLimits
import StatFormal.Wave31tr.RouteFWLower
import StatFormal.Wave31tr.RouteFWQuantile
import StatFormal.Wave31tr.RouteKernel
import StatFormal.Wave31tr.RouteKernelAdm
import StatFormal.Wave31tr.RouteKernelSum
import StatFormal.Wave31tr.RouteMisc1Bang
import StatFormal.Wave31tr.RouteMisc1Contact
import StatFormal.Wave31tr.RouteMisc1Conv
import StatFormal.Wave31tr.RouteMisc1Gauss
import StatFormal.Wave31tr.RouteMisc1House
import StatFormal.Wave31tr.RouteMisc1KS
import StatFormal.Wave31tr.RouteMisc1Kernel
import StatFormal.Wave31tr.RoutePop
import StatFormal.Wave31tr.RoutePopContam
import StatFormal.Wave31tr.RoutePopOsc
import StatFormal.Wave31tr.RoutePopQ
import StatFormal.Wave31tr.RouteRun
import StatFormal.Wave31tr.RouteRunExists
import StatFormal.Wave31tr.RouteRunPairing
import StatFormal.Wave31tr.RouteRunQP
import StatFormal.Wave31tr.RouteRunThm
import StatFormal.Wave31tr.RouteRunThmMisc
import StatFormal.Wave31tr.RouteRunThmRates
import StatFormal.Wave31tr.RouteRunWit

/-!
# Wave 31tr: proofs of the frozen claims (the non-Fourier gaps of trimmed-mmd, AoS)

Each theorem's type is literally the frozen `Claims.*` Prop of `StatFormal/Wave31tr/Statements.lean`; the proofs are in the
untrusted route files `Route*.lean` (chunks A1 `RouteRun`, A2 `RouteRunThm`, A3 `RouteKernel`, E1 `RouteExcess`, E2 `RoutePop`,
M1 `RouteMisc1`, M2 `RouteAlpha0`, M3 `RouteFW`, M4 `RouteCert`) on the library folders `StatFormal/Lib/{PaperRun, PaperRunThm,
KernelRun, ExcessRamp, TVFacts, KernelFacts, Alpha0Witness, FrankWolfe, FnCert}`.
-/

namespace StatFormal.Wave31tr

theorem genuine_rules : Claims.genuine_rules := RouteRun.genuine_rules_route
theorem printed_cuts : Claims.printed_cuts := RouteRun.printed_cuts_route
theorem paperRun_exists : Claims.paperRun_exists := RouteRun.paperRun_exists_route
theorem paperRun_exists_printed : Claims.paperRun_exists_printed := RouteRun.paperRun_exists_printed_route
theorem paperRun_exists_fractions : Claims.paperRun_exists_fractions := RouteRun.paperRun_exists_fractions_route
theorem paperRun_admissible : Claims.paperRun_admissible := RouteRun.paperRun_admissible_route
theorem paperRun_betting : Claims.paperRun_betting := RouteRunThm.paperRun_betting_route
theorem paperRun_betting_cond : Claims.paperRun_betting_cond := RouteRunThm.paperRun_betting_cond_route
theorem laplace_qdens_fails : Claims.laplace_qdens_fails := RouteExcess.laplace_qdens_fails_route
theorem finite_support_not_qdens : Claims.finite_support_not_qdens := RoutePop.finite_support_not_qdens_route
theorem alg_prior : Claims.alg_prior := RouteRunThm.alg_prior_route
theorem averaged_evalue : Claims.averaged_evalue := RouteKernel.averaged_evalue_route
theorem bound_summaries : Claims.bound_summaries := RouteKernel.bound_summaries_route
theorem tv_pushforward : Claims.tv_pushforward := RoutePop.tv_pushforward_route
theorem upper_end : Claims.upper_end := RoutePop.upper_end_route
theorem margin_eps0 : Claims.margin_eps0 := RoutePop.margin_eps0_route
theorem paper_lorate_O : Claims.paper_lorate_O := RouteRunThm.paper_lorate_O_route
theorem paper_same_rate : Claims.paper_same_rate := RouteRunThm.paper_same_rate_route
theorem paper_lorate_i : Claims.paper_lorate_i := RouteRunThm.paper_lorate_i_route
theorem paper_lorate_ii : Claims.paper_lorate_ii := RouteRunThm.paper_lorate_ii_route
theorem paper_lorate_nologJ : Claims.paper_lorate_nologJ := RouteRunThm.paper_lorate_nologJ_route
theorem paper_lorate_general : Claims.paper_lorate_general := RouteRunThm.paper_lorate_general_route
theorem paper_newrates_i_a : Claims.paper_newrates_i_a := RouteRunThm.paper_newrates_i_a_route
theorem paper_newrates_i_b : Claims.paper_newrates_i_b := RouteRunThm.paper_newrates_i_b_route
theorem paper_minimax_ii : Claims.paper_minimax_ii := RouteRunThm.paper_minimax_ii_route
theorem paper_lo_consistency : Claims.paper_lo_consistency := RouteRunThm.paper_lo_consistency_route
theorem paper_lo_refining : Claims.paper_lo_refining := RouteRunThm.paper_lo_refining_route
theorem paper_alphalo : Claims.paper_alphalo := RouteRunThm.paper_alphalo_route
theorem different_fractions : Claims.different_fractions := RoutePop.different_fractions_route
theorem trimming_at_lower : Claims.trimming_at_lower := RouteRunThm.trimming_at_lower_route
theorem propensity_core : Claims.propensity_core := RoutePop.propensity_core_route
theorem taup_jump : Claims.taup_jump := RouteCert.taup_jump_route
theorem taup_welldefined : Claims.taup_welldefined := RouteCert.taup_welldefined_route
theorem taup_valid_bound : Claims.taup_valid_bound := RouteCert.taup_valid_bound_route
theorem taup_consistent_below : Claims.taup_consistent_below := RouteCert.taup_consistent_below_route
theorem bayes_risk : Claims.bayes_risk := RoutePop.bayes_risk_route
theorem kernel_run_valid : Claims.kernel_run_valid := RouteKernel.kernel_run_valid_route
theorem median_bandwidth : Claims.median_bandwidth := RouteKernel.median_bandwidth_route
theorem kernel_profiles : Claims.kernel_profiles := RouteKernel.kernel_profiles_route
theorem margin_without_qdens : Claims.margin_without_qdens := RoutePop.margin_without_qdens_route
theorem npQuantile_rule : Claims.npQuantile_rule := RouteRun.npQuantile_rule_route
theorem ordStat_facts : Claims.ordStat_facts := RouteRun.ordStat_facts_route
theorem printedPairing_exists : Claims.printedPairing_exists := RouteRun.printedPairing_exists_route
theorem printedPairing_batch : Claims.printedPairing_batch := RouteRun.printedPairing_batch_route
theorem printedPairing_default : Claims.printedPairing_default := RouteRun.printedPairing_default_route
theorem qp_measurable_argmin : Claims.qp_measurable_argmin := RouteRun.qp_measurable_argmin_route
theorem alpha0_uniform : Claims.alpha0_uniform := RouteAlpha0.alpha0_uniform_route
theorem fw_gap : Claims.fw_gap := RouteFW.fw_gap_route
theorem fw_exact : Claims.fw_exact := RouteFW.fw_exact_route
theorem fitted_ramp_fw : Claims.fitted_ramp_fw := RouteFW.fitted_ramp_fw_route
theorem lo_lower_bound_fw : Claims.lo_lower_bound_fw := RouteFW.lo_lower_bound_fw_route
theorem lo_consistency_fw : Claims.lo_consistency_fw := RouteFW.lo_consistency_fw_route
theorem same_quantile : Claims.same_quantile := RouteFW.same_quantile_route
theorem default_pairs_three_quarters : Claims.default_pairs_three_quarters := RouteRunThm.default_pairs_three_quarters_route
theorem dbar_le_D_le : Claims.dbar_le_D_le := RouteExcess.dbar_le_D_le_route
theorem margin_dbar_factor : Claims.margin_dbar_factor := RoutePop.margin_dbar_factor_route
theorem witness_unique : Claims.witness_unique := RouteExcess.witness_unique_route
theorem contam_equiv : Claims.contam_equiv := RoutePop.contam_equiv_route
theorem trimming_removal : Claims.trimming_removal := RoutePop.trimming_removal_route
theorem regions_nested : Claims.regions_nested := RouteExcess.regions_nested_route
theorem bathtub_quantiles : Claims.bathtub_quantiles := RoutePop.bathtub_quantiles_route
theorem excess_bathtub : Claims.excess_bathtub := RouteExcess.excess_bathtub_route
theorem excess_identity : Claims.excess_identity := RouteExcess.excess_identity_route
theorem excess_i : Claims.excess_i := RouteExcess.excess_i_route
theorem excess_ii : Claims.excess_ii := RouteExcess.excess_ii_route
theorem excess_laplace : Claims.excess_laplace := RouteExcess.excess_laplace_route
theorem laplace_green : Claims.laplace_green := RouteExcess.laplace_green_route
theorem oscillation_blind : Claims.oscillation_blind := RoutePop.oscillation_blind_route
theorem gauss_qdens_formula : Claims.gauss_qdens_formula := RouteMisc1.gauss_qdens_formula_route
theorem gauss_qdens_Q_Qprime : Claims.gauss_qdens_Q_Qprime := RouteMisc1.gauss_qdens_Q_Qprime_route
theorem alpha0_fit_uniform_as : Claims.alpha0_fit_uniform_as := RouteAlpha0.alpha0_fit_uniform_as_route
theorem ksPlus_locally_constant : Claims.ksPlus_locally_constant := RouteAlpha0.ksPlus_locally_constant_route
theorem ex_ks_stable : Claims.ex_ks_stable := RouteAlpha0.ex_ks_stable_route
theorem alpha0_reject_le : Claims.alpha0_reject_le := RouteAlpha0.alpha0_reject_le_route
theorem alpha0_inconsistent : Claims.alpha0_inconsistent := RouteAlpha0.alpha0_inconsistent_route
theorem alpha0_gate : Claims.alpha0_gate := RouteAlpha0.alpha0_gate_route
theorem any_threshold_converse : Claims.any_threshold_converse := RouteMisc1.any_threshold_converse_route
theorem bangbang_aos : Claims.bangbang_aos := RouteMisc1.bangbang_aos_route
theorem tv_one_sided_ks : Claims.tv_one_sided_ks := RouteMisc1.tv_one_sided_ks_route
theorem ks_lower_confidence : Claims.ks_lower_confidence := RouteMisc1.ks_lower_confidence_route
theorem contact_densities : Claims.contact_densities := RouteMisc1.contact_densities_route
theorem contact_gauss_mix : Claims.contact_gauss_mix := RouteMisc1.contact_gauss_mix_route
theorem minimax_class_apart : Claims.minimax_class_apart := RouteMisc1.minimax_class_apart_route
theorem house_encoding : Claims.house_encoding := RouteMisc1.house_encoding_route
theorem kernel_constants : Claims.kernel_constants := RouteMisc1.kernel_constants_route
theorem fncert_drift_err : Claims.fncert_drift_err := RouteCert.fncert_drift_err_route
theorem fncert_upper : Claims.fncert_upper := RouteCert.fncert_upper_route
theorem fncert_rejected_upper : Claims.fncert_rejected_upper := RouteCert.fncert_rejected_upper_route
theorem fncert_betting_error : Claims.fncert_betting_error := RouteCert.fncert_betting_error_route

end StatFormal.Wave31tr
