import StatFormal.Archive.Wave23d.Statements
import StatFormal.Archive.Wave23d.RouteBall
import StatFormal.Archive.Wave23d.RouteCM
import StatFormal.Archive.Wave23d.RouteGrad
import StatFormal.Archive.Wave23d.RouteRepair
import StatFormal.Archive.Wave23d.RouteSinkhorn
import StatFormal.Archive.Wave23d.RouteStudent
import StatFormal.Archive.Wave23d.RouteUniq

/-! Aliases: route theorems are named `<claim>_thm`; the gate expects theorem names equal to the claim names. -/

namespace StatFormal.Wave23d
theorem birkhoff_contraction : Claims.birkhoff_contraction := birkhoff_contraction_thm
theorem sinkhorn_constants : Claims.sinkhorn_constants := sinkhorn_constants_thm
theorem sinkhorn_deltaC_diam : Claims.sinkhorn_deltaC_diam := sinkhorn_deltaC_diam_thm
theorem sinkhorn_aposteriori_i : Claims.sinkhorn_aposteriori_i := sinkhorn_aposteriori_i_thm
theorem sinkhorn_aposteriori_ii : Claims.sinkhorn_aposteriori_ii := sinkhorn_aposteriori_ii_thm
theorem ball_region_bound : Claims.ball_region_bound := ball_region_bound_thm
theorem ball_tau_mono : Claims.ball_tau_mono := ball_tau_mono_thm
theorem ball_decay : Claims.ball_decay := ball_decay_thm
theorem cm_closure : Claims.cm_closure := cm_closure_thm
theorem cm_transpose : Claims.cm_transpose := cm_transpose_thm
theorem cm_support : Claims.cm_support := cm_support_thm
theorem cm_rockafellar : Claims.cm_rockafellar := cm_rockafellar_thm
theorem cm_graph_exists : Claims.cm_graph_exists := cm_graph_exists_thm
theorem student_depth : Claims.student_depth := student_depth_thm
theorem student_content : Claims.student_content := student_content_thm
theorem student_beta : Claims.student_beta := student_beta_thm
theorem student_region : Claims.student_region := student_region_thm
theorem repair_cert : Claims.repair_cert := repair_cert_thm
theorem repair_omega_le_lip : Claims.repair_omega_le_lip := repair_omega_le_lip_thm
theorem repair_partial_delta : Claims.repair_partial_delta := repair_partial_delta_thm
theorem repair_root_affine : Claims.repair_root_affine := repair_root_affine_thm
theorem repair_convex_omega : Claims.repair_convex_omega := repair_convex_omega_thm
theorem repair_convex_lip : Claims.repair_convex_lip := repair_convex_lip_thm
theorem repair_convex_delta : Claims.repair_convex_delta := repair_convex_delta_thm
theorem repair_sqrt_envelope_not_convex : Claims.repair_sqrt_envelope_not_convex := repair_sqrt_envelope_not_convex_thm
theorem cm_gateaux : Claims.cm_gateaux := cm_gateaux_thm
theorem cm_graph_gradient : Claims.cm_graph_gradient := cm_graph_gradient_thm
theorem cm_unique_cond : Claims.cm_unique_cond := cm_unique_cond_thm
theorem ghs_grad_unique_m1 : Claims.ghs_grad_unique_m1 := ghs_grad_unique_m1_thm
theorem cm_unique_uncond : Claims.cm_unique_uncond := cm_unique_uncond_thm
end StatFormal.Wave23d
