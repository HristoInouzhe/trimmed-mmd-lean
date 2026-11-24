import StatFormal.Wave31tq.Statements
import StatFormal.Wave31tq.RouteA1
import StatFormal.Wave31tq.RouteA2
import StatFormal.Wave31tq.RouteA5
import StatFormal.Wave31tq.RouteA6
import StatFormal.Wave31tq.RouteA7
import StatFormal.Wave31tq.RouteSInt
import StatFormal.Wave31tq.RouteSNorm
import StatFormal.Wave31tq.RouteSThm
import StatFormal.Wave31tq.RouteSCor
import StatFormal.Wave31tq.RouteSOP
import StatFormal.Wave31tq.RouteGAll
import StatFormal.Wave31tq.RouteT18
import StatFormal.Wave31tq.RouteT19
import StatFormal.Wave31tq.RouteT20
import StatFormal.Wave31tq.RouteT21
import StatFormal.Wave31tq.RouteT24
import StatFormal.Wave31tq.RouteMAll
import StatFormal.Wave31tq.RouteXGamma
import StatFormal.Wave31tq.RouteXHalf

/-!
# Wave 31tq — proofs of the frozen claims

Each theorem proves the frozen claim `StatFormal.Wave31tq.Claims.<name>` of `Statements.lean` by the route theorem of its chunk
(A: the setting and the angular dictionary, Q1–Q7; S: Sobolev kernels, Q9–Q12; G: the Gaussian kernel, Q14–Q17; T: explicit trimmings,
Q18–Q20, Q21 small s, Q24; M: Propositions 5.5, 5.6 and the compositions, Q21, Q22, Q25–Q28; X: Proposition S4.5 and the half-space
witness, Q8, Q29). Route theorems named `_of` take other chunks' frozen claims as hypotheses; they are discharged here by the theorems
proved above them, so every theorem below is unconditional.
-/

namespace StatFormal.Wave31tq

/-! ### A. Setting and dictionary (Q1–Q7) -/

theorem tv_density : Claims.tv_density := RouteA.tv_density_route
theorem spectral_angular : Claims.spectral_angular := RouteA.spectral_angular_route
theorem native_angular : Claims.native_angular := RouteA.native_angular_route
theorem bochner_angular : Claims.bochner_angular := RouteA.bochner_angular_route
theorem sobolev_angular : Claims.sobolev_angular := RouteA.sobolev_angular_route
theorem sobolev_needs : Claims.sobolev_needs := RouteA.sobolev_needs_route
theorem kernel_instances : Claims.kernel_instances := RouteA.kernel_instances_route

/-! ### C. Touching contaminations (Q8) -/

theorem newgammaone : Claims.newgammaone := RouteX.newgammaone_route
theorem newgammaone_smooth : Claims.newgammaone_smooth := RouteX.newgammaone_smooth_route

/-! ### D. Sobolev kernels (Q9–Q12) -/

theorem translation_intervals : Claims.translation_intervals := RouteS.translation_intervals_route
theorem newsobnorm : Claims.newsobnorm := RouteS.newsobnorm_route
theorem newsobolev_thm : Claims.newsobolev_thm := RouteS.newsobolev_thm_of tv_density sobolev_angular
theorem newsobolev_cor_bounded : Claims.newsobolev_cor_bounded :=
  RouteS.newsobolev_cor_bounded_of tv_density sobolev_angular
theorem newsobolev_cor_line : Claims.newsobolev_cor_line := RouteS.newsobolev_cor_line_of tv_density sobolev_angular
theorem newsobolev_cor_OP : Claims.newsobolev_cor_OP := RouteS.newsobolev_cor_OP_route

/-! ### E. The Gaussian kernel (Q14–Q17) -/

theorem bandlimited_angular : Claims.bandlimited_angular := RouteG.bandlimited_angular_route
theorem bbar_even : Claims.bbar_even := RouteG.bbar_even_route
theorem bandB_facts : Claims.bandB_facts := RouteG.bandB_facts_route
theorem newgaussstep : Claims.newgaussstep := RouteG.newgaussstep_of tv_density
theorem newgauss_thm : Claims.newgauss_thm := RouteG.newgauss_thm_of tv_density
theorem newgauss_thm_rho : Claims.newgauss_thm_rho := RouteG.newgauss_thm_rho_of tv_density

/-! ### F. Explicit trimmings (Q18–Q20) -/

theorem momentdecay_angular : Claims.momentdecay_angular := RouteT.momentdecay_angular_route
theorem newupperone : Claims.newupperone := RouteT.newupperone_of tv_density bochner_angular
theorem newmoments : Claims.newmoments := RouteT.newmoments_of tv_density bochner_angular

/-! ### G. The main-text propositions (Q21, Q22, Q24) -/

theorem newsobolev : Claims.newsobolev := RouteM.newsobolev_of tv_density newsobolev_cor_line newmoments
theorem newsobolev_E1 : Claims.newsobolev_E1 := RouteM.newsobolev_E1_of tv_density newsobolev_cor_line newmoments
theorem newsobolev_upper_small : Claims.newsobolev_upper_small :=
  RouteT.newsobolev_upper_small_of tv_density bochner_angular
theorem newgauss : Claims.newgauss := RouteM.newgauss_of tv_density newgauss_thm_rho newmoments kernel_instances
theorem newgauss_margin : Claims.newgauss_margin :=
  RouteM.newgauss_margin_of tv_density newgauss_thm_rho newmoments kernel_instances
theorem sharp_line : Claims.sharp_line := RouteT.sharp_line_of newsobolev_cor_line tv_density bochner_angular

/-! ### H. Rates and the converse (Q25) -/

theorem rate_sobolev_split : Claims.rate_sobolev_split := RouteM.rate_sobolev_split_of tv_density newsobolev_cor_line
theorem converse_poly : Claims.converse_poly := RouteM.converse_poly_route
theorem lower_sobolev_A : Claims.lower_sobolev_A :=
  RouteM.lower_sobolev_A_of tv_density newsobolev_cor_line newmoments sobolev_angular
theorem slow_gauss_A : Claims.slow_gauss_A :=
  RouteM.slow_gauss_A_of tv_density newgauss_thm_rho newmoments kernel_instances

/-! ### H2. Compositions and instances (Q26–Q29) -/

theorem excess_sobolev : Claims.excess_sobolev :=
  RouteM.excess_sobolev_of tv_density newsobolev_cor_line newmoments sobolev_angular
theorem laplace_instances : Claims.laplace_instances :=
  RouteM.laplace_instances_of tv_density newsobolev_cor_line newmoments sobolev_angular kernel_instances
theorem simulated_pairs : Claims.simulated_pairs := RouteM.simulated_pairs_route
theorem halfspace_geometry : Claims.halfspace_geometry := RouteX.halfspace_geometry_route
theorem halfspace_pair : Claims.halfspace_pair := RouteX.halfspace_pair_route

end StatFormal.Wave31tq
