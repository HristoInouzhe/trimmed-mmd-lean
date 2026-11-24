import StatFormal.Wave31tu.Statements
import StatFormal.Wave31tu.RouteLBanach
import StatFormal.Wave31tu.RouteLCake
import StatFormal.Wave31tu.RouteLIntervals
import StatFormal.Wave31tu.RouteLBV
import StatFormal.Wave31tu.RouteH1
import StatFormal.Wave31tu.RouteH2
import StatFormal.Wave31tu.RouteP6
import StatFormal.Wave31tu.RouteP7
import StatFormal.Wave31tu.RouteP8
import StatFormal.Wave31tu.RouteP9
import StatFormal.Wave31tu.RouteP10
import StatFormal.Wave31tu.RouteP11
import StatFormal.Wave31tu.RouteP12
import StatFormal.Wave31tu.RouteP14
import StatFormal.Wave31tu.RouteP14Own
import StatFormal.Wave31tu.RouteD13
import StatFormal.Wave31tu.RouteFMain
import StatFormal.Wave31tu.RouteFFrac
import StatFormal.Wave31tu.RouteBRescale
import StatFormal.Wave31tu.RouteBBets
import StatFormal.Wave31tu.RouteTImproves
import StatFormal.Wave31tu.RouteTConst
import StatFormal.Wave31tu.RouteTPr
import StatFormal.Wave31tu.RouteTRate
import StatFormal.Wave31tu.RouteKLocal
import StatFormal.Wave31tu.RouteKLocalQ
import StatFormal.Wave31tu.RouteKRate
import StatFormal.Wave31tu.RouteSLocal
import StatFormal.Wave31tu.RouteSNotCross
import StatFormal.Wave31tu.RouteSSims
import StatFormal.Wave31tu.RouteR24
import StatFormal.Wave31tu.RouteR25
import StatFormal.Wave31tu.RouteR26

/-!
# Wave 31tu: proofs of the frozen claims (Theorem 5.11, Theorem S4.19, §S4.12, Prop S4.8 (ii)–(iii), trimmed-mmd AoS)

Each theorem's type is literally the frozen `Claims.*` Prop of `StatFormal/Wave31tu/Statements.lean`; the proofs are in the
untrusted route files `Route*.lean`: chunks L `RouteL*` (Y1, Y2, Y4, Y5), H `RouteH*` (Y3), P `RouteP*` (Y6–Y12, Y14),
D `RouteD*` (Y13), F `RouteF*` (Y15), B `RouteB*` (Y16, Y17), T `RouteT*` (Y18, Y19, Y22), K `RouteK*` (Y20 (a)–(c), Y21),
S `RouteS*` (Y20 (d), (e), Y23), R `RouteR*` (Y24–Y26), on the library folders `StatFormal/Lib/{Indicatrix, IntervalDev,
LaplaceH1, EmpiricalQuantile, LaplaceDev, FixedPoint, LaplaceScale, LaplaceRate, LocalLower, CrossExamples, ExpMargin}`.

Route theorems stated as `<claim>_of` take other frozen 31tu claims as hypotheses (the cross-chunk interfaces); they are
discharged here by the theorems above them, so every theorem below is unconditional.
-/

namespace StatFormal.Wave31tu

/-! ### Block L: the classical library (Y1–Y5) -/

theorem banach_indicatrix_le : Claims.banach_indicatrix_le := RouteL.banach_indicatrix_le_route
theorem banach_indicatrix : Claims.banach_indicatrix := RouteL.banach_indicatrix_route
theorem layer_cake01 : Claims.layer_cake01 := RouteL.layer_cake01_route
theorem laplace_h1 : Claims.laplace_h1 := RouteH.laplace_h1_route
theorem laplace_h1_char : Claims.laplace_h1_char := RouteH.laplace_h1_char_route
theorem lap_intervals : Claims.lap_intervals := RouteL.lap_intervals_route
theorem lap_bv : Claims.lap_bv := RouteL.lap_bv_route

/-! ### Block P: the proof section §S4.12 (Y6–Y17) -/

theorem lap_err : Claims.lap_err := RouteP.lap_err_route
theorem lap_const : Claims.lap_const := RouteP.lap_const_route
theorem condR_facts : Claims.condR_facts := RouteP.condR_facts_route
theorem lap_ratio : Claims.lap_ratio := RouteP.lap_ratio_route
theorem lap_clip : Claims.lap_clip := RouteP.lap_clip_route
theorem lap_pop : Claims.lap_pop := RouteP.lap_pop_route
theorem lap_compare : Claims.lap_compare := RouteP.lap_compare_route
theorem lap_dev : Claims.lap_dev := RouteD.lap_dev_of laplace_h1 lap_bv lap_err
theorem own_ramp : Claims.own_ramp := RouteP.own_ramp_route
theorem lap_own : Claims.lap_own := RouteP.lap_own_route
theorem lap_fitted : Claims.lap_fitted :=
  RouteF.lap_fitted_of lap_err lap_const lap_ratio lap_clip lap_pop lap_compare lap_dev lap_own
theorem lap_fitted_fraction : Claims.lap_fitted_fraction :=
  RouteF.lap_fitted_fraction_of lap_err lap_const lap_ratio lap_clip lap_pop lap_compare lap_dev lap_own
theorem lap_bets : Claims.lap_bets := RouteB.lap_bets_route
theorem lap_rescale : Claims.lap_rescale := RouteB.lap_rescale_route

/-! ### Theorem S4.19 and Theorem 5.11 (Y18, Y19, Y22) -/

theorem laplace_const_i : Claims.laplace_const_i :=
  RouteT.laplace_const_i_of lap_intervals condR_facts lap_clip lap_fitted lap_bets lap_rescale
theorem laplace_const_ii : Claims.laplace_const_ii :=
  RouteT.laplace_const_ii_of lap_intervals lap_clip lap_fitted lap_bets lap_rescale
theorem laplace_const_pr_i : Claims.laplace_const_pr_i :=
  RouteT.laplace_const_pr_i_of lap_intervals condR_facts lap_clip lap_fitted lap_bets lap_rescale
theorem laplace_const_pr_ii : Claims.laplace_const_pr_ii :=
  RouteT.laplace_const_pr_ii_of lap_intervals lap_clip lap_fitted lap_bets lap_rescale
theorem laplace_rate_i : Claims.laplace_rate_i :=
  RouteT.laplace_rate_i_of lap_intervals condR_facts lap_clip lap_fitted lap_bets lap_rescale
theorem laplace_rate_ii : Claims.laplace_rate_ii :=
  RouteT.laplace_rate_ii_of lap_intervals lap_clip lap_fitted lap_bets lap_rescale
theorem laplace_rate_improves : Claims.laplace_rate_improves := RouteT.laplace_rate_improves_route
theorem laplace_rate_grid : Claims.laplace_rate_grid :=
  RouteT.laplace_rate_grid_of lap_intervals condR_facts lap_clip lap_fitted lap_bets lap_rescale

/-! ### The local lower bound and the simulated pairs (Y20, Y21, Y23) -/

theorem lap_local : Claims.lap_local := RouteK.lap_local_route
theorem lap_local_Q : Claims.lap_local_Q := RouteK.lap_local_Q_route
theorem lap_local_c : Claims.lap_local_c := RouteK.lap_local_c_route
theorem lap_local_d : Claims.lap_local_d := RouteS.lap_local_d_of lap_local
theorem lower2pt_not_cross : Claims.lower2pt_not_cross := RouteS.lower2pt_not_cross_route
theorem local_rate : Claims.local_rate := RouteK.local_rate_route
theorem sims_condR : Claims.sims_condR := RouteS.sims_condR_route

/-! ### The paper's run and Proposition S4.8 (ii)–(iii) (Y24–Y26) -/

theorem genuine_paperrun : Claims.genuine_paperrun := RouteR.genuine_paperrun_route
theorem genuine_run_exists : Claims.genuine_run_exists := RouteR.genuine_run_exists_route
theorem newrates_ii_exp : Claims.newrates_ii_exp := RouteR.newrates_ii_exp_route
theorem newrates_iii_gauss : Claims.newrates_iii_gauss := RouteR.newrates_iii_gauss_route

/-! ### Checks: each theorem proves exactly its frozen claim, with the standard axioms only -/

example : Claims.banach_indicatrix_le := banach_indicatrix_le
example : Claims.banach_indicatrix := banach_indicatrix
example : Claims.layer_cake01 := layer_cake01
example : Claims.laplace_h1 := laplace_h1
example : Claims.laplace_h1_char := laplace_h1_char
example : Claims.lap_intervals := lap_intervals
example : Claims.lap_bv := lap_bv
example : Claims.lap_err := lap_err
example : Claims.lap_const := lap_const
example : Claims.condR_facts := condR_facts
example : Claims.lap_ratio := lap_ratio
example : Claims.lap_clip := lap_clip
example : Claims.lap_pop := lap_pop
example : Claims.lap_compare := lap_compare
example : Claims.lap_dev := lap_dev
example : Claims.own_ramp := own_ramp
example : Claims.lap_own := lap_own
example : Claims.lap_fitted := lap_fitted
example : Claims.lap_fitted_fraction := lap_fitted_fraction
example : Claims.lap_bets := lap_bets
example : Claims.lap_rescale := lap_rescale
example : Claims.laplace_const_i := laplace_const_i
example : Claims.laplace_const_ii := laplace_const_ii
example : Claims.laplace_const_pr_i := laplace_const_pr_i
example : Claims.laplace_const_pr_ii := laplace_const_pr_ii
example : Claims.laplace_rate_i := laplace_rate_i
example : Claims.laplace_rate_ii := laplace_rate_ii
example : Claims.laplace_rate_improves := laplace_rate_improves
example : Claims.laplace_rate_grid := laplace_rate_grid
example : Claims.lap_local := lap_local
example : Claims.lap_local_Q := lap_local_Q
example : Claims.lap_local_c := lap_local_c
example : Claims.lap_local_d := lap_local_d
example : Claims.lower2pt_not_cross := lower2pt_not_cross
example : Claims.local_rate := local_rate
example : Claims.sims_condR := sims_condR
example : Claims.genuine_paperrun := genuine_paperrun
example : Claims.genuine_run_exists := genuine_run_exists
example : Claims.newrates_ii_exp := newrates_ii_exp
example : Claims.newrates_iii_gauss := newrates_iii_gauss

#print axioms banach_indicatrix_le
#print axioms banach_indicatrix
#print axioms layer_cake01
#print axioms laplace_h1
#print axioms laplace_h1_char
#print axioms lap_intervals
#print axioms lap_bv
#print axioms lap_err
#print axioms lap_const
#print axioms condR_facts
#print axioms lap_ratio
#print axioms lap_clip
#print axioms lap_pop
#print axioms lap_compare
#print axioms lap_dev
#print axioms own_ramp
#print axioms lap_own
#print axioms lap_fitted
#print axioms lap_fitted_fraction
#print axioms lap_bets
#print axioms lap_rescale
#print axioms laplace_const_i
#print axioms laplace_const_ii
#print axioms laplace_const_pr_i
#print axioms laplace_const_pr_ii
#print axioms laplace_rate_i
#print axioms laplace_rate_ii
#print axioms laplace_rate_improves
#print axioms laplace_rate_grid
#print axioms lap_local
#print axioms lap_local_Q
#print axioms lap_local_c
#print axioms lap_local_d
#print axioms lower2pt_not_cross
#print axioms local_rate
#print axioms sims_condR
#print axioms genuine_paperrun
#print axioms genuine_run_exists
#print axioms newrates_ii_exp
#print axioms newrates_iii_gauss

end StatFormal.Wave31tu
