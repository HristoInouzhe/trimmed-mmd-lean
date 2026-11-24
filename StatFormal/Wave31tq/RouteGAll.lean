import StatFormal.Wave31tq.RouteGRho
import StatFormal.Wave31tq.RouteGBand

/-!
# Wave 31tq, chunk G: the route theorems of the Gaussian block (Q14–Q17)

* Q14 `RouteG.bandlimited_angular_route : Claims.bandlimited_angular` (`RouteG.lean`);
* Q15 `RouteG.bbar_even_route : Claims.bbar_even` (`RouteG.lean`), `RouteG.bandB_facts_route : Claims.bandB_facts`
  (`RouteGBand.lean`);
* Q16 `RouteG.newgaussstep_of (htv : Claims.tv_density) : Claims.newgaussstep` (`RouteGStep.lean`);
* Q17 `RouteG.newgauss_thm_of (htv : Claims.tv_density) : Claims.newgauss_thm` (`RouteGThm.lean`) and
  `RouteG.newgauss_thm_rho_of (htv : Claims.tv_density) : Claims.newgauss_thm_rho` (below, from `RouteGRho.lean` with the
  density facts of `bandB_facts_route`).

The only cross-chunk hypothesis is Q1 `Claims.tv_density` (chunk A), used through its part (b) (the error of a function for
Lebesgue densities, `|P − Q| = |p − q|·Leb`, `α⋆ = ∫ (p − q)₊`).
-/

namespace StatFormal.Wave31tq.RouteG

/-- Q17 `newgauss_thm_rho`, with Q1(b) (`Claims.tv_density`, chunk A) as a hypothesis. -/
theorem newgauss_thm_rho_of (htv : Claims.tv_density) : Claims.newgauss_thm_rho :=
  newgauss_thm_rho_of_facts htv bandB_facts_route

end StatFormal.Wave31tq.RouteG
