import StatFormal.Wave31tq.RouteM21
import StatFormal.Wave31tq.RouteM22
import StatFormal.Wave31tq.RouteM25
import StatFormal.Wave31tq.RouteM26
import StatFormal.Wave31tq.RouteM27
import StatFormal.Wave31tq.RouteM28

/-!
# Wave 31tq, route M: all route theorems of chunk M (untrusted)

* Q21 `RouteM.newsobolev_of h1 hcor hmom`, `RouteM.newsobolev_E1_of h1 hcor hmom` (`RouteM21`);
* Q22 `RouteM.newgauss_of h1 hrho hmom hk`, `RouteM.newgauss_margin_of h1 hrho hmom hk` (`RouteM22`);
* Q25 `RouteM.rate_sobolev_split_of h1 hcor`, `RouteM.converse_poly_route`, `RouteM.lower_sobolev_A_of h1 hcor hmom h5`,
  `RouteM.slow_gauss_A_of h1 hrho hmom hk` (`RouteM25`);
* Q26 `RouteM.excess_sobolev_of h1 hcor hmom h5` (`RouteM26`);
* Q27 `RouteM.laplace_instances_of h1 hcor hmom h5 hk` (`RouteM27`);
* Q28 `RouteM.simulated_pairs_route` (`RouteM28`);

with `h1 : Claims.tv_density`, `h5 : Claims.sobolev_angular`, `hk : Claims.kernel_instances` (chunk A),
`hcor : Claims.newsobolev_cor_line` (chunk S), `hmom : Claims.newmoments` (chunk T), `hrho : Claims.newgauss_thm_rho` (chunk G).
-/
