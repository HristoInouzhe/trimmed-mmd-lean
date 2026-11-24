import StatFormal.Wave31to.Statements
import StatFormal.Wave31to.RouteA
import StatFormal.Wave31to.RouteB
import StatFormal.Wave31to.RouteC
import StatFormal.Wave31to.RouteD

/-!
# Wave 31to: proofs of the frozen claims (trimmed-mmd AoS revision of 2026-11-21, general results)

Each theorem's type is literally the frozen `Claims.*` Prop of `StatFormal/Wave31to/Statements.lean`; the routes are `RouteA`
(trimmed means, the err identities, `prop:newapproxgen` (i)–(ii)), `RouteB` (`prop:newapproxgen` (iii), `prop:newapprox`), `RouteC`
(`prop:newslopegeneral`, `prop:newslope`), `RouteD` (`prop:newrates` (i)–(ii), `prop:newconverse`).
-/

namespace StatFormal.Wave31to

theorem newtrimmean : Claims.newtrimmean := RouteA.newtrimmean_route
theorem newapproxgen_i : Claims.newapproxgen_i := RouteA.approxgen_i_route
theorem newapproxgen_ii : Claims.newapproxgen_ii := RouteA.approxgen_ii_route
theorem newapproxgen_iii_a : Claims.newapproxgen_iii_a := RouteB.iii_a
theorem newapproxgen_iii_b : Claims.newapproxgen_iii_b := RouteB.iii_b
theorem newapprox_a : Claims.newapprox_a := RouteB.approx_a
theorem newapprox_b : Claims.newapprox_b := RouteB.approx_b
theorem newapprox_err : Claims.newapprox_err := RouteA.newapprox_err_route
theorem newslopegeneral : Claims.newslopegeneral := RouteC.newslopegeneral_route
theorem newslope_a : Claims.newslope_a := RouteC.newslope_a_route
theorem newslope_b : Claims.newslope_b := RouteC.newslope_b_route
theorem newrates_i : Claims.newrates_i := RouteD.newrates_i_route
theorem newrates_i_full : Claims.newrates_i_full := RouteD.newrates_i_full_route
theorem newrates_ii_a : Claims.newrates_ii_a := RouteD.newrates_ii_a_route
theorem newrates_ii_b : Claims.newrates_ii_b := RouteD.newrates_ii_b_route
theorem newconverse : Claims.newconverse := RouteD.newconverse_route

example : Claims.newtrimmean := newtrimmean
example : Claims.newapproxgen_i := newapproxgen_i
example : Claims.newapproxgen_ii := newapproxgen_ii
example : Claims.newapproxgen_iii_a := newapproxgen_iii_a
example : Claims.newapproxgen_iii_b := newapproxgen_iii_b
example : Claims.newapprox_a := newapprox_a
example : Claims.newapprox_b := newapprox_b
example : Claims.newapprox_err := newapprox_err
example : Claims.newslopegeneral := newslopegeneral
example : Claims.newslope_a := newslope_a
example : Claims.newslope_b := newslope_b
example : Claims.newrates_i := newrates_i
example : Claims.newrates_i_full := newrates_i_full
example : Claims.newrates_ii_a := newrates_ii_a
example : Claims.newrates_ii_b := newrates_ii_b
example : Claims.newconverse := newconverse

end StatFormal.Wave31to
