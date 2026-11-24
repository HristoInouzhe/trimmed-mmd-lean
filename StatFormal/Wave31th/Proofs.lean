import StatFormal.Wave31th.RouteCore
import StatFormal.Wave31th.RouteSpec

/-!
# Proofs: wave 31th, trimmed-mmd (jmlr) v3, `rem:qdens` in every dimension (untrusted proof file)

Every claim of `StatFormal/Wave31th/Statements.lean` is proved as `theorem StatFormal.Wave31th.<claim>`:
`qdens_euclid` and the local chart/density routes (`RouteChart`, `RouteDensity`, `RouteCorePi`, `RouteCore`), `gaussian_regular`
(`RouteGauss`), and the three Gaussian claims `qdens_gauss_Q`, `qdens_gauss_Qprime`, `qdens_gauss_Q_Qprime` (`RouteCore`). The gate checks
`example : Claims.c := c` and the axioms.
-/

namespace StatFormal.Wave31th

example : Claims.qdens_euclid := qdens_euclid
example : Claims.gaussian_regular := gaussian_regular
example : Claims.qdens_gauss_Q := qdens_gauss_Q
example : Claims.qdens_gauss_Qprime := qdens_gauss_Qprime
example : Claims.qdens_gauss_Q_Qprime := qdens_gauss_Q_Qprime

end StatFormal.Wave31th
