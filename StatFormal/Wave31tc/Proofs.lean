import StatFormal.Wave31tc.RouteCore

/-!
# Proofs: wave 31tc, trimmed-mmd (jmlr) v3, `rem:qdens` (untrusted proof file)

Every claim of `StatFormal/Wave31tc/Statements.lean` is proved in `RouteCore`, as `theorem StatFormal.Wave31tc.<claim>`:
`level_compact`, `qdens_univariate`, `qdens_formula`, `qdens_Q_Qprime`. The gate checks `example : Claims.c := c` and the axioms.
-/

namespace StatFormal.Wave31tc

example : Claims.level_compact := level_compact
example : Claims.qdens_univariate := qdens_univariate
example : Claims.qdens_formula := qdens_formula
example : Claims.qdens_Q_Qprime := qdens_Q_Qprime

end StatFormal.Wave31tc
