import StatFormal.Wave31tf.RouteSimple
import StatFormal.Wave31tf.RoutePositivity
import StatFormal.Wave31tf.RouteOverlap

/-!
# Proofs: wave 31tf, trimmed-mmd (jmlr) v3, six prose claims (untrusted proof file)

Every claim of `StatFormal/Wave31tf/Statements.lean` is proved in a route file, as `theorem StatFormal.Wave31tf.<claim>`:
`RouteSimple` — `linear_margin`, `gamma_ge_one`, `delta_schedule`, `consistency_schedule`, `consistency_schedule_full`,
`consistency_schedule_cpl`, `n_of_a_generic`, `no_uniform_accuracy`, `no_uniform_rate`; `RoutePositivity` — `n_of_a_full`, `n_of_a_cpl` (with the
positivity of the paper's `τ_{n,n}(0,δ)`); `RouteOverlap` — `strict_overlap`. The gate checks `example : Claims.c := c` and the axioms.
-/

namespace StatFormal.Wave31tf

example : Claims.linear_margin := linear_margin
example : Claims.gamma_ge_one := gamma_ge_one
example : Claims.delta_schedule := delta_schedule
example : Claims.consistency_schedule := consistency_schedule
example : Claims.consistency_schedule_full := consistency_schedule_full
example : Claims.consistency_schedule_cpl := consistency_schedule_cpl
example : Claims.n_of_a_generic := n_of_a_generic
example : Claims.n_of_a_full := n_of_a_full
example : Claims.n_of_a_cpl := n_of_a_cpl
example : Claims.no_uniform_accuracy := no_uniform_accuracy
example : Claims.no_uniform_rate := no_uniform_rate
example : Claims.strict_overlap := strict_overlap

end StatFormal.Wave31tf
