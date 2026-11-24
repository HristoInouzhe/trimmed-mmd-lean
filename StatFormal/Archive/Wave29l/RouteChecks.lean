import StatFormal.Archive.Wave29l.Statements
import StatFormal.Archive.Wave29l.RouteBootSE
import StatFormal.Archive.Wave29l.RouteBootPerc

/-! Route checks (non-target): frozen + discharge ⇒ new, and a `splitAss` instance. -/

namespace StatFormal.Wave29l
-- The bootstrap-SE certificate goes through the frozen conditional `Wave29i.split_level_boot`.
example : StatFormal.Wave29i.Claims.split_level_boot → Claims.split_boot_se → Claims.split_level_bootstrap :=
  split_boot_check
-- The percentile certificate goes through the frozen `Wave29i.split_asymp_normal` and `Wave22c.split_level`.
example : StatFormal.Wave29i.Claims.split_asymp_normal → Claims.split_boot_clt →
    StatFormal.Wave22c.Claims.split_level → Claims.split_boot_percentile :=
  split_perc_check
-- Non-vacuity: the hypotheses are those of the frozen `split_level_discharged`; reuse the `ass:split` instance
-- (`splitAss ⇒ splitUQ` by the frozen `split_ass_unique`, so the `splitUQ` claims are non-vacuous too).
example : StatFormal.Wave29i.splitAss (MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 1)) id (1/2) (1/2) :=
  StatFormal.Wave29i.splitAss_uniform
end StatFormal.Wave29l
