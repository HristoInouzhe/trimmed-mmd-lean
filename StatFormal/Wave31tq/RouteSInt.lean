import StatFormal.Wave31tq.Statements
import StatFormal.Lib.MollifierNorm.Intervals

/-!
# Wave 31tq, route S: the translation bound for finite unions of intervals (untrusted proof file)

Q9 `translation_intervals` (S4 :533-535, the `ℝ` part): `Leb(E △ (E + h)) ≤ 2N|h|` for a union of `N` intervals, from
`Lib/MollifierNorm/Intervals.lean` (one interval: the exit set has diameter `≤ |h|`; unions: subadditivity).
-/

namespace StatFormal.Wave31tq.RouteS

theorem translation_intervals_route : Claims.translation_intervals :=
  fun N I hI h => StatFormal.MollifierNorm.volume_symmDiff_iUnion_translate_le N I hI h

end StatFormal.Wave31tq.RouteS
