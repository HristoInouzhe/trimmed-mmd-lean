import StatFormal.Wave30tw.RouteFull

/-!
# Wave 30tw — certified claims (continuity of the sharper threshold, `→ ∞`, the crossing set at the full `τ_{n,m}`)
-/

namespace StatFormal.Wave30tw

example : Claims.tails_continuous := tails_continuous
example : Claims.tails_strict := tails_strict
example : Claims.repair_tail_jump := repair_tail_jump
example : Claims.sharp_roots_continuous := sharp_roots_continuous
example : Claims.sharp_tau_continuous := sharp_tau_continuous
example : Claims.sharp_tau_tendsto := sharp_tau_tendsto
example : Claims.coupled_tau_continuous := coupled_tau_continuous
example : Claims.grid_tau_continuous := grid_tau_continuous
example : Claims.closed_candidates := closed_candidates
example : Claims.crossing_union_min := crossing_union_min
example : Claims.tauFull_continuous := tauFull_continuous
example : Claims.tauFull_tendsto := tauFull_tendsto
example : Claims.crossing_full_cont := crossing_full_cont
example : Claims.crossing_full_cpl := crossing_full_cpl
example : Claims.crossing_full_grid := crossing_full_grid

end StatFormal.Wave30tw
