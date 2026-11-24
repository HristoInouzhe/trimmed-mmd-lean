import StatFormal.Wave30tv.RouteClaims

/-!
# Proofs: wave 30tv, trimmed-mmd (jmlr) — the sequential (batch) split certificate, v2 seq (untrusted proof file)

Routes: `RouteCoord` (functions of a set of coordinates; the freezing lemma), `RouteSeq` (the filtration over the
pairs and the core level bound, library `Lib/Betting/Predictable.lean` on top of `Lib/Betting/Ville.lean`),
`RouteClaims` (the six claims; 30tq `prod_le_of_slices`, `delta_le_tv`, `lem2_1_route`, the certified
`TrimmedMMD.Lower.downclosed_measurable_le`).
-/

namespace StatFormal.Wave30tv

theorem lem_ramp_iii : Claims.lem_ramp_iii := lem_ramp_iii_route
theorem thm_betting_cond : Claims.thm_betting_cond := thm_betting_cond_route
theorem thm_betting_condexp : Claims.thm_betting_condexp := thm_betting_condexp_route
theorem thm_betting : Claims.thm_betting := thm_betting_route
theorem cor_lower : Claims.cor_lower := cor_lower_route
theorem single_split : Claims.single_split := single_split_route

example : Claims.lem_ramp_iii := lem_ramp_iii
example : Claims.thm_betting_cond := thm_betting_cond
example : Claims.thm_betting_condexp := thm_betting_condexp
example : Claims.thm_betting := thm_betting
example : Claims.cor_lower := cor_lower
example : Claims.single_split := single_split

end StatFormal.Wave30tv
