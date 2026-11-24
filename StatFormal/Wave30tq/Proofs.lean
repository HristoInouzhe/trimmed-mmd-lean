import StatFormal.Wave30tq.RouteLemmas
import StatFormal.Wave30tq.RouteLower

/-!
# Proofs: wave 30tq, trimmed-mmd (jmlr) — the finite-sample variance-adaptive split certificate (untrusted proof file)

Routes: `RouteLemmas` (Lemma 1, Lemma 2), `RouteIndep` (independence of the fold-two coordinates and of the block
statistics; the §2.3 pairing facts), `RouteBetting` (Theorem 1; library `Lib/Betting/Ville.lean`,
`Lib/Betting/Wealth.lean`), `RouteEB` (Corollary 1; library `Lib/Bernstein/TwoSample.lean` and Maurer–Pontil Thm 10
`Lib/Bernstein/SampleVariance.lean`), `RouteLower` (Corollary 2; the certified `TrimmedMMD.Lower` combinatorics).
-/

namespace StatFormal.Wave30tq

theorem lem1_trim : Claims.lem1_trim := lem1_trim_route
theorem lem1 : Claims.lem1 := lem1_route
theorem lem1_null : Claims.lem1_null := lem1_null_route
theorem lem1_rkhs : Claims.lem1_rkhs := lem1_rkhs_route
theorem lem1_attain : Claims.lem1_attain := lem1_attain_route
theorem lem2_1 : Claims.lem2_1 := lem2_1_route
theorem lem2_2 : Claims.lem2_2 := lem2_2_route
theorem lem2_3 : Claims.lem2_3 := lem2_3_route
theorem lem2_4 : Claims.lem2_4 := lem2_4_route
theorem pair_facts : Claims.pair_facts := pair_facts_route
theorem thm1_cond : Claims.thm1_cond := thm1_cond_route
theorem thm1_condexp : Claims.thm1_condexp := thm1_condexp_route
theorem thm1 : Claims.thm1 := thm1_route
theorem cor1 : Claims.cor1 := cor1_route
theorem cor1_test : Claims.cor1_test := cor1_test_route
theorem cor1_lcb : Claims.cor1_lcb := cor1_lcb_route
theorem cor2 : Claims.cor2 := cor2_route

example : Claims.lem1_trim := lem1_trim
example : Claims.lem1 := lem1
example : Claims.lem1_null := lem1_null
example : Claims.lem1_rkhs := lem1_rkhs
example : Claims.lem1_attain := lem1_attain
example : Claims.lem2_1 := lem2_1
example : Claims.lem2_2 := lem2_2
example : Claims.lem2_3 := lem2_3
example : Claims.lem2_4 := lem2_4
example : Claims.pair_facts := pair_facts
example : Claims.thm1_cond := thm1_cond
example : Claims.thm1_condexp := thm1_condexp
example : Claims.thm1 := thm1
example : Claims.cor1 := cor1
example : Claims.cor1_test := cor1_test
example : Claims.cor1_lcb := cor1_lcb
example : Claims.cor2 := cor2

end StatFormal.Wave30tq
