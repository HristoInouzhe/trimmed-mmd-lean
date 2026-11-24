# Fidelity card — wave 24a (QUEUE rows 310–329): G `lem:randomisation`; B `prop:jensen`, `lem:lin-lipschitz`, `cor:band-saturation-limit`, `prop:rk-paths`, `thm:consistency`; TM `prop:sinkmono`, `lem:tcompact`; C `cor:conditional-uniform-x`, `lem:neural-law-to-map`; T `eq:basebridge`; A `prop:parsimony`, `cor:app-bijective-rate`(a), `cor:app-entropic-rate`, `thm:consistency`, `cor:app-hard-envelope`

Lean: `StatFormal/Archive/Wave24a/Statements.lean` (frozen), `Proofs.lean`, `Route*.lean` (12).
Critic (2026-10-16): ACCEPT, 24 claims TRUE, none tautological. Removed: `band_saturation_limit` (the frozen Wave 22b
`cert_band_consistency` at `xbar := xsat` plus one `le_trans`, a restatement). **Author: approved (automatic on AI-audit PASS, per author decision 2026-10-21).**

## Covered
* G `lem:randomisation` (any finite group action, not only permutations): `randomisation_full`, `randomisation_mc`.
* B `prop:jensen`; `lem:lin-lipschitz` (+ 𝒫^ℓ form); `cor:band-saturation-limit` sandwich; `prop:rk-paths` (monotone,
  level labels, consistency; not an instance of frozen `band_boundary_mono`); `thm:consistency` (`consistency_B`).
* TM `prop:sinkmono` (`trimSet_mono`, `sinkmono`), `lem:tcompact`.
* C `cor:conditional-uniform-x` (maps and bands, on the frozen Wave 21b result), `lem:neural-law-to-map` (W₁ ⇒ L², uniform).
* T `eq:basebridge`: abstract two-leg skeleton with C_b, L_b and the transport bound as hypotheses (not tautological).
* A `prop:parsimony` tolerance (McDiarmid) and its limit; `cor:app-bijective-rate`(a), `cor:app-entropic-rate` with
  S(K_n) → 0 proved from the frozen WaveL3 `sieve_strong_limit_uncond`; `thm:consistency` (`consistency_A`);
  `cor:app-hard-envelope`.

## Conditions
1. `consistency_A`, `consistency_B`: Ghosal–Sen uniform map convergence on the given set 𝒦 only (the literature gives it
   for compact 𝒦 ⊂ int 𝒴_K; all of ℝ^K needs their part (c)).
2. Uniform-x claims: x-uniform potential convergence on a compact S_r ⊆ O.
3. Sieve claims conclude with a lower integral (= the expectation when the selections are measurable).
Light but genuine: `jensen`, `trimSet_mono`, `sinkmono`, `consistency_A`, `rk_paths_mono`.

## Paper notes (strengthenings, no defect)
`prop:parsimony`: the one-sided tail suffices (log(2/γ) → log(1/γ)); the uniform-x step needs no convexity of the fitted potentials.

## Skipped / not covered
paper2 `prop:uniform` (duplicate of a certified JASA claim); SB `prop:kernelexact` (definitional); A `prop:curse`
(entropic maps / Rigollet–Stromme for general laws missing); C `prop:metric-uniform-localization` (needs a uniform
self-localization result). Gaps: parsimony's `prop:selector`(ii) dependence; sharp Minkowski form and (b) of the bijective
corollary; B whitening step; strictness clause of rk-paths (i).

## Fidelity review
Independent AI audit, method v1 (certify/AUDIT_METHOD.md), 2026-10-27 — PASS with notes (24 targets, each claim back-translated blind and compared with the printed text).
Notes: Card source line numbers are stale (e.g. G lem:randomisation now supplement.tex:1824, B labels in supplement.tex 685/906/939/1579/4171, C supplement.tex 1540/1767, T supplement.tex:1094, A supplement.tex 633/3258/4284/4788/6736; TM prop:sinkmono is in trimmed-mmd/entropic.tex:146). Conditional claims (consistency_A/B, conditional_uniform_x*) and the abstract skeletons (basebridge, app_hard_envelope) are declared on the card.
