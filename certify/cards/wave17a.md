# Fidelity card — wave 17a: A rt-visible; B cocycle, interior levels; C pop-content, net inner band; paper2 predline; TM separation, rffjoint; NN noncentral tube

Paper: `otfd/papers/A_sieves/supplement.tex:4175`; `B_bands/supplement.tex:5530`, `:929`; `C_conditional/main.tex:641`,
`supplement.tex:1581`; `robust-equality-outcomes-under-distribution-shift/paper2/` `:385` (proof `app_proofs.tex:118-124`);
`trimmed-mmd/paper.tex:1082`, `:1705`; `proliferation-and-geometry-in-nns` `pr:907`.
Lean: `StatFormal/Archive/Wave17a/Statements.lean` (frozen), `Proofs.lean`, `Route*.lean` (9).
Critic (2026-10-15): ACCEPT / ACCEPT-WITH-NOTE, all 28 TRUE, no statement changes. **Author: approved (automatic on AI-audit PASS, per author decision 2026-10-21).**

## Certified
* A `lem:rt-visible` (2); B `prop:rk-transfer-cocycle` (3, extends Wave8c `transfer_cocycle`); B `lem:interior-levels`
  (3: naive, cubic iffs, vanishing).
* C `prop:conditional-pop-content` (1); C `prop:net-inner-band` (6: attained, (i)–(iv), edges) — complete (wave 16b had
  only the deterministic deficit/two-sided part).
* paper2 `prop:predline` (6): certificate, constant, constrained, penalised-not-a-shift counterexample, lookback,
  budget-one exclusion.
* TM `lem:separation` (3); TM `thm:rffjoint` (1) — **with `lem:rffkernel` as premise** (then uncertified, L3; `lem:rffkernel`
  certified in Wave24e, WaveP2d; premise discharged in WaveP2d `rffjoint_uncond`).
* NN `prop:noncentral-tube` (3): affine core, `λ_s`, instance.

## Paper defect (DEFECTS #60, S2)
paper2 `prop:predline`(i) proof: "the budget term does not depend on `h`, so it adds a constant to `(P_η)`" is false
(`(Δ+c)²` has an `h`-dependent cross term); `(C_δ)` is unaffected.

## Not covered
B interior-levels ball reference (needs the Hilbert Gaussian law); paper2 predline (ii) (not a theorem in the paper).

## Closed by later waves
* TM `lem:rffkernel` (assumed): Wave24e (`rff_unbiased`, `rff_finite`), WaveP2d (`rff_sup`).

## Route
Hilbert-basis projections; null-preimage versions; cubic volume bounds; Tau Ceti subdifferentials; frozen TM concentration.

## Fidelity review
Independent AI audit, method v1 (certify/AUDIT_METHOD.md), 2026-10-27 — PASS with notes (28 targets, each claim back-translated blind and compared with the printed text).
Notes: All 28 claims faithful. Cosmetic: card/Statements line refs stale (A lem:rt-visible supplement.tex:5198; B cocycle supplement.tex:4579, interior-levels :2366; C pop-content main.tex:716, net-inner-band supplement.tex:2091; paper2 predline main.tex:390; TM separation paper.tex:982, rffjoint :1673; NN :906). Statements docstring still says 'DRAFT'. predline_penalised_not_shift targets a proof step that the paper has since corrected (DEFECTS #60): the printed (i) now says '(P_eta) penalises a function of that disparity alone', with which the claim is consistent. rffjoint is conditional on lem:rffkernel (declared; the coverage note cites the discharge in WaveP2d).
