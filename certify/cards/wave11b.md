# Fidelity card — wave 11b: SB `thm:flow`; TM `lem:attainment`; ICL `lem:cond-nonunique`, `prop:swor-score`

Paper: `data-fairness-repair/schrodinger_bridge_fairness_repair.tex:537` (`thm:flow`); `trimmed-mmd/paper.tex:672`
(`lem:attainment`); `context-distribution-ICL` `pc:223` (`lem:cond-nonunique`), `ps:346` (`prop:swor-score`).
Lean: `StatFormal/Archive/Wave11b/Statements.lean` (frozen), `Proofs.lean`, `Route{Flow,Attain,Nonunique,Swor}.lean`.
Critic (2026-10-14): ACCEPT-WITH-NOTE, all 20 TRUE, no statement changes. **Author: approved (automatic on AI-audit PASS, per author decision 2026-10-21).**

## Certified
* SB `thm:flow` (7): mixture is a probability law; (i) push-forward; (ii) monotone on `{0 < F_R < 1}` (full measure),
  optimal, cost; (iii) minimality; (iv) uniqueness given the ODE (hypothesis).
* TM `lem:attainment` (7): region convex, bounded, weakly compact (`WeakSpace`), closed; (i) infimum attained;
  (ii) zero iff and common points (characteristicness). (A2) not needed (Pettis).
* ICL `lem:cond-nonunique` (1): non-uniqueness of conditional minimisers, fair witness `[0,1] × {0,1}` with
  Lebesgue ⊗ uniform (meets every standing assumption; not the paper's own witness).
* ICL `prop:swor-score` (5): collision probability `≤ M(M−1)s₊/(2s₋n)`, score form, perturbation, CPS = iid law
  conditioned on distinct indices, value bound `C₀/n` with explicit `C₀ = 2M(M−1)(s₊/s₋)(B_L + ΛK_max/K_min)`.

## Paper note (DEFECTS #44, S4)
ICL `proofs_score.tex:5-6`: "`J^iid_{n,m}` differs from `J^iid_{n,m}`" — the first should be `J_{n,m}`.

## Not covered
SB `thm:flow`(iv) ODE part (strict increase, transport of `R_s`); TM T1-8 norm-compactness remark (not paper text);
ICL `prop:swor-score` derivative bounds `C₁/n`, `C₂/n` and the transfer to `thm:score`.
## Route
Quantile flows; Hilbert-space weak compactness; clopen-cell witness; collision counting for SWOR vs iid.

## Fidelity review
Independent AI audit, method v1 (certify/AUDIT_METHOD.md), 2026-10-27 — PASS with notes (20 targets, each claim back-translated blind and compared with the printed text).
Notes: Stale locators: card/Statements cite SB :537 (now thm:flow at l.559), TM paper.tex:672 (now l.562), ICL v3 pc:223/ps:346 (now v4 supp/proofs_conditional.tex:321, supp/proofs_score.tex:568); Statements docstring still points to paper/v3. DEFECTS #44 typo ('J^iid differs from J^iid') is fixed in v4 (now reads 'J_{n,m} differs from J^iid_{n,m}'). Card 'Not covered' list (thm:flow(iv) ODE part, swor derivative bounds) is now superseded by later waves (Wave30bo, WaveP1d/29i/29v/30x) — card could say so. Coverage note for thm:flow cites tex:558 (label at 559).

## Addendum 2026-10-31 (paper commit 7ac2285 and wave 30dr)
lem:cond-nonunique is unchanged. The remark after the proof of prop:cond-target ("For M ≥ 3 the two lemmas leave a gap …") now continues with
the new Lemma lem:cond-threshold (certified in wave 30dr, which reuses this card's witness space [0,1] × {0,1} and its lemmas `kl_cell`, `rep_T2`).
