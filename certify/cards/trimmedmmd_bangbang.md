# Fidelity card — trimmed MMD: extreme trimmed means and the bang-bang trimming (W1.7)

Paper: `trimmed-mmd/paper.tex:1100-1120` (`lem:trimmedmean`), `:1380-1420` (`prop:bangbang`).
Lean: `StatFormal/Archive/TrimmedMMD/BangBang/Statements.lean` (frozen), `Proofs.lean`.
Critic (batch 3): FAITHFUL / FAITHFUL-WITH-NOTES. **Author: approved (automatic on AI-audit PASS, per author decision 2026-10-21).**

## Certified (status: see gate output)
* `trimmedmean_value`: the maximum over `Δ_α(n)` is the extreme trimmed mean, incl. the case `k = n` (α = 0).
* `trimmedmean_argmax`: structure of every maximiser, incl. ties and the residual mass.
* `bangbang_i`: minimisers exist; the witness `d̂` is the same at every minimiser.
* `bangbang_ii`: if `D̂ > 0`, every minimiser is bang-bang w.r.t. the witness values (threshold the
  `(k_n+1)`-th smallest), ties share the residual `1 − c#{<}`; symmetric statement for `v`.

## Encoding / not covered
Abstract real inner-product space for the feature map; order statistics via `Tuple.sort`.
Not covered: (i)'s "minimum-norm element of C − C'" phrasing (implied), (iii), `v` residual mass, `prop:selection`.

## Fidelity review
Independent AI audit, method v1 (certify/AUDIT_METHOD.md), 2026-10-27 — PASS with notes (4 targets, each claim back-translated blind and compared with the printed text).
Notes: Card line refs stale (lem:trimmedmean paper.tex:1002, prop:bangbang :1323). Card 'Not covered: v residual mass' is outdated: bangbang_ii does include the v residual mass (under-claim only).
