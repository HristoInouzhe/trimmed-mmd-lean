# Fidelity card — trimmed MMD: `thm:impossible`

Paper: `trimmed-mmd/paper.tex` (`thm:impossible`), proof `supplement.tex:442-484`.
Lean: `StatFormal/Archive/TrimmedMMD/Impossible/Statements.lean` (frozen; imports locked `Foundations/Distances/TV.lean`),
`Cells.lean`, `Counting.lean`, `Mixture.lean`, `Proofs.lean`.
Critic (batch 6): ACCEPT, TRUE (for every `n, m, δ`). **Author: approved (automatic on AI-audit PASS, per author decision 2026-10-21).**

## Certified
`impossible`: a (possibly randomised) `Û(X_{1:n}, Y_{1:m}, ξ)` with `Pr_{P,Q}(TV(P,Q) ≤ Û) ≥ 1 − δ` for every pair of
laws with bounded densities on `[0,1]` satisfies `Pr_{P₀,P₀}(Û ≥ 1) ≥ 1 − δ`.

## Encoding
Bounded density on `[0,1]`: `P ≤ C·λ|_{[0,1]}`; randomiser `ξ` of arbitrary law on an arbitrary space, independent of the data;
TV = sup over sets (`½∫|p − q|`).
## Route (differs from the paper's construction)
Block construction instead of a random subset of cells: `[0,1)` cut into `K` blocks of `L` cells; `Q_σ` uniform on one cell
per block (`TV(P₀,Q_σ) ≥ 1 − 1/L`); on the event that the `m` held-out points fall in distinct blocks the uniform mixture over
`σ` has density exactly 1 w.r.t. `P₀^m` (complement mass `≤ m²/K`, vs the paper's `m(m−1)/((1−c)M)`); one-sided domination +
disintegration along `Y` (no TV-of-mixture bound); `K → ∞`, then `L → ∞` by continuity from above.

## Fidelity review
Independent AI audit, method v1 (certify/AUDIT_METHOD.md), 2026-10-27 — PASS (1 targets, each claim back-translated blind and compared with the printed text).
Notes: Route differs from the paper (block construction), declared.
