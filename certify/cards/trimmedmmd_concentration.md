# Fidelity card — trimmed MMD: `thm:concentration`, `cor:uniform`

Paper: `trimmed-mmd/paper.tex:546` (ass:regularity), `:629` (eq:region), `:765` (thm:concentration), `:785` (cor:uniform);
proof in the supplement (eq:reduction, eq:hormander, eq:cvar, lem:tcompact).
Lean: `StatFormal/Archive/TrimmedMMD/Concentration/Statements.lean` (frozen; imports locked), `Region.lean`, `Proofs.lean`;
library `StatFormal/Lib/Concentration/` (symmetrisation, contraction, McDiarmid, `tm_concentration`).
Critic (batch 10): concentration ACCEPT-WITH-NOTE, uniform_* REVISE → measurable-event form applied. **Author: approved (automatic on AI-audit PASS, per author decision 2026-10-21).**

## Certified
* `concentration`: for every `α ∈ [0,1)`, `n ≥ 1`, `δ ∈ (0,1)` there is a measurable event of probability `≥ 1 − δ` on which
  `d_H(𝒞_{α,k}(P_n), 𝒞_{α,k}(P)) ≤ κ/(1−α)·[4/√n + √(2log(2/δ)/n)]`.
* `uniform_alpha`: one measurable event, probability `≥ 1 − δ`, on which the bound holds for every `α ∈ [0,1)` at once.
* `uniform_sup`: on such an event, `sup_{α ≤ 1−η} d_H(…) ≤ r_n(1−η, δ)`.

## Encoding
RKHS via a separable Hilbert space and strongly measurable feature map `‖φ‖ ≤ κ` (implied by A1–A2 via Pettis; A3 unused);
`𝒞_{α,k}(P)` with bounded measurable densities (same set as L^∞); `P_n` empirical; `d_H` = `Metric.hausdorffDist` (no junk: regions
nonempty, κ-bounded); probability as ∃ measurable event (critic: the outer-measure form would be weaker for cor:uniform).
## Route
The paper's: CVaR representation of the support function with `t ∈ [−κ,κ]` (explicit quantile witness), Hörmander (≤ half, via
projection onto the closed convex region), reduction `d_H ≤ (1−α)⁻¹ sup_𝒢|(P_n−P)g|` over `𝒢 = {(⟨f,φ⟩−t)₊}`; symmetrisation +
contraction (`E sup ≤ 4κ/√n`) + McDiarmid at `δ/2` per side; countable dense subclass for measurability.

## Added 2026-10-14: zero set and `α* = TV(P,Q)` (`TrimmedMMD/ZeroSet`)
* `tvintersect` (`eq:tvintersect`): `TV ≤ α ⇔` common `α`-trimming. `zero_of_tv_le`: `TV ≤ α < 1 ⇒ D_α = 0` (no A3).
* `zeroeq` (`eq:zeroeq`): characteristic feature map ⇒ `D_α = 0 ⇔ TV ≤ α`. The forward direction's attainment is proved without
  weak topology: decreasing nonempty closed convex bounded sets in a Hilbert space have nonempty intersection (minimal-norm points
  are Cauchy), applied to pairs of trimming densities in `L²(P) × L²(Q)`.
* `consistency_tv`, `consistency_tv_zero`: `thm:consistency` (i) at the paper's `α* = TV(P,Q)` (TV < 1), unconditionally, without A3.
Critic: ACCEPT ×4 (+ the optional α* = 0 corollary added).

## Added 2026-10-14 (queue wave 1): `cor:lower` (`TrimmedMMD/Lower`)
`downclosed_pathwise`, `downclosed_measurable_le`, `cor_lower`: the down-closed lower bound `α̂_lo` exceeds `TV(P,Q)` only if a
true null is rejected, so `limsup P_N(α̂_lo > TV) ≤ δ` given `thm:split` (hypothesis). Certified content = pathwise inclusion +
limsup monotonicity; "rejection certifies TV > α" is not used. Critic: ACCEPT-WITH-NOTE.

## Fidelity review
Independent AI audit, method v1 (certify/AUDIT_METHOD.md), 2026-10-27 — PASS with notes (16 targets, each claim back-translated blind and compared with the printed text).
Notes: Card line refs stale (thm:concentration paper.tex:666, eq:radius 681, cor:uniform 699). The card body does not list the four Unconditional targets (events, consistency_i, consistency_i_zero, rate) filed under it; add a line. Lower/Statements.lean header still says 'DRAFT, not yet in lock' (cosmetic). Empirical-region encoding: measurable g on 𝒳; with strongly measurable φ the region of P_n equals the capped-simplex polytope even for non-separating σ-algebras (non-separated points share φ).
