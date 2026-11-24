# Fidelity card — wave 8a: SB `lem:sharp`; TM `prop:georep`, `lem:cvar`

Paper: `data-fairness-repair/schrodinger_bridge_fairness_repair.tex:901` (`lem:sharp`); `trimmed-mmd/paper.tex:653`
(`prop:georep`, proof `supplement.tex:66-77`), `:699-708` (`lem:cvar`).
Lean: `StatFormal/Archive/Wave8a/Statements.lean` (frozen), `Proofs.lean`, `Route{Sharp,Georep,Cvar}.lean`.
Critic (2026-10-14): ACCEPT-WITH-NOTE, all 12 TRUE, no statement changes. **Author: approved (automatic on AI-audit PASS, per author decision 2026-10-21).**

## Certified
* SB `lem:sharp` (5): measurable barycentric map `T = E[X₁|X₀]` exists; `T#R = ν ⇔ E‖X₁ − T(X₀)‖² = 0 ⇔ π` is a graph;
  `⇔ E Var(X₁ⁱ|X₀) = 0` for every coordinate; with a density `> 0` against `R⊗ν`, `T#R = ν ⇔ ν` Dirac; the entropic plan
  exists and the Dirac iff holds for marginals carried by a ball (cost `‖x−y‖² + εKL`, paper's `ε` ↔ `2ε`).
* TM `prop:georep` (5): embeddings of the trimmings `R_α(P)` (via `rnDeriv`) are exactly the region; `eq:setdist`;
  the empirical region is the capped-simplex polytope (ties allowed); `D̂²` is the attained minimum of `eq:qp`; the
  weight map `g ↦ (g(X_i)/n)` is not onto the capped simplex under ties (documentation claim).
* TM `lem:cvar` (2): support function = sup = CVaR infimum, both attained, for `f ∈ H` and for bounded measurable `f`.

## Paper notes
SB `lem:sharp` omits `ass:ac` (S3, DEFECTS #39); `eq:static` posed on `𝒫₂(ℝ)` vs `R_s ∈ 𝒫₂(ℝ^d)` (S4). TM
`prop:georep` proof: tie groups should be classes of measurably inseparable points (minor S2); `paper.tex:603` wording
(S4). `lem:cvar`: DEFECTS #22 / review T2-6 fixed in the current text.

## Not covered
`sharp_entropic` for general `𝒫₂` marginals (Tau Ceti's entropic transport needs bounded costs).
## Route
Conditional expectation and law of total variance; graph supports; Tau Ceti `entropicTransportCost`; tie-group averaging.

## Fidelity review
Independent AI audit, method v1 (certify/AUDIT_METHOD.md), 2026-10-27 — PASS with notes (12 targets, each claim back-translated blind and compared with the printed text).
Notes: Card line refs stale (SB lem:sharp now schrodinger_bridge_fairness_repair.tex:919; prop:georep paper.tex:543; lem:cvar :589). The card's SB paper note (lem:sharp omits ass:ac) is now applied in the text ('Under Assumption ass:ac'). 'Two convex polytopes' convexity is declared not covered but is immediate (and lem:attainment convexity is certified elsewhere); COVERAGE 'certified as printed' for prop:georep is acceptable.
