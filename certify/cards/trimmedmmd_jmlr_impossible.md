# Fidelity card — wave 30tm: trimmed MMD (JMLR) `thm:impossible`, uniform density bound 2

Paper id `trimmed-mmd (jmlr)`. Source (`trimmed-mmd/jmlr/`, untracked working copy, read 2026-11-07, re-read after the 20:26
edit of `06_splitting.tex`, which moved the theorem by two lines and left its text unchanged): statement
`sections/06_splitting.tex:228-243` (`thm:impossible`, "No informative upper bound, even for bounded densities"; Theorem 21 in
the PDF), proof `appendix/B_split.tex:186-216`; `TV(P,Q) = sup_A |P(A) − Q(A)|` from `sections/03_regions.tex:17`. (The frozen
docstring of `Statements.lean` cites `06_splitting.tex:226-244` and `B_split.tex:186-225`, the pre-edit and approximate ranges; the
claim text is unaffected.)
Lean: `StatFormal/Wave30tm/Statements.lean` (approved 2026-11-07 before proving; imports only the frozen
`Archive/TrimmedMMD/Impossible/Statements.lean`, through it `Lib/Distances/TV.lean`, and Mathlib), routes `RouteCells.lean`,
`RouteMixture.lean`, `Route.lean`, `RouteDensity.lean`, `Proofs.lean`.
Reused, not copied: `StatFormal.TrimmedMMD.Impossible.dataLaw` (law `P^n ⊗ Q^m ⊗ R` of `(X_{1:n}, Y_{1:m}, ξ)`),
`StatFormal.Distances.tvDist`; the route reuses the archived `cellSet`, `Qσ`, `card_extensions`, `block`, `floor_div_lt`,
`mem_cellSet_iff'` (with `L = 2`).
Build: `lake build StatFormal.Wave30tm.Proofs` succeeds; `#print axioms` of each theorem: `[propext, Classical.choice, Quot.sound]`.
**Author: approved (automatic on AI-audit PASS, per author decision 2026-10-21).**

## Certified (3 claims)
* `impossible` — the theorem as printed: for every `n, m ≥ 1`, `δ ∈ (0,1)`, every randomiser law `R` on any measurable space
  `Ξ` and every measurable `Û(X_{1:n}, Y_{1:m}, ξ) ∈ ℝ`: if `Pr_{P,Q}(TV(P,Q) ≤ Û) ≥ 1 − δ` for every pair of probability
  measures on `[0,1]` with densities bounded by `2`, then `Pr_{P_u,P_u}(Û ≥ 1) ≥ 1 − δ`.
* `density2_iff` — encoding check: `Density2 P` (`P` a probability measure with `P ≤ 2 • λ|_{[0,1]}`) holds iff `P` is a
  probability measure `λ.withDensity f` for a measurable `f : ℝ → [0,∞]` with `f ≤ 2` everywhere and `f = 0` off `[0,1]`.
* `impossible_implies_archived` — sanity: the JMLR claim implies the long version's frozen `thm:impossible`
  (`TrimmedMMD.Impossible.Claims.impossible`, a finite density bound `C` per law), since `𝒫₂` is contained in that class.
  (The inclusion argument gives only this direction: the JMLR claim has the weaker coverage hypothesis.)

## Deviations and encodings (declared)
* **Encodings.** "Probability measure on `[0,1]` whose density w.r.t. Lebesgue measure is bounded by `2`": a probability measure
  `P` on `ℝ` with `P ≤ 2 • λ|_{[0,1]}` (`Density2`), the archived `BddDensity01` with its `∃ C` replaced by the fixed `2`;
  `density2_iff` certifies the equivalence with an explicit Lebesgue density `f ≤ 2` vanishing off `[0,1]` (an a.e.-bounded
  density has an everywhere-bounded version, so "bounded" in the a.e. and in the pointwise sense agree). `𝒫₂` is the product
  class (`Density2 P → Density2 Q → …`). "Possibly randomized": `Û` measurable in `(X_{1:n}, Y_{1:m}, ξ)`, `ξ` independent of the
  data with arbitrary law `R` on an arbitrary measurable space `Ξ : Type` (deterministic `Û`: `Ξ = Unit`); the data law is
  `dataLaw n m P Q R = (P^n ⊗ Q^m) ⊗ R`. `Û` is real-valued and defined on all of `ℝ^n × ℝ^m × Ξ` (all laws involved live on
  `[0,1]^{n+m}`, and a measurable `Û` of `[0,1]`-valued data extends measurably, so this costs nothing). `P_u` is `λ|_{[0,1]}`. `TV` is `tvDist` (`sup` over measurable sets
  of `|P(A) − Q(A)|`), the paper's `d_TV`. Probabilities are `Measure.real` of probability measures.
* **Generalisations.** None in the claim (the hypotheses `1 ≤ n`, `1 ≤ m`, `0 < δ < 1` are kept as printed; the proof uses only
  `δ ≥ 0`).
* **Specialisations / conditionalisations.** None.

## Junk-value audit
`Measure.real` = `toReal` of a probability measure's value: finite, no `toReal ∞`. No `Measure.map` in the statements
(`dataLaw` is a product of `Measure.pi`'s and `R`; the route's `measurePreserving_sumPiEquivProdPi` is a proof device). `tvDist` is a
`⨆` over the nonempty type of measurable sets of values in `[0,1]` for probability measures (bounded above, `bddAbove_tvDist`), so no
`iSup`-of-unbounded junk. No divisions, logs or square roots in the statements. Sets of measure zero: the class is defined by an
inequality of measures, insensitive to null modifications of the density; the cell boundaries of the construction are null.
`U` measurable makes both events measurable. Vacuity: the coverage hypothesis is satisfiable (`Û ≡ 1`: `tvDist ≤ 1`), the class
is nonempty (`P_u ∈ 𝒫₂`, and the route exhibits the mutually singular pairs `(P_σ, Q_σ) ∈ 𝒫₂`), and the claim is not trivial for
`δ ∈ (0,1)`.

## Back-translation
Let `n, m ≥ 1`, `δ ∈ (0,1)`, `(Ξ, R)` a probability space, `Û : ℝ^n × ℝ^m × Ξ → ℝ` measurable. Suppose that for all probability
measures `P, Q` on `ℝ` with `P ≤ 2λ|_{[0,1]}` and `Q ≤ 2λ|_{[0,1]}` (equivalently: concentrated on `[0,1]` with Lebesgue densities
`≤ 2`), with `X_i` i.i.d. `P`, `Y_j` i.i.d. `Q`, `ξ ∼ R` all independent, `Pr(sup_A |P(A) − Q(A)| ≤ Û(X, Y, ξ)) ≥ 1 − δ`. Then with
`X_i`, `Y_j` i.i.d. uniform on `[0,1]` and `ξ ∼ R` independent, `Pr(Û(X, Y, ξ) ≥ 1) ≥ 1 − δ`. Moreover this statement implies the
long version's (densities bounded by some finite constant depending on the law), and `P ≤ 2λ|_{[0,1]}` is exactly "Lebesgue density
`≤ 2` vanishing off `[0,1]`".

## Textbook bridges
None (Radon–Nikodym for `density2_iff` is Mathlib's `withDensity_rnDeriv_eq`).

## Route (differs from the paper's construction)
Block construction instead of a uniformly random half of `M` cells: `[0,1)` is cut into `K` blocks of `2` cells; for
`σ : Fin K → Fin 2`, `P_σ` is uniform on the chosen cell of every block and `Q_σ` on the other one (densities `2·1_{S_σ}` and
`2·1_{S_σ^c}`, mutually singular, `TV ≥ |P_σ(S_σ) − Q_σ(S_σ)| = 1`), so `Pr_{P_σ,Q_σ}(Û < 1) ≤ δ` for every `σ`. The `n + m`
observations are indexed by `Fin n ⊕ Fin m` (`measurePreserving_sumPiEquivProdPi`) and the data law is disintegrated along the data.
On the event `E_K` that all `n + m` points lie in `[0,1)` in pairwise distinct blocks, the uniform mixture over `σ` of
`P_σ^n ⊗ Q_σ^m` has density exactly `2^{-K} · 2^{n+m} · 2^{K−n−m} = 1` with respect to `P_u^{n+m}` (count of `σ` with prescribed
values on `n + m` distinct blocks; a `Y` in block `b` needs the flipped value), so `P_u^{n+m}|_{E_K} ≤` mixture: one-sided domination,
no TV bound between the mixture and the product. `P_u^{n+m}(E_K^c) ≤ (n+m)²/K` (union bound over pairs and blocks). Hence
`Pr_{P_u,P_u}(Û ≥ 1) ≥ 1 − δ − (n+m)²/K`; let `K → ∞` (paper: `≥ 1 − δ − 2(n+m)²/M`, `M → ∞`). Unlike the archived (long version)
route, no second limit `L → ∞` is needed, since `TV(P_σ, Q_σ) = 1` exactly.

## Notes for the paper
* The theorem and its printed proof are correct as printed (checked by hand: the conditional-uniformity argument on `E`, the bound
  "TV ≤ sum of the masses of `E^c`" (in fact `≤` their maximum), the two collision bounds `[n(n−1)+m(m−1)]/M` and
  `(n+m)(n+m−1)/(2M)`, and their sum `≤ 2(n+m)²/M`; `M ≥ 2(n+m)` makes `E` possible under `μ_M`). The Lean proof uses the block
  variant above, so the printed random-half construction itself is not machine-checked.
* Prose (resolved in the JMLR source). When first read, `sections/06_splitting.tex:223-224` said the class `𝒫₂` is one "in which
  the trimming framework lives and mutual singularity is unavailable", which contradicts the proof (its `(P_S, Q_S) ∈ 𝒫₂` are mutually
  singular, `B_split.tex:190`; e.g. the uniform laws on `[0,½]` and `[½,1]`). The 20:26 edit replaced it: `06_splitting.tex:226` now reads
  "…in which the trimming framework lives and no atomic law can be planted", and `02_related.tex:47-49` "…the usual argument, which
  plants an atomic law, is unavailable"; both are correct (every law of `𝒫₂` is absolutely continuous). The old sentence survives in the
  long version, `trimmed-mmd/paper.tex:1167`, and in `trimmed-mmd/arxiv/submission/main.tex:1069` ("mutual singularity is unavailable"
  for the bounded-density class), where it is equally false; suggested wording there: "…in which no atomic law can be planted".

## Fidelity review
Independent AI audit, method v1 (certify/AUDIT_METHOD.md), 2026-11-07 — PASS with notes (3 targets, each claim back-translated blind
from `Statements.lean` and the frozen `Archive/TrimmedMMD/Impossible/Statements.lean` (`dataLaw`, `BddDensity01`, archived
`Claims.impossible`) and `Lib/Distances/TV.lean` before reading this card, then compared clause by clause with
`06_splitting.tex:228-243` as printed today, `B_split.tex:186-216` and `03_regions.tex:17`; label confirmed as Theorem 21 via `main.aux`).
Notes:
* All 3 faithful; the blind back-translation agrees with the card's. `Density2` is the product class `𝒫₂` with the uniform bound `2`;
  `density2_iff` uses the strongest reading of "bounded by 2" (everywhere, support in `[0,1]`), the a.e. reading lies between its two
  sides, so it settles both. `impossible_implies_archived` is the meaningful direction (`Density2 ⊂ BddDensity01`, `C = 2`).
* Junk/vacuity: none (`Measure.real` only of probability measures; `tvDist` a bounded `⨆` over a nonempty index; no `map`, division,
  `log`, `deriv`; events measurable; `Û ≡ 1` satisfies the coverage hypothesis; the class contains `(P_u, P_u)`). No hypothesis stronger
  than printed (the proof uses only `δ ≥ 0`). `Û` defined off `[0,1]^{n+m}` and `Ξ : Type` are harmless, declared.
* The printed proof re-checked by hand by the auditor (hypergeometric weight depending only on `n, m`; conditional uniformity on `E`;
  TV `≤` max of the complement masses; collision bounds and their sum `≤ 2(n+m)²/M`; `M ≥ 2(n+m)`): correct. The route's one-sided density
  argument (`2^{-K}·2^{n+m}·2^{K−n−m} = 1` on `E_K`, collision mass `≤ (n+m)²/K`) checked by hand: correct.
* Applied from the audit: the prose note was stale (the JMLR sentence had been fixed at 20:26; rewritten above, pointing to the long
  version and the arXiv submission); line numbers updated in this card (the frozen docstring keeps the pre-edit ranges, cosmetic);
  "the converse does not follow" reworded.
