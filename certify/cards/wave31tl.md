# Fidelity card — wave 31tl: trimmed-mmd (JMLR **v3** of 2026-11-19): `thm:lorate` (rate of the split-sample lower bound under the margin condition) and the prose that rides on it

Lean: `StatFormal/Wave31tl/Statements.lean` (8 claims; definitions `Tfit`, `Tbet`, `gridFloor`, `Jeps`, `GapsGe`, `MeshBelowLe`, `rOne`,
`tNM`, `defaultLabel`, `NearestCuts`, `batchCount`, `defaultPairs`, `IsDefaultRun`; frozen 2026-11-19 before any proof, commit `c9b085f`,
locked with its imports). Routes `RouteBasic`, `RouteCore`, `RouteClaims`, `RouteArith`, `RouteO` (untrusted, commit `d117c2f`);
`Proofs.lean` defines each theorem from its route and checks `example : Claims.c := c`. All 8 claims proved; axioms propext,
Classical.choice, Quot.sound. Paper id `trimmed-mmd (jmlr)`;
labels `thm:lorate (v3 2026-11-19)`, `prose:lo-rate (v3 2026-11-19)`, `prose:same-rate (v3 2026-11-19)`. Branch `tmmd-jmlr-lorate`
(worktree `~/projects/StatFormal-tmmd-rev`), from master `f3f37c4`.
Critic (independent AI reviewer, before the freeze, 2026-11-19, shared with wave 31tm): 9 claims, 6 ACCEPT, 3 ACCEPT-WITH-NOTE
(`lorate_O`, `same_rate`, `alphalo`); none false, misread, vacuous or with an undeclared conditionalisation; READY TO FREEZE after one
blocking docstring fix. It back-translated blind, typechecked a probe (every `/` in the new definitions is real division), brute-forced
the batch arithmetic (`n, m ∈ [10,139]`, every tie-break) and the constant of (iii) (worst case 694 < 1000), re-derived every printed step
of the proofs of Theorem 33 and Corollary 17 (no wrong step), and checked the hashes, the `main.aux` numbers and every line range.
Applied before hashing: R1 the batches are those of Section 4.2 (the draft said 4.1 in eight places, one inside a quotation); R2 the
hashes of `02_regions.tex` and `B_analytic.tex` and the number of Proposition 26; R3 the dropped size condition of `lorate_O` and
`same_rate` declared; R5 the order of the observations declared; the two "exponent" sentences listed under `same_rate`. No Lean term
changed.
Gate (2026-11-19, branch `tmmd-jmlr-lorate`): `CERTIFIED: 3953 targets; statements frozen; axioms within ['Classical.choice',
'Quot.sound', 'propext']`. `tools/check_aliases.py`: `ALIASES OK: 3896 aliases in 16 paper files`.
Fidelity review: independent AI audit, method v1 (certify/AUDIT_METHOD.md), 2026-11-19 — PASS with notes (blind back-translations
written before opening the tex; all eight claims faithful, deviations declared generalisations or encodings; hashes, lock, targets,
`main.aux` numbers and line ranges checked; constant 1000 checked numerically, worst ratio 694.97; audit done on the frozen statements
before any proof; notes at the end of this card).
**Author: approved (automatic on AI-audit PASS, per author decision 2026-10-21).**

## Source
trimmed-mmd commit `5e51f65` ("JMLR v3: split-sample rate and trimming corollary, …"), read with `git show 5e51f65:jmlr/v3/…` (the paper
repo is being edited by another session; the snapshot is pinned). sha256: `appendix/C_split.tex` `04089c47…d7feda1`, `sections/04_split.tex`
`790e687b…e153e`, `sections/03_analytic.tex` `f47ebecd…fe9e220`, `sections/02_regions.tex` `8c3985ee…11461`, `appendix/B_analytic.tex`
`012c79c8…fcca8da` (full hashes in the Lean header). Numbers from `main.aux` of the build of 2026-11-19 18:48: Theorem 33 `thm:lorate`
(Appendix C.6, `C_split.tex:303-340`, constants (28) `eq:loconst` `:313-318`, the paragraph after it `:342-348`, proof `:350-460`, the
paragraph after the proof `:462-468`), Proposition 12 `prop:loconsistency` (`04_split.tex:167-177`, the display after it `:181-192`),
Theorem 8 `thm:rate` (`03_analytic.tex:242-253`, the sentence after it `:256-257`), Proposition 26 `prop:rategeneral`, Section 4.2
`sec:betting` (the batches, `04_split.tex:71-77`).

## Targets (8 new claims, module `StatFormal.Wave31tl.Proofs`)
| label | claim / theorem `StatFormal.Wave31tl.(Claims.)…` |
|---|---|
| `thm:lorate` (i): `P(α̂_lo < a_ε) ≤ η` when `c₀ε^γ ≥ β⋆ max{T_fit(η), T_bet(η,J_ε)}` | `lorate_i` |
| `thm:lorate` (ii): `α⋆ − h − (t_{n,m}/c₀)^{1/γ} ≤ α̂_lo ≤ α⋆` with probability `≥ 1−δ−η` | `lorate_ii` |
| `thm:lorate` (iii), first half: the batches of Section 4.2 give `r₁ ≤ min{1, 12/(n∧m)}`, `N ≥ (n∧m)/2` | `lorate_batches` |
| `thm:lorate` (iii), the `O(·)`: explicit constant 1000 | `lorate_iii` |
| the paragraph after Theorem 33: no `log J` when `h₀ ≥ ε′_{n,m}` | `lorate_nologJ` |
| the paragraph after the proof: a general margin `ω`, `ω^{-1}(t_{n,m})` in place of `(t_{n,m}/c₀)^{1/γ}` | `lorate_general` |
| `prose:lo-rate`: the display after Proposition 12 (`04_split.tex:181-192`) | `lorate_O` |
| `prose:same-rate`: "The split-sample bound of Section 4 has the same rate" (`03_analytic.tex:256-257`) | `same_rate` |

## Encodings (declared)
* (A1)–(A2) as in every trimmed-mmd wave (`H` real complete separable, `φ` strongly measurable, `‖φ‖ ≤ κ`). (A3) is not assumed: the paper
  says the proof "does not use (A3)"; `α⋆ = TV(P,Q)` is `tvDist P Q` and `ass:margin` is the frozen `Wave31ti.PolyMargin` (`c₀ > 0`, `γ ≥ 1`,
  `c₀ε^γ ≤ D_{α⋆−ε}` on `[0,α⋆]`). Generalisation: the printed "Assumption 1" includes (A3).
* `Δ_φ`: any `Dφ` with `‖φ x − φ x′‖ ≤ Dφ ≤ 2κ`. The printed `Δ_φ` (`02_regions.tex:52`, the supremum, `≤ 2κ`) is one, and the constants
  increase with `Dφ` and `κ`, so this is a generalisation.
* The run is the frozen `Wave30tz.LoRun` with `IsWitnessRun φ α δ (1/2) s2`, `0 < s2 ≤ 4`: an exact QP minimizer at each level on the
  batches before the one bet on, cut points in (cutrank), the fractions through the bounds `lamLo ≤ λ_k ≤ lamHi` on batches with a ramp
  (the printed `eq:fractions` with `λ_max = ½`, `σ₀² ≤ 4`, floor `σ²_min` satisfies them: certified `Wave30tz.fractions_bounds`), admissible
  fitting rules and fractions. `α̂_lo` is `LoRun.alphaLo` (`eq:downclosed`). The grid is `IsGrid α` with `J ≥ 1`.
* `B`: every pair lies in a batch `≤ B` (pairs are never in batch 0 by `IsBatchPairing`), which is the printed number of batches bet on for
  batches `1, …, B`. `N` is `R.N`; `N ≥ 1` is assumed (the printed `T_bet` has `2/N`; without it Lean's `√(2/0) = 0` would make (i) false).
* `r₁ = 1/n_{<1} + 1/m_{<1}` is `rOne`, with batch 0 nonempty on both sides (`fitCard … 1 ≥ 1`; the printed `r₁` is finite).
* `h₀`: any `h0 > 0` with `α_j + h0 ≤ α_{j+1}` (`GapsGe`). The printed `h₀` is one when `J ≥ 2`; for `J = 1` every `h0 > 0` gives
  `J_ε = min{1, 2(1+ε/h0)} = 1`, as `h₀ = ∞` does. `J_ε` decreases in `h0`, so the claim implies the printed one.
* `a_ε = gridFloor α (α⋆−ε)` (`max` of `{0}` and the levels `≤ α⋆−ε`). The mesh `h`: any upper bound of `a − gridFloor α a` on `[0,α⋆]`
  (`MeshBelowLe`); the printed supremum is the least such bound and the conclusions are monotone in `h`.
* "With probability at least `1−δ−η`": a measurable event of that probability inside the claimed set.
* (iii): "the batches of Section 4.2, their boundaries rounded to the nearest integers" is `defaultLabel b₁ b₂` (batch 0 = indices `< b₁`,
  batch 1 = `[b₁,b₂)`, batch 2 = `≥ b₂`) with `|b₁ − n/4| ≤ ½`, `|b₂ − n/2| ≤ ½` (any tie-breaking; `NearestCuts`), likewise for `m`; `N` is
  the printed number of pairs `min(n_[1],m_[1]) + min(n_[2],m_[2])` (`C_split.tex:105-111`; `defaultPairs`, and `IsDefaultRun` for a run).
  The order of the observations: Section 4.2 puts each sample in a random order drawn once; the index order is an order fixed in advance
  (`C_split.tex:94`), the same in law for i.i.d. data.
* The `O(·)` of (iii) is an explicit bound with the absolute constant 1000 inside the power (as Theorem 8's constant 14 in wave 31ti; this
  is stronger than a constant outside, since `(1000X)^{1/γ} ≤ 1000X^{1/γ}` for `γ ≥ 1`), with the printed proof's intermediate
  `t_{n,m} ≤ C β⋆κσ_min^{-2}√((1+L_δ+log(J/η))/(n∧m))` at `C = 1000`.
* `lorate_O`, `same_rate`: the size condition `n∧m ≥ 10` of (iii) is dropped (the display after Proposition 12 states none; for `n∧m ≤ 9`
  the bound term is at least `α⋆` because `c₀(α⋆)^γ ≤ D₀ ≤ 2κ`, so the lower inequality is trivial); `n, m ≥ 1` is assumed.
* `same_rate`: "the same rate" is read as Theorem 8's exponent `(n∧m)^{-1/(2γ)}`: for fixed laws, `κ`, `(c₀,γ)`, `δ`, `η`, `σ²_min` and `J`,
  one constant `C` (chosen before `n, m`, the grid values, the run and `h`) with `α⋆ − h − C(n∧m)^{-1/(2γ)} ≤ α̂_lo ≤ α⋆` with probability
  `≥ 1−δ−η`. `C` depends on `J` (through `log J`), as the printed comparison of the factors says.
* `lorate_general`: the general margin is the frozen `Wave30tu.Margin` (the hypothesis of Proposition 26); `ω^{-1}(t_{n,m})` is any
  `e ∈ [0,α⋆]` with `ω(e) = t_{n,m}` (unique by strict monotonicity; it exists iff `t_{n,m} ≤ ω(α⋆)`, certified `Wave30tu.rate_eps`).

## Covered — back-translations and deviations
* `lorate_i`: (A1)–(A2), `Dφ ≤ 2κ`, `PolyMargin c₀ γ`, `α⋆ < 1`, grid of `J ≥ 1` levels, `δ, η ∈ (0,1)`, `s2 ∈ (0,4]`, a witness run with
  `λ_max = ½`, pairs in batches `≤ B`, batch 0 nonempty, `r₁ ≤ 1`, `N ≥ 1`, `h0 > 0` below the consecutive gaps, `ε ∈ (0,α⋆]`: if
  `β⋆ max{T_fit(κ,Dφ,η,r₁,B), T_bet(Dφ,s2,L_δ,η,J_ε,N)} ≤ c₀ε^γ`, then `P(α̂_lo < a_ε) ≤ η`. Generalisations: no (A3), `Dφ`, `h0`.
* `lorate_ii`: the same setting without `ε`, `h0`, and an upper bound `h` of the mesh: one measurable event of probability `≥ 1−δ−η` with
  `α⋆ − h − (t_{n,m}/c₀)^{1/γ} ≤ α̂_lo ≤ α⋆`, `t_{n,m} = β⋆ max{T_fit(η), T_bet(η,J)}`.
* `lorate_batches`: `n∧m ≥ 10`, nearest-integer boundaries: batch 0 nonempty on both sides, `r₁ ≤ min{1, 12/(n∧m)}`,
  `min(n_[1],m_[1]) + min(n_[2],m_[2]) ≥ (n∧m)/2`. Exact.
* `lorate_iii`: arithmetic: `0 ≤ Dφ ≤ 2κ`, `c₀ > 0`, `γ ≥ 1`, `α⋆ ∈ [0,1)`, `s2 ∈ (0,4]`, `δ, η ∈ (0,1)`, `J ≥ 1`, `n∧m ≥ 10`, default batches
  (`B = 2`): `t_{n,m} ≤ 1000β⋆κ/s2·√((1+L_δ+log(J/η))/(n∧m))` and `(t_{n,m}/c₀)^{1/γ} ≤ (1000κ/(c₀(1−α⋆)s2)·√(…))^{1/γ}`.
* `lorate_nologJ`: (i)'s setting with an upper bound `h` of the mesh; `ε′ = (β⋆ max{T_fit(η), T_bet(η,4)}/c₀)^{1/γ}`; if `ε′ ≤ h0`, then
  `J_{ε′} ≤ 4` and, with probability `≥ 1−δ−η`, `α⋆ − h − ε′ ≤ α̂_lo ≤ α⋆`.
* `lorate_general`: (ii)'s setting with `Wave30tu.Margin ω` in place of Assumption 2: for `e ∈ [0,α⋆]` with `ω(e) = t_{n,m}`, with
  probability `≥ 1−δ−η`, `α⋆ − h − e ≤ α̂_lo ≤ α⋆`.
* `lorate_O`: (A1)–(A2), `PolyMargin`, `α⋆ < 1`, `J ≥ 1`, a witness run with `λ_max = ½`, floor `s2 ∈ (0,4]` and the default batches (with
  `N` the printed count), `n, m ≥ 1`, `η ∈ (0,1)`, an upper bound `h` of the mesh: with probability `≥ 1−δ−η`,
  `α⋆ − h − (1000κ/(c₀(1−α⋆)s2)·√((1+log(1/δ)+log(J/η))/(n∧m)))^{1/γ} ≤ α̂_lo ≤ α⋆`. Generalisation: no size condition.
* `same_rate`: for fixed `(P,Q,φ,κ,c₀,γ,δ,η,s2,J)` there is `C ≥ 0` such that for all `n, m ≥ 1`, grids, default runs and mesh bounds `h`:
  with probability `≥ 1−δ−η`, `α⋆ − h − C(n∧m)^{-1/(2γ)} ≤ α̂_lo ≤ α⋆`. Theorem 8 (certified `Wave31ti.rate_v3_full`) has
  `|α̂ − α⋆| ≤ (14κ/(c₀(1−α⋆))√((1+log(1/δ)+log(1/δ′))/(n∧m)))^{1/γ}`, the same exponent.

## Covered by earlier certified targets (no new claim)
* "`α̂_lo ≤ α⋆` with probability at least `1−δ`" (used in (ii)): `cor:lower` (certified `Wave30tz.lo_upper`, `Wave30tv`).
* The fitted-ramp step, the fitting event and the betting bound used by the proof are the certified `Wave30tz` lemmas behind
  `lo_lower_bound` (`eq:fittedramp`, `lem:hinge` tail, `eq:betbounds`).

## Proof route (untrusted)
Same route as the paper's proof, through the certified Wave 30tz machinery of Proposition 12.
* `RouteCore.core_lower`, the lower side for a general excess profile (`D⋆ > 0`, `x_j ≥ 1`, `D⋆x_j ≤ D_{α_j}` at the levels `≤ a`):
  the fitting event `E_fit = {Z_b, Z⁻_b ≤ τ⋆ = D⋆/(8β⋆)}` (`Wave30tz.Lower.fitEvent`), `P(E_fitᶜ) ≤ 2B·η/(4B)` (`fitEvent_compl_le`, from
  `τ⋆ − μ₁ ≥ Δ_φ√(r₁ log(4B/η)/2)`, i.e. `β⋆T_fit ≤ D⋆`); on `E_fit`, at each level, `Wave30tz.Lower.witness_step` with `d = D_{α_j}` and
  `β = β(α⋆)` (the size conditions (S) from `β⋆T_fit ≤ D⋆`, `Δ_φ ≤ 2κ`, `r₁ ≤ 1`) gives a ramp with excess `ϱ_j = D_{α_j}/(2β⋆Δ_φ)`;
  Lemma 5 (`bet_power_route`, `bet_arith`) gives `genEps`, which equals `ε_N(ϱ_j)` since `N ≥ 200L` (from `D⋆ ≤ D_{α_j} ≤ Δ_φ`,
  `Basic.dpop_le_dphi`); `(ϱ_jS − C)₊ ≥ a x_j` with `a = ϱ⋆S − C ≥ (2/σ_min)√(L log(2J′/η))`, so `ε_N(ϱ_j) ≤ e^{−Ax_j²}`,
  `A ≥ log(2J′/η)`; the union over `E_fitᶜ` and the levels `≤ a` (`grid_events_route`).
* `RouteBasic.sum_exp_le_Jeps`: the grouped sum of the printed proof (at most `1 + ε/h₀` of the `x_j` in each `[1+k, 2+k)` from the
  consecutive gaps, `(1+k)² ≥ 1 + 3k`, `Σ_k e^{−3Ak} ≤ 2`), and the trivial bound `J e^{−A}`.
* `RouteClaims`: (i) is `core_lower` with `D⋆ = c₀ε^γ`, `x_j = (α⋆ − α_j)/ε` (`x_j ≤ x_j^γ`, the margin at `εx_j`); (ii) and the general
  margin are `core_lower` with `x_j = 1`, `J′ = J`, `D⋆ = t_{n,m}` (`D_{α_j} ≥ c₀(α⋆−α_j)^γ ≥ c₀e^γ = t`, resp. `≥ D_{α⋆−e} ≥ ω(e) = t` by the
  certified `Wave30tz.dpop_antitone`), the mesh bound `gridFloor α (α⋆ − e) ≥ α⋆ − e − h`, and `cor:lower` (the certified
  `Wave30tz.lo_upper`); the case `α⋆ − h − e ≤ 0` is trivial, and otherwise `α⋆ > 0` and the margin give `κ > 0`, so `t > 0`; the
  no-`log J` paragraph is (i) at `ε′` with `J_{ε′} ≤ 4` and `T_bet` increasing in `J′`.
* `RouteArith`: the default labels give `n_{<1} = b₁`, `n_[1] = b₂ − b₁`, `n_[2] = n − b₂`; the constant: `T_fit ≤ 224κq`,
  `T_bet ≤ 192κq/σ²_min`, `q = √((1+L+log(J/η))/(n∧m))` (`log 2 ≤ 1`, `√2 ≤ 3/2`, `√12 ≤ 7/2`).
* `RouteO`: `lorate_O` from (ii) at `Δ_φ = 2κ`, `B = 2` (blocks are nonempty, labels `≤ 2`) and (iii) for `n∧m ≥ 10`, and the trivial case
  `n∧m ≤ 9`; `same_rate` from `lorate_O` with `C = (1000κ√(1+L+log(J/η))/(c₀(1−α⋆)σ²_min))^{1/γ}`.
Route differences: none of substance; the proof formalises the printed steps (`C_split.tex:350-459`).

## Junk-value audit
`Real.log (4B/η)`: `B ≥ 1` (a pair exists, `N ≥ 1`, and lies in a batch `1 ≤ bat k ≤ B`), `η ∈ (0,1)`. `log(2J′/η)`: `J′ = J_ε ≥ 1`
(`J ≥ 1`), `J′ = 4`, or `J`. `√(2/N)`: `N ≥ 1`. `1/n_{<1}`, `1/m_{<1}`: batch 0 nonempty. `16/s2`, `2/√s2`: `s2 > 0`. `ε/h0`: `h0 > 0`.
`(t/c₀)^{1/γ}`: `c₀ > 0`, `γ ≥ 1`, `t ≥ 0` (𝒳 nonempty under probability measures, so `κ, Dφ ≥ 0`). `(n∧m)^{-1/(2γ)}`, `√(·/(n∧m))`:
`n, m ≥ 1` (at `n∧m = 0` Lean's `0^{-a} = 0` and `x/0 = 0` would make the bound false). `beta α⋆`: `α⋆ < 1`. `Dpop` only at levels in
`[0,1)`. `gridFloor`: a `max` of `0` and a finite `sup'`, no `sSup`. `log(J/η)`: `J ≥ 1`. Vacuity: the hypotheses are jointly satisfiable
(e.g. a finite `𝒳` with the separated example of `ex:separated`, `γ = 1`); as declared on the wave-30tz card, the existence of a jointly
measurable selection of the QP minimizer and cut points for a general `𝒳` is assumed, not proved.

## Defects / wording in the printed text
None found (the critic re-derived every step). Nits, no change needed: (a) `C_split.tex:446-447`, the case `t_{n,m} = 0` lies outside
(i)'s `ε ∈ (0,α⋆]`; it forces `κ = 0` and `α⋆ = 0` under the margin, so (ii) is trivial there. (b) `C_split.tex:464`, "uses the margin
only through `D_{α_j} ≥ D⋆`": the proof also uses `D⋆ ≤ D_{α⋆−ε} ≤ Δ_φ` (`:359-360`, `:422`), which the general margin also gives.

## Not covered (declared)
The Frank–Wolfe variant (`C_split.tex:464-467`: a feasible point with relative gap `ρ < 1` serves with `(1−ρ/2)c₀`; the frozen witness rule
takes exact minimizers); "the kernel is fixed in advance … a bandwidth computed from batch 0 is not covered" (scope remark); "The proof
needs no density of the witness at the cut points … and it does not use (A3)" (meta, consistent with the claims); "the constants … are far
from sharp" (informal); the prose comparison of the factors `h`, `1/σ²_min`, `log J` beyond the claims.

## Coverage notes (COVERAGE.md rows)
* `thm:lorate`: "certified (Theorem 33, v3 of 2026-11-19): (i) P(alpha-lo < a_eps) <= eta when c0 eps^gamma >= beta* max{T_fit, T_bet(J_eps)},
  for any h0 below the consecutive gaps; (ii) alpha* - h - (t/c0)^{1/gamma} <= alpha-lo <= alpha* with probability >= 1 - delta - eta for
  any upper bound h of the mesh; (iii) for n^m >= 10 the default batches give r_1 <= min{1, 12/(n^m)} and N >= (n^m)/2, and the O(.) with the explicit
  constant 1000; Delta_phi any bound <= 2 kappa, (A3) not needed; the paragraphs after it: no log J when h0 >= eps', and the general-margin
  form omega^{-1}(t); the Frank-Wolfe variant not covered (Wave31tl)".
* `prose:lo-rate`: "certified (the display after prop:loconsistency): with the batches of Section 4.2 and n, m >= 1, alpha* - h -
  (1000 kappa/(c0(1-alpha*) sigma^2_min) sqrt((1+log(1/delta)+log(J/eta))/(n^m)))^{1/gamma} <= alpha-lo <= alpha* with probability
  >= 1 - delta - eta (Wave31tl)".
* `prose:same-rate`: "certified (the sentence after thm:rate, and 'the exponent is that of ...' at C_split.tex:342 and 04_split.tex:191):
  for fixed laws, kappa, margin, delta, eta, sigma^2_min and J, one constant C free of n, m, the grid values and the run with
  alpha* - h - C (n^m)^{-1/(2 gamma)} <= alpha-lo <= alpha* with probability >= 1 - delta - eta (batches of Section 4.2); the mesh h and the
  dependence of C on J are part of the reading (Wave31tl)".

## AI audit notes (2026-11-19, method v1, PASS with notes)
1. The `thm:lorate` coverage row now says that part (iii) is for `n∧m ≥ 10` (applied).
2. `lorate_O` and `same_rate` use Theorem 33 (iii)'s nearest-integer cuts and the index order fixed in advance for a main-text display
   that states neither; both are declared (`IsDefaultRun`, the order note). Cosmetic.
3. `lorate_nologJ` and `lorate_general` are filed under the label `thm:lorate` although they encode the prose after the theorem; their
   target labels say so. Acceptable.
4. The general-margin paragraph is cited as `C_split.tex:462-464` in the Lean header and `:462-468` on the card; both are right for their
   scope.
5. `main.aux` (18:48) predates the commit `5e51f65` (19:29); the label sets are identical and the numbers consistent.
