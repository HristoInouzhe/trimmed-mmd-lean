# Fidelity card — wave 31ta: trimmed-mmd (JMLR **v2 short**, `jmlr/v2/`), the numbered results not implied by earlier certified claims

Lean: `StatFormal/Wave31ta/Statements.lean` (13 claims; frozen 2026-11-08 before any proof, commit `ff0d92e`, sha256
`743d2ddf397292e3a0589f98e17d2aeab52f0d2ea9578e2f4b4a2cb454bc2f14`, locked with its 34 imports). Routes `RouteBang`, `RouteSmall`, `RouteSharp`,
`RouteImpossible`, `RouteTrimrate` (untrusted); `Proofs.lean` imports them; the gate checks `example : Claims.c := c` and `#print axioms` for
each (`[propext, Classical.choice, Quot.sound]`). Paper id `trimmed-mmd (jmlr)`; labels `<label> (v2 short)` (+ a short description).
Branch `tmmd-jmlr-v2map`, based on `tmmd-jmlr-hinge` at `10180c3` (waves 30tl, 30tn, 30tp, 30tr, 30ts, 30tu, 30tw, 30tx, 30ty) with
`tmmd-jmlr-seqbet` (waves 30tq, 30tv) merged at `8d90460`.
**Coverage map** (every numbered statement and display of v2 → certified claims → exact / implied / NOT covered):
`certify/cards/wave31ta_map.md`. Its final state is summarised at the end of this card.
Critic (independent AI reviewer, before the freeze, 2026-11-08): 13 claims, 8 ACCEPT and 5 ACCEPT-WITH-NOTE, none false, verdict READY TO
FREEZE; it re-derived every proof route, checked the numerics of `sharp_le_plugin` (180 parameter combinations for the repair bound, 60 for
`τ^{P'} − τ^P ≤ 0`) and of the counterexample, and confirmed the `cor:lower` encoding. Applied before hashing: docstring notes on
`bangbang_v2` (vacuous tie clause at `n_α = n`), `sharp_le_plugin` ("smaller" read as `≤`; the junk case `D = 0`), `sharp_cpl_counterexample`
(route, non-artefact numbers, remedy), `cor_trimrate_v2` (why `N` may come before the constants), `samplesize` (numeral not covered).
Fidelity review: independent AI audit, method v1 (certify/AUDIT_METHOD.md), 2026-11-08 — PASS with notes (13 claims back-translated blind
and compared with `jmlr/v2` at `3bad3e7`, all faithful; 15 earlier-wave rows of the map spot-checked, all verdicts hold; the `rem:sharper`
defect and the proposed App. B fix confirmed; notes at the end of this card, applied).
**Author: approved (automatic on AI-audit PASS, per author decision 2026-10-21).**

## Source
`trimmed-mmd/jmlr/v2/` at trimmed-mmd master `3bad3e7` ("JMLR v2 (50 pp): consistency of the split-sample lower bound"); read-only, read
2026-11-08 (working tree identical). sha256 of the eight files: on the map. Acknowledgments: `sections/13_backmatter.tex:12-15` ("The numbered
results were further formalized and checked in Lean 4 …").

## Targets (13, all in `certify/targets.toml`, module `StatFormal.Wave31ta.Proofs`)
| label | claim / theorem `StatFormal.Wave31ta.(Claims.)…` |
|---|---|
| `prop:bangbang (v2 short)` | `bangbang_v2` |
| `lem:continuity (v2 short)` | `continuity_v2` |
| `eq:distmax (v2 short)` | `distmax` |
| `cor:uniform (v2 short)` | `uniform_event` |
| `rem:sharper (v2 short)`, "a smaller threshold" | `sharp_le_plugin` |
| `rem:sharper (v2 short)`, counterexample for the coupled supremum | `sharp_cpl_counterexample` |
| `eq:sharptau (v2 short)`, the Pinelis term | `pinelis_h_form` |
| `eq:tauA (v2 short)`, paragraph after: the paper's `τ` for `k ≥ 0` with constant diagonal | `tauV2Cpl_facts` |
| `cor:lower (v2 short)` | `cor_lower_v2` |
| `thm:impossible (v2 short)` | `impossible_two` |
| `thm:trimrate`, `cor:trimrate (v2 short)`, encoding check | `quantile_of_QDensity` |
| `cor:trimrate (v2 short)` | `cor_trimrate_v2` |
| `eq:samplesize (v2 short)` | `samplesize` |

## Encodings (declared)
* As in the reused waves: (A1)–(A2) are `𝓗` a real Hilbert space (separable where the printed proof needs it), `φ : 𝒳 → 𝓗` strongly
  measurable with `‖φ x‖ ≤ κ` (`k(x,x) = ‖φ(x)‖²`, `f(x) = ⟨f,φ(x)⟩`); `D_φ` is any bound `D` on `‖φ(x) − φ(x')‖`; `D_α(P,Q) = Dpop`,
  `D̂_α = Demp`, `α* = tvDist`; samples `P^{⊗n} ⊗ Q^{⊗m}`; "with probability at least `1 − p`" is a measurable event of probability `≥ 1 − p`.
* `prop:bangbang`: `𝒯_α` is the set of minimisers of `qp(φ∘X, φ∘Y)` (`= ‖Σ w_iφ(X_i) − Σ v_jφ(Y_j)‖²`, `eq:qp`) over `Δ_α(n) × Δ_α(m)`;
  `d̂ = witness`; `d̂_{(k)} = ord dx (k−1)`; the `(m_α+1)`-th largest is `ord dy (m − m_α − 1)`; the convention `d̂_{(n+1)} = +∞` (`n_α = n`) is
  the clause `kfloor n α = n → ∀ i, w_i = c_α` (and symmetrically for `v`, which the print leaves implicit).
* `eq:distmax`, `sep`: the `EReal` `Wave17a.sepVal`; `dist` = `setDist`; "weakly compact" = `IsCompact (toWeakSpace ℝ 𝓗 '' A)`.
* `cor:uniform`: `𝒢` is parametrised by `{(f,t) : ‖f‖ ≤ 1, |t| ≤ κ}` (`gPar`); `sup_{g∈𝒢}|(P_n − P)g|` is the real `⨆` (`gDev`; nonempty
  and bounded index, no junk); `d_H` = `Metric.hausdorffDist`; `r_n` = `TrimmedMMD.rn`.
* `rem:sharper`: `τ^P = Wave30tp.tauP`, `τ^{P'} = Wave30ts.tauPs`, `τ^{cpl}_{P'} = Wave30ts.tauCpl` (the encodings of waves 30tp/30ts: roots as
  infima over `t ≥ 0`, lists `K`, `u ∈ [0,κ²)`); "smaller" is `≤`.
* `tauV2Cpl` (`Statements.lean`) is `min(τ^A, τ^P, τ^{cpl}_{P'})` with the paper's constants in `τ^P` (`v = √min(κ², D²/2)`, `ρ̄ = D`).
  `Nonempty 𝒳` is assumed (as in the frozen `tauFullCpl_threshold`; the paper's `𝒳` carries samples).
* `cor:lower`: the betting test of `thm:betting` at each level is the frozen `Wave30tv.seqReject` with level-dependent rules `g j`, `lam j`
  (`IsBatchRule`, `IsBatchBetRule`) on one `IsBatchPairing`; `α̂_lo = TrimmedMMD.Lower.alphaLo` (`eq:downclosed`); "`H_{0,α̂_lo}` is rejected"
  = `∃ j, α̂_lo = α_j ∧ test j rejected` (with a strictly increasing grid of nonnegative levels this is "the prefix of rejections is
  nonempty"; if `α̂_lo = 0` is not a grid level, or is an unrejected `α_1 = 0`, the event fails, as it should).
* `thm:impossible`: `𝒫₂` = `Density2` (`P ≤ 2·λ|_{[0,1]}`, a probability measure on `ℝ`); `Û` measurable in `(X_{1:n}, Y_{1:m}, ξ)`, `ξ ~ R`
  independent (as in the frozen `Impossible`); `P_u = λ|_{[0,1]}`.
* `cor:trimrate`: the explicit `O_P` form of `Wave30tx.cor_trimrate` (`∀ε ∃Λ(ε)`, then the setting, then `∃N`, then `∀ n, m ≥ N`, a measurable
  event of probability `≥ 1 − ε`, every minimiser of `eq:qp`, all tie functions). `N` is quantified after `(P, Q, φ, κ, α, r_Q = ρ, d*)` and
  before `(t_α, u_α, c_f, C_f, c'_f)`; `κ` and `d*` are functions of `k` and `(P,Q,k,α)` in the print (`d*` is the unique minimum-norm element).
  (Q) is `QDensity` at an arbitrary `(1−α)`-quantile `t_α` (`IsQuantile`), (Q′) is `QDensityLower` at an `α`-quantile `u_α`.
* `eq:samplesize`: "the test rejects `H_{0,0}`" is `τ(0) < D̂₀` for every value `D̂₀ > 0` with `n > 2(C₀/D̂₀)²`, for both readings of `τ`.

## Covered — back-translations and deviations
* **`bangbang_v2`** (`05_trimming.tex:17-35`). For `n, m ≥ 1`, `α ∈ [0,1)`, strongly measurable `φ` (no `κ`, no separability: generalisation):
  `𝒯_α` nonempty, convex, compact; at every `(w,v) ∈ 𝒯_α` the witness is the minimum-norm element of `𝒞_α(P_n) − 𝒞_α(Q_m)` with norm `D̂_α`,
  and it is the same at all minimisers; if `D̂_α > 0`: for `n_α < n` the cap/zero/tie rule at `d̂_{(n_α+1)}`, for `n_α = n` all `w_i = c_α`, and
  symmetrically for `v` at the `(m_α+1)`-th largest value; if `D̂_α = 0`, `𝒯_α` = feasible pairs with equal embeddings. As printed (the tie
  clause at `n_α = n` is vacuous and omitted).
* **`continuity_v2`** (`A_regions.tex:74-81`). `|D_α − D_{α'}| ≤ 4κ(1−ᾱ)^{−2}|α − α'|` for `ᾱ ∈ [0,1)`, `α, α' ∈ [0,ᾱ]`, any probability laws,
  no (A2)/(A3) (generalisation). As printed.
* **`distmax`** (`C_split.tex:32-37`). For nonempty convex weakly compact `A, B` in a real Hilbert space: `dist(A,B)` is the greatest value of
  `sep(·;A,B)` on the closed unit ball; `= sep(0)` when `dist = 0`; `= sep((a−b)/‖a−b‖)` for every nearest pair when `dist > 0`. As printed.
* **`uniform_event`** (`D_trimming.tex:345-357`). For `n ≥ 1`, `δ ∈ (0,1)`: the named event is measurable, has probability `≥ 1 − δ`, and for
  every sample in it and every `α ∈ [0,1)`, `d_H(𝒞_α(P_n), 𝒞_α(P)) ≤ r_n(α,δ)`. As printed ((A3) not needed: generalisation).
* **`sharp_le_plugin`** (`03_analytic.tex:66-72`). (1) `τ^{P'}(α,δ) ≤ τ^P(α,δ)` for all `D > 0`, `v, ρ̄ ≥ 0`, `α ∈ [0,1)`, `δ ∈ (0,1)`, `n, m ≥ 1`;
  (2) the same at the paper's constants for every `D ≥ 0` (`D = 0`: both are `0` by the frozen junk conventions; the printed `Ψ_H` is
  undefined there); (3) `τ^{cpl}_{P'} ≤ τ^P` at `D = √2κ`, `κ > 0`. Covers "smaller" for the general-kernel `τ^{P'}` and for the coupled one on
  Gaussian-type kernels with `D_φ = √2κ`.
* **`sharp_cpl_counterexample`**. There is a feature map on two points into `ℝ²` with `⟨φx,φy⟩ ≥ 0`, `‖φx‖ = 1`, `‖φ(true) − φ(false)‖ = 1/10`
  (so `κ = 1`, `D_φ = 1/10`), and `τ^P(1/2,1/2) < τ^{cpl}_{P'}(1/2,1/2)` at `n = m = 1` (certified `τ^P < 2 ≤ τ^{cpl}`; numerically `0.855` and `4.21`).
  This is a counterexample to the printed "smaller" for the coupled supremum (see Defects).
* **`pinelis_h_form`** (`B_analytic.tex:128-136`). For `a, b² > 0` and every `t`, the frozen Pinelis term equals the printed
  `2exp(−(b²/a²)h(ta/b²))`. With the renaming `f ∈ F` ↔ `η`, every display of `eq:sharptau` is now literally a frozen definition.
* **`tauV2Cpl_facts`** (`03_analytic.tex:87-90`, `B_analytic.tex:144-147`). For `k ≥ 0` with constant diagonal `κ²`: `min(τ^A, τ^P, τ^{cpl}_{P'})` is
  a `ValidThreshold` (nonnegative, nondecreasing, level `δ` for every `α` and every pair with `TV ≤ α`), `≤ τ^A`, `≤ r_n(·,δ/2) + r_m(·,δ/2)`
  when `D ≤ 2κ`, continuous on `(0,1)`, `→ ∞` as `α → 1` when `D, κ > 0`, and satisfies `CrossingFacts` (every clause of `lem:crossing` and of the
  paragraph after `eq:alphaest`). With it, every generic §3 claim of wave 30tu (and `prop:alphahat` of 30tx) applies to the v2 coupled `τ`.
* **`cor_lower_v2`** (`04_split.tex:119-132`). Strictly increasing grid of levels `≥ 0`, betting tests on the same batches with any rules:
  the event "`H_{0,α̂_lo}` rejected and `TV(P,Q) ≤ α̂_lo`" is measurable with probability `≤ δ`, and `P(α̂_lo > TV(P,Q)) ≤ δ`. As printed (grid
  levels `≥ 1` allowed: generalisation).
* **`impossible_two`** (`04_split.tex:170-177`). For `n, m ≥ 1`, `δ ∈ (0,1)`, any measurable randomised `Û` with coverage `≥ 1 − δ` over all
  pairs in `𝒫₂`: `P_{u,u}(Û ≥ 1) ≥ 1 − δ`. As printed. (It implies the frozen `TrimmedMMD.Impossible.impossible`, whose hypothesis is stronger.)
* **`quantile_of_QDensity`**. If `t` is a `p`-quantile of measurable `f` under `P` and the law of `f` has a density `≥ c > 0` on `[t−ρ, t+ρ]`,
  `ρ > 0`, then `quantileAt P f p = t`. Encoding check: the frozen `Wave30tx.trimrate`, `cor_trimrate` use `t_α = quantileAt`; by this claim
  every printed "a `(1−α)`-quantile `t_α`" at which (Q) holds is that one, so they cover the printed theorems.
* **`cor_trimrate_v2`** (`05_trimming.tex:83-98`). As `Wave30tx.cor_trimrate`, with `N` chosen before `t_α, u_α, c_f, C_f, c'_f` and with `t_α` any
  `(1−α)`-quantile at which (Q) holds: the printed "the factor implicit in `O_P` depends only on the probability allowed … while the sample
  size from which the bounds apply depends on `(P,Q,k,α)` and `r_Q`".
* **`samplesize`** (`03_analytic.tex:61-62`, `:253-262`). Gaussian constants, `n = m`: `τ^P(0) = κ[1+√log(1/δ)]√(2/n) = C₀√(2/n)` (the
  printed "it reads `τ^P(0) = [1+√log(1/δ)]√(2/n)`" at `κ = 1`), the paper's `τ(0) ≤ C₀√(2/n)` (both readings), and `n > 2(C₀/D̂₀)²` gives
  `τ(0) < D̂₀`. The numeral `C₀ ≈ 2.73` is not covered.

**Proof routes** (untrusted): `bangbang_v2` from `Wave30ah.bangbang_set`, `BangBang.bangbang_i/ii`, `WaveP1d.bangbang_iii`, `Wave8a.georep_empirical`,
`georep_qp` (`α = 0`: the capped simplex is the uniform vector); `tauV2Cpl_facts` from `Wave30tu.Instance.valid_min`, `tauA_valid`, `tauP_valid`,
`Wave30ts.coupled_cpl`, `Wave30tr.thmA_compare`, `Wave30tw.closed_candidates`, `coupled_tau_continuous`, `crossingFacts_of`; `continuity_v2` from
`Wave18b.continuity_lip`; `distmax` from `Wave17a.separation*`; `uniform_event` from the countable-dense supremum of
`TrimmedMMD/Concentration/Proofs` (`iSup_tmParams_eq`, `tm_concentration_countable`, `hausdorffDist_le_rn`); `cor_lower_v2`: the event equals
`⋃_{j: TV ≤ α_j} ⋂_{i ≤ j} R_i ⊆ R_{i₀}`, `i₀` the first level `≥ TV`, and `Wave30tv.thm_betting` (measurability of `R_j` from
`thm_betting_condexp` at the pair `(P,P)`); `impossible_two`: `K` blocks of two half-cells, `P_σ = Qσ K 2 σ`, `Q_σ = Qσ K 2 (rev ∘ σ)` (density 2,
`TV = 1`), the mixture dominates `P_u^{⊗(n+m)}` off block collisions (counting on `Fin n ⊕ Fin m`, `measurePreserving_sumPiEquivProdPi`),
collisions `≤ (n+m)²/K`, `K → ∞`; `sharp_le_plugin`: split `1/2`, `t₁ ≤ T₁` (McDiarmid terms `≤ δ/6`), `t₂ ≤ T₂` (new deterministic
`Ψ_R(t) ≤ e^{−L}` for `t ≥ √(2(β−1)sL) + cL/3`, Bernstein's pointwise inequality on the two-point MGF at the sub-gamma `λ`), (3) by
`coupled_tau_mono`; `sharp_cpl_counterexample`: `τ^{cpl} ≥ τ^{P'}(u=0) ≥ 2` (below `√(b²)` Pinelis' term `≥ 2e^{−1}`), `τ^P < 2` (`log 12 < 3`);
`cor_trimrate_v2`: best constants (ess inf / ess sup of the density on the window, admissible after clamping on a null set; quantiles unique
by `quantile_of_QDensity`), then `Wave30tx.cor_trimrate` and monotonicity of every bound in the constants.

## Junk-value audit
* `gDev`: real `⨆` over a nonempty (`κ ≥ 0`, forced by `‖φ‖ ≤ κ` on a nonempty space) index set, bounded by `4κ`: genuine.
* `tauPs`, `rootH`, `rootR`, `tauCpl`: `sInf` of admissible sets and a real `⨆` — the frozen wave 30ts conventions; in `sharp_le_plugin` (2) at
  `D = 0` both sides are `0` through them (declared above); in `sharp_cpl_counterexample` the admissible set of `rootH` is nonempty (no
  `sInf ∅`), and `tauCpl` is bounded above (genuine supremum).
* `cor_trimrate_v2`: `D⁻¹` with `D > 0`; `D̂⁻¹` under `0 < D̂` (a conclusion); `q = √(n∧m)` with `n, m ≥ N`; at `n = 0` the capped simplex is
  empty and the conclusion vacuous. `1/√((1−α)min(c_f,c'_f))` with positive constants.
* `bangbang_v2`: ℕ subtraction `m − kfloor m α − 1` only under `kfloor m α < m`; `ord` used only in range.
* `cor_lower_v2`: `alphaLo` is a `Finset.sup'` (genuine maximum) or `0`; no division.
* `impossible_two`: `Density2` uses `ℝ≥0∞` scalars; no `toReal` of `∞` (probability measures).
* `samplesize`: `√(2/n)`, `log(1/δ) > 0`, `n ≥ 1`. `quantile_of_QDensity`: the set is nonempty and bounded below by `t`, so `sInf` is genuine.
* No `Measure.map`, `deriv`, or non-integrable Bochner integral in the new statements (reused definitions audited on their cards).
* Vacuity: every hypothesis set is satisfiable in the paper's setting (Gaussian kernel; `U ≡ 1` for `impossible_two`; the two-point example).

## Defects in the printed text (`3bad3e7`), with corrected wording
1. **`03_analytic.tex:68-71`, `rem:sharper`, "gives a smaller threshold `τ^{P'}(α)`" — false for the coupled version of
   `B_analytic.tex:144-147` when `D_φ < √2κ`.** For kernels with `k ≥ 0` and constant diagonal, App. B defines `τ^{P'}` as the supremum over
   `u ∈ [0,κ²)` with `v² = κ² − u`, `ρ̄² = κ² + u`; at `u = 0` this uses `v = κ`, which exceeds the general `v = √min(κ², D_φ²/2)` when
   `D_φ < √2κ` (e.g. a Gaussian kernel on a bounded set, whose diameter is below `√2`). Certified instance (`sharp_cpl_counterexample`):
   `κ = 1`, `D_φ = 1/10`, `α = δ = 1/2`, `n = m = 1`: `τ^P < 2 ≤ τ^{cpl}_{P'}` (`0.855` vs `4.21`); the critic's numerics give the same at
   `δ = 0.05`, `n = m = 100` (`τ^P ≈ 0.103 < 0.2`). The statement is true for the general-kernel `τ^{P'}` and for the coupled one when
   `D_φ = √2κ` (`sharp_le_plugin`). Validity and every theorem are unaffected (`τ` is a minimum that contains `τ^P`). Corrected wording, either
   in App. B: "with `u = ‖μ_R‖² ∈ [0,κ²)` unknown, we put `v² = \min(κ² − u, D_φ²/2)` and `ρ̄ = \min((κ² + u)^{1/2}, D_φ)`" (still valid by (i)
   and (iv); then the coupled threshold is at most the general one, hence at most `τ^P`; this variant is not certified, and adopting it
   would leave the coupled reading of §3 uncovered until a new wave freezes its validity, monotonicity, continuity and crossing facts), or
   — needing no new wave — keep both candidates for such kernels, `τ = \min(τ^A, τ^P, τ^{P'}, τ^{\mathrm{cpl}}_{P'})`, the frozen and certified
   `Wave30tu.Full.tauFullCpl` (`tauFullCpl_threshold`, `tauFull_continuous`, `tauFull_tendsto`, `crossing_full_cpl`, `ratecond_full_cpl`), with
   the remark reading "gives a threshold `τ^{P'}(α)`, no larger than `τ^P(α)` for a general kernel, and, in the coupled version of
   Appendix B, when `D_φ = \sqrt2\,κ` (e.g. the Gaussian kernel on `\R^d`), with the same guarantee and the same monotonicity". The second
   "gives a smaller threshold" (`B_analytic.tex:126-127`) refers to the general inversion it introduces and is correct (`sharp_le_plugin` (1)),
   but should be checked against whichever fix is chosen.
2. **`03_analytic.tex:61-62`, `eq:samplesize`**: correct as printed (certified `samplesize`); only the numeral is uncovered.
No other numbered statement of v2 is false: the other items not implied by earlier claims (`cor:lower`'s second sentence, `thm:impossible`,
`prop:bangbang`, `cor:trimrate`'s sample-size clause, `cor:uniform`'s named event, `lem:continuity` at `ᾱ = 0`, and the displays
`eq:distmax`, `eq:sharptau`, `eq:samplesize`) are true as printed and are now certified.

## Certified results reused (not re-proved)
Wave 8a (`georep_empirical`, `georep_qp`), 17a (`separation`, `separation_nearest_exists`, `separation_attained`), 18b (`continuity_lip`), 30ah
(`bangbang_set`), `TrimmedMMD/BangBang` (`bangbang_i`, `bangbang_ii`), P1d (`bangbang_iii`), `TrimmedMMD/Concentration` (proof library),
`TrimmedMMD/Impossible` (proof library: cells, counting, mixture), 30tp (`plugin_level_explicit`, `plugin_monotone`), 30tr (`thmA_compare`), 30ts
(`coupled_cpl`, `coupled_tau_mono` and route lemmas), 30tu (`Instance.valid_min`, `tauA_valid`, `tauP_valid`), 30tw (`closed_candidates`,
`coupled_tau_continuous`, `crossingFacts_of`), 30tx (`cor_trimrate`), 30tv (`thm_betting`, `thm_betting_condexp`, `cor_lower`),
`Lib/Bernstein/Pointwise` (`exp_mul_le_bernstein`).

## Not covered (declared)
Numerals (`C₀ ≈ 2.73`, the calibration ratios and percentages of §3); prose consequences without a number: "`[α̂_lo, α̂_hi]` covers `α*` with
probability at least `1 − δ`" (`B_analytic.tex:310-312`, a union bound of two certified events), the Riemann–Lebesgue paragraph
(`C_split.tex:281-287`), "Equivalently" of `eq:contam`, the order-of-magnitude remarks (`τ^A` of order `κ(1−α)^{−1}(n∧m)^{−1/2}`, `τ^{P'}` of order
`(1−α)^{−1/2}`), the local-alternative calculation (`C_split.tex:121-127`), the remarks after `prop:loconsistency` and `prop:alphahat`.
Excluded (wave 30tz): `prop:loconsistency`, `lem:popramp`, `eq:cutrank`, `eq:fittedramp`, `eq:betbounds`.

## Coverage after wave 31ta (map `certify/cards/wave31ta_map.md`)
35 numbered statements in scope (37 environments of v2 minus `prop:loconsistency`, `lem:popramp`): **exact 21\*, implied 14, NOT covered 0**
(\* `rem:sharper` is counted as exact: "smaller" is certified for the general `τ^{P'}` and for the coupled one at `D_φ = √2κ`, and certified
false for the coupled one at `D_φ < √2κ` — a printed defect, not a coverage gap)
(before this wave: exact 14, implied 14, NOT covered 7: `rem:sharper`, `cor:lower`, `thm:impossible`, `prop:bangbang`, `cor:trimrate`,
`cor:uniform`, `lem:continuity`; now exact, with `rem:sharper` certified true for the general constants and false — certified counterexample —
for the coupled supremum with `D_φ < √2κ`). Numbered displays in scope: all exact, implied, or definitions/proof steps (`eq:distmax`,
`eq:sharptau`, `eq:samplesize` were not covered and are now exact).

## Coverage notes (COVERAGE.md rows, v2 short)
* `prop:bangbang`: "certified as printed (v2 short): one level alpha in [0,1), T_alpha nonempty convex compact, witness = minimum-norm element
  with norm D-hat, (ii) including n_alpha = n, (iii) (Wave31ta; two-level form TrimmedMMD/BangBang, P1d, 30ah)".
* `cor:uniform`: "certified as printed (v2 short) with the named event, all alpha at once (Wave31ta; TrimmedMMD Concentration)".
* `rem:sharper`: "certified: same guarantee and monotonicity (Wave30ts); smaller (<=) for the general tau^P' and for the coupled supremum at
  D_phi = sqrt2 kappa (Wave31ta); the coupled supremum can exceed tau^P when D_phi < sqrt2 kappa, counterexample certified (Wave31ta)".
* `thm:impossible`: "certified as printed (v2 short): coverage over P_2 (densities bounded by 2) forces P_{u,u}(U >= 1) >= 1 - delta (Wave31ta)".
* `cor:lower` (v2 short): "certified: P(alpha_lo > TV) <= delta (Wave30tv) and the strengthened clause P(H_0 at alpha_lo rejected and
  TV <= alpha_lo) <= delta (Wave31ta), betting test, any rule per level".
* `cor:trimrate` (v2 short): "certified in explicit form with the printed sample-size clause: Lambda(eps), N depending on (P,Q,k,alpha) and r_Q
  only (Wave31ta, from Wave30tx)".
* `lem:continuity`, `eq:distmax`, `eq:sharptau`, `eq:samplesize`, the coupled `tau`: as in the target labels.

## AI audit notes (2026-11-08, PASS with notes; applied)
1. The trade-off of the App. B fix (coverage of the coupled reading would need a new wave) and the third option using the certified
   four-candidate `tauFullCpl`; the ambiguous remark-only wording; the second "smaller" at `B_analytic.tex:126-127` — added to defect 1.
2. The tally counts `rem:sharper` as exact — asterisk and explanation added (here and on the map).
3. Map row `cor:consistency`: for the v2 coupled `τ`, the rate-condition example needs `tauFullCpl ≤ tauV2Cpl` pointwise and `D̂ ≤ D_φ`
   (`Demp_le_Dphi`) — added to the reason.
4. Map row `cor:upperfs`: `Wave30tl.alphaHi_isGLB` is stated for `Ď = D̂ + (r_n + r_m)`; the infimum is genuine for every `Ď` — said so.
5. COVERAGE.md notes with unescaped `|` (broken table rows, truncated page notes) — reworded with `abs(...)` and "given".
6. Cosmetic: the header of the frozen `Statements.lean` (`:30`) cites `B_analytic.tex:128-140` for `eq:sharptau`; the display is
   `:128-136` (the claim docstring and this card); not edited (frozen). The count "the eight items" in the defects section — replaced by
   the list.
7. Recording lines written.
