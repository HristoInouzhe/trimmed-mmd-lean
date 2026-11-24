# Fidelity card — wave 30tq: trimmed-mmd (jmlr), the finite-sample variance-adaptive split certificate (betting on the ramp of the kernel witness)

Lean: `StatFormal/Wave30tq/Statements.lean` (frozen 2026-11-07 before any proof, commit `6744354`; imports the frozen
`Archive/TrimmedMMD/Lower/Statements.lean` (`alphaLo`, `eq:downclosed`; through it `ZeroSet` `IsTrimDensity`, `Unconditional`,
`Concentration` `region`, `Lib/Distances/TV` `tvDist`) and the frozen `Archive/Wave17a/Statements.lean` (`sepVal`), plus Mathlib),
routes `RouteLemmas.lean` (Lemmas 1–2), `RouteIndep.lean` (fold-two independence, §2.3 pairing facts), `RouteBetting.lean` (Theorem 1),
`RouteEB.lean` (Corollary 1), `RouteLower.lean` (Corollary 2), `Proofs.lean`. New library: `Lib/Betting/Ville.lean`,
`Lib/Betting/Wealth.lean`, `Lib/Bernstein/TwoSample.lean`.
**Printed source (READ-ONLY):** `trimmed-mmd/explore/split_adaptive/theory.md`, Section 2 (sha256
`5518c814f1ef6bda0ea1795b9990fc01e00c9424a1d9b7bd5adf63decc780852`, 190 lines, read 2026-11-07; an earlier state of the same file,
sha `ef44580d…`, differed only in §2.4 "Cross-fitting", which is not covered here). Labels are provisional (`lem:onecut`, `lem:ramp`,
`sec:certificate`, `thm:betting`, `cor:eb-cert`, `cor:betting-lower`, each with its `theory.md` number); **to be remapped to the
paper's labels when the JMLR revision absorbs §2.** Code: `explore/split_adaptive/sacert.py` (`ramp`, `pair_up`, `betting_test`,
`sd_ucb`, `lcb_bern2s`). Paper objects used through their frozen encodings: `eq:trimset`, `eq:tvintersect`, `lem:cvar`,
`eq:lowertrim`, `eq:downclosed` (`jmlr/sections/06_splitting.tex:153-167`).
Build: `lake build StatFormal.Wave30tq.Proofs` succeeds; every claim checked by `example : Claims.c := c`; `#print axioms` of each of the
17 theorems = `[propext, Classical.choice, Quot.sound]`. Paper id `trimmed-mmd (jmlr)`.
**Author: approved (automatic on AI-audit PASS, per author decision 2026-10-21).**

## Targets (17, all in `certify/targets.toml`, module `StatFormal.Wave30tq.Proofs`)
| label | claim / theorem `StatFormal.Wave30tq.(Claims.)…` |
|---|---|
| `lem:onecut (theory.md Lemma 1)`, against every pair of trimmings | `lem1_trim` |
| `lem:onecut (theory.md Lemma 1)`, `θ ≤ inf_{R_α(P)} − sup_{R_α(Q)}` | `lem1` |
| `lem:onecut (theory.md Lemma 1)`, hence `θ ≤ 0` when `TV ≤ α` | `lem1_null` |
| `lem:onecut (theory.md Lemma 1)`, for `f ∈ H` the right side is `T(f)` | `lem1_rkhs` |
| `lem:onecut (theory.md Lemma 1)`, `sup θ` = right side, attained at every quantile pair | `lem1_attain` |
| `lem:ramp (theory.md Lemma 2)` (1), `g ∈ [0,1]` | `lem2_1` |
| `lem:ramp (theory.md Lemma 2)` (2) | `lem2_2` |
| `lem:ramp (theory.md Lemma 2)` (3) | `lem2_3` |
| `lem:ramp (theory.md Lemma 2)` (4) | `lem2_4` |
| `sec:certificate (theory.md §2.3)`, pair statistics | `pair_facts` |
| `thm:betting (theory.md Thm 1)`, fold one fixed | `thm1_cond` |
| `thm:betting (theory.md Thm 1)`, `P(· | D_1) ≤ δ` a.s. | `thm1_condexp` |
| `thm:betting (theory.md Thm 1)`, `sup_{H_{0,α}} P(reject) ≤ δ` | `thm1` |
| `cor:eb-cert (theory.md Cor 1)`, `P(L̂B > Δ | D_1) ≤ δ`, fold one fixed | `cor1` |
| `cor:eb-cert (theory.md Cor 1)`, valid certificate | `cor1_test` |
| `cor:eb-cert (theory.md Cor 1)`, lower confidence bound for TV | `cor1_lcb` |
| `cor:betting-lower (theory.md Cor 2)` | `cor2` |

## Common encodings (declared)
* `β = 1/(1−α)` (`beta`), `ψ_s(u) = s − β·max(s−u, 0)` (`psiS`), `θ(f;s,s') = ∫ψ_s(f) dP − ∫(s' + β·max(f−s', 0)) dQ` (`theta`),
  Bochner integrals of bounded measurable functions (genuine). `f̃ = min(max(f, s'), s)` (`clip`), `g = (f̃ − s')/(s − s')` (`ramp`).
* `R_α(P)`: `P' = P.withDensity(ofReal ∘ γ)` (`trimMeasure`) with the frozen `IsTrimDensity P α γ` (`γ` measurable, `0 ≤ γ ≤ 1/(1−α)`
  everywhere, `∫γ dP = 1`; every `P' ≪ P` with `dP'/dP ≤ β` P-a.s. has such a version of its density, as in `eq:tvintersect`).
  `inf_{P' ∈ R_α(P)} E_{P'} f` is `trimInf P α f = ⨅` over the subtype of trimming densities; `sup_{Q'}` is `trimSup` (`⨆`). For
  `α ∈ [0,1)` the subtype is nonempty (`γ ≡ 1`) and, for bounded `f`, the values are bounded, so there is no `sInf ∅`/unbounded junk.
* `T(f)` (`f ∈ H`): the frozen `Wave17a.sepVal f (region φ α P) (region φ α Q) = ⨅_{a∈𝒞_α(P)} ⟨f,a⟩ − ⨆_{b∈𝒞_α(Q)} ⟨f,b⟩` in `EReal`,
  the paper's estimand as in the frozen `thm:split` claims (Wave22c); `𝒞_{α,k}` is the frozen `TrimmedMMD.Concentration.region`.
* A `p`-quantile `q` of `f` under `μ`: `μ{f < q} ≤ p ≤ μ{f ≤ q}` (`IsQuantileAt`; `F(q−) ≤ p ≤ F(q)`).
* Fold two: `ω = (x, y) ∈ 𝒳^{n} × 𝒳^{m}` under `P^{⊗n} ⊗ Q^{⊗m}` (`n = n₂`, `m = m₂`, i.i.d. and independent samples).
* Block pairing (§2.3): blocks `A_k ⊆ [n]`, `B_k ⊆ [m]` (`k < N`), nonempty and pairwise disjoint on each side (`IsBlockPairing`);
  `Z_k = |A_k|⁻¹Σ_{A_k} g(x_i) − |B_k|⁻¹Σ_{B_k} g(y_j)` (`pairZ`, `blockMean`, nonempty so no `/0`).
* Betting (§2.3): 0-indexed rounds `k = 0, …, N−1`; `λ_k = lam k (Z_0, …, Z_{k−1})` (`past`); `K_t = ∏_{k<t}(1 + λ_k(Z_k − α))`
  (`wealth`); reject iff `∃ t ≤ N, K_t ≥ 1/δ` (`betReject`) — this is `max_{t≤N} K_t ≥ 1/δ` (t = 0 included harmlessly: `K_0 = 1 < 1/δ`).
  "Predictable fractions in `[0, c/(1+α)]`, functions of `D_1` and `Z_1..Z_{k−1}`": fold one fixed: `IsBetRule N α c lam`
  (`lam k` measurable on `ℝ^k`, values in `[0, c/(1+α)]`, for `k < N`); random fold one: `lam : Ω₁ → …` with
  `(d, z) ↦ lam d k z` jointly measurable and the same range.
* Random fold one (`thm1`, `thm1_condexp`, `cor1_test`, `cor1_lcb`, `cor2`): fold one is any probability space `(Ω₁, μ₁)` independent
  of fold two (product `μ₁ ⊗ P^{⊗n} ⊗ Q^{⊗m}`); the rules `g : Ω₁ → 𝒳 → ℝ` (jointly measurable, values in `[0,1]`) and `lam` are
  functions of `D_1 ∈ Ω₁`. The paper's `D_1 = (X^{(1)}, Y^{(1)}) ∼ P^{⊗n₁} ⊗ Q^{⊗m₁}` under a partition fixed in advance, or with an
  independently drawn partition or other independent randomness, is an instance.
* Corollary 1: `sMean`, `uVar = (n−1)⁻¹Σ(u_i − ū)²` (unbiased, `n ≥ 2` so `n − 1 ≥ 1`, real cast), `sigBar n δ₂ V = min{1/2, √V +
  √(2 log(1/δ₂)/(n−1))}`, `ebLB δ₁ δ₂ G H = Ḡ − H̄ − √(2L₁(σ̄_G²/n + σ̄_H²/m)) − (L₁/3)max(1/n, 1/m)`, `L₁ = log(1/δ₁)`, natural log;
  `Δ = ∫g dP − ∫g dQ`. Corollary 2: `levelReject A B useBet α δ δ₁ δ₂ g lam x y` = the betting test (`useBet = true`) or
  "`L̂B > α`" (`useBet = false`); `α̂_lo` is the frozen `TrimmedMMD.Lower.alphaLo` (`eq:downclosed`: `max{α_j : H_{0,α_i}` rejected for
  every `i ≤ j}`, `0` if none; a genuine `Finset.sup'`).
* "With probability at most `δ`": an upper bound on the measure of the event (an outer-measure bound when stated without measurability,
  which is the stronger form for upper bounds); `thm1_condexp` also asserts measurability of the rejection event (so its indicator is
  integrable and the conditional expectation is not the junk `0`).

## Covered — back-translations and deviations

**Lemma 1** (`theory.md:16-31`). Setting for all five claims: probability measures `P, Q` on a measurable space, `α ∈ [0,1)` (§2.1),
`f` measurable and bounded (`∃C, |f| ≤ C`).
* `lem1_trim`: for all `s, s'` and all trimming densities `γ` of `P`, `γ'` of `Q`: `θ(f;s,s') ≤ E_{γ·P} f − E_{γ'·Q} f`.
  (The pointwise form of the printed inequality; the proof's first two displays.)
* `lem1`: for all `s, s'`: `θ(f;s,s') ≤ inf_{P'∈R_α(P)} E_{P'}f − sup_{Q'∈R_α(Q)} E_{Q'}f` — the printed display, literally.
* `lem1_null`: if `TV(P,Q) ≤ α` then the right side is `≤ 0` and `θ(f;s,s') ≤ 0` for all `s, s'` ("Hence …"; the proof's last step).
* `lem1_rkhs`: for a real Hilbert space `H`, strongly measurable `φ` with `‖φ‖ ≤ κ`, and **every** `f ∈ H` (generalisation of
  `f ∈ B_H`; the identity is homogeneous), with the witness `x ↦ ⟨f, φ(x)⟩`: `(inf − sup : ℝ) = T(f)` in `EReal`.
* `lem1_attain`: `sup_{(s,s')∈ℝ²} θ(f;s,s')` equals the right side and is attained (`IsGreatest` of the range); `(1−α)`-quantiles of
  `f` under `P` and `α`-quantiles of `f` under `Q` exist; and `θ(f;q,q') =` the right side for **every** such pair (the print says "at a
  … quantile"; every quantile is a generalisation). With `lem1_rkhs` (the witness is bounded measurable, `|⟨f,φ⟩| ≤ ‖f‖κ`) this gives
  "`sup θ = T(f)`, attained at a quantile pair" for RKHS witnesses; that combination is two certified claims, not one stated claim.

**Lemma 2** (`theory.md:33-46`), `s' < s`, `α ∈ [0,1)`, `f` measurable (bounded for (2)–(4)):
* `lem2_1`: `ramp ∈ [0,1]` everywhere and `θ(f̃;s,s') = β(s − s')(E_P g − E_Q g − α)` (needs only measurability of `f`: `f̃` is bounded).
* `lem2_2`: `θ(f̃) − θ(f) = β E_P(s' − f(X))₊ + β E_Q(f(Y) − s)₊`, and this is `≥ 0`.
* `lem2_3`: `Var_P ψ_s(f̃(X)) ≤ Var_P ψ_s(f(X))` and `Var_Q (f̃(Y) − s')₊ ≤ Var_Q (f(Y) − s')₊` (Mathlib `variance`, finite here).
* `lem2_4` (`s ≤ s'` instead of `s' < s`): `θ(f;s,s') ≤ s − s' ≤ 0` for all `P, Q`. ("so no test of `θ > 0` at that pair has any
  power" is the reading of `θ ≤ 0`; not a separate claim.)

**§2.3 pairing** (`theory.md:80-84`; `Δ ≤ TV` at l.48-49 and l.107-108), `pair_facts`, fold one fixed, `g` measurable `[0,1]`-valued, any block pairing: `Z_k(x,y) ∈ [−1,1]`
for all `k, x, y`; `E Z_k = Δ` for every `k`; `Z_0, …, Z_{N−1}` are mutually independent (`iIndepFun`); and `Δ ≤ TV(P,Q)` (the
elementary inequality for `[0,1]`-valued `g`, used in the proof of Theorem 1).

**Theorem 1** (`theory.md:97-114`). Hypotheses for all three claims: `α ≥ 0`, `δ ∈ (0,1)`, `c ∈ (0,1]`, any block pairing, `g`
measurable with values in `[0,1]`, predictable measurable fractions in `[0, c/(1+α)]`, and `TV(P,Q) ≤ α`.
* `thm1_cond` (fold one fixed): `P^{⊗n} ⊗ Q^{⊗m}(max_{t≤N} K_t ≥ 1/δ) ≤ δ`. This is "`P(· | D_1) ≤ δ`" for **every** value of `D_1`
  (stronger than a.s.), in the encoding of the repository's other split claims (fold one held fixed, `thm:split`).
* `thm1_condexp` (fold one random on `(Ω₁, μ₁)`): the rejection event is measurable and `E[1_{reject} | σ(D_1)] ≤ δ`
  `μ₁ ⊗ P^{⊗n} ⊗ Q^{⊗m}`-a.s. — the printed conditional statement, literally (conditional expectation given the σ-algebra of the
  first factor).
* `thm1` (fold one random): `P(reject) ≤ δ` — "so `sup_{(P,Q)∈H_{0,α}} P_{P,Q}(reject) ≤ δ`" (∀ `P, Q` with `TV ≤ α`).
* Deviations: **generalisations** — `α ≥ 0` instead of `α ∈ [0,1)` (the proof never uses `α < 1`); any number `N` of rounds with any
  nonempty disjoint blocks on both sides (the printed pairing, `n ≤ m`: `A_k = {k}`, `B_k` the `k`-th of `n` consecutive blocks of
  sizes `⌊m/n⌋`/`⌈m/n⌉`, `N = n`; mirror otherwise, is an instance; so are `sacert.pair_up`'s `np.array_split` blocks and the
  equal-block `equal_blocks` variant that drops a remainder); fold one any independent probability space. **Hypotheses made explicit**
  (implicit in "rule" / "functions of"): measurability of `g` and of the fractions (joint in `D_1` for the random-fold-one claims).
  The step "If `ŝ ≤ ŝ'`, do not reject" only removes rejections, so it is covered by these upper bounds; `lem2_4` is why it costs
  nothing. "A rejection certifies `TV(P,Q) > α`" is the reading of the level guarantee (under `TV ≤ α` rejection has probability
  `≤ δ`), not a separate claim. The default rule (`c = 1/2`, the Waudby-Smith–Ramdas plug-in with `w₀ = 20`) is an instance of
  `IsBetRule` (a `min` with the cap, measurable in the past); it is not stated separately.

**Corollary 1** (`theory.md:116-131`), `n, m ≥ 2`, `δ₁, δ₂ > 0` (`δ = δ₁ + 2δ₂`), `g` measurable `[0,1]`-valued:
* `cor1` (fold one fixed): `P^{⊗n} ⊗ Q^{⊗m}(L̂B > Δ) ≤ δ₁ + 2δ₂` — "`P(L̂B > Δ | D_1) ≤ δ`" for every value of `D_1`.
* `cor1_test` (fold one random, `g` a jointly measurable rule): if `TV(P,Q) ≤ α` then `P(L̂B > α) ≤ δ₁ + 2δ₂` ("reject if `L̂B > α`
  is a valid certificate").
* `cor1_lcb` (fold one random): `P(L̂B > TV(P,Q)) ≤ δ₁ + 2δ₂` for every `(P,Q)` ("`L̂B` is a `(1 − δ)` lower confidence bound for TV";
  also the remark after Corollary 2, "with a single ramp … `L̂B` is itself a lower confidence bound").
* "`| D_1`" is encoded per fold only (for every fold-one value, as in the repository's other split claims); unlike Theorem 1 there
  is no conditional-expectation claim for Corollary 1 (it would follow by the same `condExp_indicator_le_of_slices` step).
* No restriction `δ < 1` or `δᵢ ≤ 1` is imposed (for `δ₁ > 1` or `δ₂ > 1/2` the bound is trivial; the proof handles it). "We use
  `δ₁ = 0.8δ`" is a parameter choice, covered as an instance.

**Corollary 2** (`theory.md:137-144`, remarks l.146-148), `cor2`: a fixed grid `α : Fin J → ℝ` with `α_j ≥ 0`, a fixed block pairing, `δ ∈ (0,1)`,
`c ∈ (0,1]`; for each level `j` a fold-one rule `g_j` (jointly measurable, `[0,1]`-valued) and a test choice `useBet j`: betting levels
have predictable jointly measurable fractions in `[0, c/(1+α_j)]` (Theorem 1 at level `α_j`, `δ`), EB levels use Corollary 1 with
`n, m ≥ 2`, `δ₁, δ₂ > 0`, `δ = δ₁ + 2δ₂`; all on the same fold two; `α̂_lo` by `eq:downclosed`. Conclusion:
`P(α̂_lo > TV(P,Q)) ≤ δ` for every `n, m` and every `(P,Q)` (no TV assumption).
* Deviations: **generalisations** — the grid need not be increasing (`α_1 < … < α_J` is not used: the first index with `TV ≤ α_j`
  works for any grid), only `α_j ≥ 0` is needed; levels may mix the two tests; a common cap `c` is no restriction (per-level caps
  `c_j ≤ 1` fit under `c = 1`). The fold-one rules `g_j` and `λ^{(j)}` may depend on `D_1`, and so on each other, arbitrarily; the
  levels' tests share fold one and fold two and need not be independent ("the other levels' tests can depend on each other and on
  `D_1` in any way"). **Declared readings (narrower than the most liberal reading of the print):** the test type per level
  (`useBet`) and the EB split `(δ₁, δ₂)` are fixed in advance and common to all EB levels (as in the printed "`δ₁ = 0.8δ`" and
  `real.py`, which computes one `α̂_lo` per method on one split); each betting level's fractions are predictable in that level's own
  `Z^{(j)}` (as printed: "functions of `D_1` and `Z_1, …, Z_{k−1}`"). A `D_1`-dependent choice of test per level would follow from `cor2`
  at `Ω₁ = Unit` and Fubini, but is not a stated claim; per-level `δ`-splits are not covered.

## Junk-value audit
* Divisions: `1/(1−α)` with `α < 1` (Lemmas 1–2; in Theorem 1 `β` does not occur); `(s − s')` with `s' < s` in `ramp`; block means
  over nonempty blocks; `c/(1+α)` with `α ≥ 0`; `1/δ` with `δ > 0`; `/n`, `/m`, `/(n−1)`, `/(m−1)` with `n, m ≥ 2` (real casts,
  no ℕ subtraction). `(Σ…)/n` in `sMean` with `n ≥ 2`.
* Square roots: `√V` of the sample variance (`≥ 0`); `√(2 log(1/δ₂)/(n−1))`, `√(2L₁·v̄)`: arguments `≥ 0` whenever `δᵢ ≤ 1`; for
  `δ₁ > 1` or `δ₂ > 1` they may be junk `0` but then `δ₁ + 2δ₂ > 1` and the claim is trivially true (as in the paper).
* `log(1/δ)` of positive numbers. `ENNReal.ofReal δ` with `δ ∈ (0,1)`; `ofReal (δ₁ + 2δ₂)` with positive argument.
* `⨅`/`⨆` over trimming densities: nonempty, bounded (see encodings); `sepVal` finite. `IsQuantileAt` uses `μ.real` of measurable sets.
* No `Measure.map`. Conditional expectation (`thm1_condexp`): of the indicator of a set asserted measurable in the same claim,
  w.r.t. `comap Prod.fst` (a sub-σ-algebra of the product σ-algebra; the measure is finite, so σ-finite on the trace) — no junk branch.
* `variance` (Mathlib, `evariance.toReal`): bounded measurable variables, finite.
* Vacuity: all hypothesis sets are satisfiable: `P = Q` any probability measure (TV = 0), `α = 0`, `δ = 1/2`, `c = 1/2`, `g ≡ 0`,
  `n = m = N = 2`, `A_k = B_k = {k}`, `lam ≡ 0` (and `Ω₁ = Unit` with `μ₁ = δ_()`), `δ₁ = δ₂ = 1/4`; trimming densities `γ ≡ 1`.
  `lem2_4`'s `s ≤ s'` and `lem2_1`'s `s' < s` are the paper's two cases.

## Textbook bridges
None. Ville's inequality (finite horizon) is proved in `Lib/Betting/Ville.lean` from Mathlib's optional stopping; the betting
supermartingale in `Lib/Betting/Wealth.lean`; Bernstein (Boucheron–Lugosi–Massart 2013, Thm 2.10 with `c = b/3`, two independent
samples) in `Lib/Bernstein/TwoSample.lean`; Maurer–Pontil 2009 Thm 10 (eq. 3) is the existing `Lib/Bernstein/SampleVariance.lean`
`sqrt_popVar_le` (Hoeffding's permutation representation; constant `√(2 log(1/δ)/(n−1))` as printed); Popoviciu is Mathlib
`variance_le_sq_of_bounded`. Certified premises reused: `TrimmedMMD.ZeroSet.tvintersect` (`eq:tvintersect`), `Wave8a.cvar_core`
(`lem:cvar` for bounded `f`: `inf_γ E[γf]` and `sup_s Eψ_s(f)` attained and equal), `TrimmedMMD.Concentration.inner_integral_smul`,
`TrimmedMMD.Lower.downclosed_measurable_le` (`cor:lower` combinatorics), `Distances.integral_sub_le_mul_tvDist_of_nonneg`.

## Route
* Lemma 1: pointwise `γ(f − s) ≥ −γ(s − f)₊ ≥ −β(s − f)₊` and the mirror, integrated (`psi_le_trim`, `trim_le_upper`); `le_ciInf`/
  `ciSup_le`. Null case: a common trimming from `tvintersect`. Attainment: every `(1−α)`-quantile maximises `s ↦ Eψ_s(f)` (by cases,
  `ψ_s − ψ_q ≤ (s − q) − β(s − q)1{f ≤ q}` for `s ≥ q`, `≤ (s − q) + β(q − s)1{f < q}` for `s < q`); `cvar_core` gives a cut point `s*`
  with `Eψ_{s*}(f) = inf_γ E[γ f]`, so `Eψ_q(f) = trimInf`; the `Q` side through `−f` (an `α`-quantile of `f` is minus a `(1−α)`-quantile
  of `−f`). Quantiles exist: `q = inf{t : p ≤ P(f ≤ t)}` with continuity of measure from above and below. RKHS: `⟨f, ∫γφ dP⟩ = ∫γ⟨f,φ⟩ dP`
  and the `EReal` coercion of a bounded `⨅`/`⨆`.
* Lemma 2: the printed pointwise identities by cases on `f` vs `s'`, `s`; (3): `ψ_s(f̃) = max{ψ_s(f), s − β(s − s')}`,
  `(f̃ − s')₊ = min{(f − s')₊, s − s'}`, and `Var h(W) ≤ E(h(W) − h(EW))² ≤ Var W` for 1-Lipschitz `h` (instead of the printed
  `½E(h(W) − h(W'))²`; same inequality).
* Theorem 1 (paper route): `𝒢_t = σ(Z_i : i < t)`; `Z_k` depends on the coordinates of block `k`, disjoint from earlier blocks, so it
  is independent of `𝒢_k` (`indep_iSup_of_disjoint` on the `n + m` independent coordinates, `MeasurableEquiv.sumPiEquivProdPi`);
  `E[K_{k+1} 1_A] = E[K_k 1_A] + E[K_kλ_k 1_A]·E[Z_k − α] ≤ E[K_k 1_A]` for `A ∈ 𝒢_k` (Mathlib
  `supermartingale_of_setIntegral_succ_le`); `K ≥ 0` since `λ_k(Z_k − α) ≥ −c ≥ −1`; Ville: optional stopping at
  `τ = min{t ≤ N : K_t ≥ 1/δ} ∧ N` and Markov. Random fold one: Fubini over the slices; conditional form: `E[1_S | σ(D_1)] =
  ν(S_{D_1})` a.e. (characterisation of the conditional expectation by set integrals over `fst⁻¹ B`).
* Corollary 1: `{L̂B > Δ} ⊆ E₁ᶜ ∪ E₂ᶜ ∪ E₃ᶜ`; `P(E₁ᶜ) ≤ δ₁` by the two-sample Bernstein for the **upper** tail of
  `(Ḡ − H̄) − Δ` (summands `(G_i − EG)/n ≤ 1/n`, `(EH − H_j)/m ≤ 1/m`, variance `v`; sub-gamma Chernoff with the optimal `λ`, and
  `λ ↑ 3/b` when `v = 0`); `P(E₂ᶜ), P(E₃ᶜ) ≤ δ₂` by Maurer–Pontil Thm 10; Popoviciu `σ ≤ 1/2`; on the good events `v ≤ v̄`.
* Corollary 2: `{α̂_lo > TV} ⊆` rejection of the first level `j₀` with `TV ≤ α_{j₀}` (`downclosed_measurable_le`), a true null; that test
  has probability `≤ δ` by `thm1` or `cor1_test`; if no level has `TV ≤ α_j`, the event is empty.

## Notes for the source (`theory.md`) — one defect in a proof, statements correct
1. **Corollary 1, proof (`theory.md:126-129`): the Bernstein step bounds the wrong tail.** It takes summands `(EG − G_i)/n₂` and
   `(H_j − EH)/m₂` and bounds `P(Δ − (Ḡ − H̄) ≥ √(2vL₁) + L₁b/3)`, but the failure event of the lower bound, `L̂B > Δ`, is
   `(Ḡ − H̄) − Δ > √(2L₁v̄) + L₁b/3` (the upper tail). Corrected wording: "The `n₂ + m₂` summands `(G_i − EG)/n₂ ≤ 1/n₂` and
   `(EH − H_j)/m₂ ≤ 1/m₂` are independent and centered with total variance `v = σ_G²/n₂ + σ_H²/m₂`. Bernstein's inequality … gives
   `P((Ḡ − H̄) − Δ ≥ √(2vL₁) + L₁b/3) ≤ δ₁`." The statement of Corollary 1 is correct (the summands are also bounded above by
   `1/n₂`, `1/m₂`, so the same inequality applies); the Lean proof uses the corrected tail. The docstring of `sacert.lcb_bern2s` has the
   same slip ("Summands `(mu_A − A_i)/n ≤ bA/n` …"); its formula is the correct lower bound.
2. Optional precision: Theorem 1 needs only `α ≥ 0` (not `α < 1`), and any nonempty disjoint blocks; Corollary 2 does not need the grid
   to be increasing; Lemma 1's attainment holds at **every** `(1−α)`-quantile of `f(X)` and **every** `α`-quantile of `f(Y)`.
3. Implicit hypotheses worth one word in the paper: the fold-one rule `g` and the fractions `λ_k` are measurable (jointly in `D_1` when
   fold one is random).

## Not covered (declared)
Lemma 3 (price of fold-one cut points; optional target, not attempted); Proposition 4 (asymptotic power; a proof sketch, excluded by
instruction); §2.4 (cross-fitting, sequential batches); the §2.3 identity `Var Z̄ = Var G/n₂ + Var H/m₂` for equal blocks; the per-sample
Maurer–Pontil remark after Corollary 1; the closing paragraph of §2.3 on Bentkus/Kuchibhotla–Zheng; the fold-one construction of
`ŝ, ŝ'` (leave-one-out quantiles) and `σ₀²` (any fold-one rule is allowed, so they are instances); the default betting rule as a
separate claim (an instance of `IsBetRule`). Informal remarks, read but not formalised: `theory.md:48-52` (the ramp test is the
classifier inequality `E_P g − E_Q g ≤ TV`; its parts used here are `pair_facts` and `lem2_1`), `:66-70` (discussion of Lemma 3's slack),
`:146-148` (the single-ramp remark is `cor1_lcb`; "the set of rejected levels need not be an interval" is a remark).

## Reader face
The `trimmed-mmd (jmlr)` paper id has no `Papers/` page on master (the `Papers/TrimmedMMDJMLR` page and its `PAPERS` entry live on the
unmerged branch `tmmd-jmlr-wave`); when these branches are integrated, regenerate that page (`tools/gen_papers_face.py`) so that
`check_aliases.py` finds aliases for these 17 targets.

## Fidelity review
Fidelity review: independent AI audit, method v1 (certify/AUDIT_METHOD.md), 2026-11-08 — PASS with notes (17 targets; each claim
back-translated blind from `Statements.lean` and the frozen `ZeroSet`/`Concentration`/`Lower`/`Wave17a`/`TV` definitions before reading
this card, then compared clause by clause with `theory.md` §2 at sha256 `5518c814…`, `eq:downclosed`, `eq:trimset`, `eq:lowertrim`;
one `lake env lean` parse check of `sigBar`, `ebLB`, `wealth … 0 = 1` and a consecutive-block `IsBlockPairing`). Approval left to the
integration step (auditor instructed not to approve). Notes:
* All 17 faithful: 9 faithful, 8 faithful generalisations (`f ∈ H` for `B_H`; every quantile for "a" quantile; `lem2_1` for measurable
  `f`; any nonempty disjoint blocks; `α ≥ 0`; every fold-one value / arbitrary independent fold one; any grid). Quantile convention
  checked against the `eq:lowertrim` maximiser set (`F(s−) ≤ 1−α ≤ F(s)`), and on the `Q` side (minimisers of `s' + βE(f − s')₊` are
  the `s'` with `F(s'−) ≤ α ≤ F(s')`). `ebLB`, `sigBar` match the print character by character; `alphaLo` is `eq:downclosed`.
* Junk: none live (all divisions guarded; `√`/`log` junk only where the bound `δ₁ + 2δ₂ > 1` is trivial; `⨅`/`⨆` nonempty and bounded;
  `condExp` not on a junk branch since measurability of the event is part of `thm1_condexp`). Vacuity: none (witness `P = Q`, `α = 0`,
  `δ = 1/2`, `c = 1/2`, `g ≡ 0`, `λ ≡ 0`, `n = m = N = 2`, `A_k = B_k = {k}`, `Ω₁ = Unit`, `δ₁ = δ₂ = 1/4`). Smuggling: none; no
  bridges. Quantifiers: rules chosen after `P, Q, μ₁, N` (more general). Labels and paper id right.
* The "wrong tail" note on Corollary 1's proof is correct; the statement and the `lcb_bern2s` formula are unaffected.
* Applied after the audit: line references corrected (§2.3 `:80-84`, Corollary 1 proof `:126-129`, `eq:downclosed` `:153-167`); the
  Corollary 2 readings (fixed `useBet`, common `(δ₁, δ₂)`, per-level predictability) declared as recommended; the per-fold-only encoding
  of Corollary 1's "`| D_1`" and the informal remarks (`:48-52`, `:66-70`, `:146-148`) listed.
* Optional question for the author (no claim depends on it): is a data-dependent per-level test choice intended in "the test of
  Theorem 1 or Corollary 1"? If yes, a one-line remark in the paper suffices (it follows from `cor2` with a trivial fold one and Fubini).
