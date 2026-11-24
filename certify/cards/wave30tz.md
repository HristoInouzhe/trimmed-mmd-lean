# Fidelity card — wave 30tz: trimmed-mmd (JMLR v2), consistency of the split-sample lower bound `α̂_lo` (`prop:loconsistency`)

Lean: `StatFormal/Wave30tz/Statements.lean` (33 claims; frozen 2026-11-08 before the proofs were integrated, commit `f2983b2`, sha256
`cb21c0c915af01dcc8e8ef7a5018847586cd5fb9630779efdf41a1fc177cd06c`, locked with its 18 imports: Wave30tv, Wave30tq, Wave30ty, Wave30tr,
Wave30tp, Wave17a, the frozen `TrimmedMMD` files `Statements`, `Concentration`, `Unconditional`, `ZeroSet`, `Lower`, `Lib/Distances/TV.lean`
and the files they import). Routes `RouteOrder`, `RouteElem`, `RoutePop`, `RouteFit`, `RouteHoeff`, `RouteBet`, `RouteKS`, `RouteExample`,
`RouteValid`, `RouteIface`, `RouteLower`, `RouteUpper`, `RouteLimits` (untrusted); `Proofs.lean` proves all 33 claims (`theorem c : Claims.c`),
and the gate checks `example : Claims.c := c` and `#print axioms` for each (`[propext, Classical.choice, Quot.sound]`). Paper id
`trimmed-mmd (jmlr)`; labels are the printed ones of `jmlr/v2` with "(v2 …)" and a short description.
Branch `tmmd-jmlr-locons`, based on `tmmd-jmlr-hinge` at `10180c3`, with `tmmd-jmlr-seqbet` (Wave30tq, Wave30tv) merged in (`8e169a0`).
Critic (independent AI reviewer, before the freeze, 2026-11-08): first pass NOT READY — `lo_upper`'s grid-point sharpening is false at
`α* = 0 ∈ 𝒢` (counterexample compiled in Lean), the fraction lower bound was required on unrealizable pasts, and the hypotheses were
vacuous for `σ²_min > 4`; all fixed (see "Changes before the freeze"); second pass READY TO FREEZE.
Fidelity review: independent AI audit, method v1 (certify/AUDIT_METHOD.md), 2026-11-08 — PASS with notes (33 claims back-translated
blind and compared with the NOTE and the printed text at `3bad3e7`; source hashes, lock and line numbers re-checked; notes at the end of
this card, applied).
**Author: approved (automatic on AI-audit PASS, per author decision 2026-10-21).**

## Source
Frozen from the research note `trimmed-mmd/explore/lo_consistency/NOTE.md` (read-only; author decision Q10, 2026-11-08), sha256
`c5e321c3f6f39b999bceea0c57c0d8bcedc011ab7e201633f62877b6d2b9d3ed`: Proposition 1 (§2), Corollary 2 and Proposition 3 (§2), §1
conventions, Lemmas 1–7 (§4), proofs (§5), the §9 print block and the "Lean freeze list".
The result is printed at trimmed-mmd master `3bad3e7` ("JMLR v2 (50 pp): consistency of the split-sample lower bound (prop:loconsistency)"):

| file (at `3bad3e7`) | sha256 | printed items |
|---|---|---|
| `jmlr/v2/sections/04_split.tex` | `5091bcf4ada241cd6d96fbf9294ba4a6f0417a0dc4ed2a4fe4a0497b2d790b52` | `prop:loconsistency` (`:143`), the paragraph after it with the `α = 0` sentences (`:157-159`) |
| `jmlr/v2/appendix/C_split.tex` | `a3a7389e5f2ab7213ce6497a0467ec30585ad9114221f717f51661f1f680e521` | C.5: `eq:fractions` (`:112`), `eq:cutrank` (`:152`), `lem:popramp` (`:157`), proof with `eq:fittedramp` (`:188`), `eq:betbounds` (`:199`), "Upper side", "Lower side", "Refining grids", the remarks after the proof, "A witness fitted at α = 0" (`:242`) |

Context (read-only): `sections/04_split.tex` (`lem:ramp`, `thm:betting`, `cor:lower`, `eq:downclosed`, `eq:witness`), `appendix/B_analytic.tex`
(`thm:twosided`, Step 1), `sections/02_regions.tex` (`ass:regularity`, `eq:qp`).

## Targets (33, all in `certify/targets.toml`, module `StatFormal.Wave30tz.Proofs`)
| printed item | claims |
|---|---|
| `prop:loconsistency` (the proposition) | `lo_consistency` (fixed grid, fixed `δ`: all three sentences), `lo_refining` (the refining-grid sentence) |
| `prop:loconsistency`, further statements of the NOTE (not printed as statements) | `lo_upper` (upper side for every `n, m` and every pair, measurability of `α̂_lo`, the grid-point sharpening for `α* > 0`), `lo_lower_bound`, `lo_strict_bound` (the explicit bounds of §5), `lo_lower` (lower side without (A3), uniform over `D_{α_i} ≥ d`), `lo_exact` (1, third and fourth bullets), `lo_vanishing` (part 2; not printed), `lo_refining_kernel` (part 3 without (A3)) |
| proof of `prop:loconsistency` (down-closed rule, mesh) | `grid_events`, `mesh_point` |
| `eq:cutrank` (convention (C) and "as do the empirical quantiles in the range of the values and their linear interpolations") | `numpy_bracket`, `exact_quantile_bracket` |
| `eq:fractions` ("each square is at most 4") | `fractions_bounds` |
| `lem:popramp` | `pop_ramp_rkhs` (as printed), `pop_ramp` (NOTE freeze item 6, corrected), `pop_ramp_freeze_false` (item 6 as worded is false), `ramp_tv` (NOTE Lemma 1 "TV = sup over ramps"; not printed) |
| `eq:fittedramp` and its paragraph | `fitted_ramp` (NOTE Lemma 4), `crit_identity`, `crit_emp`, `crit_uniform` (Lemma 2), `quantile_bracket` (Lemma 3), `order_stat_shift`, `theta_mono` |
| `eq:betbounds`, first bound | `bet_power` (NOTE Lemma 5), `bet_power_frac`, `log_lower` |
| `eq:betbounds`, second bound | `strict_null` (NOTE Lemma 6), `strict_null_frac` |
| "A witness fitted at α = 0" (C.5) and the main-text sentence | `ramp_ks` (NOTE Lemma 7), `alpha0_example` (Prop 3, the example), `alpha0_valid` (Prop 3, the validity bound) |

## Printed statement → frozen claims (the writer's map, checked)
* `prop:loconsistency` → `lo_consistency` (parts 1 and 3 of the NOTE as printed) and `lo_refining`; the mesh inequality of "Refining
  grids" → `mesh_point`, the down-closed inclusions → `grid_events`. Part 2 (vanishing `δ`), the uniformity and the without-(A3) statements
  are not printed (NOTE Prop 1(2), the uniformity sentence and "Without (A3)") → `lo_vanishing`, `lo_lower`,
  `lo_refining_kernel`. **Checked**: every sentence of the printed proposition is a conjunct of `lo_consistency` or `lo_refining`. The
  printed hypothesis "`σ̂²_{k−1}` floored at a constant `σ²_min > 0`" is covered for every `σ²_min > 0` (the printed proof writes "for
  `σ²_min ≤ 4`"; see Deviations).
* `eq:cutrank` → convention (C), `CutsC` (with `rkLo`, `rkHi`), the arithmetic fact and `npQuantile` in `numpy_bracket`, the exact
  quantiles in `exact_quantile_bracket`. "Their linear interpolations" is covered for numpy's (the code's) scheme; any convex combination
  of exact quantiles in the range also lies in the bracket (it is an interval). (The writer's map says "the arithmetic fact of `quantile_bracket`"; it is in `numpy_bracket`.)
* `lem:popramp` → `pop_ramp_rkhs` (exactly the printed lemma; the NOTE's "TV = sup over ramps" corollary is `ramp_tv`, not printed).
* `eq:fittedramp` and its paragraph → `fitted_ramp` (the NOTE's freeze list calls the deterministic core `fitted_ramp_det`; the frozen claim
  is the full Lemma 4 for the QP construction, which contains it), `crit_uniform`, `quantile_bracket`, `order_stat_shift`.
* `eq:betbounds`, first bound → `bet_power` + `log_lower` (`a = λ_max ≤ 1/2`, `c_a ≤ 2`) and `bet_power_frac`. **Constants checked**: the
  printed `ε_N(ϱ) = exp{−(σ²_min/(4L))(ϱ√(NL/2) − L − 16L/σ²_min)₊²}` under `N ≥ 2L/λ²_max` is IMPLIED by the frozen form with
  `4L(1+α)²/σ²_min` under `N ≥ L(1+α)²/(2λ²_max)`, because `(1+α)² ≤ 4` for `α < 1`: the printed `N`-condition implies the frozen one, and
  the frozen `ε_N` is `≤` the printed one (a smaller subtracted term). Both need `σ²_min ≤ 4` ("for `σ²_min ≤ 4`" in the printed proof), a
  hypothesis of `bet_power_frac` and `lo_lower_bound`. The printed sentence "`log K_N ≥ ϱ(NL/2)^{1/2} + M_N − 4L(1+α)²/σ²_min`" is the
  frozen bound's drift (`c_a N λ̄²(1+α)² ≤ 4L(1+α)²/σ²_min`). The step from the printed event ("every batch has a ramp and
  `Δ_k ≥ α + ϱ`") to the frozen hypothesis on `E` (`λ_k ≥ λ_N`) goes through `fractions_bounds` (the realized `Z_k ∈ [−1,1]`, so
  `σ̂² ≤ 4`) and uses `α < 1`.
* `eq:betbounds`, second bound → `strict_null`, `strict_null_frac`. **Checked**: `δ^{2ζ/λ̄_N} ≤ exp(−ζσ_min√(2NL))` is the fourth conjunct of
  `strict_null_frac` (for `N ≥ 1`; at `N = 0` there is no rejection), and the printed bound `P ≤ exp(−ζσ_min(2NL)^{1/2})` is its third
  conjunct (no condition on `N`). The remark "a floor that shrinks with `N` would leave only `δ^{2ζ(1+α)/λ_max}`" is the second conjunct
  (`δ^{2ζ/λ_cap}`, `λ_cap = λ_max/(1+α)`). The refining-grid bound `e^{−εσ_min(NL/2)^{1/2}}` is the third conjunct at `ζ = ε/2`.
* "A witness fitted at α = 0" → `ramp_ks` (layer cake and `E_Pg − E_Qg ≤ KS⁺(f)`), `alpha0_example` (the laws, `TV = 0.6`,
  `KS⁺(f₀) = 0.4`), and the predictable-indicator supermartingale → `alpha0_valid`. Not covered: "`f̂_{0,b}` … tend to `f₀` uniformly,
  almost surely", "`KS⁺(f̂_{0,b}) = KS⁺(f₀)` once `f̂_{0,b}` is uniformly within half the smallest gap", "every level `α ≥ 0.4` is rejected
  with probability at most `δ + o(1)`".

## Encodings (declared)
* **(A1)–(A3)** as in `Wave30tr`, `Wave30ty` and the frozen `TrimmedMMD` claims: `H` a real inner-product space (complete, and separable
  where `lem:hinge` or `eq:zeroeq` is used), `φ : 𝒳 → H` strongly measurable with `‖φ x‖ ≤ κ` (`k(x,x) = ‖φ x‖²`), `f(x) = ⟨f, φ x⟩`; (A3)
  is `ZeroSet.Characteristic` (mean embedding injective on probability measures). **Generalisations**: `κ` any bound on `‖φ‖`, `Dφ` any
  bound on `‖φ x − φ x'‖` (the printed `κ`, `D_φ` are the least ones); `𝒳` any measurable space. `α* = TV(P,Q)` (`tvDist`).
* **Data**: `(x, y) ∈ 𝒳^n × 𝒳^m` under `sampleLaw P Q n m = P^{⊗n} ⊗ Q^{⊗m}`; no auxiliary randomness — the frozen `Wave30tv` definitions
  (`IsBatchRule`, `IsBatchBetRule`, `seqZ`, `seqReject`) with `U = Unit` (`IsFitRule`, `IsFracRule`, `pairStat`, `rejects`). The printed
  procedure has no auxiliary randomness (random features are not covered; see below).
* **Batches and pairs**: `Wave30tv.IsBatchPairing` (any batch labels, pairs numbered batch by batch, nonempty disjoint blocks inside the batch
  of the pair); the printed cut at fixed fractions with `N_b = min(n_{[b]}, m_{[b]})` pairs is an instance (**generalisation**). The fitting
  sample of batch `b` is `fitSample` (batches `0, …, b−1`, in index order, `Finset.orderEmbOfFin`; the witness, cut points and suprema do not
  depend on the order).
* **The asymptotic regime** "`n, m → ∞` with the batch fractions fixed": a family `R n m` of runs with `IsSizedRun c C0 Bmax` (pairs in
  batches `≤ Bmax`, fitting samples of sizes `≥ cn − C0` and `≥ cm − C0`, `N ≥ c·min(n,m) − C0`). The printed cut at fixed fractions
  `0 = e_0 < … < e_{B+1} = 1` satisfies it with `Bmax = B`, `c = min_b(e_{b+1} − e_b)`, `C0 = B + 1` for any rounding of `e_b n`
  (**generalisation**; the rounding is not specified in the paper).
* **Per-level witnesses with cut points satisfying (C)** (`IsWitnessRamp`, required for every batch holding a pair, for every level): for
  SOME exact minimizer `(w, v)` of `eq:qp` (`IsQPMin`: capped simplices `0 ≤ w_i ≤ [n(1−α)]⁻¹`, `Σ w_i = 1`, minimal
  `‖Σ w_i φ(X_i) − Σ v_j φ(Y_j)‖`) and, when `D̂ > 0`, SOME cut points satisfying (C) for the own-term values (`ownX`, `ownY`:
  `h̃_i = f̂(X_i) − w_i k(X_i,X_i)/D̂`, `h̃'_j = f̂(Y_j) + v_j k(Y_j,Y_j)/D̂`), the batch is bet on iff `t > u`, and then `g` is the ramp of the
  witness `f̂ = (Σ w φ(X) − Σ v φ(Y))/D̂` (`eq:witness`; `0` when `D̂ = 0`, then no bet) between `u` and `t`; empty fitting side: no bet.
  The minimizer and the cut points may depend on the data in any way; the paper's admissibility of the resulting rule (joint
  measurability, dependence on the earlier batches only) is required separately (`IsFitRule`, `IsFracRule`). **Assumed, not proved**: the
  existence of a jointly measurable selection (NOTE §1: "a measurable selection of the minimizer exists"); **exact QP minimizer** (NOTE
  Remark 4; the approximate-solution remark is not covered). Order statistics: `ordStat h k` = the least `v` with `#{h_i ≤ v} ≥ k`
  (the `k`-th smallest value, ties counted), used only for `1 ≤ k ≤ n`; `ι⁻ = rkLo = max(1, ⌈np⌉ − 1)`, `ι⁺ = rkHi = min(n, ⌊np⌋ + 2)`.
* **Fractions `eq:fractions`** enter through the bounds they satisfy (NOTE §1 "Fractions"; printed "each square in eq:fractions is at most
  4"): `λ_k ≤ λ̄_N = lamHi = min{λ_max/(1+α), √(2L/(Nσ²_min))}` always; `λ_k ≥ λ_N = lamLo = min{λ_max/(1+α), √(2L/(N·max(σ²_min, 4)))}` on a
  batch that is bet on, for every realizable past (`Z_l ∈ [−1,1]`); `λ_k = 0` otherwise (`IsWitnessRun`). `λ_N = min{λ_max/(1+α), √(L/(2N))}`
  for `σ²_min ≤ 4` (printed); the `max(σ²_min, 4)` makes the hypotheses consistent for every floor. `fractions_bounds` proves that the printed
  running estimate (`w₀ > 0`, `σ₀² ∈ [0,4]`, sums and counts over the pairs bet on, floor `σ²_min > 0`) gives these bounds, so the printed
  fractions are an instance (**generalisation**: any predictable fractions with these bounds). `λ_max ∈ (0, 1/2]` (printed `λ_max = 1/2`).
* **Grids**: `IsGrid α` (strictly increasing, in `[0,1)`), `α_{j*} = gridBelow α TV` (`0` if no level is below `TV`), mesh `gridMesh`
  (`sup_{a∈[0,1)} infDist(a, 𝒢 ∪ {0})`), `α̂_lo` the frozen `TrimmedMMD.Lower.alphaLo` (`eq:downclosed`).
* **Limits** in explicit form: "`∀ ε > 0, ∃ N₀, ∀ n m ≥ N₀, P(…) ≤ ε`" (convergence in probability: `∀ ε η > 0, ∃ N₀, …`;
  `liminf ≥ 1 − δ`: `∀ ε > 0, ∃ N₀, … ≥ 1 − δ − ε`). Levels `δ_{n,m}`: a fixed `δ` is the constant sequence; "`log(1/δ) = o(min(n,m))`" is
  "`∀ η > 0, ∃ N₀, ∀ n m ≥ N₀, log(1/δ_{n,m}) ≤ η·min(n,m)`"; "`δ_{n,m}` as in (2)" for refining grids is "eventually `≤ δ̄ < 1`" plus the
  `o(·)` condition (it covers both a fixed `δ` and `δ_{n,m} → 0`).
* **Proposition 3's example**: `exP`, `exQ` as sums of Dirac masses on `ℝ` (`0.2i/210 = i/1050`), the Gaussian kernel `k(a,x) = exp(−(a−x)²/2)`
  (`σ = 1`), `MMD(P,Q)² = ∫∫k dPdP − 2∫∫k dPdQ + ∫∫k dQdQ` (`mmdGauss`), `f₀(x) = (∫k(a,x)dP − ∫k(b,x)dQ)/MMD` (`exWitness`, the mean
  embeddings evaluated by the reproducing property). `KS⁺(f) = sup_{x∈ℝ}{P(f > x) − Q(f > x)}` (`ksPlus`, a bounded supremum).

## Deviations
* **Generalisations** (declared above): kernel constants, any batch structure and pairing with the size conditions, any predictable
  fractions within the bounds, any minimizer and cut points satisfying (C), `λ_max ∈ (0,1/2]`, `δ_{n,m}` sequences; `ramp_ks` for every
  measurable `f` (printed: `f ∈ B_H`) and every nondecreasing `h : ℝ → [0,1]`; `alpha0_valid` for any predictable direction `F_b` and any
  nondecreasing `[0,1]`-valued link (printed: one witness fitted at `α = 0`, any cut points); `fitted_ramp` for any fitting sample;
  `crit_identity` for any second pair of probability measures; `lo_lower` uniform over the pairs with `D_{α_i} ≥ d` (indexed by the grid level
  `α_i`; the NOTE's form indexed by any `a` with `D_a ≥ d` follows from the monotonicity of `α ↦ D_α`, proved in the routes
  (`dpop_antitone`) but not frozen).
* **Made explicit / stronger hypotheses** (declared): `bet_power_frac` and `lo_lower_bound` take `σ²_min ≤ 4` (their `ε_N` uses the drift
  `ϱ√(NL/2)`, i.e. `λ_N = √(L/(2N))`, which needs it; the NOTE's §1 "`σ̂² ∈ [σ²_min, 4]`" presupposes it, the printed proof says "for
  `σ²_min ≤ 4`"). `bet_power` takes `λ ≥ 0`, `ϱ > 0` (printed in Lemma 5). `lo_upper`'s sharpening takes `TV > 0` (false otherwise; source
  defect 1). `lo_refining` takes `δ_{n,m}` eventually `≤ δ̄ < 1` (NOTE: "at fixed `δ` or with `δ_{n,m}` as in 2", both instances).
* **Specialisation**: none of the printed statements; the asymptotic claims hold for every floor `σ²_min > 0`, as printed.

## Back-translations (blind form; plain mathematics of each frozen claim)
* `numpy_bracket`: for `n ≥ 1`, `p ∈ [0,1]` and reals `h_1..h_n`: `⌈np⌉ − 1 ≤ ⌊(n−1)p⌋ + 1`, `⌊(n−1)p⌋ + 2 ≤ ⌊np⌋ + 2`, and
  `h_(r) + ((n−1)p − ⌊(n−1)p⌋)(h_(min(n,r+1)) − h_(r))`, `r = ⌊(n−1)p⌋ + 1`, lies in `[h_(ι⁻(n,p)), h_(ι⁺(n,p))]`.
* `exact_quantile_bracket`: if `#{h_i < q} ≤ np ≤ #{h_i ≤ q}` and `min h ≤ q ≤ max h` then `q ∈ [h_(ι⁻(n,p)), h_(ι⁺(n,p))]`.
* `fractions_bounds`: for `w₀ > 0`, `σ₀² ∈ [0,4]`, `α ∈ [0,1)`, `Z_i ∈ [−1,1]`, any set `S` of pairs, `σ²_min > 0`, `L ≥ 0`: the running
  variance is in `[0,4]`; `σ̂² = max(σ²_min, ·) ∈ [σ²_min, max(σ²_min,4)]`; `λ_N ≤ min{λ_max/(1+α), √(2L/(Nσ̂²))} ≤ λ̄_N`.
* `pop_ramp`: bounded measurable `f` with `f(x) − f(x') ≤ D_φ`, `t ≤ sup f`, `u ≥ inf f`, `θ(f;t,u) ≥ d > 0` ⇒ `u < t`, `t − u ≤ D_φ`,
  excess of the ramp `≥ d/(βD_φ)`.
* `pop_ramp_freeze_false`: not every bounded measurable `f` with `θ(f;t,u) > 0` and `f(x) − f(x') ≤ D_φ` has ramp excess `≥ θ/(βD_φ)`.
* `pop_ramp_rkhs`: (A1)–(A2), `α ∈ [0,1)`, `a ∈ 𝒞_α(P)`, `b ∈ 𝒞_α(Q)` with `‖a − b‖ = D_α > 0`, `f* = (a−b)/‖a−b‖`, `t*` the least
  `(1−α)`-quantile of `f*` under `P`, `u*` the greatest `α`-quantile under `Q` ⇒ `D_α ≤ t* − u* ≤ D_φ`, excess `≥ D_α/(β(t*−u*)) ≥ D_α/(βD_φ)`.
* `ramp_tv`: (A1)–(A3) ⇒ `TV(P,Q)` is the least upper bound of `{E_P g − E_Q g}` over ramps of `f ∈ B_H` with cuts `t > u`.
* `crit_identity`: probability measures `P,Q,P',Q'`, bounded measurable `f`: `θ_{P,Q} − θ_{P',Q'} = −β[(P−P')(t−f)₊ + (Q−Q')(f−u)₊]`.
* `crit_emp`: `θ` of the empirical measures `= T(t) − U(u)`.
* `crit_uniform`: (A1), `n, m ≥ 1`, `‖f‖ ≤ 1`: `θ(f;t,u) − θ_n(f;t,u) ≥ −βZ`; and `(P − P_n)(t − f)₊` equals its value at some `t₀ ∈ [−κ,κ]`.
* `quantile_bracket`: (a) `t ∈ [h_(ι⁻(n,1−α)), h_(ι⁺(n,1−α))]`, range `≤ R` ⇒ `T(t') − T(t) ≤ (β/n)R` ∀ `t'`; (b) mirror for `U` at `α`;
  (c) `T`, `U` are `max(1, β−1)`-Lipschitz.
* `order_stat_shift`: `h_i − ε ≤ h̃_i ≤ h_i` ∀ i ⇒ `h_(k) − ε ≤ h̃_(k) ≤ h_(k)` (`1 ≤ k ≤ n`).
* `fitted_ramp`: (A1), `H` complete, `n, m ≥ 1`, `(w,v)` an exact QP minimizer, `βZ⁻ < D_α` ⇒ `D_α − βZ⁻ ≤ D̂`, `D̂ > 0`, and for all `(t,u)`
  satisfying (C) for the own-term values: `t − u ≤ D_φ`, `θ(f̂;t,u) ≤ t − u`, `Θ ≤ θ(f̂;t,u)` (`Θ` with `r = 1/n + 1/m`), and `Θ > 0` ⇒ `u < t`
  and the ramp excess `≥ Θ/(βD_φ)`.
* `theta_mono`: `0 ≤ α ≤ α' < 1`, `Z, Z⁻, D_φ, r ≥ 0`, `β(α')Z⁻ < D ≤ D'` ⇒ `Θ(α', D) ≤ Θ(α, D')`.
* `log_lower`: `a ∈ [0,1)`, `x ≥ −a` ⇒ `log(1+x) ≥ x − x²/(2(1−a)²)`.
* `bet_power`: admissible rule and fractions `λ_k ∈ [0, λ̄]`, `λ̄(1+α) ≤ a < 1`, `λ ≥ 0`, `ϱ > 0`, `E` with `λ_k ≥ λ`, `Δ_k ≥ α + ϱ` for all `k`
  ⇒ `P(E ∩ {no rejection}) ≤ exp(−(Nλϱ − Nλ̄²(1+α)²/(2(1−a)²) − L)₊²/(2Nλ̄²))`.
* `bet_power_frac`: the same with `λ = λ_N`, `λ̄ = λ̄_N`, `λ_max ≤ 1/2`, `σ²_min ∈ (0,4]`, `N ≥ L(1+α)²/(2λ²_max)` ⇒ `≤ ε_N(ϱ)`; and `ε_N(ϱ') ≤ ε`
  for all `N ≥ N₀`, `ϱ' ≥ ϱ`, `0 < L ≤ ηN` (some `η > 0`, `N₀`).
* `strict_null`: `TV ≤ α − ζ`, `ζ > 0`, fractions `≤ λ̄` ⇒ `P(reject) ≤ exp(−2ζL/λ̄)`. `strict_null_frac`: with `λ̄ = λ̄_N`:
  `P ≤ δ^{2ζ/λ̄_N}`, `≤ δ^{2ζ/λ_cap}`, `≤ exp(−ζσ_min√(2NL))`, and `δ^{2ζ/λ̄_N} ≤ exp(−ζσ_min√(2NL))` for `N ≥ 1`.
* `grid_events`: grid `α`, any rejections: `α̂_lo > gridBelow α a` ⇒ the first level `≥ a` exists and is rejected; `α̂_lo < α_i` ⇒ some
  `j ≤ i` is not rejected. `mesh_point`: `a ∈ [0,1)` ⇒ some `b ∈ 𝒢 ∪ {0}` with `a − 2h ≤ b ≤ a`.
* `lo_upper`: admissible run, every pair: `α̂_lo` measurable, `P(α̂_lo > α_{j*}) ≤ δ`, and `TV ∈ 𝒢`, `TV > 0` ⇒ `P(α̂_lo ≥ TV) ≤ δ`.
* `lo_strict_bound`: every grid level `≥ TV` is `≥ TV + ζ` ⇒ `P(α̂_lo > α_{j*}) ≤ δ^{2ζ/λ_max}` and `≤ exp(−ζσ_min√(2NL))`.
* `lo_lower_bound`: Proposition 1's run, batches `≤ B`, `σ²_min ≤ 4`, fitting sizes `≥ 1` with `1/n_b + 1/m_b ≤ r`, `0 < d ≤ D_{α_i}`, (S),
  `N ≥ L(1+α_i)²/(2λ²_max)` ⇒ `P(α̂_lo < α_i) ≤ 2B exp(−2(τ_* − μ₁)₊²/(D_φ² r)) + J ε_N(ϱ_*)`.
* `lo_lower`: runs in the regime, `log(1/δ) = o(min(n,m))`: `∀ i, d > 0, ε > 0, ∃ N₀, ∀ n m ≥ N₀, ∀ (P,Q)` with `D_{α_i} ≥ d`:
  `P(α̂_lo < α_i) ≤ ε`.
* `lo_consistency`: (A1)–(A3), fixed grid and `δ`, runs in the regime: `P(α̂_lo > α_{j*}) ≤ δ` ∀ n, m; `P(α̂_lo < α_{j*}) → 0`; `TV ∉ 𝒢` ⇒
  `P(α̂_lo > α_{j*}) → 0`.
* `lo_exact`: `TV ∉ 𝒢` ⇒ `P(α̂_lo = α_{j*}) → 1`; `TV ∈ 𝒢` ⇒ `P(α̂_lo = α_{j*}) ≥ 1 − δ − ε` eventually.
* `lo_vanishing`: `δ_{n,m} → 0`, `log(1/δ) = o(min(n,m))` ⇒ `P(α̂_lo = α_{j*}) → 1`.
* `lo_refining`: (A1)–(A3), grids with mesh `→ 0`, `log J = o(min)`, `δ_{n,m}` eventually `≤ δ̄ < 1` with `log(1/δ) = o(min)` ⇒
  `P(|α̂_lo − TV| > ε) → 0` ∀ ε. `lo_refining_kernel`: without (A3): `D_a > 0` ⇒ `P(α̂_lo < a − ε) → 0`; `P(α̂_lo > TV + ε) → 0`.
* `ramp_ks`: measurable `f`, `t > u`: `E_P g − E_Q g = ∫_0^1 {P(f > u + s(t−u)) − Q(f > u + s(t−u))} ds ≤ KS⁺(f)`; nondecreasing
  `h : ℝ → [0,1]`: `E_P h(f) − E_Q h(f) ≤ KS⁺(f)`.
* `alpha0_example`: `exP`, `exQ` probability measures, `TV = 3/5`, `MMD > 0`, `KS⁺(f₀) = 2/5`, every ramp of `f₀` has excess `≤ 2/5`.
* `alpha0_valid`: admissible rule whose ramps are nondecreasing `[0,1]`-transforms of predictable jointly measurable directions `F_b`:
  `P(reject H_{0,α}) ≤ δ + P(∃ k, KS⁺(F_{bat k}) > α)`, every pair.

## Defects of the source, with corrected wording
1. **NOTE §5 (Proposition 1(1), upper side, last sentence) and §6** — "When `α*` is a grid point, this gives `P(α̂_lo ≥ α*) ≤ δ`, which
   sharpens cor:lower": **false** at `α* = 0 ∈ 𝒢` (then `α̂_lo ≥ 0 = α*` surely; the critic compiled the counterexample in Lean: `𝒳` a point,
   `P = Q`, `J = 1`, `α_1 = 0`). Corrected: "When `α* > 0` is a grid point, …" (`lo_upper`). The paper does not print this sentence.
2. **NOTE "Lean freeze list", item 6** (`pop_ramp`, abstract form: "If `θ(f;t,u) = D > 0` and `sup f − inf f ≤ D_φ`, then
   `E_Pg − E_Qg − α ≥ D/(βD_φ)`"): **false** as worded (certified counterexample `pop_ramp_freeze_false`: `P = δ_1`, `Q = δ_0`,
   `f = (x ∨ 0) ∧ 1`, `α = 0`, `t = 2`, `u = 0`, `D_φ = 1`: `θ = 1`, the ramp is `f/2`, its excess `1/2`). Corrected: "… and the cut points
   lie in the range of `f` (`t ≤ sup f`, `u ≥ inf f`), …" (`pop_ramp`). Lemma 1 itself and the printed `lem:popramp` are right (their
   quantiles lie in the range).
3. **NOTE freeze list, item 4**: "For finite measures, the identity `θ − θ_n = −β[…]`" — true only for measures of equal total mass (the
   constants `t`, `u` must cancel); corrected: "for probability measures" (`crit_identity`).
4. **NOTE freeze list, item 7**: the item omits the sign conditions of Lemma 5 (`λ > 0`, `ϱ > 0`); the bound fails when `λ < 0` and
   `ϱ < 0` (then `Nλϱ > 0` while the test may have no power); either sign condition alone suffices, the frozen claim assumes both
   (`0 ≤ λ`, `0 < ϱ`), as Lemma 5 does.
5. **Printed `prop:loconsistency` vs its proof**: the proposition takes any floor `σ²_min > 0`, the proof's fraction bounds are derived
   "for `σ²_min ≤ 4`" (with `σ²_min > 4` the floor is always active and `λ_k = √(2L/(Nσ²_min))`, below the printed `λ_k ≥ (L/(2N))^{1/2}`).
   The proposition is true for every floor (`lo_consistency` etc. cover all `σ²_min > 0`). Suggested fix, either: assume `σ²_min ≤ 4` in
   the proposition (it covers the code's `10⁻⁸`); or run the argument with `max(σ²_min, 4)` in place of `4` throughout, which changes the
   lower fraction to `(2L_δ/(N\max(\sigma^2_{\min},4)))^{1/2}` AND the drift of `ε_N` to `ϱ(2NL_δ/\max(\sigma^2_{\min},4))^{1/2}` (for
   `σ²_min > 4` the displayed first bound of `eq:betbounds` does not follow as written).
6. **Cosmetic** (NOTE §9 proposed labels `lem:critunif`, `lem:nearquantile`, `lem:fittedramp`, `lem:betpower`, `lem:strictnull`,
   `prop:alphazero` are not printed; the targets use the printed `eq:fittedramp`, `eq:betbounds` and `prop:loconsistency`).

## Changes before the freeze (critic)
`lo_upper` third conjunct: `0 < TV` added (defect 1). `IsWitnessRun`: the fraction lower bound is required only for realizable pasts
(`Z_l ∈ [−1,1]`), so the printed `eq:fractions` rule is literally an instance. `lamLo` takes `max(σ²_min, 4)` (removes the vacuity of the
run hypotheses for `σ²_min > 4`); `bet_power_frac`, `lo_lower_bound` take `σ²_min ≤ 4`. `strict_null_frac` states the printed
`δ^{2ζ/λ̄_N}`, the NOTE's `δ^{2ζ/λ_cap}` and the printed chain. `bet_power`: `λ ≥ 0`, `ϱ > 0`. Rename `pop_ramp_printed_false` →
`pop_ramp_freeze_false`.

## Junk-value audit
* `ordStat` is an `sInf`: for `1 ≤ k ≤ n` the set `{v : #{h_i ≤ v} ≥ k}` is nonempty and bounded below (attained at `h_(k)`); all ranks used
  are in `[1,n]` (`rkLo ≥ 1`, `rkHi ≤ n`, `numpy` ranks `⌊(n−1)p⌋+1 ∈ [1,n]`); ℕ subtraction in `rkLo` is under `max 1`.
* Divisions: `1/(n(1−α))`, `β/n`, `1/n_b` with `n, m, n_b, m_b ≥ 1` where used (hypotheses); `1/qpVal` in `witness`, `ownX`, `ownY` is the
  printed "`f̂ = 0` when the minimum is zero" convention and is only used for `D̂ > 0`; `fitTheta`'s `D − βZ⁻ > 0` by hypothesis;
  `lamLo`, `lamHi` at `N = 0` give `0` (no pairs; no claim depends on it); `epsN` with `L > 0` (`δ < 1`); `d/(2βD_φ)` with `D_φ > 0`
  forced by `D_α > 0`; `/hi` in `strict_null` (`hi ≤ 0` gives a bound `≥ 1`, true); `δ^x` rpow of `δ ∈ (0,1)`.
* Suprema: Wave30ty's `hingeZ`, `hingeZm` (with `hingePos`, `r = 1`, `ρ₁ = ρ₂ = κ`) are bounded suprema (no junk); `ksPlus` is a supremum of values in `[−1,1]`; `gridMesh` a supremum of
  values in `[0,1)`; `⨆ f`, `⨅ f` in `pop_ramp` for bounded `f` on a nonempty space; `gridBelow` is a `sup'` of a nonempty finset or `0`.
* Measures: no `Measure.map` in the statements; probabilities of possibly non-measurable sets are outer measures (an upper bound on an
  outer measure is the stronger statement; the sets are measurable — `lo_upper` proves `α̂_lo` measurable); lower bounds `1 − ε ≤ P(α̂ = a)`
  are on measurable sets.
* Vacuity: the run hypotheses are satisfiable (the printed procedure with a measurable selection; `lamLo ≤ lamHi` always; the fraction
  lower bound only on realizable pasts); `IsSizedRun` holds for the printed cut; the grid and level hypotheses are the printed ones.
* Smuggling: none (the witness/QP/cut/fraction hypotheses describe the procedure; no hypothesis states a probability bound).

## Certified results reused (not re-proved)
Wave30tq `lem2_1`, `lem2_2`, `lem1_attain`-style CVaR facts and `pairZ_mem`, `delta_le_tv`; Wave30tv `thm_betting` (upper side),
`measurableSet_seqReject`, the coordinate-freezing route (`integral_mul_coord`, `integral_mul_pairZ`, `predSet`, `seqFiltration`, `core_level`
as template); Wave30ty `hinge`, `hinge_tail_strict` (fitting event); Wave30tr `ek_le` and the Step-1 projection argument
(`setDist_region_le`, adapted to a QP target point); `TrimmedMMD.ZeroSet.zeroeq` ((A3)); `Lib/Betting/Predictable` (`betting_ville_pred`);
Mathlib's Hoeffding lemma (`hasSubgaussianMGF_of_mem_Icc`) for the two-point law; the `TrimmedMMD.Concentration` CVaR witnesses
(`exists_cvar_witness`, `integral_mul_le_cvar`).

## Not covered (declared)
Corollary 2 (rate under `ass:margin`; printed only as a remark after the proof) and Remarks 1–5 (floor dependence, random features with a
data-driven bandwidth, a data-driven Gaussian bandwidth, approximate QP solutions — printed "A minimizer … with Frank–Wolfe gap … serves
with `(1−ρ/2)D_*`" —, M1's formula); Proposition 3's convergence part (`f̂_{0,b} → f₀` a.s., `KS⁺(f̂_{0,b}) = 0.4` eventually, the limit
statement for levels `≥ 0.4`, the 24 distinct atom values as such); `log ε_N ∼ −σ²_min ϱ² N/8`; the existence of a measurable selection of
the minimizer and cut points; without (A3) the off-grid upper limit only as the explicit `lo_strict_bound` (the NOTE's "the upper
statements are uniform over all pairs" is certified for the "`≤ δ`" statement, `lo_upper`); the §7 numerical checks.

## Coverage note (COVERAGE.md rows)
* `prop:loconsistency`: "certified: the printed proposition (upper side ≤ delta for all n,m; lower side -> 0; off-grid upper side -> 0;
  refining grids: alpha-hat -> alpha* in probability) for per-level witnesses with any exact QP minimizer and cut points in eq:cutrank,
  eq:fractions with any floor sigma^2_min > 0, fixed batch fractions; also the explicit bounds, the lower side without (A3) uniformly over
  D >= d, the exact-limit bullets, vanishing delta (NOTE Prop 1(2), not printed), refining grids without (A3); measurable selection
  assumed (Wave30tz)".
* `eq:cutrank`, `eq:fractions`, `lem:popramp`, `eq:fittedramp`, `eq:betbounds`: see the rows.

## Proof routes (untrusted; notes)
`fitted_ramp`: Step 1 of `thm:twosided` by the projection argument of `Wave30tr.setDist_region_le` with the QP point as target; QP
first-order conditions along segments; finite strong duality from the CVaR witnesses of the empirical law; own-term shift; Lemma 3;
Lemma 2. Lemmas 5–6: a conditional Hoeffding lemma for a block pair (two-point Hoeffding bound and freezing) and Ville's inequality for
products of predictable supermartingale factors. `alpha0_valid`: the predictable indicator `1{Δ_k ≤ α}` (a measurable function of the
earlier batches; it equals `1` wherever every `KS⁺(f_b) ≤ α`, by Lemma 7) in place of the printed `1{KS⁺(f̂_{0,b}) ≤ α}`, so no
measurability of `KS⁺` is needed; the proof does not use the predictability of `F_b`. Proposition 1: a general lower-side bound for every
floor (`RouteIface.CoreLowerBound`, the fitting event by `lem:hinge` on the fitting sub-sample, whose law is `P^{⊗n_b} ⊗ Q^{⊗m_b}`), the
monotonicity of `α ↦ D_α`, the upper side by `thm:betting` and `strict_null_frac`; the refining-grid upper side through a one-level
sub-run.

## Fidelity review
Independent AI audit, method v1 (certify/AUDIT_METHOD.md), 2026-11-08 — PASS with notes. All 33 claims faithful (faithful with note:
`numpy_bracket` — numpy's interpolation scheme; `bet_power_frac` — the implication to the printed first bound of `eq:betbounds` checked,
via `fractions_bounds`; `lo_vanishing` — label). Notes, all applied: (1) `lo_vanishing` was attributed to a printed sentence that is not
in the text at `3bad3e7` (it was in an earlier draft) — now "not printed (NOTE Prop 1(2))" on the card, in the target label and the
COVERAGE row; (2) the `α = 0` sentences of `04_split.tex` are at `:157-159`; (3) route-internal names in the junk audit replaced by frozen
ones; (4) defect 4 reworded (either sign condition suffices); (5) defect 5's suggested fix completed (`ε_N` changes too); (6) the step
from "every batch has a ramp" to `λ_k ≥ λ_N` goes through `fractions_bounds` and `α < 1`; optional: "linear interpolations" read as
numpy's scheme, the uncovered "`δ + o(1)`" sentence added to the COVERAGE row, the redundant `∧ e_1` removed. The printed procedure is
an instance of `IsWitnessRun` + `IsSizedRun` (measurable selection assumed and declared); nothing vacuous; no junk value bites.
