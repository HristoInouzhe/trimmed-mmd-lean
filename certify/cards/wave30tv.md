# Fidelity card — wave 30tv: trimmed-mmd (jmlr), the sequential (batch) split certificate (v2 seq)

Lean: `StatFormal/Wave30tv/Statements.lean` (frozen 2026-11-08 before any proof, commit `e350f67`, sha256
`1a54efa45ff5c333adcc84319cc6a77475726d20c1bb9afe98a3f78f4b7d6dfb`; imports the frozen `Wave30tq/Statements.lean`
(`blockMean`, `pairZ`, `IsBlockPairing`, `past`, `wealth`, `betReject`, `ramp`, `clip`, the 30tq claims `thm1_cond`,
`thm1_condexp`, `thm1`) and through it `Archive/TrimmedMMD/Lower/Statements.lean` (`alphaLo`, `eq:downclosed`) and
`Lib/Distances/TV.lean` (`tvDist`)), routes `RouteCoord.lean` (functions of a set of coordinates; the freezing lemma),
`RouteSeq.lean` (the filtration over the pairs; the core level bound), `RouteClaims.lean` (the six claims), `Proofs.lean`.
New library: `Lib/Betting/Predictable.lean` (betting wealth with an initial capital and predictable outcomes of nonpositive
conditional mean is a nonnegative supermartingale; Ville's inequality for it).
**Printed source (READ-ONLY):** `trimmed-mmd/jmlr` at commit `8f6e0e5` —
`sections/06_splitting.tex` (sha256 `58506daf3593e08f9a99f91daab8441bc4357140a19fbd6b89c1f006fbb46074`, 302 lines): `lem:ramp`
l.89-100, "The certificate." l.107-121, `thm:betting` l.122-134, the proof sketch l.136-138, `cor:lower` l.199-212
(the frozen docstring says "l.136-139" and "remarks l.137-145"; correct: sketch l.136-138, remarks l.138-145);
`appendix/B_split.tex` (sha256 `4355a4d882b65df8b4efc11e813595740398393e42bdcba59db98445b74e26a7`, 257 lines): proof of
`thm:betting` l.162-173, the fractions l.175-179 (Bernstein remark l.180-182), proof of `cor:lower` l.184-193. jmlr HEAD
`88bf3e5` (2026-11-08) differs from `8f6e0e5` only at `06:140-142` (uncovered remarks, numbers replaced by macros). Code checked against the print:
`src/trimmedmmd/splitting.py` `sequential_horizon`, `sequential_betting_certificate`. Labels: the paper's, with " (v2 seq)".
Build: `lake build StatFormal.Wave30tv.Proofs` succeeds; every claim checked by `example : Claims.c := c`; `#print axioms` of each of
the 6 theorems = `[propext, Classical.choice, Quot.sound]`. Paper id `trimmed-mmd (jmlr)`.
Critic before freeze: independent AI reviewer, verdict READY TO FREEZE (no statement change; three docstring edits applied
before hashing; it also checked `single_split`'s instantiations in Lean).
**Author: approved (automatic on AI-audit PASS, per author decision 2026-10-21).**

## Targets (6, all in `certify/targets.toml`, module `StatFormal.Wave30tv.Proofs`)
| label | claim / theorem `StatFormal.Wave30tv.(Claims.)…` |
|---|---|
| `lem:ramp (iii) (v2 seq)`, `E_P g − E_Q g ≤ TV(P,Q)` for the ramp | `lem_ramp_iii` |
| `thm:betting (v2 seq)`, `P(max_{t≤N} K_t ≥ 1/δ | batch 0) ≤ δ` for every value of batch 0 | `thm_betting_cond` |
| `thm:betting (v2 seq)`, the same a.s., conditional expectation given `σ(u, batch 0)` | `thm_betting_condexp` |
| `thm:betting (v2 seq)`, "Hence": level `≤ δ` for every sample size, uniformly over `H_{0,α}` | `thm_betting` |
| `cor:lower (v2 seq)`, finite-sample clause | `cor_lower` |
| certificate paragraph (v2 seq), "the single split `e = (0,1/2,1)` is the case `B = 1`" | `single_split` |

## Common encodings (declared)
* **Data.** `ω = (u, x, y) ∈ U × 𝒳^n × 𝒳^m` under `ν ⊗ P^{⊗n} ⊗ Q^{⊗m}`: `x = (X_1..X_n)` i.i.d. `P`, `y = (Y_1..Y_m)` i.i.d. `Q`,
  independent. `u` is auxiliary randomness independent of the samples that the rules may use (**generalisation**: randomised fitting
  rules, e.g. the shared RNG of the software; `U` a one-point space is the printed deterministic case). `thm_betting_cond` has no `ν`.
* **Batches.** `lx i` / `ly j` = the batch of `X_i` / `Y_j`, any fixed assignment (**generalisation**). The printed cut "in an order
  fixed in advance, at fractions `0 = e_0 < … < e_B = 1` of its size" (software: rows `[round(e_b n), round(e_{b+1} n))` after a
  data-independent permutation) is an instance; batch 0 = `{lx = 0}`, `{ly = 0}`. Empty batches and non-consecutive labels allowed.
* **Pairs** (`IsBatchPairing`): `k = 0..N−1` (0-indexed; printed `1..N`), pair `k` in batch `bat k ≥ 1` ("batch 0 is used only for
  fitting"), `bat` monotone ("number the pairs of all batches consecutively"), blocks `A k ⊆ {lx = bat k}`, `B k ⊆ {ly = bat k}`,
  nonempty and pairwise disjoint on each side (30tq `IsBlockPairing`). **Generalisation**: any such blocks; the printed pairing
  (`N_b = min(n_b, m_b)` pairs in batch `b`, the smaller side as singletons, the larger side cut into `N_b` consecutive nearly
  equal blocks, mirror otherwise, `N = Σ_b N_b` fixed in advance) is an instance (instance not proved; it is the 30tq instance
  batch by batch). `N` and the blocks are deterministic.
* **Fitting rule** (`IsBatchRule`): `g b u x y : 𝒳 → ℝ` is `g_b`; for every `b = bat k` that holds a pair it is jointly measurable on
  `(U × 𝒳^n × 𝒳^m) × 𝒳`, `[0,1]`-valued, and agrees for any two samples that agree on batches `0..b−1` ("produces `g_b` from batches
  `0..b−1`, jointly measurable in those batches and the point"; equivalent, by composition with the restriction map one way and a
  section the other way, `𝒳` being nonempty). "If `ŝ_b ≤ ŝ'_b` … do not bet on batch `b`" / "`λ_k = 0` on a batch without a
  ramp": instance (take `g_b := ramp · 1{ŝ_b > ŝ'_b}` and multiply `λ_k` by the same indicator, which is a function of batches
  `< bat k`); the printed rule (QP witness on batches `0..b−1` → leave-one-out quantiles → ramp) is an instance **whose joint
  measurability is assumed, not proved** (as on the 30tq card).
* **Pair statistics**: `Z_k = mean_{A_k} g_b(X) − mean_{B_k} g_b(Y)`, `b = bat k` (`seqZ` = 30tq `pairZ` with `g_b`).
* **Fractions** (`IsBatchBetRule`): `λ_k = lam k u x y (Z_0..Z_{k−1})`, jointly measurable in `(u, x, y)` and the past, values in
  `[0, c/(1+α)]`, depending on the sample only through the batches before that of pair `k` ("each a function of the earlier batches
  and of the earlier `Z`'s"). The printed default (B_split l.175-180, `c = 1/2`, `w_0 = 20`, `σ_0²` from the earlier batches, sums
  over the pairs actually bet on) is an instance: which earlier pairs were bet on is a function of the batches before theirs, hence of
  batches `< bat k` (monotone `bat`).
* **Wealth and rejection**: `K_t = ∏_{k<t}(1 + λ_k(Z_k − α))` (30tq `wealth`); reject iff `∃ t ≤ N, K_t ≥ 1/δ` (30tq `betReject`,
  `= max_{t≤N} K_t ≥ 1/δ`; `K_0 = 1 < 1/δ`) (`seqReject`).
* **"Conditional on batch 0"**: (a) for every value — `withBatchZero l x₀ x` replaces exactly the label-0 entries of `x` by those of
  `x₀`; the other coordinates stay i.i.d. `P`/`Q`, so `P^{⊗n}⊗Q^{⊗m}{ω : reject(u, withBatchZero(ω))}` is the regular conditional
  probability given `(u, batch 0) = (u, x₀|batch 0, y₀|batch 0)` (only the batch-0 entries of `x₀, y₀` are read); (b) as
  `condExp` of the indicator given `comap batchZero = σ(u, (X_i)_{lx i = 0}, (Y_j)_{ly j = 0})`. Conditioning on `σ(u, batch 0)` implies
  conditioning on `σ(batch 0)` by the tower property, and equals it for `U` a point.

## Covered — back-translations and deviations
**`lem_ramp_iii`** (`06:89-100` (iii); proof `B_split:159`): for probability measures `P, Q`, measurable `f` and `s' < s`, the ramp
`g = ((f ∨ s') ∧ s − s')/(s − s')` is measurable, `[0,1]`-valued, and `E_P g − E_Q g ≤ TV(P,Q)`. **Generalisation**: `f` need not be
bounded, `α` plays no role in (iii) and is dropped. Closes the gap noted for (iii) in `LEAN_MAP_v2.md` §7 (measurability of the ramp
was not frozen). (i), (ii) are the 30tq claims `lem1`, `lem1_attain`, `lem1_rkhs`, `lem2_1`, `lem2_2`.

**`thm:betting` (v2 seq)** (`06:122-134`). Hypotheses of all three claims: any `n, m`, any batch assignment and batch pairing as
above, `α ≥ 0` (**generalisation** of `α ∈ [0,1)`; never used), `δ ∈ (0,1)`, `c ∈ (0,1]`, a fitting rule and fractions as above,
`TV(P,Q) ≤ α`; the rules are quantified with `(P,Q)` (equivalent to "for every rule … every pair": universal quantifiers commute).
* `thm_betting_cond`: for every `u`, `x₀`, `y₀`: `P^{⊗n} ⊗ Q^{⊗m}(max_{t≤N} K_t ≥ 1/δ` with batch 0 set to `(x₀, y₀)`) `≤ δ` — the
  printed display for **every** value of batch 0 (stronger than a.s.).
* `thm_betting_condexp`: the rejection event is measurable and `E[1_reject | σ(u, batch 0)] ≤ δ` `ν⊗P^{⊗n}⊗Q^{⊗m}`-a.s. — the
  printed display literally (with `u`).
* `thm_betting`: `ν⊗P^{⊗n}⊗Q^{⊗m}(max_{t≤N} K_t ≥ 1/δ) ≤ δ` for every `(P,Q)` with `TV ≤ α` — "Hence … level at most `δ` for every
  sample size, uniformly over `H_{0,α}`, with no assumption on the laws of the witness values, the kernel or the sample sizes" (no
  kernel appears; `n = 0` or `m = 0` allowed, then `N = 0`). "A rejection certifies `TV(P,Q) > α`" is the reading of this bound.
* The hypotheses `bat k ≥ 1` and `Monotone bat` are printed (`06:109`, `06:116`) and **necessary** (critic's counterexamples):
  without monotonicity — `P = Q = Bern(1/2)`, `α = 0`, `c = 1`, `δ = 1/4`, batches `1..2M` with pairs ordered `2,1,4,3,…`, `g_odd = id`,
  `g_{2r} = id` if the `Z` of batch `2r−1` is `1` else `0` (a function of batches `< 2r`), `λ = 0` on even-batch pairs and
  `1{previous Z ≠ 0}` on the batch-`2r−1` pair: `K = 2^R`, `R ∼ Bin(M, 1/8)`, `P(reject) → 1`; with a pair in batch 0
  (conditional form) — `g = id`, `λ = 1`, `δ = 1/2`: given `X = 1, Y = 0` in batch 0, `K_1 = 2` and the conditional rejection
  probability is 1. A rule that reads its own batch, two pairs sharing an observation, or a block across batches break the
  supermartingale; the dependence clause, block disjointness and `lx i = bat k` exclude them.

**`cor_lower`** (`06:199-212`, proof `B_split:184-193`): a fixed grid `α : Fin J → ℝ` with `α_j ≥ 0`, one batch assignment and pairing,
`δ ∈ (0,1)`, `c ∈ (0,1]`; per level `j` a fitting rule `g^{(j)}` and fractions `λ^{(j)}` (cap `c/(1+α_j)`), all on the same data;
`α̂_lo` = frozen `alphaLo` (`eq:downclosed`, `0` if none). Conclusion: `P(α̂_lo > TV(P,Q)) ≤ δ` for every `n, m` and every `(P,Q)`.
**Generalisations**: the grid need not be increasing or below 1; per-level rules arbitrary (they may depend on each other through
`u` and the data); a common `c` is no restriction (take `c = max_j c_j ≤ 1`). The kept hypothesis `α_j ≥ 0` is implied by the print
("test each `H_{0,α_j}` by Theorem `thm:betting`", whose `α ∈ [0,1)`) and is dispensable: it is used only at the first level `j₀`
with `TV ≤ α_{j₀}`, where `α_{j₀} ≥ TV ≥ 0` holds anyway. The remark `06:214-217` (a different witness and cut points per level, or one
witness fitted at `α = 0`) is covered as instances; its union-bound aside (factor `J`) is not.
**Not covered**: the asymptotic clause (levels tested by `thm:split`); its logic with `thm:split` as a hypothesis is the archived
`TrimmedMMD.Lower.Claims.cor_lower`.

**`single_split`** (`06:108-109`, "the single split `e = (0, 1/2, 1)` is the case `B = 1`"): `thm_betting_cond → 30tq thm1_cond`,
`thm_betting_condexp → 30tq thm1_condexp`, `thm_betting → 30tq thm1`. **B = 1 specialisation (answer to the check requested):
yes, the earlier one-fold claims are the special case of one betting batch.** The 30tq claims are the instance `U = Ω₁` (fold
one), every label `1` (batch 0 empty), `bat ≡ 1`, `g_1(u,·) = g(u)`, `λ_k(u, ·, z) = λ(u)_k(z)` (for `thm1_cond`: `U = Unit`);
`σ(u, empty batch 0) = σ(u)` (`comap_batchZero_one`). The paper's literal single split (fold one = batch 0 in the data,
`lx = 0` on fold one and `1` on fold two, `U` a point) is also directly an instance of the three `thm:betting` claims. **Caveat**:
as a Prop, `single_split` is also implied by the certified 30tq claims alone (its conclusions are theorems; the auditor's probe
`⟨fun _ => thm1_cond, fun _ => thm1_condexp, fun _ => thm1⟩` typechecks), so the gate certifies no content beyond 30tq. The
specialisation lives in the proof (`RouteClaims.lean`, `single_split_route`), a pure instantiation of the 30tv claims that does not
use the 30tq theorems, checked by reading it (critic and auditor).

## Junk-value audit
* Divisions: `c/(1+α)` with `α ≥ 0`; `1/δ` with `δ > 0`; block means over nonempty blocks; `(s − s')` with `s' < s` in `ramp`. No `ℕ`
  subtraction (`bat`, labels compared with `<`, `=`).
* `ENNReal.ofReal δ` with `δ ∈ (0,1)`. `tvDist` (frozen) is a real `⨆` of `Measure.real` (`toReal`) values; for probability measures
  these are finite and bounded (`bddAbove_tvDist`), so no junk. No `sInf`.
* No `Measure.map`. `condExp` (`thm_betting_condexp`) of the indicator of a set asserted measurable in the same claim, with respect to
  `comap batchZero`, which is below the ambient σ-algebra (`batchZero` is measurable); the measure is finite, so its trim is too. The
  junk branch (`condExp = 0`, which would make `≤ δ` trivial) is excluded by the claim's own measurability conjunct (integrable indicator).
* `withBatchZero` is an `if` on `l i = 0`; the subtypes `{i // lx i = 0}` may be empty (then the batch-0 factor is a point).
* Vacuity: all hypotheses jointly satisfiable — `P = Q` (TV = 0), `α = 0`, `δ = c = 1/2`, `n = m = 2`, `lx = ly = (0, 1)`, `N = 1`,
  `bat ≡ 1`, `A 0 = B 0 = {1}`, `g ≡ 0`, `λ ≡ 0`, `U = Unit`; and the printed pairing at any sizes.

## Textbook bridges
None. Ville's inequality on a finite horizon (30tq `Lib/Betting/Ville.lean`, from Mathlib optional stopping); the supermartingale
with predictable outcomes and initial capital (`Lib/Betting/Predictable.lean`, new); `E_P g − E_Q g ≤ TV` (30tq `delta_le_tv`, from
`Distances.integral_sub_le_mul_tvDist_of_nonneg`); coordinate independence (30tq `iIndepFun_coord`); `TrimmedMMD.Lower.
downclosed_measurable_le` (`cor:lower` combinatorics, certified); 30tq `lem2_1_route` (range of the ramp).

## Route
* Filtration (`RouteSeq`): `predSet t` = the coordinates of batches `< bat t` and of the blocks of pairs `< t` (all coordinates for
  `t ≥ N`); `𝒢_t = σ(coordinates in predSet t)`, increasing because `bat` is monotone. This is the filtration of the corrected proof
  wording below (not the printed "observations that enter pairs `1..k`").
* `Λ_k` depends only on `predSet k`, `Z_k` only on `predSet (k+1)`; a measurable function that depends only on a coordinate set is
  measurable for its σ-algebra (`resetOut`), and conversely (saturated sets form a σ-algebra).
* Conditional mean: for `V ≥ 0` bounded and `𝒢_k`-measurable, `E[V Z_k] = E[V (E_P g_b − E_Q g_b)] ≤ α E V` — the block coordinates of
  pair `k` are outside `predSet k`, and for `j ∉ C` the **freezing lemma** `E[V G(X_j)] = E[V ∫ G dLaw(X_j)]` (independence of
  `resetOut C ω₀` and `X_j`, `indepFun_iff_map_prod_eq_prod_map_map`, Fubini); then `lem:ramp` (iii).
* Ville with initial capital `1_s`, `s` an event of batch 0: `P(reject ∩ s) ≤ δ P(s)` (`core_level`). `s = univ` gives the
  unconditional slices; per-value: the rules composed with `withBatchZero` (the blocks lie outside batch 0); `condExp`: every
  `S ∈ σ(u, batch 0)` sliced in `u`, then the set-integral characterisation on `μ.trim`; Fubini in `u` (30tq `prod_le_of_slices`).

## Defects in the printed text (jmlr @ 8f6e0e5)
1. **`06:107-109`, off-by-one in `B`.** With `0 = e_0 < … < e_B = 1` there are `B` batches `0..B−1`, so `e = (0, 1/2, 1)` is `B = 2`,
   not `B = 1` (the code: `for b in range(1, len(edges) - 1)`). *Fix*: "…at fractions `0 = e_0 < e_1 < ⋯ < e_{B+1} = 1` of its size
   (batches `0, …, B`); we use `e = (0, 1/4, 1/2, 1)`, and the single split `e = (0, 1/2, 1)` is the case `B = 1`."
2. **`B_split:163-165`, the filtration.** "Every observation of a batch enters one of its pairs" is false when `N_b = 0`
   with one side nonempty (`n_b = 0 < m_b` or the mirror, possible through rounding at small sizes: `n = 1`, `m ≥ 2`,
   `e = (0,1/4,1/2,1)` gives X-batches `0, 1` empty while Y-batch 1 has an observation that feeds `g_2`).
   The observations of such a batch enter no pair but feed `g_{b+1}`, so `g_{b+1}` is not measurable for `F_{k−1}` as defined. The
   theorem stands (certified with the larger filtration). *Fix*: "For pair `k`, lying in batch `b`, let `F_{k−1}` be generated by
   batches `0, …, b−1` and the observations of the earlier pairs of batch `b`. These σ-algebras increase with `k` because the pairs are
   numbered batch by batch, `g_b` and `λ_k` are `F_{k−1}`-measurable, and `Z_k` is `F_k`-measurable." (drop "Every observation…").
3. **`B_split:175-178`, the default fractions.** The denominators `w_0 + k − 1`, `w_0 + i − 1` count all earlier pairs while the
   sums "run over the pairs actually bet on"; the code (`cnt`) counts only pairs bet on. Validity unaffected. *Fix*: "…where `i`, `l`
   and `k − 1` count only the pairs actually bet on before pair `k` (`N` still counts all pairs)." (Also: the printed `λ_k` divides by
   `σ̂²_{k−1}`, positive only if `σ_0² > 0`; the code floors `σ_0²` at `1e-4` and `σ̂²` at `1e-8`.)
4. **`06:91-94`, scope of `s > s'` in `lem:ramp`.** The preamble fixes `s > s'` while (i) is "for all reals `s, s'`"; read with the
   standing `s > s'`, (i)'s supremum/attainment clause is false (`LEAN_MAP_v2.md` §7: `P = Q = U[0,1]`, `f = id`, `α = 0.8`: the
   supremum over `ℝ²` is `−0.8`, at `(0.2, 0.8)`; over `s > s'` it is `−1.25`). *Fix*: attach `s > s'` to the definition of `g`, i.e.
   to (ii)-(iii) only. (Not a 30tv target; (i) is certified in 30tq under the reading "over all `(s,s') ∈ ℝ²`".)
5. **`lem:ramp` (iii) scope.** (iii) is stated for the lemma's ramp, but `06:136-137` and `B_split:167` apply it to an arbitrary
   `[0,1]`-valued `g_b` (`thm:betting` allows every rule). The proof (`B_split:159`) covers every measurable `[0,1]`-valued `g`.
   *Fix*: state (iii) for every measurable `g` with values in `[0,1]` (certified in that form as the last conjunct of 30tq `pair_facts`).
6. Cosmetic: `06:115` "its block `B`" reuses `B` (number of batches); rename the block. Optional, `06:201`: "a grid
   `0 ≤ α_1 < ⋯ < α_J < 1`" so that every level is in the range of `thm:betting`.
No printed theorem, lemma or corollary is false under its intended reading; the sentence `06:108-109` (B = 1) is literally false
(defect 1), and `lem:ramp` (i) is false if the standing `s > s'` is read into it (defect 4).

## Coverage note
`thm:betting` (v2 seq): the display (every value of batch 0, and a.s. as a conditional expectation) and the "Hence" are certified, as a
generalisation; `cor:lower`: the finite-sample clause only; `lem:ramp` (iii) certified for the ramp; the single-split sentence certified
as the implication to the 30tq claims. Not covered: `cor:lower`'s asymptotic clause; the remarks `06:138-145` (WSR fractions approach
the best constant fraction; `2.45`/`1.645`; the `1.75×`/`2.2×` sample-size factors) and `B_split:180` ("comes close to the best
constant fraction"); the Bernstein alternative (`B_split:180-182`); the union-bound aside of `06:216`; that the printed batch cut and
pairing are `IsBatchPairing` instances, and that the printed QP/leave-one-out ramp rule and the default fraction rule are jointly
measurable (instances declared, not proved). `single_split` carries no content beyond 30tq as a statement (see its caveat).

## Fidelity review
Fidelity review: independent AI audit, method v1 (certify/AUDIT_METHOD.md), 2026-11-08 — PASS with notes
(blind back-translation of the six claims, clause-by-clause comparison with jmlr@8f6e0e5, checklist; source hashes and the six
targets' labels and paper id checked; card deviations, B = 1 paragraph and printed-text defects 1-3 verified, also against the code).
Notes (all applied above):
* `single_split` is implied by the certified 30tq claims alone; the instantiation was checked by reading the proof.
* "No printed statement is false" reworded; `lem:ramp` (i) scope promoted from cosmetic (defect 4); defect 5 (scope of (iii)) added.
* Defect 2's example needs one side nonempty (`n = 1`, `m ≥ 2`); defect 3: the printed `λ_k` needs `σ_0² > 0`.
* "Rules chosen after `(P,Q)`" is equivalent, not stronger; `cor_lower`'s `α_j ≥ 0` is dispensable.
* Junk audit: `tvDist` bounded real `⨆`; the `condExp` junk branch is excluded by the measurability conjunct.
* Line numbers: sketch `06:136-138`, remarks `06:138-145`, default fractions `B_split:175-179` (the frozen docstring keeps the
  older ranges); coverage note extended (`06:214-217`, `B_split:180`, pairing instances); jmlr HEAD `88bf3e5` changes only `06:140-142`.
