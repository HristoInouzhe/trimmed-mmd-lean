# Fidelity card — wave 31tj: trimmed-mmd (JMLR **v3**, revision of 2026-11-17): Algorithm 1 (`alg:bisect`) and `rem:batch0grid` (Remark 30)

Lean: `StatFormal/Wave31tj/Statements.lean` (7 claims; definitions `rejected`, `bisectLoop`, `startPoint`, `bisectAlg`, `IsBatchBetRuleU`,
`Batch0Grid`; frozen 2026-11-17 before any proof, commit `ff42af2`, locked with its imports). Routes `RouteAlg`, `RouteGrid` (untrusted,
commit `3a6cd55`). Paper id `trimmed-mmd (jmlr)`; labels `alg:bisect (v3 rev)`, `rem:batch0grid (v3 rev)`. Branch `tmmd-jmlr-rev`.
Critic (independent AI reviewer, before the freeze, 2026-11-17): 7 claims, 5 ACCEPT (`alg_bracket`, `alg_loop`, `alg_cost`, `alg_start`,
`alg_event`), 2 REVISE (`batch0grid_cond`, `batch0grid`: true as drafted, but the grid depended on the auxiliary `u` only; revised so that
it is a function of batch 0 inside the samples, as in the frozen Wave 30tv framework); none false; READY TO FREEZE after the changes. It
confirmed the corrected reading of the printed `α̂ ∈ (ℓ,u]` with a counterexample (`τ(0) = 0`, `τ = c` on `(0,1)`, `D̂₀ ∈ (0,c]`: `0`
rejected, `α̂ = 0 = ℓ`). Applied: two line numbers, the revised encoding.
Fidelity review: independent AI audit, method v1 (certify/AUDIT_METHOD.md), 2026-11-17 — PASS with notes (first pass FLAG on one
coverage-note wording, fixed and re-audited; claims back-translated blind and compared with the print, freeze before proofs, hashes,
numbers, labels and coverage notes checked; notes at the end of this card).
**Author: approved (automatic on AI-audit PASS, per author decision 2026-10-21).**

## Source
Working tree of `trimmed-mmd/jmlr/v3/` on 2026-11-17 (uncommitted on `5e17fad`). sha256: `03_analytic.tex` `1d3360b7…d437`,
`B_analytic.tex` `b0e9849a…a2c9`, `C_split.tex` `e2db7656…4ae2`, `04_split.tex` `8a187adb…220c`, `07_data.tex` `ef1aa08a…0330`.
Algorithm 1 `alg:bisect` (`B_analytic.tex:259-278`, the sentence before it `:256-257`), the bisection paragraph of §3.2
(`03_analytic.tex:139-147`), Table 3's bisection (`07_data.tex:36-38`), Remark 30 `rem:batch0grid` (`C_split.tex:168-178`) and its mention
in §4.3 (`04_split.tex:161-163`).

## Targets (7, module `StatFormal.Wave31tj.Proofs`)
| label | claim |
|---|---|
| `alg:bisect`: the algorithm's guarantee (bracket, `α̂ = 0` when `0` is accepted, stopping) | `alg_bracket` |
| `alg:bisect`: the loop from any bracket (Table 3; "it brackets `α̂` at every step") | `alg_loop` |
| `alg:bisect`: cost, width `≤ 2^{−t}`, `t ≤ k` when `2^{−k} ≤ ε`, seven tests for `ε = 0.01` | `alg_cost` |
| `alg:bisect`: the upper end `u` (accepted; the least `α` with `τ(α) ≥ Δ_φ`) | `alg_start` |
| `alg:bisect` / §3.2: one event of probability `≥ 1−δ`, every rejected level `< α⋆`, however chosen | `alg_event` |
| `rem:batch0grid`: conditional on batch 0 | `batch0grid_cond` |
| `rem:batch0grid`: unconditional | `batch0grid` |

## Encodings (declared)
* Rejection `τ(α) < D̂_α`; the loop and the algorithm as total functions with a test budget `J` (the printed "fewer than `J` levels
  tested"; the test of level 0 is not counted). `u₀` is any accepted level in `(0,1)` (generalisation of "the smallest `α` with
  `τ(α) ≥ Δ_φ`", which `alg_start` covers when it exists). `τ ≥ 0`, nondecreasing on `[0,1)`, continuous on `(0,1)`: the hypotheses of
  `lem:crossing` (the paper's `τ` has them, certified in waves 30tu/30tw/31ta).
* **Corrected reading:** the printed `α̂ ∈ (ℓ,u]` is frozen as `ℓ ≤ α̂ ≤ u`, strict on the left when `ℓ > 0`. The printed form fails when
  `τ` jumps at 0 (allowed by `lem:crossing`; the paper's `τ^P` has `τ^P(0+) > τ^P(0)`): then `0` may be rejected while `α̂ = 0`.
* "however the levels were chosen": the quantifiers over `α₀, u₀, ε, J` and the start are inside the event (data-dependent choices allowed).
* `rem:batch0grid`: batch 0 is `(u, (x_i)_{lx i = 0}, (y_j)_{ly j = 0})` as in the frozen `Wave30tv.batchZero`; the grid `α_j(u,x,y)` is
  jointly measurable, `≥ 0`, and depends on the sample through batch 0 only (`Batch0Grid`); it need not be increasing (generalisation);
  the fractions at level `j` are capped by `c/(1+α_j)` at that level (`IsBatchBetRuleU`, the printed `λ_max/(1+α)` at the level tested).
  The conditional form is for every value of batch 0 (`withBatchZero`), as `Wave30tv.thm_betting_cond`.

## Covered — back-translations
* `alg_bracket`: for every realization (n, m ≥ 1), `τ` as above, accepted `u₀ ∈ (0,1)`, any `α₀, ε, J`: the output is `none` iff `0` is
  accepted, and then `α̂ = 0`; otherwise `(ℓ,u,t)` with `ℓ` rejected, `u` accepted, `0 ≤ ℓ < u ≤ u₀`, `ℓ ≤ α̂ ≤ u`, `ℓ < α̂` if `ℓ > 0`,
  `t ≤ J`, and if `t < J` then `u − ℓ ≤ ε` and `α̂ − ℓ ≤ ε` ("within `ε` of `α̂`").
* `alg_loop`: the same from any rejected `ℓ₀ ≥ 0`, accepted `u₀ ∈ (ℓ₀,1)` and first test in `(ℓ₀,u₀)`.
* `alg_cost`: any rejection rule, `α₀ = ½`, `0 < u₀ ≤ 1`, `ε > 0`: `u − ℓ ≤ 2^{−t}`; `t ≤ k` whenever `2^{−k} ≤ ε`; `t ≤ 7` at `ε = 0.01`.
* `alg_start`: for `D ≥ ‖φx − φx′‖`, levels with `τ ≥ D` are accepted; such levels exist in `(0,1)` if `τ → ∞` at 1; if moreover
  `τ(0+) < D`, the least such level exists and is positive.
* `alg_event`: for a valid threshold at `δ` and `α⋆ < 1`: one measurable event of probability `≥ 1−δ` on which every rejected level in
  `[0,1)` is `< α⋆`, and so is the output `ℓ` of the algorithm and of the loop, for every choice of their inputs.
* `batch0grid_cond`: for every batch-0 value `(u,x₀,y₀)`, `P(TV < α̂_lo) ≤ δ` over the other batches.
* `batch0grid`: `P(TV < α̂_lo) ≤ δ` under `ν ⊗ P^{⊗n} ⊗ Q^{⊗m}`, every sample size, every pair.

## Proof route (untrusted)
`RouteAlg`: loop invariants by induction (rejected lower end, accepted upper end, test point inside, counts); the bracket contains `α̂` by
the certified `Wave30tu.crossing`; the cost by halving from a midpoint; the least level by continuity at the infimum; the event of the
certified `Wave30tu.oneevent`. `RouteGrid`: fractions with batch 0 frozen are an `IsBatchBetRule` at that batch 0's level, so the certified
`Wave30tv.thm_betting_cond` and `TrimmedMMD.Lower.downclosed_measurable_le` give the conditional bound; the unconditional bound by slicing
over `u` (`Wave30tq.prod_le_of_slices`) and over batch 0 through `law(withBatchZero x₀ x, withBatchZero y₀ y) = P^{⊗n} ⊗ Q^{⊗m}` for
independent copies (proved: `Measure.pi_eq` on boxes, `Measure.prod_eq` on rectangles). Measurability of `{TV < α̂_lo}` with a random grid:
`α̂_lo > t ⇔ ∃ j, all levels ≤ j rejected and t < α_j`.

## Junk-value audit
`Demp` only at tested levels in `(ℓ₀,u₀) ⊆ [0,1)` or at `0`, `u₀`; `alphaHat` is the `sInf` of a set containing the accepted `u₀`
(nonempty, bounded below by 0); `(1/2)^k`; the cap `c/(1+α_j)` with `α_j ≥ 0`. Vacuity: `Wave30tu.hausdorff_valid` supplies a valid
threshold with the `lem:crossing` hypotheses; a constant grid is a `Batch0Grid`.

## Defects / wording in the printed text (suggested fixes, none applied)
1. `B_analytic.tex:275` "then `α̂ ∈ (ℓ,u]`": fails if `τ` jumps at 0. Fix: "then `ℓ ≤ α̂ ≤ u`, with `ℓ < α̂` unless `ℓ = 0`".
2. `B_analytic.tex:256-257` "the levels it rejects are exactly those below `α̂`" and `03_analytic.tex:139-140` "every level from `α̂` on is
   accepted": except level 0 when `α̂ = 0` and `τ` jumps at 0. Fix: add "(level 0 may be rejected when `α̂ = 0`)".
3. `B_analytic.tex:269` "the smallest `α` with `τ(α) ≥ Δ_φ`" need not exist if `τ(0) < Δ_φ ≤ τ(0+)` (then every positive level is
   accepted and `α̂ = 0`). Fix: "any accepted level, e.g. the smallest `α` with `τ(α) ≥ Δ_φ` when `τ(0+) < Δ_φ`".
4. `03_analytic.tex:141-145`: with a user start `α₀ ≠ ½` the first test is not a midpoint, so the cost can be one test more
   (`1 + ⌈log₂(1/ε)⌉`); "`α_last` within `ε` of `α̂`" needs the loop to stop on the tolerance, not on `J` (`J ≥ log₂(1/ε)` at the
   default start).
5. `03_analytic.tex:142` "seven for `ε = 0.01`" counts the bisection tests only; Algorithm 1 also tests level 0, so a run is eight
   convex solves. Fix: "seven, after the test of level 0".

## Not covered (declared)
"where a grid of mesh `ε` needs up to `1/ε`" (a count); §4.3 "the betting test refits its ramp at each level, so it may accept a level
and reject a larger one, and a bisection … could test several true nulls and would need a multiplicity correction" and "Reading the grid
upward costs only one fit more than the number of rejected levels" (methodological remarks, not results); "For instance, a bisection on
batch 0 alone, with any statistic, may place a short grid" (an instance of `batch0grid`, any measurable rule).

## Coverage notes (COVERAGE.md rows)
* `alg:bisect`: "certified (Algorithm 1, v3 revision 2026-11-17): output brackets alpha-hat (ell <= alpha-hat <= u, strict when ell > 0;
  the printed (ell,u] corrected), alpha-hat = 0 when 0 is accepted, within eps when stopped on tolerance; from any bracket (Table 3);
  width <= 2^-t and t <= ceil(log2(1/eps)) at the default start, 7 tests for eps = 0.01; the start u; one event of probability >= 1 - delta on
  which every rejected level and every output is below alpha*, however chosen (Wave31tj)".
* `rem:batch0grid`: "certified (Remark 30): cor:lower with a grid that is a measurable function of batch 0, conditionally on batch 0 and
  unconditionally (Wave31tj)".

## AI audit notes (2026-11-17)
1. First pass FLAG: the alg:bisect coverage note said `t <= log2(1/eps)`, false at `ε = 0.01` (7 tests, `log₂100 ≈ 6.64`). Fixed to
   `t <= ceil(log2(1/eps))` in the card and COVERAGE.md; re-audit PASS with notes.
2. The corrected reading of `α̂ ∈ (ℓ,u]` re-verified with the counterexample; `alg_event` quantifies every choice inside one event.
3. Defect 1 line fixed to `B_analytic.tex:275`; defect 5 added (eight convex solves counting the test of level 0).
