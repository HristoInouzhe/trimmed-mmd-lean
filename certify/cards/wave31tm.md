# Fidelity card — wave 31tm: trimmed-mmd (JMLR **v3** of 2026-11-19): `cor:alphalo` (the trimmed sample at the split-sample lower bound)

Lean: `StatFormal/Wave31tm/Statements.lean` (1 claim, no new definition; frozen 2026-11-19 before any proof, commit `c9b085f`, locked with
its imports). Route `RouteAlphalo` (untrusted, commit `d7a4d79`); `Proofs.lean` defines `alphalo` and checks
`example : Claims.alphalo := alphalo`; proved, axioms propext, Classical.choice, Quot.sound. Paper id `trimmed-mmd (jmlr)`; label
`cor:alphalo (v3 2026-11-19)`. Branch `tmmd-jmlr-lorate` (worktree `~/projects/StatFormal-tmmd-rev`), from master `f3f37c4`.
Critic (independent AI reviewer, before the freeze, 2026-11-19, shared with wave 31tl): `alphalo` ACCEPT-WITH-NOTE (R4: the `λ_max`,
`σ²_min` generalisation of the print to be declared, applied); the printed proof re-derived step by step, no wrong step; `N₀` placed after
`ε`, `δ′` and the sequences; `𝒯_α`, `R⋆` and the MMD faithful; no junk value. No Lean term changed.
Gate (2026-11-19, branch `tmmd-jmlr-lorate`): `CERTIFIED: 3953 targets; statements frozen; axioms within ['Classical.choice',
'Quot.sound', 'propext']`. `tools/check_aliases.py`: `ALIASES OK: 3896 aliases in 16 paper files`.
Fidelity review: independent AI audit, method v1 (certify/AUDIT_METHOD.md), 2026-11-19 — PASS with notes (blind back-translation
written before opening the tex; faithful, generalisations declared; `IsSizedRun` is met by the printed batches with `c = 1/4`,
`C₀ = 3/2`, `B = 2`; hashes, lock, target, numbers checked; audit done on the frozen statement before any proof; notes at the end).
**Author: approved (automatic on AI-audit PASS, per author decision 2026-10-21).**

## Source
trimmed-mmd commit `5e51f65`, read with `git show 5e51f65:jmlr/v3/…`. sha256: `sections/05_trimming.tex` `7ea03da3…49d7b9b`,
`appendix/D_trimming.tex` `848ad1f7…7ad419`; context `sections/04_split.tex` `790e687b…e153e`, `sections/03_analytic.tex`
`f47ebecd…fe9e220` (full hashes in the Lean header). Numbers from `main.aux` of the build of 2026-11-19 18:48: Corollary 17 `cor:alphalo`
(`05_trimming.tex:158-165`, proof `D_trimming.tex:447-468`), Proposition 16 `prop:alphahat`, Proposition 12 `prop:loconsistency`,
Corollary 11 `cor:lower`, Lemma 7 `lem:pathconvex`.

## Target (1 new claim, module `StatFormal.Wave31tm.Proofs`)
| label | claim / theorem |
|---|---|
| `cor:alphalo`: for `n, m` large, with probability `≥ 1−δ−δ′`, every `(w,v) ∈ 𝒯_{α̂_lo}` has `MMD(P_n^w,R⋆) ≤ ε`, `MMD(Q_m^v,R⋆) ≤ ε` | `StatFormal.Wave31tm.(Claims.)alphalo` |

## Encodings (declared)
* (A1)–(A3) (`Characteristic φ`) with `0 < α⋆ = TV(P,Q) < 1`.
* "`α̂_lo` at level `δ` as in Proposition 12, on grids fixed in advance whose mesh tends to zero, with `log J = o(n∧m)`": exactly the
  hypotheses of the certified `Wave30tz.lo_refining` at a fixed `δ ∈ (0,1)`: deterministic grids `α n m` (`IsGrid`, `J n m` levels) with
  `gridMesh → 0` and `log J = o(n∧m)` in explicit form, runs with `IsWitnessRun` (any `λ_max ∈ (0,½]`, any floor `σ²_min > 0`; the v3 print
  takes `λ_max = ½`, `σ²_min ∈ (0,4]`: generalisation) and `IsSizedRun` (batch fractions fixed in advance).
* `𝒯_α` (`05_trimming.tex:12`): the minimizers of `qp` over `capped n α × capped m α` on the full samples (as in the certified
  `Wave30tx.alphahat`); `R⋆ = (P∧Q)/(1−α⋆)` is `Wave30tx.contactLaw`; `MMD(P_n^w,R⋆) = ‖∫φ d(Σ w_iδ_{X_i}) − μ_{R⋆}‖`.
* "for all `n, m` large enough, with probability at least `1−δ−δ′`": `∀ε > 0, ∀δ′ ∈ (0,1), ∃N₀, ∀n, m ≥ N₀`, a measurable event of probability
  `≥ 1−δ−δ′` on which the two bounds hold for every minimizer.

## Covered — back-translation and deviations
* `alphalo`: under (A1)–(A3), `0 < α⋆ < 1`, a fixed `δ ∈ (0,1)`, grids with mesh `→ 0` and `log J = o(n∧m)`, runs of Proposition 12: for
  every `ε > 0` and `δ′ ∈ (0,1)` there is `N₀` such that for all `n, m ≥ N₀` some measurable event `E` has probability `≥ 1−δ−δ′` and on `E`
  every minimizer `(w,v)` of (qp) at the level `α̂_lo` satisfies `‖Σ w_iφ(X_i) − μ_{R⋆}‖ ≤ ε` and `‖Σ v_jφ(Y_j) − μ_{R⋆}‖ ≤ ε`.
  Generalisation: `λ_max ∈ (0,½]`, floor `σ²_min > 0`.

## Proof route (untrusted)
The printed proof (`D_trimming.tex:447-468`) with certified ingredients: the event of Proposition 16 at level `δ′/3` is the product of
the `cor:uniform` events (certified `TrimmedMMD.Concentration.uniform_alpha`), probability `≥ 1 − 2δ′/3`, on which every minimizer at a
level `a ≤ α⋆` has `MMD ≤ r_n + Ω(D̂_a + r_n + r_m)` (`Wave30tx.RAlpha.bound_on_event`, the route of the certified `Wave30tx.alphahat`)
and `D̂_a ≤ D_a + r_n + r_m` (`Unconditional.abs_Demp_sub_Dpop_le`, `r_n(a,·) ≤ r_n(α⋆,·)`); `D_a ≤ D₀(α⋆ − a)/(α⋆(1−α⋆))` (certified
`Wave31ti.pathconvex_ii`), `D₀ > 0` (certified `ZeroSet.zeroeq`); `|α̂_lo − α⋆| ≤ sα⋆(1−α⋆)/D₀` with probability `≥ 1 − δ′/3` for `n, m`
large (certified `Wave30tz.lo_refining` at the constant schedule `δ`); `α̂_lo ≤ α⋆` with probability `≥ 1 − δ` (`cor:lower`, certified
`Wave30tz.lo_upper`); `s ≤ ε/2` with `Ω^{P,Q}(3s), Ω^{Q,P}(3s) < ε/2` (certified `Wave30tx.contact`, `Ω` nondecreasing) and `r_n, r_m < s/2`
for `n, m` large (`Wave30tu.rn_tendsto`). Route differences: none (the printed nit about choosing `s` for both moduli is handled).

## Junk-value audit
`capped n a` at `a = α̂_lo ∈ {0} ∪ grid ⊆ [0,1)`: the cap `1/(n(1−a))` is genuine; `contactLaw` divides by `1 − α⋆ > 0`; `wEmp` uses
`ofReal (w i)` with `w ≥ 0` on `capped`; the only supremum is the imported `gridMesh`, an `iSup` over `[0,1)` of distances bounded
by 1 (genuine); `log (J n m)` at `J = 0` would be Lean's `log 0 = 0`, which only weakens a hypothesis, and mesh `→ 0` forces `J ≥ 1`
eventually (both inherited from the certified `lo_refining`). Vacuity: the hypotheses are those of the certified
`Wave30tz.lo_refining` plus `0 < α⋆ < 1`; satisfiable (e.g. finite `𝒳`, Gaussian kernel, `0 < TV < 1`), with the wave-30tz caveat on the
measurable selection of the minimizer and cut points.

## Defects / wording in the printed text
None. Nit (no change needed): `D_trimming.tex:460-461`, "the same bound for `MMD(Q_m^v,R⋆)`" uses the modulus with `P` and `Q` exchanged,
so `s` must be chosen with `s + Ω(3s) ≤ ε` for both moduli.

## Not covered (declared)
The prose around the corollary (`05_trimming.tex:155-156`, `167-170`): "At the split-sample bound the convexity of the path does,
together with its consistency"; "the corollary needs no margin" (true of the claim, which assumes none); "Under Assumption 2, Theorem 33
bounds `α⋆ − α̂_lo` explicitly, but as at `α̂` the bound carries no rate unless `Ω` is known" (informal; the bound is `Wave31tl.lorate_ii`).

## Coverage note (COVERAGE.md row)
* `cor:alphalo`: "certified (Corollary 17): under (A1)-(A3), 0 < alpha* < 1, a fixed delta, grids with mesh -> 0 and log J = o(n^m), and
  runs of prop:loconsistency (any lambda_max in (0,1/2], floor sigma^2_min > 0, batch fractions fixed in advance): for every eps > 0 and
  delta' in (0,1), for all n, m large, with probability >= 1 - delta - delta', every minimizer (w,v) of (qp) at alpha-lo has
  MMD(P_n^w, R*) <= eps and MMD(Q_m^v, R*) <= eps (Wave31tm)".

## AI audit notes (2026-11-19, method v1, PASS with notes)
1. The junk-value section said "no `sSup`/`sInf` in the statement"; the imported `gridMesh` is an `iSup` (genuine), and `log (J n m)` at
   `J = 0` is harmless; reworded (applied).
2. `main.aux` (18:48) predates the commit `5e51f65` (19:29); the label sets are identical and the numbers consistent.
