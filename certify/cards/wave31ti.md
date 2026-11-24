# Fidelity card — wave 31ti: trimmed-mmd (JMLR **v3**, revision of 2026-11-17): `lem:pathconvex`, the polynomial `ass:margin`, `thm:rate`, `lem:marginexists`, `prop:rategeneral`

Lean: `StatFormal/Wave31ti/Statements.lean` (10 claims; definitions `PolyMargin`, `uPath`, `uEmp`, `mRun`, `omegaRun`; frozen 2026-11-17
before any proof, commit `8f98c67`, locked with its imports). Routes `RoutePath`, `RouteRate` (untrusted, commit `d0cfb97`); `Proofs.lean`
checks `example : Claims.c := c` for each claim. Paper id `trimmed-mmd (jmlr)`; labels `lem:pathconvex (v3 rev)`, `lem:marginexists (v3
rev)`, `prop:rategeneral (v3 rev)`, `thm:rate (v3 rev)`, `prose:linear-margin (v3 rev)`. Branch `tmmd-jmlr-rev` (worktree
`~/projects/StatFormal-tmmd-rev`), from master `6e8cd0e`.
Critic (independent AI reviewer, before the freeze, 2026-11-17): 10 claims, 8 ACCEPT, 1 ACCEPT-WITH-NOTE (`pathconvex_ii`: (A3) not needed),
1 REVISE non-blocking (`rate_v3_full`: add the printed `O(·)` at the paper's thresholds); none false; READY TO FREEZE. It typechecked the
draft, back-translated blind, checked the four sha256 hashes and the `main.aux` numbers, and re-derived the secant bound, the limit `s`,
the equivalence in (ii), the `D₀` bound and the `τ^A` bound. Applied before hashing: five line numbers, (A3) dropped from `pathconvex_ii`
and `pathconvex_tangent`, the constant-14 conjunct of `rate_v3_full`, the coverage lines for `ex:separated` and for "exponents below 1",
a Not-covered list.
Fidelity review: independent AI audit, method v1 (certify/AUDIT_METHOD.md), 2026-11-17 — PASS with notes (first pass FLAG on one
coverage-note wording, fixed and re-audited; claims back-translated blind and compared with the print, freeze before proofs, hashes,
numbers, labels and coverage notes checked; notes at the end of this card).
**Author: approved (automatic on AI-audit PASS, per author decision 2026-10-21).**

## Source
Working tree of `trimmed-mmd/jmlr/v3/` on 2026-11-17, uncommitted on top of trimmed-mmd `5e17fad` (the revision is the red text,
`\rev{}`/`revblock`; `git diff 5e17fad -- jmlr/v3/sections jmlr/v3/appendix`). sha256: `sections/03_analytic.tex` `1d3360b7…d437`,
`appendix/B_analytic.tex` `b0e9849a…a2c9`, `sections/02_regions.tex` `8c3985ee…1461`, `sections/05_trimming.tex` `d418a839…60be` (full
hashes in the Lean header). Numbers from `main.aux` of the same build: Assumption 2 `ass:margin` (`03_analytic.tex:178-182`), Lemma 7
`lem:pathconvex` (`:197-212`, prose `:214-219`, proof `B_analytic.tex:423-477`), Example 1 `ex:separated` (`:223-235`), Theorem 8
`thm:rate` (`:241-252`, proof `B_analytic.tex:482-505`), Lemma 24 `lem:marginexists` (`B_analytic.tex:371-381`), Proposition 25
`prop:rategeneral` (`:406-415`, the sentence after it `:417-419`), the linear pair (`05_trimming.tex:85`).

## Targets (10 new claims, module `StatFormal.Wave31ti.Proofs`, and 3 relabelled)
| label | claim / theorem `StatFormal.Wave31ti.(Claims.)…` |
|---|---|
| `lem:pathconvex` first sentence: `u(α) = (1−α)D_α` convex and nonincreasing on `[0,1)`, any `P, Q` | `pathconvex` |
| `lem:pathconvex` for `P_n, Q_m`, and "the rescaled empirical path is convex too" | `pathconvex_emp` |
| `lem:pathconvex` (i): strict decrease on `[0,α⋆]`, the secant bound | `pathconvex_i` |
| `lem:pathconvex` (ii): `u(α⋆−ε)/ε` nondecreasing, its limit `s ≥ 0`, linear margin iff `s > 0` (with `c₀ = s`), `D_{α⋆−ε} ≤ D₀ε/(α⋆(1−α⋆))` | `pathconvex_ii` |
| prose after Lemma 7: tangential contact (`s = 0`) excludes `γ = 1` | `pathconvex_tangent` |
| `lem:marginexists`: the printed running-minimum `ω` | `marginexists` |
| sentence after `prop:rategeneral`: the polynomial margin is a general margin, `ε_{n,m} = (t/c₀)^{1/γ}` | `poly_is_general` |
| `thm:rate` (v3), any valid `τ` and lower tool `τ^A` | `rate_v3` |
| `thm:rate` (v3) at the paper's `τ_{n,m}`, `τ^A_{n,m}` | `rate_v3_full` |
| the linear pair satisfies Assumption 2 with `c₀ = 3/2`, `γ = 1` | `linear_poly` |

Plus 3 targets under the new label `prop:rategeneral (v3 rev)` for the already certified claims `Wave30tu.rate`, `Wave30tu.rate_eps` and
`Wave30tu.Full.rate_full` (module `StatFormal.Wave30tu.Proofs`; Proposition 25 is the former `thm:rate` verbatim; no new statement), so
that the reader face lists them under Proposition 25 as well as under `thm:rate`.

## Encodings (declared)
* (A1)–(A2) as in every trimmed-mmd wave (`H` real complete separable, `φ` strongly measurable, `‖φ‖ ≤ κ`); (A3) `Characteristic φ` only in
  `pathconvex_i` and `marginexists` (where `D_α > 0` below `α⋆` is used, `eq:zeroeq`); dropped elsewhere (generalisation: the printed
  "Let Assumption 1 hold" includes (A3)).
* `D_α(P,Q)` is `Dpop` (the regions' distance, equal to the printed infimum over trimmings by the certified `Wave8a.georep_dist`),
  `D̂_α = Demp`. `α⋆ = TV(P,Q)` is `tvDist`.
* `ass:margin` (v3) is `PolyMargin φ P Q c₀ γ`: `0 < c₀`, `1 ≤ γ`, `c₀ε^γ ≤ D_{α⋆−ε}` on `[0,α⋆]` (`rpow`).
* (ii): "it has a limit `s ≥ 0`" is `∃ s, Tendsto r (𝓝[>] 0) (𝓝 s)` with every such limit `≥ 0` and satisfying the equivalence.
* `lem:marginexists`: `m(ε)` is the `sInf` of the image of `[ε,α⋆]`, and the claim states that it is attained (`IsLeast`).
* `thm:rate`: generalised to any valid threshold and lower two-sided tool as in `Wave30tu.rate_poly`; `α⋆ < 1` assumed (the printed theorem
  evaluates `τ(α⋆)`, defined on `[0,1)`); the `O(·)` as an explicit bound (constant 24 under `τ, τ^A ≤ r_n + r_m`; at the paper's thresholds
  the printed proof's bound and the constant 14 by Cauchy–Schwarz).

## Covered — back-translations and deviations
* `pathconvex`: for all probability measures `P, Q` and `φ` with (A1)–(A2), `α ↦ (1−α)D_α(P,Q)` is convex and nonincreasing on `[0,1)`.
  Generalisation: no (A3).
* `pathconvex_emp`: the same for `(1−α)D̂_α` at every realization with `n, m ≥ 1`.
* `pathconvex_i`: under (A1)–(A3), `0 < α⋆ < 1`: `u` strictly decreasing on `[0,α⋆]`; for `0 ≤ α₁ < α₂ < α⋆`,
  `α₂ + (α₂−α₁)u(α₂)/(u(α₁)−u(α₂)) ≤ α⋆`. Exact.
* `pathconvex_ii`: under (A1)–(A2), `0 < α⋆ < 1`: `r(ε) = u(α⋆−ε)/ε` nondecreasing on `(0,α⋆]`; a limit as `ε ↓ 0` exists; every limit `s`
  is `≥ 0`, `(∃c₀, PolyMargin c₀ 1) ↔ s > 0`, and `s > 0 → PolyMargin s 1`; `D_{α⋆−ε} ≤ D₀ε/(α⋆(1−α⋆))` on `[0,α⋆]`. Generalisation: no (A3).
* `pathconvex_tangent`: if `s = 0`, no `c₀` gives `γ = 1` and every `(c₀,γ)` with Assumption 2 has `γ > 1` (the printed "needs `γ > 1`").
* `marginexists`: under (A1)–(A3), `0 < α⋆ < 1`: the minimum is attained for every `ε ∈ [0,α⋆]`; `ω` continuous and strictly increasing on
  `[0,α⋆]`, `ω(0) = 0`, `ω ≤ D_{α⋆−·}`; and `ω` satisfies `Wave30tu.Margin` (the hypothesis of `prop:rategeneral`). Exact.
* `poly_is_general`: `PolyMargin c₀ γ → Margin (ε ↦ c₀ε^γ)`, and for `0 ≤ t ≤ c₀(α⋆)^γ`, `(t/c₀)^{1/γ} ∈ [0,α⋆]` solves `c₀ε^γ = t`.
* `rate_v3`: (A1)–(A2), `α⋆ < 1`, `PolyMargin c₀ γ`, valid `τ` at `δ`, lower tool `τ^A` at `δ′`, `t = τ(α⋆) + τ^A(α⋆) ≤ c₀(α⋆)^γ`: one
  measurable event of probability `≥ 1−δ−δ′` with `α̂ ≤ α⋆` and `|α̂−α⋆| ≤ (t/c₀)^{1/γ}`; and the constant-24 bound.
* `rate_v3_full`: the same at `τ = τ_{n,m}(·,δ)` (`Wave30tu.Full.tauFull`) and `τ^A = τ^A_{n,m}(·,δ′)` (`Wave30tr.tauA`), any `D ≥ ‖φx−φx′‖`;
  for `D ≤ 2κ`: `t ≤ 2κ(1−α⋆)^{-1}(2√2+4+√log(1/δ)+√log(1/δ′))/√(n∧m)` (the printed proof's bound) and
  `(t/c₀)^{1/γ} ≤ (14κ/(c₀(1−α⋆))·√((1+log(1/δ)+log(1/δ′))/(n∧m)))^{1/γ}` (the printed `O(·)`).
* `linear_poly`: `PolyMargin φLin Plin Qlin (3/2) 1`.

## Covered by earlier certified targets (no new claim; coverage map of the revision)
* `prop:rategeneral` (Proposition 25) is the former `thm:rate` verbatim: `Wave30tu.rate` (any valid `τ`, lower tool, general `ω` with
  `Wave30tu.Margin`, `ε ∈ [0,α⋆]` with `ω(ε) = t`), `Wave30tu.rate_eps` (`ω^{-1}(t)` exists and is unique), `Wave30tu.Full.rate_full` (at the
  paper's `τ`). `α⋆ < 1` is assumed there as here.
* `ex:separated` (Example 1) "Assumption 2 holds with `γ = 1` and `c₀ = 2/‖f‖`": the certified `Wave31tb.separated` states `‖f‖ > 0` and
  `2/‖f‖·ε^1 ≤ D_{α⋆−ε}` on `[0,α⋆]`, which is `PolyMargin φ P Q (2/‖f‖) 1`.
* "Exponents below 1 are excluded because no path can satisfy them" (`03_analytic.tex:186-187`, `B_analytic.tex:474-476`):
  `Wave31tf.gamma_ge_one` (under (A1)–(A2), `0 < α⋆ < 1`, `c₀ > 0`, `γ > 0`, the bound forces `γ ≥ 1`).
* "Some lower bound of this kind, without a speed, always exists" (`03_analytic.tex:187-190`): `Wave31te.margin_exists` and the new
  `marginexists`.
* Reworded `lem:oneevent` (Lemma 5) and `thm:consistency` (Theorem 6), "with `α⋆ < 1`" and `α⋆ := TV(P,Q)` defined once in §2: the frozen
  `Wave30tu.oneevent`, `consistency_i`, `consistency_ii` (and `_inst`, `_full`) already assume `tvDist P Q < 1` with `α⋆ = tvDist P Q`;
  unchanged.
* Reworded `cor:trimrate` (Theorem 15, last sentence: for every `η` a constant `C_η` depending on `η` alone and a size `n_η` depending on
  `η`, `(P,Q,k,α)` and `r_Q`): the frozen `Wave31ta.cor_trimrate_v2` has exactly this quantifier order (`∀ε ∃Λ ∀(P,Q,φ,α,d⋆,ρ) ∃N`, `N`
  chosen before `t_α, u_α, c_f, C_f, c′_f`), with one event for the four bounds (stronger than "each bound").
* Renamed objects (the ramp `ψ`, `φ` in `lem:hinge`, `lem:popramp`, `lem:ramp`, `cor:lower`): notation only; the Lean names (`ramp`, the
  hinge class of `Wave30tx`) and the cards' mapping are unaffected.
* `rem:sharper` reworded in §3.1 ("It is never larger than `τ^P(α)`"): `Wave31ta` certified `τ^{P′} ≤ τ^P` for the general kernel.

## Proof route (untrusted)
`RoutePath`: for weights `p, q` and levels `α₀, α₁`, `c = p(1−α₀)/(1−α)`, `d = q(1−α₁)/(1−α)` mix the densities of `𝒞_{α₀}` and `𝒞_{α₁}`
into one of `𝒞_α` (`region_mix`); the triangle inequality and an `ε`-argument on the infima (`setDist_le_comb`) give
`D_α ≤ cD_{α₀} + dD_{α₁}`, i.e. convexity of `u`. Monotonicity from nested regions (`Wave18b.Dpop_anti`). Abstract lemmas for a convex
`u ≥ 0` on `[0,1)` with `u(α⋆) = 0` give (i) and (ii); `u(α⋆) = 0` by the certified `ZeroSet.zero_of_tv_le`, positivity below `α⋆` by the
certified `ZeroSet.zeroeq`. `marginexists`: `m(ε) = D_{α⋆−ε}` by monotonicity, continuity by the certified `Wave18b.continuity_cont`.
`RouteRate`: `rpow` facts; the certified `Wave30tu.rate`, `rate_poly`, `Full.rate_full`, `Full.tauFull_threshold`, `Wave30tr.ek_le`,
`Wave31tf.linear_margin`.

## Junk-value audit
`Dpop` evaluated only at levels in `[0,1)`; `r(ε)` divides by `ε` only on `(0,α⋆]` (the filter `𝓝[>] 0` is eventually there); the secant
denominator is positive by the strict decrease proved in the same claim; `D₀ε/(α⋆(1−α⋆))`, `(t/c₀)^{1/γ}`, `log(1/δ)` and `√(n∧m)` have
genuine arguments; `omegaRun` divides by `α⋆ > 0`. Vacuity: (A1)–(A3) with `0 < α⋆ < 1` hold for `𝒳 = Bool`, `H = ℝ`, `φ = 1_{true}`,
`P = δ_true`, `Q` uniform (the Wave31te witness); `PolyMargin` holds for the linear pair (`linear_poly`).

## Defects / wording in the printed text (suggested fixes, none applied)
1. `03_analytic.tex:186-187`, "Exponents below 1 are excluded because no path can satisfy them": false when `α⋆ = 0` (then `ε` ranges
   over `{0}`). Fix: "When `0 < α⋆ < 1`, exponents below 1 are excluded …".
2. `thm:rate`, `prop:rategeneral`: `α⋆ < 1` is implicit (they evaluate `τ(α⋆)`). Fix: "with `α⋆ < 1`", as `thm:consistency` now says.
3. Lemma 7 puts (A3) on all of it, but only (i) uses it (convexity and (ii) hold under (A1)–(A2)). Optional.

## Not covered (declared)
"The rate is `(n∧m)^{-1/(2γ)}`" (a reading of the `O(·)`, whose explicit form is certified); "a larger `γ` allows a flatter contact,
which is harder to detect" (informal); the discussion's suggestion of extrapolating the empirical rescaled path (`08_discussion.tex`,
declared heuristic, "carries no guarantee"; its basis, convexity of the empirical path, is `pathconvex_emp`).

## Coverage notes (COVERAGE.md rows)
* `lem:pathconvex`: "certified (Lemma 7, v3 revision 2026-11-17): (1-alpha)D_alpha convex and nonincreasing on [0,1) for any P, Q and for
  P_n, Q_m ((A3) not needed); (i) strict decrease on [0,alpha*] and the secant bound (with (A3)); (ii) u(alpha*-e)/e nondecreasing, its
  limit s >= 0, linear margin iff s > 0 with c0 = s, D_{alpha*-e} <= D_0 e/(alpha*(1-alpha*)); s = 0 forces gamma > 1 (Wave31ti)".
* `lem:marginexists`: "certified (Lemma 24): the printed running-minimum omega, minimum attained, continuous, strictly increasing,
  omega(0) = 0, below the path, a margin for prop:rategeneral (Wave31ti)".
* `prop:rategeneral`: "certified (Proposition 25, the former thm:rate verbatim): Wave30tu.rate, rate_eps, Full.rate_full; the sentence after
  it (poly_is_general, Wave31ti)".
* `thm:rate`: add "v3 revision (polynomial margin, c0 > 0, gamma >= 1): alpha-hat <= alpha* and |alpha-hat - alpha*| <= (t/c0)^{1/gamma}
  on one event, the O(.) with constant 24 for any valid tau with tau, tau^A <= r_n + r_m at alpha* (and 14 at the paper's tau with Delta_phi <= 2 kappa) (Wave31ti)".

## AI audit notes (2026-11-17)
1. First pass FLAG: the thm:rate coverage note omitted the hypothesis `τ, τ^A ≤ r_n + r_m` of the constant 24. Fixed in the card and in
   COVERAGE.md; re-audit PASS with notes.
2. The ten claims are faithful (blind back-translations agree clause by clause); the (A3) drops are generalisations; constant 14 checked;
   no junk-value or vacuity risk; the covered-elsewhere claims (ex:separated, gamma_ge_one, oneevent, consistency, cor_trimrate_v2) hold.
