# Fidelity card — wave 31to: trimmed-mmd (**Annals of Statistics version, revision of 2026-11-21**): the general (kernel-free) results `lem:newtrimmean`, `prop:newapproxgen`, `prop:newapprox`, `prop:newslopegeneral`, `prop:newslope` (first two sentences), `prop:newrates` (i)–(ii), `prop:newconverse`, and the AoS rows of `lem:attainment`

Lean: `StatFormal/Wave31to/Statements.lean` (16 claims; new definitions `densP`, `densQ`, `setA`, `errFn`, `wit`, `oscFn`, `Fset`,
`xiH`, `Kfun`, `Nfun`, `genInv`, `InSuppImg`, `gNM`; frozen 2026-11-21 before any proof, commit `fd9d482`, locked with its 41 imports).
Routes `RouteA`, `RouteB`, `RouteC`, `RouteD` (untrusted; WIP commit `2089eb6`); `Proofs.lean` defines the 16 theorems and checks
`example : Claims.X := X`; all proved, axioms propext, Classical.choice, Quot.sound. (The freeze commit message and the lock note say
"17 claims"; the frozen file has 16 — the count was wrong, the file is what was reviewed and frozen.)
Paper id `trimmed-mmd (jmlr)` (face `Papers/TrimmedMMDJMLR`), labels suffixed "(AoS 2026-11-21, <printed number>)". Branch
`tmmd-aos-minimax` (worktree `~/projects/StatFormal-tmmd-aos`), on top of Wave31tn (`ac45971`).
Scope (author decision, 2026-11-21): a light wave of the general results; the Fourier-analytic results of the same sections are not
formalized (hand-checked by an independent referee and numerically): see "Not covered".
Critic (independent AI reviewer, before the freeze, 2026-11-21, `tmmd-aos-brief/wave31to/CRITIC.md`): READY TO FREEZE after R1–R4 —
S8 `lem:newtrimmean`, S14 `prop:newconverse` ACCEPT; S9, S11, S12, S13, S15 ACCEPT-WITH-NOTE; S10 REVISE on (c) only. Applied before the
freeze: R1 (S10 (c) kept as a definite claim, for any probability measures), R2 (provenance block), R3 (printed-source pin and notation
map), R4 (ω `MonotoneOn`/nonnegative on `[0,α⋆]` only), and the notes N3 (ℝ≥0∞ non-vacuity, below), N4–N5 (S11 closedness, nonempty, full
mass as conjuncts), N8 (wording for the remark `S4_rates.tex:612-613`), N10 (AoS rows for all six clauses of `lem:attainment`).
Gate: see "Gate" below.
Fidelity review: independent AI audit, method v1 (certify/AUDIT_METHOD.md), 2026-11-21 — PASS with notes (blind back-translation of all
16 claims written from the frozen files before comparison; Statements hash matches the lock, source hashes match; faithful, deviations
declared and harmless (κ > 0 in `newrates_ii_a`, `0 < α⋆ < 1` in (iii), the ℝ≥0∞ `𝒩`, the extra conjuncts of `newslopegeneral`); no
undeclared stronger hypothesis, unguarded junk value, vacuous hypothesis set or restated conclusion; the six `lem:attainment` aliases
state the printed clauses; the "Not covered" list is accurate; full audit `certify/audits/audit31to.md`; notes at the end).
**Author: approved (automatic on AI-audit PASS, per author decision 2026-10-21).**

## Source
`~/projects/tmmd-aos-brief/NEW_STATEMENTS.md` at freeze: whole file sha256 `a746b3c27cbba633d6cfa9bed05078b026f5abd171dc9d55bc521d80e6df8ae9`
(402 lines; copy committed as `certify/sources/tmmd-aos-NEW_STATEMENTS-wave31to.md`); the Wave31to block (line 207, "# Wave31to — …",
to the end; S8–S15) sha256 `843849754ffc6b1c6fc8e39f8fcdda54ca5074cb8b8afba67baee11017a4c8db`; lines 1–205 sha256
`18f9fd214bc8366173ac9b3f41eda7e78d4fa2360f2e991728717b28b25dddac`, unchanged by this wave. Chain to Wave31tn (recovered by the critic):
trimmed-mmd commit `84e9c60`, `aos/NEW_STATEMENTS.md` (150 lines), reproduces the Wave31tn hashes `467357fe…` (whole file) and `23660a33…`
(lines 1–120); the present lines 1–205 differ from it only at line 45 (the S2 header location note recorded on the Wave31tn card) and by
the appended Lean-status section (lines 151–205); no frozen statement text changed. ("Lemma S4.7" in that header is the numbering of
2026-11-20; in the revision of 2026-11-21 `lem:twopointmargin` is Lemma S4.19 and Proposition S4.7 is `prop:newslopegeneral`.)
Printed source: local copies in `~/projects/tmmd-aos-brief/wave31to/` (read 2026-11-21), sha256 `05_rates.tex` `03a3e25d…6a74`,
`S4_rates.tex` `3e78db18…02c8`, `02_regions.tex` `471c47e7…4ee7`, `S1_regions.tex` `d85c328a…85e7`, `S5_trimming.tex` `6235009c…854a`,
`main.pdf` `ed07e8f4…0237`, `supplement.pdf` `7e7bdbb7…07e6` (full hashes in the Statements header). Printed numbers: Lemma 2.3
`lem:attainment`, Proposition 5.3 `prop:newslope`, Proposition 5.4 `prop:newapprox`, Proposition 5.9 `prop:newrates`, Proposition S4.7
`prop:newslopegeneral`, Lemma S4.9 `lem:newtrimmean`, Proposition S4.10 `prop:newapproxgen`, Proposition S4.18 `prop:newconverse`
(context: Theorem 5.7 `thm:rate`, Lemma S4.3 `lem:pathconvex`, Theorem S4.6 `thm:lorate`, Lemma S5.6 `lem:contact`). The live AoS source of
2026-11-21 10:15 differs from the copies by notation only within the scope: `ξ_ℋ` is printed `ω_ℋ`, the mesh `h` is `Δ_𝒢`, the smallest
gap `h₀` is `Δ_min`, the slope `s` is `𝔰`, `1/n + 1/m` is `1/n_⋆`, `Z` is `Γ`; no statement in scope changed.
Printed locations (copies): `lem:newtrimmean` `S4_rates.tex:525-532`; `prop:newapproxgen` `:549-561` (notation `:539-547`);
`prop:newapprox` `05_rates.tex:94-103` (err `:88-92`, balanced error `S4_rates.tex:589-593`); `prop:newslopegeneral` `S4_rates.tex:453-457`
(setting `:427-431`, `:449-451`); `prop:newslope` `05_rates.tex:66-77` (`:79`); `prop:newrates` `05_rates.tex:200-212` (proofs
`S4_rates.tex:599-634`); `prop:newconverse` `S4_rates.tex:951-961`; `lem:attainment` `02_regions.tex:103-109` (proof `S1_regions.tex:35-48`).

## Targets (16 claims in `StatFormal.Wave31to.Proofs`; 6 alias rows)
| label | claim / theorem |
|---|---|
| `lem:newtrimmean`: `(E_Pf − α sup f)/(1−α) ≤ E_{P′}f ≤ (E_Pf − α inf f)/(1−α)` | `StatFormal.Wave31to.(Claims.)newtrimmean` |
| `prop:newapproxgen` (i): `(1−α)‖f‖D_α ≥ E_Pf − E_Qf − α osc f` | `StatFormal.Wave31to.(Claims.)newapproxgen_i` |
| `prop:newapproxgen` (ii): `E_Pf − E_Qf = α⋆ − err f`, `u(α⋆−ε) ≥ (ε − err f)/‖f‖` | `StatFormal.Wave31to.(Claims.)newapproxgen_ii` |
| `prop:newapproxgen` (iii)(a): `ξ_ℋ` nondecreasing, `D ≥ u ≥ ξ_ℋ ≥ ε/(2𝒩(ε/2))` | `StatFormal.Wave31to.(Claims.)newapproxgen_iii_a` |
| `prop:newapproxgen` (iii)(b): `ξ_ℋ(ε) > λ ⟺ 𝒦(λ) < ε` | `StatFormal.Wave31to.(Claims.)newapproxgen_iii_b` |
| `prop:newapprox` (a): `D_{α⋆−ε} ≥ (ε − err f)/((1−α⋆+ε)‖f‖)` | `StatFormal.Wave31to.(Claims.)newapprox_a` |
| `prop:newapprox` (b): `D_{α⋆−ε} ≥ ε/(2𝒩(ε/2))` | `StatFormal.Wave31to.(Claims.)newapprox_b` |
| `prop:newapprox`, the identities printed with err | `StatFormal.Wave31to.(Claims.)newapprox_err` |
| `prop:newslopegeneral`: slope `≤ dist(supp φ#P₀, supp φ#Q₀)`; supports closed, nonempty, full mass | `StatFormal.Wave31to.(Claims.)newslopegeneral` |
| `prop:newslope` (a): continuous φ, slope `≤ inf ‖φ(x) − φ(y)‖` over the supports | `StatFormal.Wave31to.(Claims.)newslope_a` |
| `prop:newslope` (b): supports meet ⟹ slope `0`, no linear margin | `StatFormal.Wave31to.(Claims.)newslope_b` |
| `prop:newrates` (i), any valid τ and lower tool τ^A | `StatFormal.Wave31to.(Claims.)newrates_i` |
| `prop:newrates` (i) at the paper's `τ_{n,m}`, `τ^A_{n,m}` | `StatFormal.Wave31to.(Claims.)newrates_i_full` |
| `prop:newrates` (ii), `thm:lorate` (i) with `ω(ε)` | `StatFormal.Wave31to.(Claims.)newrates_ii_a` |
| `prop:newrates` (ii), `thm:lorate` (ii) with `ω^←(t)` | `StatFormal.Wave31to.(Claims.)newrates_ii_b` |
| `prop:newconverse`: `α⋆ − α̂^A ≥ sup{ε : D_{α⋆−ε} ≤ g_{n,m}}` with probability `≥ 1 − δ′` | `StatFormal.Wave31to.(Claims.)newconverse` |
| `lem:attainment` (Lemma 2.3): convex / κ-bounded / **norm-compact** / attained / `D = 0` ⟹ common point / common trimming | `Wave11b.attain_convex`, `attain_bounded`, `Wave30tx.contact_compact`, `Wave11b.attain_inf`, `attain_zero`, `attain_common` (aliases, no new claim) |

## Encodings (declared; full list in the Lean header)
* (A1)–(A2): `H` real complete separable, `φ` strongly measurable with `‖φ x‖ ≤ κ`. (A3) assumed nowhere: dropping it from the printed
  "Assumption 1" of `prop:newrates` is a generalisation, with the one added guard `0 < κ` in `newrates_ii_a` (implied by the printed (A3)
  when `α⋆ > 0`; without a guard the (A3)-free form fails at `φ ≡ 0`: `T_fit = T_bet = 0 = ω`, nothing rejected, `α̂_lo = 0 < a_ε`).
* "`f ∈ ℋ`" is `g : H` with `f = ⟪g, φ·⟫` and `‖f‖ := ‖g‖` (Waves 31tb/31tn); exact on the canonical feature map, and for a general φ the
  sup/inf of `ξ_ℋ`, `𝒦`, `𝒩` over `g` equal the printed ones for the RKHS of `⟪φx, φy⟫`.
* `err`, `A`, `|P−Q|` through the densities w.r.t. `P + Q` (`densP`, `densQ`, `setA`, `errFn`); `osc` by `iSup`/`iInf`; `𝓕 = Fset`;
  `ξ_ℋ = xiH` (`sup ∅ = 0`); `𝒦 = Kfun`; `𝒩 = Nfun` in ℝ≥0∞ (`inf ∅ = ∞`, "read as 0" is `ε/(2·⊤) = 0`); `ω^← = genInv` over `[0,α⋆]`.
* `prop:newapproxgen` (iii) read under `0 < α⋆ < 1` (the hypothesis of (ii), on which it rests).
* `newapprox_err`: kernel-free, any probability measures, any `α⋆ ∈ [0,1]` (generalisation of the scope of `prop:newapprox`).
* Supports: `InSuppImg` (the ball characterisation of `supp φ_#P₀`, `P₀` through the positive multiple `P − P ⊓ Q`, no `Measure.map`) in
  `newslopegeneral`; Mathlib `Measure.support` of `P − P ⊓ Q` in `newslope_*`. "The limit": every `s` that `u(α⋆−ε)/ε` (resp. the printed
  `(1−α⋆+ε)D/ε`) tends to as `ε ↓ 0` (it exists by the certified `Wave31ti.pathconvex_ii`).
* `newrates_i`: any valid threshold `τ` and any lower tool `τ^A` (house generalisation, as `Wave30tu.rate`, `Wave31ti.rate_v3`);
  `newrates_i_full` at the paper's thresholds. The remark `S4_rates.tex:612-613` (`τ = τ^A(·,δ)`) is covered by `newrates_i` at that
  threshold together with the certified `Wave30tu.upper_valid`, `Wave30tr.thmA` (a) and `tauA_scale` (which make `τ^A(·,δ)` valid); no
  separate target.
* `newrates_ii_*`: the run hypotheses of `Wave31tl.lorate_i`/`lorate_ii` verbatim (inherited encodings and generalisations; inherited
  caveat: the existence of a run satisfying `IsWitnessRun` on a general `𝒳` is not certified).
* `newconverse`: any bound `D` (the printed `Δ_φ` is one); "≥ sup S" as "every `ε ∈ S` is `≤ α⋆ − α̂^A`" with `0 ∈ S` stated.

## Covered — back-translation and deviations
* `newtrimmean`: `α ∈ [0,1)`, `P` a probability, `f` measurable with bounded range, `P′ ∈ trimSet P α`: both printed bounds. Faithful.
* `newapproxgen_i`: (A1)–(A2), any probabilities, `g ≠ 0`, `α ∈ [0,1)`: `E_P⟪g,φ⟫ − E_Q⟪g,φ⟫ − α osc ≤ (1−α)‖g‖ D_α`. Faithful.
* `newapproxgen_ii`: plus `0 < α⋆ < 1`, `g ∈ 𝓕`: the identity, and the bound on `u` for `g ≠ 0`, `ε ∈ [0,α⋆]`. Faithful.
* `newapproxgen_iii_a`: monotone on `[0,α⋆]`; for `ε ∈ [0,α⋆]`: the set bounded above (added conjunct), `u ≤ D`, `ξ ≤ u`,
  `ofReal ε/(2𝒩(ε/2)) ≤ ofReal ξ` in ℝ≥0∞. Faithful.
* `newapproxgen_iii_b`: `λ ≥ 0`, `ε ∈ (0,α⋆]`: `λ < ξ(ε) ↔ 𝒦(λ) < ε`. Faithful.
* `newapprox_a`, `newapprox_b`: the printed bounds (the second in ℝ≥0∞). Faithful.
* `newapprox_err`: measurable `f : 𝒳 → [0,1]`: `err = α⋆ − (E_Pf − E_Qf)`, `err ≥ 0`, balanced error `= (1 − α⋆ + err)/2 ≥ (1−α⋆)/2`,
  excess `= err/2`, `A` measurable, `err(1_A) = 0`, balanced error of `1_A` `= (1−α⋆)/2`. Generalisation (any probabilities).
* `newslopegeneral`: every limit `s` and all `z, z′` in the two supports: `s ≤ ‖z − z′‖`; supports closed, nonempty, of full mass
  (`(P − P⊓Q)(φ⁻¹(supp)ᶜ) = 0`). Faithful (the last three conjuncts are the lead-in sentence `S4_rates.tex:450-451`).
* `newslope_a`, `newslope_b`: as printed (first two sentences); `StronglyMeasurable φ` is kept next to `Continuous φ` (implied, harmless).
* `newrates_i`, `newrates_i_full`: `D_{α⋆−ε} ≥ ω(ε)` (the printed "(i) needs only"), event of probability `≥ 1−δ−δ′` with
  `α⋆ − ω^←(t) ≤ α̂ ≤ α⋆`. Generalisation ((A3) dropped; any τ, τ^A in `newrates_i`).
* `newrates_ii_a`: `u(α⋆−ε) ≥ ω(ε)` on `[0,α⋆]`, run of `lorate_i`, `κ > 0` (declared guard), `ε ∈ (0,α⋆]`, `β⋆ max{T_fit, T_bet(J_ε)} ≤ ω(ε)`:
  `P(α̂_lo < a_ε) ≤ η`.
* `newrates_ii_b`: run of `lorate_ii`, mesh bound `h`: event of probability `≥ 1−δ−η` with `α⋆ − h − ω^←(t_{n,m}) ≤ α̂_lo ≤ α⋆`. No guard needed.
* `newconverse`: `α⋆ < 1`, `0 < δ < δ′ < 1`, `n, m ≥ 1`: `D_{α⋆} ≤ g_{n,m}` and an event of probability `≥ 1−δ′` on which every
  `ε ∈ [0,α⋆]` with `D_{α⋆−ε} ≤ g_{n,m}` has `ε ≤ α⋆ − α̂^A`. Generalisation (any `D`, any `κ`).
* `lem:attainment` (AoS rows): the six certified clauses; norm-compactness is `Wave30tx.contact_compact` ((A1)–(A2), (A3) not needed).

## Proof route (untrusted)
* `RouteA`: S8 from `P′ = gP`, `g ≤ β` a.e., `∫(β − g) = αβ` (`integral_toReal_rnDeriv_mul`); `err_eq` from the library
  `Distances.tvDist_eq_integral_max_sub` (`TV = ∫(p−q)₊ d(P+Q)`) and the pointwise identity `|1_A − f||p−q| = (p−q)₊ − f(p−q)`;
  (i) by S8 under `P` and `Q`, `⟪g, μ_{P′} − μ_{Q′}⟫ ≤ ‖g‖‖μ_{P′} − μ_{Q′}‖`, `le_csInf` over trimming pairs, `dTrim = Dpop` (certified
  `Wave8a.georep_dist`); (ii) from (i) at `α⋆ − ε`, `osc ≤ 1`.
* `RouteB`: (iii)(a) elementwise monotonicity and `Real.sSup_le`; the `𝒩` bound via `ε/(2ξ) ≤ ‖g‖` for every `g ∈ 𝓕` with
  `err(g) ≤ ε/2` (all nonzero since `err(0) = α⋆`); (iii)(b) `exists_lt_of_lt_csSup` / `exists_lt_of_csInf_lt`; `newapprox_a/b` from (ii),
  (iii).
* `RouteC`: `P_ε = P⊓Q + (ε/a)(P − P⊓Q)|_U ≤ P` (`Measure.sub_add_cancel_of_le`), mass `1 − α⋆ + ε` (route `Wave30tx.RContact.inf_univ`),
  normalised an `(α⋆−ε)`-trimming (`rnDeriv_le_one_of_le`, `rnDeriv_smul_left_of_ne_top`); `u(α⋆−ε) ≤ ε(‖z−z′‖ + 2ρ)` by
  `norm_setIntegral_le_of_norm_le_const`; `le_of_tendsto` on `𝓝[>] 0`; supports: closed by balls, full mass by
  `TopologicalSpace.isOpen_iUnion_countable` (second countable separable `H`), nonempty since `(P − P⊓Q)(univ) = α⋆ > 0`. `newslope_a`
  from `Measure.mem_support_iff_forall` and continuity; `newslope_b` with the certified `Wave31ti.pathconvex_ii`.
* `RouteD`: (i) on `E⁰ ∩ E⁻` (certified `Wave30tu.oneevent`, the lower tool; `inter_prob`), `α⋆ ∈ crossSet`, for `ε ∈ (ω^←(t), α⋆]`
  `ω(ε) > t` and no level `≤ α⋆ − ε` crosses (`Wave30tz.dpop_antitone`), `le_csInf`; (i-full) with `tauFull_threshold`, `thmA`,
  `tauA_scale`; (ii-a) the route `Wave31tl.Core.core_lower` with `D_* = ω(ε) > 0` (`Tfit_pos`, κ > 0), `x_j = (α⋆−α_j)/ε`, the profile bound
  `ω(ε)x_j ≤ u(α⋆−ε)x_j ≤ u(α_j) ≤ D_{α_j}` from the monotone ratio of `pathconvex_ii`, the packing sum `Basic.sum_exp_le_Jeps`; (ii-b)
  `core_lower` at `x_j = 1` for every `ε ∈ (ω^←(t), α⋆]`, `Basic.floor_ge_of_mesh`, continuity from below (`Monotone.measure_iUnion`) along
  `ε_k = ω^← + (α⋆ − ω^←)/(k+2)`, the route `Route.two_sided` (certified validity `Wave30tz.lo_upper`), `Route.lower_trivial`; converse:
  `E⁺` of `thmA` at `δ′`, `τ^A(α,δ) − τ^A(α,δ′) = β·g_{n,m} ≥ g_{n,m}`, `alphaHat_le_of_mem`, `zero_of_tv_le`.

## Junk-value audit
`toReal` of `rnDeriv` w.r.t. `P + Q` (finite a.e.; only integrated); `errFn` applied only to measurable `[0,1]`-valued functions
(integrand bounded by `|p − q|`); `xiH`: its set is bounded above (a stated conjunct), empty set gives the printed `0`; `Kfun`: nonempty
(`0 ∈ 𝓕`), bounded below by `0`; `Nfun` (critic N3): for `ε ∈ (0,α⋆]`, `|err(f) − err(0)| ≤ 2α⋆ sup|f| ≤ 2α⋆κ‖g‖` and `err(0) = α⋆`, so
`err(g) ≤ ε/2` forces `‖g‖ ≥ 1/(4κ)` (no such `g` when `κ = 0`, then `𝒩 = ∞`); hence `𝒩(ε/2) > 0`, `ε/(2·0) = ⊤` never occurs, and at
`ε = 0` the bound is `0/x = 0`; both sides are `ENNReal.ofReal` of nonnegative reals (no truncation); `genInv`: set contains `0`
(`ω(0) ≤ D_{α⋆} = 0 ≤ t`) and bounded by `α⋆`; `oscFn`/`iSup`/`iInf` of bounded functions on nonempty spaces; `InSuppImg`: measures of
preimages of open balls (measurable for strongly measurable φ; the outer-measure reading agrees); `Dpop` only at levels in `[0,1)`;
`u(α⋆−ε)/ε` only near `0⁺`; `log(1/δ)` with `δ ∈ (0,1)`; `1/n`, `1/m` with `n, m ≥ 1`; `1/(1 − (α⋆ − ε))` with `α⋆ − ε < 1`. Vacuity: every
hypothesis set has a witness (e.g. two three-point laws with a rank-one feature map; `ω = 0`; the paper's thresholds; for (ii) the run
caveat above).

## Defects / wording in the printed text
None found. All printed proofs in scope were re-derived (drafter and critic). Notation in the live source differs from the copies only by
the renaming map above.

## Not covered (declared)
* The Fourier-analytic results (author decision; hand-checked by an independent referee and numerically, `S4_rates.tex:992-1013`):
  `prop:newsobolev` (`05_rates.tex:115-135`), `prop:newgauss` (`:137-153`), `prop:newrates` (iii) (`:213-215`), `prop:newgammaone`
  (`S4_rates.tex:498-506`), `lem:newsobnorm` (`:649-661`), `thm:newsobolev` (`:695-712`), `cor:newsobolev` (`:726-734`), `lem:newgaussstep`
  (`:780-786`, with eq:newbandlim and the band-limited density `:760-773`), `thm:newgauss` (`:809-819`), `prop:newupperone` (`:859-867`),
  `prop:newmoments` (`:883-898`, eq:newmomentdecay `:850-857`), the Fourier setting `:433-447` (eq:newnative, eq:newbochner).
* The last sentence of `prop:newslope` (`05_rates.tex:75-76`; connected domains, Gaussian mixtures).
* Heuristics `05_rates.tex:79-87`, `:105-113`, `:219-229`; `S4_rates.tex:431` (`u ≤ D ≤ u/(1−α⋆)`; the first half is inside
  `newapproxgen_iii_a`); `:539`, `:589-595` beyond `newapprox_err` (the osc price, the Steinwart reading of `𝒦`); `:636-638` (the factor
  `(1−α⋆)^{1/γ}`); `:963-964`, `:976-979` (meta; the any-threshold variant of the converse).

## Coverage note (COVERAGE.md rows)
Rows added to `docs/planning/inventory/COVERAGE.md` (section trimmed-mmd-jmlr, now 79/79) and to the extracted inventory, with the AoS
locations: `lem:attainment` (all six clauses, earlier waves), `lem:newtrimmean`, `prop:newapproxgen`, `prop:newapprox`,
`prop:newslopegeneral`, `prop:newslope` ("first two sentences certified; last sentence hand-checked only"), `prop:newrates` ("(i), (ii)
certified; (iii) hand-checked only", the guard κ > 0, the run caveat), `prop:newconverse`. Paper face `Papers/TrimmedMMDJMLR` regenerated.

## Gate
`python3 tools/certify.py check` (2026-11-21, branch `tmmd-aos-minimax`):
`CERTIFIED: 3988 targets; statements frozen; axioms within ['Classical.choice', 'Quot.sound', 'propext']`
`python3 tools/check_aliases.py`:
`ALIASES OK: 3931 aliases in 16 paper files; each is literally a certified theorem under its frozen claim; all 3920 targets of the 16 paper pages covered (68 targets have no page)`

## AI audit notes (2026-11-21, method v1, PASS with notes; full audit `certify/audits/audit31to.md`)
1. Live source: `aos/sections/05_rates.tex` was edited again at 11:27 (sha256 `054bd58e…`, after the 10:15 version above); the statements
   of `prop:newslope`, `prop:newapprox` (with the err paragraph) and `prop:newrates` are byte-identical to the copies; the changed hunks
   are prose outside them and the out-of-scope renaming `h → Δ_𝒢` in `thm:loratemain`. `S4_rates.tex` (`1632f526…`) differs in scope
   only by `ξ_ℋ → ω_ℋ`; `02_regions.tex` is identical.
2. "17 claims" (freeze commit `fd9d482`, lock note): the commit message lists exactly the 16 frozen names and the lock note the same
   items by part (S8; S9 (i)-(iii), four claims; S10 (a)-(c); S11; S12 (a)-(b); S13, four; S14); the slip comes from `PLAN.md`
   (its table lists 15 claims plus the optional `newapprox_err`, its summary says "16 (17 with the optional S10 (c))"), repeated by the
   critic. No planned claim is missing; the note in the header above is adequate.
3. The scope paragraph of the frozen NEW_STATEMENTS block calls the excluded last sentence of `prop:newslope` "parts (c)–(d)"; the printed
   proposition has no lettered parts (the S12 block quotes the sentence; this card and the Lean header say "last sentence").
4. The remark `S4_rates.tex:612-613` is covered through a chain of certified results (`newrates_i` with `Wave30tu.upper_valid`,
   `Wave30tr.thmA` (a), `tauA_scale`), not a single target, as declared; the COVERAGE row does not claim it.
5. Gate re-run by the auditor: `CERTIFIED: 3988 targets; statements frozen; axioms within ['Classical.choice', 'Quot.sound', 'propext']`;
   `ALIASES OK: 3931 aliases in 16 paper files; …`; `#print axioms` of the 16 theorems: `[propext, Classical.choice, Quot.sound]`.
