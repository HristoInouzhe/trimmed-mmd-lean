# Fidelity card — wave 31tu: the near-parametric rate with the Laplace kernel of trimmed-mmd (**Annals of Statistics version**)

Lean: `StatFormal/Wave31tu/Statements.lean` (40 claim definitions for the drafted items Y1–Y26; 34 new definitions `IsLaplaceFeature`,
`ExpTailWith`, `SumTail`, `CondR`, `TwoSided54`, `linL`, `errL`, `rho0`, `cV`, `kappa0`, `cx`, `IntervalEvent`, `sDev`, `rDev`, `piK`,
`devA'`, `devG'`, `devB`, `lapA0`, `lapA1`, `devA`, `devG`, `epsFitI`, `epsFitII`, `fitF`, `tHat`, `uHat`, `GenuineCuts`, `IsGenuineRamp`,
`IsGenuineRun`, `IsH1`, `h1Laplace`, `levelCount`, `bumpDens`; it imports, not copies, the frozen 31tq definitions `absPQ`, `IsCross`,
`ExpTail` and the frozen 31tr definitions `IsPaperRun`, `IsGenuineQuantileRule`, `lowQ`, `highQ`; frozen 2026-11-23 before any proof,
freeze commit `69f1ac7` (on top of the merge `9997d6d`), sha256 `b01cd7091bcfaa35171e3a345ededcbb9eb85b3c189c16affc9992eb82c03f37`, locked in
`certify/statements.lock` with its 122 local imports; the file's docstring lists the encodings and junk-value guards). Routes (untrusted),
by proof chunk: L `RouteLCake`, `RouteLBanach`, `RouteLIntervals`, `RouteLBV`, `RouteLAll` (Y1, Y2, Y4, Y5); H `RouteH1`, `RouteH2` (Y3);
P `RouteP6`–`RouteP12`, `RouteP10Setup`, `RouteP14`, `RouteP14Own` (Y6–Y12, Y14); D `RouteDAux`, `RouteDErr`, `RouteD13` (Y13); F
`RouteFArith`, `RouteFSetup`, `RouteFCommon`, `RouteFOwn`, `RouteFI`, `RouteFII`, `RouteFMain`, `RouteFFrac` (Y15); B `RouteBRescale`,
`RouteBBets` (Y16, Y17); T `RouteTImproves`, `RouteTEvent`, `RouteTArith`, `RouteTFit`, `RouteTConst`, `RouteTPr`, `RouteTRate`, `RouteTAll`
(Y18, Y19, Y22); K `RouteKCore`, `RouteKLocal`, `RouteKLocalQ`, `RouteKRate` (Y20 (a)–(c), Y21); S `RouteSLocal`, `RouteSSims`,
`RouteSNotCross` (Y20 (d), (e), Y23); R `RouteR24`, `RouteR25`, `RouteR26`, `RouteRAll` (Y24–Y26); on the library folders
`StatFormal/Lib/{Indicatrix, IntervalDev, LaplaceH1, EmpiricalQuantile, LaplaceDev, FixedPoint, LaplaceScale, LaplaceRate, LocalLower,
CrossExamples, ExpMargin}` (31 files). Chunk K was split at the resume (2026-11-24): K proved `lap_local`, `lap_local_Q`, `lap_local_c`,
`local_rate`; the new chunk S proved `lap_local_d` (as `RouteS.lap_local_d_of (h20 : Claims.lap_local)`, importing chunk T's route lemma
`RouteT.laplace_twoSided` from `RouteTPr.lean`, with the coordinator's authorization), `lower2pt_not_cross` and `sims_condR`.
`Proofs.lean` defines the 40 theorems `StatFormal.Wave31tu.<claim>`, each of type literally `Claims.<claim>`; the route theorems named
`_of` take other frozen 31tu claims as hypotheses and are discharged there by the theorems proved above them: `lap_dev` (`laplace_h1`,
`lap_bv`, `lap_err`), `lap_fitted` and `lap_fitted_fraction` (`lap_err`, `lap_const`, `lap_ratio`, `lap_clip`, `lap_pop`, `lap_compare`,
`lap_dev`, `lap_own`), the seven T claims `laplace_const_i`, `laplace_const_pr_i`, `laplace_rate_i`, `laplace_rate_grid` (`lap_intervals`,
`condR_facts`, `lap_clip`, `lap_fitted`, `lap_bets`, `lap_rescale`) and `laplace_const_ii`, `laplace_const_pr_ii`, `laplace_rate_ii` (the
same without `condR_facts`), and `lap_local_d` (`lap_local`); so every theorem is unconditional. All 40 proved, `example` checks and
`#print axioms` propext, Classical.choice, Quot.sound for each (capped `lake build StatFormal.Wave31tu.Proofs`, EXIT 0). Proof commits: the
`Wave31tu WIP` commits `bc0de89` … `b8ee9d8` and the wiring commit `592099b` (`git log --oneline 69f1ac7..592099b`; interleaved and touching
no Wave31tu file: the 31tq audit commits `9d9c19a`, `5af02d4`, the map `d8a8553` and the merge `8b6711f`). No frozen claim was found false.
Paper id `trimmed-mmd (jmlr)` (face `Papers/TrimmedMMDJMLR`; the AoS version is tracked on this page, as for Waves 31tn–31tr). Branch
`tmmd-aos-fullstack` (worktree `~/projects/StatFormal-tmmd-aos`).
Scope (author decisions of 2026-11-21: Theorem 5.11 enters the paper, and the full-stack campaign `~/projects/tmmd-aos-brief/fullstack/
CAMPAIGN.md`): Theorem 5.11 `thm:laplacerate` in its printed `O` form and Theorem S4.19 `thm:laplaceconst` with its constants, the whole
proof section §S4.12 `sec:laplaceproof` (`eq:laphone`, `eq:laperr`, `eq:lappop`, Lemmas S4.20–S4.26, Proposition S4.27, the proof of
Theorem S4.19, Lemma S4.28 and the sentences around it), `eq:condR` and the prose of §5 :237-328 on it, the abstract/§1/§5 sentences on the
Laplace and Gaussian rates, the paper's run as a genuine-quantile run, Proposition S4.8 (ii) (exponential margin) and (iii) (the Gaussian
logarithmic rate), and the classical library they need (Banach's indicatrix theorem, the layer cake on `[0,1]`, the `H¹` form of the
Laplace RKHS, relative deviations for intervals, localized deviations), stated as claims and proved with no textbook bridge. Of
`GAPS.md` it closes A3 (the rate of Proposition S4.8(iii), formerly 5.9(iii); 31tq supplied its margin Q22(c) and the `ω_ℋ` bound Q17) and
the logarithmic half of E6 (the split-sample bound; the analytic Gaussian rate was dropped from the paper with 31tq Q25(d)); the rest of
the scope (Theorem 5.11, Theorem S4.19, §S4.12, `eq:condR`, Proposition S4.8(ii) in its exponential-margin form) entered the paper after
`GAPS.md` was written and has no GAPS item. Plan: `fullstack/PLAN_31tu.md`; prover brief `PROVER_BRIEF_31tu.md`.
Critic (independent AI reviewer, before the freeze; files in `tmmd-aos-brief/fullstack/`): `CRITIC_31tu.md` (v1, 2026-11-22) NOT READY TO
FREEZE (B1: in Y18(Pr), Y19, Y22, Y26 the constant was chosen after `H, φ`, now `∃ C` (resp. `∃ n₀`) before the feature space and map;
B2: Y20 assumed a finite `p̄`, now only in a conditional conjunct; B3: shapes to typecheck); `CRITIC_31tu_v2.md` (diff-only) READY TO
FREEZE (Y19(c) re-derived); the coordinated F1 at `b3125cf`, `CRITIC_F1_b3125cf.md` §4: 31tu READY TO FREEZE, no blocking item (Y24, Y8(d),
Y19(c), Y22 ACCEPT-WITH-NOTE; `‖φ x‖ ≤ κ` added to Y24 to match 31tr T5; paper corrections #7–#10 for Y19(c), Y22, Y8(d), applied at
`1fbc8df`); diff-only re-check `CRITIC_F1b_1fbc8df.md`: READY TO FREEZE, text note c1 (the §E rows §5 :240-243 and :246-249 at the
`1fbc8df` wording) applied before hashing. Change records: `DIFF_31tu.md` (v1 → v2), `DIFF_F1_b3125cf.md` (and
`work/f1_b3125cf/DIFF_31tu_section.md`, v2 → v3).
Gate (2026-11-24, on the `7db150b` tree, under the 7 GB cap): `python3 tools/certify.py check` CERTIFIED 4201 targets (statements
frozen, axioms within propext, Classical.choice, Quot.sound); `python3 tools/check_aliases.py` ALIASES OK 4144.
Fidelity review: independent AI audit, method v1 (certify/AUDIT_METHOD.md), 2026-11-24 — PASS with notes. Scope: all 40 claims,
back-translated from the frozen `Statements.lean` and its definitions and compared clause by clause with the printed text at `1fbc8df`
and at the current trimmed-mmd `8cefcef`. The reviewer had read the approved prose, which quotes the print, before the frozen file, so
the back-translation was not blind to the printed wording; the card was read only after the comparison. The 74 frozen definitions
are identical, by script, to the critic-checked scratch `Defs31tu.lean` v3.1 (706a1ca2734400f5), and its 14 copied 31tq/31tr
definitions are identical to the frozen files. Hashes: `Statements.lean` matches the lock, and no frozen file, lock entry, source copy
or target row changed after `69f1ac7`. `Proofs.lean` discharges every `_of` hypothesis (31tu claims only) by a theorem proved above it,
with nothing circular. `RouteT.laplace_twoSided`, imported by chunk S, is a proved lemma with only the hypotheses of Proposition 5.5,
built on certified 31tq/31tp theorems. Findings: 8 claims faithful and 32 faithful with a note (generalisations and declared
encodings); no undeclared stronger hypothesis, unguarded junk value, vacuous hypothesis set or restated conclusion. The four flagged
readings are faithful: `laplace_rate_grid`'s `J ≤ n∧m` is the grid of matching mesh the abstract means (note); `local_rate`'s order
"for every `T`, some nearby pair" is the printed sentence's, and Lemma S4.28 gives the `T`-free pair (note); `lap_fitted`'s lower gap
bound needs no `2ε ≤ α⋆` in the proof, so the claim implies the printed remark (note); `v₀² ≤ 4` enters through the fraction bounds
that make the printed rule a member of the run class. Post-freeze drift to `8cefcef`: every labelled environment in scope is unchanged
(`eq:laperr` notation only), and two encoded prose sentences changed, both still faithful: §1's rate sentence lost its clipping clause,
and the S4 remark behind Y21's pointer "S4 :1024-1026" is gone, while Y21 still rests on the sentence before Lemma S4.28. The gate was
re-run on the `3f43ba1` tree: CERTIFIED 4201, ALIASES OK 4144. Full audit: `tmmd-aos-brief/fullstack/AUDIT_31tu.md`. Non-blocking
notes there:
* at the merge, the paper's `aos/tools/lean_map.py` (`NOT_FORMALIZED` emptied, a `STATUS_OVERRIDE` for `prop:newrates`, whose COVERAGE
  lead is stale, the fixed prose) and `docs/trimmed-mmd-aos.md`;
* before submission, the AI statement (P6);
* the `TEXTCHANGE_57917c4.md` record notes;
* rows for the new §8 and S0 sentences, and the line tables for `8cefcef`;
* docstrings (35 of 256 new Lib declarations) and one near-duplicate Le Cam step.
**Author: approved (automatic on AI-audit PASS, per author decision 2026-10-21).**

## Source
`~/projects/tmmd-aos-brief/fullstack/NEW_STATEMENTS_31tu.md` at freeze (v3.2: v3, F1 at `b3125cf`, re-hashed at `1fbc8df`, with the
critic's text note c1): whole file sha256 `c46494bd77268fe74ab10da412ef1939f7a8fb0446505c6bf05fe9939cbbf5c7` (853 lines; copy committed in
`69f1ac7` as `certify/sources/tmmd-aos-NEW_STATEMENTS-wave31tu.md`, same hash); the claims block (line 89, "A. Common setting and encodings
of Wave31tu", to the end) sha256 `5f1293c991e6cff03ca90636b599a62b5192cd2d7714ab0e5a02e0ec3fc35aa6`. Earlier drafts kept as
`fullstack/work/NEW_STATEMENTS_31tu.v1.md`, `.v2.md` (sha256 prefix 1d7fa5a88a7f13c6), `.v3.md`; scratch shapes
`fullstack/work/scratch31tu/Defs31tu.lean` v3.1 (sha256 prefix 706a1ca2734400f5, typechecked by the drafter and the critic, EXIT 0, empty
log), with v1–v3 kept beside it. Item numbers Y1–Y26, the setting §A, the classification of every printed sentence in scope §E, the
decisions §F (D1–D17), the paper findings §G (P1–P6) and the dependencies §I are those of the source.
Printed source: trimmed-mmd `aos/` at `1fbc8df` (read with `git show 1fbc8df:<path>` for this card). Sha256 prefixes at `1fbc8df` of the
cited files (re-computed for this card, equal to the source's list): `sections/00_abstract` a3d7a240bff9, `01_introduction` 6cf223469dd0,
`02_regions` 6126ebd22dbe, `04_split` ba0117322917, `05_rates` 9bcd992dbfab, `06_trimming` 725265e8156e, `07_numerical` d3a9002b1b03,
`08_final` 9b6f55fb3a9f, `09_backmatter` 3aaff798b7e7, `supplement/00_abstract` 91ac1181e282, `supplement/S3_split` 3325e6424cdc,
`supplement/S4_rates` 58bf03da5e94, `supplement/S6_experiments` bbad674c39eb, `preamble` 75ea6de5a068. Printed numbers: `aos/main.aux`,
`aos/supplement.aux` of the build of `b3125cf` (all 111 labelled environments are byte-identical at `1fbc8df` after normalization): Thm 5.11
`thm:laplacerate`, (5.1) `eq:condR`, Thm S4.19 `thm:laplaceconst`, (S4.7) `eq:laphone`, (S4.8) `eq:laperr`, (S4.9) `eq:lappop`, Lemmas S4.20
`lem:lapratio`, S4.21 `lem:lapclip`, S4.22 `lem:lapcompare`, S4.23 `lem:lapintervals`, S4.24 `lem:lapbv`, S4.25 `lem:lapdev`, S4.26
`lem:lapown`, Prop S4.27 `prop:lapfitted`, Lemma S4.28 `lem:laplocal`, §S4.12 `sec:laplaceproof`, Prop S4.8 `prop:newrates`, Prop 5.5
`prop:newsobolev`, Prop 5.6 `prop:newgauss`, Thm 5.7 `thm:loratemain`, Prop 5.8 `prop:lower2pt`, Thm S4.3 `thm:lorate`, Prop 4.4
`prop:loconsistency`, Algorithm S1 `alg:split`. Line numbers below are those of `1fbc8df`: `main` = `sections/05_rates.tex`, `§1` =
`01_introduction.tex`, `§2` = `02_regions.tex`, `§4` = `04_split.tex`, `§7` = `07_numerical.tex`, `§8` = `08_final.tex`, `abs` =
`00_abstract.tex`, `bm` = `09_backmatter.tex`, `S3`, `S4`, `S6` = the supplement files.
Post-freeze drift: not checked for this card (the paper was read only at `1fbc8df`). Known: `TEXTCHANGE_57917c4.md` (2026-11-24) records
that Proposition 5.6 gained the words "the slope of p−q at x₀" after "put `ℓ₀ = (p−q)′(x₀)`" at trimmed-mmd `57917c4` (notation only,
FAITHFUL; Y26 takes Prop 5.6's hypotheses through 31tq's `IsCross`, whose `ℓ₀` is that slope). The auditor should compare the labelled
environments and the unlabelled sentences cited here against the current paper master.

## Targets (40 claims in `StatFormal.Wave31tu.Proofs`; all in `certify/targets.toml`, theorem = `StatFormal.Wave31tu.<name>`)
| item | label (abridged) | claim |
|---|---|---|
| Y1(a) | S4 :1220-1222 (Banach's indicatrix theorem, the half used by `lem:lapbv`) | `banach_indicatrix_le` |
| Y1(b) | S4 :1220-1222 (the printed equality `∫N = V_I(h)`) | `banach_indicatrix` |
| Y2 | S4 :1218-1219 (the layer cake for `[0,1]`-valued functions) | `layer_cake01` |
| Y3(a), (c) | S4 :1039-1048, `eq:laphone` (eq. S4.7; S4 :1043-1046) | `laplace_h1` |
| Y3(b) | S4 :1039-1041 (the `H¹` identification) | `laplace_h1_char` |
| Y4 | `lem:lapintervals` (Lemma S4.23; S4 :1188-1205), S4 :1351-1352, :1088-1089 | `lap_intervals` |
| Y5 | `lem:lapbv` (Lemma S4.24; S4 :1207-1225) | `lap_bv` |
| Y6 | `eq:laperr` (eq. S4.8; S4 :1048-1056) | `lap_err` |
| Y7 | S4 :1063-1071 (the constants `ρ₀`, `c_V`, `κ₀`) | `lap_const` |
| Y8 | `eq:condR` (eq. 5.1; main :304-307), main :324-325, abs :12-13, §1 :85-86, S4 :1071-1073 | `condR_facts` |
| Y9 | `lem:lapratio` (Lemma S4.20; S4 :1075-1086) | `lap_ratio` |
| Y10 | `lem:lapclip` (Lemma S4.21; S4 :1088-1132), §2 :230-232, main :288-290 | `lap_clip` |
| Y11 | `eq:lappop` (eq. S4.9; S4 :1134-1143), S4 :1342-1344 (order of `g⋆`) | `lap_pop` |
| Y12 | `lem:lapcompare` (Lemma S4.22; S4 :1145-1182) | `lap_compare` |
| Y13 | `lem:lapdev` (Lemma S4.25; S4 :1227-1275), at `σ = 1` | `lap_dev` |
| Y14 | `lem:lapown` (Lemma S4.26), the general inequality | `own_ramp` |
| Y14 | `lem:lapown` (Lemma S4.26; S4 :1277-1291), printed form | `lap_own` |
| Y15(a), (b) | `prop:lapfitted` (Proposition S4.27; S4 :1293-1344), at `σ = 1` | `lap_fitted` |
| Y15(c) | main :290-291, S4 :1034-1036 (a fixed fraction of the population excess) | `lap_fitted_fraction` |
| Y16 | S4 :1037-1038, :1354-1366 (the bets are those of Theorem S4.3) | `lap_bets` |
| Y17 | S4 :1038-1039 (rescaling the data by `1/σ`) | `lap_rescale` |
| Y18 (G) | `thm:laplaceconst` (Theorem S4.19; S4 :989-1018) (i), uniform form | `laplace_const_i` |
| Y18 (G) | `thm:laplaceconst` (ii), uniform form | `laplace_const_ii` |
| Y18 (Pr) | `thm:laplaceconst` (i) under the printed hypotheses, `∃ C` before `H, φ` | `laplace_const_pr_i` |
| Y18 (Pr) | `thm:laplaceconst` (ii) under the printed hypotheses | `laplace_const_pr_ii` |
| Y19(i) | `thm:laplacerate` (Theorem 5.11; main :293-318) (i), S4 :985-987 | `laplace_rate_i` |
| Y19(ii) | `thm:laplacerate` (ii) | `laplace_rate_ii` |
| Y19(c) | main :240-243 ("which Theorem 5.11 improves to `(n∧m)^{−1/2}` …, for samples of comparable size") | `laplace_rate_improves` |
| Y20(a) | `lem:laplocal` (Lemma S4.28; S4 :1386-1414), first sample | `lap_local` |
| Y20(b) | `lem:laplocal`, second sample | `lap_local_Q` |
| Y20(c) | S4 :1416-1417 (the choice `h = (1−δ)/{2(nπ)^{1/2}}`) | `lap_local_c` |
| Y20(d) | S4 :1417-1418 ("The constants of Proposition 5.5 for `(P_h,Q)` exist") | `lap_local_d` |
| Y20(e) | S4 :1383-1384 (the pairs of Proposition 5.8 do not satisfy these hypotheses) | `lower2pt_not_cross` |
| Y21 | S4 :1024-1026, :1383 (an error of order `(n∧m)^{−1/2}` near each pair covered by (i)) | `local_rate` |
| Y22 | abs :11-13; §1 :84-88; main :8-10, :322-323 (order `(n∧m)^{−1/2}` up to logarithmic factors on a grid of that mesh) | `laplace_rate_grid` |
| Y23 | S6 :157, :167-168 (the simulated pairs satisfy (5.1)) | `sims_condR` |
| Y24(a) | §4 :60-68, S3 :105-111 (the paper's run is a genuine-quantile run) | `genuine_paperrun` |
| Y24(c) | S3 :181-182, §7 :20-22 (the printed run exists and is one) | `genuine_run_exists` |
| Y25 | `prop:newrates` (Proposition S4.8) (ii) (S4 :470-487; proof :514-526) | `newrates_ii_exp` |
| Y26 | `prop:newrates` (iii) (S4 :484-485; proof :736-745), main :243-246, abs :9-10, §1 :82-83 | `newrates_iii_gauss` |

## Encodings (declared; full list in the Lean header and `NEW_STATEMENTS_31tu.md` §A, §F)
* Kernel: "the kernel `e^{−|x−y|/σ}`, `σ > 0` fixed in advance" (main :297) is a feature map `φ : ℝ → H` with `IsLaplaceFeature σ φ`
  (`⟪φx, φy⟫ = e^{−|x−y|/σ}`) into a real inner-product space `H`, complete, and separable where Assumption 2.1 (A2) is used (31tq rule
  D1; Y3, Y9, Y13, Y17, Y24 do without it, a generalisation). Continuity, strong measurability, `‖φx‖ = 1` (`κ = 1`), characteristic and
  strictly positive definite are theorems (31tp L14, L16, L25 with L21/L22), not hypotheses. Non-vacuity: 31tp L15 `feature_exists` with
  31tq Q7(a) gives a complete separable `H : Type` for every `σ > 0` (the routes also build an explicit `L²(ℝ)` feature map,
  `Lib/LaplaceH1/Feature`). Nothing depends on the choice of `φ` (31tp L12 `gram_mmd`).
* Bandwidth (D1): the lemmas of §S4.12 are printed after "so we take `σ = 1`" (S4 :1039). Y13 and Y15, whose constants are those of `σ = 1`,
  are stated at `σ = 1` as printed; Y3 for every `σ`; Y9–Y12, Y14 for every `σ` (scale-free); the theorems Y18–Y22 for every `σ > 0` as
  printed, through the rescaling claim Y17 (D9).
* Laws: "the hypotheses of Proposition 5.5 (on the laws)" are 31tq's (L55) `IsCross P Q p q x₀ ℓ₀ ∧ 0 < p x₀ ∧ ExpTail P Q x₀` (Lebesgue
  densities `p, q`, measurable nonnegative versions, continuous on an open interval about `x₀`, `q ≤ p` a.e. on `(x₀, ∞)`, `p ≤ q` a.e. on
  `(−∞, x₀)`, `HasDerivAt (p − q) ℓ₀ x₀`, `ℓ₀ > 0`, `p(x₀) > 0`, and `|P−Q|({|x−x₀| > t}) ≤ C′e^{−t/C′}` with `C′ > 0`); `α⋆ = tvDist P Q`,
  and `0 < α⋆ < 1` follows (31tq route `cross_tv`). `ExpTailWith P Q x₀ C′` names the tail constant; `SumTail P Q x₀ C′` is the printed
  `(P+Q)({|x−x₀| > t}) ≤ C′e^{−t/C′}` for all `t > 0` with `C′ > 0` (Theorem 5.11(ii)). (5.1) is `CondR p q x₀ r⋆ c⋆`: `0 < r⋆ ≤ 1`, `c⋆ > 0`
  and `c⋆ min(r⋆, |x−x₀|)(p+q)(x) ≤ |p−q|(x)` for almost every `x`, for the density versions of `IsCross`. `p̄ = sup_{[x₀−r⋆, x₀+r⋆]}(p+q)` is
  read as any bound `p + q ≤ p̄` on that interval (pointwise, for those versions; the printed supremum is the least, and the constants
  increase in `p̄`). `TwoSided54 φ P Q c₁ c₂ ε₀` is the two-sided bound of Proposition 5.5 at `s = 1` with the printed range: `0 < c₁ ≤ c₂`,
  `0 < ε₀ ≤ α⋆`, `c₁ε^{5/4} ≤ D_{α⋆−ε} ≤ c₂ε^{5/4}` for `ε ∈ (0, ε₀]`.
* Functions of the RKHS (D4): an element `g : H` and its function `wit φ g = ⟪g, φ·⟫`; "`φ ∈ ℋ` with `‖φ‖_ℋ`" is read for every
  representer `g` with `‖g‖` (each statement is monotone in the norm in the direction that makes the representer form imply the printed
  one, and the least representer is attained, 31tp L18; where the printed text names a least norm, Y10(g) and Y11 state that the element
  is a least representer). `osc = oscFn` (`iSup − iInf`), `L(f) = linL P Q f = ∫f dP − ∫f dQ`, `err(f) = errL P Q f = α⋆ − L(f)` (equal to
  the frozen `errFn` on `[0,1]`-valued `f`, Y6), `D̄_α = uPath φ P Q α` (`(1−α)D_α`), `V(ε) = uPath φ P Q (α⋆ − ε)`.
* Empirical objects: `P̃ = empirical x` for `x : Fin n → ℝ`; `L̃ = linL (empirical x) (empirical y)`; an exact minimizer of (2.10) is
  `IsQPMin φ α x y w v`, `D̂ = qpVal` (`= Demp`, Y10(a)), `D̄̂ = (1−α)qpVal`, the witness `f̂ = fitF`, `t̂ = tHat` (the `⌈n(1−α)⌉`-th order
  statistic of `f̂` at the `X`'s), `û = uHat` (the `(⌊mα⌋+1)`-th at the `Y`'s), `ĝ = t̂ − û`, `φ̂ = ĝ⁻¹ • witness`; own-term values the frozen
  `ownX`, `ownY`. "With the pooled points pairwise distinct" (S4 :1088-1089) is read in the lemmas as the weaker "no `X` equals a `Y`"
  (`∀ i j, x i ≠ y j`, what the proofs use: `TV(P̃,Q̃) = 1`; D14, a generalisation); the printed "(almost surely, as `P` and `Q` have
  densities)" is Y4(c), with full pairwise distinctness. The fitting batches of sizes `n′, m′` are arbitrary samples of sizes `n, m`.
* Cut points (D2): `GenuineCuts φ x y w v α t u` = (`t` a genuine empirical `(1−α)`-quantile of `f̂` at the `X`'s and `u` a genuine `α`-quantile
  at the `Y`'s) or (the same for the own-term values), `IsEmpQuantile h p q` being `#{h_i < q} ≤ np ≤ #{h_i ≤ q}`. `IsGenuineRamp` is the
  frozen `IsWitnessRamp` with `GenuineCuts` in place of (cutrank), and `IsGenuineRun R φ α δ λ_max v²_min` the frozen `IsWitnessRun` with
  `IsGenuineRamp` in place of `IsWitnessRamp` (admissibility, the per-level rule on the fitting sample of every batch that holds a pair, and
  the fraction bounds `lamHi`/`lamLo`/`0`). The choice plain or own-term may differ between levels, batches and samples; the printed "computed
  with or without the own terms" is its two uniform instances.
* "Compute `α̂` as in Theorem 5.7 / at level `δ` as in Proposition 4.4, with the batches and fractions of Section 4.2, `λ_max = ½`, initial
  variance `v₀² ≤ 4` in (S3.3), the running variance floored at `v²_min ∈ (0,4]`, an exact minimizer at each level, and genuine-quantile cut
  points" is `IsGenuineRun R φ α δ (1/2) v²_min ∧ IsDefaultRun R` (batches at the nearest integers to `n/4, n/2`, `N = defaultPairs`, the
  frozen Wave31tl encoding); the printed fractions with `v₀² ≤ 4` and the floor enter only through the bounds `lamHi`/`lamLo` they satisfy
  (certified `fractions_bounds`), so the run class contains the printed runs; the paper's own run is in it and exists (Y24). "A grid of `J`
  levels in `(0,1)` fixed in advance" is `IsGrid α ∧ ∀ j, 0 < α j`, `J ≥ 1`; "whose mesh below `α⋆` is `Δ_𝒢`" is any `h` with
  `MeshBelowLe α α⋆ h` (the printed mesh is the least; a generalisation, as in Wave31tl); `α̂ = R.alphaLo α δ` (`eq:downclosed`); the order of
  the observations is an order fixed in advance (S3 :101), as on the 31tl card. In Y25, Y26 "compute `α̂` as in Theorem 5.7" is the frozen
  class of Theorem S4.3, `IsWitnessRun ∧ IsDefaultRun` with (cutrank), which contains the paper's own run (31tr T5).
* "With probability at least `1 − p`, `S`": a measurable `E` with `ofReal(1 − p) ≤ sampleLaw P Q n m E` and `E ⊆ S`. A valid lower bound of the
  local claims Y20, Y21 is any measurable `T` of the two samples and an independent randomization `ρ` on any `Ξ` (`(sampleLaw P Q n m).prod ρ`)
  with `P_{P,Q}(T > α⋆) ≤ δ`, validity being asked at the unperturbed pair only (a stronger claim).
* "`C` depends only on …" (Theorem S4.19, S4 :1015-1017; Theorem 5.11, main :316-317) (D3, B1): the uniform form (G) `∀ σ α⋆ c₁ c₂ ε₀ C′ [c⋆ r⋆
  p̄], ∃ C, ∀ H φ P Q p q x₀ ℓ₀ J n m α δ v²_min η h R, [hypotheses with these constants] → …`, so that `C` is free of `x₀, ℓ₀, p(x₀)`, of
  `δ, η, J, v²_min`, of the grid and of `n, m`; and, under the printed hypotheses only, the form (Pr) `∀ σ P Q p q x₀ ℓ₀ [r⋆ c⋆ | C′], (L55) →
  [CondR | SumTail] → ∃ C, ∀ H φ, IsLaplaceFeature σ φ → ∀ J n m α δ v²_min η h R, …`, with `∃ C` before the feature space and map (the RKHS
  is determined by the kernel). Y19, Y22 use the (Pr) order, Y26 the same order with `∃ n₀`.
* "For samples of comparable size" (main :240-243, D15): `n∨m ≤ (n∧m)^k` for a fixed `k ≥ 1`; "improves" read as `o((n∧m)^{−2/5})`.
* Intervals (D10): "every interval `I ⊆ ℝ`" is every `OrdConnected` set (empty, singletons, bounded intervals of the four kinds, half-lines, ℝ).
* `H¹(ℝ)` is `IsH1 f` (locally absolutely continuous on every `[a,b]`, `f ∈ L²`, `deriv f ∈ L²`; `deriv` is the a.e. derivative of a locally
  AC function), and `h1Laplace σ f = (1/(2σ))∫⁻(f² + σ²(deriv f)²)` in `[0, ∞]` (`= ½∫(f²+f′²)` at `σ = 1`, the printed norm).
* `N(s) = #{x ∈ [a,b] : h x = s}` is `levelCount h a b s` in `[0, ∞]` (`Set.encard`); `V_I(h)` is `eVariationOn` in `[0, ∞]`.
* The perturbed law `P_h` of Lemma S4.28 is `volume.withDensity (bumpDens p A₁ B₁ P(A₁) P(B₁) π h)` with the printed identity
  `P_h(S) = P(S) + hπ{P(S∩A₁)/P(A₁) − P(S∩B₁)/P(B₁)}` for measurable `S` as a conjunct, and `IsProbabilityMeasure P_h` by an existential
  binder.
* New total definitions: `rho0`, `cV`, `kappa0` (the printed `ρ₀`, `c_V`, `κ₀`), `cx c = 2c+4`, `sDev c n m = √(c/n) + √(c/m)` (`s_{n,m}`),
  `rDev n m = 1/n + 1/m`, `piK P Q x₀ K = (P+Q).real{|z−x₀| > K}`, `devA′ = 5s + 4c_xr + 2π_K`, `devG′ = 2K^{1/4}s`, `devB = 6K^{1/2}c_xr`,
  `lapA0`, `lapA1` (the printed `A₀`, `A₁`), `devA = A₀s + 7c_xr + 2π_K`, `devG = A₁K^{1/4}s` (the printed `ϖ, ϖ′` of `b3125cf`), `epsFitI`,
  `epsFitII` (the two printed `ε_fit`, written out term by term), `IntervalEvent P x c` (the event of Lemma S4.23 at parameter `x = c`).

## Covered — back-translation and deviations
Back-translated from the frozen `Statements.lean`. Shorthands: "(Lap σ)" means `H` a complete real inner-product space, `σ > 0` and
`IsLaplaceFeature σ φ` for `φ : ℝ → H`, "(Lap σ, sep)" the same with `H` separable; "the run hypotheses" are `IsGrid α`, `∀ j, 0 < α_j`,
`J ≥ 1`, `δ, η ∈ (0,1)`, `v²_min ∈ (0,4]`, `IsGenuineRun R φ α δ (1/2) v²_min`, `IsDefaultRun R`, `n∧m ≥ 10` and `MeshBelowLe α α⋆ h`; "the
fitting setting at `α`" is `n, m ≥ 1`, samples `x, y` with no `x_i = y_j`, `α ∈ (0,1)` and `IsQPMin φ α x y w v`; "the population objects at
`α = α⋆ − ε`" are nearest points `a ∈ 𝒞_α(P)`, `b ∈ 𝒞_α(Q)` (`a ∈ region φ α P`, `b ∈ region φ α Q`, `‖a − b‖ = D_α`), `t⋆` the least
`(1−α)`-quantile under `P` and `u⋆` the greatest `α`-quantile under `Q` of `f⋆ = ⟨(a−b)/‖a−b‖, φ·⟩` (the printed `t⋆, u⋆`, encoded as in
the certified `pop_ramp_rkhs` and 31tr's (Pr) form), `ψ⋆ = ramp f⋆ t⋆ u⋆`, `φ⋆ = (t⋆−u⋆)⁻¹(a−b)/‖a−b‖`; `L = log((n∨m)/η)`,
`B = v²_min⁻¹(√log(1/δ) + √log(2J/η))/√(n∧m)`.

**Block L (the classical library).**
* Y1 `banach_indicatrix_le`: for `h : ℝ → ℝ` and `a ≤ b` with `h` continuous on `[a,b]`: `s ↦ N(s) = #{x ∈ [a,b] : h x = s}` is measurable and
  `∫⁻ N ≤ V_{[a,b]}(h)`. `banach_indicatrix`: under the same hypotheses `∫⁻ N = V_{[a,b]}(h)`. Printed S4 :1220-1222 ("By Banach's indicatrix
  theorem [Banach 1925], `N` is measurable and `∫N(s)ds = V_I(h)`", with `N(s)` the number of points of `Ī` where `h = s`). Faithful; both sides in
  `[0, ∞]`, `a = b` allowed; (a) is the half that Y5 uses (D8), measurability is stated in (a). Not in Mathlib or Tau Ceti; proved in
  `Lib/Indicatrix` (dyadic counting functions, and the reverse inequality by the intermediate value theorem on each partition gap).
* Y2 `layer_cake01`: for any finite measure `μ` on any measurable space and `h` with values in `[0,1]`, `AEMeasurable h μ`:
  `∫ h dμ = ∫_0^1 μ.real{h > s} ds`. Printed S4 :1218-1219 ("By Tonelli's theorem, `∫_I h d(P̃−P) = ∫_0^1(P̃−P)(A_s)ds` and `∫_I h dP =
  ∫_0^1 P(A_s)ds`"). Faithful: the printed signed form is the difference of the claim for `P̃` and for `P` restricted to `I` (a hand step,
  in the route of Y5); generalisation: any finite measure. A documented wrapper of Mathlib's layer cake.
* Y3 `laplace_h1`: (Lap σ) (no separability): (a) for every `g : H`, `wit φ g` is `IsH1` and `h1Laplace σ (wit φ g) ≤ ‖g‖²`, with equality
  when `g` lies in the closed span of `φ(ℝ)`; (c) for every `g`: `|wit φ g x| ≤ ‖g‖` for all `x`; `∫_a^b |(wit φ g)′| ≤ √(2(b−a)/σ)‖g‖` and
  `V_{[a,b]}(wit φ g) ≤ √(2(b−a)/σ)‖g‖` for `a ≤ b`; `wit φ g → 0` along the cocompact filter; and `osc(wit φ g) ≤ 1` implies `|wit φ g| ≤ 1`.
  `laplace_h1_char` (b): under (Lap σ), a continuous `f : ℝ → ℝ` is represented (`∃ g, ⟪g, φ·⟫ = f`) iff `IsH1 f`, and then some representer
  `g₀` has `‖g₀‖² = h1Laplace σ f` and `‖g₀‖ ≤ ‖g‖` for every representer `g`. Printed S4 :1039-1048 at `σ = 1` ("The reproducing kernel
  Hilbert space of `e^{−|x−y|}` is the Sobolev space `H¹(ℝ)` with `‖f‖²_ℋ = ½∫(f²+f′²)`, since `e^{−|x|}` has Fourier transform `2/(1+ω²)`
  [Wendland, Thm 10.12]. Every `f ∈ ℋ` is absolutely continuous, tends to `0` at `±∞`, and satisfies `|f(x)| ≤ ‖f‖_ℋ`, `∫_a^b|f′| ≤
  √(2(b−a))‖f‖_ℋ` (S4.7) … for `f ∈ ℋ` with `osc(f) ≤ 1`, `|f| ≤ 1`, as `f` tends to `0` at infinity"). Faithful; generalisation: every
  `σ > 0` (at `σ = 1` the norm is `½∫(f²+f′²)` and the factor `√(2(b−a))`); encodings: `H¹` as `IsH1`, the RKHS as the represented functions
  with the least representer norm, "`f ∈ ℋ`" for every representer (D4); the variation conjunct is the form Lemma S4.25 uses ("the variation
  of `φ` on an interval of length `λ` is at most `(2λ)^{1/2}N`", S4 :1245-1246). The cited reason "since `e^{−|x|}` has Fourier transform
  `2/(1+ω²)`" is replaced by a proof (the route uses an explicit `L²` feature map, no Fourier analysis; the transform itself is certified as
  31tq Q7(a)). The identification (b) is used by no proof of the wave (D11).
* Y4 `lap_intervals`: (a) for every probability `P` on ℝ with no atoms (`NullSingletonClass`), `n ≥ 1`, `η′ ∈ (0,1)`: a measurable `E ⊆ ℝ^n`
  with `P^{⊗n}(E) ≥ 1 − η′` on which `IntervalEvent P x (log(2(n+1)²/η′))` holds, i.e. every `OrdConnected` `I ⊆ ℝ` has `|P̃(I) − P(I)| ≤
  √(2P(I)x/n) + c_x/n`, `c_x = 2x + 4`; (b) for any `P`, `x` and `0 ≤ c ≤ c′`, `IntervalEvent P x c` implies `IntervalEvent P x c′`; (c) for
  probabilities `P, Q` on ℝ, both atomless, and all `n, m`: the pooled sample has pairwise distinct points (each sample injective and no
  `X` equal to a `Y`) `sampleLaw P Q n m`-almost surely. Printed Lemma S4.23 (S4 :1188-1193: "`P̃` the empirical law of `n` independent draws
  from `P`, which has a continuous distribution function, `η′ ∈ (0,1)`, `x = log{2(n+1)²/η′}`, `c_x = 2x+4`. With probability at least `1−η′`,
  every interval `I ⊆ ℝ` satisfies …"); S4 :1351-1352 ("these events weaken as `x` grows"); S4 :1088-1089 ("with the pooled points pairwise
  distinct (almost surely, as `P` and `Q` have densities)"). Faithful; encodings: a continuous distribution function as an atomless law
  (equivalent on ℝ), intervals as `OrdConnected` sets (D10); generalisation in (c): atomless laws in place of laws with densities. The
  route's sandwich is deterministic (no almost-sure event on the constancy intervals of `F` is needed, unlike the printed proof).
* Y5 `lap_bv`: for a probability `P` on ℝ, `n ≥ 1`, `c ≥ 0` and `IntervalEvent P x c`: for every bounded `OrdConnected` `I`, every
  `h : ℝ → [0,1]` continuous on `Ī` and every `V ≥ 0` with `V_{Ī}(h) ≤ V`: `|∫_I h dP̃ − ∫_I h dP| ≤ √(2(V+1)(∫_I h dP)c/n) + (V+1)c_x/n`.
  Printed Lemma S4.24 (S4 :1207-1213). Faithful; generalisations: any finite upper bound `V` of the variation (the printed `V_I(h)`, when
  finite, is the least, and the right side increases in `V`; when it is infinite the printed bound is empty), the event at any parameter
  `c ≥ 0`; encoding: "the total variation there" on the closure (for `h` continuous on `Ī` the variations on `I` and on `Ī` agree).

**Block P (the proof section §S4.12).**
* Y6 `lap_err`: probabilities `P = p·Leb`, `Q = q·Leb` (measurable nonnegative `p, q`), `f` measurable and bounded with `osc(f) ≤ 1`, `M = sup f`,
  `m = inf f`: `err(f) = α⋆(1 − osc f) + ∫(M − f)(p−q)₊ + ∫(f − m)(q−p)₊`, each of the three terms is `≥ 0`, `0 ≤ err(f) ≤ 2`, and `errL = errFn`
  when `f` is `[0,1]`-valued. Printed S4 :1048-1056 (`L`, `err`, "the error of Section 5.2 when `f` takes values in `[0,1]`", (S4.8), "all
  three terms being nonnegative: the error of a function of oscillation at most one is its loss of range plus …"). Faithful; the last
  clause is the identity read in words; `osc(f) = M − m`.
* Y7 `lap_const`: (A1)–(A2) on ℝ (`H` complete separable, `φ` strongly measurable with `‖φx‖ ≤ κ`; any feature map), `α⋆ < 1`,
  `TwoSided54 φ P Q c₁ c₂ ε₀`: `0 < ρ₀ < 1`, `0 < κ₀ < 1`, `0 < c_V`; `e ↦ V(e)` nondecreasing on `[0, α⋆]`; `(1−α⋆)D_{α⋆−e} ≤ V(e) ≤
  D_{α⋆−e}` on `[0, α⋆]`; `c_V e^{5/4} ≤ V(e)` on `(0, α⋆]`; `ρ₀V(2e) ≤ V(e)` for `e ∈ (0, ε₀/2)`. Printed S4 :1063-1071 ("so that `ρ₀, κ₀ ∈ (0,1)`
  and `c_V > 0`. Each has one role: `ρ₀` is a lower bound on `V(ε)/V(2ε)` for `ε < ε₀/2`, by the two-sided bound and `(1−α⋆)D_{α⋆−ε} ≤ V(ε) ≤
  D_{α⋆−ε}`; `c_V` extends the lower bound to all levels, … as `V` is nondecreasing"). Faithful; generalisation: any feature map with the
  two-sided bound. "`κ₀` is the fraction of `ε` that the comparison below guarantees as excess" is the reading of Y12(ii). The first printed
  sentence (S4 :1061-1062, existence of `c₁, c₂, ε₀` "by Proposition 5.5 with `s = 1`") is the hand composition of 31tq Q21 with Q7(a) (route
  lemma `RouteT.laplace_twoSided`, used in Y18(Pr) and Y20(d)), not a claim of this wave.
* Y8 `condR_facts`: under `IsCross P Q p q x₀ ℓ₀` and `0 < p x₀`: (b) `(∃ r⋆ c⋆, CondR p q x₀ r⋆ c⋆)` iff for every `r > 0` some `c > 0` has
  `c(p+q) ≤ |p−q|` a.e. on `{|x−x₀| ≥ r}`; and for `CondR p q x₀ r⋆ c⋆`: (c) `CondR` with every `r⋆′ ∈ (0, r⋆]` and the same `c⋆`; some
  `r⋆′ ∈ (0, r⋆]` and `p̄` with `p + q ≤ p̄` on `[x₀−r⋆′, x₀+r⋆′]`; `p + q ≤ |p−q|/(c⋆r⋆)` a.e. on `{|x−x₀| ≥ r⋆}`; and for every `C′` with
  `ExpTailWith P Q x₀ C′`, `(P+Q){|x−x₀| > t} ≤ C′e^{−t/C′}/(c⋆r⋆)` for `t ≥ r⋆` and `SumTail P Q x₀ C″` for some `C″`; (d) for every `a < b`, if
  `p = q` a.e. on `(a,b)`, then `p + q = 0` a.e. on `(a,b)`. Printed: main :324-325 ("Condition (5.1) asks that `p/q` stay away from one off
  every neighborhood of `x₀`, so it excludes contaminations local to a common core, with `p = q > 0` on an interval, where only part (ii)
  applies"), abs :12-13 ("when the likelihood ratio stays away from one off the crossing"), §1 :85-86, S4 :1071-1073 ("`p̄` …, which is finite
  once `r⋆` is small, as `p, q` are continuous near `x₀`, and shrinking `r⋆` keeps (5.1) with the same `c⋆`; off this interval `p + q ≤
  |p−q|/(c⋆r⋆)`, so `P+Q` inherits the exponential tails of `|P−Q|`"). Faithful under the declared readings: "stay away from one" as `|p−q| ≥
  c(p+q)` (i.e. `p/q ∉ ((1−c)/(1+c), (1+c)/(1−c))` where `q > 0`); "excludes contaminations local to a common core, with `p = q > 0` on an
  interval" as (d) (critic correction #9 printed `p = q > 0`); "where only part (ii) applies" is a scope reading (declared, no claim). The
  source's v2 part (a) (the bound near `x₀`) was dropped with its sentence and survives as a route lemma.
* Y9 `lap_ratio`: any measurable space, `H` complete, `φ` strongly measurable with `‖φx‖ ≤ κ`, probabilities `P, Q`, `α ∈ [0,1)`, `g ≠ 0` with
  `osc(wit φ g) ≤ 1`: `(L(wit φ g) − α)/‖g‖ ≤ D̄_α(P,Q)`; and if `α⋆ < 1`, `(e − err(wit φ g))/‖g‖ ≤ V(e)` for every `e ∈ [0, α⋆]`. Printed Lemma
  S4.20 (S4 :1075-1080: "For any probability measures `P̃, Q̃`, any `α ∈ [0,1)` and any `φ ∈ ℋ ∖ {0}` with `osc(φ) ≤ 1`, `D̄_α(P̃,Q̃) ≥ {L̃(φ) −
  α}/‖φ‖_ℋ`. In particular `V(ε′) ≥ {ε′ − err(φ)}/‖φ‖_ℋ` for `ε′ ∈ [0, α⋆]`"). Faithful; generalisation: any measurable space and bounded
  feature map, no separability (the lemma uses no property of the Laplace kernel); declared: `α⋆ < 1` for the "in particular" (the printed
  context, (L55)); every representer (D4).
* Y10 `lap_clip`: (Lap σ, sep), the fitting setting at `α`: (a) `0 < D̂` and `D̂ = Demp φ x y α`; (b) `û ≤ f̂ ≤ t̂` on ℝ; (c) `osc(f̂) = t̂ − û > 0`;
  (d) the order statistics of `f̂` at the `X`'s of ranks `⌈n(1−α)⌉, …, n` equal `t̂`, those at the `Y`'s of ranks `1, …, ⌊mα⌋+1` equal `û`;
  (e) every genuine `(1−α)`-quantile of the values at the `X`'s is `t̂`, every genuine `α`-quantile of those at the `Y`'s is `û`; (f) `ramp f̂ t̂ û =
  (f̂ − û)/(t̂ − û)`; (g) `osc(wit φ φ̂) = 1`, `‖φ̂‖ = 1/(t̂−û) ≥ ½`, and `‖φ̂‖` is the least representer norm of `wit φ φ̂`; (h) `L̃(φ̂) − α =
  (1−α)D̂‖φ̂‖`; (i) `φ̂` maximizes `(L̃(g′) − α)/‖g′‖` over `g′ ≠ 0` with `osc(wit φ g′) ≤ 1`; (j) the own-term order statistics at the `X`'s of
  ranks `⌈n(1−α)⌉, …, n` lie in `[t̂ − 1/(n(1−α)D̂), t̂]`, those at the `Y`'s of ranks `1, …, ⌊mα⌋+1` in `[û, û + 1/(m(1−α)D̂)]`; (k) every genuine
  own-term `(1−α)`-quantile lies in `[t̂ − 1/(n(1−α)D̂), t̂]` and every own-term `α`-quantile in `[û, û + 1/(m(1−α)D̂)]`. Printed S4 :1088-1109
  (the setting and Lemma S4.21: "Then `D̄̂ > 0`, `û ≤ f̂ ≤ t̂` on ℝ, `ĝ = t̂ − û = osc(f̂) > 0`, … Hence every genuine `(1−α)`-quantile … is `t̂`, …
  and the plain ramp is `ψ̂ = (f̂ − û)/ĝ`. Moreover `φ̂ = f̂/ĝ` has `osc(φ̂) = 1`, `N̂ = ‖φ̂‖_ℋ = 1/ĝ ≥ ½` and `L̃(φ̂) − α = D̄̂N̂`, so by Lemma S4.20
  `φ̂` maximizes … With the own terms removed, the values … lie in `[t̂ − 1/(n′D̄̂), t̂]` … `[û, û + 1/(m′D̄̂)]`"), with §2 :230-232 ("with the Laplace
  kernel on the line all the `X`'s from rank `⌈n(1−α)⌉` on do") and main :288-290. Faithful; `D̄̂ = (1−α)D̂`, so `1/(n′D̄̂) = 1/(n(1−α)D̂)`;
  encodings: "pooled points pairwise distinct" as no `X` equal to a `Y` (D14); `φ̂` as an element of `H`; (k) is the consequence that
  Lemma S4.26 uses. Generalisation: every `σ > 0`. The proof sentence S4 :1112-1119 (Lemmas S4.17, S4.18 and Proposition 5.10(iii) hold for
  `P̃, Q̃`) is 31tr T38, T39, T42 in their general form (G), used by the route.
* Y11 `lap_pop`: (Lap σ, sep), `0 < ε < α⋆ < 1`, the population objects at `α = α⋆ − ε`: `D_α > 0`, `t⋆ − u⋆ > 0`, `osc(wit φ φ⋆) ≤ 1`,
  `‖φ⋆‖ = 1/(t⋆−u⋆)` and it is the least representer norm, `L(φ⋆) − α = E_Pψ⋆ − E_Qψ⋆ − α = V(ε)/(t⋆−u⋆) ≤ ε`, `V(ε)/ε ≤ t⋆ − u⋆`,
  `err(φ⋆) ≤ ε`, `t⋆ − u⋆ ≤ osc(f⋆) ≤ 2`; and under `TwoSided54 φ P Q c₁ c₂ ε₀`: `‖φ⋆‖ ≤ c_V⁻¹ε^{−1/4}`, `c_Vε^{1/4} ≤ t⋆ − u⋆`, and
  `t⋆ − u⋆ ≤ c₂(2ε)^{5/4}/ε` when `2ε ≤ ε₀`. Printed S4 :1134-1143 ("By Proposition 5.10(iii), `osc(φ⋆) ≤ 1`, `‖φ⋆‖_ℋ = 1/g⋆` and `L(φ⋆) − α =
  E_Pψ⋆ − E_Qψ⋆ − α = V(ε)/g⋆ ≤ ε` (S4.9) … So `g⋆ ≥ V(ε)/ε`, `‖φ⋆‖_ℋ ≤ c_V^{−1}ε^{−1/4}`, `err(φ⋆) ≤ ε`, and `g⋆ ≤ osc(f⋆) ≤ 2`"), S4 :1343-1344
  ("the fitted gap is of the order `ε^{1/4}` of `g⋆`"). Faithful; encoding: the printed objects in 31tr's (Pr) encoding; "the order
  `ε^{1/4}` of `g⋆`" as the two-sided bound `c_Vε^{1/4} ≤ g⋆ ≤ c₂2^{5/4}ε^{1/4}` (for `2ε ≤ ε₀`).
* Y12 `lap_compare`: (Lap σ, sep), `α⋆ < 1`, `TwoSided54`, `0 < ε < α⋆`, the population objects at `α = α⋆ − ε` and the fitting setting at `α`.
  With `Δ(g) = L̃(wit φ g) − L(wit φ g)`, `V = V(ε)`, `D̄̂ = (1−α)D̂`, `T̂ = err(φ̂)`, `y = V + (t⋆−u⋆)Δ(φ⋆)`, `e = E_Pψ̂ − E_Qψ̂ − α`
  (`ψ̂ = ramp f̂ t̂ û`): (i) `e = ε − T̂`, `e + Δ(φ̂) = D̄̂‖φ̂‖`, `y ≤ D̄̂` and `‖φ̂‖y + T̂ ≤ ε + Δ(φ̂)`; (ii) if `κ₀ε − |Δ(φ⋆)| − Δ(φ̂) > 0`, then
  `e ≥ κ₀ε − |Δ(φ⋆)| − Δ(φ̂)`; (iii) if `|Δ(φ⋆)| ≤ κ₀ε/4`, then `y ≥ V/2 ≥ c_Vε^{5/4}/2`. Printed Lemma S4.22 (S4 :1145-1155). Faithful; every
  `ε ∈ (0, α⋆)` (both cases `ε < ε₀/2` and `ε ≥ ε₀/2` of the proof); every `σ > 0`. The proof's supporting-slope sentence is 31tr T40(i-2).
* Y13 `lap_dev` (`σ = 1`, as printed): `H` complete, `IsLaplaceFeature 1 φ`, probabilities `P, Q` on ℝ, `n, m ≥ 1`, `c ≥ log 8` with
  `IntervalEvent P x c` and `IntervalEvent Q y c` (one parameter for both), `K ≥ 1`, any `x₀`, any `g` with `osc(wit φ g) ≤ 1`,
  `N = max(‖g‖, ½)`, `Δ = L̃(wit φ g) − L(wit φ g)`: (a) `|Δ| ≤ a′ + ϖ′N^{1/2} + bN` (`a′ = devA′`, `ϖ′ = devG′`, `b = devB`, with
  `π_K = (P+Q)({|z−x₀| > K})`); (b) for every `p, q, ℓ₀, r⋆, c⋆, p̄` with `IsCross`, `0 < p x₀`, `CondR p q x₀ r⋆ c⋆` and `p + q ≤ p̄` on
  `[x₀−r⋆, x₀+r⋆]`: `err(wit φ g) > 0` and `|Δ| ≤ a + ϖN^{1/2}T^{3/10} + bN` (`a = devA`, `ϖ = devG`, `T = err(wit φ g)`). Printed Lemma S4.25 (S4
  :1227-1240, with `A₀ = 4 + 2√(2p̄) + 4(c⋆r⋆)^{−1/2}`, `A₁ = 2{(2√2p̄)^{1/2} + 2^{1/5}(2√2/(c⋆r⋆))^{1/2}}`). Faithful; encodings: the events
  of Lemma S4.23 as `IntervalEvent` at a common `c`, "under (5.1)" with the laws of Theorem 5.11(i) without the tail, `p̄` any bound, every
  representer (D4); `T > 0` is the printed first step of (b) (S4 :1252-1255), stated as a conjunct; deterministic on the events, for every
  `g` at once (the data-dependent `φ̂` included). Generalisations: no hypothesis on the laws in (a), any `x₀`, no separability.
* Y14 `own_ramp`: any measurable space, probabilities `P, Q`, measurable `ψ` with values in `[0,1]`, `a_o, b_o ≥ 0`, `a_o + b_o < 1`, with
  `ϱ(s) = min{1, max{0, (s − a_o)/(1 − a_o − b_o)}}`: `L(ψ) − max(a_o, b_o)err(ψ)/(1 − a_o − b_o) ≤ L(ϱ ∘ ψ)`. `lap_own`: (Lap σ, sep), any
  probabilities `P, Q` on ℝ, the fitting setting at `α`, `D̄ = (1−α)D̂`: for `û ≤ ũ < t̃ ≤ t̂`, with `a_o = (ũ−û)/(t̂−û)`, `b_o = (t̂−t̃)/(t̂−û)`:
  `a_o + b_o < 1`, `ramp f̂ t̃ ũ = ϱ ∘ ramp f̂ t̂ û`, and `L(ramp f̂ t̂ û) − max(a_o,b_o)err(ramp f̂ t̂ û)/(1−a_o−b_o) ≤ L(ramp f̂ t̃ ũ)`; and for
  genuine own-term quantiles `t̃` (of `ownX` at `1−α`) and `ũ` (of `ownY` at `α`): `û ≤ ũ`, `t̃ ≤ t̂`, `a_o ≤ 1/(mD̄ĝ)`, `b_o ≤ 1/(nD̄ĝ)`. Printed
  Lemma S4.26 (S4 :1277-1283). Faithful; `own_ramp` is the general inequality behind the printed one (any `[0,1]`-valued `ψ`, any laws).
* Y15 `lap_fitted` (`σ = 1`, as printed): (Lap 1, sep), `IsCross`, `0 < p x₀`, `TwoSided54 φ P Q c₁ c₂ ε₀`, `α⋆ < 1`, samples with `n, m ≥ 1`
  and no `x_i = y_j`, `c ≥ log 8`, `K ≥ 1`, `IntervalEvent P x c`, `IntervalEvent Q y c`: (case (i)) for every `r⋆, c⋆, p̄` with `CondR` and
  `p + q ≤ p̄` on `[x₀−r⋆, x₀+r⋆]`, every `ε` with `ε_fit^{(i)} ≤ ε < α⋆` (`epsFitI` at `κ₀, c_V`, the constants `devA, devG, devB` of Lemma
  S4.25(b) and `n∧m`), every exact minimizer at `α⋆ − ε`: every `GenuineCuts` pair `(t, u)` has `u < t` and `κ₀ε/2 ≤ E_P ramp − E_Q ramp −
  (α⋆−ε)`; and `c_Vε^{1/4}/24 ≤ t̂ − û`, and `t̂ − û ≤ V(2ε)/ε` when `2ε ≤ α⋆`; (case (ii)) for every `ε` with `ε_fit^{(ii)} ≤ ε < α⋆` (`epsFitII`
  at `devA′, devG′, devB`), every minimizer and every `GenuineCuts` pair: `u < t` and the same excess bound. Printed Proposition S4.27 (S4
  :1293-1308: "On the events of Lemma S4.23 for `P̃` and `Q̃` with a common `x ≥ log 8`, and with the constants of Lemma S4.25 for the sizes
  `n′, m′`, put, in case (i) of Theorem 5.11, `ε_fit = max{…}` … At every level `α = α⋆−ε ∈ (0, α⋆)` with `ε ≥ ε_fit`, the ramp fitted on `P̃, Q̃`
  with genuine-quantile cut points, plain or own-term, has cut points that do not cross and `E_Pψ − E_Qψ − α ≥ κ₀ε/2`") and S4 :1342-1344
  ("The proof also gives `c_Vε^{1/4}/24 ≤ ĝ ≤ V(2ε)/ε` in case (i) when `2ε ≤ α⋆`"). Faithful; encodings: case (i) of Theorem 5.11 as `CondR`
  with `p̄`, the sizes `n′, m′` as `n, m`, genuine-quantile cuts through `GenuineCuts` (D2); declared: the lower gap bound is stated without
  "when `2ε ≤ α⋆`" (the qualifier attached to the upper bound only, which needs Lemma S4.20 at `α⋆ − 2ε`; stronger if the printed qualifier is
  read on both), and in case (ii) `IsCross` and `0 < p x₀` are assumed (the printed context; not used by (ii), critic v1 note). "No bound on the
  variation of the fitted ramp is needed" is a remark on the proof (declared).
  `lap_fitted_fraction`: the hypotheses of `lap_fitted`, case (i)'s or case (ii)'s condition on `ε` (a disjunction), `ε < α⋆`, an exact minimizer
  at `α⋆ − ε`, a `GenuineCuts` pair `(t, u)`, and the population objects at `α⋆ − ε`: `(κ₀/2)(E_Pψ⋆ − E_Qψ⋆ − (α⋆−ε)) ≤ E_Pψ − E_Qψ − (α⋆−ε)`
  for the fitted ramp `ψ = ramp f̂ t u`. Printed main :290-291 ("Comparing this ratio with the population path at two levels shows that the
  fitted ramp keeps a fixed fraction of the excess of the population ramp (Proposition S4.27)") and S4 :1034-1036. Faithful; "a fixed fraction"
  is `κ₀/2`, which depends only on `α⋆, c₁, c₂, ε₀`.
* Y16 `lap_bets`: any measurable space, probabilities `P, Q`, a run `R` with `R.IsAdmissible α (1/2)` and the fraction bounds (`λ ≤ lamHi` always,
  `λ ≥ lamLo` on batches with a ramp, at `λ_max = ½`, `L_δ = log(1/δ)`, floor `v²_min`), `IsGrid α`, `J ≥ 1`, `δ, η ∈ (0,1)`, `v²_min ∈ (0,4]`,
  `h₀ > 0` with `GapsGe α h₀`, `ε > 0`, `N ≥ 1`, a measurable `E` with `P(Eᶜ) ≤ η/2`, `ϱ ≥ T_bet(J_ε)` (the frozen `Tbet` at `Δ_φ = ½`,
  `J_ε = Jeps J ε h₀`), and on `E`, at every grid level `α_j ≤ α⋆ − ε`, every pair `k` has a ramp with `Δ_k = E_P g_b − E_Q g_b ≥ α_j +
  ϱ(α⋆ − α_j)/ε`: then `P{α̂ < a_ε} ≤ η` with `a_ε = gridFloor α (α⋆ − ε)`. Printed S4 :1037-1038 ("and the bets are those of Theorem S4.3") and the
  betting paragraph of the proof S4 :1354-1366 ("… bounds the probability that `𝓔_fit` holds and `H_{0,α_j}` is not rejected by … and the
  summation over levels in the proof of Theorem S4.3, with `γ = 1`, bounds the sum by `η/2`. By (eq:downclosed), `P(α̂ < a_ε) ≤ η`").
  Not a numbered result: the betting half of the proof of Theorem S4.3 with an arbitrary fit event, isolated as a claim (critic: acceptable,
  it gives the printed sentence a target). Faithful; generalisation: no rule for the ramps is assumed (only admissibility and the fraction
  bounds).
* Y17 `lap_rescale`: `H` any real inner-product space, `σ > 0`, `IsLaplaceFeature σ φ`, `φ_σ(u) = φ(σu)`: `IsLaplaceFeature 1 φ_σ`; for all samples,
  weights and `α`: `IsQPMin φ α x y w v ⟺ IsQPMin φ_σ α (x/σ) (y/σ) w v`, equal `qpVal`, `fitF φ … z = fitF φ_σ … (z/σ)`, equal `ownX`, `ownY`;
  and for every `IsCross P Q p q x₀ ℓ₀`, with `P_σ = P.map(·/σ)`, `p_σ(u) = σp(σu)` (same for `Q`): `IsCross P_σ Q_σ p_σ q_σ (x₀/σ) (σ²ℓ₀)`,
  `TV(P_σ,Q_σ) = TV(P,Q)`, `D_α(P_σ,Q_σ)` for `φ_σ` equals `D_α(P,Q)` for `φ` at every `α`, `ExpTailWith … C′ → ExpTailWith … (max(C′, C′/σ))`,
  the same for `SumTail`, `CondR p q x₀ r⋆ c⋆ → CondR p_σ q_σ (x₀/σ) (min(1, r⋆/σ)) (c⋆σ)`, the `p̄` bound becomes `σp̄` on the rescaled interval,
  and `sampleLaw P_σ Q_σ n m` is the image of `sampleLaw P Q n m` under the rescaling. Printed S4 :1038-1039 ("Rescaling the data by `1/σ` leaves
  the witness values, cut points and ramps unchanged and preserves the hypotheses with rescaled constants, so we take `σ = 1`"). Faithful;
  encoding: the witness values, cut points (any rule of the witness or own-term values) and ramps through the QP objects; `TwoSided54` with the
  same `c₁, c₂, ε₀` follows from the `D_α` and `TV` conjuncts; `p_σ(x₀/σ) = σp(x₀)` is arithmetic; the transport of a run (`IsGenuineRun`,
  `IsDefaultRun`, `alphaLo`) is a route lemma of Y18, not claimed (D9).

**The theorems.**
* Y18 `laplace_const_i` (G): for all `σ > 0`, `α⋆ ∈ (0,1)`, `0 < c₁ ≤ c₂`, `ε₀ ∈ (0, α⋆]`, `C′ > 0`, `c⋆ > 0`, `r⋆ ∈ (0,1]`, `p̄ ≥ 0` there is `C > 0`
  such that for every (Lap σ, sep), every `P, Q, p, q, x₀, ℓ₀` with `IsCross`, `0 < p x₀`, `ExpTailWith P Q x₀ C′`, `TV(P,Q) = α⋆`,
  `TwoSided54 φ P Q c₁ c₂ ε₀`, `CondR p q x₀ r⋆ c⋆` and `p + q ≤ p̄` on `[x₀−r⋆, x₀+r⋆]`, and all `J, n, m, α, δ, v²_min, η, h, R` with the run
  hypotheses: with probability `≥ 1−δ−η`, `α⋆ − h − C[(log(n∨m))^{1/4}L^{1/2} + v²_min⁻¹(√log(1/δ) + √log(2J/η))]/√(n∧m) ≤ α̂ ≤ α⋆`.
  `laplace_const_ii` (G): for all `σ > 0`, `α⋆ ∈ (0,1)`, `0 < c₁ ≤ c₂`, `ε₀ ∈ (0, α⋆]`, `C′ > 0` there is `C > 0` such that the same holds with
  `SumTail P Q x₀ C′` in place of `ExpTailWith`, `CondR` and `p̄`, and the bound `C[{(log(n∨m))^{1/2}L/(n∧m)}^{4/9} + v²_min⁻¹(√log(1/δ) +
  √log(2J/η))/√(n∧m)]`. `laplace_const_pr_i` (Pr): for every `σ > 0` and every `P, Q, p, q, x₀, ℓ₀, r⋆, c⋆` with (L55) and `CondR`, there is
  `C > 0` such that for every (Lap σ, sep) and all `J, n, m, α, δ, v²_min, η, h, R` with the run hypotheses the bound of (i) holds with
  probability `≥ 1−δ−η`. `laplace_const_pr_ii` (Pr): the same with (L55) and `SumTail P Q x₀ C′` and the bound of (ii). Printed Theorem S4.19 (S4
  :989-1018), with the dependence list "Here `C` depends only on `σ` and on the pair through `α⋆`, the constants of Proposition 5.5 with `s = 1`, the
  tail constant `C′` (that of `P+Q` in (ii)), and, in (i), `c⋆`, `r⋆` and the supremum of `p+q` on `[x₀−r⋆, x₀+r⋆]`, which is finite once `r⋆` is
  small enough". Faithful; (G) is the literal reading of the dependence list (its quantifier lists are exactly the printed ones), (Pr) the
  theorem under its own hypotheses with `∃ C` before `H, φ` (D3, B1); encodings: the run class, `v_min^{−2}` as `v²_min⁻¹`, the mesh as any
  bound `h`, the grid in `(0,1)` (Lemma S4.21 needs `α > 0`), the constants of Prop 5.5 as the hypothesis `TwoSided54` in (G); in (Pr)(ii) the
  `|P−Q|` tail of (L55) is kept beside the `P+Q` tail (implied by it with the same `C′`). The guards on the outer constants of (G) are implied
  by the inner hypotheses (no pair satisfies them otherwise), except `σ > 0`, which is printed.
* Y19 `laplace_rate_i`: for every `σ > 0` and every `P, Q, p, q, x₀, ℓ₀, r⋆, c⋆` with (L55) and `CondR`, there is `C > 0` such that for every
  (Lap σ, sep) and all `J, n, m, α, δ, v²_min, η, h, R` with the run hypotheses: with probability `≥ 1−δ−η`, `α⋆ − h − C(L^{3/4}/√(n∧m) + B) ≤ α̂
  ≤ α⋆`. `laplace_rate_ii`: the same with (L55) and `SumTail P Q x₀ C′`, and `L^{2/3}(n∧m)^{−4/9}` in place of `L^{3/4}(n∧m)^{−1/2}`. Printed Theorem
  5.11 (main :293-318: "Let `P, Q` satisfy the hypotheses of Proposition 5.5 on the laws, let `n∧m ≥ 10`, and compute `α̂` as in Theorem 5.7, on
  a grid of `J` levels in `(0,1)` with mesh `Δ_𝒢` below `α⋆`, with the kernel `e^{−|x−y|/σ}`, `σ > 0` fixed in advance, an exact minimizer of (2.10)
  at each level, and, in place of the one-rank tolerance (S3.4), cut points that are genuine empirical quantiles of the witness values, computed
  with or without each point's own term in (2.11) … (i) If for some `r⋆ ∈ (0,1]` and `c⋆ > 0` (5.1) holds, then with probability at least
  `1−δ−η`, `α⋆ − Δ_𝒢 − O(L_{n,m}^{3/4}(n∧m)^{−1/2} + B_{n,m}) ≤ α̂ ≤ α⋆`. (ii) If instead `(P+Q)({x : |x−x₀| > t}) ≤ C′e^{−t/C′}` for all `t > 0`,
  the same holds with … The constant in the `O` depends only on `σ` and on the pair, as stated in Theorem S4.19"), S4 :985-987 (the two
  inequalities that absorb the constants). Faithful; the `O(·)` as a constant `C` chosen after `σ` and the pair (and the constants `r⋆, c⋆` or
  `C′` of the hypothesis, functions of the pair by choice) and before the feature map, the sample sizes, the grid, `δ, η` and `v²_min`.
  `laplace_rate_improves`: (c1) for every `C > 0`, `δ, η ∈ (0,1)`, `v²_min > 0`, `J ≥ 1` there is `C₀ > 0` with, for all `n, m` with `n∧m ≥ 10`,
  `C(L^{3/4}/√(n∧m) + B) ≤ C₀(log(n∨m))^{3/4}/√(n∧m)` and `C(L^{2/3}(n∧m)^{−4/9} + B) ≤ C₀(log(n∨m))^{2/3}(n∧m)^{−4/9}`; (c2) for every `k ≥ 1`,
  every real `C`, `δ, η ∈ (0,1)`, `v²_min > 0`, `J ≥ 1` and `ε > 0` there is `N₀` such that for `n∧m ≥ N₀` and `n∨m ≤ (n∧m)^k` both bounds are at
  most `ε(n∧m)^{−2/5}`. Printed main :240-243 ("Under the hypotheses of Proposition 5.5, Theorem 5.7 guarantees at least the rate
  `(n∧m)^{−2/(2s+3)}`, `(n∧m)^{−2/5}` for the Laplace kernel, which Theorem 5.11 improves to `(n∧m)^{−1/2}`, up to powers of `log(n∨m)`, under
  one more condition, for samples of comparable size"; the qualifier restored at `1fbc8df`, critic correction #7). Faithful under D15: (c1) is
  "`(n∧m)^{−1/2}` up to powers of `log(n∨m)`" for fixed `δ, η, v²_min, J`; (c2) is "improves", `o((n∧m)^{−2/5})`, the order of Theorem 5.7's
  Laplace guarantee (31tq Q25(b), Q27(b)), for samples of comparable size read as `n∨m ≤ (n∧m)^k`; "under one more condition" is (5.1) or the
  `P+Q` tail of Y19 (the claim is about the printed bounds, for any constant). Without a size condition "improves" fails (`m = e^n`).
* Y22 `laplace_rate_grid`: for every `σ > 0`, every pair with (L55) and `CondR`, and fixed `δ, η ∈ (0,1)`, `v²_min ∈ (0,4]`, there is `C > 0` such
  that for every (Lap σ, sep), all `n, m` with `n∧m ≥ 10`, every grid in `(0,1)` with `J ≤ n∧m` levels and mesh below `α⋆` at most
  `(n∧m)^{−1/2}`, and every run with `IsGenuineRun ∧ IsDefaultRun`: with probability `≥ 1−δ−η`, `α⋆ − C L^{3/4}/√(n∧m) ≤ α̂ ≤ α⋆`. Printed abs
  :11-13 ("for densities that cross once the error is of order `(n∧m)^{−1/2}` up to logarithmic factors on a grid of that mesh when the likelihood
  ratio stays away from one off the crossing"), §1 :84-88, main :8-10 ("recovers the parametric rate, up to logarithmic factors, on the line
  with the Laplace kernel, for densities that cross once and under a condition on their likelihood ratio (Theorem 5.11)"), main :322-323 ("a
  kernel bound that ignores the order of the line, and returns the set, attains this rate up to logarithmic factors"). Faithful under the
  declared readings: "densities that cross once" as Proposition 5.5's hypotheses, "the likelihood ratio stays away from one off the crossing"
  as (5.1) (Y8(b)), "a grid of that mesh" as mesh `≤ (n∧m)^{−1/2}` with at most `n∧m` levels (the bound on `J` is a reading: the abstract bounds
  no `J`, and `B` grows with `J`; the grid of Corollary 5.9 is one; any polynomial bound on `J` gives the same order); `C` depends on `σ`, the
  pair, `δ, η, v²_min`. §1's "matches it" is the same claim (critic: correct as printed after "up to logarithmic factors"); "a one-sided
  Kolmogorov–Smirnov bound attains this rate there" is 31tr T28(b); "the witness clips itself" is Y10(b) (31tr T42(a) for the population
  witness).

**The local lower bound (Lemma S4.28 and its sentences).**
* Y20 `lap_local`: probabilities `P, Q`, (L55) with `ExpTailWith P Q x₀ C′`, `CondR p q x₀ r⋆ c⋆`, `0 < r ≤ r⋆`, `p, q` continuous and positive on
  `[x₀−2r, x₀+2r]`, `A₁ = (x₀+r, x₀+2r)`, `B₁ = (x₀−2r, x₀−r)`, `π = min{P(A₁), P(B₁)}`, any `δ`: `π > 0`, and for every `h ∈ [0,1]`, with
  `p_h = p{1 + hπ1_{A₁}/P(A₁) − hπ1_{B₁}/P(B₁)}` and `P_h = p_h·Leb`: `p_h ≥ 0`; `P_h(S) = P(S) + hπ{P(S∩A₁)/P(A₁) − P(S∩B₁)/P(B₁)}` for measurable `S`;
  `P_h` is a probability measure with `TV(P_h,Q) = α⋆ + hπ` and `TV(P_h,P) = hπ`; `IsCross P_h Q p_h q x₀ ℓ₀`, `0 < p_h(x₀)`,
  `ExpTailWith P_h Q x₀ (C′ + 2r + 2e)`, `CondR p_h q x₀ r⋆ (c⋆/2)`; for every `p̄` with `p + q ≤ p̄` on `[x₀−r⋆, x₀+r⋆]`, `p_h + q ≤ 2p̄` there; and for
  all `n, m`, every probability `ρ` on any `Ξ` and every measurable `T` of the samples and `Ξ` with `P_{P,Q}(T > α⋆) ≤ δ`:
  `P_{P_h,Q}{TV(P_h,Q) − T ≥ hπ} ≥ 1 − δ − h(nπ)^{1/2}`. `lap_local_Q`: the same for the second sample (`Q` moved from `A₁` to `B₁`, `q_h =
  q{1 + hπ′1_{B₁}/Q(B₁) − hπ′1_{A₁}/Q(A₁)}`, `π′ = min{Q(A₁), Q(B₁)}`, `TV(P,Q_h) = α⋆ + hπ′`, `TV(Q_h,Q) = hπ′`, `IsCross P Q_h p q_h x₀ ℓ₀`, the
  tail, `CondR (c⋆/2)`, `p + q_h ≤ 2p̄`, and `1 − δ − h(mπ′)^{1/2}`). Printed Lemma S4.28 (S4 :1386-1400: "Then `P_h` is a probability measure,
  `TV(P_h,Q) = α⋆ + hπ`, and `(P_h,Q)` satisfies the hypotheses of Theorem 5.11(i), with `c⋆/2`, `2p̄` and a tail constant depending only on `C′` and
  `r`. Every `α̃`, a measurable function of the samples and of an independent randomization, with `P_{P,Q}(α̃ > α⋆) ≤ δ` satisfies … The same
  holds for the second sample …"). Faithful; encodings: `P_h` by its density with the printed identity as a conjunct; the hypotheses of Theorem
  5.11(i) for `(P_h,Q)` with the same `x₀, ℓ₀, r⋆` and the explicit tail constant `C′ + 2r + 2e`; `2p̄` conditional on a bound `p̄` (critic B2:
  no finite `p̄` is assumed); the conjunct `TV(P_h,P) = hπ` is added (used by Y21); validity is asked at `(P,Q)` only.
* Y20(c) `lap_local_c`: the hypotheses of `lap_local`, `δ ∈ [0,1)`, `n, m` with `nπ ≥ 1/4` and `h = (1−δ)/(2(nπ)^{1/2})`: `h ∈ [0,1]` and every valid `T`
  (as above) has `P_{P_h,Q}{TV(P_h,Q) − T ≥ ½(1−δ)(π/n)^{1/2}} ≥ (1−δ)/2`. Printed S4 :1416-1417 ("With `h = (1−δ)/{2(nπ)^{1/2}}`, which is at most
  `1` once `nπ ≥ 1/4`, a valid lower bound falls short at `(P_h,Q)` by at least `½(1−δ)(π/n)^{1/2}` with probability at least `(1−δ)/2`").
  Faithful.
* Y20(d) `lap_local_d`: for every `σ > 0`, the hypotheses of `lap_local` (without `δ`) and every `h ∈ [0,1]` there are `c₁, c₂, ε₀` with
  `TwoSided54 φ P_h Q c₁ c₂ ε₀` for every (Lap σ, sep). Printed S4 :1417-1418 ("The constants of Proposition 5.5 for `(P_h,Q)` exist, but we have
  not shown that they stay bounded uniformly in `h` …"). Faithful; the constants before `H, φ` (B1); the second half is declared open.
* Y20(e) `lower2pt_not_cross`: for probabilities `R, P₀, Q₀` on ℝ concentrated on pairwise disjoint measurable sets and every `b, c ∈ (0,1)`, there
  are no `p, q, x₀, ℓ₀` with `IsCross ((1−b)R + bP₀) ((1−c)R + cQ₀) p q x₀ ℓ₀ ∧ 0 < p x₀`. Printed S4 :1383-1384 ("The pairs of Proposition 5.8 are
  separated and do not satisfy these hypotheses, so we perturb `P` away from `x₀` instead"). Faithful; generalisation: every pair of mixtures of
  Proposition 5.8's form (`Wave31tn.mixAt`, both `P_a, Q_a` and the perturbed `P_{a,h}`), and the failure already of `IsCross ∧ 0 < p x₀`, a part
  of "these hypotheses" (those of Theorem 5.11(i)).
* Y21 `local_rate`: for every pair with (L55) and `CondR` and every `δ ∈ [0,1)` there are `c, C > 0` and `N₀` such that for all `n, m` with
  `n∧m ≥ N₀` and every valid `T` (as above) there is a pair `(P′,Q′)` with densities `p′, q′` satisfying (L55) at the same `x₀, ℓ₀` and `CondR`
  for some `r⋆′, c⋆′`, with `TV(P′,P) + TV(Q′,Q) ≤ C(n∧m)^{−1/2}`, and `P_{P′,Q′}{TV(P′,Q′) − T ≥ c(n∧m)^{−1/2}} ≥ (1−δ)/2`. Printed S4 :1024-1026
  ("as Lemma S4.28 gives every valid lower bound an error of order `(n∧m)^{−1/2}` near each pair covered by (i) with a constant not shown to
  be uniform"), S4 :1383 ("Near every pair covered by part (i) no valid lower bound does better than `(n∧m)^{−1/2}`"). Faithful under D12:
  "near" as within `O((n∧m)^{−1/2})` in total variation, "covered by (i)" as (L55) and (5.1); the order "for every `T`, some nearby pair" is
  the printed sentence's (the route chooses the pair from `n, m` alone, before `T`, as Lemma S4.28 does: the first sample is perturbed when
  `n ≤ m`, the second otherwise); validity at `(P,Q)` only (stronger); "with a constant not shown to be uniform" declared (open).

**Readings, the simulated pairs and the paper's run.**
* Y23 `sims_condR`: `CondR` holds at `x₀ = 0` for some `r⋆, c⋆` for the densities of `N(1,1)` and `N(−1,1)`, and for `0.8φ₁ + 0.2φ₁(·−1.5)` and
  `0.8φ₁ + 0.2φ₁(·+1.5)` (`φ₁` the standard normal density, `gaussianPDFReal`). Printed S6 :157 ("For the shift `N(±1,1)` and the mixtures `0.8N(0,1)
  + 0.2N(±μ,1)` … which cross at `x₀ = 0`"), S6 :167-168 ("The split-sample bound was computed on the shift and the mixture with `μ = 1.5`, which
  satisfy (5.1)"). Faithful; that the pairs cross at `0` and satisfy Prop 5.5's hypotheses is 31tq Q28 (with these densities); "agrees with
  the rate", the slopes and the interpolated cuts (S4 :1029-1030) are numerical or scope (declared).
* Y24 `genuine_paperrun`: `H` complete, `φ : ℝ → H` strongly measurable with `‖φx‖ ≤ κ` (any feature map), `IsGrid α`, `∀ j, 0 < α_j`, `δ ∈ (0,1)`,
  `v²_min ∈ (0,4]`, `w₀ > 0`, any prior `v₀`, cut rules `qt`, `qu` that are genuine-quantile rules (31tr `IsGenuineQuantileRule`), boundaries
  `cx 1, cx 2` and `cy 1, cy 2` at the nearest integers to `n/4, n/2` and `m/4, m/2` (`NearestCuts`): every `IsPaperRun R φ α δ (1/2) v²_min w₀ v₀
  qt qu 2 cx cy` satisfies `IsGenuineRun R φ α δ (1/2) v²_min ∧ IsDefaultRun R`. `genuine_run_exists`: for the same `φ`, grid, `δ`, `v²_min`, all
  `n, m` and nearest-integer boundaries, some run is `IsPaperRun` at the printed rule (`lowQ`, `highQ`, `w₀ = 20`, `v₀² ≡ 1`, `λ_max = ½`) and is
  `IsGenuineRun ∧ IsDefaultRun`. Printed §4 :60-68 (the cut points are "the smallest `(1−α)`-quantile … their `⌈n_{<b}(1−α)⌉`-th order
  statistic, and the largest `α`-quantile …, the `(⌊m_{<b}α⌋+1)`-th … Each value is computed without the point's own term"), S3 :105-111 (genuine
  empirical quantiles of the own-term values), S3 :181-182 (Algorithm S1's cut points), §7 :20-22 ("The split-sample bound `α̂` is Algorithm S1
  of the supplement"). Faithful as a composition: the paper's run (31tr's `IsPaperRun`, certified and audited) is in the run class of Theorems
  5.11 and S4.19 (the own-term branch of `GenuineCuts`), and the printed run exists, which makes Y18–Y22 non-vacuous statements about the
  paper's procedure with a kernel fixed in advance and an exact minimizer (the runs' median-distance bandwidth and iterative solver are outside
  the theorem, as §4 :167-173 says, declared). Declared: `‖φx‖ ≤ κ` (aligned with 31tr T5; harmless, `‖φx‖ = 1` under `IsLaplaceFeature`).
  Generalisations: any bounded feature map, any genuine rules, any prior and `w₀ > 0` in (a).

**Proposition S4.8 (ii)–(iii).**
* Y25 `newrates_ii_exp`: for all `κ > 0`, `α⋆ < 1`, `c′ > 0`, `ε₀ ∈ (0, α⋆]`, `b > 0`, `η, δ ∈ (0,1)`, `v²_min ∈ (0,4]` and `c > 2c′` there is `n₀`
  such that for every measurable space `𝒳`, every complete separable `H`, strongly measurable `φ` with `‖φx‖ ≤ κ`, probabilities with `TV(P,Q) = α⋆`,
  every `ω` nondecreasing and nonnegative on `[0, α⋆]` with `ω(e) ≤ (1−α⋆+e)D_{α⋆−e}` on `[0, α⋆]` and `ω(e) ≥ exp(−c′/e)` on `(0, ε₀]`, every grid
  (`IsGrid`) with `1 ≤ J ≤ (n∧m)^b` levels, every run with `IsWitnessRun φ α δ (1/2) v²_min ∧ IsDefaultRun`, every `n∧m ≥ n₀` and every mesh bound
  `h`: with probability `≥ 1−δ−η`, `α⋆ − h − c/log(n∧m) ≤ α̂ ≤ α⋆`. Printed Proposition S4.8 (S4 :470-483: "Let Assumption 2.1 hold, let `α⋆ < 1`,
  compute `α̂` as in Theorem 5.7, and let `ω : [0,α⋆] → [0,∞)` be nondecreasing with `(1−α⋆+ε)D_{α⋆−ε}(P,Q) ≥ ω(ε)` for every `ε ∈ [0,α⋆]`. … (ii) If
  moreover `ω(ε) ≥ exp(−c′/ε)` for `0 < ε ≤ ε₀`, for some `c′ > 0` and `ε₀ ∈ (0,α⋆]`, and the grid has at most `(n∧m)^b` levels for a fixed `b > 0`, then
  for every `η ∈ (0,1)` and every `c > 2c′` there is `n₀`, depending on `c, c′, ε₀, b, η, δ, κ, α⋆` and `v²_min`, such that `P{α⋆ − Δ_𝒢 − c/log(n∧m) ≤
  α̂ ≤ α⋆} ≥ 1−δ−η` whenever `n∧m ≥ n₀`"). Faithful; `n₀` is chosen after exactly the printed list and before everything else (the laws, `ω`, the
  grid, the run, the sample sizes); generalisations: (A3) not assumed (as in Wave31to), any mesh bound; encoding: the run class of Theorem
  S4.3 (D3 of 31tq), which contains the paper's run (31tr T5); `κ > 0` is a harmless guard (`κ = 0` forces `D ≡ 0`, against the exponential
  margin).
* Y26 `newrates_iii_gauss`: for every `σ > 0`, every pair with (L55), `b > 0`, `η, δ ∈ (0,1)`, `v²_min ∈ (0,4]` and `c > π²σ²ℓ₀/4` there is `n₀` such that
  for every complete separable `H` and `φ : ℝ → H` with Gram `exp(−(x−y)²/(2σ²))`, every grid with `1 ≤ J ≤ (n∧m)^b` levels, every run with
  `IsWitnessRun ∧ IsDefaultRun`, every `n∧m ≥ n₀` and every mesh bound `h`: with probability `≥ 1−δ−η`, `α⋆ − h − c/log(n∧m) ≤ α̂ ≤ α⋆`. Printed S4
  :484-485 ("(iii) Under the hypotheses of Proposition 5.6, with a grid as in (ii) and no `ω` assumed, the conclusion of (ii) holds for every
  `c > π²σ²ℓ₀/4`"), main :243-246 ("Under those of Proposition 5.6 the margin guarantees at least the logarithmic rate `c/log(n∧m)` for every
  `c > π²σ²ℓ₀/4`, on grids with at most `(n∧m)^b` levels for a fixed `b` (Proposition S4.8 of the supplement), in both cases up to the mesh"), abs
  :9-10 ("… and a logarithmic rate for the Gaussian kernel"), §1 :82-83. Faithful; `σ` is here the Gaussian bandwidth of Proposition 5.6; `n₀`
  depends on the pair (through the `c′, ε₀` that Proposition 5.6 gives) and the printed constants, not on the feature map (31tq Q22 at one
  Gaussian feature map, transferred by 31tp L12 `gram_mmd`); `κ = 1`. Decision D6 (stated in 31tu): the route is Y25 with 31tq Q22 `newgauss` and
  `ω(e) = (1−α⋆+e)D_{α⋆−e}`, shorter than the printed route through `ω_ℋ` (S4 :736-745), a different proof of the same statement.

## Junk-value audit
Every `rpow` base is positive or nonnegative where read: `ε^{5/4}`, `ε^{±1/4}`, `(2ε)^{5/4}` (`ε > 0`); `(ε₀/α⋆)^{5/4}`, `(ε₀/2)^{5/4}`, `2^{5/4}`,
`2^{1/5}` (positive); `K^{1/4}`, `K^{1/2}` (`K ≥ 1`); `N^{1/2}` (`N ≥ ½`); `T^{3/10}` (`T > 0` a conjunct of Y13(b)); `(c⋆r⋆)^{−1/2}`,
`(2√2/(c⋆r⋆))^{1/2}` (`c⋆r⋆ > 0`); `(2√2p̄)^{1/2}` (`p̄ ≥ 0`, forced by `p + q ≥ 0` on a nonempty interval, or a hypothesis in (G)); the
`ε_fit` terms `(300b/(κ₀c_V))^{4/5}`, `(2/c_V)^{20/33}ϖ^{40/33}`, `(1920/(κ₀c_V²(n∧m)))^{2/3}`, `(60ϖ′/(κ₀√c_V))^{8/9}`, `(156b/(κ₀c_V))^{4/5}`,
`(576/(κ₀c_V²(n∧m)))^{2/3}` (`b, ϖ, ϖ′ ≥ 0`, `κ₀, c_V > 0` by Y7 under `TwoSided54` and `α⋆ < 1`, `n∧m ≥ 1`); `(log(n∨m))^{1/4, 1/2, 2/3, 3/4}`,
`(log((n∨m)/η))^{1/2, 2/3, 3/4}` and the bracket `{…}^{4/9}` (positive bases: `n∨m ≥ 10`, `η < 1`); `(n∧m)^{−4/9}`, `(n∧m)^{−2/5}` at `n∧m ≥ 10` or
`n∧m ≥ N₀` with `N₀` chosen by the prover. `log` only of arguments `> 1` in the read range: `log(1/δ)`, `log(2J/η)` (`J ≥ 1`, `η < 1`),
`log(2(n+1)²/η′)`, `log(n∨m)`, `log((n∨m)/η)` (`n∨m ≥ 10`), `log 8`; `c/log(n∧m)` in Y25, Y26 only for `n∧m ≥ n₀` with `n₀` chosen by the
prover (a junk `c/log 1 = 0` at a small `n∧m` would make the claim harder, not easier: the claim is `∃ n₀ ∀ n∧m ≥ n₀`); likewise the
`∃ N₀` claims Y19(c2), Y21 read the true powers for large `n∧m`. Divisions: by `‖g‖` with `g ≠ 0` (Y9, Y10(i)); by `t̂ − û`, `t⋆ − u⋆` (positive
conjuncts, Y10, Y11, and in Y12, Y14 through Y10); by `n(1−α)D̂`, `m(1−α)D̂` (`D̂ > 0`, `α < 1`, `n, m ≥ 1`); by `1 − a_o − b_o > 0`; by `P(A₁)`,
`P(B₁)`, `Q(A₁)`, `Q(B₁)` (positive: `π > 0`, resp. `π′ > 0`, is a conjunct); by `2(nπ)^{1/2}` with `nπ ≥ 1/4`; by `ε > 0`, `c⋆r⋆ > 0`, `σ > 0`,
`κ₀`, `c_V`, `√c_V`, `s2 = v²_min > 0`, `√(n∧m) > 0`, `n, m ≥ 1` (in `sDev`, `rDev`, `IntervalEvent`), `2σ`, `2σ²`. `IsLaplaceFeature σ φ` at
`σ = 0` reads `e^{−|x−y|/0} = e^0 = 1` (the constant kernel, Lean's `x/0 = 0`), and at `σ < 0` it has no feature map (`⟪φx,φy⟫ ≤ 1 <
e^{|x−y|/|σ|}`); every claim with a general bandwidth assumes `σ > 0` (the printed `σ > 0`), and Y13, Y15 are at `σ = 1`. `sSup`/`sInf`:
`oscFn`, `⨆ f`, `⨅ f` only of bounded functions (`|wit φ g| ≤ ‖g‖κ`, a boundedness hypothesis in Y6, `fitF` bounded); no new `sInf ∅`/`sSup ∅`
(`alphaLo`, `gridFloor`, `genInv` frozen elsewhere). `ordStat` only at ranks in `[1, n]`: `⌈n(1−α)⌉ ≥ 1` and `⌊mα⌋ + 1 ≤ m` for `α ∈ (0,1)`, and the
ranges of Y10(d), (j) lie in `[1, n]`, `[1, m]`; `tHat`, `uHat` are read at `α = α⋆ − ε ∈ (0,1)` in Y12, Y14, Y15. `deriv` is read in `IsH1`,
`h1Laplace` and Y3(c) for locally absolutely continuous functions, where it is the a.e. derivative (Lean's `deriv = 0` at non-differentiable
points is a null set). `ENNReal`: `levelCount` and `eVariationOn` may be `∞` (both sides of Y1 in `[0,∞]`, the printed convention);
`ENNReal.ofReal` of a negative `1 − δ − η` is `0` (a true, weaker bound); `ofReal(C′e^{−t/C′})`, `ofReal(‖g‖²)` of nonnegative reals; in Y5 the
variation bound `ofReal V` with `V ≥ 0`. `.real` only of finite measures (`P`, `P+Q`, `μ`, the sample laws and their products). `Measure.map` only of
the continuous maps `x ↦ x/σ` and the coordinatewise rescaling (Y17). Bochner integrals: bounded measurable integrands on finite measures
(ramps, witnesses, `h ∈ [0,1]`), and in Y6 the products `(M−f)(p−q)₊` with `f` bounded and `p, q` integrable densities. `bumpDens` is read only for
`h ∈ [0,1]`, where `p_h ≥ 0` is a conjunct. Vacuity: every hypothesis set has a witness — (Lap σ, sep) for every `σ > 0` (31tp L15 with 31tq
Q7(a)); (L55) by the shift and the mixtures (31tq Q28) and `CondR` for the shift and the `μ = 1.5` mixture (Y23); `TwoSided54` for every pair of
Theorem 5.11(i) with the Laplace kernel (Y20(d) at `h = 0`, where `P_0 = P`, a hand instantiation; also the route lemma `laplace_twoSided`);
`IntervalEvent` (Y4(a)); exact minimizers (the capped quadratic program over a compact set; 31tr T3's measurable selection); no `X` equal to a `Y`
(Y4(c), almost surely); the run class of Y18–Y22 at every bounded feature map (Y24(c)), and that of Y25, Y26 (31tr T4, T5); the exponential
margin of Y25 (31tq Q22(c) under Prop 5.6's hypotheses); Y16's hypotheses (e.g. on the event where no grid level is below `α⋆ − ε`); Y20(e)'s
pairs (31tn).

## Rows only / not claimed
* Heuristic or outline sentences, declared (§E): §1 :83-84 ("because a flat path has flat tangents"; the claim half is Y19(c)); S4 :1020-1021
  ("Its constant degenerates when `c⋆` is small, as for narrow contaminations on a wide core"; visible in `A₀, A₁ ∝ (c⋆r⋆)^{−1/2}`, Y13); S4
  :1032-1038 (the outline of the proof; its content is Y10(b), (i), Y12, Y15, Y16); S4 :1184-1186 (outline; the uniformity is built into Y13);
  the opening sentence of the proof of Lemma S4.24 (S4 :1216-1217); S4 :1344 ("no bound on the variation of the fitted ramp is needed").
* Meta sentences, declared: §1 :82-83's "with no lower bound proved to match"; main :246-249's "For the split-sample bound we prove no converse"
  and "for `τ^P` no converse is known" (the `τ^A` converse is 31tq Q25(c1), (c3), (e)); main :323-324's "but it is no reason to prefer the method on
  the line"; main :325-327 (the choice of the Laplace kernel in `ℝ^d`); main :327-328 (pointer to §S4.12); §4 :167-173 and S3 :155-158 ("describe
  the trend", "not usable"; the `v_min^{−2}` factor is in Y18); §7 :101; the supplement abstract :1-3 and the section overview S4 :4-7; S4
  :509-512 except the factor `(1−α⋆)^{1/γ}` (31tr T25); S4 :978-980's Green-function sentence; S6 :173-174's "we prove no rate for it".
* Open, declared: §8 :22-24 (whether the kernel bounds attain the rate, whether Theorem 5.11(i) holds without (5.1), other kernels, `ℝ^d`, data-driven
  kernels); S4 :1021-1022 (the survival of self-clipping under an inexact solve; Y10 and Y18 assume exact minimizers); S4 :1022-1026's "whether
  `C` is uniform over a natural class is open, and with it a minimax statement" and "with a constant not shown to be uniform"; S4 :1418-1419 ("we
  have not shown that they stay bounded uniformly in `h`, which a minimax statement over a class containing these pairs would need").
* Scope, declared: main :324-325's "where only part (ii) applies"; §7 :20-22's median-distance bandwidth (outside Theorem 5.11, §4 :167-173);
  S4 :1029-1030's interpolated cut points ("which the theorem does not cover"; that they lie within one rank is the certified `numpy_bracket`).
* Numerical, declared: S4 :1029-1030 ("agrees with the rate", the geometric grid); S6 :157-165 (the path computations; the two bounds are 31tq
  Q19/Q20 and the certified `newapproxgen`); S6 :167-178 (the slopes).
* Citations, declared: S4 :1026-1028's minimax rate for `L₁`-type functionals (the `ℝ^d` half of that sentence is 31tq Q6 with Q12); Wendland Thm
  10.12 (S4 :1040-1041), whose conclusion is proved (Y3; the transform is 31tq Q7(a)); Banach (1925) (S4 :1221), proved (Y1).
* Author item (P6, open): the AI statement bm :11-15 still names only "Propositions 5.5, 5.6 and S4.8(iii), and the results of the supplement
  behind them" as exempt; its wording is the author's call (source §G).
* Owned elsewhere (certified, audited): §1 :72-79 (31tr T40–T41, `pathconvex`, Theorem 5.7 via 31tr T8); §1 :86-88's Kolmogorov–Smirnov half and
  main :320-322 (31tr T28 (a), (b)); §1 :88-91 and §7 :188-190 (31tr, Remark S5.5's Laplace sentence, T42's remark); §2 :48-50 (31tr T35); main
  :240-242's first half, abs :9-10's and §1 :82-83's polynomial halves (31tq Q25(b), Q27(b)); main :246-249's `τ^A` converse (31tq Q25); main
  :251-259, :271-286 (31tr T40–T42, 31tq Q26); main :288-290's population half (31tr T42(a)); S4 :467-468 (`Wave31to.genInv`); S4 :470-487 (i) and
  its proof S4 :489-507 (`Wave31to.newrates_ii_a/b`, 31tr T10); S4 :1056-1059's "the smallest" (31tr T33); S4 :1061-1062 (31tq Q21 with Q7(a), a
  hand composition); S4 :1112-1119 (31tr T38, T39, T42 (G)); the supporting-slope sentence of the proof of Lemma S4.22 (31tr T40(i-2)); S4
  :1026-1027 (31tq Q6, Q12); S6 :157-168's pairs (31tq Q28); S6 :173-175's `τ^A` bound (31tq Q25(c3) at `s = 1`, Q27(d)).
* Gone from the paper (no target): v2's §1 :110-111, §5 :299-300, §8 :7-8 and §5 :328-336 (the two-point sentence moved to S4 :1024-1026, Y21; the
  simulation sentence to §S6.4, Y23).

## Notes for the auditor
* Provenance of the frozen shapes (prover log, `STATUS_31tu.md`): all 40 claims are the critic-checked scratch shapes of
  `fullstack/work/scratch31tu/Defs31tu.lean` v3.1 (sha256 prefix 706a1ca2734400f5), with `Tr.` → `Wave31tr.` and the 14 copied 31tq/31tr
  definitions (`absPQ`, `IsCross`, `ExpTail`; `cutLabel` … `IsPaperRun`) replaced by imports (byte-identity of the copies checked by script at the
  freeze). Re-checked for this card by script: the 74 definitions of the frozen file (34 definitions and 40 claims) are identical to the scratch
  ones up to whitespace and `Tr.` → `Wave31tr.`. No claim was drafted at the freeze without a critic-checked shape (unlike 31tq).
* Frozen files unchanged: `git diff --stat 69f1ac7 HEAD -- StatFormal/Wave31tu/Statements.lean certify/statements.lock certify/targets.toml
  certify/sources` is empty at `592099b`; the 40 target rows have module `StatFormal.Wave31tu.Proofs`, paper `trimmed-mmd (jmlr)`, card
  `certify/cards/wave31tu.md`.
* Cross-chunk interfaces: the `_of` hypotheses listed in the header are all discharged in `Proofs.lean` by theorems proved above them; nothing is
  circular (`lap_local_d` uses `lap_local`; T uses L, P, F, B; F uses P, D; D uses H, L, P). The one route-level cross-chunk import is
  `RouteSLocal` → `RouteTPr` (`RouteT.laplace_twoSided`, authorized by the coordinator; untrusted, like every route). Certified theorems of earlier
  waves used by the routes (from the helper status files): 31tq `tv_density`, `newsobolev`, `newgauss`, `kernel_instances` and the route lemmas
  `RouteM.cross_tv`, `RouteM.cross_zero`, `MomentTrim.exists_linear_lower`, `exists_half_lower`, `CrossLaws.integrable_of_density`; 31tr
  `witness_unique`, `excess_i`/`excess_laplace` (G), `genuine_rules`, `paperRun_exists`, `paperRun_admissible`, `RouteRun.nearestCuts_bounds`,
  `prior_one`; 31tp `feature_exists`, `fourier_feature`, `gram_mmd`, `mmd_fourier` and the Gram/native-space Lib (`gram_rep_le`, `gramIso`,
  `native_le_norm`, `rkhs_vanish_facts`); `Wave31to.newrates_ii_b`, `genInv`; `Wave31tl.lorate_iii`, `lorate_batches` and route helpers
  (`two_sided`, `lower_trivial`, `floor_ge_of_mesh`, `Tbet_mono`, `Core.genEps_le`, `Core.arith_a0`, `Basic.sum_exp_le_Jeps`); Wave30tz
  `bet_power_route`, `grid_events_route`, `map_fitSample`, `pop_ramp_rkhs`, `order_stat_shift`; `Wave31ti.pathconvex`; 31tn `RouteKL.klDiv_le_of_withDensity`
  and `Lib/Distances` (Pinsker, product TV).
* Observations of the proof helpers (generalisations available, not claimed): `lower2pt_not_cross`'s route does not use `0 < b`, `0 < c`; the T
  routes do not use Y7 `lap_const` (`κ₀, c_V > 0` proved directly); `lap_clip`'s `½ ≤ ‖φ̂‖` comes from Cauchy–Schwarz with `‖φx‖ = 1`, not from Y3;
  Y3's routes use an explicit `L²` feature map and no Fourier analysis (Tau Ceti's variation module is not built in the shared package, so the
  variation bound is proved directly); Y4's sandwich is deterministic; Y1(b)'s reverse inequality uses the intermediate value theorem on each
  partition gap (no uniform continuity); Y26's route is Y25 with Q22 at `ω(e) = (1−α⋆+e)D_{α⋆−e}` (D6), not the printed `ω_ℋ` route.
* Readings to check against the paper (all approved by the critics): D2 (plain/own-term per level and batch); D3 ((G) and (Pr), `∃ C` before
  `H, φ`); D4 (every representer); D12 ("near" as `O((n∧m)^{−1/2})` in total variation); D14 ("pooled points pairwise distinct" as no `X` equal to a
  `Y` in the lemmas); D15 ("for samples of comparable size" as `n∨m ≤ (n∧m)^k`, "improves" as `o((n∧m)^{−2/5})`); D17 (Y8(d)); Y8(b) ("stay away
  from one"); Y22's `J ≤ n∧m`; Y21's order (some nearby pair for every `T`, as the sentence prints it); Y16 isolated from a proof paragraph; Y15's
  gap qualifier; the run class's fraction bounds in place of the printed `v₀² ≤ 4` (S3.3).
* Paper findings (source §G): P1–P5 are fixed at `1fbc8df` (critic corrections #7–#11); P6 (the AI statement, bm :11-15) is open and the author's
  call. The map `docs/trimmed-mmd-aos.md` (regenerated in `d8a8553` after 31tq: "11 for Wave31tu") is to be regenerated from
  `aos/tools/lean_map.py` when this wave certifies.
* A grep of the 81 Lean files changed since the freeze (`StatFormal/Wave31tu`, the 11 Lib folders) for `sorry`, `admit`, `axiom`, `opaque`,
  `native_decide`, `implemented_by` and `extern` found nothing (not a substitute for the gate's scan).
* The printed line numbers are those of `1fbc8df`; for the post-freeze drift see Source.
