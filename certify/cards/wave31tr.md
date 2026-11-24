# Fidelity card — wave 31tr: the non-Fourier gaps of trimmed-mmd (**Annals of Statistics version**): the paper's own run and the rest

Lean: `StatFormal/Wave31tr/Statements.lean` (89 claim definitions for the drafted items T1–T57, with T21, T22(a), T23, T30, T43, T44
dropped together with their printed text; new definitions `cutLabel`, `IsBoundaries`, `IsPrintedPairing`, `IsQuantileRule`,
`IsGenuineQuantileRule`, `lowQ`, `highQ`, `IsPriorRule`, `IsQPSel`, `fracFormula`, `IsPaperRun`, `IsFractions`, `BoundariesNear`,
`empVar`, `algPrior`, `hzWealth`, `kqpVal`, `kwit`, `kownX`, `kownY`, `IsKernelRun`, `pairDist`, `zeroCount`, `medianBw`, `scaledDist`,
`lapK`, `gaussK`, `b0Scale`, `splitStart`, `fwSep`, `IsFWPoint`, `IsWitnessRampFW`, `IsWitnessRunFW`, `oscLaw`, `alphaZeroWit`,
`alphaZeroFn`, `ksGate`, `exAtoms`, `ksRadius`, `fnRamp`, `fnDrift`, `fnAlpha`; frozen 2026-11-22 before any proof, freeze commit
`eb93feb`, sha256 `50d648704073b5bf905884221673dcf6c04601189c68bbb0d306585640a05f9f`, locked in `certify/statements.lock` with its 120
local imports). Routes (untrusted), by proof chunk: A1 `RouteRun*`, A2 `RouteRunThm*`, A3 `RouteKernel*`, E1 `RouteExcess*`, E2
`RoutePop*`, M1 `RouteMisc1*`, M2 `RouteAlpha0*`, M3 `RouteFW*`, M4 `RouteCert*`, on the library folders `StatFormal/Lib/{PaperRun,
PaperRunThm, KernelRun, ExcessRamp, TVFacts, KernelFacts, Alpha0Witness, FrankWolfe, FnCert}`; `Proofs.lean` defines the 89 theorems,
each of type literally `Claims.X`; all proved, `#print axioms` propext, Classical.choice, Quot.sound for each (proof commit `1404091`).
Paper id `trimmed-mmd (jmlr)` (face `Papers/TrimmedMMDJMLR`; the AoS version is tracked on this page, as for Waves 31tn–31tp). Branch
`tmmd-aos-fullstack` (worktree `~/projects/StatFormal-tmmd-aos`); the freeze commit sits on top of `4e50e04`.
Scope (author decision, 2026-11-21, full-stack campaign `~/projects/tmmd-aos-brief/fullstack/CAMPAIGN.md`): the non-Fourier rest of the
AoS version, with no bridge. This wave closes GAPS C1 (the paper's own split-sample run, and the certified split-sample results restated
for it), B2, C2, C3, C5 (split-sample half), C7, D1–D4, D8, D9, A12, E7, E9, E14, E15, E18, the sweep's group (A), Proposition 5.10 with
Lemmas S4.17–S4.18, and the procedure-level sentences new at trimmed-mmd `b3125cf` (T47–T57). Plan: `fullstack/PLAN_31tr.md`.
Critic (independent AI reviewer, before the freeze; files in `tmmd-aos-brief/fullstack/`): `CRITIC_31tr.md` (v1, 2026-11-21) NOT READY TO
FREEZE (B1: the QP-selection clause made `IsPaperRun` unsatisfiable on an empty fitting side; T17; scope); `CRITIC_31tr_v2.md` NOT READY
(P1: the printed pairing unsatisfiable on a batch empty on one side only; F1: the paper had changed); `CRITIC_31tr_v3.md` NOT READY
(T46's conclusion); `CRITIC_31tr_v4.md` (diff-only) READY TO FREEZE; the coordinated F1 at `b3125cf`, `CRITIC_F1_b3125cf.md`
(2026-11-22): 31tr NOT READY (B1: T49 to be restated at the kernel level with a satisfiability witness; the existence conjunct of T47(b);
the paper corrections #1–#5); diff-only re-check `CRITIC_F1b_1fbc8df.md`: READY TO FREEZE, with the text notes n1 (the T49(b)
composition sentence), c2 (T50 line citations) and c3 (a P-3 line citation) applied before hashing. Change records: `DIFF_31tr.md`,
`DIFF_F1_b3125cf.md`.
Fidelity review: independent AI audit, method v1 (certify/AUDIT_METHOD.md), 2026-11-23 — PASS with notes. Scope: all 89 claims,
back-translated from the frozen `Statements.lean` and its definitions before the paper was opened; the reviewer had read this card's own
back-translation while locating files, so the step was blind to the paper but not to the card. The 38 critic-checked shapes were
compared by script with the critic's `Shapes31tr.lean` (a101b6fd983ffcac): byte-identical except the declared existence wrappers of
T6–T12. The 51 claims drafted by helpers were checked clause by clause against the printed text at `1fbc8df`. Hashes: `Statements.lean`
matches the lock, and no frozen file, lock entry, source copy or target row changed after `eb93feb`; the later 31tq freeze `5d9b27e`
touches no 31tr file. Findings: 52 claims faithful and 37 faithful with a note (generalisations and declared encodings); no
undeclared stronger hypothesis, unguarded junk value, vacuous hypothesis set or restated conclusion. The two narrower points: T57 freezes
the textbook Bayes risk (measurable decision rules), which is the printed R⋆, and the randomized form is prose only and follows from
`lem_ramp_iii`; T49(b) freezes the ingredients, and the printed "both bandwidth rules are admissible" follows by an unfrozen elementary
composition (coordinate maps; the rescaling identity of critic note n1 for RHC), while the solver's output enters `IsKernelRun` as a
measurable map (declared). C1 (the measurable paper run), B2 (the Remark S5.5 composition, T13) and the assigned sentences are closed;
the remaining declared caveats are listed in the audit. The gate was re-run on the `f9ec247` tree: CERTIFIED 4122, ALIASES OK 4065. Full
audit: `tmmd-aos-brief/fullstack/AUDIT_31tr.md`. Non-blocking notes there: the wording of the `alg:split` and `thm:betting` COVERAGE
rows (W1); T26's printed sentence removed from the paper after the freeze (master `50fbdc6`), and the line tables to refresh for
`1721ee6`, `a9a0ce9`, `5218bfa`; the conditioning on the permutations in T50(b) to be mentioned here; `docs/trimmed-mmd-aos.md`
and `lean_map.py` to be regenerated at merge; docstrings, three near-duplicate helpers and the layering of the new Lib folders.
**Author: approved (automatic on AI-audit PASS, per author decision 2026-10-21).**

## Source
`~/projects/tmmd-aos-brief/fullstack/NEW_STATEMENTS_31tr.md` at freeze (v5.1 + the critic's text notes n1, c2, c3): whole file sha256
`6652c9336597f1723ecc71b87f369349aa25d6b499098a888c29de6723736486` (1440 lines; copy committed in `eb93feb` as
`certify/sources/tmmd-aos-NEW_STATEMENTS-wave31tr.md`, same hash); the claims block (line 78, "Common setting", to the end) sha256
`fc5ed738eb223d2e54d4978567d8198950cbb02e3d48d55212a423929e518e62`. Earlier drafts kept as `fullstack/work/NEW_STATEMENTS_31tr_v1.md` to
`_v5.md` and `_v5.1_prefreeze.md`.
Printed source: trimmed-mmd `aos/` at `1fbc8df` (the 11 wording corrections of `CRITIC_F1_b3125cf.md` §1 and four length cuts on top of
`b3125cf`). The file hashes are listed at the top of the source: the sha256 prefixes at `1fbc8df` of the seven files changed since
`b3125cf` (`sections/00_abstract` a3d7a240bff9, `01_introduction` 6cf223469dd0, `05_rates` 9bcd992dbfab, `06_trimming` 725265e8156e,
`07_numerical` d3a9002b1b03, `08_final` 9b6f55fb3a9f, `supplement/S4_rates` 58bf03da5e94), and the `b3125cf` prefixes of every other cited
file (byte-identical at `1fbc8df`), with `main.tex`, `supplement.tex`, `preamble.tex` and `src/trimmedmmd/splitting.py`. Printed numbers:
`aos/main.aux`, `aos/supplement.aux` (all 111 labelled environments byte-identical between `b3125cf` and `1fbc8df` after normalization).
Line numbers below are those of `1fbc8df`: `§k` = `sections/0k_*.tex`, `main` = `sections/05_rates.tex`, `S1`–`S6` the supplement files.
After the freeze the author moved the impossibility of informative upper bounds to §2.4 (Theorem 2.6, labels `sec:upper`,
`thm:impossible` kept; trimmed-mmd `1721ee6`, "statements byte-identical"). The sentences cited below at main :347-354 (T45's main-text
summary, T54) now read at `sections/02_regions.tex` :254-258 of `1721ee6`. The line tables (and D9's printed number of `thm:impossible`)
are to be refreshed at the next F1. The trimmed-mmd working tree also has uncommitted edits in `sections/04_split.tex`,
`07_numerical.tex` and the supplement, not compared here.

## Targets (89 claims in `StatFormal.Wave31tr.Proofs`; all in `certify/targets.toml`, theorem = `StatFormal.Wave31tr.<name>`)
| item | label (abridged) | claim |
|---|---|---|
| T1(a) | `eq:cutrank` (S3 :247, linear interpolations) | `npQuantile_rule` |
| T1(b) | `eq:cutrank` (S3 :106-108, :241-247) | `genuine_rules` |
| T1(c) | `eq:cutrank` (order statistics) | `ordStat_facts` |
| T1(d) | `alg:split` line 10 (§4 :61-64) | `printed_cuts` |
| T2(a) | `sec:betting` pairing (S3 :113-119; `alg:split` lines 1-2) | `printedPairing_exists` |
| T2(b) | `sec:betting` pairing (closes `wave30tv.md:44-46`) | `printedPairing_batch` |
| T2(c) | `sec:betting` batches (§4 :54-56, S4 :286) | `printedPairing_default` |
| T3 | `eq:qp` (`prop:loconsistency`, "an exact minimizer") | `qp_measurable_argmin` |
| T4(a) | `alg:split` (§4.2, S3 :97-159) | `paperRun_exists` |
| T4(b) | `alg:split`, the printed instance | `paperRun_exists_printed` |
| T7, T12 (existence) | `sec:betting` fractions fixed in advance (S3 :99) | `paperRun_exists_fractions` |
| T5 | S3 :120-126 | `paperRun_admissible` |
| T6(iii)–(iv) | `thm:betting`, `cor:lower` (Theorem 4.2, Corollary 4.3) | `paperRun_betting` |
| T6(i), (ii), (v) | `thm:betting` given batch 0, `cor:lower` second sentence | `paperRun_betting_cond` |
| T7 | `prop:loconsistency` (Proposition 4.4) | `paper_lo_consistency` |
| T7 | `prop:loconsistency`, refining grids | `paper_lo_refining` |
| T8 | `thm:loratemain` (Theorem 5.7) | `paper_lorate_O` |
| T8 | main :146-147 ("at most of order `(n∧m)^{−1/(2γ)}`") | `paper_same_rate` |
| T9 | `thm:lorate` (i) (Theorem S4.3) | `paper_lorate_i` |
| T9 | `thm:lorate` (ii) | `paper_lorate_ii` |
| T9 | `thm:lorate`, the paragraph after (S4 :184-189) | `paper_lorate_nologJ` |
| T9 | `thm:lorate`, general margin | `paper_lorate_general` |
| T10 | `prop:newrates` (i) (Proposition S4.8), first part | `paper_newrates_i_a` |
| T10 | `prop:newrates` (i), second part | `paper_newrates_i_b` |
| T11 | `cor:minimax` (ii) (Corollary 5.9) | `paper_minimax_ii` |
| T12 | `cor:alphalo` (Corollary 6.3) | `paper_alphalo` |
| T13(a) | `rem:qdens` (Remark S5.5) at `d = 1` (closes GAPS B2) | `gauss_qdens_formula` |
| T13(b) | `rem:qdens` at `d = 1`, (Q) and (Q′) | `gauss_qdens_Q_Qprime` |
| T14 | S3 :363-364 | `alpha0_uniform` |
| T15 | S3 :364 | `alpha0_fit_uniform_as` |
| T16(a) | S3 :374-377 | `ksPlus_locally_constant` |
| T16(b) | S3 :374-377 | `ex_ks_stable` |
| T17(a) | S3 :377 | `alpha0_reject_le` |
| T17(b) | S3 :377, §4 :162-165 | `alpha0_inconsistent` |
| T17(c) | S3 :364-368 | `alpha0_gate` |
| T18(a)–(b) | S3 :358-360 | `fw_gap` |
| T18(c) | S3 :358-360 | `fw_exact` |
| T19 | S3 :358-360 | `fitted_ramp_fw` |
| T20(a) | S3 :358-360 | `lo_lower_bound_fw` |
| T20(b) | S3 :358-360 | `lo_consistency_fw` |
| T22(b) | `cor:minimax`, main :220-222 | `same_quantile` |
| T24 | S4 :306 | `dbar_le_D_le` |
| T25 | `prop:newrates`, S4 :509-512 | `margin_dbar_factor` |
| T26 | S4 :876-879 | `any_threshold_converse` |
| T27 | `prop:bangbang` (D4) | `bangbang_aos` |
| T28(a) | main :320-322, §1 :86-88 | `tv_one_sided_ks` |
| T28(b) | main :320-322 | `ks_lower_confidence` |
| T29(a) | `prop:newslope` last sentence (Proposition 5.3, main :68-70) | `contact_densities` |
| T29(b) | `prop:newslope` last sentence | `contact_gauss_mix` |
| T29(c) | `cor:minimax` class (main :222-224; E9) | `minimax_class_apart` |
| T31 | §4 :73 | `default_pairs_three_quarters` |
| T32 | `ass:regularity` (Assumption 2.1; §2 :57-61, S1 :6; D8) | `house_encoding` |
| T33 | §2 :196-197, §6 :17-19, S5 :45-47 | `witness_unique` |
| T34(a) | `eq:contam` (§2 :28-34, §1 :11-13) | `contam_equiv` |
| T34(b) | §1 :19-22, S1 :17-26 | `trimming_removal` |
| T34(c) | S1 :25-26, §2 :40 | `different_fractions` |
| T35 | §2 :47-50 | `kernel_constants` |
| T36 | §2 :85-86, :116-118 | `regions_nested` |
| T37 | §2 :150-154, S5 :69-73 | `bathtub_quantiles` |
| T38 | `lem:excessbathtub` (Lemma S4.17) | `excess_bathtub` |
| T39 | `lem:excessid` (Lemma S4.18) | `excess_identity` |
| T40 | `prop:excess` (i) (Proposition 5.10; main :253-255, :275-279) | `excess_i` |
| T41 | `prop:excess` (ii) (main :256-257, :280-282) | `excess_ii` |
| T42(a)–(c) | `prop:excess` (iii) (main :283-284, S4 :978-979) | `excess_laplace` |
| T42(d) | `prop:excess` (iii), proof step (S4 :967) | `laplace_green` |
| T45 | S4 :1531-1537, main :349-351 | `oscillation_blind` |
| T46(a) | §8 :9-10 | `fncert_drift_err` |
| T46(b) | §8 :9-11 | `fncert_upper` |
| T46(c) | §8 :9-11 | `fncert_rejected_upper` |
| T46(d) | §8 :11-12 | `fncert_betting_error` |
| T47(a) | `rem:qdens` last sentence (Remark S5.5), §6 :9-12 | `laplace_qdens_fails` |
| T47(b) | §6 :46-47 | `finite_support_not_qdens` |
| T47(b) (existence) | §6 :46-47 ("the margin does not imply the density conditions") | `margin_without_qdens` |
| T48(c) | `alg:split` line 12 (Algorithm S1; S3 :153-154) | `alg_prior` |
| T49(a) | §4 :170-173, S3 :199-200, `alg:split` lines 4-7 | `kernel_run_valid` |
| T49(b)(i) | `alg:split` line 5 | `median_bandwidth` |
| T49(b)(ii)–(iii) | `alg:split` line 5, §7 :126-127, :158 | `kernel_profiles` |
| T50(b) | §7 :147-152, Table 2 caption, §8 :24-25 | `averaged_evalue` |
| T50(c)–(d) | §7 :152, :155, S6 :84-86 | `bound_summaries` |
| T51 | §6 :102-103 (`prop:alphahat` composed) | `trimming_at_lower` |
| T52 | §7 :170-175 | `propensity_core` |
| T53 | S6 :191, :117 | `tv_pushforward` |
| T54 | main :351-354 | `upper_end` |
| T55 | `ass:margin` (main :28-29) | `margin_eps0` |
| T56(a) | `eq:null`, §3 :49-50 | `taup_jump` |
| T56(c) | §3 :92-93 | `taup_welldefined` |
| T56(d) | §3 :93-97 | `taup_valid_bound` |
| T56(e) | §3 :97-100 | `taup_consistent_below` |
| T57 | §1 :106-107 | `bayes_risk` |

## Encodings (declared; full list in the Lean header and `NEW_STATEMENTS_31tr.md` "Common setting")
* Kernel, data, regions as in every trimmed-mmd wave: `𝒳` a measurable space, `ℋ` a real inner-product space, complete, and separable
  where (A2) is used; `φ` strongly measurable with `‖φx‖ ≤ κ` and `‖φx − φx′‖ ≤ Δ_φ`; (A3) is `ZeroSet.Characteristic φ`; the data have
  law `sampleLaw P Q n m = P^{⊗n} ⊗ Q^{⊗m}`; `α⋆ = tvDist P Q`; `D_α = Dpop`, `D̂_α = Demp`, `D̄_α = (1−α)D_α = Wave31ti.uPath`.
* Frozen run objects reused, not redefined: `Wave30tz.LoRun` and its `alphaLo` (`eq:downclosed`, printed `α̂`), `IsAdmissible`,
  `IsWitnessRun`, `IsSizedRun`, `IsQPMin`, `IsCapped`, `qpVal`, `witness`, `ownX`, `ownY` (own term removed, Algorithm S1 line 9 with
  `k(x,x) = ‖φx‖²`), `CutsC`, `ordStat`, `npQuantile`, `IsEmpQuantile`, `fitSample`, `fitCard`, `lamLo`, `lamHi`, `IsGrid`;
  `Wave30tv.IsBatchPairing`, `withBatchZero`; `Wave30tq.wealth`, `ramp`, `IsQuantileAt`; `Wave31tl.IsDefaultRun`, `NearestCuts`,
  `defaultLabel`, `batchCount`, `defaultPairs`.
* `nb` is the number of batches bet on (printed `B`; the frozen `LoRun` field `B` is the `Y`-blocks). Batches from interior boundaries:
  `cutLabel nb c i = #{b ∈ [1, nb] : c_b ≤ i}`, `IsBoundaries` (nondecreasing, at most the sample size; equal boundaries allowed).
* The printed pairing in a decidable form (`IsPrintedPairing`): `N = Σ_b min(n_b, m_b)`, pairs numbered batch by batch, exactly
  `min(n_b, m_b)` pairs in batch `b`, singletons of the smaller side used once each, order-convex blocks of the larger side partitioning the
  batch with sizes differing by at most one; the block clauses are guarded by `1 ≤ n_b` (resp. `1 ≤ m_b`), so a batch with an empty side
  has no pair (critic P1). "Paired one to one" is any bijection, in any order inside a batch (a generalisation; the code pairs in order).
* Two cut rules: `qt` on the `X` side at `1−α`, `qu` on the `Y` side at `α`; the printed rules are `lowQ` (smallest empirical quantile)
  and `highQ` (largest). The universal parts of T5–T12 and T49 quantify over every `IsQuantileRule` (measurable, within one rank of the
  quantile, `eq:cutrank`), which contains the printed genuine rules (T1(b)) and the interpolated rule of the Gaussian runs of S6.
  `IsGenuineQuantileRule` (X2) is shared with 31tu.
* The QP selection (`IsQPSel`, a measurable selection of exact minimizers) is required only on nonempty fitting sides (B1 guard).
  `eq:fractions` is written with indicator weights (`fracFormula`, `e_l = 1` iff pair `l` was bet on). The prior `v₀²` is any
  `IsPriorRule` (measurable, in `[0,4]`, a function of the batches before `b`); the existence conjuncts use `v₀ ≡ 1`.
* The index order is an order fixed in advance (S3 :101), equivalent in law to the printed random order for i.i.d. data; T15 uses it
  pathwise (prefixes of two infinite sequences).
* Form of T6–T12: `genuine_rules ∧ <existence at lowQ/highQ, v₀ ≡ 1> ∧ <every paper run with quantile rules>`. The universal conjuncts
  are the certified claims with `R.IsWitnessRun …` replaced by `0 < w₀ → IsQuantileRule qt → IsQuantileRule qu → IsPaperRun …`,
  `IsDefaultRun R` by `nb = 2 ∧ NearestCuts … ∧ NearestCuts …`, and (T7, T12) `IsSizedRun` by fractions fixed in advance
  (`IsFractions`, `BoundariesNear`, any rounding, `1 ≤ nb`).
* "Conditionally on batch 0": batch 0 replaced by a fixed value through `withBatchZero`, the other batches drawn from the product law
  (as in the certified `thm_betting_cond`), or a conditional expectation on `Unit × sample` (as in `thm_betting_condexp`).
* `IsKernelRun` is the run as computed, at the kernel level: a measurable parameter space `Θ`, a kernel family `kf θ`, a parameter `θh b`
  measurable in the batches before `b`, any measurable capped weights; no positive definiteness, no feature map, no bound on the kernel.
* `IsFWPoint φ α ρ` is the Frank–Wolfe point of relative gap `ρ`; `IsWitnessRampFW`, `IsWitnessRunFW` are verbatim copies of the frozen
  `IsWitnessRamp`, `IsWitnessRun` with `IsQPMin` replaced by it.
* T38–T42 each as `(G) ∧ (Pr)`: (G) any representing densities or region points, any quantiles `t`, `u`, no (A3); (Pr) the printed
  objects under Assumption 2.1, `0 < α⋆ < 1`, `0 ≤ α < α⋆`, the least `(1−α)`-quantile `t⋆` and the greatest `α`-quantile `u⋆`.
* Densities are nonnegative and measurable where a density is meant; laws on `[0,1]` are laws on `ℝ` carried by `[0,1]`; mixtures are
  `ENNReal.ofReal (1−α) • R + ENNReal.ofReal α • P₀`; for T29, `𝒳 = U` is a subtype of `ℝ^d` with its Borel sets and densities with
  respect to `Measure.comap Subtype.val volume`.
* Encoding choices made at drafting (declared): T29 densities nonnegative on `U`; T32 `κ ≥ 0`; T46(d) `N ≥ 1`, `h ≥ 0`, every pair bet
  on, `∃ C` before everything but `δ, η, J, v²_min`, generalised to any batch pairing; T46(b)–(c) generalised to any batch pairing; T28
  measurable densities; T15 every exact minimizer at `α = 0`; T17 the ramp hypothesis on nonempty fitting sides in (a)–(b) and on every
  pair in (c), and "not consistent" read as "does not tend to 1"; T14 the `Demp`/MMD conjuncts guarded by `StronglyMeasurable φ`; T18
  `fw_gap` includes the identification with `Wave17a.sepVal`; T22(b) `∃ C N₁` before `∀ a₀`; T42 no `κ` (`‖φx‖ = 1` from the Gram
  function); T38 (G) drops `a ∈ region` (implied by the densities); T40 (G) (i-2) without `u < t`; T45 the supremum over `α` written
  uniformly; T25 two harmless extra conjuncts; `paperRun_exists_fractions` with `J`, `α`, `δ` allowed to depend on `(n, m)`; T2(a) the
  `array_split` description as a conjunct; T1(c) `LipschitzWith 1`; T3 for every `IsQPSel σ`.

## Covered — back-translation and deviations
Back-translated from the frozen `Statements.lean`. "Paper run" below means `IsPaperRun R φ α δ λ_max v²_min w₀ v₀ qt qu nb cx cy` with
`IsQuantileRule qt`, `IsQuantileRule qu`, `w₀ > 0`; "the run hypotheses of T5" are `StronglyMeasurable φ`, `‖φ‖ ≤ κ`, `IsGrid α`,
`δ ∈ (0,1)`, `λ_max ∈ (0,1]`, `v²_min > 0`, `w₀ > 0` and the two quantile rules.
* T1(a) `npQuantile_rule`: numpy's linearly interpolated quantile is measurable in the values for every `k, p`, and for `k ≥ 1`,
  `p ∈ [0,1]` lies between the order statistics of ranks `ι⁻(k,p)` and `ι⁺(k,p)`. Faithful (S3 :247, S6 :36, :86).
* T1(b) `genuine_rules`: `lowQ` and `highQ` are genuine-quantile rules (measurable; for `k ≥ 1`, `p ∈ [0,1]`, a value `q` with
  `#{h_i < q} ≤ kp ≤ #{h_i ≤ q}` between the smallest and the largest value), and every genuine-quantile rule is a quantile rule.
  Faithful.
* T1(c) `ordStat_facts`: for `1 ≤ r ≤ k`, `h ↦ h_(r)` is measurable and 1-Lipschitz for the sup norm (`LipschitzWith 1` on
  `Fin k → ℝ`), and `h_(r) ≤ v` iff at least `r` values are `≤ v`. Faithful.
* T1(d) `printed_cuts`: for `k ≥ 1`, `α ∈ [0,1)`: `1 ≤ ⌈k(1−α)⌉ ≤ k`, `⌊kα⌋ + 1 ≤ k`, `lowQ k h (1−α) = h_(⌈k(1−α)⌉)`,
  `highQ k h α = h_(⌊kα⌋+1)`, the first is the least empirical `(1−α)`-quantile and the second the greatest empirical `α`-quantile.
  Faithful (§4 :61-64, Algorithm S1 line 10).
* T2(a) `printedPairing_exists`: for `nb ≥ 1` and any boundaries, a printed pairing of `cutLabel nb cx`, `cutLabel nb cy` exists, with
  pair number `Σ_{b′<b} min(n_{b′}, m_{b′}) + l` (for `l < min(n_b, m_b)`) in batch `b` and, when `n_b ≤ m_b`, pairing `X` index
  `cx_b + l` with the `Y` indices from `cy_b + splitStart(m_b, n_b, l)` up to `cy_b + splitStart(m_b, n_b, l+1)` (numpy's
  `array_split`); the mirror when `m_b < n_b`. Faithful; encoding: the `array_split` description is a conjunct.
* T2(b) `printedPairing_batch`: for `nb ≥ 1` and any boundaries, every printed pairing is a `Wave30tv.IsBatchPairing` with
  `N = Σ_b min(n_b, m_b)`, every `bat k ∈ [1, nb]`, exactly `min(n_b, m_b)` pairs in batch `b`, none in a batch with an empty side, and
  nonempty blocks. Faithful (closes the instance gap declared on `wave30tv.md:44-46`).
* T2(c) `printedPairing_default`: with `nb = 2` and nearest-integer boundaries (any tie-breaking, any `n, m`), `cutLabel 2` equals the
  frozen `defaultLabel`, a printed pairing has `N = defaultPairs`, and every run with these labels and a printed pairing is an
  `IsDefaultRun`. Faithful.
* T3 `qp_measurable_argmin`: for strongly measurable `φ` into a complete space, `α ∈ [0,1)`, `n, m ≥ 1`: a measurable selection of
  exact minimizers of `eq:qp` exists; for every such selection `σ`, `(x,y) ↦ qpVal` at `σ(x,y)` is measurable and equals `Demp φ x y α`;
  and the `Wave30tz` and `BangBang` encodings of `eq:qp` agree (`IsCapped ↔ capped`, `qp = qpVal²`, `IsQPMin ↔` minimality on
  `capped × capped`). Faithful; encoding: for every `IsQPSel σ` (Aliprantis–Border Thm 18.19 for existence).
* T4(a) `paperRun_exists`: for every `𝒳`, complete `ℋ`, strongly measurable `φ`, levels in `[0,1)`, `δ ∈ (0,1)`, `λ_max ∈ (0,1]`,
  `v²_min > 0`, `w₀ > 0`, boundaries, a prior rule for the induced labels and any two cut rules (no property assumed), some run satisfies
  `IsPaperRun`. Faithful (generalisation: any rules).
* T4(b) `paperRun_exists_printed`: under the same `φ`, levels, `δ`, `v²_min > 0`, for all `n, m` there are a run and nearest-integer
  boundaries with `IsPaperRun` at `nb = 2`, `λ_max = ½`, `w₀ = 20`, `v₀ ≡ 1`, `qt = lowQ`, `qu = highQ`. Specialisation to `v₀ ≡ 1`
  (Algorithm S1's prior: T48(c)).
* `paperRun_exists_fractions` (existence conjunct of T7, T12): for fractions `IsFractions nb π`, `nb ≥ 1`, level grids `α n m` in
  `[0,1)`, levels `δ n m ∈ (0,1)`, `λ_max ∈ (0,1]`, `v²_min > 0`, `w₀ > 0`, there are runs `R n m` and boundaries within one of `π_b n`,
  `π_b m`, with `IsPaperRun` at `lowQ`, `highQ`, `v₀ ≡ 1`, for every `(n, m)`. Faithful; encoding: `J`, `α`, `δ` may depend on `(n, m)`
  (fixed ones are the constant case).
* T5 `paperRun_admissible`: every paper run under the run hypotheses of T5 is admissible (`IsAdmissible α λ_max`) and a witness run
  (`IsWitnessRun φ α δ λ_max v²_min`); with `nb = 2` and nearest-integer boundaries it is an `IsDefaultRun`; and for every `π` with
  `nb ≥ 1`, `IsFractions` and boundaries within one of the fractions it is `IsSizedRun c 2 nb` with `c = min_{0≤b≤nb}(π_{b+1} − π_b)`.
  Faithful (the bridge to every certified split-sample result; `1 ≤ nb` added in v5, as `nb = 0` gives no pair).
* T6 `paperRun_betting`: form of T6–T12; for every paper run under the run hypotheses of T5 and all probability measures `P, Q`:
  `P(H_{0,α_j} rejected) ≤ δ` at every level with `TV(P,Q) ≤ α_j`, and `P(α̂ > TV(P,Q)) ≤ δ`. Faithful (Thm 4.2, Cor 4.3).
  `paperRun_betting_cond`: same form; (i) at every true-null level and every value `(x₀, y₀)` of batch 0, the rejection probability with
  batch 0 fixed at `(x₀, y₀)` is `≤ δ`; (ii) the rejection event on `Unit × sample` is measurable and its conditional expectation given
  `σ(batch 0)` is `≤ δ` a.s.; (v) the event "`α̂` is a grid level whose test rejected, and `TV ≤ α̂`" is measurable with probability `≤ δ`.
  Faithful; encoding: "conditionally on batch 0" as declared.
* T7 `paper_lo_consistency`: form of T6–T12 with `paperRun_exists_fractions`; under (A1)–(A3) (`ℋ` complete separable,
  `‖φx − φx′‖ ≤ Δ_φ`, `Characteristic φ`), a fixed grid, `δ ∈ (0,1)`, `λ_max ∈ (0,½]`, `v²_min > 0`, `w₀ > 0`, fractions with `nb ≥ 1`,
  and for every `(n,m)` a paper run with quantile rules (allowed to depend on `(n,m)`) and boundaries within one of the fractions:
  `P(α̂ > α_{j⋆}) ≤ δ` for all `n, m` (`α_{j⋆} = gridBelow α α⋆`, the largest level below `α⋆`); `P(α̂ < α_{j⋆}) → 0` as `n, m → ∞`;
  and, if no level equals `α⋆`, also `P(α̂ > α_{j⋆}) → 0`. `paper_lo_refining`: for grids with mesh `→ 0` and `log J = o(n∧m)`, levels
  `δ_{n,m} ∈ (0,1)` eventually `≤ δ̄ < 1` with `log(1/δ_{n,m}) = o(n∧m)`, and the same run hypotheses: `α̂ → α⋆` in probability.
  Faithful (generalisation: `λ_max ∈ (0,½]`, printed ½; any prior and quantile rules; any fractions).
* T8 `paper_lorate_O`: form of T6–T12; under (A1)–(A2), `PolyMargin c₀ γ`, `α⋆ < 1`, a grid of `J ≥ 1` levels, `δ, η ∈ (0,1)`,
  `v²_min ∈ (0,4]`, a paper run at `λ_max = ½` with `nb = 2` and nearest-integer boundaries, `n, m ≥ 1`, and `h` bounding the mesh below
  `α⋆`: an event of probability `≥ 1−δ−η` on which
  `α⋆ − h − (1000κ/(c₀(1−α⋆)v²_min) · √((1 + log(1/δ) + log(J/η))/(n∧m)))^{1/γ} ≤ α̂ ≤ α⋆`. `paper_same_rate`: for fixed laws and fixed
  `κ, c₀, γ, J, δ, η, v²_min` there is `C ≥ 0` such that for all `n, m ≥ 1`, grids, such paper runs and mesh bounds `h`, with probability
  `≥ 1−δ−η`, `α⋆ − h − C(n∧m)^{−1/(2γ)} ≤ α̂ ≤ α⋆`. Faithful (the absolute constant is 1000 inside the power and `n∧m ≥ 10` is dropped,
  as certified in `Wave31tl`).
* T9 `paper_lorate_i`, `paper_lorate_ii`, `paper_lorate_nologJ`, `paper_lorate_general`: the certified `Wave31tl` claims with the run
  hypothesis replaced by a paper run at `λ_max = ½` (any `nb`, boundaries, prior and quantile rules); the other hypotheses as certified
  (pairs in batches `≤ B`, batch 0 nonempty on both sides, `r₁ ≤ 1`, `N ≥ 1`, `Δ_φ ≤ 2κ`, `v²_min ∈ (0,4]`). (i): under gaps `≥ h₀` and
  `β(α⋆)·max(T_fit, T_bet(J_ε)) ≤ c₀ε^γ`, `P(α̂ < gridFloor(α⋆ − ε)) ≤ η`; (ii): with probability `≥ 1−δ−η`,
  `α⋆ − h − (t_{n,m}/c₀)^{1/γ} ≤ α̂ ≤ α⋆`; the paragraph after: if the error term at `T_bet(4)` is `≤ h₀`, then `J_ε ≤ 4` there and the
  same two-sided bound holds with `T_bet(4)` in place of `J`; general margin: if `ω(e) = t_{n,m}` for some `e ∈ [0, α⋆]`, then
  `α⋆ − h − e ≤ α̂ ≤ α⋆` with probability `≥ 1−δ−η`. Faithful.
* T10 `paper_newrates_i_a`, `paper_newrates_i_b`: Proposition S4.8 (i) for a paper run at `λ_max = ½`, with a margin `ω` nondecreasing
  and nonnegative on `[0, α⋆]` and `ω(e) ≤ D̄_{α⋆−e}`: (a) under gaps and `β·max(T_fit, T_bet(J_ε)) ≤ ω(ε)`, `P(α̂ < gridFloor(α⋆ − ε)) ≤ η`
  (with `κ > 0`); (b) with probability `≥ 1−δ−η`, `α⋆ − h − ω^←(t_{n,m}) ≤ α̂ ≤ α⋆`. Faithful (the certified `Wave31to.newrates_ii_a`,
  `_b`, now printed as part (i)).
* T11 `paper_minimax_ii`: form of T6–T12; for `κ, Δ_φ`, `0 < a₁ < 1`, `c₀ > 0`, `v²_min ∈ (0,4]`, `δ, η ∈ (0,1)` there are `C, N₁` such
  that for every `a₀ ∈ (0, a₁)`, every (A1)–(A2) `φ` with `‖φ‖ ≤ κ`, `‖φx − φx′‖ ≤ Δ_φ ≤ 2κ`, all `n, m` with `n∧m ≥ max(N₁, 10)`,
  every `(P,Q) ∈ 𝓜(a₀, a₁, c₀)` and every paper run on `rootGrid(n∧m)` at `λ_max = ½`, `nb = 2`, nearest-integer boundaries:
  `P(α̂ > TV) ≤ δ` and `P(TV − α̂ > C(n∧m)^{−1/2}) ≤ η`. Faithful (`C, N₁` uniform in `a₀`, as certified).
* T12 `paper_alphalo`: form of T6–T12 with `paperRun_exists_fractions`; under (A1)–(A3), `0 < α⋆ < 1`, refining grids (mesh `→ 0`,
  `log J = o(n∧m)`), fixed `δ ∈ (0,1)`, `λ_max ∈ (0,½]`, `v²_min > 0`, `w₀ > 0`, fractions with `nb ≥ 1` and paper runs at them: for every
  `ε > 0` and `δ′ ∈ (0,1)`, eventually an event of probability `≥ 1−δ−δ′` on which every exact minimizer of `eq:qp` at the level `α̂` has
  both weighted empirical embeddings within `ε` of the embedding of the contact law. Faithful (Corollary 6.3).
* T13(a) `gauss_qdens_formula`: Gaussian Gram on `ℝ` (`σ > 0`), any `g ∈ ℋ`, `h = ⟨g, φ·⟩`, `t ≠ 0` with `{h = t}` nonempty and
  `h′ ≠ 0` on it, an open `U ⊇ {h = t}`, `p` continuous on `U` and positive on `{h = t}`: `{h = t}` is finite and there are `r > 0`,
  `0 < c ≤ C` with `h′ ≠ 0` on `h⁻¹[t−r, t+r]`, finite level sets there, `levelDens h p` continuous on `[t−r, t+r]` with values in
  `[c, C]`, and `(p·λ)(h⁻¹A) = ∫_A levelDens h p` for measurable `A ⊆ [t−r, t+r]`. T13(b) `gauss_qdens_Q_Qprime`: with these conditions
  for `p` at `t_α ≠ 0` and for `q` at `u_α ≠ 0` (open `V`), for any `d⋆ ∈ ℋ`, there are `r_Q > 0`, `0 < c_f ≤ C_f`, `c′_f > 0` with
  `QDensity (p·λ) d⋆ t_α r_Q c_f C_f` and `QDensityLower (q·λ) d⋆ u_α r_Q c′_f`. Faithful (no hypothesis on the witness: the `C¹` and
  decay hypotheses of the certified `Wave31tc` claims are discharged; removes the conditionalisation of the `wave31tc` row).
* T14 `alpha0_uniform`: for `n, m ≥ 1` and any `φ`: `Δ_0(n)` is the single uniform point; the exact minimizers of `eq:qp` at `α = 0` are
  exactly the uniform pair; there `qpVal = ‖n⁻¹Σφ(x_i) − m⁻¹Σφ(y_j)‖` and the witness is that difference divided by its norm (`0` when
  the norm is `0`); with `φ` strongly measurable also `Demp φ x y 0` and `‖∫φ dP_n − ∫φ dQ_m‖` equal that norm. Faithful; encoding: the
  `Demp`/MMD conjuncts are guarded by `StronglyMeasurable φ`.
* T15 `alpha0_fit_uniform_as`: on a probability space, `X_i` pairwise independent with law `P`, `Y_j` pairwise independent with law `Q`
  (measurable, nothing assumed between the sequences), `ℋ` complete separable Borel, `φ` strongly measurable, `‖φ‖ ≤ κ`,
  `‖μ_P − μ_Q‖ > 0`: almost surely, for every `ε > 0`, eventually in `n, m` every exact minimizer at `α = 0` on the prefixes `X_{1:n}`,
  `Y_{1:m}` has witness within `ε` of `f₀ = ⟨(μ_P − μ_Q)/‖μ_P − μ_Q‖, φ·⟩` uniformly on `𝒳`; and on the same almost-sure event the same
  holds for prefixes of sizes `a(n,m), b(n,m)` that tend to infinity. Faithful; encoding: prefixes (order fixed in advance), every exact
  minimizer at `α = 0`.
* T16(a) `ksPlus_locally_constant`: for laws carried by a finite set `S`, `f₀` injective on `S` and `0 < g₀` at most every gap of `f₀` on
  `S`, every `f` within `g₀/2` of `f₀` on `S` has `KS⁺(f) = KS⁺(f₀)`. Faithful (the measurability hypotheses are not used: Notes).
  T16(b) `ex_ks_stable`: the 24 atoms are distinct, `f₀ = exWitness exP exQ` is injective on them, `KS⁺(f₀) = 2/5`, and every `f` within
  `g₀/2` of `f₀` on the atoms, for any `0 < g₀` at most every gap, has `KS⁺(f) = 2/5`. Faithful (generalisation: any such `g₀`, any `f`).
* T17(a) `alpha0_reject_le`: for `exP`, `exQ`, any `φ : ℝ → ℋ` (complete separable) with the Gaussian Gram (`σ = 1`), `δ ∈ (0,1)`,
  `λ_max ∈ (0,1]`, `c > 0`, and run families with `IsAdmissible α λ_max ∧ IsSizedRun c C₀ B` whose ramp, at every pair's batch with
  nonempty fitting sides, is `h_b ∘ f̂_{0,b}` for some nondecreasing `[0,1]`-valued `h_b`: for every level `α_j ≥ 2/5` and `ε > 0`,
  eventually `P(reject H_{0,α_j}) ≤ δ + ε`. T17(b) `alpha0_inconsistent`: the same on a grid: `TV(exP, exQ) = 3/5`, and for every level
  `α_i ∈ [2/5, 3/5)`, eventually `P(α̂ ≥ α_i) ≤ δ + ε`, and `P(α̂ ≥ α_i)` does not tend to 1. Faithful; encodings as declared (ramp
  hypothesis on nonempty fitting sides, which hold for every pair eventually under `IsSizedRun`; "not consistent").
* T17(c) `alpha0_gate`: for fixed `P, Q`, (A1)–(A2) `φ`, a batch pairing, `α ≥ 0`, `δ ∈ (0,1)`, `c ∈ (0,1]`, a fitting rule `g` and an
  admissible fraction rule `λ` with every pair's ramp `h ∘ f̂_{0,bat k}`: for every batch `b`, `KS⁺_{P,Q}(f̂_{0,b})` is measurable in the
  sample and a function of the batches before `b`; the gated fractions `λ′ = λ·1{KS⁺(f̂_{0,bat k}) ≤ α}` are admissible; on
  `{KS⁺(f̂_{0,bat k}) ≤ α for every pair}` the fractions and the rejections of `λ′` and `λ` coincide; `P(λ′ rejects H_{0,α}) ≤ δ`; and
  `P(λ rejects) ≤ δ + P(some pair has KS⁺(f̂_{0,bat k}) > α)`. Faithful; encoding: the fractions use the true laws, the oracle device of
  the printed proof.
* T18 `fw_gap`: for strongly measurable `φ`, capped `(w, v)` with `d = qpVal > 0`: the maximum over capped `(w′, v′)` of
  `2⟨e,e⟩ − 2⟨e,e′⟩` is attained and equals `2d² − 2ds` (`s = fwSep` of the witness, over the capped simplices); `IsFWPoint ρ` iff
  `s ≥ (1 − ρ/2)d`; `s ≤ D̂_α ≤ d`; and `s` is the printed separation `sep(f̂; 𝒞_α(P_n), 𝒞_α(Q_m))` (`Wave17a.sepVal`). `fw_exact`: an
  exact minimizer is an `IsFWPoint 0` with `s = d` (any `φ`), and every `IsWitnessRun` is an `IsWitnessRunFW 0`. Faithful.
* T19 `fitted_ramp_fw`: the certified `Wave30tz.fitted_ramp` for an `IsFWPoint ρ`, `0 ≤ ρ < 1`, with hypothesis `βZ⁻ < (1−ρ/2)D_α`:
  `D̂ ≥ D_α − βZ⁻ > 0`, and for every pair of cut points satisfying (C) for the own-term values, `t − u ≤ Δ_φ`, `θ ≤ t − u`,
  `fitTheta(α, (1−ρ/2)D_α, Z, Z⁻, κ, Δ_φ, 1/n + 1/m) ≤ θ`, and if this `Θ > 0` then `u < t` and the ramp excess
  `E_Pψ − E_Qψ − α ≥ Θ/(βΔ_φ)`. Faithful.
* T20(a) `lo_lower_bound_fw`: the certified `lo_lower_bound` for `IsWitnessRunFW ρ`, `0 ≤ ρ < 1`, with `d ≤ (1−ρ/2)D_{α_i}`; the
  conclusion as certified (`P(α̂ < α_i) ≤ 2B·exp(−2(⋯)²/(Δ_φ²r)) + J·epsN(⋯)`). T20(b) `lo_consistency_fw`: the certified
  `lo_consistency` (the three sentences of `prop:loconsistency`) for families of `IsWitnessRunFW ρ ∧ IsSizedRun` runs. Faithful.
* T22(b) `same_quantile`: for `κ, Δ_φ`, `0 < a₁ < 1`, `c₀ > 0`, `v²_min ∈ (0,4]`, `δ, η ∈ (0,1)` with `η < (1−δ)/2` there are `C, N₁`
  such that for every `a₀ ∈ (0, a₁)`, every (A1)–(A2) `φ` with the bounds of T11, three points with `f(x₁) = 1`, `f(x₂) = 0`,
  `f(x₃) = −1`, `c₀ ≤ 1/‖f‖`, all `n, m` with `n∧m ≥ max(N₁, 10, c_lo²/(a₁−a₀)²)` and every run with
  `IsWitnessRun φ (rootGrid N) δ (1/2) v²_min ∧ IsDefaultRun`, the error `e = TV − α̂` has `P(e > C N^{−1/2}) ≤ η` at every pair of `𝓜`,
  `P(e > r) > η` for every `r < c_lo N^{−1/2}` at some pair of `𝓜`, and `c_lo ≤ C`. Faithful; encoding: `∃ C N₁` before `∀ a₀`, no
  `sInf` (generalisation: any witness run with the default batches, the paper run included by T5).
* T24 `dbar_le_D_le`: under (A1), `α⋆ < 1` and `α ∈ [0, α⋆]`: `D̄_α ≤ D_α ≤ D̄_α/(1−α⋆)`. Faithful.
* T25 `margin_dbar_factor`: under `PolyMargin c₀ γ` with `α⋆ < 1`: `ω(e) = (1−α⋆)c₀e^γ` is nondecreasing and nonnegative on `[0, α⋆]`
  with `ω(e) ≤ D̄_{α⋆−e} = (1−α⋆+e)D_{α⋆−e}`; for every `t ≥ 0`, `ω^←(t) = min{α⋆, (1−α⋆)^{−1/γ}(t/c₀)^{1/γ}}`; and
  `(1−α⋆)^{−1/γ} ≥ 1`. Faithful; encoding: "loses a factor `(1−α⋆)^{1/γ}`" read as the error term divided by it; the identity
  `D̄_{α⋆−e} = (1−α⋆+e)D_{α⋆−e}` and `(1−α⋆)^{−1/γ} ≥ 1` are the two extra conjuncts.
* T26 `any_threshold_converse`: under (A1)–(A2), `‖φx − φx′‖ ≤ D`, `α⋆ < 1`, `δ′ ∈ (0,1)`, `n, m ≥ 1`: one measurable event `E⁺` of
  probability `≥ 1 − δ′` on which, for every `τ : ℝ → ℝ` and every `ε ∈ [0, α⋆]` with `D_{α⋆−ε} + τ^A(α⋆−ε, δ′) ≤ τ(α⋆−ε)`,
  `α̂_an = alphaHat(D̂, τ) ≤ α⋆ − ε`. Generalisation (no validity or monotonicity of `τ`; one event for every `τ`).
* T27 `bangbang_aos`: for strongly measurable `φ`, `α ∈ [0,1)`, `n, m ≥ 1`, with `𝒯` the exact minimizers of `eq:qp`: `𝒯` is nonempty,
  convex, compact; every `(w,v) ∈ 𝒯` gives the same unnormalized `d̂`, of minimal norm in `𝒞_α(P_n) − 𝒞_α(Q_m)` and of norm `D̂_α`; if
  `D̂_α > 0`, with `t̂_n` the `(n_α+1)`-th smallest `d̂(X_i)` (`+∞` if `n_α = ⌊n(1−α)⌋ = n`) and `ŝ_m` the `(m_α+1)`-th largest `d̂(Y_j)`
  (`−∞` if `m_α = m`): `w_i = β/n` below `t̂_n`, `0` above, the ties share `1 − (β/n)#{below}`, and symmetrically for `v`; if `D̂_α = 0`,
  `𝒯` is the set of capped pairs with equal weighted embeddings. Faithful (the AoS wording of §2 :203-220; `EReal` cuts).
* T28(a) `tv_one_sided_ks`: `P, Q` on `ℝ` with measurable Lebesgue densities `p, q`, `p ≥ q` a.e. on `(x₀, ∞)` and `p ≤ q` a.e. on
  `(−∞, x₀)`: `TV = P(x₀,∞) − Q(x₀,∞) = F_Q(x₀) − F_P(x₀) = sup_x {F_Q(x) − F_P(x)} = KS⁺_{P,Q}(id)`. T28(b) `ks_lower_confidence`: for
  every pair on `ℝ`, `n, m ≥ 1`, `δ ∈ (0,1)`, with `L̂ = KS⁺_{P_n,Q_m}(id) − t_n − t_m`, `t_k = √(log(2/δ)/(2k))`: `P(L̂ ≤ KS⁺) ≥ 1−δ`;
  `KS⁺ ≤ TV`; `P(L̂ ≤ TV) ≥ 1−δ`; with probability `≥ 1−2δ`, `L̂ ≤ KS⁺ ≤ L̂ + 2(t_n + t_m)`; and
  `2(t_n + t_m) ≤ 4√(log(2/δ)/2)(n∧m)^{−1/2}`. Faithful; encoding: measurable densities.
* T29(a) `contact_densities`: `U ⊆ ℝ^d` open connected, `P ≠ Q` probability measures on `U` with densities `p, q` continuous and
  nonnegative on `U`, `{p = q}` with empty interior in `U`: the supports of `P − P⊓Q` and `Q − P⊓Q` meet; and if `α⋆ < 1`, for every
  continuous (A1)–(A2) `φ`, every limit of `(1−α⋆+ε)D_{α⋆−ε}/ε` as `ε ↓ 0` is `0` and no `c₀` gives `PolyMargin φ P Q c₀ 1`. T29(b)
  `contact_gauss_mix`: two distinct finite mixtures of nondegenerate Gaussian laws on `ℝ^d` are probability measures with continuous
  nonnegative densities `gaussMixDens`, equal on no open set, `α⋆ < 1`, meeting excess supports, and the conclusions of (a) for every
  continuous (A1)–(A2) `φ`. T29(c) `minimax_class_apart`: for continuous (A1)–(A2) `φ` on a Borel space, every pair of `𝓜(a₀, a₁, c₀)`
  (`a₀ > 0`, `a₁ < 1`) has disjoint excess supports, and no pair as in (a) lies in `𝓜`. Faithful; encoding: `𝒳 = U` a subtype,
  densities nonnegative on `U`.
* T31 `default_pairs_three_quarters`: for nearest-integer boundaries (any tie-breaking, any `n, m`),
  `|defaultPairs − ¾ min(n,m)| ≤ 3/2`. Faithful ("about `¾ min(n,m)`").
* T32 `house_encoding`: for `φ` into a complete separable Borel `ℋ`, `κ ≥ 0`, `x ↦ ⟨φx, φx′⟩` measurable for every `x′` and
  `⟨φx, φx⟩ ≤ κ²`: `φ` is measurable and strongly measurable with `‖φx‖ ≤ κ`, and `g • φ` is Bochner integrable for every probability
  `P` and bounded measurable `g`; and for a Mathlib `RKHS ℝ H 𝒳 ℝ` with kernel measurable in its first argument and `k(x,x) ≤ κ²`, the
  canonical feature map is strongly measurable with norm `≤ κ`. Faithful (Pettis, S1 :6); encoding: `κ ≥ 0`.
* T33 `witness_unique`: under (A1)–(A2), `α ∈ [0,1)`: `𝒞_α(P) − 𝒞_α(Q)` is nonempty, convex and compact, has exactly one element of
  minimal norm, and every such element has norm `D_α` and is `a − b` with `a ∈ 𝒞_α(P)`, `b ∈ 𝒞_α(Q)`. Faithful.
* T34(a) `contam_equiv`: for `α ∈ [0,1]`, `TV ≤ α` iff `P = (1−α)R + αP₀` and `Q = (1−α)R + αQ₀` for some probability measures
  `R, P₀, Q₀`; and `TV` is the least such `α`. T34(b) `trimming_removal`: for `α ∈ [0,1)`, the laws with a trimming density
  `≤ (1−α)⁻¹` with respect to `P` are exactly the `(P − ν)/(1 − ν(𝒳))` with `ν ≤ P`, `ν(𝒳) ≤ α`. T34(c) `different_fractions`: if
  `(1−α₁)R ≤ P` and `(1−α₂)R ≤ Q` for probability measures and `α₁, α₂ ∈ [0,1)`, then `TV ≤ max(α₁, α₂)`. Faithful (mixtures and
  renormalisation as declared).
* T35 `kernel_constants`: for `d ≥ 1`, `σ > 0`, `g` the Gaussian or the Laplace profile and any `φ` on `ℝ^d` with
  `⟨φx, φy⟩ = g(‖x−y‖)`: `‖φx‖ = 1`; `‖φx − φy‖² = 2 − 2g(‖x−y‖) < 2`; `√2` is the least upper bound of `‖φx − φy‖`, not attained.
  Faithful (`κ = 1`, `Δ_φ = √2`).
* T36 `regions_nested`: under (A1): `𝒞_α(P) ⊆ 𝒞_{α′}(P)` for `0 ≤ α ≤ α′ < 1`; `𝒞_0(P) = {μ_P}`; `α ↦ D_α(P,Q)` is nonincreasing on
  `[0,1)`. Faithful.
* T37 `bathtub_quantiles`: for a probability `R`, bounded measurable `f`, `α ∈ [0,1)`: `t` maximizes `s ↦ s − βE_R(s − f)_+` iff `t` is
  a `(1−α)`-quantile of `f` under `R`, and `u` minimizes `s ↦ s + βE_R(f − s)_+` iff `u` is an `α`-quantile. Faithful ("exactly").
* T38 `excess_bathtub`: (G) for nearest points represented as `a = ∫gφ dP`, `b = ∫hφ dQ` with trimming densities `g, h`,
  `‖a − b‖ = D_α > 0`, any `(1−α)`-quantile `t` and `α`-quantile `u` of `f⋆ = ⟨(a−b)/‖a−b‖, φ·⟩`, and the parts `P′ = (1−α)g·P`,
  `Q′ = (1−α)h·Q`: every `P″ ≤ P` has `∫f⋆ dP″ ≥ ∫f⋆ dP′ + t(P″(𝒳) − (1−α))`, every `Q″ ≤ Q` has `∫f⋆ dQ″ ≤ ∫f⋆ dQ′ + u(Q″(𝒳) − (1−α))`,
  `P′ = P` on `{f⋆ < t}`, `P′{f⋆ > t} = 0`, `Q′ = Q` on `{f⋆ > u}`, `Q′{f⋆ < u} = 0`; (Pr) the same at the printed objects with
  representing densities. Generalisation in (G) (any quantiles and densities, no (A3)); encoding: (G) drops `a ∈ region`.
* T39 `excess_identity`: (G) for region points `a, b` at distance `D_α > 0` and any quantiles `u < t`:
  `E_Pψ − E_Qψ − α = (D̄_α + ∫(u − f⋆)_+ dP + ∫(f⋆ − t)_+ dQ)/(t − u)` with `ψ = ramp f⋆ t u`; (Pr) the same at `t⋆, u⋆`. Faithful.
* T40 `excess_i`: (G) (i-1) if `u < t`, `E_Pψ − E_Qψ − α ≥ (1−α)D_α/(t − u)`; (i-2) for every `α′ ∈ [0,1)`,
  `(1−α′)D_{α′} ≥ (1−α)D_α − (t − u)(α′ − α)`; (Pr) `D_α ≤ t⋆ − u⋆`, `D_α > 0` (Pr-0), and (i-1), (i-2) at `t⋆, u⋆`. Faithful (the
  supporting line of the convex rescaled path, main :253-255); encoding: (G) (i-2) without `u < t`.
* T41 `excess_ii`: (G) for `0 < α⋆ < 1`, `γ, c₁, c₂ > 0`, `0 < ε₀ ≤ α⋆` with `c₁e^γ ≤ D_{α⋆−e} ≤ c₂e^γ` on `(0, ε₀]`, every
  `ε ∈ (0, ε₀/2]`, nearest points at `α = α⋆ − ε` and any quantiles `u < t`: `(1−α⋆)c₁ε/(2^γ c₂) ≤ E_Pψ − E_Qψ − α ≤ ε`; (Pr) the same at
  `t⋆, u⋆` under Assumption 2.1. Faithful; encoding: `γ > 0` (the print has no restriction).
* T42(a)–(c) `excess_laplace`: Laplace Gram `e^{−|x−y|/σ}` on `ℝ`, (G) region points at distance `D_α > 0` and any quantiles `u < t`:
  `u ≤ f⋆ ≤ t` on `ℝ`; `E_Pψ − E_Qψ − α = (1−α)D_α/(t − u)`; `P{f⋆ = t} ≥ α` and `Q{f⋆ = u} ≥ α`; (Pr) the same at `t⋆, u⋆`. Faithful;
  encoding: no `κ`. T42(d) `laplace_green`: for `σ > 0`, every compactly supported `C²` `ψ` has
  `∫e^{−|x|/σ}(ψ − σ²ψ″) = 2σψ(0)`, and `k(x+h,y) + k(x−h,y) − 2k(x,y) ≤ 2(cosh(h/σ) − 1)k(x,y)` for `h > 0`, with equality when
  `|x − y| ≥ h`. Faithful (the printed distributional identity as a test-function identity, and its discrete form used by the proof).
* T45 `oscillation_blind`: for any (A1)–(A2) `φ : ℝ → ℋ` and a measurable 1-periodic `ς` with `∫₀¹ς = 0`, `|ς| = 1`: for every integer
  `ν ≥ 1`, `Q_ν = oscLaw ς ν` is a probability measure and `TV(P_u, Q_ν) = ½` (`P_u` Lebesgue on `[0,1]`); `‖μ_{Q_ν} − μ_{P_u}‖ → 0`;
  `D_α(P_u, Q_ν) ≤ ‖μ_{P_u} − μ_{Q_ν}‖` for `α ∈ [0,1)`, `ν ≥ 1`; and for every `ε > 0`, eventually `D_α(P_u, Q_ν) ≤ ε` for every
  `α ∈ [0,1)`. Faithful; encoding: `𝒳 = ℝ`, laws carried by `[0,1]`, the supremum over `α` written uniformly.
* T46(a) `fncert_drift_err`: for jointly measurable `[0,1]`-valued `F` of (batch 0, point), at every sample
  `Δ = E_P f̂ − E_Q f̂ = α⋆ − err(f̂)`. Faithful. T46(b) `fncert_upper`: the single-function certificate (ramp `f̂ = F(batch 0)` at every
  batch and level), any batch pairing, any admissible fractions with cap `c ≤ 1`, nonnegative strictly increasing levels, `δ ∈ (0,1)`:
  `P(α̂ > max(Δ, 0)) ≤ δ` for every value of batch 0 and unconditionally. T46(c) `fncert_rejected_upper`: likewise
  `P(α̂ is a grid level whose test rejected, and Δ ≤ α̂) ≤ δ`. Generalisation: any batch pairing (the print fits on half of the data).
* T46(d) `fncert_betting_error`: for `δ, η ∈ (0,1)`, `v²_min ∈ (0,4]` and `J` there is `C ≥ 0` such that for every setting of (b) with
  the fractions of `eq:fractions` (`λ_max = ½`, any `w₀ > 0`, a prior rule, every pair bet on), `N ≥ 1` pairs and `h ≥ 0`: for every
  value of batch 0 at which `h` bounds the mesh below `Δ`, with probability `≥ 1−η`, `α̂ ≥ Δ − h − C/√N` and
  `α⋆ − α̂ ≤ err(f̂) + h + C/√N`; the same unconditionally when the mesh bound holds at every sample; and for the single split (`nb = 1`,
  printed pairing, boundaries within one of `n/2`, `m/2`), `N = min(n_[1], m_[1]) ≥ (n∧m)/2 − 1`. Faithful; encodings as declared (`N ≥ 1`,
  `h ≥ 0`, every pair bet on, `∃ C` before everything but `δ, η, J, v²_min`, any batch pairing).
* T47(a) `laplace_qdens_fails`: Laplace Gram on `ℝ`, Assumption 2.1, `0 < α < α⋆ < 1`, nearest points `a, b`: there is `t` with
  `P(d⋆(X) = t) ≥ α` (`d⋆ = a − b`), `t` is the unique `(1−α)`-quantile of `d⋆(X)` under `P`, and `QDensity P d⋆ t r c C` fails for
  every `r > 0` and all `c, C`. Faithful. T47(b) `finite_support_not_qdens`: if `P` is carried by a finite set, (Q) fails for every
  measurable `f`, every `t`, `r > 0`, `c > 0`, `C`. `margin_without_qdens`: on `Fin 3` with the basis feature map, `P = ½δ₀ + ½δ₁`,
  `Q = ½δ₀ + ½δ₂` satisfy `PolyMargin c₀ 1` for some `c₀ > 0`, and (Q) fails for `P` for every `f`, `t`, `r > 0`, `c > 0`. Faithful (the
  non-implication needs the instance).
* T48(c) `alg_prior`: on every paper run under the run hypotheses of T5, Algorithm S1's initial variance `algPrior R` is a prior rule,
  takes values in `[10⁻⁴, ½]` on the batches bet on, and some run with the same bets and ramps and this prior is again a paper run.
  Faithful (S3 :153-154 "Algorithm S1 gives ours").
* T49(a) `kernel_run_valid`: for a measurable parameter space, a jointly measurable kernel family and an `IsKernelRun` with a grid,
  `δ ∈ (0,1)`, `λ_max ∈ (0,1]`, `v²_min > 0`, `w₀ > 0` and quantile rules: the run is admissible, and for every `P, Q`, rejection at every
  true-null level has probability `≤ δ` and `P(α̂ > TV) ≤ δ`. Faithful ("Validity is unaffected"; no positive definiteness, no bound, no
  feature map). T49(b)(i) `median_bandwidth`: for measurable, nonnegative, symmetric `ρ` with `ρ(a,a) = 0`, `medianBw ρ` is measurable
  and positive. T49(b)(ii)–(iii) `kernel_profiles`: `lapK`, `gaussK` are jointly measurable in `(θ, x, y)` with values in `[0,1]`;
  `scaledDist s` is measurable, nonnegative, symmetric, zero on the diagonal; `b0Scale` is measurable and positive. Faithful; encodings:
  numpy's median as the average of two order statistics of the `k²` ordered-pair distances, the subsample as a fixed index selection
  (prose), `|σ|` making `lapK` total.
* T50(b) `averaged_evalue`: for `S ≥ 1` admissible runs on the same data and a grid: under `H_{0,α_j}` each horizon wealth has
  `E K^{(s)}_N ≤ 1`; `P(S⁻¹Σ_s K^{(s)}_N ≥ 1/δ) ≤ δ`; and the grid read upward on the averaged tests gives `P(α̂_avg > TV) ≤ δ`.
  Faithful. T50(c)–(d) `bound_summaries`: on any measure space, two `δ`-level bounds give a `2δ`-level bound for their maximum; and on
  nonnegative levels the down-closed bound read on an initial segment of a grid is at most that of the whole grid. Faithful.
* T51 `trimming_at_lower`: under (A1)–(A3), `0 < α⋆ < 1`, `δ, δ′ ∈ (0,1)`, `n, m ≥ 1`, for every measurable `α̃ ≥ 0` with
  `P(α̃ > α⋆) ≤ δ`: an event `E` with `P(E ∩ {α̃ ≤ α⋆}) ≥ 1 − δ − 2δ′` on which, when `α̃ ≤ α⋆`, every exact minimizer at level `α̃` has the
  two bounds of Proposition 6.2 (`r_n + ω_C(D̂_{α̃} + r_n + r_m)` for `P`, and its mirror for `Q`). Faithful (Proposition 6.2 composed).
* T52 `propensity_core`: `π ∈ (0,1)`, measurable nonnegative densities `p, q` with respect to `P + Q`, `ρ = πp + (1−π)q`, `e = πp/ρ`
  (`0` where `ρ = 0`): `min(p,q) = ρ min{e/π, (1−e)/(1−π)}` where `ρ > 0`, and `TV(e#P, e#Q) = TV(P,Q)`. Faithful.
* T53 `tv_pushforward`: `TV(f#P, f#Q) ≤ TV(P,Q)` for measurable `f`; with densities with respect to `P + Q`,
  `P(p > q) − Q(p > q) = TV(P,Q)` and every measurable `ψ : 𝒳 → [0,1]` has `E_Pψ − E_Qψ ≤ TV(P,Q)`. Faithful.
* T54 `upper_end`: under `PolyMargin c₀ γ`, for `α ∈ [0,1)` and every `Ď ≥ D_α(P,Q)`: `α⋆ ≤ α + (Ď/c₀)^{1/γ}`. Faithful (no measurability
  or bound on `φ` needed; generalisation).
* T55 `margin_eps0`: under (A1), `c₀ > 0`, `γ ≥ 1`, `0 < ε₀ ≤ α⋆` and `c₀ε^γ ≤ D_{α⋆−ε}` for `ε ∈ [0, ε₀]`:
  `PolyMargin φ P Q (c₀(ε₀/α⋆)^γ) γ`. Faithful (the printed `(0, ε₀]`; `ε = 0` is trivial for `γ ≥ 1`).
* T56 (the analytic estimator at `τ = τ^P`, with `κ̄ = √min(κ², Δ²/2)` and `ρ̄ = Δ` in `Wave30tp.tauP` for (c)–(e)): (a) `taup_jump`:
  for `D > 0`, any `v, ρ̄ ≥ 0`, `δ ∈ (0,1)`, `n, m ≥ 1`, there is `c > τ^P(0)` with `τ^P(α) ≥ c` for all small `α > 0`; (c)
  `taup_welldefined`: under (A1)–(A2), `D > 0`, `n, m ≥ 1`, the crossing set is nonempty for every sample; (d) `taup_valid_bound`:
  for `α⋆ < 1`, one event of probability `≥ 1 − δ` on which `α̂_an ≤ α⋆`, every level `α ∈ [0,1)` with `D̂_α > τ^P(α)` is `< α⋆`, and
  every grid read upward gives a bound `≤ α⋆`; (e) `taup_consistent_below`: under (A1)–(A3), `α⋆ < 1`: `P(α̂_an < α) → 0` for every
  `α ∈ [0, α⋆)`. Faithful.
* T57 `bayes_risk`: `inf_A ½{P(Aᶜ) + Q(A)}` over measurable sets equals `(1 − TV)/2`; and for every `α̃` on any measure space with
  `μ(α̃ > TV) ≤ δ`, `μ((1 − α̃)/2 < R⋆) ≤ δ`. Faithful; encoding: the Bayes risk over deterministic classifiers (see Notes).

## Junk-value audit
`ordStat` is read only at ranks in `[1, k]` (`lowQ`/`highQ` by their `max 1`, `min k` guards, inactive at grid levels by T1(d); T1(c)'s
docstring records the junk `sInf univ = 0` at `r = 0`); the cut rules are applied only for `k ≥ 1` (`has` requires both fitting sides
nonempty). `ownX`, `ownY`, `witness`, `kwit`, `kownX`, `kownY` divide by `D̂` (`qpVal`, `kqpVal`) and are read only where `D̂ > 0` (a
clause of `has`); `kqpVal`'s `max 0` only makes it total (inactive for a positive semidefinite kernel); `ramp` divides by `t − u` and is
read only where `u < t` (`has`, the (G) hypotheses, `t⋆ − u⋆ ≥ D_α > 0` in (Pr)). `fracFormula` divides by `N·max(v²_min, ·)` with
`v²_min > 0` and by `w₀ + |S|` with `w₀ > 0`, and is used only for pairs `k < N`. `algPrior` is `1` off the batches bet on (never read)
and divides by the sizes of batch `b`, positive at every batch holding a pair (elsewhere `x/0 = 0` keeps it in `[10⁻⁴, ½]`); `empVar` of
an empty sample is `0`. `splitStart` uses ℕ division by `K`, read only for `1 ≤ K ≤ M`. `medianBw` is `1` when all distances vanish
and uses ℕ subtraction and halving of counts (`zeroCount ≤ k²`); `b0Scale` is `1` where the variance vanishes (as in the code); `lapK`
uses `|σ|`, `gaussK` divides by `2σ²` (`/0 = 0` makes both total; the runs read them at `σ > 0`).
`fwSep` takes `sInf`/`sSup` of images of the capped simplices, nonempty and compact exactly when a capped pair exists, and is read only
at a capped pair. `alphaZeroWit` at `n = 0` or `m = 0` uses weights `1/0 = 0` and is read there only as a measurable function. `ksGate`
gates only pairs `k < N`. `ksRadius` is used at `k ≥ 1`. `oscLaw` is a probability measure for `ν ≥ 1` only, and the claims use it there
or in a limit `ν → ∞`. `ENNReal.ofReal` of a negative number is `0` (a true, weaker bound). `alphaHat` is an `sInf`: T56(c) proves the
crossing set nonempty when `D > 0`; in T26 the hypothesis puts `α⋆ − ε ∈ [0,1)` in it; in T56(d)–(e) an empty set would give `0`, which
works against the conclusions. `iSup` in T28(a) is of a function bounded by 1; `iInf` in T57 is over a nonempty type of values in
`[0,1]`; `⨅ b : Fin (nb+1)` in T5 is over a nonempty index. `genInv` in T10, T25 at `c₀ > 0`; every `Real.rpow` base is nonnegative or
positive (`1 − α⋆ > 0`, `Ď ≥ D_α ≥ 0`, `ε₀/α⋆ > 0`, the bracket of T8). `Measure.map` occurs only along measurable maps (T15 `X_i`, T52
the propensity score, T53 `f`). Bochner integrals in `ℋ` are of bounded strongly measurable maps (hypotheses), and the T14 integrals
against empirical measures are guarded by `StronglyMeasurable φ`; `fnDrift` integrates a bounded jointly measurable `F`. `ksPlus` reads
`P.real` of sets that may be non-measurable when `f` is not (T16): the outer-measure reading, a generalisation. `deriv` is read in T13 at
a differentiable witness and in T42(d) at a `C²` function. Vacuity: every hypothesis set has a witness — paper runs by T4 (and the
scratch witnesses `paperRun_ex`, `paperRun_ex1`), kernel runs by the scratch `kernelRun_ex`, `𝓜` by `margin_without_qdens`, the T29
pairs by T29(b), nearest points and the printed quantiles by T33 and the quantile lemmas of the route, T17 runs with `h ≡ 0`, T46 with a
constant `F` (see Notes for the feature maps).

## Rows only / not claimed
* T48(a) (Algorithm S1 line 9: the own-term values are the frozen `ownX`, `ownY`, definitional), T48(b) (line 10: the cut points are
  `lowQ`, `highQ` at the grid level, by T1(d)), T48(d) (lines 13–17: stop and return are the frozen `LoRun.alphaLo`): rows.
* T50(a) (the minimum over splits is `δ`-level: the certified `Wave30tk.split_min_median`), T50(e) (three events of probability `≥ 1−δ`
  meet with probability `≥ 1−3δ`): rows.
* T56(b) (bisection brackets `α̂_an`: the certified `Wave30tu.Crossing.crossing_nc` at `τ^P`, nondecreasing by `plugin_monotone`): row.
* D1 `lem:plugin` (Lemma S2.2): rows with the AoS label for `Wave30tp.plugin_det`, `plugin_det_zero`. D2 `thm:loratemain` (Theorem 5.7):
  rows for `Wave31tl.lorate_O`, `same_rate` (and T8). D3: the renaming table for the AoS map and this card (`1/n+1/m = s → 1/n⋆`,
  `v → κ̄`, `D_φ → Δ_φ`, `Z → Γ`, `h → Δ_𝒢`, `h₀ → Δ_min`, `a, b → g_P, g_Q`, `θ → ϱ`, `g → ψ`, `α̂_lo → α̂`, analytic `α̂ → α̂_an`,
  `σ₀ → v₀`, `σ²_min → v²_min`, `u(α) → D̄_α`, `ψ̆⋆ → ψ⋆`, Laplace `ℓ → σ`, `D_* → D̲`, and the rest in the source). D4: the
  `prop:bangbang` row points to `bangbang_v2` and T27. D9: the reader-page printed numbers and line ranges at `b3125cf`, the rows of the
  dropped labels removed (certificates stay valid), `alg:split` (T48) and the 31tu labels added. D12 (coordinator): the map's prose on
  Remark S5.5.
* For a positive semidefinite kernel with feature map `φ_θ`, `kqpVal`, `kwit`, `kownX`, `kownY` equal `qpVal`, `witness`, `ownX`,
  `ownY` (row, used by no proof).
* Dropped with their printed text (certificates of the old claims stay valid, off the map): T21, T22(a), T23, T30, T43, T44.
* Classified, not claimed, per item: main :224-226 (T22: a row and a meta sentence); S4 :863-864 and "may fail for every `ε` when
  `τ = τ^P`" (T26, meta); the Green-function remark S4 :979-980 (T42, methodological); "whether (Q) can hold for the Laplace kernel in
  `ℝ^d` is open" (T47(a)); the scope and heuristic sentences of T49 (§4 :167-173, S3 :360); the numerical and heuristic sentences of T50;
  the cited readings of T52 and T57; "both tests are valid", "neither is a proven ceiling" (T53); the citation and meta half of T54; the
  classified sentences of T56 (§3 :48-49 is 31ts U8, `eq:samplesize` the certified `Wave31ta.samplesize`, §3 :55-57 numerical, §3 :76-77
  31ts U2); the excess-block sentences and Figure 2 (`pop_ramp_rkhs`, numerical, 31tq Q22, 31tu).
* Declared, not claimed (the source's list): E11 (the heuristic reading of the trimming; its mathematical parts are rows, T27 and
  `bangbang_v2`); E12 (the numerical checks, S6.4); E13 = B1 (31tp L29) and E16 (covered by `newrates_i`); the meta sentences (main
  :225-226, S4 :863-864, "may fail for every `ε` when `τ = τ^P`"); the scope remarks on consistency (S3 :360, S4 :295, S3 :199-200,
  §4 :167-173; their validity half is T49); the numerals and heuristics of §4/S3 (`cstBetRatioEighty`, "comes close to the best
  constant fraction", "constants grow like `1/v²_min`", "an artifact of the proof", "the logarithm of the wealth grows linearly in
  `k`"); the critic's group (D) (§4 :138-140, S3 :122-124 and §7 :23-26, the limit law of §1 and §3 :23-25, the support-function and
  ν-SVM readings); every Monte Carlo number; E2, E4 and the Matérn closed form; the 31ts procedure-level claims not moved into T49–T50
  (U2, U4(a), (c), (d), U5–U8, U9(a), (d)–(g)), open on the AoS map until 31ts is certified.
* Open on the map: the Audibert–Tsybakov rate half of §8 (:12-16), queued for the `ℝ^d` wave (decision 4).

## Notes for the auditor
* Unused or weaker hypotheses reported by the proof helpers (generalisations): T16(a) `ksPlus_locally_constant` uses none of
  `Measurable f₀`, `Measurable f`, `MeasurableSingletonClass` (`ksPlus` reads `P.real` of the up-sets); T17(c) `alpha0_gate` uses neither
  `‖φ‖ ≤ κ` nor the separability of `ℋ`; T17(a) needs no measurability hypothesis on `φ` (continuity follows from the Gram function),
  and the frozen claim states none; T46(b) `fncert_upper` does not use `StrictMono α` (only (c) does, to read "`H_{0,α̂}` rejected" as a
  down-closed run); T56(e) `taup_consistent_below` does not use `D ≤ 2κ` (`D > 0` follows on the event from `D ≥ D̂_α > τ^P(α) ≥ 0`); the
  positivity of `medianBw` needs only `ρ ≥ 0` (symmetry and the zero diagonal are not used); `fw_gap`'s side conditions `n, m ≥ 1`,
  `0 ≤ α < 1` are forced by the capped pair (`FrankWolfe.isCapped_params`).
* Constants and routes the helpers reported that bear on reading the statements: T46(d)'s constant is
  `FnCert.betC δ η v²_min J = max{√(8L), (L + 16L/v²_min + √((4L/v²_min) log((J+1)/η)))/√(L/2)}`, `L = log(1/δ)` (per-level failure
  `≤ η/(J+1)`), so it depends only on `δ, η, J, v²_min` as the statement's quantifier order says; T51 goes through the certified
  `Wave30tx.alphahat` at the constant threshold `τ ≡ 2κ` (valid by `Demp ≤ 2κ`) and a union bound; T45 goes through
  `oscLaw ς ν = Wave30tj.blindLaw ς ν` and the certified `blind_construction`, `blind_mmd`, `riemann_lebesgue_periodic`; T37 through
  the certified `Wave30tj.lowertrim_shape` on `R.map f`; `margin_without_qdens` through the certified `Wave31tb.separated` with
  `f = (0, 1, −1)`, `c₀ = 2/‖f‖`; T50(b)'s `E K_N ≤ 1` by the supermartingale (no optional stopping), with the hypotheses of the certified
  `Wave30tv.core_level` (copied with attribution into `Lib/KernelRun/HorizonWealth.lean`); T20's routes are attributed copies of the
  `Wave30tz` routes, and T20(b)'s validity is the certified `lo_upper` unchanged; T19's last inequality is proved term by term rather
  than through the monotonicity of `x ↦ (1−ρ/2)x − c/x` (same conclusion); T22(b) gets the measurability of `α̂` from `lo_upper` at the
  pair `(δ_{x₁}, δ_{x₁})`; T56(d) uses the certified `plugin_one_event` directly, and its grid conjunct needs only that every rejected
  grid level lies below `α⋆`; `π (b + 1)` in T5's `IsSizedRun` constant elaborates as `π (↑b + 1)` (ℕ addition), so the infimum is over
  `b ∈ {0, …, nb}`.
* Encoding choices made at drafting are listed under Encodings; each is restated in its bullet above.
* Points where the frozen statement and the source prose differ in scope (stated as drafted, for checking): T57's Bayes risk is the
  infimum over measurable sets (deterministic classifiers); the source's route adds that randomized classifiers `h : 𝒳 → [0,1]` give the
  same infimum, which is not a conjunct. T49(b) gives the ingredients (`medianBw` for a fixed `ρ`, the profiles, `scaledDist`,
  `b0Scale`); that the three printed bandwidth rules are measurable functions of the batches before `b` (the real-data rule through
  `medianBw (scaledDist ŝ) z = medianBw (scaledDist 1)(z/ŝ)`) is source text (critic note n1, route text only), not a frozen conjunct.
  T16(b)'s docstring says "the smallest gap is one"; the statement quantifies over every admissible `g₀` and asserts nothing about the
  smallest gap. T46(b)–(d) and T22(b) are stated for wider classes than the printed procedure (any batch pairing; any witness run with
  the default batches), and the printed instances follow through T2, T5.
* Non-vacuity of the feature-map hypotheses rests partly outside this wave: the Gaussian feature map (T13, T17, T35) is 31tp L15; the
  Laplace map on `ℝ` (T42, T47(a)) is the explicit `L²` map named in the source (T42) and in T35's docstring; the Laplace half of T35
  on `ℝ^d`, `d ≥ 2`, rests on positive definiteness by Gaussian subordination (31ts U6(b)), not certified here. `kernelRun_ex`
  (`𝒳 = Θ = Unit`, `kf ≡ 1`) and `paperRun_ex`, `paperRun_ex1` are scratch witnesses (`fullstack/work/scratch31tr/`), not frozen claims;
  the frozen non-vacuity of the paper run is T4.
* The existence conjuncts of T6–T12 are separate universal statements (`paperRun_exists_printed`, `paperRun_exists_fractions`) at the
  printed rule and `v₀ ≡ 1`, not instantiated at the binders of the universal conjunct; `paperRun_exists_fractions` allows
  `λ_max ∈ (0,1]`, which contains the `λ_max ≤ ½` of T7 and T12.
* The printed line numbers are those of `1fbc8df`; for T45's main-text summary and T54 see the post-freeze move under Source.
