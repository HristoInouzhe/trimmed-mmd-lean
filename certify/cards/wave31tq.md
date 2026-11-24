# Fidelity card — wave 31tq: the Fourier-analytic results of trimmed-mmd (**Annals of Statistics version**)

Lean: `StatFormal/Wave31tq/Statements.lean` (39 claim definitions for the drafted items Q1–Q29, with Q13, Q23, the parts
`newsobolev_cor_rate`, `rate_sobolev`, `exact_sobolev_A`, `rate_gauss_A`, `rate_gauss_split`, Q22 (b), (d) and Q27 (b-analytic) dropped
together with their printed text; 20 new definitions `ftA`, `ft2A`, `kHat`, `nativeA`, `sobolevA`, `lapC`, `ftMeasA`, `absPQ`, `tailOut`,
`tailPlus`, `IsCross`, `ExpTail`, `ftSigned`, `sMoment`, `cJ`, `sobConst`, `bbar`, `bbarE`, `bandH`, `bandB`; frozen 2026-11-23 before any
proof, freeze commit `5d9b27e` (on top of 31tr's documentation commit `f9ec247`), sha256
`1409e6af1524c7c1ebd84a98a18c7b3c6b8ef963c396009ea083fa7badaaa705`, locked in `certify/statements.lock` with its 117 local imports; the
file's docstring lists the encodings, junk values, declared extra hypotheses and freeze-time encodings). Routes (untrusted), by proof
chunk: A `RouteA1`, `RouteA2`, `RouteA5`, `RouteA6`, `RouteA7` (Q1–Q7); S `RouteSInt`, `RouteSNorm`, `RouteSThm`, `RouteSCor`, `RouteSOP`
(Q9–Q12); G `RouteG`, `RouteGStep`, `RouteGThm`, `RouteGRho`, `RouteGBand`, `RouteGAll` (Q14–Q17); T `RouteT18`, `RouteT19`, `RouteT20`,
`RouteT20a`, `RouteT20b`, `RouteT21`, `RouteT24` (Q18–Q20, Q21 for small `s`, Q24); M `RouteM21`, `RouteM22`, `RouteM25`, `RouteM26`,
`RouteM27`, `RouteM28`, `RouteMAll` (Q21, Q22, Q25–Q28); X `RouteXCore`, `RouteXGamma`, `RouteXHalf` (Q8, Q29); on the library folders
`StatFormal/Lib/{TVMeasure, AngularFourier, MollifierNorm, BandLimited, MomentTrim, CrossLaws, SupportSeparation, HalfSpace}`.
`Proofs.lean` defines the 39 theorems, each of type literally `Claims.X`; the route theorems named `_of` take other chunks' frozen claims
as hypotheses (`tv_density`, `sobolev_angular`, `bochner_angular`, `kernel_instances`, `newsobolev_cor_line`, `newmoments`,
`newgauss_thm_rho`), discharged there by the theorems proved above them, so every theorem is unconditional; all proved, `#print axioms`
propext, Classical.choice, Quot.sound for each (proof commit `b53c365`).
Paper id `trimmed-mmd (jmlr)` (face `Papers/TrimmedMMDJMLR`; the AoS version is tracked on this page, as for Waves 31tn–31tr). Branch
`tmmd-aos-fullstack` (worktree `~/projects/StatFormal-tmmd-aos`).
Scope (author decision, 2026-11-21, full-stack campaign `~/projects/tmmd-aos-brief/fullstack/CAMPAIGN.md`): the paper's own
Fourier-analytic results (main §5.2 and §5.4, supplement §S4.4–§S4.10), stated as printed in the paper's angular convention and composed
on the certified classical library of Wave 31tp (L1–L30) with no textbook bridge: `prop:newgammaone` (S4.5), `lem:newsobnorm` (S4.9),
`thm:newsobolev` (S4.10), `cor:newsobolev` (S4.11), `lem:newgaussstep` (S4.12), `thm:newgauss` (S4.13), `prop:newupperone` (S4.14),
`prop:newmoments` (S4.15), `prop:newsobolev` (5.5), `prop:newgauss` (5.6), the Fourier parts around `prop:newconverse` (S4.16), the
displays `eq:newnative`, `eq:newbochner`, `eq:newbandlim`, `eq:newmomentdecay` in the printed form, the unnumbered sentences that rest on
them, and the compositions that 31tr points at 31tq (`prop:excess` (ii) "under the hypotheses of Proposition 5.5", the simulated pairs of
S6.4). Closes GAPS A1–A11, E1, E5, E6, E8, E10 and the ℝ part of E4. Plan: `fullstack/PLAN_31tq.md`.
Critic (independent AI reviewer, before the freeze; files in `tmmd-aos-brief/fullstack/`): `CRITIC_31tq.md` (v1, 2026-11-21, against
trimmed-mmd `6ac0ca7`) NOT READY TO FREEZE (B1: Theorem S4.10 false as drafted for negative `Π_ρ` or `V_ρ`; the guards `0 ≤ Π_ρ`, `0 ≤ V_ρ`
added to Q11 and inherited by Q12 case 1); `CRITIC_31tq_v2.md` (diff-only, against `9599818`) READY TO FREEZE for the kept claims, with
the re-scope flags R1 (a split-sample claim for Corollary S4.11's "Hence") and R2 (no analytic `α̂` with the paper's threshold), settled
in v3; the coordinated F1 at `b3125cf`, `CRITIC_F1_b3125cf.md` §3 (2026-11-22): 31tq READY TO FREEZE, no blocking item (Q6 and Q25
ACCEPT-WITH-NOTE, depending on the paper corrections #6b and #6a, applied at `1fbc8df`); diff-only re-check `CRITIC_F1b_1fbc8df.md`: READY
TO FREEZE, no text note for 31tq. Change records: `DIFF_31tq.md` (v1 → v2), `DIFF_F1_b3125cf.md` (section 31tq, v2 → v3).
Fidelity review: independent AI audit, method v1 (certify/AUDIT_METHOD.md), 2026-11-23 — PASS with notes. Scope: all 39 claims,
back-translated from the frozen `Statements.lean` and its definitions before the paper was opened. The reviewer had read this card's header
while locating files, so the step was blind to the paper but not to the card. The 20 frozen definitions and the 13 verbatim claims were
compared by script with the critic's `Defs31tq.lean` (bae7218dacc56922) and `Shapes31tq.lean` (1e9303235590be62): byte-identical up to the
declared `lapC`, `tailPlus` and `CrossPair → IsCross … ∧ 0 < p x₀` substitutions (the last equivalent by currying). The 6 shapes with added
conjuncts differ from their scratch shapes only by those conjuncts. These 6 and the 20 claims drafted at the freeze were checked clause by
clause against the printed text at `1fbc8df` and the approved prose v3. The Fourier constants (inversion, Laplace, Gaussian, Matérn as a
Bessel potential, band-limited bound, `ĥ`, `‖h‖²`, `m₂ = π²`, the constants of Props S4.14–S4.15, `ℓ₀` of the simulated pairs) were
re-derived. Hashes: `Statements.lean` matches the lock; nothing frozen changed after `5d9b27e`, and the 31tu freeze `69f1ac7` touches no
31tq file. Q26 uses the certified 31tr `excess_ii` term itself (`RouteExcess.excess_ii_route`). `Proofs.lean` discharges every cross-chunk
hypothesis by a theorem proved above it, with nothing circular or assumed.

Findings: 8 claims faithful and 31 faithful with a note (generalisations, declared guards and encodings). There is no undeclared stronger
hypothesis, unguarded junk value, vacuous hypothesis set or restated conclusion. The F1 wordings (#6a τ^A converse, #6b "guarantees at
best", F2 one-sided O_P, F3, F6) are matched; the F1 hypersurface sentence is declared GMT and only its (G)-form is claimed. Q12's cases
without `b`, `m` are a strengthening (a mollifier always exists). Q28's `ℝ≥0` weights are the same measures, and its probability conjuncts
are what instantiating Props 5.5 and 5.6 needs.

Correction to the scope line above: 31tq closes GAPS A1, A2, A4–A11, E1, E5, E8, E10, the ℝ part of E4, and E6 except its logarithmic
half. For A3 (Prop S4.8(iii)) and the logarithmic rate sentences, 31tq supplies only the margin (Q22(c)) and the `ω_ℋ` bound (Q17); the
rate is 31tu Y26. The COVERAGE rows already say so. The last sentence of Proposition 5.3 is 31tr T29, not 31tq.

Gate: the tree has 31tu targets without proofs, so the gate was re-run on a temporary worktree at `9997d6d`:
* CERTIFIED 4161, also after rebuilding every 31tq module and the eight new Lib folders from source;
* ALIASES OK 4104;
* no escape hatch in the 67 changed Lean files.

Full audit: `tmmd-aos-brief/fullstack/AUDIT_31tq.md`. Non-blocking notes there:
* `docs/trimmed-mmd-aos.md` is to be regenerated at merge (it still says 31tq is in progress and attributes Prop 5.3's last sentence to 31tq);
* the line tables are to be refreshed at the next F1 (all 31tq statements are unchanged at master `92cd12c`);
* 48 of 377 new declarations lack a docstring, and there are four near-duplicate helpers (`withDensity_inf` with `Wave30tx`, smooth
  Urysohn and `withDensity_sub` with Mathlib, Gaussian pdf helpers with `Lib/GaussCoord`).

**Author: approved (automatic on AI-audit PASS, per author decision 2026-10-21).**

## Source
`~/projects/tmmd-aos-brief/fullstack/NEW_STATEMENTS_31tq.md` at freeze (v3, F1 at `b3125cf`, re-hashed at `1fbc8df`): whole file sha256
`678110f6fd66a776ffa0f1c252a7b216a5b3970c3041f087d1ccb8f5833e5943` (913 lines; copy committed in `5d9b27e` as
`certify/sources/tmmd-aos-NEW_STATEMENTS-wave31tq.md`, same hash); the claims block (line 87, "A. Common setting and encodings of
Wave31tq", to the end) sha256 `5c1f971660860cba9035a596706f509b9238a0eca89b2fa137e3982ddd996efe`. Earlier drafts kept as
`fullstack/work/NEW_STATEMENTS_31tq.v1.md` and `.v2.md` (sha256 prefix b99bf8aaf62e1306). Item numbers Q1–Q29, the setting §A, the
classification of every printed sentence in scope §I, the decisions §J (D1–D15) and the author items §K are those of the source.
Printed source: trimmed-mmd `aos/` at `1fbc8df` (the 11 wording corrections of `CRITIC_F1_b3125cf.md` §1, among them #6a and #6b on the
sentences of Q25 and Q6, and four length cuts on top of `b3125cf`). The sha256 prefixes of the cited files are listed at the top of the
source (the seven files changed since `b3125cf`, at `1fbc8df`: `sections/00_abstract` a3d7a240bff9, `01_introduction` 6cf223469dd0,
`05_rates` 9bcd992dbfab, `06_trimming` 725265e8156e, `07_numerical` d3a9002b1b03, `08_final` 9b6f55fb3a9f, `supplement/S4_rates`
58bf03da5e94; every other cited file, with `main.tex`, `supplement.tex` and `preamble.tex`, byte-identical to `b3125cf`). Printed
numbers: `aos/main.aux`, `aos/supplement.aux` (Props 5.5 `prop:newsobolev`, 5.6 `prop:newgauss`, 5.10 `prop:excess`; Thm 5.7 `thm:loratemain`; Props S4.5
`prop:newgammaone`, S4.14 `prop:newupperone`, S4.15 `prop:newmoments`, S4.16 `prop:newconverse`; Lemmas S4.9 `lem:newsobnorm`, S4.12
`lem:newgaussstep`; Thms S4.10 `thm:newsobolev`, S4.13 `thm:newgauss`; Cor S4.11 `cor:newsobolev`; equations S4.3–S4.6 `eq:newnative`,
`eq:newbochner`, `eq:newbandlim`, `eq:newmomentdecay`). Line numbers below are those of `1fbc8df`: `main` = `sections/05_rates.tex`,
`§1` = `01_introduction.tex`, `abs` = `00_abstract.tex`, `S4` = `supplement/S4_rates.tex`, `S6` = `supplement/S6_experiments.tex`.
After the freeze the author changed `05_rates`, `S4_rates` and `S6_experiments` (with other files) in `1721ee6`, `a9a0ce9`, `5218bfa`
("statements byte-identical"). Checked for this card at trimmed-mmd `663fe6e`: the 17 labelled environments that 31tq cites (the ten
results of this wave, the four equations, `prop:excess`, `thm:loratemain`, `prop:newconverse`) are identical to `1fbc8df` after whitespace
normalization, each one line earlier; the unlabelled sentences checked (S4 :371-372, :739-741, :841-842, :1026-1027, main :119-120, :125,
:138, :240-249, :281, S6 :157-175) are all still printed, one line earlier in main and in S4 up to :851, at S4 :1016-1017 for
:1026-1027, and 18 lines later in S6. The line tables are to be refreshed at the next F1.

## Targets (39 claims in `StatFormal.Wave31tq.Proofs`; all in `certify/targets.toml`, theorem = `StatFormal.Wave31tq.<name>`)
| item | label (abridged) | claim |
|---|---|---|
| Q1 | main :57-58, :81-85; S4 :302-304, :609-610 (P₀, Q₀, `err`, `\|P−Q\|`) | `tv_density` |
| Q2 | S4 :308-310 (`k̂₀ ≥ 0` integrable, inversion) | `spectral_angular` |
| Q3 | `eq:newnative` (eq. S4.3; S4 :310-316) | `native_angular` |
| Q4 | `eq:newbochner` (eq. S4.4; S4 :317-322) | `bochner_angular` |
| Q5 | S4 :530-533, :32-33; §1 :82; main :105-109 (Sobolev kernels) | `sobolev_angular` |
| Q6 | S4 :1026-1027 (E8, "needs `s > d/2`") | `sobolev_needs` |
| Q7 | main :108-109, :131; S4 :376-377, :657, :794-795 (the kernels named) | `kernel_instances` |
| Q8 | `prop:newgammaone` (Proposition S4.5; S4 :374-382) | `newgammaone` |
| Q8 | S4 :371-372 (E10) | `newgammaone_smooth` |
| Q9 | S4 :533-535 (the ℝ part of E4) | `translation_intervals` |
| Q10 | `lem:newsobnorm` (Lemma S4.9; S4 :537-549) | `newsobnorm` |
| Q11 | `thm:newsobolev` (Theorem S4.10; S4 :586-603) | `newsobolev_thm` |
| Q12 | `cor:newsobolev` (Corollary S4.11; S4 :620-627), case `T(ρ) = 0` | `newsobolev_cor_bounded` |
| Q12 | `cor:newsobolev`, case `d = 1` | `newsobolev_cor_line` |
| Q12 | `cor:newsobolev`, "Hence" (S4 :628-630, :646-647) | `newsobolev_cor_OP` |
| Q14 | `eq:newbandlim` (eq. S4.5; S4 :656-664) | `bandlimited_angular` |
| Q15 | S4 :664-666, :674 (`b̄`) | `bbar_even` |
| Q15 | S4 :664-670 (the density `b`) | `bandB_facts` |
| Q16 | `lem:newgaussstep` (Lemma S4.12; S4 :677-684, setting :664-666, :672-675) | `newgaussstep` |
| Q17 | `thm:newgauss` (Theorem S4.13; S4 :705-711) and S4 :739-741 (`ω_ℋ`) | `newgauss_thm` |
| Q17 | `thm:newgauss` (S4 :711-715) | `newgauss_thm_rho` |
| Q18 | `eq:newmomentdecay` (eq. S4.6; S4 :749-756) | `momentdecay_angular` |
| Q19 | `prop:newupperone` (Proposition S4.14; S4 :758-766) | `newupperone` |
| Q20 | `prop:newmoments` (Proposition S4.15; S4 :782-797) | `newmoments` |
| Q21 | `prop:newsobolev` (Proposition 5.5; main :105-117) | `newsobolev` |
| Q21 | main :119-120 | `newsobolev_E1` |
| Q21 | S4 :841-842 (proof of Proposition 5.5) | `newsobolev_upper_small` |
| Q22 | `prop:newgauss` (Proposition 5.6; main :128-136) | `newgauss` |
| Q22 | main :138, :257-258 | `newgauss_margin` |
| Q24 | main :124-126 ("sharp on the line at least when `s < 3/2`") | `sharp_line` |
| Q25(b) | main :240-242 (`thm:loratemain` under Proposition 5.5) | `rate_sobolev_split` |
| Q25(c1) | S4 :847-849, :882-884 (`prop:newconverse` composed, general form) | `converse_poly` |
| Q25(c3) | S4 :882-885, main :246-248 | `lower_sobolev_A` |
| Q25(e) | S4 :885-887, main :246-249 | `slow_gauss_A` |
| Q26 | `prop:excess` (ii) (Proposition 5.10; main :280-282, S4 :963-964) | `excess_sobolev` |
| Q27 | main :108-109, :119-120, :241-242, :256-259; S6 :173-175 (Laplace) | `laplace_instances` |
| Q28 | S6 :157-168; main :264-265 (the simulated pairs) | `simulated_pairs` |
| Q29(a)–(b) | non-vacuity of Theorem S4.10 in every dimension (not printed) | `halfspace_geometry` |
| Q29(c) | non-vacuity of Theorem S4.10 and Corollary S4.11 case 1 (not printed) | `halfspace_pair` |

## Encodings (declared; full list in the Lean header and `NEW_STATEMENTS_31tq.md` §A)
* Domains: `V` a finite-dimensional real inner-product space with its Borel sets and `volume`, `d = finrank ℝ V`; ℝ is the case `d = 1`, so
  the results printed "on ℝ" (Props 5.5, 5.6, S4.12–S4.15, Cor S4.11 case 2) are stated on ℝ and the `ℝ^d` results (S4.5, S4.9, S4.10,
  Cor S4.11 case 1) on `V`; the claims that use `c_d` quantify `(d : ℕ) [NeZero d]` and `V` with `finrank ℝ V = d`.
* Kernel (K), the printed "`k(x,y) = k₀(x−y)` with `k₀` continuous, integrable and positive definite" (S4 :308-309): `H` a real
  inner-product space, complete, and a feature map `φ : V → H` with `⟪φx, φy⟫ = k₀(x − y)`, `k₀` continuous and integrable. Positive
  definiteness of `k₀`, continuity, boundedness (`‖φx‖ = √k₀(0)`) and strong measurability of `φ` are then theorems (31tp L14, L16), so
  (A1) is discharged, not assumed; every continuous integrable positive definite `k₀` has such a `φ` into a complete separable `H`
  (31tp L15: the non-vacuity witness of every kernel hypothesis). `‖f‖_ℋ` is the least representer norm (attained, 31tp L18); "`f ∈ ℋ`
  with `‖f‖²_ℋ ≤ B`" is `∃ g : H, (∀ x, ⟪g, φx⟫ = f x) ∧ ‖g‖² ≤ B`; "every such `f` gives …" is "every representer `g` gives …" (the least
  one included).
* Separability ((A2), decision D1): `[SeparableSpace H]` is assumed exactly in the claims whose routes use a frozen claim that needs it
  (Q8, Q11, Q12, Q17, Q20–Q22, Q24–Q27, as Assumption 2.1 (A2) prints it), not in Q2–Q7, Q14, Q16, Q19 (a generalisation there); Q1, Q9,
  Q10, Q15, Q18, Q28, Q29 have no feature map. The printed RKHS of a continuous kernel on `ℝ^d` is separable, so each claim at `H = ℋ` is the
  printed statement.
* Angular convention (S4 :309, :317, eq:newnative): `ftA g ξ = 𝓕 g (ξ/2π)` (the printed `ĝ(ξ) = ∫ g e^{−i⟨ξ,x⟩}`), `ft2A` the same for the
  `L²` transform (junk `0` off `L²`), `ftMeasA μ ξ = ftMeas μ (ξ/2π)`, `kHat k₀ = Re (ftA k₀)` (real by Q2), `nativeA k₀ f =
  (2π)^{−d} ∫⁻ |f̂|²/k̂₀` and `sobolevA s f = (2π)^{−d} ∫⁻ |f̂|²(1 + ‖ξ‖²)^s` in `[0, ∞]`. Q3 proves `nativeA = nativeN`, `sobolevA = sobolevS`.
* Laws: "`P, Q` have densities `p, q`" = `p, q` measurable and nonnegative with `P = volume.withDensity (ofReal ∘ p)`, same for `Q`;
  pointwise hypotheses (continuity near `x₀`, `p(x₀) > 0`, differentiability at `x₀`) refer to these versions; the sign hypotheses are
  almost everywhere, as printed at `1fbc8df` (D2). Global Lebesgue densities are also assumed in Q16–Q19, where the printed hypotheses
  ("`p − q ≥ ℓ′(x−x₀)^r` almost everywhere", "`p, q` continuous on …") presuppose them (declared reading). `α⋆ = tvDist P Q`, `R = P ⊓ Q`,
  `P₀ ∝ P − P ⊓ Q`, `supp P₀ = (P − P ⊓ Q).support`.
* `|P − Q|` (main :83) = `absPQ P Q`, Mathlib's total variation of `P − Q` as signed measures; `T(ρ) = |P−Q|(ℝ^d ∖ B_{ρ−1})` = `tailOut P Q c₀
  ρ` with the open ball `B_{ρ−1}` about a centre `c₀` (S4 :583-584); `T₊(ρ) = |P−Q|((x₀+ρ, ∞))` = `tailPlus P Q x₀ ρ`.
* The laws of Proposition 5.5, (L55) := `IsCross P Q p q x₀ ℓ₀ ∧ 0 < p x₀ ∧ ExpTail P Q x₀`: `IsCross` = densities, `p, q` continuous on an
  open interval about `x₀`, `q ≤ p` a.e. on `(x₀, ∞)`, `p ≤ q` a.e. on `(−∞, x₀)`, `HasDerivAt (p − q) ℓ₀ x₀`, `0 < ℓ₀` (so `ℓ₀ =
  (p − q)′(x₀)` is named, as in Proposition 5.6); `ExpTail` = `∃ C′ > 0, ∀ t > 0, |P−Q|({|x − x₀| > t}) ≤ C′e^{−t/C′}`.
* Signed measures (D9): `ν = P′ − Q′` as `P'.toSignedMeasure − Q'.toSignedMeasure`, `|ν| = ν.totalVariation univ`, "`supp ν ⊆ I`" =
  `ν.totalVariation Iᶜ = 0`, the moments (`sMoment`) and `ν̂` (`ftSigned`) through the Jordan parts; `P′, Q′` of Q20 are `FiniteMeasure ℝ`.
* Paths and margins: `D_α = Dpop φ P Q α`; the printed rescaled path `D̄_α = (1−α)D_α` is the frozen `Wave31ti.uPath`; Assumption 5.1 is
  `Wave31ti.PolyMargin φ P Q c₀ γ` (`0 < c₀`, `1 ≤ γ`, `c₀e^γ ≤ D_{α⋆−e}` for `e ∈ [0, α⋆]`); `ω_ℋ` (S4 :419) is `Wave31to.xiH`; `err` is
  `Wave31to.errFn` (Q1 shows it is the printed `∫|1_A − f| d|P − Q|`).
* Quantifier readings: "for all small `ε > 0`" = `∃ ε₀, 0 < ε₀ ∧ ε₀ ≤ α⋆ ∧ ∀ ε ∈ (0, ε₀]` (D10; `ε₀ ≤ α⋆` keeps every level in `[0, 1)`); "for
  `n∧m` large" = `∃ n₀, ∀ n m, n₀ ≤ min n m → …`; "with probability at least `1 − p`" = a measurable event of `sampleLaw P Q n m`-probability
  `≥ ofReal (1 − p)` contained in the set; `O(log log(1/ε))` = `C·log log(1/ε)` for `ε ≤ ε₃ < e^{−1}`.
* Estimators: the split-sample bound, printed `α̂`, is `R.alphaLo α δ` for runs with `R.IsWitnessRun φ α δ (1/2) v²_min ∧ IsDefaultRun R`, the
  frozen hypotheses of the certified `Wave31tl.same_rate` and the printed class of Theorem 5.7 (D3); the paper's own run (`IsPaperRun` at the
  printed rules) is in this class by 31tr T5 and exists by 31tr T4 (31tr certified, audited PASS with notes at `ca19d29`); no 31tq
  statement imports 31tr. The analytic baseline with `τ^A` alone, printed `α̂_an^A`, is `alphaHat (Demp φ z.1 z.2) (τ^A κ D · δ n m)`, as in the
  certified `newconverse`; `κ`, `D` any bounds of `‖φx‖`, `‖φx − φx′‖` (the printed `κ`, `Δ_φ` are instances).
* Other definitions (all total): `cJ d = 1 − sSup (jBall d '' [1, ∞))` (`c_d`); `lapC m b = ‖Δ^m b‖_{L¹}` with the real Laplacian; `sobConst`
  (`C_{d,s,b}`); `bbar b t = ∫_t^∞ b`; `bbarE b Ω r₀` = `b̄(Ωr₀)` for `r₀ ∈ (0, ∞]` with `b̄(∞) = 0`; `bandH`, `bandB` the printed `h` and `b`
  with their continuous values `1/(4π)` at `±π`, where the printed formulas read `0/0`.
* Declared extra hypotheses (harmless; the docstring's list): `0 ≤ Π_ρ`, `0 ≤ V_ρ` in Q11–Q12 (critic B1: without them the claim is false;
  the printed constants bound measures); `0 < C` in Q19 and Q20(a) (with `C ≤ 0` the upper spectral bound forces `k̂₀ ≡ 0`, `φ ≡ 0`); `0 < C′`
  in `ExpTail` (`C′ ≤ 0` forces `P = Q`); `ε₀ ≤ α⋆`. Derived, not assumed: `m₂ > 0` (Q17), `0 < α⋆ < 1` under (L55), the compact support of
  `b` (Q10).
* Freeze-time encodings of the approved prose (the docstring's list): Q1 is (a) ∧ (b) under one name; Q12's two cases do not assume the
  mollifier `b` and the integer `m` of Theorem S4.10 (neither is in the conclusion: a stronger statement); Q20 states the main part, (a) and
  (b) as one claim, with `T_N, w_N` chosen before the kernel; Q15(c) takes `ĥ′` as the derivative of `ĥ = ftA bandH` itself on
  `(−1/2, 1/2)`; Q7(c) adds positive definiteness of the profile written on ℝ (`x²` for `‖x‖²`); Q28 takes the shift `N(±a, 1)` for every
  `a > 0` and writes the mixture weights as `ℝ≥0` scalars (the same measures as the prose's `ℝ≥0∞` scalars), with the conjuncts that the
  mixtures are probability measures; Q29(b) is (G2) for every `w₀ > 0`, in the form of Theorem S4.10's hypothesis.

## Covered — back-translation and deviations
Back-translated from the frozen `Statements.lean`. "(K) on ℝ" below means `H` complete, `φ : ℝ → H` with `⟪φx, φy⟫ = k₀(x − y)`, `k₀`
continuous and integrable; "the two-sided bound" means `c(1+ξ²)^{−s} ≤ k̂₀(ξ) ≤ C(1+ξ²)^{−s}` for all `ξ`, with `0 < c`, `1/2 < s`, any `C`;
"Prop 5.5's hypotheses" are (K) on ℝ with `H` separable, the two-sided bound and (L55); "Prop 5.6's hypotheses" are `H` complete separable,
`φ : ℝ → H` with Gram `exp(−(x−y)²/(2σ²))`, `σ > 0`, and (L55).
* Q1 `tv_density`: (a) on any measurable space, for probability measures: `|P − Q| = |p − q|·(P + Q)` with the frozen densities
  `p = dP/d(P+Q)`, `q = dQ/d(P+Q)`; for measurable `f` with values in `[0, 1]`, `errFn P Q f = ∫ |1_A − f| d|P − Q|` (`A = {q < p}`);
  `|P − Q|(𝒳) = 2α⋆`; `|P − Q| = (P − P⊓Q) + (Q − P⊓Q)`; `(P⊓Q)(𝒳) = 1 − α⋆`. (b) on `V`, for Lebesgue densities `p, q`: `|P − Q|`, `P⊓Q`,
  `P − P⊓Q` have densities `|p − q|`, `min(p, q)`, `(p − q)₊`; `α⋆ = ∫ (p − q)₊`; and for measurable `G` with `q ≤ p` a.e. on `G`, `p ≤ q`
  a.e. off `G`, and measurable `[0,1]`-valued `f`, `errFn P Q f = ∫ |1_G − f| |p − q| dx`. Printed: "`P₀`, `Q₀` … with densities `(p−q)₊/α⋆`
  and `(q−p)₊/α⋆`" (main :57-58), "`err(f) = ∫|1_A − f| d|P−Q|`, where `|P−Q|` is the total variation measure of `P − Q`" (main :82-83),
  "`R = P∧Q`, of mass `1−α⋆` … `|P−Q| = α⋆(P₀+Q₀)`" (S4 :302-304), "`1_G = 1_A` almost everywhere for `|P−Q|`" (S4 :609-610). Faithful;
  encodings: `P₀, Q₀` as the parts `P − P⊓Q`, `Q − P⊓Q` (normalised by `α⋆`), the `Q₀` density is the claim at `(Q, P)`; the `1_G = 1_A`
  sentence through the `err` identity with `1_G`; (a) ∧ (b) under one name.
* Q2 `spectral_angular`: for `k₀ : V → ℝ` continuous, integrable and positive definite: `ftA k₀` is real, `k̂₀ ≥ 0`, `k̂₀` integrable, and
  `k₀(z) = (2π)^{−d} ∫ k̂₀(ξ) e^{i⟨ξ,z⟩} dξ` for every `z`; and every feature map into any real inner-product space with Gram `k₀(x − y)`
  makes `k₀` positive definite. Printed S4 :308-310 ("Then `k̂₀ ≥ 0` is integrable, `k₀(z) = (2π)^{−d}∫k̂₀(ξ)e^{iξ·z}dξ`"). Faithful (the
  second conjunct: the hypothesis holds in (K)).
* Q3 `native_angular` (eq:newnative): (a) for every `k₀`, `nativeA k₀ = nativeN k₀`, `sobolevA s = sobolevS s` and `k̂₀(ξ) = specDens k₀
  (ξ/2π)` (the dictionary to 31tp's convention); in (K) on `V`: (b) for every `g ∈ H`, `f = ⟪g, φ·⟫` is continuous, in `L²`, with
  `(2π)^{−d}∫|f̂|²/k̂₀ ≤ ‖g‖²`, with equality when `g` lies in the closed span of `φ(V)`; (c) a continuous real `f` is represented iff
  `f ∈ L²` and `(2π)^{−d}∫|f̂|²/k̂₀ < ∞`, and then some representer `g₀` has `‖g₀‖² = (2π)^{−d}∫|f̂|²/k̂₀` and `‖g₀‖ ≤ ‖g‖` for every
  representer `g`. Printed S4 :310-316 ("the RKHS consists of the continuous `f ∈ L²(ℝ^d)` with `∫|f̂|²/k̂₀ < ∞`, with `‖f‖²_ℋ = (2π)^{−d}
  ∫|f̂|²/k̂₀`", Wendland Thm 10.12). Faithful; encodings: the RKHS as the represented functions with the least representer norm; the
  quotient in `[0, ∞]` (`x/0 = ∞` for `x ≠ 0`).
* Q4 `bochner_angular` (eq:newbochner): in (K) on `V`, for finite measures `μ₁, μ₂`: `ξ ↦ k̂₀(ξ)|μ̂₁(ξ) − μ̂₂(ξ)|²` is integrable and
  `‖∫φ dμ₁ − ∫φ dμ₂‖² = ∫∫k₀(x−y)dμ₁dμ₁ − 2∫∫k₀(x−y)dμ₂(y)dμ₁(x) + ∫∫k₀(x−y)dμ₂dμ₂ = (2π)^{−d}∫ k̂₀ |μ̂₁ − μ̂₂|²`. Printed S4 :317-322, for a
  finite signed measure `ν`. Faithful; encoding: `ν = μ₁ − μ₂` (every finite signed measure is the difference of its Jordan parts, and both
  sides depend on `ν` only), the double integral `∫∫k₀ dν dν` expanded bilinearly.
* Q5 `sobolev_angular`: in (K) on `V` with `c > 0` and `k̂₀(ξ) ≥ c(1+‖ξ‖²)^{−s}`: (a) every continuous `f ∈ L²` with `‖f‖_{H^s} < ∞` is
  represented by some `g` with `‖g‖² ≤ ‖f‖²_{H^s}/c`; (b) equal embeddings of two finite measures force equality of the measures,
  `Characteristic φ` and `StrictlyPDOn φ univ`; (c) if also `k̂₀ ≤ C(1+‖ξ‖²)^{−s}`, a continuous `f` is represented iff `f ∈ L²` and
  `‖f‖_{H^s} < ∞`, and the least representer has `‖f‖²_{H^s}/C ≤ ‖g₀‖² ≤ ‖f‖²_{H^s}/c`; (d) for `s > d/2`, `a, ℓ > 0` the Matérn profile is
  continuous, integrable, with `aℓ^d max(1,ℓ²)^{−s}(1+‖ξ‖²)^{−s} ≤ k̂₀ ≤ aℓ^d max(1,ℓ^{−2})^s(1+‖ξ‖²)^{−s}`. Printed S4 :530-533 (the
  `H^s` norm, the inclusion with `‖f‖²_ℋ ≤ ‖f‖²_{H^s}/c`, "Such a kernel is characteristic"), S4 :32-33 ("For a Matérn kernel on `ℝ^d` the
  RKHS is a Sobolev space with an equivalent norm"), §1 :82 ("a Sobolev kernel of order `s`"), main :105-109. Faithful; encoding: "a Sobolev
  kernel of order `s`" read through the two-sided spectral bound, for which (c) proves "RKHS = `H^s` with an equivalent norm" (the converse,
  equivalent norms ⇒ the two-sided bound, is not claimed); the cited reason "as `k̂₀ > 0`" is replaced by a proof.
* Q6 `sobolev_needs`: for `d ≥ 1`, `k₀` continuous, integrable, positive definite, `c > 0` and `k̂₀(ξ) ≥ c(1+‖ξ‖²)^{−s}` for all `ξ`:
  `d/2 < s`, hence `(d+3)/4 < (2s+3)/4` and `2/(2s+3) < 2/(d+3)`. Printed S4 :1026-1027 ("in `ℝ^d` the margin that Theorem S4.10 gives a
  transversal crossing guarantees at best `(n∧m)^{−2/(d+3)}`, as a Sobolev kernel needs `s > d/2`"). Faithful under the reading D15: "guarantees
  at best" is the exponent inequality for the rate that Theorem 5.7 gives at Theorem S4.10's exponent `(2s+3)/4` (`r = 1`); that the true
  margin exponent in `ℝ^d` is no smaller is not claimed (no upper bound on the path is printed for `d ≥ 2`). `d ≥ 1` is needed (on the
  one-point space the claim fails). The citation clause is declared.
* Q7 `kernel_instances`: (a) for `σ > 0`, the Laplace profile `e^{−|x|/σ}` on ℝ is continuous, integrable, positive definite, `k̂₀(ξ) =
  2σ/(1+σ²ξ²)`, `2σ min(1,σ^{−2})(1+ξ²)^{−1} ≤ k̂₀ ≤ 2σ max(1,σ^{−2})(1+ξ²)^{−1}`, and `k̂₀(ξ) ≤ (2/σ)|ξ|^{−2}` for `ξ ≠ 0`; (b) for `s > d/2`,
  `a, ℓ > 0` the Matérn profile on `V` is positive definite with `k̂₀(ξ) = aℓ^d(1 + ℓ²‖ξ‖²)^{−s}`; (c) for `σ > 0` the Gaussian profile on
  `V` is positive definite with `k̂₀(ξ) = (2πσ²)^{d/2}e^{−σ²‖ξ‖²/2}`, and on ℝ (written with `x²`) positive definite with `k̂₀(ξ) =
  √(2π)σe^{−σ²ξ²/2}`, `ξ^{2N}k̂₀` integrable and `(2π)^{−1}∫ξ^{2N}k̂₀ = (2N−1)!!σ^{−2N}` for every `N ∈ ℕ`. Printed: "as for the Laplace
  kernel, with `s = 1`, and the Matérn kernel of smoothness `s − 1/2`" (main :108-109), main :131, "as for the Matérn kernels" (S4 :376-377),
  "`k̂₀(ξ) = (2π)^{1/2}σe^{−σ²ξ²/2}`" (S4 :657), "For the Gaussian kernel `M_{2N} = (2N−1)!!σ^{−2N}`" (S4 :794-795). Faithful;
  encodings: the explicit Laplace constants of Prop 5.5's two-sided bound and of Prop S4.14's hypothesis; the Laplace bandwidth `σ` (§2
  :49); `N = 0` included (`(2·0 − 1)!! = 0!! = 1 = M₀` in ℕ arithmetic, the correct value).
* Q8 `newgammaone`: `V` with `finrank V = d`, (K) with `H` complete separable, `c > 0`, `d/2 < s`, `k̂₀ ≥ c(1+‖ξ‖²)^{−s}`; any probability
  measures `P, Q` on `V` with `0 < α⋆ < 1` and `supp P₀` compact: (a) if `supp P₀ ∩ supp Q₀ = ∅`, some `g` has `0 ≤ ⟪g, φx⟫ ≤ 1` everywhere,
  `= 1` on `supp P₀`, `= 0` on `supp Q₀`; (b) every such `g` is nonzero and, for `ε ∈ [0, α⋆]`, `D̄_{α⋆−ε} ≤ D_{α⋆−ε}` and
  `ε/‖g‖ ≤ D̄_{α⋆−ε}`, and `PolyMargin φ P Q (1/‖g‖) 1`; (c) for every limit `sl` of `D̄_{α⋆−e}/e` as `e ↓ 0`, `0 < sl` iff the supports are
  disjoint. Printed S4 :374-382 (Proposition S4.5, the last sentence "Together with Proposition 5.3, the rescaled path then has a positive
  slope at `α⋆` if and only if `supp P₀ ∩ supp Q₀ = ∅`"). Faithful; encodings: `‖f‖_ℋ` through every representer; "has a positive slope" as
  every limit of the difference quotient being positive (the limit exists, certified `Wave31ti.pathconvex_ii`).
  `newgammaone_smooth` (E10): (a)–(c) verbatim on `V = EuclideanSpace ℝ (Fin d)` for every continuous, strongly measurable feature map
  bounded by `κ` into a complete separable `H` with `ContainsSmoothCompact φ`. Printed S4 :371-372 ("When `supp P₀` is compact, the bound is
  an equivalence for continuous kernels whose RKHS contains the smooth functions with compact support"). Faithful; encoding: the kernel's
  RKHS through `ContainsSmoothCompact φ`; boundedness and strong measurability of `φ` are the standing (A1) (Assumption 2.1).
* Q9 `translation_intervals`: for `N` order-connected sets `I_i ⊆ ℝ` (intervals of any type, possibly empty or unbounded, not necessarily
  disjoint) and `E = ⋃I_i`: `Leb(E △ (E + h)) ≤ 2N|h|` for every `h` (`E + h` = `(· − h)⁻¹' E`). Printed S4 :533-535 ("in ℝ, with `Π = 2N` for a
  union of `N` disjoint intervals"). Generalisation (no disjointness). The perimeter half is declared (GMT, E4).
* Q10 `newsobnorm` (Lemma S4.9): for `d ≥ 1`, `V` with `finrank V = d`, `s > 1/2`, `E` bounded measurable with `Leb(E △ (E+h)) ≤ Π‖h‖` for all
  `h` (any real `Π`), `b` smooth, nonnegative, `∫b = 1`, supported in the closed unit ball, and every `m ∈ ℕ` with `2s − 1 < 4m`: `c_d > 0`, and
  for every `w > 0`, `f_w = 1_E ∗ b_w` (`mollify E (dilateR w b)`) has `0 ≤ f_w ≤ 1`, is `C^∞` with compact support, and for `w ≤ 1`
  `‖f_w‖²_{H^s} ≤ 2^s Leb(E) + C_{d,s,b} Π w^{1−2s}`, `C_b = ‖Δ^m b‖_{L¹}`. Printed S4 :537-549. Generalisation: every `m` with `4m > 2s − 1`,
  not only the smallest (D4); encodings: `Δ` the real Laplacian, `‖·‖_{H^s}` = `sobolevA`. The sub-sentence "In ℝ, `j₁(y) = sin y/y` and
  `c₁ = 1 − sin 1`" (S4 :564-565) is the certified 31tp L11.
* Q11 `newsobolev_thm` (Theorem S4.10): `d ≥ 1`, `V`, (K) with `H` separable, `c > 0`, `d/2 < s`, the lower spectral bound; `P, Q` with Lebesgue
  densities `p, q`, `0 < α⋆ < 1`; `G` open with `q ≤ p` a.e. on `G`, `p ≤ q` a.e. off `G`; a centre `c₀`; `ρ ≥ 1`, `r > 0`, `ℓ > 0`,
  `0 < w₀ ≤ 1`, `Π_ρ ≥ 0`, `V_ρ ≥ 0` with (G1) `Leb(E_ρ △ (E_ρ+h)) ≤ Π_ρ‖h‖` (`E_ρ = G ∩ B(c₀, ρ)`), (G2) `Leb{x ∈ B(c₀,ρ) : dist(x, ∂G) ≤ t} ≤
  V_ρ t` for `0 < t ≤ w₀`, (G3) `|p − q|(x) ≤ ℓ dist(x, ∂G)^r` for a.e. `x ∈ B(c₀, ρ)` with `dist(x, ∂G) ≤ w₀`; `b`, `m` as in Q10. Then for
  every `w ∈ (0, w₀]`, with `f = 1_{E_ρ} ∗ b_w` and `B = 2^s Leb(B(c₀,ρ)) + C_{d,s,b}Π_ρ w^{1−2s}`: `f` is represented by some `g` with
  `‖g‖² ≤ B/c`, `0 ≤ f ≤ 1`, `err(f) ≤ ℓV_ρw^{r+1} + T(ρ)`, and for every `ε ∈ [0, α⋆]`, `D̄_{α⋆−ε} ≤ D_{α⋆−ε}` and
  `√c·{ε − ℓV_ρw^{r+1} − T(ρ)}₊/√B ≤ D̄_{α⋆−ε}`. Printed S4 :586-603. Faithful; declared: `0 ≤ Π_ρ`, `0 ≤ V_ρ` (B1, the printed reading; the claim
  is false for negative constants); the norm bound `‖f_w‖²_ℋ ≤ B/c` is printed in the proof (S4 :607-608) and stated as a conjunct;
  encodings: `dist(x, ∂G)` = `infDist x (frontier G)`, `B_ρ` the open ball about any centre, `d ≥ 1` through `NeZero d`.
* Q12 `newsobolev_cor_bounded` (Corollary S4.11, `T(ρ) = 0`): all hypotheses of Q11 at the given `ρ` except `b`, `m`, and `T(ρ) = 0`; with
  `γ = 1 + (2s−1)/(2(r+1))`: some `c₁ > 0`, `ε₁ ∈ (0, α⋆]` with `c₁ε^γ ≤ D̄_{α⋆−ε}` for `ε ∈ (0, ε₁]`; `PolyMargin φ P Q c γ` for some `c`; and
  `1/(2γ) = (r+1)/(2(r+1) + 2s − 1)`, `= 2/(2s+3)` when `r = 1`. `newsobolev_cor_line` (case `d = 1`): `V = ℝ`, (K) on ℝ with `H` separable,
  `c > 0`, `s > 1/2`, the lower bound; densities, `0 < α⋆ < 1`; `q ≤ p` a.e. on `(x₀, ∞)`, `p ≤ q` a.e. on `(−∞, x₀]`; `r > 0`, `ℓ > 0`,
  `0 < w₀ ≤ 1` with `|p − q|(x) ≤ ℓ|x − x₀|^r` for a.e. `x` with `|x − x₀| ≤ w₀`; `C_T, a > 0` with `T(ρ) ≤ C_Te^{−ρ/a}` for `ρ ≥ 1` (balls about
  `x₀`): the same conclusion. Printed S4 :620-627. Faithful; encodings: case 1 with the B1 guards; case 2 with `G = (x₀, ∞)`, (G1)–(G2) not
  assumed (they hold with `Π_ρ = V_ρ = 2`), (G3) for every `ρ` with the same `ℓ, w₀` written once, `dist(x, ∂G) = |x − x₀|`; neither case
  assumes the mollifier `b` and the integer `m` (a stronger statement; freeze-time encoding); "Assumption 5.1 holds with this `γ`" =
  `∃ c, PolyMargin φ P Q c γ`.
  `newsobolev_cor_OP` ("Hence"): for any measurable space `𝒳`, `H` complete separable, `φ` strongly measurable with `‖φ‖ ≤ κ`,
  `PolyMargin φ P Q c₀ γ`, `α⋆ < 1`, `J ≥ 1`, `δ ∈ (0,1)`, `v²_min ∈ (0,4]`: for every `η ∈ (0,1)` there are `C`, `n₀` such that for all `n, m`
  with `n₀ ≤ n∧m`, every grid `α` of `J` levels, every run `R` with `IsWitnessRun φ α δ (1/2) v²_min ∧ IsDefaultRun` and every upper bound `h`
  of the mesh below `α⋆`, a measurable event of probability `≥ 1 − η` lies in `{α⋆ − h − C(n∧m)^{−1/(2γ)} ≤ α̂}`. Printed S4 :628-630 ("Hence,
  with `α̂` computed as in Theorem 5.7 on a grid of `J` levels fixed in advance with mesh `Δ_G` below `α⋆`, `α̂ ≥ α⋆ − Δ_G −
  O_P((n∧m)^{−1/(2γ)})` for fixed `J`") and S4 :646-647 ("part (i) alone … gives the bound with probability at least `1 − η`"). Faithful;
  encodings: the run class of `same_rate` (D3), any mesh bound `h`, `J` before `C`, `O_P` one-sided as the paper's (§6 :62-64), probability
  `1 − η` with no `δ`; generalisation: the margin is a hypothesis (any pair with a polynomial margin), and `C` is uniform over grids of `J`
  levels and runs; the corollary's "Hence" is the composition with either case (`∃ c, PolyMargin`), not a conjunct.
* Q14 `bandlimited_angular` (eq:newbandlim): `H` complete, `φ : ℝ → H` with Gram `exp(−(x−y)²/(2σ²))`, `σ > 0`, `Ω ≥ 0`: every continuous
  `f ∈ L²` whose `L²` transform vanishes a.e. on `|ξ| > Ω` is represented by some `g` with `‖g‖² ≤ e^{σ²Ω²/2}/((2π)^{1/2}σ)·∫f²`. Printed S4
  :656-664. Faithful (vanishing a.e., a generalisation of "vanishes outside `[−Ω, Ω]`"); the spectral density is Q7(c).
* Q15 `bbar_even`: for `b` measurable, nonnegative, `∫b = 1`, even: `b̄(t) ≤ 1/2` for `t ≥ 0`, `b̄` nonincreasing on `[0, ∞)`, `b̄(t) → 0` as
  `t → ∞`. Printed S4 :664-666 ("so that `b̄ ≤ 1/2`"), S4 :674 ("`b̄(∞) = 0`"). Faithful.
  `bandB_facts`: (a) `h = cos(t/2)/(π² − t²)` is continuous, integrable, square integrable, `ĥ(ξ) = cos(πξ)` for `|ξ| ≤ 1/2` and `0` for
  `|ξ| > 1/2`, `∫h² = 1/(4π)`, `b = h²/∫h²`; (b) `b = 4π cos²(t/2)/(π² − t²)²` is continuous, bounded, even, nonnegative, integrable,
  `∫b = 1`, `b̂` real, `b̂(ξ) = 0` for `|ξ| > 1`, `b̂(ξ) = (2π)^{−1}·4π·∫ĥ(η)ĥ(ξ − η)dη`; (c) `t²b` integrable, `∫t²b = π²`, `ĥ` has derivative
  `−π sin(πξ)` on `(−1/2, 1/2)`, and `π² = ∫_{−1/2}^{1/2}|ĥ′|²/∫|ĥ|²`; (d) for `t ≥ √2π`: `t²/2 ≤ t² − π²`, `b(t) ≤ 16πt^{−4}`,
  `b̄(t) ≤ 16π/(3t³)`. Printed S4 :664-670. Faithful; encodings: `h`, `b` at `±π` (continuous values; continuity is a conjunct); "a multiple of
  the autocorrelation of `ĥ`" as the convolution identity (`ĥ` real and even); `ĥ′` the derivative of `ĥ` itself on the open band (Q15(c),
  freeze-time).
* Q16 `newgaussstep` (Lemma S4.12): `H` complete, Gaussian `φ` on ℝ (`σ > 0`); `P, Q` with densities, `q ≤ p` a.e. on `(x₀, ∞)`, `p ≤ q` a.e.
  on `(−∞, x₀)`; `ℓ > 0`, `r₀ ∈ (0, ∞]` with `|p − q|(x) ≤ ℓ|x − x₀|` for a.e. `x` with `|x − x₀| ≤ r₀`; `b` measurable, nonnegative,
  `∫b = 1`, even, `b̂(ξ) = 0` for `|ξ| > 1`, `t²b` integrable. For `Ω, ρ > 0`, `f = 1_{(x₀,x₀+ρ)} ∗ b_Ω` (`b_Ω(t) = Ωb(Ωt)`): `f` is represented
  with `‖g‖² ≤ ρe^{σ²Ω²/2}/((2π)^{1/2}σ)`, `0 ≤ f ≤ 1`, and `err(f) ≤ ℓm₂/(2Ω²) + 2T₊(ρ/2) + 2α⋆{b̄(Ωr₀) + b̄(Ωρ/2)}`, `m₂ = ∫t²b`. Printed S4
  :677-684 with the setting S4 :664-666, :672-675. Faithful; encodings: `r₀ ∈ (0, ∞]` as `ℝ≥0∞` with `b̄(∞) = 0` (`bbarE`, D6); "`A = (x₀,∞)` up
  to a null set of `|P−Q|`" is a consequence (Q1(b)), not a hypothesis; no continuity of `b` assumed (none printed).
* Q17 `newgauss_thm` (Theorem S4.13): the setting of Q16 with `H` separable; `θ ∈ (0,1)`, `ε ∈ (0, α⋆]`, `ρ > 0`, `Ω_ε = √(ℓm₂/(2θε))`, and the
  condition `2T₊(ρ/2) + 2α⋆{b̄(Ω_εr₀) + b̄(Ω_ερ/2)} ≤ (1−θ)ε/2`: `D̄_{α⋆−ε} ≤ D_{α⋆−ε}`, `((1−θ)ε/2)·{(2π)^{1/2}σ/ρ}^{1/2}·exp(−σ²ℓm₂/(8θε)) ≤
  D̄_{α⋆−ε}`, and the same bound `≤ ω_ℋ(ε)` (`xiH`). Printed S4 :705-711 and S4 :739-741 ("so it is also a lower bound on `ω_ℋ(ε)`").
  Faithful; no `α⋆ < 1` (none printed).
  `newgauss_thm_rho`: the setting of Q16 with `b = bandB` (`m₂ = π²`, Q15), `H` separable, `C_T, a > 0` with `T₊(t) ≤ C_Te^{−t/a}` for `t > 0`,
  `θ ∈ (0,1)`, `α⋆ > 0`: (a) for some `ε₂ > 0` and all `ε ∈ (0, min(ε₂, α⋆)]`, `ρ_ε = max{2, 2a log(8C_T/((1−θ)ε))}` satisfies the condition
  of the theorem with `Ω_ε = √(ℓπ²/(2θε))`; (b) for some `C` and `ε₃ ∈ (0, e^{−1})`, `ε₃ ≤ α⋆`, and all `ε ∈ (0, ε₃]`: `D̄_{α⋆−ε} > 0` and
  `log(1/D̄_{α⋆−ε}) ≤ σ²ℓπ²/(8θε) + log(1/ε) + C log log(1/ε)`. Printed S4 :711-715. Faithful; encodings: "for all small `ε`", `O(log log)`
  as declared.
* Q18 `momentdecay_angular` (eq:newmomentdecay): (a) for a finite signed measure `ν` on ℝ, `x₀`, `W ≥ 0`, `N ≥ 1` with `|ν|` carried by
  `[x₀ − W, x₀ + W]` and `∫(x − x₀)^j dν = 0` for `j < N`: `|ν̂(ξ)| ≤ |ν|(ℝ)·min{1, (|ξ|W)^N/N!}` for every `ξ`; (b) for finite measures
  `P′, Q′`, `ν̂` of `P′ − Q′` is `P̂′ − Q̂′`. Printed S4 :749-756 (`ν = P′ − Q′`). Faithful; generalisation: any finite signed measure;
  encodings: moments and `ν̂` through the Jordan parts (D9).
* Q19 `newupperone` (Proposition S4.14): (K) on ℝ (no separability), `C > 0`, `s ∈ (1/2, 3/2)`, `k̂₀(ξ) ≤ C|ξ|^{−2s}` for `ξ ≠ 0`; `P, Q` with
  densities; `ℓ′, r, r₀ > 0` with `p − q ≥ ℓ′(x − x₀)^r` a.e. on `(x₀, x₀ + r₀)` and `q − p ≥ ℓ′(x₀ − x)^r` a.e. on `(x₀ − r₀, x₀)`. For every
  `ε ∈ (0, ℓ′r₀^{r+1}/(r+1)]`, with `W = ((r+1)ε/ℓ′)^{1/(r+1)}`: `ε ≤ α⋆`, `D̄_{α⋆−ε} ≤ 2εW^{s−1/2}{(C/2π)(2/(3−2s) + 2/(2s−1))}^{1/2}`, and
  `∫min(1, ξ²W²)|ξ|^{−2s}dξ = W^{2s−1}(2/(3−2s) + 2/(2s−1))`. Printed S4 :758-766. Faithful; declared: `0 < C` (harmless guard), Lebesgue
  densities (presupposed by "`p − q`"); the printed integral and `ε ≤ α⋆` are conjuncts.
* Q20 `newmoments` (Proposition S4.15): `P, Q` with densities, `r₀ > 0`, `p, q` continuous on `(x₀ − r₀, x₀ + r₀)`, `HasDerivAt (p − q) ℓ₀ x₀`,
  `ℓ₀ > 0`, `p(x₀) = q(x₀) > 0`. For every `N ≥ 1` there are `T_N ≥ 1`, `w_N > 0` such that: for every `w ∈ (0, w_N]` there are finite measures
  `P′ ≤ P`, `Q′ ≤ Q` and `e ≥ ℓ₀w²/8` with `P′(ℝ) = Q′(ℝ) = 1 − α⋆ + e`, `ν = P′ − Q′` with `|ν| ≤ 2ℓ₀w²`, `|ν|` carried by
  `[x₀ − T_Nw, x₀ + T_Nw]`, and vanishing moments of order `< N`; (a) for every (K) on ℝ with `H` separable, `C > 0`, `1/2 < s`, `s − 1/2 < N`
  and `k̂₀ ≤ C(1+ξ²)^{−s}`: `v ↦ min(1, v^{2N}/N!²)|v|^{−2s}` is integrable and there is `K` with, for `ε ∈ (0, ℓ₀w_N²/8]` and `w = √(8ε/ℓ₀)`,
  `D̄_{α⋆−ε} ≤ 2ℓ₀w²(T_Nw)^{s−1/2}{CI_{N,s}/(2π)}^{1/2} ≤ Kε^{(2s+3)/4}`; (b) for every (K) on ℝ with `H` separable and `ξ^{2N}k̂₀` integrable,
  there is `K` with `D̄_{α⋆−ε} ≤ 2ℓ₀w²(T_Nw)^N M_{2N}^{1/2}/N! ≤ Kε^{1+N/2}` on the same range, `M_{2N} = (2π)^{−1}∫ξ^{2N}k̂₀`. Printed S4
  :782-797. Faithful; encodings: the signed-measure objects (D9), `P′, Q′` as `FiniteMeasure ℝ`, "of equal mass `1 − α⋆ + ε(w)`" with `ε(w)`
  existential per `w`; `T_N, w_N` before the kernel, as printed ("For every integer `N ≥ 1` there are … Consequently …"); "at most a
  constant times" = `∃ K` (depending on the kernel); declared `0 < C` in (a); the Gaussian `M_{2N}` is Q7(c).
* Q21 `newsobolev` (Proposition 5.5): under Prop 5.5's hypotheses: `0 < α⋆ < 1` and there are `0 < c₁ ≤ c₂` and `ε₀ ∈ (0, α⋆]` with
  `c₁ε^{(2s+3)/4} ≤ D_{α⋆−ε} ≤ c₂ε^{(2s+3)/4}` for `ε ∈ (0, ε₀]`. Printed main :105-117. Faithful; encodings: (L55), "for all small `ε`" (D10),
  `C′ > 0` in the tail hypothesis; the conjunct `0 < α⋆ < 1` is derived (approved prose), not printed in the statement.
  `newsobolev_E1`: under the same hypotheses, `PolyMargin φ P Q c₀ ((2s+3)/4)` for some `c₀`, and `PolyMargin φ P Q c₀′ γ′` fails for every
  `γ′ < (2s+3)/4` and every `c₀′`. Printed main :119-120 ("Assumption 5.1 therefore holds with `γ = (2s+3)/4` and with no smaller exponent";
  "`γ = 5/4` for the Laplace kernel" is Q27(a)). Faithful.
  `newsobolev_upper_small`: (K) on ℝ with `H` separable, `s ∈ (1/2, 3/2)`, `k̂₀ ≤ C(1+ξ²)^{−s}` (any `C`; no lower spectral bound), `IsCross`
  (no `p(x₀) > 0`, no tails): there are `c₂` and `ε₀ ∈ (0, α⋆]` with `D̄_{α⋆−ε} ≤ c₂ε^{(2s+3)/4}` for `ε ∈ (0, ε₀]`, and, if `α⋆ < 1`,
  `D_{α⋆−ε} ≤ c₂(1−α⋆)^{−1}ε^{(2s+3)/4}` on the same range. Printed S4 :841-842 ("For `s < 3/2` and `α⋆ < 1`, Proposition S4.14 with `r = 1`
  already gives the upper bound, without `p(x₀) > 0`"). Faithful: the `D`-conjunct under `α⋆ < 1` is the sentence; the `D̄`-conjunct without
  `α⋆ < 1` is a declared strengthening; dropping the lower bound and the tails is a generalisation.
* Q22 `newgauss` (Proposition 5.6): under Prop 5.6's hypotheses, for every `c > π²σ²ℓ₀/8` and `N ≥ 1` there are `ε₀ ∈ (0, α⋆]` and `C_N` with
  `exp(−c/ε) ≤ D_{α⋆−ε} ≤ C_Nε^N` for `ε ∈ (0, ε₀]`. Printed main :128-136 ("satisfy the hypotheses of Proposition 5.5 on the laws, put
  `ℓ₀ = (p−q)′(x₀)`"). Faithful.
  `newgauss_margin`: under the same hypotheses, (a) `D_{α⋆−ε}/ε^N → 0` as `ε ↓ 0`, for every `N ∈ ℕ`; (c) for every `c > π²σ²ℓ₀/8` some
  `c″ > 0` has `c″exp(−c/ε) ≤ D_{α⋆−ε}` for every `ε ∈ (0, α⋆]`. Printed main :138 ("the path thus leaves zero faster than every power, yet a
  margin of exponential type holds"), main :257-258 ("whose path leaves zero faster than every power"). Faithful; encoding: the margin read
  on all of `(0, α⋆]` (D7); (b) and (d) of v2 dropped with their printed text.
* Q24 `sharp_line`: (K) on ℝ with `H` separable, `c, C > 0`, `s ∈ (1/2, 3/2)`, `k̂₀ ≥ c(1+ξ²)^{−s}`, `k̂₀(ξ) ≤ C|ξ|^{−2s}` for `ξ ≠ 0`; densities,
  `0 < α⋆ < 1`, the a.e. signs about `x₀`; `r > 0`, `0 < w₀ ≤ 1`, `0 < ℓ′ ≤ ℓ` with `ℓ′|x − x₀|^r ≤ |p − q|(x) ≤ ℓ|x − x₀|^r` for a.e. `x` with
  `|x − x₀| < w₀`; `C_T, a > 0` with `T(ρ) ≤ C_Te^{−ρ/a}` for `ρ ≥ 1`. With `γ = 1 + (2s−1)/(2(r+1))`: `c₁ε^γ ≤ D̄_{α⋆−ε} ≤ c₂ε^γ` for some
  `0 < c₁ ≤ c₂`, `ε ∈ (0, ε₁]`, `ε₁ ∈ (0, α⋆]`; `PolyMargin φ P Q c₀ γ` for some `c₀`; and no `γ′ < γ` gives a margin. Printed main :124-126 ("with
  the exponent `1+(2s−1)/{2(r+1)}` when `p−q` vanishes to order `r` there, sharp on the line at least when `s < 3/2`"). Faithful under the
  declared reading: "vanishes to order `r`" as the two-sided local bound; "sharp" as `D̄ ≍ ε^γ` for every such pair and no smaller exponent
  (stronger than one extremal pair; critic Q24).
* Q25 `rate_sobolev_split`: under Prop 5.5's hypotheses with `‖φ‖ ≤ κ`, `J ≥ 1`, `δ, η ∈ (0,1)`, `v²_min ∈ (0,4]`: some `K ≥ 0` such that for all
  `n, m ≥ 1`, grids `α` of `J` levels, runs with `IsWitnessRun φ α δ (1/2) v²_min ∧ IsDefaultRun`, and mesh bounds `h`, a measurable event of
  probability `≥ 1 − δ − η` lies in `{α⋆ − h − K(n∧m)^{−2/(2s+3)} ≤ α̂ ≤ α⋆}`. Printed main :240-242 ("Under the hypotheses of Proposition 5.5,
  Theorem 5.7 guarantees at least the rate `(n∧m)^{−2/(2s+3)}` … in both cases up to the mesh"; the polynomial halves of abs :9-10, §1
  :80-83, main :6-8). Faithful; encoding: the run class of `same_rate` (D3), `K` uniform in `n, m`, the grid, the run and `h`.
  `converse_poly` (general form): any measurable space, `H` complete separable, `φ` strongly measurable, `‖φ‖ ≤ κ`, `‖φx − φx′‖ ≤ D`,
  `α⋆ < 1`, `0 < δ < δ′ < 1`, `n, m ≥ 1`, `c₂, γ > 0`, `ε₀ ∈ (0, α⋆]` with `D_{α⋆−ε} ≤ c₂ε^γ` on `(0, ε₀]`: a measurable event of probability
  `≥ 1 − δ′` on which `min{α⋆, ε₀, (g_{n,m}/c₂)^{1/γ}} ≤ α⋆ − α̂_an^A`. Printed S4 :847-849 ("an upper bound on the path gives a lower bound on
  the error"), S4 :882-884 (at `γ = (2s+3)/4`, "on `E⁺`"). Generalisation (any `γ`, `c₂`, any (A1)–(A2) setting); the printed instance is
  `γ = (2s+3)/4` with Q21's `c₂`.
  `lower_sobolev_A`: under Prop 5.5's hypotheses, `‖φ‖ ≤ κ`, `‖φx − φx′‖ ≤ D`, `0 < δ < δ′ < 1`: some `C₁ > 0` and `n₀` such that for `n∧m ≥ n₀`
  a measurable event of probability `≥ 1 − δ′` lies in `{C₁(n∧m)^{−2/(2s+3)} ≤ α⋆ − α̂_an^A}`. Printed S4 :882-885 ("of order
  `(n∧m)^{−2/(2s+3)}`"), main :246-248 (Sobolev half). Faithful.
  `slow_gauss_A`: under Prop 5.6's hypotheses with `κ`, `D`, `δ < δ′`: for every `N ≥ 1` some `c > 0`, `n₀` with an event of probability
  `≥ 1 − δ′` in `{c(n∧m)^{−1/(2N)} ≤ α⋆ − α̂_an^A}` for `n∧m ≥ n₀`; and for every `a > 0`, `C > 0` some `n₀` with an event of probability
  `≥ 1 − δ′` in `{C(n∧m)^{−a} < α⋆ − α̂_an^A}` for `n∧m ≥ n₀`. Printed S4 :885-887, main :246-249 ("with the Gaussian kernel its error is not
  `O((n∧m)^{−a})` for any `a > 0`", corrected wording #6a). Faithful; encoding: "not `O((n∧m)^{−a})`" in the strong form (for every `C`,
  eventually, with probability `≥ 1 − δ′`).
* Q26 `excess_sobolev`: under Prop 5.5's hypotheses, `γ = (2s+3)/4`: there are `0 < c₁ ≤ c₂` and `ε₀ ∈ (0, α⋆]` with `c₁ε^γ ≤ D_{α⋆−ε} ≤ c₂ε^γ`
  on `(0, ε₀]`, and for every `ε ∈ (0, ε₀/2]`, nearest points `a ∈ 𝒞_α(P)`, `b ∈ 𝒞_α(Q)` (`α = α⋆ − ε`, `‖a − b‖ = D_α`), the least
  `(1−α)`-quantile `t⋆` and the greatest `α`-quantile `u⋆` of `f⋆ = ⟨(a−b)/‖a−b‖, φ·⟩` under `P`, resp. `Q`, and `ψ⋆ = ramp f⋆ t⋆ u⋆`:
  `(1−α⋆)c₁ε/(2^γc₂) ≤ E_Pψ⋆ − E_Qψ⋆ − α ≤ ε`. Printed main :280-282 (Proposition 5.10(ii), "and this holds under the hypotheses of
  Proposition 5.5"), S4 :963-964. Faithful; encoding: the printed objects in 31tr's (Pr) encoding; the upper half `≤ ε` is 31tr T41's.
* Q27 `laplace_instances`: `σ > 0`, `H` complete separable, `φ : ℝ → H` with Gram `e^{−|x−y|/σ}`, (L55): (a) `PolyMargin φ P Q c₀ (5/4)` for some
  `c₀` and no `γ′ < 5/4` works; (b) the conclusion of `rate_sobolev_split` with exponent `2/5` (for every `J ≥ 1`, `δ, η ∈ (0,1)`,
  `v²_min ∈ (0,4]`; no `κ` needed); (c) the conclusion of `excess_sobolev` with `γ = 5/4`; (d) for every bound `D` of `‖φx − φx′‖` and
  `0 < δ < δ′ < 1`, the conclusion of `lower_sobolev_A` with exponent `2/5` for `α̂_an^A` at `κ = 1`. Printed main :108-109, :119-120
  ("`γ = 5/4` for the Laplace kernel"), :241-242 ("`(n∧m)^{−2/5}` for the Laplace kernel"), :256-259 (the Laplace instance of the excess),
  S6 :173-175 ("with `τ^A` alone its error is at least of order `n^{−2/5}`", `n = m` in the simulation). Faithful; encodings: `κ = 1`
  (`‖φx‖ = 1`), `n∧m` for the simulation's `n`; "in the figure it is most of `α⋆ − α`" is numerical.
* Q28 `simulated_pairs`: (a) for every `a > 0`, `P = N(a, 1)`, `Q = N(−a, 1)` with their Gaussian densities satisfy `IsCross` at `x₀ = 0` with
  `ℓ₀ = 2aφ₁(a)`, `p(0) > 0` and `ExpTail`; (b) for every `μ > 0`, `P = 0.8N(0,1) + 0.2N(μ,1)`, `Q = 0.8N(0,1) + 0.2N(−μ,1)` are probability
  measures satisfying `IsCross` with the densities `0.8φ₁ + 0.2φ₁(· − μ)`, `0.8φ₁ + 0.2φ₁(· + μ)`, `x₀ = 0`, `ℓ₀ = 0.4μφ₁(μ)`, `p(0) > 0` and
  `ExpTail`. Printed S6 :157-164 ("For the shift `N(±1,1)` and the mixtures `0.8N(0,1)+0.2N(±μ,1)`, `μ ∈ {1.5, 2, 3}`, which cross at `x₀ = 0`,
  … with `ℓ₀ = 0.4μφ(μ)`"), S6 :167-168, main :264-265 (Figure 2: the shift `N(±1,1)` with the Laplace and Gaussian kernels, `σ = 1`).
  Generalisation (every `a > 0`, every `μ > 0`); encodings: `ℝ≥0` weights, the probability conjuncts (freeze-time). That these pairs are
  instances of Props 5.5, 5.6, Q26 and Q27 is the composition with Q7, Q21–Q27, not a conjunct; "(eq:condR)" is 31tu Y23.
* Q29 `halfspace_geometry` (not printed; PLAN §5, D8): for `d ≥ 1`, `V`, a unit vector `e`, `a ∈ ℝ`, `G = {⟨x, e⟩ > a}`, any centre `c₀`, `ρ ≥ 1`:
  (G1) for `E_ρ = G ∩ B(c₀, ρ)` with `Π_ρ = (2ρ)^{d−1} + 2d·Leb(B(0,1))ρ^{d−1}`; (G2) with `V_ρ = 2(2ρ)^{d−1}` for every `w₀ > 0`;
  `dist(x, ∂G) = |⟨x, e⟩ − a|`. `halfspace_pair`: with `⟨c₀, e⟩ = a`, `η = (2Leb(B(0,2)))^{−1}`, `u = Leb(B(c₀,2))^{−1}1_{B(c₀,2)}`,
  `w = η(⟨x, e⟩ − a)1_{B(c₀,1)}` and the densities `p = u + w`, `q = u − w`: `p, q` measurable and nonnegative, `P(V) = Q(V) = 1`, `q ≤ p` on `G`
  and `p ≤ q` off `G` (everywhere), `|p − q| ≤ 2η·dist(x, ∂G)` everywhere ((G3) with `r = 1`, `ℓ = 2η`), `w = 0` off `B(c₀, 1)`, and
  `0 < α⋆ < 1`. Non-vacuity witness, no printed text; with (a)–(b) at `ρ = 2`, Q1(b) (`T(2) = 0`) and a Matérn kernel (Q5(d), Q7(b), 31tp
  L15) these are all the hypotheses of Q11 and Q12 case 1, in every dimension (a hand composition: `T(2) = 0` is not a conjunct, critic v2).

## Junk-value audit
Every `rpow` base is positive or nonnegative where read: `(1+‖ξ‖²)^{±s}`; `w^{1−2s}`, `w^{r+1}` (`w > 0`); `ε^γ`, `ε^{(2s+3)/4}` (`ε > 0`);
`(x − x₀)^r` on `x > x₀` and `(x₀ − x)^r` on `x < x₀` (Q19); `|x − x₀|^r` (`0^r = 0` for `r > 0`, the right value); `W_ε^{s−1/2}`,
`(T_Nw)^{s−1/2}`, `((r+1)ε/ℓ′)^{1/(r+1)}` (positive); `(g_{n,m}/c₂)^{1/γ}` (`g_{n,m} ≥ 0` because `D ≥ 0` and `δ < δ′`, `c₂ > 0`); `2^γ`;
`(n∧m)^{−·}` at `n, m ≥ 1` in `rate_sobolev_split` and Q27(b); in the claims with `∃ n₀` a junk `0^{−a} = 0` at `n∧m = 0` concerns only
sample sizes that any `n₀ ≥ 1` excludes, and the conclusion for large `n∧m` reads the true power. `|ξ|^{−2s}` at
`ξ = 0` is Mathlib's `0`: in Q7(a), Q19, Q24 the spectral hypothesis is stated for `ξ ≠ 0` only (the printed bound is `+∞` there), and
inside the integrals of Q19 and Q20 it is a null set. `log` only of arguments `> 1` in the read range (`log(1/ε)` and `log log(1/ε)` for
`ε < e^{−1}`; `log(8C_T/((1−θ)ε))`, positive argument) and `log(1/D̄)` with `D̄ > 0` a conjunct. `sSup`: `cJ d` of a nonempty bounded set
(`|j_d| ≤ 1`, 31tp L11); `xiH` (Q17) of a set that is nonempty (the constructed `f`) and bounded above (the route bounds it from
`newapproxgen_i` without `α⋆ < 1`); a junk `sSup = 0` would make the conjunct false, as its left side is positive. `sInf`: `alphaHat` of the
crossing set `{α ∈ [0,1) : D̂_α ≤ τ^A(α)}`, which is nonempty for `n, m ≥ 1` (`τ^A(α) = τ^A(0)/(1−α) → ∞` when `κ > 0` while `D̂ ≤ 2κ`;
`φ ≡ 0` when `κ = 0`), so the lower bounds on `α⋆ − α̂_an^A` (Q25, Q27(d)) are not met through `sInf ∅ = 0`. `toReal`: of `|P − Q|`,
`|ν|` (finite), `Leb(E)` (`E` bounded), `Leb(B)` (balls), `r₀` only when `r₀ ≠ ∞` (`bbarE`). ENNReal quotients in `nativeA`: `x/0 = ∞` for
`x ≠ 0`, the printed convention; `kHat ≥ 0` in (K) (Q2), so `ofReal` truncates nothing. `ft2A` (junk `0` off `L²`) is read only on `L²`
functions (`MemLp` hypotheses or conjuncts; in Q5(c) and Q3(c) the `iff` carries `MemLp f 2` on its right side). `ftA` (the integral
transform, junk off `L¹`) is read on integrable functions: `k₀` (hypothesis), `bandH`, `bandB` (conjuncts), `b` (`∫b = 1` forces
integrability, a non-integrable `b` has Bochner integral `0`). Bochner integrals: `∫t²b`, `∫ξ^{2N}k̂₀` (integrability hypotheses or
conjuncts), Q20(a)'s `I_{N,s}` (integrability conjunct), Q19's `∫min(1, ξ²W²)|ξ|^{−2s}` (a non-integrable integrand would give `0`, against
the positive right side of the proved equation), `errFn` and the ramp integrals (bounded integrands, finite measures), `∫φ dμ` in `H` (`φ`
bounded, continuous, strongly measurable, 31tp L16), the double integrals of `k₀` (bounded continuous). `deriv` is read in Q15(c) on
`(−1/2, 1/2)`, where `HasDerivAt` is a conjunct; the endpoints are a null set of the interval integral. `infDist x (frontier G)` is never read
with `frontier G = ∅` in Q11–Q12 (an empty frontier makes `G` clopen, `G ∈ {∅, V}`, hence `P = Q`, against `α⋆ > 0`); in Q29 the frontier is
the hyperplane. Divisions: by `‖g‖` with `g ≠ 0` a conjunct (Q8); by `√B` with `B ≥ 2^sLeb(B(c₀,ρ)) > 0` (Q11, `sobConst ≥ 0` since `c_d > 0`,
`1 − 2^{1−2s} > 0`, `1 − 2^{−(4m+1−2s)} > 0` for `s > 1/2`, `4m > 2s − 1`); by `r + 1`, `2γ`, `2s + 3`, `3 − 2s`, `2s − 1` (positive in range),
`θε`, `ℓ′`, `ℓ₀`, `c₂`, `σ`, `N!`, `2π`; `(1 − α⋆)^{−1}` only under `α⋆ < 1` (Q21). `√` of nonnegative arguments (`√M` with `M ≥ 0` because
`k̂₀ ≥ 0`). `ENNReal.ofReal` of a negative number is `0` (a true, weaker bound; Q10 needs no guard: `Π < 0` forces `E` null). ℕ subtraction:
`(2N − 1)!!` at `N = 0` is `0!! = 1 = M₀` (the right value), `d − 1` at `d ≥ 1`. `bandH`, `bandB` take their continuous values at `±π`;
`bbarE b Ω ∞ = 0`. No `Measure.map`. Vacuity: every hypothesis set has a witness — (K) by 31tp L15 for every continuous integrable positive
definite profile, the Sobolev bounds by the Matérn profiles (Q5(d)) and the Laplace kernel (Q7(a)), (L55) by the shift and the mixtures
(Q28), Theorem S4.10 and Corollary S4.11 case 1 in every dimension by Q29, case 2 and Q24 by the shift pair with the Laplace kernel at
`r = 1`, Q16–Q17 with `b = bandB` (Q15), Q8 by any pair whose contaminations have finite, disjoint supports (as in `ex:separated`) with a
Matérn kernel, the runs of Q12/Q25(b)/Q27(b) by 31tr T4 and T5, `PolyMargin` pairs by Q12 and Q21.

## Rows only / not claimed
* Heuristic sentences, declared (§I): main :73-76 (the trimming heuristic, E11), main :81-82 ("the path leaves zero tangentially, at a speed
  set by how well the RKHS approximates the indicator of `A`"), main :98-103 (the trimming bound sketch, "the smoother the kernel, the more this
  costs"), main :120-122 (the proof sketch of the lower and upper bounds; the results are Q12, Q20, Q21), main :139-140 ("with a norm that
  grows like `exp(c/ε)`"; the upper bound on the norm is Q14–Q17), §1 :83-84 ("These guarantees are not sharp, because a flat path has flat
  tangents"), S4 :778-780 (more vanishing moments need positive core density; the result is Q20).
* Meta sentences, declared: main :246 ("For the split-sample bound we prove no converse"), main :246-249's "for `τ^P` no converse is known",
  main :325-328, §1 :83 ("with no lower bound proved to match"), S4 :397 ("This sharpens Example 5.2"), S4 :847-849's `τ^P` half, S4 :863-864,
  S4 :1022-1026 (the constants of Prop 5.5 are not explicit; uniformity open), S6 :173-174 ("we prove no rate for it").
* Citations and cited reasons, declared: S4 :1027-1028 (the minimax rate for `L₁`-type functionals); "as `k̂₀ > 0` [Sriperumbudur et al.]" (S4
  :532-533) and "[Wendland, Ch. 10]" (S4 :32-33), whose conclusions are proved (Q5); Wendland Thm 10.12 (S4 :310-316) is the certified 31tp L18.
* Numerical, declared (E12): Figure 2 and its caption (main :264-267; the pair is Q28(a)), "in the figure" (main :256-259), the path
  computations of S6.4 (S6 :157-165).
* Declared, author question pending (E2/E4, the geometric-measure-theory sentences, PLAN §5): S4 :534 ("with `Π` the perimeter of `E`"), S4
  :650-653 (a compact `C²` hypersurface gives (G1)–(G3) with `r = 1`), and the `ℝ^d` hypotheses of main :122-125 in that form; their (G)-form
  is Q11, Q12 case 1, with non-vacuity in every dimension by Q29.
* Owned by 31tr (certified, audited at `ca19d29`): main :68-70 and :78-79 (T29), main :251-256 and the general half of :256-259 (T40, T41),
  main :320-322 (T28), S4 :304-306 (T24), S4 :876-879 (T26), S4 :978-980 (T42), `prop:excess` itself and Lemmas S4.17–S4.18 (T38–T42).
* Owned by 31tu: main :242-243 (Theorem 5.11, Y19(c)); main :243-246 and the logarithmic halves of abs :9-10, main :6-8, §1 :80-83 (Y26, the
  rate of Proposition S4.8(iii), with Q22 for the margin); the proof S4 :736-745 (route of Y26; its sentence :739-741 is Q17's `ω_ℋ`
  conjunct); S4 :1039-1041 (Y3); S4 :1061-1062 (uses Q21 at `s = 1`); S6 :167-168's `(eq:condR)` (Y23).
* Certified elsewhere: main :50-52 (31tp L29); main :82-85's `err = α⋆ − (E_Pf − E_Qf)` and the balanced risk (`Wave31to.newapprox_err`;
  the `|P−Q|` form is Q1(a)); Proposition S4.16 (S4 :851-861, `Wave31to.newconverse`); S4 :564-565 (31tp L11); the tangential half of §1
  :80-83 (Proposition 5.3, `Wave31to.newslope_b`, and 31tr T29); the consequence of S4 :31-36 (31tp L29).
* Dropped with their printed text (§M; the sentences are gone at `b3125cf`): Q13 `newsobolev_cor_log`, Q23 `newrates_iii`, Q12
  `newsobolev_cor_rate`, Q25 (a) `rate_sobolev`, (c2) `exact_sobolev_A`, (d) `rate_gauss_A`, (f) `rate_gauss_split` (X1: the printed fixed-`J`
  form is implied by 31tu Y26), Q22 `newgauss_margin` (b), (d), Q27 (b-analytic).

## Notes for the auditor
* Provenance of the frozen shapes (prover log, `STATUS_31tq.md`). 13 claims are copied verbatim from the critic-checked scratch files
  `fullstack/work/scratch31tq/{Defs31tq,Shapes31tq}.lean` (v3, sha256 prefixes bae7218dacc56922 and 1e9303235590be62, both typechecked by the
  drafter and the critic), modulo `CrossPair` → `IsCross … ∧ 0 < p x₀` and the inlined `|P − Q|((x₀ + ρ/2, ∞))`, `‖Δ^m b‖_{L¹}` written as
  `tailPlus`, `lapC`: `newsobnorm`, `newsobolev_thm`, `newsobolev_cor_OP`, `newgammaone`, `newgaussstep`, `newgauss_thm`, `newgauss_margin`,
  `converse_poly`, `sobolev_needs`, `rate_sobolev_split`, `lower_sobolev_A`, `excess_sobolev`, `halfspace_pair`. 6 are built on a scratch shape
  with conjuncts of the approved prose added: `tv_density` (+ (a)), `momentdecay_angular` (+ (b)), `newmoments` (+ (a), (b) on
  `newmoments_main`), `laplace_instances` (+ (c)), `newsobolev` (+ `0 < α⋆ < 1`), `simulated_pairs` (the final form with explicit densities).
  The other 20 were drafted by the prover at the freeze from the approved prose and have no critic-checked scratch shape: `spectral_angular`,
  `native_angular`, `bochner_angular`, `sobolev_angular`, `kernel_instances`, `newgammaone_smooth`, `translation_intervals`,
  `newsobolev_cor_bounded`, `newsobolev_cor_line`, `bandlimited_angular`, `bbar_even`, `bandB_facts`, `newgauss_thm_rho`, `newupperone`,
  `newsobolev_E1`, `newsobolev_upper_small`, `newgauss`, `sharp_line`, `slow_gauss_A`, `halfspace_geometry`. These need the clause-by-clause
  check most. An earlier version of the prover-log entry said "23 verbatim, 16 drafted"; it was corrected after the proofs to 13 + 6 + 20.
* Freeze-time encodings (the docstring's list, repeated under Encodings): Q1 (a) ∧ (b) under one name; Q12's cases without `b`, `m`; Q20 as
  one claim with `T_N, w_N` before the kernel; Q15(c) with `ĥ′` the derivative of `ftA bandH`; Q7(c) positive definiteness on ℝ with `x²`;
  Q28 every `a > 0` and `ℝ≥0` weights with the probability conjuncts; Q29(b) (G2) for every `w₀ > 0`.
* Q26 `excess_sobolev` uses the 31tr route theorem `Wave31tr.RouteExcess.excess_ii_route` (its type is literally `Wave31tr.Claims.excess_ii`,
  and it is the theorem by which 31tr's target `excess_ii` is proved; 31tr audited PASS with notes, commit `ca19d29`), part (Pr), with (A1) from
  31tp `mmd_fourier` and (A3) from Q5(b). Q12 `newsobolev_cor_OP` uses, besides the certified `Wave31tl.lorate_i`, `lorate_iii`,
  `lorate_batches`, proved route-level helpers of Wave31tl and Wave30tz (`Wave31tl.Route.Tbet_mono`, `Route.ofReal_one_sub_le`,
  `Basic.floor_ge_of_mesh`, `Basic.mesh_nonneg`, `Arith.label_le_two`, `Wave30tz.Limits.run_alphaLo_nonneg`). Other certified theorems used
  by the routes: `Wave31tl.same_rate`, `Wave31to.newconverse`, `newapproxgen_i`, `_ii`, `_iii_a`, `newapprox_err`, `newslope_b`,
  `Wave31ti.pathconvex`, `pathconvex_ii`, `Wave18b.Dpop_anti`, and 31tp L1–L30.
* Observations of the proof helpers (generalisations available, not claimed): `newgammaone`'s route uses neither `s > d/2` nor
  `finrank V = d` (the Sobolev case is argued directly on `V` through 31tp L16, L9, L19(a)); `halfspace_pair`'s route gives `α⋆ ≤ 2^{−d}`
  (stronger than the frozen `< 1`); Q20's route replaces the printed "`G_w → G₀` uniformly" by an explicit bound of the moment solver
  (`Lib/MomentTrim/Solver`: the solver on `[−L, L]` by scaling the `[−1, 1]` one, `|S_L(m)(t)| ≤ L^{−1}KΣ_jL^{−j}|m_j|`, `K` the operator norm
  of `𝒢₁`), a different proof of the same statement; Q21 `newsobolev_upper_small` avoids a `C ≤ 0` case split by running Q19 with
  `C′ = max(C, 1)`, so that claim carries no `0 < C` guard, unlike Q19 and Q20(a). The route theorems of Q1–Q7, Q8 (both), Q9, Q10,
  Q12 OP, Q14, Q15 (both), Q18, Q25(c1), Q28 and Q29 (both) take no other claim as hypothesis; of the claims passed to chunk T only the fourth
  conjunct of `tv_density` (b) and the Bochner identity of `bochner_angular` are used.
* Readings to check against the paper (stated as drafted, all approved by the critics): Q5's "a Sobolev kernel of order `s`" through the
  two-sided spectral bound (§1 :82); Q6's "guarantees at best" as an exponent inequality (D15; the paper wording corrected by #6b); Q24's "sharp"
  as `D̄ ≍ ε^γ` for every pair vanishing exactly to order `r`; Q22(c)'s exponential margin on all of `(0, α⋆]` (D7); Q25(e)'s "not
  `O((n∧m)^{−a})`" in the strong form; Q12 OP's `O_P` one-sided at probability `1 − η` with the margin as a hypothesis.
* Non-vacuity of the run class of Q12 OP, Q25(b) and Q27(b) rests on 31tr (T4 existence, T5 inclusion of `IsPaperRun` in `IsWitnessRun ∧
  IsDefaultRun`); 31tr is certified and audited, so the source's "conditional on 31tr until it certifies" (D3) is resolved. Q29's pair gives
  the hypotheses of Q11 and Q12 case 1 only through a hand composition with Q1(b) (`T(2) = 0`); a composed claim was optional (critic v2) and
  was not frozen.
* The printed line numbers are those of `1fbc8df`; for the post-freeze shifts see Source.
