import StatFormal.Archive.Wave24a.Statements
import StatFormal.Archive.OTFD.WaveL8.Statements
import StatFormal.Archive.WaveP3c.Statements
import StatFormal.Archive.Wave29a.Statements
import StatFormal.Archive.Wave10b.Statements
import StatFormal.Archive.Wave27a.Statements
import StatFormal.Archive.WaveP2a.Statements
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# FROZEN STATEMENTS — wave 29m: DISCHARGES of conditional/partial otfd C and B results — C `cor:conditional-uniform-x`
# (the `x`-uniform potential convergence), `cor:coordinate-obstruction-empirical` (the slow schedule),
# `lem:cond-rank-consistency` (Step 6), `prop:cond-paths` (iii); B `prop:band-two-stage` (the schedule, fixed-`K`
# containment discharged), `prop:band-injectivity` (i) for the entropic map, `prop:width` (DKW without Massart)

Sources (current text of 2026-10-20, `otfd/papers/`):
* C `cor:conditional-uniform-x` (`C_conditional/supplement.tex:2775-2785`, proof `:1151-1158`), with
  `ass:conditional-oos` and `thm:conditional-band-limits` (`main.tex:654-685`).
* C `prop:cond-paths` (`supplement.tex:2933-2943`, proof `:2163-2171`, `def:cond-path` `:2925-2931`).
* C `cor:coordinate-obstruction-empirical` (`supplement.tex:501-515`, proof `:517-533`), with the setting of
  `subsec:supp-coordinate` (`:236-258`) and `prop:coordinate-obstruction`(c) (frozen Wave 10b `coord_limit`).
* C `lem:cond-rank-consistency` (`main.tex:1002-1010`, proof `supplement.tex:2064-2114`, Step 6 `:2111-2113`).
* B `prop:band-two-stage` (`B_bands/supplement.tex:1408-1422`, proof `:2413-`), with `thm:band-containment`.
* B `prop:band-injectivity` (`supplement.tex:4487-4509`, proof `:4510-4532`).
* B `prop:width` (`main.tex:943-958`, proof `supplement.tex:3257-3274`).
Imports the frozen statement files of waves 24a (`conditional_uniform_x*`), L8 (and through it L1, L3, L4, 15b, 23c,
24e: `IsCMMapAE`, `RefLaw`, `WeightedFit`, `lagPot`, `rankMap`, `ColumnEq`, `entMap`, `cond_potentials_weighted`,
`cond_rank_consistency_uncond`), P3c, 29a (`RefPot`, `coordobs_fixed_eps`), 10b (`IsCompactSupport`, `locLaw`,
`brenierPot`, `brenierMap`), 27a (`band_two_stage_schedule`, and through it 23a `popSupp`, `fitSupp`, `empCDF`,
`scoreCDF`, `scoreQuant`, `omegaHat`, OTFD Wave 3 `bandScore`, `inflBand`), P2a (`FixedKOOSInexact`), not copied;
Mathlib and Tau Ceti (`wassersteinEDist`) otherwise. One new definition: `UnifWeightedFit` (the frozen `WeightedFit`
at every query plus four uniformity clauses).

Covered:
* `cor:conditional-uniform-x`, its premise DISCHARGED: `cux_potentials` (the `x`-uniform potential convergence: from
  `ass:conditional-oos` uniformly in `x ∈ D₀` and weak continuity of `x ↦ P_{K,x}`, the normalised Laguerre and fitted
  potentials converge to `χ_x` uniformly on compacts of `int 𝒰_K`, uniformly in `x`); `cux_maps`, `cux_bands` (the
  frozen Wave 24a `conditional_uniform_x_maps`, `conditional_uniform_x` with that premise replaced by the
  uniform-OOS hypotheses; route checks `route_cux_maps`, `route_cux_bands`).
* `prop:cond-paths` (iii): `cpaths_iii` (route check `route_cpaths_iii` from `cux_maps`).
* `cor:coordinate-obstruction-empirical`, the slow schedule: `coordobs_slow_schedule` (route check
  `route_coordobs_slow_schedule` from the frozen Wave 29a `coordobs_fixed_eps`, Wave 10b `coord_limit`, Wave 22b
  `selfloc_staircase`).
* `lem:cond-rank-consistency`, Step 6: `crank_prob` (a.s. and in probability at a test point `Z ∼ P_{K,x}`; route
  check `route_crank_prob` from the frozen wave-L8 `cond_rank_consistency_uncond`).
* `prop:band-two-stage`, the schedule with the fixed-`K` containment DISCHARGED: `twostage_schedule` (route check
  `route_twostage_schedule` from the frozen Wave 27a `band_two_stage_schedule` and the certified WaveP2a
  `band_containment_discharged`).
* `prop:band-injectivity` (i) + (ii), entropic map: `binj_entropic_contour` (`∂Q̂(A) = Q̂(∂A)` for every compact `A`,
  no injectivity or invariance-of-domain hypothesis; route check `route_binj_entropic_contour` from the frozen
  Wave 24e `band_injectivity_entropic` and WaveP3a `band_injectivity_contour`).
* `prop:width` without DKW–Massart (VARIANT, non-sharp constant; the printed `t` and `1 − 1/n₂` are NOT reached):
  `width_sandwich_dkw` ((ii) at any `t`, probability `≥ 1 − 4|Θ|(k + 1)e^{−nt²/2}`), `width_coverage_dkw` ((i),
  `≥ 1 − α − t − 4|Θ|(k + 1)e^{−nt²/2}`), `k ≥ 1`, `2 ≤ kt`. The DKW-type inequality they use
  (`P(∃ s, λ < |Ĝ − G|) ≤ 4(k + 1)e^{−nλ²/2}`) is not a printed claim (the paper cites Massart) and is library only:
  `StatFormal.DKW.dkw_bracket`, restated in the frozen notation as `width_dkw_proof` in `RouteWidth.lean`.

Not covered (declared):
* `cor:conditional-uniform-x`, last sentence ("self-transport weights … supported grids and exact response fits …
  satisfy these premises"): the certified metric localisation (Wave 26b, Wave 29a `metricloc_quad_uniform`) supplies
  the `W₁`-uniform target clause of `UnifWeightedFit`, but no certified result supplies the uniform-in-`x` gap and
  fit-closeness clauses (`lem:weighted-duality` uniformly in the query); not attempted.
* `prop:width`: the printed level `t = (log(2n|Θ|)/(2n))^{1/2}` NEEDS Massart's constant exactly (`2|Θ|e^{−2nt²} =
  1/n`); Massart (1990) is not formalised, so the frozen Wave 23a `width_sandwich`, `width_coverage` stay conditional.
  The variant claims hold at every `t` with `4(k + 1)e^{−nt²/2}` in place of `2e^{−2nt²}`.
* `prop:band-injectivity` (i) for maps that are only continuous and injective (the inclusion `∂Q̂(A) ⊆ Q̂(∂A)` needs
  Brouwer's invariance of domain, not in Mathlib); the quadratic/Karp instances beyond the frozen WaveP3a (iii).
* `prop:cond-paths` (ii) beyond the frozen `rk_paths_labels` (unchanged).
* `cor:coordinate-obstruction-empirical`: existence of the empirical potentials (as in Wave 29a).

Encodings (to be checked by the critic):
* `UnifWeightedFit D₀ μ P U α ν χn g ζ`: the frozen `WeightedFit μ (P x) U (α · x) (ν · x) (χn · x) (g · x) (ζ · x)` at
  every `x ∈ D₀` (atomic grids and weighted targets, Laguerre potentials, the hard semi-dual gap inequality), plus
  "uniformly in `x`": `∀ ε > 0, ∀ᶠ n, ∀ x ∈ D₀` for `W₁(α_{n,x}, μ_K) ≤ ε`, `W₁(P̂_{K,n,x}, P_{K,x}) ≤ ε`,
  `ζ_{n,x} ≤ ε`, `sup_𝒰 |g_{n,x} − χ_{n,x}| ≤ ε` (C: "the premises of `ass:conditional-oos` hold uniformly in
  `x ∈ D₀`", `W₁` as printed). Grids may depend on `x` (C: one grid; generalisation). `x ↦ P_{K,x}` is assumed
  weakly continuous on `D₀` (`ContinuousOn` into `ProbabilityMeasure`; C: `W₁`-continuous, which implies it — the
  Tau Ceti/Mathlib comparison `W₁ < δ² ⇒ d_LP ≤ δ`; generalisation); "common bounded support" is NOT assumed
  (generalisation). Population objects per query as in the frozen wave-L8 claim (`Q_x` Borel, `Q_x#μ_K = P_{K,x}`,
  `μ_K`-a.e. cyclically monotone, `χ_x` convex on `int 𝒰_K`, `Q_x = ∇χ_x` a.e., `inf_{int 𝒰} χ_x = 0`; their
  existence is the certified P3c/L8 first conjunct). The constants `c_{n,x} = inf_𝒰 χ_{n,x}` are binders with `IsGLB`
  in `cux_potentials` (as in the frozen L8 claim); in `cux_maps`/`cux_bands` they are constructed (continuity of the
  Laguerre potential). `cux_maps`/`cux_bands` add `O ⊆ int 𝒰_K` (C: `S ⊆ int 𝒰_K` and the potentials converge on
  compacts of `int 𝒰_K`). All statements are per realisation ("almost surely" = for every realisation in the a.s. event,
  as the frozen Wave 24a claims).
* `cpaths_iii`: "the points `τ_p v` with `p ≤ 1 − δ` lie in `A_{K,1−δ} = S`" is a hypothesis (`τ p • v ∈ S` for
  `0 < p ≤ 1 − δ`, `v ∈ V`); paths `γ_v(p | x)(t) = 𝔪(t) + ⟨e_K(t), Q̂_x(τ_p v)⟩`, `‖e_K(t)‖ ≤ E_K`.
* `coordobs_slow_schedule`: the setting of the frozen `coordobs_fixed_eps` verbatim (ε-free part); population
  potentials a family `(ψ_ε, φ_ε)` with `RefPot` at every `ε > 0`; empirical potentials a fixed selection
  `(ψ_{n,ε}, φ_{n,ε})(ω)` with `RefPot` for each `ε > 0`, a.s., at every `n ≥ 1`; the hypotheses of the frozen
  `coord_limit` at `r = x` (continuity of `φ_ε` on `D` follows from `RefPot`). ADDED premise: for every `ε > 0` and `n`,
  `ω ↦ W₁(P̂^ν_{K,n,x}(ε), P^ν_{K,ε,x})` is a.e.-measurable (see Paper notes (2): without measurability the
  staircase step is false in the abstract). "`ε_{X,n} ↓ 0`" is `0 < ε_{X,n}`, `Antitone`, `→ 0`.
* `crank_prob`: fits on `(Ω, Pr)` (sizes `n_k, M_k`, strengths, grids, responses, duals all random), the frozen L8
  hypotheses holding a.s.; `Z` measurable with `Pr.map Z = P_{K,x} ≪ Leb`; NO independence of `Z` from the fits
  (generalisation); `ω ↦ F̂_k(ω)(Z(ω))` a.e. strongly measurable (needed for `TendstoInMeasure`, as in the frozen
  `cond_transfer_consistency_prob_weighted`). `F_{K,x} = ∇X_{K,x}`, `X_{K,x}(y) = sup_{w ∈ int 𝒰} (⟨w, y⟩ − χ(w))`, as
  in the frozen claim.
* `twostage_schedule`: the hypotheses of the frozen `band_two_stage_pop`/`band_two_stage_schedule`; sieve laws `μ_K`,
  `P_K` as probability measures equal to the push-forwards by `Π_K = truncK`; at every `K` the printed fixed-`K`
  assumption (frozen `FixedKOOSInexact`); computed edges `x̂^↑_{K,n}(t) = fitSupp (B̄(0, τ_K)) (entMap …) (Π_K g_t)`,
  `x̂^↓ = −fitSupp(…)(−Π_K g_t)` (the frozen computed band, `𝔪 = 0`, region `A_{K,p} = B̄(0, τ_K)`); ADDED premise:
  the fixed-`K` failure events are measurable (the frozen Wave 27a card names exactly this gap: continuity from above
  fails for outer measures). Population map at `K`: the frozen `Q_{+,K}`; `HasLaw`, a.e. cyclical monotonicity
  (subgradients of `supAff`) and the bound `‖Q_{+,K}‖ ≤ sup_T ‖·‖` are derived, not assumed.
* `binj_entropic_contour`: `K ≥ 1`, `n ≥ 1`, `ε > 0`, `M_K = I`, `A` any compact set (C/B: `A_{K,p}`, compact).
* `width_*`: frozen Wave 23a objects verbatim; `t > 0` any level, `k ≥ 1` integer with `2 ≤ kt`.

Proof notes (untrusted; `#print axioms`: propext, Classical.choice, Quot.sound for all 10 claims):
* Routes `Wave29m/Route{Cux,CoordSlow,Crank,TwoStage,Binj,Width}.lean`, new library
  `Foundations/UniformQuery/W1Weak.lean` (`W₁`-closeness to a weakly convergent family gives weak convergence, through
  the Lévy–Prokhorov metric) and `Foundations/DKW/Bracket.lean` (two-sided Hoeffding for empirical frequencies under
  `Measure.pi`; quantile bracketing with right continuity `G(q_j) ≥ j/k` and left limits `G(q_j−) ≤ j/k`).
* `cux_potentials` is the paper's subsequence argument: violating `(n_k, x_k, u_k)`, `x_k → x`; the frozen L8 theorem
  on the diagonal `(n_k, x_k)` (a `WeightedFit` for `P_x`); the same theorem at each fixed `x_k` and on a second
  diagonal `(m_k, x_k)` gives `χ_{x_k} → χ_x` uniformly on `S` — no joint continuity of the potentials is assumed.
* `crank_prob`: the population rank potential is Lipschitz (normalisation, `𝒰` bounded); Rademacher (Mathlib) and
  `P_{K,x} ≪ Leb` put `Z` a.s. at a differentiability point, where the frozen claim gives convergence for every fit.
* `binj_entropic_contour`: spanning — `entMap` is `C^∞` with `⟨h, DQ̂(u)h⟩ = (2/ε) Var_{w(u)}(⟨h, Z⟩) > 0` for `h ≠ 0`, so `DQ̂(u)` is
  injective, hence a continuous linear equivalence, and the frozen P3a theorem applies on `U = ℝ^K`;
  non-spanning — `Q̂(A) ⊆ conv(Z)` has empty interior, and a line of constancy through `u ∈ A` leaves the compact `A`
  through `∂A`.
* No tautology (no conclusion is a hypothesis; `UnifWeightedFit` contains no convergence of potentials or maps). No
  junk: every `Measure.map` is guarded by `Measurable`/`HasLaw`; `sSup`s are of nonempty bounded sets or the frozen
  ones; `W₁` is the Tau Ceti extended distance (no `toReal`); the only `toReal` is the frozen `scoreCDF`.
* Nonvacuity: `cux_*` with `D₀ = {x}` reduce to the frozen wave-L8/24a claims (whose hypotheses are satisfiable,
  WaveL4 card); `coordobs_slow_schedule` in the Wave 29a example (`P_C = δ_b`); `crank_prob` with a deterministic
  `Ω`-constant fit; `twostage_schedule` inherits the frozen Wave 27a nonvacuity plus measurable fits; `binj` and
  `width_*` have no restrictive hypotheses.

Paper notes:
(1) C `cor:conditional-uniform-x`: weak continuity of `x ↦ P_{K,x}` suffices, and common bounded support is not used
  for the potential half; uniform convergence `χ_{x_k} → χ_x` follows from the pointwise theorem on a second diagonal.
(2) C `cor:coordinate-obstruction-empirical`: the deterministic slow schedule needs the `W₁` errors to be measurable in
  the sample (the reference measures `ν_m` are random and nothing is said about their measurability). Abstractly the
  staircase is false without it: partition `[0,1]` into continuum many sets `A_σ` of full outer Lebesgue measure
  indexed by the nondecreasing `σ : ℕ → ℕ` with `σ → ∞` (a transfinite Bernstein construction), and put
  `E_{j,n}(ω) = 1{j = σ_ω(n)}` (`σ_ω` the index of the cell of `ω`); every `E_{j,·} → 0` everywhere (`σ_ω → ∞`), yet
  along every deterministic schedule `σ` the error `E_{σ(n),n}` is `1` on `A_σ`, which is not contained in a null set.
  In the paper's setting the gap is only the measurability of the random reference measures `ν_m` (the data enter
  measurably); satisfiable, e.g. `ν_m` deterministic or a measurable function of an auxiliary sample.
(3) C `lem:cond-rank-consistency` Step 6: neither independence of `Z` nor dominated convergence is needed; convergence
  holds at every differentiability point of `X_{K,x}` on one a.s. event, hence a.s. at `Z` for any `Z ∼ P_{K,x}`.
(4) B `prop:band-two-stage`: combining the a.s. `thm:band-containment` with the in-probability staircase needs
  measurable failure events (a.s. eventual containment gives outer probabilities `→ 0` only for measurable events);
  they are measurable when the fitted duals `f^{(n)}` are measurable in the sample (both edges are continuous in the
  direction, so `∀ t` reduces to a countable dense set of directions); `ass:fixedK-oos`(iv) asks this of the
  residuals `r_n` only. Worth one clause in the text.
(5) B `prop:width` (formalisation remark, NOT a manuscript defect: the cited DKW–Massart bound holds for every
  `t`, and the printed `t`, `1 − 1/n₂` are correct with it): an elementary bracketing bound gives the same statements
  with `4(k + 1)e^{−nt²/2}`, `2 ≤ kt`, in place of `2e^{−2nt²}`; the printed constants need Massart exactly.
(6) B `prop:band-injectivity`: for the entropic map, (i)'s conclusion holds for every compact region with no further
  hypothesis (local diffeomorphism when spanning; trivially otherwise), so the injectivity hypothesis of (i) is needed
  only for general maps.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave29m

open StatFormal.OTFD.WaveL1 (IsCMMapAE Euc)
open StatFormal.OTFD.WaveL3 (RefLaw)
open StatFormal.OTFD.WaveL4 (WeightedFit)

/-! ### Definitions -/

/-- C `ass:conditional-oos` (weighted, verbatim discrete form of the frozen wave-L4 `WeightedFit`) holding
**uniformly in the query** `x ∈ D₀`: at every query the frozen `WeightedFit` holds, and moreover the grids and the
weighted targets converge in `W₁` uniformly in `x ∈ D₀` (`sup_{x∈D₀} W₁(α_{n,x}, μ_K) → 0`,
`sup_{x∈D₀} W₁(P̂_{K,n,x}, P_{K,x}) → 0`), the hard semi-dual gaps vanish uniformly (`sup_x ζ_{n,x} → 0`) and the
fitted potentials are uniformly close to the Laguerre potentials (`sup_x sup_U |g_{n,x} − χ_{n,x}| → 0`). -/
def UnifWeightedFit {K : ℕ} {X : Type*} (D0 : Set X) (μ : ProbabilityMeasure (Euc K))
    (P : X → ProbabilityMeasure (Euc K)) (U : Set (Euc K)) (α ν : ℕ → X → ProbabilityMeasure (Euc K))
    (χn g : ℕ → X → Euc K → ℝ) (ζ : ℕ → X → ℝ) : Prop :=
  (∀ x ∈ D0, WeightedFit μ (P x) U (fun n => α n x) (fun n => ν n x) (fun n => χn n x) (fun n => g n x)
      (fun n => ζ n x)) ∧
    (∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ n in atTop, ∀ x ∈ D0,
      TauCeti.wassersteinEDist 1 (α n x : Measure (Euc K)) (μ : Measure (Euc K)) ≤ ε) ∧
    (∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ n in atTop, ∀ x ∈ D0,
      TauCeti.wassersteinEDist 1 (ν n x : Measure (Euc K)) (P x : Measure (Euc K)) ≤ ε) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x ∈ D0, ζ n x ≤ ε) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x ∈ D0, ∀ u ∈ U, |g n x u - χn n x u| ≤ ε)

namespace Claims

/-! #### C `cor:conditional-uniform-x`: the `x`-uniform potential convergence (DISCHARGE of the premise of the
frozen Wave 24a `conditional_uniform_x_maps`, `conditional_uniform_x`) -/

/-- `x`-uniform potential convergence. On a compact query set `D₀` of a pseudometric space, with the frozen reference
law `RefLaw μ_K 𝒰_K`, conditional targets `x ↦ P_{K,x}` weakly continuous on `D₀`, at each query a population McCann
map `Q_x` (Borel, `Q_x#μ_K = P_{K,x}`, `μ_K`-a.e. cyclically monotone) with a normalised convex potential `χ_x`
(`Q_x = ∇χ_x` `μ_K`-a.e., `inf_{int 𝒰} χ_x = 0`), and `ass:conditional-oos` uniformly in `x ∈ D₀`
(`UnifWeightedFit`): after normalisation by `c_{n,x} = inf_𝒰 χ_{n,x}`, both the Laguerre potentials `χ_{n,x}` and the
fitted potentials `g_{n,x}` converge to `χ_x` uniformly on every compact `S ⊆ int 𝒰_K`, uniformly in `x ∈ D₀`. -/
def cux_potentials : Prop :=
  ∀ (K : ℕ) (X : Type) [PseudoMetricSpace X] (D0 : Set X) (μ : ProbabilityMeasure (Euc K))
    (P : X → ProbabilityMeasure (Euc K)) (U : Set (Euc K)) (Q : X → Euc K → Euc K) (χ : X → Euc K → ℝ)
    (α ν : ℕ → X → ProbabilityMeasure (Euc K)) (χn g : ℕ → X → Euc K → ℝ) (ζ c : ℕ → X → ℝ),
    IsCompact D0 → RefLaw (μ : Measure (Euc K)) U → ContinuousOn P D0 →
    (∀ x ∈ D0, Measurable (Q x) ∧ (μ : Measure (Euc K)).map (Q x) = P x ∧ IsCMMapAE (μ : Measure (Euc K)) (Q x)) →
    (∀ x ∈ D0, ConvexOn ℝ (interior U) (χ x) ∧ Q x =ᵐ[(μ : Measure (Euc K))] gradient (χ x) ∧
      IsGLB (χ x '' interior U) 0) →
    UnifWeightedFit D0 μ P U α ν χn g ζ → (∀ n, ∀ x ∈ D0, IsGLB (χn n x '' U) (c n x)) →
      ∀ S ⊆ interior U, IsCompact S → ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ x ∈ D0, ∀ u ∈ S,
        |χn n x u - c n x - χ x u| ≤ η ∧ |g n x u - c n x - χ x u| ≤ η

/-- `cor:conditional-uniform-x`, maps, with the potential premise DISCHARGED: the hypotheses of `cux_potentials`
(without the normalising constants) and of the frozen Wave 24a `conditional_uniform_x_maps` other than its
`x`-uniform potential convergence — `S` compact, `S_r = cthickening r S ⊆ O ⊆ int 𝒰_K`, `O` open, `HasGradientAt
(χ x) (Q x u) u` on `O`, `(u, x) ↦ Q_x(u)` jointly continuous on `O × D₀`, the fitted maps `T_{n,x}(u)` subgradients
of `g_{n,x}` (tested on `S_r`) at every `u ∈ S`: then `sup_{x∈D₀} sup_{u∈S} ‖T_{n,x}(u) − Q_x(u)‖ → 0`. -/
def cux_maps : Prop :=
  ∀ (K : ℕ) (X : Type) [PseudoMetricSpace X] (D0 : Set X) (μ : ProbabilityMeasure (Euc K))
    (P : X → ProbabilityMeasure (Euc K)) (U : Set (Euc K)) (Q : X → Euc K → Euc K) (χ : X → Euc K → ℝ)
    (α ν : ℕ → X → ProbabilityMeasure (Euc K)) (χn g : ℕ → X → Euc K → ℝ) (ζ : ℕ → X → ℝ)
    (S O : Set (Euc K)) (r : ℝ) (T : ℕ → X → Euc K → Euc K),
    IsCompact D0 → RefLaw (μ : Measure (Euc K)) U → ContinuousOn P D0 →
    (∀ x ∈ D0, Measurable (Q x) ∧ (μ : Measure (Euc K)).map (Q x) = P x ∧ IsCMMapAE (μ : Measure (Euc K)) (Q x)) →
    (∀ x ∈ D0, ConvexOn ℝ (interior U) (χ x) ∧ Q x =ᵐ[(μ : Measure (Euc K))] gradient (χ x) ∧
      IsGLB (χ x '' interior U) 0) →
    UnifWeightedFit D0 μ P U α ν χn g ζ →
    IsCompact S → 0 < r → IsOpen O → Metric.cthickening r S ⊆ O → O ⊆ interior U →
    (∀ x ∈ D0, ∀ u ∈ O, HasGradientAt (χ x) (Q x u) u) → ContinuousOn (fun p => Q p.2 p.1) (O ×ˢ D0) →
    (∀ n, ∀ x ∈ D0, ∀ u ∈ S, ∀ y ∈ Metric.cthickening r S, g n x u + ⟪T n x u, y - u⟫ ≤ g n x y) →
      ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ x ∈ D0, ∀ u ∈ S, ‖T n x u - Q x u‖ ≤ η

/-- `cor:conditional-uniform-x`, bands, with the potential premise DISCHARGED: the hypotheses of `cux_maps` and the
frozen level regions of `conditional_uniform_x` (`A_p ⊆ S` for `0 < p ≤ 1 − δ`, compact convex with interior, in
`supp μ_K`), `‖e_K(t)‖ ≤ E_K`: every band edge is eventually within `η` of the population edge, uniformly in
`x ∈ D₀`, `p` and `t` (`eq:conditional-two-sided` with `sup_{x∈D₀}`). -/
def cux_bands : Prop :=
  ∀ (K : ℕ) (X 𝒯 : Type) [PseudoMetricSpace X] (D0 : Set X) (μ : ProbabilityMeasure (Euc K))
    (P : X → ProbabilityMeasure (Euc K)) (U : Set (Euc K)) (Q : X → Euc K → Euc K) (χ : X → Euc K → ℝ)
    (α ν : ℕ → X → ProbabilityMeasure (Euc K)) (χn g : ℕ → X → Euc K → ℝ) (ζ : ℕ → X → ℝ)
    (A : ℝ → Set (Euc K)) (S O : Set (Euc K)) (r δ EK : ℝ) (T : ℕ → X → Euc K → Euc K) (e : 𝒯 → Euc K),
    IsCompact D0 → RefLaw (μ : Measure (Euc K)) U → ContinuousOn P D0 →
    (∀ x ∈ D0, Measurable (Q x) ∧ (μ : Measure (Euc K)).map (Q x) = P x ∧ IsCMMapAE (μ : Measure (Euc K)) (Q x)) →
    (∀ x ∈ D0, ConvexOn ℝ (interior U) (χ x) ∧ Q x =ᵐ[(μ : Measure (Euc K))] gradient (χ x) ∧
      IsGLB (χ x '' interior U) 0) →
    UnifWeightedFit D0 μ P U α ν χn g ζ →
    IsCompact S → 0 < r → IsOpen O → Metric.cthickening r S ⊆ O → O ⊆ interior U →
    (∀ x ∈ D0, ∀ u ∈ O, HasGradientAt (χ x) (Q x u) u) → ContinuousOn (fun p => Q p.2 p.1) (O ×ˢ D0) →
    (∀ n, ∀ x ∈ D0, ∀ u ∈ S, ∀ y ∈ Metric.cthickening r S, g n x u + ⟪T n x u, y - u⟫ ≤ g n x y) →
    (∀ t, ‖e t‖ ≤ EK) →
    (∀ p, 0 < p → p ≤ 1 - δ → IsCompact (A p) ∧ Convex ℝ (A p) ∧ (interior (A p)).Nonempty ∧
      A p ⊆ (μ : Measure (Euc K)).support ∧ A p ⊆ S) →
      ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ x ∈ D0, ∀ p, 0 < p → p ≤ 1 - δ → ∀ t,
        ∀ v ∈ ({e t, -e t} : Set (Euc K)),
          ∃ a b : ℝ, StatFormal.Wave17a.hPop (μ : Measure (Euc K)) (A p) (Q x) v = a ∧
            StatFormal.Wave21b.supE (A p) (T n x) v = b ∧ |b - a| ≤ η

/-! #### C `prop:cond-paths` (iii) -/

/-- `prop:cond-paths` (iii): under the hypotheses of `cux_maps` (those of `cor:conditional-uniform-x`), with a level
map `p ↦ τ_p`, a set `V` of signs and `τ_p v ∈ S = A_{K,1−δ}` for `0 < p ≤ 1 − δ`, `v ∈ V` (the proof's "the points
`τ_p v` with `p ≤ 1 − δ` lie in `A_{K,1−δ}`"), `sup_{x∈D₀} sup_{p≤1−δ} sup_{v∈V} ‖Q̂_x(τ_p v) − Q_{K,x}(τ_p v)‖ → 0`,
and the scenario paths `γ_v(p | x)(t) = 𝔪(t) + ⟨e_K(t), Q̂_x(τ_p v)⟩` converge to the population paths uniformly in
`t`, the level, the direction and the covariate (`‖e_K(t)‖ ≤ E_K`). -/
def cpaths_iii : Prop :=
  ∀ (K : ℕ) (X 𝒯 : Type) [PseudoMetricSpace X] (D0 : Set X) (μ : ProbabilityMeasure (Euc K))
    (P : X → ProbabilityMeasure (Euc K)) (U : Set (Euc K)) (Q : X → Euc K → Euc K) (χ : X → Euc K → ℝ)
    (α ν : ℕ → X → ProbabilityMeasure (Euc K)) (χn g : ℕ → X → Euc K → ℝ) (ζ : ℕ → X → ℝ)
    (S O : Set (Euc K)) (r δ EK : ℝ) (T : ℕ → X → Euc K → Euc K) (τ : ℝ → ℝ) (V : Set (Euc K))
    (mfrak : 𝒯 → ℝ) (e : 𝒯 → Euc K),
    IsCompact D0 → RefLaw (μ : Measure (Euc K)) U → ContinuousOn P D0 →
    (∀ x ∈ D0, Measurable (Q x) ∧ (μ : Measure (Euc K)).map (Q x) = P x ∧ IsCMMapAE (μ : Measure (Euc K)) (Q x)) →
    (∀ x ∈ D0, ConvexOn ℝ (interior U) (χ x) ∧ Q x =ᵐ[(μ : Measure (Euc K))] gradient (χ x) ∧
      IsGLB (χ x '' interior U) 0) →
    UnifWeightedFit D0 μ P U α ν χn g ζ →
    IsCompact S → 0 < r → IsOpen O → Metric.cthickening r S ⊆ O → O ⊆ interior U →
    (∀ x ∈ D0, ∀ u ∈ O, HasGradientAt (χ x) (Q x u) u) → ContinuousOn (fun p => Q p.2 p.1) (O ×ˢ D0) →
    (∀ n, ∀ x ∈ D0, ∀ u ∈ S, ∀ y ∈ Metric.cthickening r S, g n x u + ⟪T n x u, y - u⟫ ≤ g n x y) →
    (∀ p, 0 < p → p ≤ 1 - δ → ∀ v ∈ V, τ p • v ∈ S) → (∀ t, ‖e t‖ ≤ EK) →
      ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ x ∈ D0, ∀ p, 0 < p → p ≤ 1 - δ → ∀ v ∈ V,
        ‖T n x (τ p • v) - Q x (τ p • v)‖ ≤ η ∧
          ∀ t, |(mfrak t + ⟪e t, T n x (τ p • v)⟫) - (mfrak t + ⟪e t, Q x (τ p • v)⟫)| ≤ EK * η

/-! #### C `cor:coordinate-obstruction-empirical`: the slow schedule -/

/-- `cor:coordinate-obstruction-empirical`, last sentence: in the setting of the frozen Wave 29a `coordobs_fixed_eps`
(i.i.d. pairs `(C_i, Z_i)` of law `P_C ⊗ P_{K,·}`, `C_i ∈ D`, `Z_i ∈ B̄(0, R)`, reference measures `ν_{m_n}` carried by
`S` converging weakly a.s.), with population potentials `(ψ_ε, φ_ε)` solving the frozen `RefPot` system at every
strength `ε > 0`, empirical potentials `(ψ_{n,ε}, φ_{n,ε})` of `(ν_{m_n}, P̂_{C,n})` solving it (for each `ε > 0`,
almost surely, at every `n ≥ 1`), the `W₁` error `ω ↦ W₁(P̂^ν_{K,n,x}, P^ν_{K,ε,x})` a.e.-measurable for every `ε > 0` and `n`,
and the hypotheses of `prop:coordinate-obstruction`(c) at `r = x` (those of the frozen Wave 10b `coord_limit`:
`φ_ε → φ₀` uniformly on `D`, `φ₀` continuous on `D`, the Brenier potential `β_X` differentiable at `x`, and `c ↦ P_{K,c}`
`W₁`-continuous at `T_X(x)` within `D`): there are deterministic strengths `ε_{X,n} > 0`, nonincreasing, `ε_{X,n} → 0`,
with `W₁(P̂^ν_{K,n,x}, P_{K,T_X(x)}) → 0` almost surely, `P̂^ν_{K,n,x}` computed at strength `ε_{X,n}`. -/
def coordobs_slow_schedule : Prop :=
  ∀ (q K : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (PC ν : Measure (Euc q)) [IsProbabilityMeasure PC] [IsProbabilityMeasure ν] (κ : Kernel (Euc q) (Euc K))
    [IsMarkovKernel κ] (R : ℝ) (S D : Set (Euc q)) (νs : ℕ → Ω → Measure (Euc q))
    (Cs : ℕ → Ω → Euc q) (Zs : ℕ → Ω → Euc K) (ψ φ : ℝ → Euc q → ℝ) (φ₀ : Euc q → ℝ)
    (ψn φn : ℝ → ℕ → Ω → Euc q → ℝ) (x : Euc q),
    StatFormal.Wave10b.IsCompactSupport ν S → StatFormal.Wave10b.IsCompactSupport PC D →
    (∀ c ∈ D, κ c (Metric.closedBall 0 R)ᶜ = 0) →
    (∀ i, Measurable (Cs i)) → (∀ i, Measurable (Zs i)) → iIndepFun (fun i ω => (Cs i ω, Zs i ω)) P →
    (∀ i, P.map (fun ω => (Cs i ω, Zs i ω)) = PC ⊗ₘ κ) →
    (∀ n ω, IsProbabilityMeasure (νs n ω) ∧ νs n ω Sᶜ = 0) →
    (∀ᵐ ω ∂P, ∀ f : BoundedContinuousFunction (Euc q) ℝ,
      Tendsto (fun n => ∫ r, f r ∂(νs n ω)) atTop (𝓝 (∫ r, f r ∂ν))) →
    (∀ ε, 0 < ε → StatFormal.Wave29a.RefPot ν PC S D ε (ψ ε) (φ ε)) →
    (∀ ε, 0 < ε → ∀ᵐ ω ∂P, ∀ n, 0 < n → StatFormal.Wave29a.RefPot (νs n ω)
      (StatFormal.Wave23b.empW (fun _ : Fin n => 1 / (n : ℝ)) (fun i => Cs i ω)) S D ε (ψn ε n ω) (φn ε n ω)) →
    (∀ ε, 0 < ε → ∀ n, AEMeasurable (fun ω => TauCeti.wassersteinEDist 1
      (StatFormal.Wave12b.wEmp (StatFormal.OTFD.Bands.softmax fun i : Fin n =>
          (φn ε n ω (Cs i ω) - ‖x - Cs i ω‖ ^ 2) / ε) (fun i : Fin n => Zs i ω))
      (StatFormal.Wave10b.locLaw PC D κ (φ ε) ε x)) P) →
    ContinuousOn φ₀ D → TendstoUniformlyOn φ φ₀ (𝓝[>] 0) D →
    DifferentiableAt ℝ (StatFormal.Wave10b.brenierPot D φ₀) x →
    Tendsto (fun c => TauCeti.wassersteinEDist 1 (κ c) (κ (StatFormal.Wave10b.brenierMap D φ₀ x)))
      (𝓝[D] (StatFormal.Wave10b.brenierMap D φ₀ x)) (𝓝 0) →
      ∃ εs : ℕ → ℝ, (∀ n, 0 < εs n) ∧ Antitone εs ∧ Tendsto εs atTop (𝓝 0) ∧
        ∀ᵐ ω ∂P, Tendsto (fun n => TauCeti.wassersteinEDist 1
          (StatFormal.Wave12b.wEmp (StatFormal.OTFD.Bands.softmax fun i : Fin n =>
              (φn (εs n) n ω (Cs i ω) - ‖x - Cs i ω‖ ^ 2) / εs n) (fun i : Fin n => Zs i ω))
          (κ (StatFormal.Wave10b.brenierMap D φ₀ x))) atTop (𝓝 0)

/-! #### C `lem:cond-rank-consistency`, Step 6 -/

/-- `lem:cond-rank-consistency`, last sentence (Step 6 of the proof): on a probability space carrying the fits and a
test point `Z` of law `P_{K,x} ≪ Leb`, if almost surely the fits satisfy the hypotheses of the frozen moment-free
wave-L8 `cond_rank_consistency_uncond` (the paper's fit assumption `WeightedFit` with exact entropic fits: counting
grids in `𝒰_K`, the column equations, `ε_n log((M_n + 1)(N_n + 1)) → 0`, responses in `B̄(0, R)`; sizes, strengths and
fits may be random), then, for the population McCann map `Q` and its normalised potential `χ`, the fitted rank map at
`Z` converges to the population rank map `F_{K,x} = ∇X_{K,x}`, `X_{K,x}(y) = sup_{w ∈ int 𝒰} (⟨w, y⟩ − χ(w))`, almost
surely, and hence in probability (`TendstoInMeasure`; each `ω ↦ F̂_n(Z(ω))` a.e. strongly measurable). No independence
of `Z` from the fits is needed: the convergence holds at every differentiability point of `X_{K,x}`, a `P_{K,x}`-full
set (Rademacher). -/
def crank_prob : Prop :=
  ∀ (K : ℕ) (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (n M : ℕ → Ω → ℕ) (ε : ℕ → Ω → ℝ) (R : ℝ) (z : ∀ k ω, Fin (n k ω + 1) → Euc K)
    (f : ∀ k ω, Fin (n k ω + 1) → ℝ) (u : ∀ k ω, Fin (M k ω + 1) → Euc K) (gc : ∀ k ω, Fin (M k ω + 1) → ℝ)
    (μ P : ProbabilityMeasure (Euc K)) (U : Set (Euc K)) (Q : Euc K → Euc K) (χ : Euc K → ℝ)
    (α ν : ℕ → Ω → ProbabilityMeasure (Euc K)) (ζ : ℕ → Ω → ℝ) (Z : Ω → Euc K),
    RefLaw (μ : Measure (Euc K)) U → Measurable Q → (μ : Measure (Euc K)).map Q = P →
    IsCMMapAE (μ : Measure (Euc K)) Q →
    ConvexOn ℝ (interior U) χ → Q =ᵐ[(μ : Measure (Euc K))] gradient χ → IsGLB (χ '' interior U) 0 →
    (∀ᵐ ω ∂Pr, WeightedFit μ P U (fun k => α k ω) (fun k => ν k ω)
        (fun k => StatFormal.Wave23c.lagPot (z k ω) (f k ω)) (fun k => StatFormal.Wave23c.lagPot (z k ω) (f k ω))
        (fun k => ζ k ω) ∧
      (∀ k, (α k ω : Measure (Euc K)) = ∑ j, ENNReal.ofReal (1 / ((M k ω : ℝ) + 1)) • Measure.dirac (u k ω j)) ∧
      (∀ k j, u k ω j ∈ U) ∧ (∀ k, 0 < ε k ω) ∧
      Tendsto (fun k => ε k ω * Real.log (((M k ω : ℝ) + 1) * ((n k ω : ℝ) + 1))) atTop (𝓝 0) ∧
      (∀ k, StatFormal.Wave24e.ColumnEq (ε k ω) (z k ω) (f k ω) (u k ω) (gc k ω)) ∧ (∀ k i, ‖z k ω i‖ ≤ R)) →
    Measurable Z → Pr.map Z = P → (P : Measure (Euc K)) ≪ volume →
    (∀ k, AEStronglyMeasurable (fun ω => StatFormal.Wave24e.rankMap (ε k ω) (u k ω) (gc k ω) (Z ω)) Pr) →
      (∀ᵐ ω ∂Pr, Tendsto (fun k => StatFormal.Wave24e.rankMap (ε k ω) (u k ω) (gc k ω) (Z ω)) atTop
        (𝓝 (gradient (fun y' => sSup ((fun w => ⟪w, y'⟫ - χ w) '' interior U)) (Z ω)))) ∧
      TendstoInMeasure Pr (fun k ω => StatFormal.Wave24e.rankMap (ε k ω) (u k ω) (gc k ω) (Z ω)) atTop
        (fun ω => gradient (fun y' => sSup ((fun w => ⟪w, y'⟫ - χ w) '' interior U)) (Z ω))

/-! #### B `prop:band-two-stage`: the schedule with the fixed-`K` containment DISCHARGED -/

/-- `prop:band-two-stage`, the schedule sentence, with the fixed-`K` containment premise of the frozen Wave 27a
`band_two_stage_schedule` DISCHARGED: the hypotheses of `band_two_stage_pop`; at every `K` the sieve laws
`μ_K = μ ∘ Π_K⁻¹`, `P_K = P ∘ Π_K⁻¹` (as probability measures) and the printed fixed-`K` assumption
`ass:fixedK-oos` (the frozen WaveP2a `FixedKOOSInexact`: grids, i.i.d. projected responses `Z^{(K)}_i ∼ P_K`,
strengths with `ε_n log(n + 1) → 0`, fitted duals with vanishing residuals); the computed edges are the frozen ones of
the entropic fit at `K` on the sieve region `A_{K,p} = B̄(0, τ_K)`:
`x̂^↑_{K,n}(t) = sup_{u ∈ A_{K,p}} ⟨Π_K g_t, Q̂_{K,n}(u)⟩`, `x̂^↓_{K,n}(t) = −sup_{u ∈ A_{K,p}} ⟨−Π_K g_t, Q̂_{K,n}(u)⟩`
(`𝔪 = 0`); and the fixed-`K` failure events are measurable. Then there is a deterministic nondecreasing `K_n → ∞` along
which, for every `η > 0`, the computed band contains the `η`-deflation of the Hilbert band with probability tending to
one. -/
def twostage_schedule : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (P μ : ProbabilityMeasure H) (T S : Set H) (b : H → ℝ) (x₀ : H) (Q : H → H)
    (SK : (K : ℕ) → Set (Euc K)) (bK : (K : ℕ) → Euc K → ℝ) (zK : (K : ℕ) → Euc K)
    (QK : (K : ℕ) → Euc K → Euc K) (τ : ℕ → ℝ) (p Λ : ℝ)
    (Tt : Type) (gt : Tt → H) (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (μK PK : (K : ℕ) → ProbabilityMeasure (Euc K)) (μs : (K : ℕ) → ℕ → ProbabilityMeasure (Euc K))
    (Zd : (K : ℕ) → ℕ → Ω → Euc K) (εd : ℕ → ℕ → ℝ) (fd : (K : ℕ) → (n : ℕ) → Ω → Fin (n + 1) → ℝ)
    (rd : ℕ → ℕ → Ω → ℝ),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    StatFormal.OTFD.Wave1.PellClass (P : Measure H) →
    (μ : Measure H) (Metric.closedBall 0 1)ᶜ = 0 →
    (∀ r ∈ Icc (0 : ℝ) 1, (μ : Measure H) (Metric.closedBall 0 r) = ENNReal.ofReal r) →
    Metric.closedBall 0 1 ⊆ (μ : Measure H).support →
    IsCompact T → (P : Measure H) Tᶜ = 0 → S.Nonempty → S ⊆ T →
    BddAbove (range fun y : S => ⟪x₀, (y : H)⟫ - b y) →
    Measurable Q → (μ : Measure H).map Q = P →
    (∀ᵐ u ∂(μ : Measure H), StatFormal.OTFD.Wave22a.IsSubgrad (StatFormal.OTFD.Wave22a.supAff S b) u (Q u)) →
    (∀ K, (SK K).Nonempty) → (∀ K, SK K ⊆ StatFormal.OTFD.Wave1.truncK e K '' T) →
    (∀ K, BddAbove (range fun z : SK K => ⟪zK K, (z : Euc K)⟫ - bK K z)) →
    (∀ K, Measurable (QK K)) →
    (∀ K, ((μ : Measure H).map (StatFormal.OTFD.Wave1.truncK e K)).map (QK K) =
      (P : Measure H).map (StatFormal.OTFD.Wave1.truncK e K)) →
    (∀ K, ∀ᵐ z ∂((μ : Measure H).map (StatFormal.OTFD.Wave1.truncK e K)),
      StatFormal.OTFD.Wave22a.IsSubgrad (StatFormal.OTFD.Wave22a.supAff (SK K) (bK K)) z (QK K z)) →
    (∀ᵐ u ∂(μ : Measure H), ∀ v, HasLineDerivAt ℝ (StatFormal.OTFD.Wave22a.supAff S b) ⟪Q u, v⟫ u v) →
    0 < p → p < 1 →
    (∀ K, ENNReal.ofReal p ≤ ((μ : Measure H).map (StatFormal.OTFD.Wave1.truncK e K)) (Metric.closedBall 0 (τ K))) →
    (∀ t, ‖gt t‖ ≤ Λ) →
    (∀ K, (μK K : Measure (Euc K)) = (μ : Measure H).map (StatFormal.OTFD.Wave1.truncK e K)) →
    (∀ K, (PK K : Measure (Euc K)) = (P : Measure H).map (StatFormal.OTFD.Wave1.truncK e K)) →
    (∀ K, StatFormal.WaveP2a.FixedKOOSInexact (μK K) (PK K) (μs K) Pr (Zd K) (εd K) (fd K) (rd K)) →
    (∀ (K n : ℕ) (η : ℝ), 0 < η → MeasurableSet {ω | ¬ ∀ t,
      StatFormal.Wave23a.popSupp ((μ : Measure H).map (StatFormal.OTFD.Wave1.truncK e K)) (Metric.closedBall 0 (τ K))
          (QK K) (StatFormal.OTFD.Wave1.truncK e K (gt t)) ≤
        StatFormal.Wave23a.fitSupp (Metric.closedBall 0 (τ K))
          (StatFormal.Wave23c.entMap (εd K n) (fun i : Fin (n + 1) => Zd K i ω) (fd K n ω))
          (StatFormal.OTFD.Wave1.truncK e K (gt t)) + (η : EReal) ∧
      -StatFormal.Wave23a.fitSupp (Metric.closedBall 0 (τ K))
          (StatFormal.Wave23c.entMap (εd K n) (fun i : Fin (n + 1) => Zd K i ω) (fd K n ω))
          (-StatFormal.OTFD.Wave1.truncK e K (gt t)) ≤
        -StatFormal.Wave23a.popSupp ((μ : Measure H).map (StatFormal.OTFD.Wave1.truncK e K))
          (Metric.closedBall 0 (τ K)) (QK K) (-StatFormal.OTFD.Wave1.truncK e K (gt t)) + (η : EReal)}) →
      ∃ Kn : ℕ → ℕ, Monotone Kn ∧ Tendsto Kn atTop atTop ∧ ∀ η : ℝ, 0 < η →
        Tendsto (fun n => Pr {ω | ¬ ∀ t,
          StatFormal.Wave23a.popSupp (μ : Measure H) (Metric.closedBall 0 p) Q (gt t) ≤
            StatFormal.Wave23a.fitSupp (Metric.closedBall 0 (τ (Kn n)))
              (StatFormal.Wave23c.entMap (εd (Kn n) n) (fun i : Fin (n + 1) => Zd (Kn n) i ω) (fd (Kn n) n ω))
              (StatFormal.OTFD.Wave1.truncK e (Kn n) (gt t)) + (η : EReal) ∧
          -StatFormal.Wave23a.fitSupp (Metric.closedBall 0 (τ (Kn n)))
              (StatFormal.Wave23c.entMap (εd (Kn n) n) (fun i : Fin (n + 1) => Zd (Kn n) i ω) (fd (Kn n) n ω))
              (-StatFormal.OTFD.Wave1.truncK e (Kn n) (gt t)) ≤
            -StatFormal.Wave23a.popSupp (μ : Measure H) (Metric.closedBall 0 p) Q (-gt t) + (η : EReal)})
          atTop (𝓝 0)

/-! #### B `prop:band-injectivity` (i) for the entropic map -/

/-- `prop:band-injectivity` (i) with (ii) for the entropic out-of-sample map `Q̂ = entMap ε Z f` (`ε > 0`, `M_K = I`,
`K, n ≥ 1`), with NO injectivity or invariance-of-domain hypothesis: for every compact region `A` (in particular
`A = A_{K,p}`), `∂Q̂(A) = Q̂(∂A)`. When the `Z_j` affinely span `ℝ^K` the map is injective (frozen (ii)) with invertible
derivative (a local diffeomorphism), and the contour statement holds by the certified WaveP3a
`band_injectivity_contour`; when they do not, `Q̂(A)` lies in a proper affine subspace and is its own boundary, and
every line of constancy through a point of `A` meets `∂A` (the parenthetical of (ii)). -/
def binj_entropic_contour : Prop :=
  ∀ (K N : ℕ) (ε : ℝ) (z : Fin N → Euc K) (f : Fin N → ℝ) (A : Set (Euc K)),
    1 ≤ K → 1 ≤ N → 0 < ε → IsCompact A →
      frontier (StatFormal.Wave23c.entMap ε z f '' A) = StatFormal.Wave23c.entMap ε z f '' frontier A

/-! #### B `prop:width`: the width statements without DKW–Massart (VARIANT, non-sharp constant) -/

/-- `prop:width` (ii) WITHOUT the DKW–Massart premise of the frozen Wave 23a `width_sandwich`, at any level `t > 0`
(in place of the printed `t = (log(2n|Θ|)/(2n))^{1/2}`), with the non-sharp bracketing–Hoeffding DKW constant (library
`StatFormal.DKW.dkw_bracket`; VARIANT: the printed probability `1 − 1/n₂` is not reached): for an integer
`k ≥ 1` with `2 ≤ kt`, with probability at least `1 − 4|Θ|(k + 1)e^{−nt²/2}`, simultaneously for all `θ`,
`q_θ̂(1−α−t) w̄_θ̂ ≤ W_θ̂ ≤ W_θ ≤ q_θ(1−α+t+2/n₂) w̄_θ` (the event is measurable). -/
def width_sandwich_dkw : Prop :=
  ∀ (T : Type) (Θ : Type) [Fintype Θ] [Nonempty Θ] (c w : Θ → T → ℝ) (wbar : Θ → ℝ≥0) (μ : Measure (T → ℝ))
    [IsProbabilityMeasure μ] (n : ℕ) (α : ℝ) (θhat : (Fin n → T → ℝ) → Θ) (t : ℝ) (k : ℕ),
    1 ≤ n → 0 < α → α < 1 → (∀ θ t, 0 ≤ w θ t) → (∀ θ, 0 < wbar θ) →
    (∀ θ, Measurable (StatFormal.OTFD.Wave3.bandScore (c θ) (w θ))) →
    (∀ θ, MeasurableSet {y | θhat y = θ}) →
    (∀ y θ, StatFormal.Wave23a.omegaHat α (StatFormal.OTFD.Wave3.bandScore (c (θhat y)) (w (θhat y))) y *
        wbar (θhat y) ≤ StatFormal.Wave23a.omegaHat α (StatFormal.OTFD.Wave3.bandScore (c θ) (w θ)) y * wbar θ) →
    0 < t → 1 ≤ k → 2 ≤ k * t →
      MeasurableSet {y : Fin n → T → ℝ | ∀ θ,
          StatFormal.Wave23a.scoreQuant μ (StatFormal.OTFD.Wave3.bandScore (c (θhat y)) (w (θhat y))) (1 - α - t) *
              wbar (θhat y) ≤
            StatFormal.Wave23a.omegaHat α (StatFormal.OTFD.Wave3.bandScore (c (θhat y)) (w (θhat y))) y *
              wbar (θhat y) ∧
          StatFormal.Wave23a.omegaHat α (StatFormal.OTFD.Wave3.bandScore (c (θhat y)) (w (θhat y))) y *
              wbar (θhat y) ≤
            StatFormal.Wave23a.omegaHat α (StatFormal.OTFD.Wave3.bandScore (c θ) (w θ)) y * wbar θ ∧
          StatFormal.Wave23a.omegaHat α (StatFormal.OTFD.Wave3.bandScore (c θ) (w θ)) y * wbar θ ≤
            StatFormal.Wave23a.scoreQuant μ (StatFormal.OTFD.Wave3.bandScore (c θ) (w θ)) (1 - α + t + 2 / n) *
              wbar θ} ∧
        ENNReal.ofReal (1 - 4 * Fintype.card Θ * (k + 1) * Real.exp (-n * t ^ 2 / 2)) ≤
          (Measure.pi fun _ : Fin n => μ) {y | ∀ θ,
          StatFormal.Wave23a.scoreQuant μ (StatFormal.OTFD.Wave3.bandScore (c (θhat y)) (w (θhat y))) (1 - α - t) *
              wbar (θhat y) ≤
            StatFormal.Wave23a.omegaHat α (StatFormal.OTFD.Wave3.bandScore (c (θhat y)) (w (θhat y))) y *
              wbar (θhat y) ∧
          StatFormal.Wave23a.omegaHat α (StatFormal.OTFD.Wave3.bandScore (c (θhat y)) (w (θhat y))) y *
              wbar (θhat y) ≤
            StatFormal.Wave23a.omegaHat α (StatFormal.OTFD.Wave3.bandScore (c θ) (w θ)) y * wbar θ ∧
          StatFormal.Wave23a.omegaHat α (StatFormal.OTFD.Wave3.bandScore (c θ) (w θ)) y * wbar θ ≤
            StatFormal.Wave23a.scoreQuant μ (StatFormal.OTFD.Wave3.bandScore (c θ) (w θ)) (1 - α + t + 2 / n) *
              wbar θ}

/-- `prop:width` (i) WITHOUT the DKW–Massart premise of the frozen Wave 23a `width_coverage`, at any level `t > 0`
with the non-sharp constant (VARIANT, as `width_sandwich_dkw`): the selected recalibrated band covers a new curve
with probability at least
`1 − α − t − 4|Θ|(k + 1)e^{−nt²/2}` (`k ≥ 1`, `2 ≤ kt`; the event is measurable). -/
def width_coverage_dkw : Prop :=
  ∀ (T : Type) (Θ : Type) [Fintype Θ] [Nonempty Θ] (c w : Θ → T → ℝ) (μ : Measure (T → ℝ))
    [IsProbabilityMeasure μ] (n : ℕ) (α : ℝ) (θhat : (Fin n → T → ℝ) → Θ) (t : ℝ) (k : ℕ),
    1 ≤ n → 0 < α → α < 1 → (∀ θ t, 0 ≤ w θ t) →
    (∀ θ, Measurable (StatFormal.OTFD.Wave3.bandScore (c θ) (w θ))) →
    (∀ θ, MeasurableSet {y | θhat y = θ}) →
    0 < t → 1 ≤ k → 2 ≤ k * t →
      MeasurableSet {z : (Fin n → T → ℝ) × (T → ℝ) | z.2 ∈ StatFormal.OTFD.Wave3.inflBand (c (θhat z.1))
          (w (θhat z.1)) (StatFormal.Wave23a.omegaHat α
            (StatFormal.OTFD.Wave3.bandScore (c (θhat z.1)) (w (θhat z.1))) z.1)} ∧
        ENNReal.ofReal (1 - α - t - 4 * Fintype.card Θ * (k + 1) * Real.exp (-n * t ^ 2 / 2)) ≤
          ((Measure.pi fun _ : Fin n => μ).prod μ)
            {z | z.2 ∈ StatFormal.OTFD.Wave3.inflBand (c (θhat z.1)) (w (θhat z.1))
              (StatFormal.Wave23a.omegaHat α (StatFormal.OTFD.Wave3.bandScore (c (θhat z.1)) (w (θhat z.1))) z.1)}

end Claims

end StatFormal.Wave29m
