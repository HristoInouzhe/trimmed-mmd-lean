import StatFormal.Archive.Wave24d.Statements
import StatFormal.Archive.Wave24e.Statements

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave P2a (partial-audit wave 2b, FIXEDKOOS-RELAX): otfd B `prop:app-potential-consistency`,
# `thm:band-containment`, `lem:band-pointwise-lower`, `cor:band-coverage-asymptotic` under the PRINTED
# `ass:fixedK-oos` (inexact duals `r_n → 0`, no moment beyond what the paper states, `inf χ_K = 0`)

Sources (current text of `otfd/papers/B_bands/supplement.tex`, read 2026-10-16):
* `ass:fixedK-oos` (`:743-776`: (i) `μ_K` a.c., `𝒰_K` convex compact; (ii) `P_K` first moment; (iii) grids in `𝒰_K`,
  `W₁(μ_{K,m_n}, μ_K) → 0`; (iv) `ε_n log n → 0` and `∫φ̂_n dμ_{K,m_n} + n⁻¹Σf_i ≥ W₂²(μ_{K,m_n}, P̂_{K,n}) − r_n`,
  `r_n ≥ 0` measurable, `r_n → 0` a.s., `φ̂_n` the SOFT `c`-transform).
* `prop:app-potential-consistency` (`:1852-1863`, proof `:1865-1934`, with Step 1 `:1772-1818` and the normalisation
  `X_n(0) = 0`, i.e. `inf_{𝒰} χ_n = 0`, `eq:app-conj-normalization`), `lem:app-subgradient-convergence`(a)
  (`:1938-1950`).
* `thm:band-containment` (`:805-824`), `lem:band-pointwise-lower` (`:836-847`), `cor:band-coverage-asymptotic`
  (`:1074-1105`).
* The frozen claims relaxed (same objects, imported, not copied): Wave 23c (`Wave23c/Statements.lean`) `FixedKOOS`,
  `empLaw`, `lagPot`, `softPot`, `hardCT`, `entMap`, `potential_consistency`, `potential_consistency_maps`,
  `band_containment_discharged`; Wave 24e `band_pointwise_lower`; Wave 24d `band_coverage_asymptotic`, `InSuppBand`;
  Wave 23a `popSupp`, `fitSupp`; wave L1 `IsCMMapAE`. New definitions: `softCT` (the printed `φ̂_n`) and
  `FixedKOOSInexact` (the printed assumption).

Covered:
* `fixedKOOSInexact_of_fixedKOOS`: the frozen `FixedKOOS` is the case `r_n = 0` of `FixedKOOSInexact` (generalisation).
* `prop:app-potential-consistency` as printed: `potential_consistency` (a McCann Brenier map exists; a convex `χ_K` on
  `int 𝒰_K` with `inf χ_K = 0` has `∇χ_K` = every Brenier map a.e.; uniqueness; a.s. `χ_n − c_n → χ_K` and
  `χ̂_n − c_n → χ_K` locally uniformly on `int 𝒰_K`, `c_n = inf_{𝒰_K} χ_n`); `potential_consistency_maps`
  (a.s. `Q̂_n → Q` `μ_K`-a.e.).
* `thm:band-containment` as printed: `band_containment_discharged`.
* `lem:band-pointwise-lower` as printed (entropic map): `band_pointwise_lower`.
* `cor:band-coverage-asymptotic` (i), (iii): `band_coverage_asymptotic_discharged`; (ii): `band_coverage_asymptotic_sup`
  (`liminf ≥ p^♮`, `p^♮` an `IsLUB`).

Not covered (declared):
* `prop:app-potential-consistency`: the extended-value statements (`χ_K` closed, `+∞` off `𝒰_K`, values on `∂𝒰_K`);
  `χ_K` is a function on `int 𝒰_K` (its values elsewhere are unconstrained).
* `thm:band-containment`: the certified band `B̄_K(p)` ("the same holds for the certified band", via
  `prop:band-certificate`; as in the frozen Wave 23a claim).
* `lem:band-pointwise-lower`: the hard-map and certified-edge variants ("the same holds with … `ξ_n` … or by the
  certified support").
* `cor:band-coverage-asymptotic`: (i)'s "likewise for the certified band `B̄_K(p)`"; (ii)'s "since `ς` is nonincreasing, `p^♮ = p` as soon as …"; (iv); the population
  coverage at the levels `p'` (`prop:pop-band-coverage`) is a premise (certified elsewhere in a different encoding,
  Wave 5a `pop_band_coverage` on `Fin K → ℝ`).

Encodings (to be checked by the critic):
* MECHANICAL DIFF against the frozen claims. (1) `FixedKOOS μ P μs Pr Z ε f` ↦ `FixedKOOSInexact μ P μs Pr Z ε f r`
  (new binder `r`): field `moment` (`m₂(P_K)`) DELETED; fields `resid_nonneg`, `resid_lim` ADDED; field `dual`: the
  hard transform `hardCT` ↦ the printed soft transform `softCT`, and `+ r n ω` added. (2) The population map: frozen
  `IsKantorovichOptimalTransportMap (½‖·‖²) μ_K P_K T` ↦ `HasLaw T P_K μ_K ∧ IsCMMapAE μ_K T` (a Brenier map in
  McCann's sense, the paper's `Q_{±,K}` of `thm:prob-content`(c): an `M_K`-monotone map, `½∇χ` with `χ` convex,
  `main.tex:432-435`, at `M_K = I` a gradient of a convex function; the proof of the proposition, step (b), identifies
  it by McCann's uniqueness theorem). This change is FORCED: without `m₂`, `W₂(μ_K, P_K)`
  may be `+∞`, and then Tau Ceti's `IsKantorovichOptimalTransportMap` holds for EVERY `T` pushing `μ_K` to `P_K`
  (`transportMapCost = ∞ = transportCost`), so the frozen clause "`∇φ = T` for every such `T`" would be false. Under
  `m₂` every Kantorovich-optimal map is a McCann map (route `isCMMapAE_of_kantorovich`), so the relaxed claims imply
  the frozen ones (route `RouteImplies`: `*_frozen`, typechecked `Claims.X → Wave23c/Wave24e.Claims.X` for the four
  `FixedKOOS` claims). `HasLaw` (a.e.-measurable, `T#μ_K = P_K`) and not a bare `μ_K.map T = P_K`: in this Mathlib
  `Measure.map f μ` of a non-a.e.-measurable `f` is `dirac Classical.ofNonempty` when `μ ≠ 0` (and `0` when `μ = 0`;
  `Mathlib/MeasureTheory/Measure/Map.lean`, `Measure.map`, `map_of_not_aemeasurable_of_ne_zero`; only the linear
  `Measure.mapₗ` is `0` for non-measurable maps), so the bare equation is not a measurability guarantee. The
  existence clause of `potential_consistency` writes `Measurable T ∧ μ_K.map T = P_K` (no junk). (3) Normalisation: frozen `x₀ ∈ int 𝒰_K`, `φ(x₀) = 0`, `χ_n − χ_n(x₀)` ↦ the printed `inf χ_K = 0`
  (`IsGLB (φ '' int 𝒰_K) 0`) and `χ_n − c_n` with `IsGLB (χ_n '' 𝒰_K) (c_n)` (`c_n` exists and is unique: `χ_n`
  continuous, `𝒰_K` compact; the paper's `X_n(0) = −inf_{𝒰} χ_n = 0`); the binder `x₀` and its premise deleted.
  (4) `band_coverage_asymptotic_discharged`: the frozen Wave 24d claim with `Q := T`, `Q̂_n(ω) := entMap` of the fit,
  its premise `∀ᵐ ω, ∀ᵐ u ∂μ|A, Q̂_n(ω, u) → Q(u)` replaced by `FixedKOOSInexact` and `T` a McCann map; `P` (on `Ω`)
  renamed `Pr`, the test vector `Z` renamed `Y` (the data are `Z`).
* `(iv)` is written as the existence of a coupling of cost `≤` semi-dual value `+ r_n` (as in the frozen
  `FixedKOOS.dual`); equivalent to the printed `W₂²`-form because optimal couplings exist (compact grid support,
  finite `P̂_n`). No measurability of `r_n` is assumed (generalisation). Grids converge weakly (equivalent to `W₁` on
  the compact `𝒰_K`). `N = n + 1`, `ε_n log(n+1) → 0`.
* `softCT ε z f u = −ε log(N⁻¹ Σ_i exp((f_i − ‖u − Z_i‖²)/ε))` verbatim (`ε_n > 0`, argument of `log` positive).

Critic notes:
* Proved in `WaveP2a/Route{Soft,Defect,Core,Claims,Implies}.lean` (kernel dependencies: propext, Classical.choice, Quot.sound only).
  Route: `φ_n ≤ φ̂_n ≤ φ_n + ε log N`, so the soft gap `r_n` is a hard gap `r_n + ε_n log(n+1)`; the frozen exact-dual
  argument with the residual kept gives a Borel defect `d_n ≥ 0` with `∫d_n dπ_n ≤ (r_n + ε_n log(n+1))/2` and the
  `d_n`-subgradient inequality, i.e. C's wave-L4 `InexactFit` (grids `μ_{K,m_n}`, targets `P̂_n`, `χ_n`, `g_n = χ̂_n`)
  at every `ω` of a probability-one event (Varadarajan: no moment). Existence of the McCann map, moment-free: the
  plans are tight (Prokhorov), a cluster point couples `(μ_K, P_K)` with cyclically monotone support (wave L4), and
  the approximate-potential library identifies it with the graph of `∇φ`. Then the certified moment-free wave-L8
  `cond_potentials_inexact` (C `prop:conditional-potentials`, inexact fits), moment-free uniqueness
  (`brenierUniq_general`), Rademacher, and the certified frozen `band_containment` (23a), `band_pointwise_lower_core`
  (24e), `band_coverage_asymptotic` (24d).
* No moment at all is used: the printed (ii) `m₁(P_K) < ∞` is dropped (a generalisation; the paper's conjugate /
  Arzelà–Ascoli route needs it for `W₁` and uniform integrability, the plan route does not).
* No tautology: `FixedKOOSInexact` contains no convergence of potentials or maps (only marginals, residuals, the
  smoothing schedule and the per-`n` dual inequality). No junk: `IsGLB` replaces `sInf`; the dual integrals are
  genuine (continuous integrands bounded on the compact `𝒰_K`, finite `P̂_n`); `softCT`'s `log` has a positive
  argument; `HasLaw` guards `Measure.map`; outer probabilities in the coverage claims as in the frozen 24d claim;
  `IsLUB ∅` has no solution in `ℝ` (the paper's `sup ∅ := 0` case is the trivial bound `≥ 0`).
* Nonvacuity: `FixedKOOS` ⇒ `FixedKOOSInexact` (`fixedKOOSInexact_of_fixedKOOS`). Genuinely inexact fits (argument,
  not formalised): the hypothesis is monotone in `r` (any `r'_n ≥ r_n` with `r'_n → 0`), so `r_n > 0` is never
  excluded; and non-optimal duals satisfy it: the hard semi-dual value `∫φ dμ_{K,m_n} + N⁻¹Σf_i` is `2`-Lipschitz in
  `‖f‖_∞` and `φ ≤ φ̂`, so perturbations `f*_n + e_1/(n+1)` of hard-LP-optimal duals satisfy (iv) with
  `r_n = 2/(n+1)`.
* Critic (2026-10-16): ACCEPT-WITH-NOTE, all 7 claims TRUE (kernel-checked: `example : Claims.X := X` for all 7
  and the 4 `*_frozen` implications `Claims.X → Wave23c/Wave24e.Claims.X`; kernel dependencies propext, Classical.choice,
  Quot.sound). Fidelity: `softCT` is the printed `φ̂_n` verbatim (`N = n + 1`); `FixedKOOSInexact` is the printed
  assumption minus (ii), minus the measurability of `r_n` and of the fitted duals (generalisations; the coverage
  claims then use outer probabilities); the coupling form of (iv) is equivalent to the `W₂²` form (optimal couplings
  exist). McCann population map = the paper's `Q_{±,K}` (monotone map, McCann uniqueness in the printed proof); under
  `m₂` it coincides with the frozen Kantorovich-optimal notion on the same `T`s (both directions true; the direction
  needed, Kantorovich ⇒ McCann, is proved). Normalisation: `inf_{int 𝒰} φ = inf χ_K` for the closed extension
  (Rockafellar Thm 7.5), not necessarily attained in `int 𝒰` (hence `IsGLB`, not `IsLeast`); `c_n` is attained.
  Manuscript notes: (1) (ii) `m₁(P_K) < ∞` is not needed for the four results (the Lean route is moment-free);
  (2) the population band cites `Q_{±,K}` of `thm:prob-content`(c), whose hypothesis `P_K ∈ 𝒫^ℓ` includes a finite
  SECOND moment not given by `ass:fixedK-oos`; (c) holds for every `P_K` by McCann (1995), so the citation should say
  so. Fixes: docstrings only (the exact Mathlib `Measure.map` junk value; the certified-band gaps of
  `thm:band-containment` and (i) declared). Conditionality: `band_coverage_asymptotic_discharged`,
  `band_coverage_asymptotic_sup` take the population coverage (`prop:pop-band-coverage`) as a premise.

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace Gradient

namespace StatFormal.WaveP2a

open StatFormal.Wave23c (empLaw lagPot softPot hardCT entMap FixedKOOS)
open StatFormal.Wave23a (popSupp fitSupp)
open StatFormal.OTFD.WaveL1 (IsCMMapAE Euc)
open StatFormal.Wave24d (InSuppBand)
open TauCeti (IsCoupling IsKantorovichOptimalTransportMap)

section FixedK

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The soft `c`-transform of `ass:fixedK-oos`(iv), `φ̂_n(u) = −ε log(N⁻¹ Σ_i exp{(f_i − ‖u − Z_i‖²)/ε})`
(`N = n + 1` data points), which defines `Q̂_n`. -/
def softCT {n : ℕ} (ε : ℝ) (z : Fin (n + 1) → E) (f : Fin (n + 1) → ℝ) (u : E) : ℝ :=
  -ε * Real.log ((∑ i, Real.exp ((f i - ‖u - z i‖ ^ 2) / ε)) / (n + 1))

variable [MeasurableSpace E] [BorelSpace E]

/-- `ass:fixedK-oos` AS PRINTED, except (ii): (i) `μ_K ≪ Leb` with convex compact support `𝒰_K`; (ii) DELETED (the
paper's first moment of `P_K` is not needed); (iii) grids `μ_{K,m_n}` carried by `𝒰_K`, converging weakly to `μ_K`;
data `Z_0, Z_1, …` iid `P_K`, the `n`-th fit using `Z_0, …, Z_n`; (iv) `ε_n > 0`, `ε_n log(n+1) → 0`, residuals
`r_n ≥ 0` with `r_n → 0` almost surely, and almost surely, for every `n`,
`∫ φ̂_n dμ_{K,m_n} + N⁻¹ Σ_i f_i ≥ W₂²(μ_{K,m_n}, P̂_{K,n}) − r_n` with the SOFT transform `φ̂_n = softCT`, written as
the existence of a coupling whose cost `∫ ‖u − z‖² dπ` is at most the semi-dual value plus `r_n`. The frozen
Wave 23c `FixedKOOS` is the case `r_n = 0` with the hard transform and a second moment. -/
structure FixedKOOSInexact (μ P : ProbabilityMeasure E) (μs : ℕ → ProbabilityMeasure E) {Ω : Type*}
    [MeasurableSpace Ω] (Pr : Measure Ω) (Z : ℕ → Ω → E) (ε : ℕ → ℝ) (f : (n : ℕ) → Ω → Fin (n + 1) → ℝ)
    (r : ℕ → Ω → ℝ) : Prop where
  ac : ∀ (ρ : Measure E), ρ.IsAddHaarMeasure → (μ : Measure E) ≪ ρ
  convex : Convex ℝ (μ : Measure E).support
  compact : IsCompact (μ : Measure E).support
  grid_supp : ∀ n, (μs n : Measure E) ((μ : Measure E).support)ᶜ = 0
  grid_lim : Tendsto μs atTop (𝓝 μ)
  indep : iIndepFun Z Pr
  law : ∀ i, HasLaw (Z i) (P : Measure E) Pr
  eps_pos : ∀ n, 0 < ε n
  eps_log : Tendsto (fun n : ℕ => ε n * Real.log (n + 1)) atTop (𝓝 0)
  resid_nonneg : ∀ n ω, 0 ≤ r n ω
  resid_lim : ∀ᵐ ω ∂Pr, Tendsto (fun n => r n ω) atTop (𝓝 0)
  dual : ∀ᵐ ω ∂Pr, ∀ n, ∃ π : Measure (E × E),
    IsCoupling π (μs n : Measure E) (empLaw fun i : Fin (n + 1) => Z i ω) ∧
      ∫ p, ‖p.1 - p.2‖ ^ 2 ∂π ≤
        ∫ u, softCT (ε n) (fun i : Fin (n + 1) => Z i ω) (f n ω) u ∂(μs n : Measure E) +
          (∑ i, f n ω i) / (n + 1) + r n ω

end FixedK

namespace Claims

/-! ### The relaxed assumption contains the frozen one -/

/-- The frozen Wave 23c `FixedKOOS` (second moment, exactly optimal HARD dual) implies `FixedKOOSInexact` with
`r_n = 0`: the relaxation is a generalisation. -/
def fixedKOOSInexact_of_fixedKOOS : Prop :=
  ∀ (K : ℕ) (μ P : ProbabilityMeasure (Euc K)) (μs : ℕ → ProbabilityMeasure (Euc K)) (Ω : Type)
    [MeasurableSpace Ω] (Pr : Measure Ω) (Z : ℕ → Ω → Euc K) (ε : ℕ → ℝ) (f : (n : ℕ) → Ω → Fin (n + 1) → ℝ),
    FixedKOOS μ P μs Pr Z ε f → FixedKOOSInexact μ P μs Pr Z ε f (fun _ _ => 0)

/-! ### B `prop:app-potential-consistency` -/

/-- `prop:app-potential-consistency` under `ass:fixedK-oos` as printed (`FixedKOOSInexact`), with the printed
normalisation: a Brenier map in McCann's sense exists (a Borel map, `μ_K`-a.e. cyclically monotone, pushing `μ_K` to
`P_K`); there is a convex `χ_K` on `int 𝒰_K` with `inf_{int 𝒰_K} χ_K = 0` whose gradient equals every such map
`μ_K`-a.e.; it is the unique such function on `int 𝒰_K`; and almost surely, with `c_n = inf_{𝒰_K} χ_n` (the paper's
`X_n(0) = 0`), `χ_n − c_n → χ_K` and `χ̂_n − c_n → χ_K` uniformly on compact subsets of `int 𝒰_K`. -/
def potential_consistency : Prop :=
  ∀ (K : ℕ) (μ P : ProbabilityMeasure (Euc K)) (μs : ℕ → ProbabilityMeasure (Euc K)) (Ω : Type)
    [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (Z : ℕ → Ω → Euc K) (ε : ℕ → ℝ)
    (f : (n : ℕ) → Ω → Fin (n + 1) → ℝ) (r : ℕ → Ω → ℝ),
    FixedKOOSInexact μ P μs Pr Z ε f r →
      (∃ T : Euc K → Euc K, Measurable T ∧ (μ : Measure (Euc K)).map T = P ∧ IsCMMapAE (μ : Measure (Euc K)) T) ∧
      ∃ φ : Euc K → ℝ, ConvexOn ℝ (interior (μ : Measure (Euc K)).support) φ ∧
        IsGLB (φ '' interior (μ : Measure (Euc K)).support) 0 ∧
        (∀ T : Euc K → Euc K, HasLaw T (P : Measure (Euc K)) (μ : Measure (Euc K)) → IsCMMapAE (μ : Measure (Euc K)) T →
          ∀ᵐ u ∂(μ : Measure (Euc K)), DifferentiableAt ℝ φ u ∧ ∇ φ u = T u) ∧
        (∀ ψ : Euc K → ℝ, ConvexOn ℝ (interior (μ : Measure (Euc K)).support) ψ →
          IsGLB (ψ '' interior (μ : Measure (Euc K)).support) 0 →
          (∀ᵐ u ∂(μ : Measure (Euc K)), DifferentiableAt ℝ ψ u ∧ ∇ ψ u = ∇ φ u) →
            EqOn ψ φ (interior (μ : Measure (Euc K)).support)) ∧
        ∀ᵐ ω ∂Pr, ∃ c : ℕ → ℝ,
          (∀ n, IsGLB ((lagPot (fun i : Fin (n + 1) => Z i ω) (f n ω)) '' (μ : Measure (Euc K)).support) (c n)) ∧
          TendstoLocallyUniformlyOn (fun n u => lagPot (fun i : Fin (n + 1) => Z i ω) (f n ω) u - c n) φ atTop
            (interior (μ : Measure (Euc K)).support) ∧
          TendstoLocallyUniformlyOn (fun n u => softPot (ε n) (fun i : Fin (n + 1) => Z i ω) (f n ω) u - c n) φ
            atTop (interior (μ : Measure (Euc K)).support)

/-- The map form (`prop:app-potential-consistency` with `lem:app-subgradient-convergence`(a)) under the printed
assumption: for every Brenier map `T` (McCann), almost surely `Q̂_n(u) → T(u)` for `μ_K`-a.e. `u`. -/
def potential_consistency_maps : Prop :=
  ∀ (K : ℕ) (μ P : ProbabilityMeasure (Euc K)) (μs : ℕ → ProbabilityMeasure (Euc K)) (Ω : Type)
    [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (Z : ℕ → Ω → Euc K) (ε : ℕ → ℝ)
    (f : (n : ℕ) → Ω → Fin (n + 1) → ℝ) (r : ℕ → Ω → ℝ) (T : Euc K → Euc K),
    FixedKOOSInexact μ P μs Pr Z ε f r →
    HasLaw T (P : Measure (Euc K)) (μ : Measure (Euc K)) → IsCMMapAE (μ : Measure (Euc K)) T →
      ∀ᵐ ω ∂Pr, ∀ᵐ u ∂(μ : Measure (Euc K)),
        Tendsto (fun n => entMap (ε n) (fun i : Fin (n + 1) => Z i ω) (f n ω) u) atTop (𝓝 (T u))

/-! ### B `thm:band-containment` -/

/-- `thm:band-containment` under the printed assumption: the frozen Wave 23c `band_containment_discharged` with
`FixedKOOS` ↦ `FixedKOOSInexact` and the Kantorovich-optimal `T` ↦ a McCann Brenier map: almost surely, for every
`η > 0`, eventually `x↑pop ≤ x̂↑_n + η` and `x̂↓_n ≤ x↓pop + η`, uniformly in `t`. -/
def band_containment_discharged : Prop :=
  ∀ (K : ℕ) (μ P : ProbabilityMeasure (Euc K)) (μs : ℕ → ProbabilityMeasure (Euc K)) (Ω : Type)
    [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (Z : ℕ → Ω → Euc K) (ε : ℕ → ℝ)
    (f : (n : ℕ) → Ω → Fin (n + 1) → ℝ) (r : ℕ → Ω → ℝ) (T : Euc K → Euc K)
    (𝒯 : Type) (A : Set (Euc K)) (mfrak : 𝒯 → ℝ) (e : 𝒯 → Euc K),
    FixedKOOSInexact μ P μs Pr Z ε f r →
    HasLaw T (P : Measure (Euc K)) (μ : Measure (Euc K)) → IsCMMapAE (μ : Measure (Euc K)) T →
    MeasurableSet A → (∃ R : ℝ, ∀ᵐ u ∂(μ : Measure (Euc K)).restrict A, ‖T u‖ ≤ R) → (∃ C : ℝ, ∀ t, ‖e t‖ ≤ C) →
      ∀ᵐ ω ∂Pr, ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t,
        (mfrak t : EReal) + popSupp (μ : Measure (Euc K)) A T (e t) ≤
            (mfrak t : EReal) + fitSupp A (entMap (ε n) (fun i : Fin (n + 1) => Z i ω) (f n ω)) (e t) +
              (η : EReal) ∧
          (mfrak t : EReal) - fitSupp A (entMap (ε n) (fun i : Fin (n + 1) => Z i ω) (f n ω)) (-e t) ≤
            (mfrak t : EReal) - popSupp (μ : Measure (Euc K)) A T (-e t) + (η : EReal)

/-! ### B `lem:band-pointwise-lower` -/

/-- `lem:band-pointwise-lower` under the printed assumption (the frozen Wave 24e `band_pointwise_lower` with
`FixedKOOS` ↦ `FixedKOOSInexact`, `T` a McCann Brenier map): almost surely, simultaneously for every measurable region
`A` and every `v`, `liminf_n ĥ_n(v) ≥ h^pop(v)`. -/
def band_pointwise_lower : Prop :=
  ∀ (K : ℕ) (μ P : ProbabilityMeasure (Euc K)) (μs : ℕ → ProbabilityMeasure (Euc K)) (Ω : Type)
    [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (Z : ℕ → Ω → Euc K) (ε : ℕ → ℝ)
    (f : (n : ℕ) → Ω → Fin (n + 1) → ℝ) (r : ℕ → Ω → ℝ) (T : Euc K → Euc K),
    FixedKOOSInexact μ P μs Pr Z ε f r →
    HasLaw T (P : Measure (Euc K)) (μ : Measure (Euc K)) → IsCMMapAE (μ : Measure (Euc K)) T →
      ∀ᵐ ω ∂Pr, ∀ A : Set (Euc K), MeasurableSet A → ∀ v : Euc K,
        popSupp (μ : Measure (Euc K)) A T v ≤
          liminf (fun n => fitSupp A (entMap (ε n) (fun i : Fin (n + 1) => Z i ω) (f n ω)) v) atTop

/-! ### B `cor:band-coverage-asymptotic` -/

/-- `cor:band-coverage-asymptotic`(i) with (iii) under the printed assumption: the frozen Wave 24d
`band_coverage_asymptotic` with its a.e.-convergence premise DISCHARGED (`Q := T` a McCann Brenier map,
`Q̂_n := entMap` of the fit, `FixedKOOSInexact`); the test coefficient vector `Y` lives on the same probability space
as the sample, with no independence. Outer probabilities as in the frozen claim. -/
def band_coverage_asymptotic_discharged : Prop :=
  ∀ (K : ℕ) (μ P : ProbabilityMeasure (Euc K)) (μs : ℕ → ProbabilityMeasure (Euc K)) (𝒯 Ω : Type)
    [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (Z : ℕ → Ω → Euc K) (ε : ℕ → ℝ)
    (f : (n : ℕ) → Ω → Fin (n + 1) → ℝ) (r : ℕ → Ω → ℝ) (T : Euc K → Euc K) (A A' : Set (Euc K))
    (Y : Ω → Euc K) (mfrak : 𝒯 → ℝ) (e : 𝒯 → Euc K) (p' ς : ℝ),
    FixedKOOSInexact μ P μs Pr Z ε f r →
    HasLaw T (P : Measure (Euc K)) (μ : Measure (Euc K)) → IsCMMapAE (μ : Measure (Euc K)) T →
    MeasurableSet A → A.Nonempty → (∃ R : ℝ, ∀ᵐ u ∂(μ : Measure (Euc K)).restrict A, ‖T u‖ ≤ R) →
    0 < ς → (∀ t, e t ≠ 0 → ∀ σ ∈ ({1, -1} : Set ℝ),
      popSupp (μ : Measure (Euc K)) A' T (σ • e t) + ((ς * ‖e t‖ : ℝ) : EReal) ≤
        popSupp (μ : Measure (Euc K)) A T (σ • e t)) →
    ENNReal.ofReal p' ≤ Pr {ω | InSuppBand (popSupp (μ : Measure (Euc K)) A' T) mfrak e (Y ω)} →
      ENNReal.ofReal p' ≤
        liminf (fun n => Pr {ω | InSuppBand (fitSupp A (entMap (ε n) (fun i : Fin (n + 1) => Z i ω) (f n ω)))
          mfrak e (Y ω)}) atTop

/-- `cor:band-coverage-asymptotic`(ii) under the printed assumption: with population regions `A'(p')` (levels
`p' ∈ (0, p)`) each covering `Y` with probability `≥ p'` (`prop:pop-band-coverage`, premise), the computed band at
level `p` has `liminf_n P(Y ∈ B̂_K(p)) ≥ p^♮`, where `p^♮` is the supremum (`IsLUB`) of the levels `p' ∈ (0, p)` with
a positive normalised nesting margin `ς(p') > 0` (written: some `ς > 0` with
`h^pop_{p'}(σe(t)) + ς‖e(t)‖ ≤ h^pop_p(σe(t))` for `σ = ±1` and every `t` with `e(t) ≠ 0`). The paper's
`sup ∅ := 0` case is trivial (`liminf ≥ 0`) and excluded by `IsLUB` (no least upper bound of `∅` in `ℝ`). -/
def band_coverage_asymptotic_sup : Prop :=
  ∀ (K : ℕ) (μ P : ProbabilityMeasure (Euc K)) (μs : ℕ → ProbabilityMeasure (Euc K)) (𝒯 Ω : Type)
    [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (Z : ℕ → Ω → Euc K) (ε : ℕ → ℝ)
    (f : (n : ℕ) → Ω → Fin (n + 1) → ℝ) (r : ℕ → Ω → ℝ) (T : Euc K → Euc K) (A : Set (Euc K))
    (A' : ℝ → Set (Euc K)) (Y : Ω → Euc K) (mfrak : 𝒯 → ℝ) (e : 𝒯 → Euc K) (p pnat : ℝ),
    FixedKOOSInexact μ P μs Pr Z ε f r →
    HasLaw T (P : Measure (Euc K)) (μ : Measure (Euc K)) → IsCMMapAE (μ : Measure (Euc K)) T →
    MeasurableSet A → A.Nonempty → (∃ R : ℝ, ∀ᵐ u ∂(μ : Measure (Euc K)).restrict A, ‖T u‖ ≤ R) →
    (∀ p' ∈ Ioo 0 p,
      ENNReal.ofReal p' ≤ Pr {ω | InSuppBand (popSupp (μ : Measure (Euc K)) (A' p') T) mfrak e (Y ω)}) →
    IsLUB {p' ∈ Ioo 0 p | ∃ ς : ℝ, 0 < ς ∧ ∀ t, e t ≠ 0 → ∀ σ ∈ ({1, -1} : Set ℝ),
      popSupp (μ : Measure (Euc K)) (A' p') T (σ • e t) + ((ς * ‖e t‖ : ℝ) : EReal) ≤
        popSupp (μ : Measure (Euc K)) A T (σ • e t)} pnat →
      ENNReal.ofReal pnat ≤
        liminf (fun n => Pr {ω | InSuppBand (fitSupp A (entMap (ε n) (fun i : Fin (n + 1) => Z i ω) (f n ω)))
          mfrak e (Y ω)}) atTop

end Claims

end StatFormal.WaveP2a
