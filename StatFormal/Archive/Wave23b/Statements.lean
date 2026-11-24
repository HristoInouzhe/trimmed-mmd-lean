import StatFormal.Archive.OTFD.Wave5b.Statements
import StatFormal.Archive.OTFD.Wave8c.Statements
import StatFormal.Archive.OTFD.WaveL1.Statements
import StatFormal.Archive.OTFD.WaveL3.Statements
import StatFormal.Archive.OTFD.Wave6b.Statements
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.MetricSpace.Holder

/-!
# FROZEN STATEMENTS — wave 23b (QUEUE rows 273–281, 288–290): C `lem:self-potentials`; G `prop:cap`,
# `prop:quantile`, `cor:discretisation`; T `prop:parallel` (`eq:H1eval`), `thm:population`, `prop:linearmodel`
# (`eq:explicitbridge`), `prop:transfer-M`, `prop:chart`; A `prop:selector`, `cor:convergent-references`;
# R `thm:nullmass`

Sources (verbatim in `lean-formalisation/inventory/extracted/otfd-{C_conditional,G_geodesic,T_tangent,A_sieves,
R_robustness}.md`; current text of 2026-10-15, paths under `otfd/papers/`):
* C `lem:self-potentials` (`C_conditional/supplement.tex:559-574`, set-up `:533-556`, proof `:576-640`).
* G `prop:cap` (`G_geodesic/main.tex:407-447`), `prop:quantile` (`main.tex:550-565`, with `def:ranks` `:518-531` and
  the canonical potentials of `thm:wellposed`(b) `:479-492`), `cor:discretisation` (`supp_moved.tex:202-235`, proof
  `:237-280`), with the frozen `lem:stability` (`OTFD/Wave5b`: `GibbsHyp`, `gibbsPlan`, `gibbsMean`, certified
  `stab_tv_osc`, `stab_tv_integrable`, `stab_mean`, `stab_rank`).
* T `prop:parallel` (`T_tangent/sec_tangent_theory.tex:20-33`, proof `:34-56`), `thm:population` (`:137-158`, with
  `ass:model` `:89-96`, `eq:chart` `:76-80`), `prop:linearmodel` (`supp_moved.tex:183-200`, model `:160-181`, proof
  `app_proofs.tex:373-393`), `prop:transfer-M` (`supp_toolkit.tex:181-198`, `def:transfer-M` `:142-150`), `prop:chart`
  (`supp_toolkit.tex:242-282`, proof `:284-358`).
* A `prop:selector` (`A_sieves/main.tex:1251-1263`, criterion `:1240-1249`), with the frozen `OTFD/Wave1.edStat`;
  A `cor:convergent-references` (`A_sieves/supplement.tex:5179-5218`), with the frozen WaveL1 plan stability.
* R `thm:nullmass` (`R_robustness/sections/s3_infinite.tex:18-29`, proof `appendix_a.tex:161-176`), `cor:uncertainty`
  (`:41-49`); class (a) is frozen in Wave 21b (`nullmass_a`).
Imports the frozen `OTFD/Wave5b` (Gibbs plans), `OTFD/Wave8c` (`IsRankPair`, `IsGradMap`, `quadCost`), `OTFD/WaveL3`
(`Mom1`), `OTFD/Wave6b` (`sphDist`, `sphExp`) and `OTFD/WaveL1`
(through it `OTFD/Wave1`: `edStat`, `truncK`, `IsLipHyp`; `OTFD/Wave8b`: `embed`, `proj`, `embLaw`; `Wave21b`:
`depthH`, `depthRegion`; `LipNull`, `BrenierUniq`, `IsCMMapAE`) statements, not copied; Tau Ceti (`IsOptimalCoupling`,
`graphPlan`) and Mathlib otherwise. No `Foundations` file is imported by the statements.

Covered:
* C `lem:self-potentials`: `selfpot_ent_unique` (continuous entropic solutions on `D` are unique, for any `P` carried
  by the compact `D`: empirical and population at once), `selfpot_ent_exists` (finitely supported `P`: a continuous
  solution at every point, i.e. on `D` with its out-of-sample extension), `selfpot_ent_bounds` (`−d²/2 ≤ F ≤ d²`,
  `2d`-Lipschitz on `D`), `selfpot_quad_bounds` (`η/2 − d² ≤ H ≤ η/2 + 3d²/2`, `2d`-Lipschitz), `selfpot_quad_unique`
  (empirical: two solution vectors coincide), `selfpot_quad_unique_ext` (empirical uniqueness on `D`, extension
  included), `selfpot_quad_exists` (empirical existence of a continuous solution at every point).
* G `prop:cap` on a grid: (a) `cap_sup` (`b_K = sup{max_j |v(t_j)| : v ∈ S, ‖v‖ ≤ 1}`, attained), `cap_basis`
  (`max_j |v(t_j)| ≤ b_K‖v‖`; basis independence), `cap_lower` (`b_K² ≥ K/min(K,q) ≥ 1`); (e) `cap_full` (full rank:
  `b = (min_j w_j)^{−1/2}`), `cap_trapezoid` (`= √(2(J−1))`, weights sum to one); (f) `cap_pilot_exact` (exceedance
  probability exactly `1/(r₀+1)`), `cap_pilot_support` (a.s. `μ(esssup|v| > b̂) > 0`), `cap_pilot_atomless`
  (`τW` atomless).
* G `prop:quantile`, flat (`E_m(sv) = m + sv`): `quantile_mean`, `quantile_flat` (existence, uniqueness, `Q_ε(v)` the
  conditional mean, continuity in `v`).
* G `cor:discretisation`: (a) `disc_cost`, `disc_rank_uniform`, `disc_rank_integrable`; (b) `disc_trunc_cost`,
  `disc_trunc_rank`.
* T `prop:parallel`: `h1_eval`, `h1_sharp` (attained at both endpoints), `h1_const` (`Λ₁ = 1.145877…`).
* T `thm:population`: `pop_hilbert` (`eq:Hilbertinverse` with subgradient potentials and uniqueness of both optimal
  plans), `pop_manifold` (`eq:manifoldinverse`), `pop_regions` (full-measure Borel sets of mutual inversion; the
  rank-defined region of any Borel `A` has `P`-mass `μ(A)` and is the `Q^m`-image of `Ω_μ ∩ A`).
* T `prop:linearmodel`, finite rank: `lm_tangent` (`Q₀ = A`, its plan the unique optimum), `lm_exists`, `lm_bridge`
  (`eq:explicitbridge`, sandwich as hypothesis), `lm_bridge_sphere` (`eq:explicitbridge` on the unit sphere with the
  concrete `c_g = ½D₂(E_m u, E_m v)²`, unconditional), `lm_order` (`1 − (sin r/r)² ≤ r²/3`, so the bound is `O(h⁴)`).
* T `prop:transfer-M` (i)–(iii): `transferM_push`, `transferM_unique` (via the certified `lem:depthsign-rank`),
  `transferM_cocycle`.
* T `prop:chart`: (ii) `chart_flat` (both identities and both "iff"s), (iii) on `ℝ^d` `chart_translation`.
* A `prop:selector`(i): `selector_dev` (the event with probability `≥ 1 − γ`, `Δ` with the exact constants, and the
  oracle inequality, also for `s`-approximate minimisers).
* A `cor:convergent-references`: `convref_a`, `convref_b` (identification CONDITIONAL on `BrenierUniq`, as WaveL1),
  `convref_a_uncond`, `convref_b_uncond` (`BrenierUniq` discharged by the certified WaveL3 `brenier_uniq_H_bdd`, with
  `m₁(P) < ∞`), `convref_spherical` (no weak limit), `convref_coherent` (example (i)).
* R `thm:nullmass`(b): `nullmass_b` (elliptical laws, eigenbasis form); (c): `nullmass_c` (generalised),
  `nullmass_c_gauss` (as printed, eigenbasis form); `cor:uncertainty` for (b), (c): `uncertainty_b`, `uncertainty_c`.

Not covered (declared):
* C: the a.s. uniform convergence `F_{n,ε} → F_ε`, `H_{n,η} → H_η` (needs uniform weak convergence) and the limits
  `‖F_ε‖_∞ → 0`, `‖H_η‖_∞ → 0` (uniform Laplace principle); population existence (it is the limit argument); population
  quadratic uniqueness (needs `supp P = D`).
* G `prop:cap`: (b) Gaussian support, (c) injectivity radius, cut locus, minimising geodesics (and "no larger `s`"),
  (d) design-split measurability (interpretive), the continuum halves of (a) (ess sup) and (e) (infinite rank);
  `prop:quantile`(a) pointwise characterisation and (b) on curved `M` (Afsari convexity, the single null set `N`);
  `cor:discretisation`: measurability of `c^Δ` and of `ℓ` (hypotheses here), the trapezoid remark, the lifting of the
  truncated plan to `(G, τ)` (encoded directly), `E_m` 1-Lipschitz on `S²`, Rauch/`cosh` factors and all of (c).
* T: parallel frames and covariant derivatives, separability, the `H¹` density step (`C¹` here); GHS Thm 2.3 beyond
  `𝒫^ℓ`, the chart `E_m` itself (abstract Borel bijection here); the infinite-rank cubic model (finite `K` here), the
  existence of a `c_g`-optimal coupling for the concrete sphere cost (`lm_exists` is the generic l.s.c. statement; the
  continuity of `cgSph` is not proved), and, in `lm_bridge` only, `prop:distortion` (hypothesis there; discharged in
  `lm_bridge_sphere`); `prop:transfer-M`(iv) (B Prop S13.4, `lem:exp`) and the existence
  of the McCann maps (rank pairs are hypotheses); `prop:chart`(i), (iii) on curved `M` and with a general centering `v̄`, (iv), the
  entropic version of (ii) and its "without a sieve, the Hilbert transfer" clause.
* A: `prop:selector`(ii) (needs `lem:T-stability`); `cor:convergent-references` examples (ii)–(iv) (Gaussian `ζ` on
  `H`, perturbed boxes) and, in `convref_a`, `convref_b`, the `BrenierUniq` input (discharged in the `_uncond` versions at the price
  of `m₁(P) < ∞`; the existence of `𝔽^μ_P` is not asserted: it is quantified over).
* R: nothing (class (a) is frozen in Wave 21b; the proof of (b) here avoids the Cameron–Martin space).

Encodings (to be checked by the critic):
* C: `P` any Borel probability carried by a compact `D` with `‖x − y‖ ≤ d` on `D` (`d ≥ diam D`: generalisation);
  `eq:ent-self-pop`, `eq:quad-self-pop` as `EntSelfEq`, `QuadSelfEq` at each `x ∈ D` (Bochner integrals: the solutions
  are continuous on `D`, so the integrands are bounded measurable `P`-a.e. — no junk); empirical laws
  `Σ_i p_i δ_{C_i}` (`empW`, `p_i > 0`, generalising `1/n`); the quadratic empirical system on the sample points.
* G `prop:cap`: fields on `J ≥ 1` nodes with weights `w_j > 0` (nodes of positive weight; `Σ w_j = 1` where `λ(T) = 1`
  is used), inner product `Σ_j w_j ⟨u_j, v_j⟩` (`gridInner`), `max_j` as `⨆ j` over `Fin J` (`gridSup`), orthonormal
  `φ_1..φ_K`, `Φ_K(t_j)` as a continuous linear map `ℝ^K → ℝ^q` (`PhiMat`), `b_K = max_j ‖Φ_K(t_j)‖_op` (`bK`);
  full rank as `span = ⊤`; pilot draws and the new draw i.i.d. atomless reals (coordinate `0` is the new draw);
  `esssup_t|V(t)| = τW` with `τ ~ Unif(0,1]` independent of `W`, `P(W = 0) = 0`.
* G flat: `X = H_m = H` a real Hilbert space, `D` its norm distance, `c_s(v,x) = ½‖m + sv − x‖²`, `g` any bounded
  measurable potential, `f = f^c` the canonical extension (`flatPot`), `π_ε(dx|v)` by its density (`flatCond`).
* G (a): `T = [0,1]`, `λ` a probability on `ℝ` carried by `T`; a Riemann rule is a finite family of disjoint measurable
  cells in `T` covering it `λ`-a.e. with nodes `t_I ∈ T` within `Δ` of their cell (intervals of length `≤ Δ` with
  `t_I ∈ cl I` are a special case); curves `ℝ → M` with `HolderOnWith` on `T`, constants `ℓ` as `ℝ≥0`
  (`(ℓ v).toNNReal`), `Δ^α` real power; `diam M ≤ Dm` (compactness only through this bound); the reference curve map
  `Y : H → (ℝ → M)` (`E_m(s·)`) and data curves `X : 𝒳 → (ℝ → M)`. (b): the curve space a metric space `(𝒳, D)` with
  base `m`, `E_m(s·)` continuous with `D(E_m(sv), m) ≤ s` for `‖v‖ ≤ 1`, `‖V‖, ‖V_K‖ ≤ 1` and `D(m, x) ≤ B` everywhere
  (`ass:bounded` read pointwise: the frozen stability lemma needs bounded costs), the lifted plans on the reference
  space `(ϖ, ϱ)` (`F^{(K)} = gibbsMean … V_K`, `F = gibbsMean … V`).
* T `eq:H1eval`: `f ∈ C¹([0,1]; E)` as `ContinuousOn f, f'` on `[0,1]` with `HasDerivAt f (f' s) s` on `(0,1)`, any
  real inner-product space `E` (parallel-frame coordinates); `‖v‖_{H₁}² = ∫₀¹ ‖f‖² + ‖f'‖²`; `Λ₁ = √(cosh 1/sinh 1)`.
* T population: `H` separable Hilbert, `𝒫^ℓ` as the frozen `LipNull` (with bounded supports instead of second moments:
  `ass:model`); "a.e. gradient of a convex potential" as `IsGradMap` (subgradient selection of a function into `EReal`);
  the chart: `E_m : H → 𝒳`, `L_m : 𝒳 → H` Borel, `L_m E_m = Id` on a Borel `𝒟_r`, `X ∈ E_m(𝒟_r)` a.s.; `𝒳` second
  countable `T₂` Borel (Polish curve space) for the inversion sets.
* T linear model: `ℝ^K` (`EuclideanSpace ℝ (Fin K)`), `A = diag(t_k)` with `0 < t₋ ≤ t_k ≤ t₊`, `μ_h` any law carried by
  the box `∏[−h a_k/2, h a_k/2]` (the cubic law is one), `ν_h = A#μ_h`, costs `ℝ≥0∞`-valued (`c₀ = ½‖u − v‖²`, `c_g` any
  measurable), Tau Ceti `IsOptimalCoupling`; `a = sin r_h/r_h` enters through the hypothesis `a² c₀ ≤ c_g ≤ c₀` on
  `S × A(S)` (`prop:distortion`), any `a ∈ (0,1]`. Sphere (`lm_bridge_sphere`): `S^d ⊂ ℝ^{d+1}`, the base curve
  `m : T → S^d` measurable, tangent fields `e_k : T → ℝ^{d+1}` in ambient coordinates (a parallel frame is not needed),
  orthonormal in `L²(λ)` for a finite `λ`, `‖e_k(s)‖ ≤ en k` everywhere (`en k = ‖e_k‖_∞` recovers `B_∞`), `0 < r_h`.
* T transfers: coefficient space `ℝ^K`, the fixed charts as Borel `Φ_g : ℝ^K → 𝒳` with Borel `Ψ_g` (`Φ_g Ψ_g = Id`
  `P^K_g`-a.e.), coefficient laws `P_g.map Ψ_g`, McCann rank pairs as the frozen `IsRankPair`; depth `1 − c_K(‖F‖)` with
  `c_K` the cdf of `‖U‖` (`cK`) and sign `u/‖u‖` (`sgnK`, `0` at the origin).
* T charts (flat): `H` the curve Hilbert space, `Π_K`, `ι_K` the frozen `proj`, `embed` for a common basis `e`
  (orthonormality not needed in (ii); needed in (iii) for `Π_Kι_K = Id`), `P^K_A`-a.e. read as `P_A`-a.e. at
  `y = m_A + ι_KΠ_K(x − m_A)` (implies the a.e. statement for the law `P^K_A`), constant frames, `v̄ = 0`; any base curves `m₀, m_A, m_B` in (ii) (generalisation;
  the paper uses the mean curves), the mean curves `∫ x dP` in (iii); `μ_K ≪ Leb`, second moments; shared-chart maps
  any McCann rank pairs of the translated coefficient laws.
* A selector: given the training fold, `Φ_θ = Υ F̂_θ : X → E` (any measurable maps, `‖Φ_θ‖ ≤ R = R_Υ`), `Ψ = Υ`,
  `E` second-countable normed (`ℝ^K`), finite nonempty `Θ`; validation and reference samples i.i.d. on the product
  `P^{n_v} ⊗ μ^{m_v}`; `D(θ)` the energy distance of `Φ_θ#P` and `Ψ#μ` (`edPop`); `D̂` the frozen `edStat`.
* A convergent references: `H` separable Hilbert, `Π_K = truncK`, `ι_K = embed` (frozen) for an orthonormal `e`
  (a Hilbert basis in (i)); `F_K` a `P_K`-a.e. cyclically monotone Borel map pushing `P_K` to `ν_K` (frozen `IsCMMapAE`);
  weak convergence in `ProbabilityMeasure H` (norm topology), resp. against `H →ᵇ ℝ`; the spherical references are the
  frozen `embLaw e (L K)` with `c‖v‖² ≤ ‖L_K v‖² ≤ C‖v‖²`.
* R: `TD_H`, `D_α` the frozen `depthH`, `depthRegion`; class (c) as `μ ≪ γ` with `γ`'s coordinates along an
  orthonormal sequence independent `N(m_k, λ_k)`, `λ_k > 0` (`nullmass_c_gauss`; the eigenbasis of an injective
  covariance), and, generalised, independent atomless (`nullmass_c`); class (b) as the law of `√W • G` on a probability
  space, `W > 0` a.s. independent of `G`, `G`'s coordinates along an orthonormal sequence independent `N(0, λ_k)`,
  `λ_k > 0` (the eigenbasis of the injective covariance; completeness of the basis is not used), `H` separable (so the
  pushforward is of a measurable map: no `Measure.map` junk).

Critic notes:
* All 50 claims are proved in `Wave23b/Route{SelfPot,QuadExists,Cap,Pilot,Quantile,Disc,Trunc,H1,Pop,Transfer,Linear,
  Chart,Selector,ConvRef,Null,Elliptic}.lean` (axioms: propext, Classical.choice, Quot.sound). Routes reuse the
  certified `stab_*` (Wave 5b),
  `depthsign_rank` (Wave 4), `plan_stab_b_map` (WaveL1), `naive_weak_tendsto`, `naive_norm_no_weak` (Wave 8b), the
  WaveL3 `brenier_uniq_H_bdd`, Wave 7b `distortion_cost`, the
  Foundations `exists_unique_optimal_graphPlan_of_lipNull` (Brenier–Gigli in `H`), `measure_cntLt_eq` (exchangeable
  ranks), and Tau Ceti's Sinkhorn–Knopp, Brenier uniqueness, Knott–Smith optimality and McDiarmid.
* CONDITIONAL claims: `convref_a`, `convref_b` (on `BrenierUniq`, the WaveL1 convention; unconditional twins
  `convref_*_uncond`); `lm_bridge` (on the distortion sandwich; unconditional twin `lm_bridge_sphere`); `transferM_*`, `chart_*`, `pop_manifold` (on given rank pairs / charts). `disc_rank_*` take the
  measurability of the costs as hypotheses.
* Observations (no statement found false): (C) the quadratic oscillation is `M − m ≤ d²` (the proof's `2d²` is loose),
  giving the sharper `η/2 − d²/2 ≤ H ≤ η/2 + d²`; (R) class (c) needs no Gaussian structure, only a dominating law with
  independent atomless coordinates (it contains class (a)); (T) `prop:chart`(ii) holds for any base curves; (G) the cost
  bound of `cor:discretisation`(a) uses only `diam M`.
* Critic (2026-10-15): ACCEPT after fixes, all 50 TRUE (Lean-proved). Fixes: `chart_translation`'s first conjunct
  was the trivial restriction of the second to rank-`K` curves of `P_A` (possibly a null set) instead of `P^K_A`-a.e.;
  restated at `y = m_A + ι_KΠ_K(x − m_A)` (needs `Orthonormal e`, added). `chart_flat` lacked the printed
  detail-preserving "iff" (added). Added `convref_a_uncond`, `convref_b_uncond`, `lm_bridge_sphere`. The four drafter
  observations are confirmed strengthenings (no printed statement false): the hinge threshold moves by at most the
  cost change `≤ d²`, so `M − m ≤ d²`; `nullmass_c` (proved) contains class (a); (ii) of `prop:chart` never uses the
  centering; the cost bound uses `a + b ≤ 2 diam M` only. Hypotheses stronger than printed: `disc_rank_*` ask the
  Hölder bounds for every reference and data curve (printed: `μ`-, `P`-a.s., Hölder representatives) and
  `disc_trunc_rank` asks `D(m, x) ≤ B` and `‖V‖, ‖V_K‖ ≤ 1` everywhere; `*_uncond` add `m₁(P) < ∞`; `quantile_flat`
  reads `ass:bounded` as `‖x‖ ≤ B` (equivalent: `B` is arbitrary). Restrictions: grid-only (`prop:cap` (a), (e)), flat
  (`prop:quantile`, `prop:chart`), finite rank (`prop:linearmodel`), `C¹` (`eq:H1eval`), empirical-only quadratic
  uniqueness and existence (C). Junk: none reachable (Bochner integrands bounded on the hypotheses, which force
  integrability where an equation `= 1`, `= η > 0` is assumed; `⨆`/`⨅` over nonempty `Fin`; `cK` only compared).

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace BoundedContinuousFunction

namespace StatFormal.Wave23b

open StatFormal.OTFD.Wave1 (edStat truncK IsLipHyp)
open StatFormal.OTFD.Wave5b (GibbsHyp gibbsPlan gibbsMean)
open StatFormal.OTFD.Wave8c (IsRankPair IsGradMap)
open StatFormal.OTFD.Wave8b (embed proj embLaw)
open StatFormal.OTFD.WaveL1 (LipNull BrenierUniq IsCMMapAE)
open StatFormal.Wave21b (depthRegion depthH)

/-! ### C `lem:self-potentials` -/

section SelfPot
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

/-- `eq:ent-self-pop` at `x`: `e^{F(x)/ε} ∫ e^{−‖x−c‖²/ε} e^{F(c)/ε} dP(c) = 1`. -/
def EntSelfEq (P : Measure E) (ε : ℝ) (F : E → ℝ) (x : E) : Prop :=
  Real.exp (F x / ε) * ∫ c, Real.exp (-‖x - c‖ ^ 2 / ε) * Real.exp (F c / ε) ∂P = 1

/-- `eq:quad-self-pop` at `x`: `∫ [H(x) + H(c) − ‖x−c‖²]_+ dP(c) = η`. -/
def QuadSelfEq (P : Measure E) (η : ℝ) (H : E → ℝ) (x : E) : Prop :=
  ∫ c, max (H x + H c - ‖x - c‖ ^ 2) 0 ∂P = η

/-- The weighted empirical law `Σ_i p_i δ_{C_i}`. -/
def empW {n : ℕ} (p : Fin n → ℝ) (C : Fin n → E) : Measure E :=
  ∑ i, ENNReal.ofReal (p i) • Measure.dirac (C i)

end SelfPot

/-! ### G `prop:cap` (grid) -/

section Cap
variable {J q K : ℕ}

/-- The quadrature inner product `⟨u, v⟩ = Σ_j w_j ⟨u(t_j), v(t_j)⟩` of fields on the grid. -/
def gridInner (w : Fin J → ℝ) (u v : Fin J → EuclideanSpace ℝ (Fin q)) : ℝ :=
  ∑ j, w j * ⟪u j, v j⟫

/-- `‖v‖ = ⟨v, v⟩^{1/2}`. -/
def gridNorm (w : Fin J → ℝ) (v : Fin J → EuclideanSpace ℝ (Fin q)) : ℝ :=
  Real.sqrt (gridInner w v v)

/-- `max_j |v(t_j)|`. -/
def gridSup (v : Fin J → EuclideanSpace ℝ (Fin q)) : ℝ := ⨆ j, ‖v j‖

/-- `φ_1, …, φ_K` are orthonormal for the quadrature inner product. -/
def GridOrthonormal (w : Fin J → ℝ) (φ : Fin K → Fin J → EuclideanSpace ℝ (Fin q)) : Prop :=
  ∀ k l, gridInner w (φ k) (φ l) = if k = l then 1 else 0

/-- `Φ_K(t_j) = [φ_1(t_j), …, φ_K(t_j)] : ℝ^K → ℝ^q`. -/
def PhiMat (φ : Fin K → Fin J → EuclideanSpace ℝ (Fin q)) (j : Fin J) :
    EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin q) :=
  ∑ k, (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin K) →L[ℝ] ℝ).smulRight (φ k j)

/-- `b_K = max_j ‖Φ_K(t_j)‖_op`. -/
def bK (φ : Fin K → Fin J → EuclideanSpace ℝ (Fin q)) : ℝ := ⨆ j, ‖PhiMat φ j‖

/-- Trapezoid weights on `J ≥ 2` equispaced nodes of `[0,1]`: `1/(2(J−1))` at the end nodes, `1/(J−1)` inside. -/
def trapW (J : ℕ) (j : Fin J) : ℝ :=
  if (j : ℕ) = 0 ∨ (j : ℕ) = J - 1 then 1 / (2 * ((J : ℝ) - 1)) else 1 / ((J : ℝ) - 1)

end Cap

/-! ### G `prop:quantile` (flat) -/

section Quantile
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]

/-- The flat cost `c_s(v, x) = ½ ‖m + s v − x‖²` (`E_m(sv) = m + sv`). -/
def flatCost (m : H) (s : ℝ) (v x : H) : ℝ := ‖m + s • v - x‖ ^ 2 / 2

/-- The canonical first potential `f(v) = −ε log ∫ e^{(g(x) − c_s(v,x))/ε} dP(x)` (`eq:schrodinger`). -/
def flatPot (P : Measure H) (ε s : ℝ) (m : H) (g : H → ℝ) (v : H) : ℝ :=
  -ε * Real.log (∫ x, Real.exp ((g x - flatCost m s v x) / ε) ∂P)

/-- `π_ε(dx | v) = e^{(f(v) + g(x) − c_s(v,x))/ε} P(dx)`. -/
def flatCond (P : Measure H) (ε s : ℝ) (m : H) (g : H → ℝ) (v : H) : Measure H :=
  P.withDensity fun x => ENNReal.ofReal (Real.exp ((flatPot P ε s m g v + g x - flatCost m s v x) / ε))

end Quantile

/-! ### G `cor:discretisation` -/

section Disc
variable {M : Type*} [PseudoMetricSpace M]

/-- `c = ½ ∫ d_M(y(t), x(t))² dλ(t)`. -/
def curveCost (lam : Measure ℝ) (y x : ℝ → M) : ℝ := (∫ t, dist (y t) (x t) ^ 2 ∂lam) / 2

/-- The Riemann-sum cost `½ Σ_I λ(I) d_M(y(t_I), x(t_I))²`. -/
def riemannCost {N : ℕ} (lam : Measure ℝ) (I : Fin N → Set ℝ) (tn : Fin N → ℝ) (y x : ℝ → M) : ℝ :=
  (∑ k, lam.real (I k) * dist (y (tn k)) (x (tn k)) ^ 2) / 2

/-- A Riemann-sum rule of mesh `Δ` for `λ` on `T = [0,1]`: disjoint measurable cells in `T` covering it up to a
`λ`-null set, with nodes `t_I ∈ T` within `Δ` of every point of their cell. -/
structure RiemannRule (lam : Measure ℝ) (Δ : ℝ) {N : ℕ} (I : Fin N → Set ℝ) (tn : Fin N → ℝ) : Prop where
  meas : ∀ k, MeasurableSet (I k)
  disj : Pairwise fun k l => Disjoint (I k) (I l)
  sub : ∀ k, I k ⊆ Icc 0 1
  cover : lam (Icc 0 1 \ ⋃ k, I k) = 0
  node : ∀ k, tn k ∈ Icc 0 1
  mesh : ∀ k, ∀ t ∈ I k, |t - tn k| ≤ Δ

end Disc

/-! ### T `prop:parallel` (`eq:H1eval`) -/

/-- `Λ₁ = √(coth 1)`. -/
def Lam1 : ℝ := Real.sqrt (Real.cosh 1 / Real.sinh 1)

/-! ### T `prop:linearmodel` (`eq:explicitbridge`) -/

section Linear
variable {K : ℕ}

/-- `A u = (t_k u_k)_k`. -/
def diagMap (t : Fin K → ℝ) (u : EuclideanSpace ℝ (Fin K)) : EuclideanSpace ℝ (Fin K) :=
  WithLp.toLp 2 fun k => t k * u k

/-- The support box of `U_h = h Σ_k a_k W_k e_k`, `W_k ∈ [−1/2, 1/2]`. -/
def cubeBox (h : ℝ) (a : Fin K → ℝ) : Set (EuclideanSpace ℝ (Fin K)) := {u | ∀ k, |u k| ≤ h * a k / 2}

/-- `B₂ = ½ max{(Σ a_k²)^{1/2}, (Σ t_k² a_k²)^{1/2}}`. -/
def B2 (a t : Fin K → ℝ) : ℝ :=
  max (Real.sqrt (∑ k, a k ^ 2)) (Real.sqrt (∑ k, t k ^ 2 * a k ^ 2)) / 2

/-- The tangent cost `c₀(u, v) = ½ ‖u − v‖²`. -/
def c0 (z : EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K)) : ℝ≥0∞ := ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)

/-- The field `u(s) = Σ_k u_k e_k(s)` of a coefficient vector (tangent fields `e_k` along `m`, ambient coordinates). -/
def fieldOf {T : Type*} {d : ℕ} (ef : Fin K → T → EuclideanSpace ℝ (Fin (d + 1))) (u : EuclideanSpace ℝ (Fin K))
    (s : T) : EuclideanSpace ℝ (Fin (d + 1)) :=
  ∑ k, u k • ef k s

/-- The geodesic cost on the unit sphere `c_g(u, v) = ½ D₂(E_m u, E_m v)²`, `D₂(x, y)² = ∫ d_{S^d}(x(s), y(s))² dλ(s)`,
`E_m u(s) = Exp_{m(s)} u(s)` (the frozen `sphDist`, `sphExp`). -/
def cgSph {T : Type*} [MeasurableSpace T] {d : ℕ} (lam : Measure T) (m : T → EuclideanSpace ℝ (Fin (d + 1)))
    (ef : Fin K → T → EuclideanSpace ℝ (Fin (d + 1)))
    (z : EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K)) : ℝ≥0∞ :=
  2⁻¹ * ∫⁻ s, ENNReal.ofReal (StatFormal.OTFD.Wave6b.sphDist (StatFormal.OTFD.Wave6b.sphExp (m s) (fieldOf ef z.1 s))
    (StatFormal.OTFD.Wave6b.sphExp (m s) (fieldOf ef z.2 s)) ^ 2) ∂lam

/-- `B_∞ = ½ max{Σ_k a_k ‖e_k‖_∞, Σ_k t_k a_k ‖e_k‖_∞}`, with `en k ≥ ‖e_k‖_∞`. -/
def Binf (a t en : Fin K → ℝ) : ℝ := max (∑ k, a k * en k) (∑ k, t k * a k * en k) / 2

end Linear

/-! ### T `prop:transfer-M`, `prop:chart` -/

/-- `ℝ^K`. -/
abbrev Euc (K : ℕ) := EuclideanSpace ℝ (Fin K)

/-- The radial distribution function `c_K(ρ) = μ_K{‖u‖ ≤ ρ}`. -/
def cK {K : ℕ} (μ : Measure (Euc K)) (ρ : ℝ) : ℝ := cdf (μ.map fun u => ‖u‖) ρ

/-- The sign `u/‖u‖` (`0` at the origin, a convention on a null set). -/
def sgnK {K : ℕ} (u : Euc K) : Euc K := ‖u‖⁻¹ • u

/-! ### A `prop:selector` -/

/-- The energy distance `ED(α, β) = 2E‖A − B‖ − E‖A − A'‖ − E‖B − B'‖` (independent copies). -/
def edPop {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] (α β : Measure E) : ℝ :=
  2 * ∫ z, ‖z.1 - z.2‖ ∂(α.prod β) - ∫ z, ‖z.1 - z.2‖ ∂(α.prod α) - ∫ z, ‖z.1 - z.2‖ ∂(β.prod β)

/-- `Δ = 2R h + R √(32 h log(2|Θ|/γ))`, `h = 1/n_v + 1/m_v`. -/
def DeltaSel (R : ℝ) (nv mv card : ℕ) (γ : ℝ) : ℝ :=
  2 * R * (1 / (nv : ℝ) + 1 / mv) + R * Real.sqrt (32 * (1 / (nv : ℝ) + 1 / mv) * Real.log (2 * card / γ))

namespace Claims

/-! #### C `lem:self-potentials` -/

/-- Entropic self-potentials are unique: two solutions of `eq:ent-self-pop`, continuous on the compact `D`
carrying `P`, agree on `D` (no density or support hypothesis). Covers the empirical and the population case. -/
def selfpot_ent_unique : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (D : Set E) (ε : ℝ) (F G : E → ℝ),
    IsCompact D → P Dᶜ = 0 → 0 < ε → ContinuousOn F D → ContinuousOn G D →
    (∀ x ∈ D, EntSelfEq P ε F x) → (∀ x ∈ D, EntSelfEq P ε G x) → ∀ x ∈ D, F x = G x

/-- Empirical existence: for a finitely supported `P = Σ_i p_i δ_{C_i}` (`p_i > 0`) there is a continuous
solution of `eq:ent-self-pop` at every point (in particular on `D`, with its out-of-sample extension). -/
def selfpot_ent_exists : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (n : ℕ) (p : Fin n → ℝ) (C : Fin n → E) (ε : ℝ),
    (∀ i, 0 < p i) → ∑ i, p i = 1 → 0 < ε →
      ∃ F : E → ℝ, Continuous F ∧ ∀ x, EntSelfEq (empW p C) ε F x

/-- Bounds and Lipschitz property of entropic self-potentials: if `diam D ≤ d`, `P` is carried by `D` and `F` is a
solution on `D`, continuous there, then `−d²/2 ≤ F ≤ d²` and `F` is `2d`-Lipschitz on `D`. -/
def selfpot_ent_bounds : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (D : Set E) (ε d : ℝ) (F : E → ℝ),
    IsCompact D → P Dᶜ = 0 → 0 < ε → 0 ≤ d → (∀ x ∈ D, ∀ y ∈ D, ‖x - y‖ ≤ d) → ContinuousOn F D →
    (∀ x ∈ D, EntSelfEq P ε F x) →
      (∀ x ∈ D, -d ^ 2 / 2 ≤ F x ∧ F x ≤ d ^ 2) ∧ ∀ x ∈ D, ∀ y ∈ D, |F x - F y| ≤ 2 * d * ‖x - y‖

/-- Bounds and Lipschitz property of quadratic self-potentials: `η/2 − d² ≤ H ≤ η/2 + 3d²/2`, `2d`-Lipschitz on `D`. -/
def selfpot_quad_bounds : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (D : Set E) (η d : ℝ) (H : E → ℝ),
    IsCompact D → P Dᶜ = 0 → 0 < η → 0 ≤ d → (∀ x ∈ D, ∀ y ∈ D, ‖x - y‖ ≤ d) → ContinuousOn H D →
    (∀ x ∈ D, QuadSelfEq P η H x) →
      (∀ x ∈ D, η / 2 - d ^ 2 ≤ H x ∧ H x ≤ η / 2 + 3 * d ^ 2 / 2) ∧
        ∀ x ∈ D, ∀ y ∈ D, |H x - H y| ≤ 2 * d * ‖x - y‖

/-- Empirical uniqueness of quadratic self-potentials: two solutions of `eq:quad-self-pop` for
`P = Σ_j p_j δ_{C_j}` (`p_j > 0`) agree at the sample points. -/
def selfpot_quad_unique : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n : ℕ) (p : Fin n → ℝ) (C : Fin n → E)
    (η : ℝ) (H H' : Fin n → ℝ),
    (∀ i, 0 < p i) → 0 < η →
    (∀ i, ∑ j, p j * max (H i + H j - ‖C i - C j‖ ^ 2) 0 = η) →
    (∀ i, ∑ j, p j * max (H' i + H' j - ‖C i - C j‖ ^ 2) 0 = η) → H = H'

/-- Empirical existence of the quadratic self-potential: for `P = Σ_i p_i δ_{C_i}` (`p_i > 0`) there is a continuous
solution of `eq:quad-self-pop` at every point (on `D`, with its out-of-sample extension). -/
def selfpot_quad_exists : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (n : ℕ) (p : Fin n → ℝ) (C : Fin n → E) (η : ℝ),
    (∀ i, 0 < p i) → ∑ i, p i = 1 → 0 < η →
      ∃ H : E → ℝ, Continuous H ∧ ∀ x, QuadSelfEq (empW p C) η H x

/-- Empirical uniqueness on `D` (sample points and out-of-sample extension): two solutions of `eq:quad-self-pop` for
`P = Σ_j p_j δ_{C_j}` on a set `D` containing the sample agree on `D`. -/
def selfpot_quad_unique_ext : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (n : ℕ) (p : Fin n → ℝ) (C : Fin n → E) (η : ℝ) (D : Set E) (H H' : E → ℝ),
    (∀ i, 0 < p i) → 0 < η → (∀ i, C i ∈ D) →
    (∀ x ∈ D, QuadSelfEq (empW p C) η H x) → (∀ x ∈ D, QuadSelfEq (empW p C) η H' x) → ∀ x ∈ D, H x = H' x

/-! #### G `prop:cap` on a grid -/

/-- (a) `b_K = sup{max_j |v(t_j)| : v ∈ S, ‖v‖ ≤ 1}` (attained). -/
def cap_sup : Prop :=
  ∀ (J q K : ℕ) (w : Fin J → ℝ) (φ : Fin K → Fin J → EuclideanSpace ℝ (Fin q)),
    1 ≤ J → (∀ j, 0 < w j) → GridOrthonormal w φ →
      IsGreatest {b | ∃ v ∈ Submodule.span ℝ (Set.range φ), gridNorm w v ≤ 1 ∧ b = gridSup v} (bK φ)

/-- (a) Hence `max_j |v(t_j)| ≤ b_K ‖v‖` on `S`, and `b_K` depends only on `S`: two orthonormal bases of the same span
give the same constant. -/
def cap_basis : Prop :=
  ∀ (J q K : ℕ) (w : Fin J → ℝ) (φ ψ : Fin K → Fin J → EuclideanSpace ℝ (Fin q)),
    1 ≤ J → (∀ j, 0 < w j) → GridOrthonormal w φ → GridOrthonormal w ψ →
    Submodule.span ℝ (Set.range φ) = Submodule.span ℝ (Set.range ψ) →
      bK φ = bK ψ ∧ ∀ v ∈ Submodule.span ℝ (Set.range φ), gridSup v ≤ bK φ * gridNorm w v

/-- (a) `b_K² ≥ K/min(K, q) ≥ 1` (weights summing to `λ(T) = 1`). -/
def cap_lower : Prop :=
  ∀ (J q K : ℕ) (w : Fin J → ℝ) (φ : Fin K → Fin J → EuclideanSpace ℝ (Fin q)),
    1 ≤ J → 1 ≤ q → 1 ≤ K → (∀ j, 0 < w j) → ∑ j, w j = 1 → GridOrthonormal w φ →
      (K : ℝ) / (min K q : ℕ) ≤ bK φ ^ 2 ∧ 1 ≤ (K : ℝ) / (min K q : ℕ)

/-- (e) Full rank on a grid: `b = (min_j w_j)^{−1/2}`. -/
def cap_full : Prop :=
  ∀ (J q K : ℕ) (w : Fin J → ℝ) (φ : Fin K → Fin J → EuclideanSpace ℝ (Fin q)),
    1 ≤ J → 1 ≤ q → (∀ j, 0 < w j) → GridOrthonormal w φ → Submodule.span ℝ (Set.range φ) = ⊤ →
      bK φ = 1 / Real.sqrt (⨅ j, w j)

/-- (e) Trapezoid weights on `J ≥ 2` equispaced nodes sum to one and give `(min_j w_j)^{−1/2} = √(2(J−1))`. -/
def cap_trapezoid : Prop :=
  ∀ J : ℕ, 2 ≤ J → ∑ j, trapW J j = 1 ∧ 1 / Real.sqrt (⨅ j, trapW J j) = Real.sqrt (2 * ((J : ℝ) - 1))

/-- (f) Pilot cap: a new draw independent of `r₀` i.i.d. pilot draws, all with the same atomless law, exceeds their
maximum with probability exactly `1/(r₀+1)` (coordinate `0` is the new draw). -/
def cap_pilot_exact : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (r : ℕ) (Y : Fin (r + 1) → Ω → ℝ)
    (ν : Measure ℝ), (∀ l, Measurable (Y l)) → iIndepFun Y P → (∀ l, P.map (Y l) = ν) → NullSingletonClass ν →
      P.real {ω | ∀ l : Fin (r + 1), l ≠ 0 → Y l ω < Y 0 ω} = 1 / ((r : ℝ) + 1)

/-- (f) Conditionally on the pilot, the cap is exceeded with positive probability: almost surely
`ν(max_l Y_l, ∞) > 0`. -/
def cap_pilot_support : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (r : ℕ) (Y : Fin r → Ω → ℝ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν], 1 ≤ r → (∀ l, Measurable (Y l)) → (∀ l, P.map (Y l) = ν) →
    NullSingletonClass ν → ∀ᵐ ω ∂P, 0 < ν (Ioi (⨆ l, Y l ω))

/-- (f) The statistic is atomless: `esssup_t |V(t)| = τ W` with `τ ~ Unif(0,1)` independent of `W`, `W ≠ 0` a.s. -/
def cap_pilot_atomless : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (τ W : Ω → ℝ),
    Measurable τ → Measurable W → IndepFun τ W P → P.map τ = volume.restrict (Ioc 0 1) → P {ω | W ω = 0} = 0 →
      NullSingletonClass (P.map fun ω => τ ω * W ω)

/-! #### G `prop:quantile`, flat -/

/-- In a Hilbert space, `z ↦ ∫ ‖z − x‖² dν(x)` has the unique minimiser `∫ x dν` (finite second moment). -/
def quantile_mean : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
    [SecondCountableTopology H] (ν : Measure H) [IsProbabilityMeasure ν], MemLp id 2 ν →
      ∀ z : H, (∀ z' : H, ∫ x, ‖z - x‖ ^ 2 ∂ν ≤ ∫ x, ‖z' - x‖ ^ 2 ∂ν) ↔ z = ∫ x, x ∂ν

/-- Flat quantile curves (`E_m(sv) = m + sv`, `D` the norm distance, data in a ball, `g` bounded): for every `v`
`π_ε(·|v)` is a probability, the quantile `Q_ε(v)` exists and is unique, `Q_ε(v) = ∫ x π_ε(dx|v)`, and
`v ↦ Q_ε(v)` is continuous. -/
def quantile_flat : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
    [SecondCountableTopology H] (P : Measure H) [IsProbabilityMeasure P] (ε s B : ℝ) (m : H) (g : H → ℝ),
    0 < ε → (∀ᵐ x ∂P, ‖x‖ ≤ B) → Measurable g → (∃ C, ∀ x, |g x| ≤ C) →
      (∀ v, IsProbabilityMeasure (flatCond P ε s m g v)) ∧
      (∀ v z : H, (∀ z' : H, ∫ x, ‖z - x‖ ^ 2 ∂(flatCond P ε s m g v) ≤
          ∫ x, ‖z' - x‖ ^ 2 ∂(flatCond P ε s m g v)) ↔ z = ∫ x, x ∂(flatCond P ε s m g v)) ∧
      Continuous fun v => ∫ x, x ∂(flatCond P ε s m g v)

/-! #### G `cor:discretisation` -/

/-- (a) The time-quadrature cost bound `|c^Δ − c_s| ≤ diam(M) Δ^α (ℓ_Y + ℓ_X)` for `α`-Hölder curves. -/
def disc_cost : Prop :=
  ∀ (M : Type) [MetricSpace M] (Dm : ℝ) (lam : Measure ℝ) [IsProbabilityMeasure lam] (Δ : ℝ) (α : ℝ≥0)
    (lY lX : ℝ≥0) (N : ℕ) (I : Fin N → Set ℝ) (tn : Fin N → ℝ) (y x : ℝ → M),
    lam (Icc 0 1)ᶜ = 0 → RiemannRule lam Δ I tn → 0 < α → α ≤ 1 → 0 ≤ Δ → (∀ p p' : M, dist p p' ≤ Dm) →
    HolderOnWith lY α y (Icc 0 1) → HolderOnWith lX α x (Icc 0 1) →
      |riemannCost lam I tn y x - curveCost lam y x| ≤ Dm * Δ ^ (α : ℝ) * (lY + lX)

/-- (a) Uniform Hölder constants: `∫ ‖F^Δ − F‖ dP ≤ diam(M) Δ^α (L_Y + L_X)/ε`. -/
def disc_rank_uniform : Prop :=
  ∀ (Hs 𝒳 M : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℝ Hs] [CompleteSpace Hs] [MeasurableSpace Hs]
    [BorelSpace Hs] [SecondCountableTopology Hs] [MeasurableSpace 𝒳] [MetricSpace M]
    (μ : Measure Hs) (P : Measure 𝒳) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (Dm : ℝ) (lam : Measure ℝ) [IsProbabilityMeasure lam] (Δ ε : ℝ) (α LY LX : ℝ≥0) (N : ℕ)
    (I : Fin N → Set ℝ) (tn : Fin N → ℝ) (Y : Hs → ℝ → M) (X : 𝒳 → ℝ → M) (f fΔ : Hs → ℝ) (g gΔ : 𝒳 → ℝ),
    lam (Icc 0 1)ᶜ = 0 → RiemannRule lam Δ I tn → 0 < α → α ≤ 1 → 0 ≤ Δ → 0 < ε →
    (∀ p p' : M, dist p p' ≤ Dm) → (∀ v, HolderOnWith LY α (Y v) (Icc 0 1)) →
    (∀ x, HolderOnWith LX α (X x) (Icc 0 1)) → (∀ᵐ v ∂μ, ‖v‖ ≤ 1) →
    Measurable (fun z : Hs × 𝒳 => curveCost lam (Y z.1) (X z.2)) →
    Measurable (fun z : Hs × 𝒳 => riemannCost lam I tn (Y z.1) (X z.2)) →
    GibbsHyp μ P ε (fun z => curveCost lam (Y z.1) (X z.2)) f g →
    GibbsHyp μ P ε (fun z => riemannCost lam I tn (Y z.1) (X z.2)) fΔ gΔ →
      ∫⁻ x, ‖gibbsMean μ ε (fun z => riemannCost lam I tn (Y z.1) (X z.2)) fΔ gΔ id x -
          gibbsMean μ ε (fun z => curveCost lam (Y z.1) (X z.2)) f g id x‖ₑ ∂P ≤
        ENNReal.ofReal (Dm * Δ ^ (α : ℝ) * (LY + LX) / ε)

/-- (a) Integrable Hölder constants: `∫ ‖F^Δ − F‖ dP ≤ 2{diam(M) Δ^α (Eℓ_Y + Eℓ_X)/(2ε)}^{1/2}`. -/
def disc_rank_integrable : Prop :=
  ∀ (Hs 𝒳 M : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℝ Hs] [CompleteSpace Hs] [MeasurableSpace Hs]
    [BorelSpace Hs] [SecondCountableTopology Hs] [MeasurableSpace 𝒳] [MetricSpace M]
    (μ : Measure Hs) (P : Measure 𝒳) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (Dm : ℝ) (lam : Measure ℝ) [IsProbabilityMeasure lam] (Δ ε : ℝ) (α : ℝ≥0) (N : ℕ)
    (I : Fin N → Set ℝ) (tn : Fin N → ℝ) (Y : Hs → ℝ → M) (X : 𝒳 → ℝ → M) (ℓY : Hs → ℝ) (ℓX : 𝒳 → ℝ)
    (f fΔ : Hs → ℝ) (g gΔ : 𝒳 → ℝ),
    lam (Icc 0 1)ᶜ = 0 → RiemannRule lam Δ I tn → 0 < α → α ≤ 1 → 0 ≤ Δ → 0 < ε →
    (∀ p p' : M, dist p p' ≤ Dm) → (∀ v, 0 ≤ ℓY v) → (∀ x, 0 ≤ ℓX x) →
    (∀ v, HolderOnWith (ℓY v).toNNReal α (Y v) (Icc 0 1)) →
    (∀ x, HolderOnWith (ℓX x).toNNReal α (X x) (Icc 0 1)) → Integrable ℓY μ → Integrable ℓX P →
    (∀ᵐ v ∂μ, ‖v‖ ≤ 1) →
    Measurable (fun z : Hs × 𝒳 => curveCost lam (Y z.1) (X z.2)) →
    Measurable (fun z : Hs × 𝒳 => riemannCost lam I tn (Y z.1) (X z.2)) →
    GibbsHyp μ P ε (fun z => curveCost lam (Y z.1) (X z.2)) f g →
    GibbsHyp μ P ε (fun z => riemannCost lam I tn (Y z.1) (X z.2)) fΔ gΔ →
      ∫⁻ x, ‖gibbsMean μ ε (fun z => riemannCost lam I tn (Y z.1) (X z.2)) fΔ gΔ id x -
          gibbsMean μ ε (fun z => curveCost lam (Y z.1) (X z.2)) f g id x‖ₑ ∂P ≤
        ENNReal.ofReal (2 * Real.sqrt (Dm * Δ ^ (α : ℝ) * (∫ v, ℓY v ∂μ + ∫ x, ℓX x ∂P) / (2 * ε)))

/-- (b) The cost perturbation of a truncated reference: if the reference curves are within `s` of the base curve
and the data within `B`, then `|½D(y_K, x)² − ½D(y, x)²| ≤ (s + B) D(y_K, y)`. -/
def disc_trunc_cost : Prop :=
  ∀ (𝒳 : Type) [MetricSpace 𝒳] (m y yK x : 𝒳) (s B : ℝ),
    dist y m ≤ s → dist yK m ≤ s → dist m x ≤ B →
      |dist yK x ^ 2 / 2 - dist y x ^ 2 / 2| ≤ (s + B) * dist yK y

/-- (b) Reference truncation, on the reference space `(ϖ, ϱ)` with `V, V_K` and the lifted plans:
`∫ ‖F^{(K)} − F‖ dP ≤ 2{(s + B) e'_K/(2ε)}^{1/2} + e_K`, `e'_K = E D(E_m(sV_K), E_m(sV))`, `e_K = E‖V − V_K‖`. -/
def disc_trunc_rank : Prop :=
  ∀ (Ωr 𝒳 Hs : Type) [MeasurableSpace Ωr] [MetricSpace 𝒳] [SecondCountableTopology 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳]
    [NormedAddCommGroup Hs] [InnerProductSpace ℝ Hs] [CompleteSpace Hs] [MeasurableSpace Hs] [BorelSpace Hs]
    [SecondCountableTopology Hs]
    (ϱ : Measure Ωr) (P : Measure 𝒳) [IsProbabilityMeasure ϱ] [IsProbabilityMeasure P]
    (V VK : Ωr → Hs) (Em : Hs → 𝒳) (m : 𝒳) (s B ε : ℝ) (f fK : Ωr → ℝ) (g gK : 𝒳 → ℝ),
    0 < ε → Measurable V → Measurable VK → Continuous Em → (∀ v, ‖v‖ ≤ 1 → dist (Em v) m ≤ s) →
    (∀ ω, ‖V ω‖ ≤ 1) → (∀ ω, ‖VK ω‖ ≤ 1) → (∀ x, dist m x ≤ B) →
    GibbsHyp ϱ P ε (fun z => dist (Em (V z.1)) z.2 ^ 2 / 2) f g →
    GibbsHyp ϱ P ε (fun z => dist (Em (VK z.1)) z.2 ^ 2 / 2) fK gK →
      ∫⁻ x, ‖gibbsMean ϱ ε (fun z => dist (Em (VK z.1)) z.2 ^ 2 / 2) fK gK VK x -
          gibbsMean ϱ ε (fun z => dist (Em (V z.1)) z.2 ^ 2 / 2) f g V x‖ₑ ∂P ≤
        ENNReal.ofReal (2 * Real.sqrt ((s + B) * (∫ ω, dist (Em (VK ω)) (Em (V ω)) ∂ϱ) / (2 * ε)) +
          ∫ ω, ‖V ω - VK ω‖ ∂ϱ)

/-! #### T `prop:parallel` (`eq:H1eval`) -/

/-- `sup_t ‖v(t)‖ ≤ Λ₁ ‖v‖_{H₁}` with `Λ₁ = √(coth 1)`, for `C¹` fields on `[0,1]` in a parallel frame. -/
def h1_eval : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f f' : ℝ → E),
    ContinuousOn f (Icc 0 1) → ContinuousOn f' (Icc 0 1) → (∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt f (f' s) s) →
      ∀ t ∈ Icc (0 : ℝ) 1, ‖f t‖ ≤ Lam1 * Real.sqrt (∫ s in (0 : ℝ)..1, ‖f s‖ ^ 2 + ‖f' s‖ ^ 2)

/-- `Λ₁` is sharp, attained at both endpoints of `T` (by `cosh(1 − s) e` at `t = 0`, `cosh(s) e` at `t = 1`). -/
def h1_sharp : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nontrivial E] (t : ℝ), t = 0 ∨ t = 1 →
    ∃ f f' : ℝ → E, ContinuousOn f (Icc 0 1) ∧ ContinuousOn f' (Icc 0 1) ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt f (f' s) s) ∧ 0 < ∫ s in (0 : ℝ)..1, ‖f s‖ ^ 2 + ‖f' s‖ ^ 2 ∧
        ‖f t‖ = Lam1 * Real.sqrt (∫ s in (0 : ℝ)..1, ‖f s‖ ^ 2 + ‖f' s‖ ^ 2)

/-- `Λ₁ = 1.145877…`. -/
def h1_const : Prop := 1.145877 < Lam1 ∧ Lam1 < 1.145878

/-! #### T `thm:population` -/

/-- `eq:Hilbertinverse`: for `ν, μ` boundedly supported and null on Lipschitz hypersurfaces of a separable Hilbert
space, quadratic transport supplies a.e. subgradient (convex-potential) maps `F_ν`, `Q_ν` with `F_ν#ν = μ`,
`Q_ν#μ = ν`, `Q_ν F_ν = Id` `ν`-a.e., `F_ν Q_ν = Id` `μ`-a.e.; each graph plan is the unique optimal plan. -/
def pop_hilbert : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (ν μ : Measure H) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] (B Bμ : ℝ),
    LipNull ν → LipNull μ → (∀ᵐ v ∂ν, ‖v‖ ≤ B) → (∀ᵐ u ∂μ, ‖u‖ ≤ Bμ) →
      ∃ F Q : H → H, IsRankPair μ ν F Q ∧ IsGradMap ν μ F ∧ IsGradMap μ ν Q ∧
        (∀ π, TauCeti.IsOptimalCoupling StatFormal.OTFD.Wave8c.quadCost π ν μ ↔ π = TauCeti.graphPlan F ν) ∧
        ∀ π, TauCeti.IsOptimalCoupling StatFormal.OTFD.Wave8c.quadCost π μ ν ↔ π = TauCeti.graphPlan Q μ

/-- `eq:manifoldinverse`: through a Borel chart `E_m` with Borel inverse `L_m` on `𝒟_r`, with `X ∈ 𝒳_r = E_m(𝒟_r)`
a.s., the maps `F^m = F_ν L_m`, `Q^m = E_m Q_ν` satisfy `F^m#P = μ`, `Q^m#μ = P` and are mutual inverses a.e. -/
def pop_manifold : Prop :=
  ∀ (H X : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (μ : Measure H) [IsProbabilityMeasure μ]
    (Em : H → X) (Lm : X → H) (Dr : Set H) (F Q : H → H),
    Measurable Em → Measurable Lm → MeasurableSet Dr → (∀ v ∈ Dr, Lm (Em v) = v) → (∀ᵐ x ∂P, Lm x ∈ Dr ∧ Em (Lm x) = x) →
    IsRankPair μ (P.map Lm) F Q →
      P.map (F ∘ Lm) = μ ∧ μ.map (Em ∘ Q) = P ∧ (∀ᵐ x ∂P, Em (Q (F (Lm x))) = x) ∧
        ∀ᵐ u ∂μ, F (Lm (Em (Q u))) = u

/-- Full-measure Borel sets `Ω_P`, `Ω_μ` on which `F^m`, `Q^m` are mutual inverse bijections; the rank-defined region
`C = Ω_P ∩ (F^m)⁻¹(A)` of a Borel `A` has `P(C) = μ(A)` (so `P(C_p) = p` when `μ(A_p) = p`), and `C = Q^m(Ω_μ ∩ A)`. -/
def pop_regions : Prop :=
  ∀ (H X : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] (P : Measure X) [IsProbabilityMeasure P] (μ : Measure H)
    [IsProbabilityMeasure μ] (Fm : X → H) (Qm : H → X),
    Measurable Fm → Measurable Qm → P.map Fm = μ → μ.map Qm = P → (∀ᵐ x ∂P, Qm (Fm x) = x) →
    (∀ᵐ u ∂μ, Fm (Qm u) = u) →
      ∃ ΩP : Set X, ∃ Ωμ : Set H, MeasurableSet ΩP ∧ MeasurableSet Ωμ ∧ P ΩPᶜ = 0 ∧ μ Ωμᶜ = 0 ∧
        (∀ x ∈ ΩP, Fm x ∈ Ωμ ∧ Qm (Fm x) = x) ∧ (∀ u ∈ Ωμ, Qm u ∈ ΩP ∧ Fm (Qm u) = u) ∧
        ∀ A : Set H, MeasurableSet A → P (ΩP ∩ Fm ⁻¹' A) = μ A ∧ ΩP ∩ Fm ⁻¹' A = Qm '' (Ωμ ∩ A)

/-! #### T `prop:linearmodel` (`eq:explicitbridge`), finite rank -/

/-- The tangent quadratic optimal map from `μ_h` to `ν_h = A#μ_h` is `Q₀(u) = Au`: its graph plan is optimal for
`c₀` and is the only optimal plan (positive dual gap). -/
def lm_tangent : Prop :=
  ∀ (K : ℕ) (μ : Measure (Euc K)) [IsProbabilityMeasure μ] (h tm tp : ℝ) (a t : Fin K → ℝ),
    0 < h → 0 < tm → (∀ k, 0 < a k) → (∀ k, tm ≤ t k ∧ t k ≤ tp) → μ (cubeBox h a)ᶜ = 0 →
      ∀ π, TauCeti.IsOptimalCoupling c0 π μ (μ.map (diagMap t)) ↔ π = TauCeti.graphPlan (diagMap t) μ

/-- An optimal coupling exists for every continuous geodesic-type cost. -/
def lm_exists : Prop :=
  ∀ (K : ℕ) (μ : Measure (Euc K)) [IsProbabilityMeasure μ] (t : Fin K → ℝ) (cg : Euc K × Euc K → ℝ≥0∞),
    LowerSemicontinuous cg → ∃ π, TauCeti.IsOptimalCoupling cg π μ (μ.map (diagMap t))

/-- `eq:explicitbridge`: if `a² c₀ ≤ c_g ≤ c₀` on the supports (`a = sin r_h / r_h` on the unit sphere,
`prop:distortion`), every `c_g`-optimal coupling satisfies `∫ ‖v − Au‖² dπ ≤ 4 t₊ h² B₂² (1 − a²)`. -/
def lm_bridge : Prop :=
  ∀ (K : ℕ) (μ : Measure (Euc K)) [IsProbabilityMeasure μ] (h tm tp a0 : ℝ) (a t : Fin K → ℝ)
    (cg : Euc K × Euc K → ℝ≥0∞) (π : Measure (Euc K × Euc K)),
    0 < h → 0 < tm → (∀ k, 0 < a k) → (∀ k, tm ≤ t k ∧ t k ≤ tp) → μ (cubeBox h a)ᶜ = 0 → 0 < a0 → a0 ≤ 1 →
    Measurable cg →
    (∀ u ∈ cubeBox h a, ∀ v ∈ diagMap t '' cubeBox h a,
      ENNReal.ofReal (a0 ^ 2) * c0 (u, v) ≤ cg (u, v) ∧ cg (u, v) ≤ c0 (u, v)) →
    TauCeti.IsOptimalCoupling cg π μ (μ.map (diagMap t)) →
      ∫⁻ z, ‖z.2 - diagMap t z.1‖ₑ ^ 2 ∂π ≤ ENNReal.ofReal (4 * tp * h ^ 2 * B2 a t ^ 2 * (1 - a0 ^ 2))

/-- The order of the bound: `1 − (sin r/r)² ≤ r²/3`, so with `r_h = h B_∞` the right side is `O(h⁴)`. -/
def lm_order : Prop := ∀ r : ℝ, 0 < r → 1 - (Real.sin r / r) ^ 2 ≤ r ^ 2 / 3

/-- `eq:explicitbridge` UNCONDITIONALLY on the unit sphere `S^d` (finite rank `K`): fields `u = Σ_k u_k e_k` with
`e_k` measurable tangent fields along a measurable base curve `m`, orthonormal in `L²(λ)` and bounded by `en k`;
`c_g = ½ D₂(E_m u, E_m v)²`; if `0 < r_h = h B_∞ < π`, every `c_g`-optimal coupling of `μ_h` and `A#μ_h` satisfies
`∫ ‖v − Au‖² dπ ≤ 4 t₊ h² B₂² (1 − (sin r_h/r_h)²)`. The sandwich of `lm_bridge` is discharged by the certified
`eq:bilip` (Wave 7b). -/
def lm_bridge_sphere : Prop :=
  ∀ (K d : ℕ) (T : Type) [MeasurableSpace T] (lam : Measure T) [IsFiniteMeasure lam]
    (m : T → EuclideanSpace ℝ (Fin (d + 1))) (ef : Fin K → T → EuclideanSpace ℝ (Fin (d + 1))) (en : Fin K → ℝ)
    (μ : Measure (Euc K)) [IsProbabilityMeasure μ] (h tm tp : ℝ) (a t : Fin K → ℝ) (π : Measure (Euc K × Euc K)),
    0 < h → 0 < tm → (∀ k, 0 < a k) → (∀ k, tm ≤ t k ∧ t k ≤ tp) → μ (cubeBox h a)ᶜ = 0 →
    Measurable m → (∀ s, ‖m s‖ = 1) → (∀ k, Measurable (ef k)) → (∀ k s, ⟪m s, ef k s⟫ = 0) →
    (∀ k s, ‖ef k s‖ ≤ en k) → (∀ k l, ∫ s, ⟪ef k s, ef l s⟫ ∂lam = if k = l then 1 else 0) →
    0 < h * Binf a t en → h * Binf a t en < Real.pi →
    TauCeti.IsOptimalCoupling (cgSph lam m ef) π μ (μ.map (diagMap t)) →
      ∫⁻ z, ‖z.2 - diagMap t z.1‖ₑ ^ 2 ∂π ≤
        ENNReal.ofReal (4 * tp * h ^ 2 * B2 a t ^ 2 * (1 - (Real.sin (h * Binf a t en) / (h * Binf a t en)) ^ 2))

/-! #### T `prop:transfer-M`, fixed charts `Φ_g = E_{c_g}(v̄ + ι_K ·)` with Borel inverses `Ψ_g` -/

/-- (i) `T_{A→B}#P^K_A = P^K_B`, and `P^K_A`-a.e. the depth and the sign of `T_{A→B}x` in `B` equal those of `x` in
`A` (the ranks agree). -/
def transferM_push : Prop :=
  ∀ (K : ℕ) (X : Type) [MeasurableSpace X] (μ : Measure (Euc K)) (PA PB : Measure X)
    (ΦA ΦB : Euc K → X) (ΨA ΨB : X → Euc K) (FA QA FB QB : Euc K → Euc K),
    Measurable ΦA → Measurable ΦB → Measurable ΨA → Measurable ΨB →
    (∀ᵐ x ∂PA, ΦA (ΨA x) = x) → (∀ᵐ x ∂PB, ΦB (ΨB x) = x) →
    IsRankPair μ (PA.map ΨA) FA QA → IsRankPair μ (PB.map ΨB) FB QB →
      PA.map (fun x => ΦB (QB (FA (ΨA x)))) = PB ∧
        ∀ᵐ x ∂PA, FB (ΨB (ΦB (QB (FA (ΨA x))))) = FA (ΨA x) ∧
          cK μ ‖FB (ΨB (ΦB (QB (FA (ΨA x)))))‖ = cK μ ‖FA (ΨA x)‖ ∧
          sgnK (FB (ΨB (ΦB (QB (FA (ΨA x)))))) = sgnK (FA (ΨA x))

/-- (ii) `T_{A→B}` is the `P^K_A`-a.e. unique Borel map with the properties in (i) (depth and sign preserved). -/
def transferM_unique : Prop :=
  ∀ (K : ℕ) (X : Type) [MeasurableSpace X] (μ : Measure (Euc K)) [IsProbabilityMeasure μ] (PA PB : Measure X)
    [IsProbabilityMeasure PA] (ΦA ΦB : Euc K → X) (ΨA ΨB : X → Euc K) (FA QA FB QB : Euc K → Euc K) (T' : X → X),
    Measurable ΦA → Measurable ΦB → Measurable ΨA → Measurable ΨB →
    (∀ᵐ x ∂PA, ΦA (ΨA x) = x) → (∀ᵐ x ∂PB, ΦB (ΨB x) = x) →
    IsRankPair μ (PA.map ΨA) FA QA → IsRankPair μ (PB.map ΨB) FB QB →
    Measurable T' → PA.map T' = PB →
    (∀ᵐ x ∂PA, cK μ ‖FB (ΨB (T' x))‖ = cK μ ‖FA (ΨA x)‖) →
    (∀ᵐ x ∂PA, sgnK (FB (ΨB (T' x))) = sgnK (FA (ΨA x))) →
      ∀ᵐ x ∂PA, T' x = ΦB (QB (FA (ΨA x)))

/-- (iii) Cocycle: `T_{A→A} = Id` and `T_{B→C} ∘ T_{A→B} = T_{A→C}`, `P^K_A`-a.e. -/
def transferM_cocycle : Prop :=
  ∀ (K : ℕ) (X : Type) [MeasurableSpace X] (μ : Measure (Euc K)) (PA PB PC : Measure X)
    (ΦA ΦB ΦC : Euc K → X) (ΨA ΨB ΨC : X → Euc K) (FA QA FB QB FC QC : Euc K → Euc K),
    Measurable ΦA → Measurable ΦB → Measurable ΦC → Measurable ΨA → Measurable ΨB → Measurable ΨC →
    (∀ᵐ x ∂PA, ΦA (ΨA x) = x) → (∀ᵐ x ∂PB, ΦB (ΨB x) = x) → (∀ᵐ x ∂PC, ΦC (ΨC x) = x) →
    IsRankPair μ (PA.map ΨA) FA QA → IsRankPair μ (PB.map ΨB) FB QB → IsRankPair μ (PC.map ΨC) FC QC →
      (∀ᵐ x ∂PA, ΦA (QA (FA (ΨA x))) = x) ∧
        ∀ᵐ x ∂PA, ΦC (QC (FB (ΨB (ΦB (QB (FA (ΨA x))))))) = ΦC (QC (FA (ΨA x)))

/-! #### T `prop:chart`, flat case (`M = ℝ^d`, constant frames, common sieve basis `e`, `v̄ = 0`) -/

/-- (ii) `T^shared_{A→B} − T^moving_{A→B} = −(I − P_K)(m_B − m_0)`, `P_A`-a.e.; the detail-preserving transfers differ by
`−(I − P_K)(m_B − m_A)`; the projected transfers agree iff the sieve holds `m_B − m_0`, the detail-preserving ones iff
it holds `m_B − m_A`. The shared-chart maps are any
McCann rank pairs of the translated coefficient laws (translation equivariance is proved, by Brenier uniqueness). -/
def chart_flat : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (K : ℕ) (e : ℕ → H) (μ : Measure (Euc K)) [IsProbabilityMeasure μ] (PA PB : Measure H)
    [IsProbabilityMeasure PA] [IsProbabilityMeasure PB] (m0 mA mB : H)
    (FmA QmA FmB QmB FsA QsA FsB QsB : Euc K → Euc K),
    μ ≪ volume → MemLp id 2 μ → MemLp id 2 PA → MemLp id 2 PB →
    IsRankPair μ (PA.map fun x => proj e K (x - mA)) FmA QmA →
    IsRankPair μ (PB.map fun x => proj e K (x - mB)) FmB QmB →
    IsRankPair μ (PA.map fun x => proj e K (x - m0)) FsA QsA →
    IsRankPair μ (PB.map fun x => proj e K (x - m0)) FsB QsB →
    IsGradMap μ (PA.map fun x => proj e K (x - mA)) QmA → IsGradMap μ (PB.map fun x => proj e K (x - mB)) QmB →
    IsGradMap μ (PA.map fun x => proj e K (x - m0)) QsA → IsGradMap μ (PB.map fun x => proj e K (x - m0)) QsB →
      (∀ᵐ x ∂PA, (m0 + embed e K (QsB (FsA (proj e K (x - m0))))) -
          (mB + embed e K (QmB (FmA (proj e K (x - mA))))) =
          -((mB - m0) - embed e K (proj e K (mB - m0)))) ∧
      (∀ᵐ x ∂PA, (m0 + embed e K (QsB (FsA (proj e K (x - m0)))) +
            ((x - m0) - embed e K (proj e K (x - m0)))) -
          (mB + embed e K (QmB (FmA (proj e K (x - mA)))) + ((x - mA) - embed e K (proj e K (x - mA)))) =
          -((mB - mA) - embed e K (proj e K (mB - mA)))) ∧
      ((∀ᵐ x ∂PA, m0 + embed e K (QsB (FsA (proj e K (x - m0)))) =
          mB + embed e K (QmB (FmA (proj e K (x - mA))))) ↔ mB - m0 = embed e K (proj e K (mB - m0))) ∧
      ((∀ᵐ x ∂PA, m0 + embed e K (QsB (FsA (proj e K (x - m0)))) + ((x - m0) - embed e K (proj e K (x - m0))) =
          mB + embed e K (QmB (FmA (proj e K (x - mA)))) + ((x - mA) - embed e K (proj e K (x - mA)))) ↔
        mB - mA = embed e K (proj e K (mB - mA)))

/-- (iii) on `ℝ^d`: if `P_B = ψ#P_A` for a translation `ψ(x) = x + c` and the base curves are the mean curves, the
moving-chart transfer equals `ψ` `P^K_A`-a.e. (at `y = m_A + ι_KΠ_K(x − m_A)`, `x ∼ P_A`, i.e. `y ∼ P^K_A`) and the
detail-preserving transfer equals `ψ` `P_A`-a.e., for every reference and every common orthonormal sieve basis. -/
def chart_translation : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
    (K : ℕ) (e : ℕ → H) (μ : Measure (Euc K)) [IsProbabilityMeasure μ] (PA : Measure H) [IsProbabilityMeasure PA]
    (c : H) (FA QA FB QB : Euc K → Euc K),
    Orthonormal ℝ e → μ ≪ volume → MemLp id 2 μ → MemLp id 2 PA →
    IsRankPair μ (PA.map fun x => proj e K (x - ∫ y, y ∂PA)) FA QA →
    IsRankPair μ ((PA.map fun x => x + c).map fun x => proj e K (x - ∫ y, y ∂(PA.map fun x => x + c))) FB QB →
    IsGradMap μ (PA.map fun x => proj e K (x - ∫ y, y ∂PA)) QA →
    IsGradMap μ ((PA.map fun x => x + c).map fun x => proj e K (x - ∫ y, y ∂(PA.map fun x => x + c))) QB →
      (∀ᵐ x ∂PA, (∫ y, y ∂(PA.map fun x => x + c)) + embed e K (QB (FA (proj e K
            (((∫ y, y ∂PA) + embed e K (proj e K (x - ∫ y, y ∂PA))) - ∫ y, y ∂PA)))) =
          ((∫ y, y ∂PA) + embed e K (proj e K (x - ∫ y, y ∂PA))) + c) ∧
      ∀ᵐ x ∂PA, (∫ y, y ∂(PA.map fun x => x + c)) + embed e K (QB (FA (proj e K (x - ∫ y, y ∂PA)))) +
          ((x - ∫ y, y ∂PA) - embed e K (proj e K (x - ∫ y, y ∂PA))) = x + c

/-! #### A `prop:selector` (i) -/

/-- (i) Given the training fold (candidate maps `Φ_θ = Υ F̂_θ` fixed, `‖Υ‖ ≤ R`), with probability at least `1 − γ` over
the validation fold `Z ~ P_K^{n_v}` and the reference draws `U ~ μ_K^{m_v}`, `sup_θ |D̂(θ) − D(θ)| ≤ Δ`; on the same event
every `s`-approximate minimiser `θ̂` of `D̂` has `D(θ̂) ≤ min_θ D + 2Δ + s` (`s = 0`: the minimiser). -/
def selector_dev : Prop :=
  ∀ (E X Y Θ : Type) [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace X] [MeasurableSpace Y] [Fintype Θ] [Nonempty Θ]
    (P : Measure X) (μ : Measure Y) [IsProbabilityMeasure P] [IsProbabilityMeasure μ] (nv mv : ℕ) (R γ : ℝ)
    (Φ : Θ → X → E) (Ψ : Y → E),
    1 ≤ nv → 1 ≤ mv → 0 < γ → γ < 1 → (∀ θ, Measurable (Φ θ)) → Measurable Ψ →
    (∀ θ x, ‖Φ θ x‖ ≤ R) → (∀ y, ‖Ψ y‖ ≤ R) →
      ∃ S : Set ((Fin nv → X) × (Fin mv → Y)), MeasurableSet S ∧
        ENNReal.ofReal (1 - γ) ≤ ((Measure.pi fun _ : Fin nv => P).prod (Measure.pi fun _ : Fin mv => μ)) S ∧
        (S ⊆ {w | ∀ θ, |edStat (fun i => Φ θ (w.1 i)) (fun j => Ψ (w.2 j)) - edPop (P.map (Φ θ)) (μ.map Ψ)| ≤
            DeltaSel R nv mv (Fintype.card Θ) γ}) ∧
        ∀ (θhat : (Fin nv → X) × (Fin mv → Y) → Θ) (s : ℝ),
          S ⊆ {w | (∀ θ, edStat (fun i => Φ (θhat w) (w.1 i)) (fun j => Ψ (w.2 j)) ≤
                edStat (fun i => Φ θ (w.1 i)) (fun j => Ψ (w.2 j)) + s) →
              ∀ θ, edPop (P.map (Φ (θhat w))) (μ.map Ψ) ≤
                edPop (P.map (Φ θ)) (μ.map Ψ) + 2 * DeltaSel R nv mv (Fintype.card Θ) γ + s}

/-! #### A `cor:convergent-references` -/

/-- (a) If the embedded references converge weakly, `ι_K#ν_K ⇀ μ`, then `supp μ ⊆ B̄(0, M)` and
`E‖Y_K − 𝔽^μ_P(X)‖² → 0` — CONDITIONAL on the Brenier–Gigli uniqueness `BrenierUniq P μ 𝔽^μ_P` (as in WaveL1). -/
def convref_a : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (P μ : ProbabilityMeasure H) (e : ℕ → H) (M : ℝ)
    (ν : ∀ K, Measure (Euc K)) (F : ∀ K, Euc K → Euc K) (νH : ℕ → ProbabilityMeasure H) (Fμ : H → H),
    Orthonormal ℝ e → LipNull (P : Measure H) → (∀ K, ν K (Metric.closedBall 0 M)ᶜ = 0) →
    (∀ K, Measurable (F K)) → (∀ K, ((P : Measure H).map (truncK e K)).map (F K) = ν K) →
    (∀ K, IsCMMapAE ((P : Measure H).map (truncK e K)) (F K)) →
    (∀ K, (νH K : Measure H) = (ν K).map (embed e K)) → Tendsto νH atTop (𝓝 μ) →
    Measurable Fμ → BrenierUniq (P : Measure H) μ Fμ →
      (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 ∧
        Tendsto (fun K => ∫⁻ x, ‖embed e K (F K (truncK e K x)) - Fμ x‖ₑ ^ 2 ∂(P : Measure H)) atTop (𝓝 0)

/-- (b) If `Y_K = ι_K F_K(Π_K X)` converges in probability to `Y`, then `ι_K#ν_K ⇀ L(Y)`, and `Y = 𝔽^{L(Y)}_P(X)` a.s.
(the identification CONDITIONAL on `BrenierUniq P L(Y) 𝔽`). -/
def convref_b : Prop :=
  ∀ (H Ω : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (X Y : Ω → H) (e : ℕ → H) (M : ℝ) (ν : ∀ K, Measure (Euc K)) (F : ∀ K, Euc K → Euc K)
    (νH : ℕ → ProbabilityMeasure H) (μY : ProbabilityMeasure H),
    Measurable X → Measurable Y → Orthonormal ℝ e → LipNull (Pr.map X) → (∀ K, ν K (Metric.closedBall 0 M)ᶜ = 0) →
    (∀ K, Measurable (F K)) → (∀ K, ((Pr.map X).map (truncK e K)).map (F K) = ν K) →
    (∀ K, IsCMMapAE ((Pr.map X).map (truncK e K)) (F K)) →
    (∀ K, (νH K : Measure H) = (ν K).map (embed e K)) → (μY : Measure H) = Pr.map Y →
    TendstoInMeasure Pr (fun K ω => embed e K (F K (truncK e K (X ω)))) atTop Y →
      Tendsto νH atTop (𝓝 μY) ∧
        ∀ Fμ : H → H, Measurable Fμ → BrenierUniq (Pr.map X) (μY : Measure H) Fμ → ∀ᵐ ω ∂Pr, Y ω = Fμ (X ω)

/-- (a) UNCONDITIONALLY: `BrenierUniq` discharged by the certified WaveL3 `brenier_uniq_H_bdd` (bounded target), at
the price of a first moment `m₁(P) < ∞` (the corollary assumes none); `𝔽^μ_P` any Borel map, `P`-a.e. cyclically
monotone, pushing `P` to `μ`. -/
def convref_a_uncond : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (P μ : ProbabilityMeasure H) (e : ℕ → H) (M : ℝ)
    (ν : ∀ K, Measure (Euc K)) (F : ∀ K, Euc K → Euc K) (νH : ℕ → ProbabilityMeasure H) (Fμ : H → H),
    Orthonormal ℝ e → LipNull (P : Measure H) → StatFormal.OTFD.WaveL3.Mom1 (P : Measure H) ≠ ∞ →
    (∀ K, ν K (Metric.closedBall 0 M)ᶜ = 0) →
    (∀ K, Measurable (F K)) → (∀ K, ((P : Measure H).map (truncK e K)).map (F K) = ν K) →
    (∀ K, IsCMMapAE ((P : Measure H).map (truncK e K)) (F K)) →
    (∀ K, (νH K : Measure H) = (ν K).map (embed e K)) → Tendsto νH atTop (𝓝 μ) →
    Measurable Fμ → (P : Measure H).map Fμ = μ → IsCMMapAE (P : Measure H) Fμ →
      (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 ∧
        Tendsto (fun K => ∫⁻ x, ‖embed e K (F K (truncK e K x)) - Fμ x‖ₑ ^ 2 ∂(P : Measure H)) atTop (𝓝 0)

/-- (b) UNCONDITIONALLY (with `m₁(P) < ∞`): if `Y_K → Y` in probability then `ι_K#ν_K ⇀ L(Y)`, and `Y = 𝔽(X)` a.s. for
every Borel `𝔽`, `P`-a.e. cyclically monotone, pushing `P` to `L(Y)`. -/
def convref_b_uncond : Prop :=
  ∀ (H Ω : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (X Y : Ω → H) (e : ℕ → H) (M : ℝ) (ν : ∀ K, Measure (Euc K)) (F : ∀ K, Euc K → Euc K)
    (νH : ℕ → ProbabilityMeasure H) (μY : ProbabilityMeasure H),
    Measurable X → Measurable Y → Orthonormal ℝ e → LipNull (Pr.map X) →
    StatFormal.OTFD.WaveL3.Mom1 (Pr.map X) ≠ ∞ → (∀ K, ν K (Metric.closedBall 0 M)ᶜ = 0) →
    (∀ K, Measurable (F K)) → (∀ K, ((Pr.map X).map (truncK e K)).map (F K) = ν K) →
    (∀ K, IsCMMapAE ((Pr.map X).map (truncK e K)) (F K)) →
    (∀ K, (νH K : Measure H) = (ν K).map (embed e K)) → (μY : Measure H) = Pr.map Y →
    TendstoInMeasure Pr (fun K ω => embed e K (F K (truncK e K (X ω)))) atTop Y →
      Tendsto νH atTop (𝓝 μY) ∧
        ∀ Fμ : H → H, Measurable Fμ → (Pr.map X).map Fμ = μY → IsCMMapAE (Pr.map X) Fμ →
          ∀ᵐ ω ∂Pr, Y ω = Fμ (X ω)

/-- The per-`K` spherical reference with `c ≤ λ_min(M_K) ≤ λ_max(M_K) ≤ C` fails the hypothesis of (a): its embeddings
`ι_K#μ°_K` have no weak limit in `H` (norm topology). -/
def convref_spherical : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (e : ℕ → H)
    (L : ∀ K : ℕ, EuclideanSpace ℝ (Fin K) ≃L[ℝ] EuclideanSpace ℝ (Fin K)) (c C : ℝ),
    Orthonormal ℝ e → 0 < c → (∀ K v, c * ‖v‖ ^ 2 ≤ ‖L K v‖ ^ 2) → 0 < C → (∀ K v, ‖L K v‖ ^ 2 ≤ C * ‖v‖ ^ 2) →
      ¬ ∃ μ : Measure H, IsProbabilityMeasure μ ∧
        ∀ f : H →ᵇ ℝ, Tendsto (fun K => ∫ x, f x ∂(embLaw e (L K))) atTop (𝓝 (∫ x, f x ∂μ))

/-- (i) Coherent truncations: `ι_K#(Π_K#μ) ⇀ μ` for every Borel probability `μ` (a Hilbert basis `e`). -/
def convref_coherent : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure H) [IsProbabilityMeasure μ] (b : HilbertBasis ℕ ℝ H),
      ∀ f : H →ᵇ ℝ, Tendsto (fun K => ∫ x, f x ∂((μ.map (truncK (fun k => b k) K)).map (embed (fun k => b k) K)))
        atTop (𝓝 (∫ x, f x ∂μ))

/-! #### R `thm:nullmass`(c) -/

/-- (c), generalised: if `μ ≪ γ` for a law `γ` whose coordinates along an orthonormal sequence are independent and
atomless, then `μ(D_α(μ)) = 0` (class (a) is `γ = μ`). -/
def nullmass_c : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (μ γ : Measure H) [IsProbabilityMeasure μ] [IsProbabilityMeasure γ] (e : ℕ → H) (α : ℝ),
    Orthonormal ℝ e → μ ≪ γ → iIndepFun (fun k (z : H) => ⟪e k, z⟫) γ →
    (∀ k, NullSingletonClass (γ.map fun z => ⟪e k, z⟫)) → 0 < α → α ≤ 1 / 2 →
      μ (depthRegion μ α) = 0

/-- (c) as printed, in the eigenbasis of the covariance: `μ ≪ γ`, `γ` Gaussian with injective covariance (independent
coordinates `N(m_k, λ_k)`, `λ_k > 0`). -/
def nullmass_c_gauss : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (μ γ : Measure H) [IsProbabilityMeasure μ] [IsProbabilityMeasure γ] (e : ℕ → H) (m : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (α : ℝ), Orthonormal ℝ e → μ ≪ γ → iIndepFun (fun k (z : H) => ⟪e k, z⟫) γ →
    (∀ k, γ.map (fun z => ⟪e k, z⟫) = gaussianReal (m k) (v k)) → (∀ k, v k ≠ 0) → 0 < α → α ≤ 1 / 2 →
      μ (depthRegion μ α) = 0

/-- (b) Elliptical laws: `Z = √W G` with `G` a centred Gaussian with injective covariance (in its eigenbasis: independent
coordinates `N(0, λ_k)`, `λ_k > 0`) and `W > 0` a.s. independent of `G` (no moment on `W`): `μ(D_α(μ)) = 0`. -/
def nullmass_b : Prop :=
  ∀ (H Ω : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [SecondCountableTopology H] [MeasurableSpace H]
    [BorelSpace H] [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (W : Ω → ℝ) (G : Ω → H)
    (e : ℕ → H) (v : ℕ → ℝ≥0) (α : ℝ),
    Measurable W → Measurable G → Orthonormal ℝ e → IndepFun W G Pr → (∀ᵐ ω ∂Pr, 0 < W ω) →
    iIndepFun (fun k ω => ⟪e k, G ω⟫) Pr → (∀ k, Pr.map (fun ω => ⟪e k, G ω⟫) = gaussianReal 0 (v k)) →
    (∀ k, v k ≠ 0) → 0 < α → α ≤ 1 / 2 →
      (Pr.map fun ω => Real.sqrt (W ω) • G ω) (depthRegion (Pr.map fun ω => Real.sqrt (W ω) • G ω) α) = 0

/-- `cor:uncertainty` for class (b): no Borel `A` with `μ(A) ≥ p > 0` has depth `≥ α` throughout. -/
def uncertainty_b : Prop :=
  ∀ (H Ω : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [SecondCountableTopology H] [MeasurableSpace H]
    [BorelSpace H] [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (W : Ω → ℝ) (G : Ω → H)
    (e : ℕ → H) (v : ℕ → ℝ≥0) (α p : ℝ),
    Measurable W → Measurable G → Orthonormal ℝ e → IndepFun W G Pr → (∀ᵐ ω ∂Pr, 0 < W ω) →
    iIndepFun (fun k ω => ⟪e k, G ω⟫) Pr → (∀ k, Pr.map (fun ω => ⟪e k, G ω⟫) = gaussianReal 0 (v k)) →
    (∀ k, v k ≠ 0) → 0 < p → p ≤ 1 → 0 < α → α ≤ 1 / 2 →
      ¬ ∃ A : Set H, MeasurableSet A ∧ ENNReal.ofReal p ≤ (Pr.map fun ω => Real.sqrt (W ω) • G ω) A ∧
        ∀ u ∈ A, ENNReal.ofReal α ≤ depthH (Pr.map fun ω => Real.sqrt (W ω) • G ω) u

/-- `cor:uncertainty` for class (c): no Borel `A` with `μ(A) ≥ p > 0` has depth `≥ α` throughout. -/
def uncertainty_c : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (μ γ : Measure H) [IsProbabilityMeasure μ] [IsProbabilityMeasure γ] (e : ℕ → H) (α p : ℝ),
    Orthonormal ℝ e → μ ≪ γ → iIndepFun (fun k (z : H) => ⟪e k, z⟫) γ →
    (∀ k, NullSingletonClass (γ.map fun z => ⟪e k, z⟫)) → 0 < p → p ≤ 1 → 0 < α → α ≤ 1 / 2 →
      ¬ ∃ A : Set H, MeasurableSet A ∧ ENNReal.ofReal p ≤ μ A ∧ ∀ u ∈ A, ENNReal.ofReal α ≤ depthH μ u

end Claims

end StatFormal.Wave23b
