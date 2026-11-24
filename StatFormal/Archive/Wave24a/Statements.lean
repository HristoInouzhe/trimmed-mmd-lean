import StatFormal.Archive.OTFD.Conformal.Statements
import StatFormal.Archive.OTFD.Wave1.Statements
import StatFormal.Archive.OTFD.Wave22b.Statements
import StatFormal.Archive.Wave23a.Statements
import StatFormal.Archive.OTFD.WaveL3.Statements
import StatFormal.Archive.OTFD.Wave8b.Statements
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Convex.Jensen
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Data.EReal.Basic

/-!
# FROZEN STATEMENTS — wave 24a (QUEUE rows 310–329): G `lem:randomisation`; B `prop:jensen`, `lem:lin-lipschitz`,
# `cor:band-saturation-limit`, `thm:consistency`, `prop:rk-paths`; TM `prop:sinkmono`, `lem:tcompact`; C
# `cor:conditional-uniform-x`, `lem:neural-law-to-map`; T `eq:basebridge`; A `prop:parsimony`, `cor:app-bijective-rate`,
# `cor:app-entropic-rate`, `thm:consistency`, `cor:app-hard-envelope`

Sources (verbatim in `lean-formalisation/inventory/extracted/{otfd-G_geodesic,otfd-B_bands,otfd-C_conditional,
otfd-T_tangent,otfd-A_sieves,trimmed-mmd}.md`; current text after the 2026-10-15 corrections, paths under
`research-lines/`):
* G `lem:randomisation` (`otfd/papers/G_geodesic/appendix.tex:260-272`, proof `:274-296`).
* B `prop:jensen` (`otfd/papers/B_bands/supplement.tex:6259-6268`, proof `:1749-1760`, soft depths `:6418-6427`);
  `lem:lin-lipschitz` (`:448-452`, proof `:454-465`; Lipschitz hypersurface `main.tex:429-431`, frozen `OTFD/Wave1`);
  `cor:band-saturation-limit` (`:4654-4666`, proof `:4668-4675`; `prop:band-saturation` from `:4574`);
  `thm:consistency` (`:6117-6150`, proof `:6168-6199`); `prop:rk-paths` (`:6586-6615`, proof `:5186-5204`,
  `def:rk-path` `main.tex:1077-1088`).
* TM `prop:sinkmono` (`trimmed-mmd/entropic.tex:144-153`, with `eq:trimset` `:59-66`, `eq:trimSink` `:126-133`);
  `lem:tcompact` (`trimmed-mmd/supplement.tex:166-187`).
* C `cor:conditional-uniform-x` (`otfd/papers/C_conditional/supplement.tex:2775-2785`, with
  `thm:conditional-band-limits` `main.tex:666-684`, frozen Wave 21b); `lem:neural-law-to-map` (`supplement.tex:1290-1311`,
  with `lem:neural-witness-ball` from `:2814`, frozen Wave 4).
* T `eq:basebridge` / `prop:base` (`otfd/papers/T_tangent/sec_tangent_theory.tex:641-661`, with `eq:L` of `lem:exp`,
  frozen Wave 22b).
* A `prop:parsimony` (`otfd/papers/A_sieves/main.tex:1330-1338`, proof `supplement.tex:5013-5016`; `prop:selector`
  `main.tex:1251-1266`, proof `supplement.tex:4960-4975`); `cor:app-bijective-rate` (`supplement.tex:2557-2582`, proof
  `:3886-3905`); `cor:app-entropic-rate` (`:2619-2642`, proof `:3913-3930`); `thm:consistency` (`:5078-5100`);
  `cor:app-hard-envelope` (`:5277-5285`, proof `:4075-4089`).
Imports the frozen `OTFD/Conformal` (`unif`), `OTFD/Wave1` (`IsLipHyp`, `PellClass`, `truncK`), `OTFD/Wave22b` (through it
`Wave21b` `supE`, `Wave17a` `hPop`, `Wave19a` `extTop`, `Wave12b` `Euc`, `OTFD/Wave2` `cappedSimplex`, `OTFD/Bands`
`simplex`; and `LengthBound`, `Lb`), `Wave23a` (`cdfK`, `cdfKInv`), `OTFD/WaveL3` (through it `WaveL1`
`LipNull`, `IsCMMapAE`) and `OTFD/Wave8b` (`embed`, `SubgradAt`, `OneSidedAt`, `IsOptAssign`, `IsEntPlan`, `entBary`;
through it `Wave6b` `empMeasure`) statements, not copied; Mathlib and Tau Ceti (`wassersteinEDist`, `subdifferential`)
otherwise.

Covered:
* `lem:randomisation`: `randomisation_full` (`P(p_𝒢 ≤ α) ≤ α`), `randomisation_mc` (`P(p ≤ α) ≤ α`), any finite group
  acting measurably on any measurable space (the frozen `prop:test` claims are the permutation-subgroup case).
* `prop:jensen`: `jensen` (`D^{bar,geom}_i ≥ D^{soft,geom}_i`).
* `prop:sinkmono`: `trimSet_mono` (`R_α(P) ⊆ R_{α'}(P)`), `sinkmono` (`α ↦ S_{ε,α}(P,Q)` nonincreasing on `[0,1)`, for
  every functional, as the proof remarks).
* `lem:tcompact`: `tcompact`.
* `lem:lin-lipschitz`: `lin_lipschitz`, `lin_lipschitz_pell` (`L#P ∈ 𝒫^ℓ ⟺ P ∈ 𝒫^ℓ`).
* `cor:band-saturation-limit`: `band_saturation_sandwich` (`x̂↑ ≤ x̄↑,sat ≤ x̄↑`).
* `cor:conditional-uniform-x`: `conditional_uniform_x_maps` (`sup_{x∈D₀} sup_S ‖T̂_{n,x} − Q_x‖ → 0` from
  `x`-uniform potential convergence and joint continuity), `conditional_uniform_x` (`eq:conditional-two-sided` with
  `sup_{x∈D₀}`).
* `eq:basebridge`: `basebridge` (abstract two-leg skeleton, below).
* `prop:parsimony`: `parsimony_tolerance` (`s_n ≤ 2R_Υ h + R_Υ(32h log(2/γ))^{1/2}`), `parsimony_tolerance_tendsto`
  (`→ 0`).
* `cor:app-bijective-rate` (a): `app_bijective_rate` (`B_n → 0 ⇒ E[n⁻¹Σ‖ι_{K_n}F̂(x_i) − 𝔽_P(X_i)‖²] → 0`, with
  `S(K_n) → 0` derived from the frozen `sieve_strong_limit_uncond`).
* `cor:app-entropic-rate`: `app_entropic_rate` (the displayed consistency under both joint conditions).
* A and B `thm:consistency`: `consistency_A` (uniform convergence of `1 − ‖F̂(Π_Kx)‖_{M_K}`), `consistency_B` (the
  deterministic bound `|D̂^geom − D^geom| ≤ c'_K‖F̂ − F‖` and uniform convergence of both depths), both CONDITIONAL on
  the uniform convergence of the semi-discrete maps on `𝒦` (Ghosal–Sen; the first display of B).
* `cor:app-hard-envelope`: `app_hard_envelope` (the envelope lemma).
* `prop:rk-paths`: `rk_paths_mono` ((i)), `rk_paths_labels` ((ii)), `rk_paths_consistency` ((iii), the
  `thm:band-consistency` case).
* `lem:neural-law-to-map`: `neural_law_to_map` (`W₁ ⇒ L²(μ_K)`), `neural_law_to_map_uniform` (uniform on `S`).

Not covered (declared):
* robust-equality paper 2 `prop:uniform` (`paper2/main.tex:269-273`): verbatim the JASA `prop:uniform` (same sets
  `B_s = 𝔹^𝒩(P̂_s; r_s)`, same `F̄`), already frozen and certified as `RobustEquality.Certificate.Claims.uniform`; a
  re-export would be a duplicate, so it is skipped (COVERAGE can point at the existing target).
* SB `prop:kernelexact` (`data-fairness-repair/schrodinger_bridge_fairness_repair.tex:702-707`): definitional (the
  time-1 marginal of a bridge with terminal marginal `ν` is `ν`); no statement with real content, skipped.
* A `prop:curse` (`A_sieves/main.tex:319-332`): far beyond its estimate — the population entropic barycentric map
  `F_{K,ε}` of general bounded laws, its plug-in estimator extended by the Schrödinger potentials, and Rigollet–Stromme
  Thm 4 for general laws are not formalised (only discrete Schrödinger systems exist, frozen Wave 23a); a faithful
  conditional would need all three objects. Skipped.
* C `prop:metric-uniform-localization` (`C_conditional/supplement.tex:728-763`): the substance is the uniform-in-
  `(Λ, s)` version of `thm:self-localization` (frozen Wave 22b only at a fixed metric), well beyond the estimate; the
  remaining "eventually in a compact set" bookkeeping alone would be near-tautological. Skipped.
* `prop:parsimony`: "the conclusions of `prop:selector`(ii) hold for `θ̃`" (needs `lem:T-stability` and
  `prop:selector`(ii), not formalised) and the interpretive last sentence.
* `cor:app-bijective-rate`: the sharper Minkowski display `{E…}^{1/2} ≤ √B_n + S(K_n)` (only the consequence
  `E_n ≤ 2B_n + 2S(K_n)² → 0` is proved), the transparent sufficient set, and (b) (`ass:app-grid-stability`).
  `cor:app-entropic-rate`: the transparent sufficient set.
* `thm:consistency` (A, B): Ghosal–Sen's theorem itself (hypothesis), B's whitening reduction to `M_K = I` (the
  hypothesis is the uniform convergence of the `M_K`-estimator), the rate-transfer remark.
* `cor:conditional-uniform-x`: deriving the `x`-uniform potential convergence from `W₁`-continuity of `x ↦ P_{K,x}`,
  common bounded support and `ass:conditional-oos` uniformly in `x` (hypothesis); the "satisfy these premises" sentence.
* `prop:rk-paths`: the strictness clause of (i) (needs `prop:band-injectivity`), the curve-space form, the shell variant
  of (iii) and the general-`M_K` case (whitening).
* `lem:neural-law-to-map`: deriving optimality of the population map from source absolute continuity alone (the
  population map is assumed to be a subgradient selection, as `Q_{K,x}` is).
* `cor:band-saturation-limit`: the limit half ("the tightened band converges uniformly in `t`") is not a new target: the
  frozen `Wave22b.cert_band_consistency` already bounds any edge `x` with `x̂↑ ≤ x ≤ supSub + slack`, so applied to
  `x̄^sat` (with `x̄^sat ≤ x̄ ≤ supSub + slack`) it is that frozen claim verbatim (critic: a draft `band_saturation_limit`
  was a restatement of it and was removed). Also not covered: the lower edge (the same statement with `−𝐞`);
  `thm:band-consistency-shell`.
* `eq:basebridge`: parallel transport, Jacobi fields and the differential `∂_σ Exp_{γ(σ)}(P_σ v)` themselves (the
  skeleton takes their integrated consequences as hypotheses); `prop:Cb`.

Encodings (to be checked by the critic):
* randomisation: `G` a finite group with a `MulAction` on `𝒲`, each translation measurable (equivalent to joint
  measurability for a finite discrete group); `W ∼ μ`, `gW =ᵈ W` is `μ.map (g • ·) = μ`; `g_1..g_B` i.i.d. uniform and
  independent of `W` is `μ ⊗ unif(𝒢)^{⊗B}` (frozen `unif`); upper bounds on the raw (outer-measure) event, as in the
  frozen `prop:test` claims; `α ∈ [0,1]`.
* jensen: any real vector space and any convex `g` (the three gauges are norms: generalisation); `p_{j|i} = π_ij/α_i`
  for any nonnegative `π` with row sums `α_i > 0` ("nothing uses `p` beyond being a probability vector").
* sinkmono: `R_α(P) = {Q prob. : Q ≪ P, dQ/dP ≤ 1/(1−α) P-a.e.}` (`rnDeriv`, `P` probability); the trimmed
  discrepancy is an `EReal` infimum over `R_α(P) × R_α(Q)` of an arbitrary `Δ` (in particular `S_ε`); no attainment.
* tcompact: `f` measurable with `|f| ≤ κ` (every `f ∈ B_H` under `ass:regularity`: generalisation); `R` any
  probability; `A(t) = t + (1−α)⁻¹∫(f − t)_+ dR`; attained at `t⋆ ∈ [−κ, κ]` is `∃ t ∈ Icc (−κ) κ, ∀ s, A t ≤ A s`.
* lin-lipschitz: any real inner product space and a continuous linear automorphism `L` (for `ℝ^K` every invertible
  matrix); hypersurfaces and `𝒫^ℓ` are the frozen `IsLipHyp`, `PellClass` (with its second-moment clause).
* band-saturation: weights `q(u)` of `Q̂(u) = Σ_j q_j(u)Z_j` in the frozen simplex, valid caps as hypotheses (certified
  in `prop:band-certificate`(iii), Bands2 `sat_cap_*`); the knapsack value is the `EReal` supremum over the frozen
  `cappedSimplex` (`⊥` if empty; nonempty here since `q(u)` is feasible); edges relative to `𝔪(t)`; `κ ∧ κ^sat` is `κ ⊓
  κsat`.
* uniform-x: `D₀` compact in a pseudometric space of queries; potentials `χ_x` with `HasGradientAt (χ x) (Q x u) u`
  on an open `O ⊇ cthickening r S`; joint continuity `ContinuousOn` on `O ×ˢ D₀`; fitted maps are subgradients of
  `g_{n,x}` tested on `cthickening r S` (weaker than global subgradients of convex `g_{n,x}`; convexity unused);
  "uniformly in `x`" is `∀ η > 0, ∀ᶠ n, ∀ x ∈ D₀, ∀ u ∈ cthickening r S, |g − χ| ≤ η`; levels, `E_K` as in Wave 21b.
* basebridge: `Ex_t`, `Exh_t : V → M` the exponentials at `m(t)`, `m̂(t)` (tangent spaces identified with `V`);
  `J_t` norm-preserving; the frozen `LengthBound Exh Dh` and `L_b = Lb Dh b`; the horizontal curve `Hc t x` from
  `Ex_t x` to `Exh_t(J_t x)` has `d(ends) ≤ ∫₀¹ spd`, `spd ≤ C_b · |γ_t'|` for `‖x‖ ≤ b` (definition of `C_b`) and
  `∫₀¹ |γ_t'| = d(m(t), m̂(t))` (minimising geodesic); `C_b` finite (`ℝ≥0`); `D_∞` is `⨆_t edist` in `ℝ≥0∞`.
* parsimony: the `n_v + m_v` reference draws are `Υ(U_k)`, `U ∼ μ` i.i.d. (`Measure.pi` over `Fin n_v ⊕ Fin m_v`),
  `‖Υ‖ ≤ R` everywhere; `D̂` the V-statistic of `prop:selector` (`edVstat`); the upper `γ`-quantile is
  `inf{s : P(D̂ > s) ≤ γ}` (`upperQuantile`; nonempty and bounded below, `|D̂| ≤ 4R`); `n_v, m_v ≥ 1`, `0 < γ < 1`.
* sieve rates: `H` separable Hilbert, `(e_k)` a complete orthonormal system (`⊤ ≤` closure of the span); `𝒫^ℓ(H)` is
  `LipNull` plus `∫‖x‖² dP < ∞`; the coherent reference `μ` is carried by `B̄(0, M)`; `𝔽_P = F` and `F_{+,K} = FK K`
  are encoded as in the frozen `sieve_strong_limit_uncond` (cyclically monotone pushforwards); data are a triangular
  array `X n : Fin n → Ω → H`, independent with law `P` within each row (generalisation of one i.i.d. sequence);
  `x_i = Π_{K_n}X_i` (frozen `truncK`), `σ²_{K} = ∫‖z‖² dP_K`; `ass:app-weak-conditioning` along `K_n` is the frozen
  `SubgradAt`/`OneSidedAt` a.s. with `α_n, β_n` (as in `emp_bijective_weak`, `app_entropic_weak`); `B_n` and the joint
  conditions are stated in `ℝ≥0∞` with `ENNReal.ofReal` of the nonnegative real factors (a `W₂ = ∞` is never truncated);
  the conclusion is the lower integral of `ENNReal.ofReal(n⁻¹Σ‖ι_{K_n}F̂(x_i) − 𝔽_P(X_i)‖²)` (no measurability of the
  fitted maps needed, as in the frozen cores).
* consistency: `F̂_n(ω)`, `F` arbitrary maps on a normed space `E` (`ℝ^K`), `Π_K` an arbitrary map from the curve space;
  Ghosal–Sen's conclusion is `∀ᵐ ω, TendstoUniformlyOn (F̂_n ω) F atTop 𝒦`; A's `‖u‖_{M_K} = ‖Lu‖` (`L` continuous
  linear); B's gauge `g` subadditive, symmetric, `g ≤ c'‖·‖` (the norms `g_K`, `c'_K = max_{‖u‖=1} g_K(u)`), `c_K`
  continuous on `ℝ`, `g(F z) ≤ 1` on `𝒦` (`F` maps into `𝒰_K ⊆ {g ≤ 1}`); uniform convergence of depths is
  `TendstoUniformlyOn` on `{x : Π_K x ∈ 𝒦}`; the `ϖ_K` bound is replaced by its consequence (uniform continuity of `c_K`).
* envelope: `A_K(n)` and `S(K)` arbitrary real sequences with `A_K(n) → 0` for each `K` and `S(K) → 0`; the error
  `e(n,K) ∈ [0, A_K(n) + S(K)]` (step 2 of `thm:app-hard-diagonal`, Minkowski, as a hypothesis); `K*` depends only on
  `A`; schedules `K_n → ∞` with `K_n ≤ K*_n` eventually.
* rk-paths: (i) the frozen `prop:band-boundary` setting (`M` positive definite, `T(u) ∈ ½M⁻¹∂ψ(u)`), `p ↦ τ_p`
  nondecreasing on `𝒫_v`, `⟨v, ·⟩_M = (Mv) ⬝ᵥ ·`; (ii) `F(Q(z)) = z` on `int 𝒰_K` (the homeomorphism hypothesis, only
  its left-inverse half is used), `ρ` positively homogeneous with `ρ(v) = 1` (`v ∈ 𝕊_K`), `τ_{K,p} = cdfKInv`,
  probability depth `1 − c_K(ρ(F(·)))`, sign `F(·)/ρ(F(·))`; (iii) the hypotheses of the frozen `band_consistency`
  with the population map `∇χ` (everywhere on `O`, the continuous representative) and `𝒫_w`, `𝕊_K` arbitrary with
  `τ_p w ∈ A_{K,1−δ}`; data-driven directions `v̂_n → v` with `τ_p v̂_n ∈ A_{K,1−δ}` and bounded `τ`.
* neural-law-to-map: `μ_K ≪ Leb` on `ℝ^K` with finite second moment (compact support in the paper); convex-gradient
  maps are `μ_K`-a.e. selections of Tau Ceti `subdifferential`s of arbitrary `φ_n : ℝ^K → EReal` (convexity is
  automatic for a subgradient selection's optimality); the target `P_{K,x} = Q#μ_K` with `Q` such a selection; values in a
  common ball `‖·‖ ≤ R` everywhere; `W₁` is Tau Ceti's `wassersteinEDist 1` (`ℝ≥0∞`); the uniform part takes `O` open
  with `S ⊆ O ⊆ supp μ_K`, `Q` continuous on `O`, and subgradients at every point of `O`.

Critic notes:
* All 24 claims are proved in `Wave24a/Route{Random,Small,Tcompact,Consistency,LinLip,BandSat,UniformX,Neural,RkPaths,
  Parsimony,Basebridge,SieveRate}.lean` (foundations used: propext, Classical.choice, Quot.sound). Routes reuse the library
  `Foundations/Exchangeable` (`grp_test_valid`, `mc_test_valid`), `Foundations/OTLimits`
  (`tendsto_lintegral_brenierMap_sub_sq`), Tau Ceti's McDiarmid and Knott–Smith direction, and the certified frozen
  `Wave22b.continuousAt_gradient`, `exp_pointwise`, `Wave21b.cond_band_two_sided`,
  `Wave4.neural_witness_ball`, `Bands.band_boundary_mono`, `Wave19a.subgrad_conv_unif`, `Wave23a.cdfK_inv_spec`,
  `Wave8b.emp_bijective_weak`, `app_entropic_weak`, `Wave6b.empirical_wass_rate20`, `WaveL3.sieve_strong_limit_uncond`.
* CONDITIONAL claims: `consistency_A`, `consistency_B` (Ghosal–Sen's uniform convergence, a property of the given
  estimator sequence, exactly the first display of B's corollary). The premise is uniform convergence on the one given
  set `𝒦` only; Ghosal–Sen Thm 4.1 (as restated in A `thm:app-ghosalsen-rate`) gives it for every compact
  `𝒦 ⊂ int 𝒴_K`, which is how the paper uses it (uniformity on all of `ℝ^K` would need their part (c), a truncated
  estimator and strictly convex `S_K`, and is never assumed). `conditional_uniform_x*` take the `x`-uniform potential
  convergence as a hypothesis, again only on the compact `S_r ⊆ O` (the uniform-in-`x` version of the first conclusion
  of `thm:conditional-band-limits`, which is on compacts of `int 𝒰_K`).
* Light claims (content mostly in a frozen result or elementary), reviewed by the critic: `rk_paths_mono` (frozen
  `band_boundary_mono` at `u = 0`, `v ↦ Mv`, with `M⁻¹Mv = v` and composed with `τ`; its conclusion is not an instance
  of the frozen one), `trimSet_mono`/`sinkmono` (the paper's whole proof), `jensen` (finite Jensen), `consistency_A`
  (Lipschitz composition of uniform convergence, pulled back along `Π_K`). Each is the printed statement and none
  restates a hypothesis or a frozen claim. The draft's `band_saturation_limit` did (an instance of the frozen
  `cert_band_consistency` with a weakened hypothesis) and was removed.
* No statement was found false. Observations: (1) `prop:parsimony`'s bound holds with the one-sided McDiarmid tail
  (`P(D̂ > Δ) ≤ γ/2`), so `log(2/γ)` could be `log(1/γ)`; the printed bound is correct. (2) `prop:selector`(i)'s
  bounded differences are `8R/n_v`, `8R/m_v` as printed (the proof's `2(n_v − 1)·2R/n_v²` is replaced by the cruder
  `4R/n_v` without changing the constant). (3) `cor:conditional-uniform-x` needs no convexity of the fitted potentials
  once the fitted maps are subgradients near `S`; the `x`-uniform bound is quantitative: `‖ξ − Q_x(u)‖ ≤ ε + 2η/h`.
  (4) `lem:neural-law-to-map`'s uniform part needs `S` inside the interior of `supp μ_K` (the witness balls must have
  positive mass), which "interior compact" provides. (5) `lem:lin-lipschitz` holds in any real inner product space for
  continuous linear automorphisms, with the explicit graph function `g(x) = ⟨L y(x), w⟩/‖w‖² + τ(y(x))`,
  `y = P_ν ∘ L⁻¹`.

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset Matrix
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave24a

/-! ### G `lem:randomisation` -/

/-- The whole-group `p`-value `p_𝒢(w) = #{g ∈ 𝒢 : T(gw) ≥ T(w)}/|𝒢|`. -/
def grpPvalue (G : Type*) {𝒲 : Type*} [Group G] [Fintype G] [MulAction G 𝒲] (T : 𝒲 → ℝ) (w : 𝒲) : ℝ :=
  ((Finset.univ.filter fun g : G => T w ≤ T (g • w)).card : ℝ) / Fintype.card G

/-- The Monte Carlo `p`-value `p = (1 + #{b ≤ B : T(g_b w) ≥ T(w)})/(B + 1)`. -/
def mcPvalue {G 𝒲 : Type*} [Group G] [MulAction G 𝒲] {B : ℕ} (T : 𝒲 → ℝ) (w : 𝒲) (g : Fin B → G) : ℝ :=
  (1 + ((Finset.univ.filter fun b : Fin B => T w ≤ T (g b • w)).card : ℝ)) / (B + 1)

/-! ### B `prop:jensen` -/

/-! ### TM `prop:sinkmono` -/

/-- The trimming set `R_α(P) = {Q ≪ P probability : dQ/dP ≤ 1/(1 − α) P-a.s.}` (`eq:trimset`). -/
def trimSet {X : Type*} [MeasurableSpace X] (α : ℝ) (P : Measure X) : Set (Measure X) :=
  {Q | IsProbabilityMeasure Q ∧ Q ≪ P ∧ ∀ᵐ x ∂P, Q.rnDeriv P x ≤ ENNReal.ofReal (1 / (1 - α))}

/-- The trimmed discrepancy `Δ_α(P, Q) = inf{Δ(P', Q') : P' ∈ R_α(P), Q' ∈ R_α(Q)}` (`eq:trimSink` for
`Δ = S_ε`), in `EReal`. -/
def trimmedDisc {X : Type*} [MeasurableSpace X] (Δ : Measure X → Measure X → EReal) (α : ℝ) (P Q : Measure X) :
    EReal :=
  ⨅ P' ∈ trimSet α P, ⨅ Q' ∈ trimSet α Q, Δ P' Q'

/-! ### TM `lem:tcompact` -/

/-- `A(t) = t + (1 − α)⁻¹ E_R[(f(X) − t)_+]` (`eq:cvar`). -/
def cvarObj {X : Type*} [MeasurableSpace X] (R : Measure X) (α : ℝ) (f : X → ℝ) (t : ℝ) : ℝ :=
  t + (1 - α)⁻¹ * ∫ x, max (f x - t) 0 ∂R

/-! ### B `cor:band-saturation-limit` -/

/-- The knapsack value `max{Σ_j q_j c_j : q ∈ 𝒫_κ}` of `prop:band-certificate`(iv) (relative to `𝔪(t)`, with
`c_j = ⟨𝐞(t), Z_j⟩`), over the frozen capped simplex `𝒫_κ = {q ∈ Δ_n : q ≤ κ}`, in `EReal` (`⊥` if `𝒫_κ = ∅`). -/
def knapVal {n : ℕ} (κ c : Fin n → ℝ) : EReal :=
  ⨆ q ∈ StatFormal.OTFD.Wave2.cappedSimplex κ, ((∑ j, q j * c j : ℝ) : EReal)

/-! ### A `prop:parsimony` -/

/-- The energy-distance V-statistic `D̂ = 2/(nm) Σ_{i,j} ‖a_i − b_j‖ − n⁻² Σ_{i,i'} ‖a_i − a_{i'}‖ − m⁻² Σ_{j,j'} ‖b_j −
b_{j'}‖` of `prop:selector`. -/
def edVstat {E : Type*} [NormedAddCommGroup E] {n m : ℕ} (a : Fin n → E) (b : Fin m → E) : ℝ :=
  2 / ((n : ℝ) * m) * ∑ i, ∑ j, ‖a i - b j‖ - 1 / (n : ℝ) ^ 2 * ∑ i, ∑ i', ‖a i - a i'‖ -
    1 / (m : ℝ) ^ 2 * ∑ j, ∑ j', ‖b j - b j'‖

/-- The upper `γ`-quantile `inf{s : P(X > s) ≤ γ}` of a real statistic. -/
def upperQuantile {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) (γ : ℝ) : ℝ :=
  sInf {s : ℝ | P {ω | s < X ω} ≤ ENNReal.ofReal γ}

/-- The reference-only tolerance bound `2Rh + R(32h log(2/γ))^{1/2}`, `h = n_v⁻¹ + m_v⁻¹`. -/
def parsBound (R γ : ℝ) (nv mv : ℕ) : ℝ :=
  2 * R * (1 / (nv : ℝ) + 1 / (mv : ℝ)) + R * √(32 * (1 / (nv : ℝ) + 1 / (mv : ℝ)) * Real.log (2 / γ))

namespace Claims

/-! #### G `lem:randomisation` -/

/-- Complete enumeration: for a finite group acting measurably on `𝒲` and a `𝒢`-invariant law `μ` of `W`,
`P(p_𝒢 ≤ α) ≤ α` for every `α ∈ [0,1]`. -/
def randomisation_full : Prop :=
  ∀ (G 𝒲 : Type) [Group G] [Fintype G] [MulAction G 𝒲] [MeasurableSpace 𝒲] (μ : Measure 𝒲)
    [IsProbabilityMeasure μ] (T : 𝒲 → ℝ),
    (∀ g : G, Measurable fun w : 𝒲 => g • w) → (∀ g : G, μ.map (fun w : 𝒲 => g • w) = μ) → Measurable T →
      ∀ α : ℝ, 0 ≤ α → α ≤ 1 → μ {w | grpPvalue G T w ≤ α} ≤ ENNReal.ofReal α

/-- Monte Carlo: with `g_1, …, g_B` i.i.d. uniform on `𝒢` and independent of `W`, `P(p ≤ α) ≤ α` for every
`α ∈ [0,1]`. -/
def randomisation_mc : Prop :=
  ∀ (G 𝒲 : Type) [Group G] [Fintype G] [MeasurableSpace G] [MeasurableSingletonClass G] [MulAction G 𝒲]
    [MeasurableSpace 𝒲] (μ : Measure 𝒲) [IsProbabilityMeasure μ] (T : 𝒲 → ℝ) (B : ℕ),
    (∀ g : G, Measurable fun w : 𝒲 => g • w) → (∀ g : G, μ.map (fun w : 𝒲 => g • w) = μ) → Measurable T →
      ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
        (μ.prod (Measure.pi fun _ : Fin B => StatFormal.OTFD.Conformal.unif G)) {z | mcPvalue T z.1 z.2 ≤ α}
          ≤ ENNReal.ofReal α

/-! #### B `prop:jensen` -/

/-- `D^{bar,geom}_i ≥ D^{soft,geom}_i`: with conditional weights `p_{j|i} = π_ij/α_i` of any nonnegative plan with row
sums `α_i > 0`, and any convex gauge `g`, `1 − Σ_j p_{j|i} g(u_j) ≤ 1 − g(Σ_j p_{j|i} u_j)`. -/
def jensen : Prop :=
  ∀ (E : Type) [AddCommGroup E] [Module ℝ E] (n m : ℕ) (g : E → ℝ) (π : Fin n → Fin m → ℝ) (α : Fin n → ℝ)
    (u : Fin m → E),
    ConvexOn ℝ univ g → (∀ i j, 0 ≤ π i j) → (∀ i, ∑ j, π i j = α i) → (∀ i, 0 < α i) →
      ∀ i, 1 - ∑ j, π i j / α i * g (u j) ≤ 1 - g (∑ j, (π i j / α i) • u j)

/-! #### TM `prop:sinkmono` -/

/-- The trimming sets are nested: `R_α(P) ⊆ R_{α'}(P)` for `0 ≤ α ≤ α' < 1`. -/
def trimSet_mono : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (P : Measure X) (α α' : ℝ), 0 ≤ α → α ≤ α' → α' < 1 →
    trimSet α P ⊆ trimSet α' P

/-- `α ↦ Δ_α(P, Q)` is nonincreasing on `[0,1)`, for every functional `Δ` (in particular `S_ε`) and all probability
laws `P, Q`. -/
def sinkmono : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (Δ : Measure X → Measure X → EReal) (P Q : Measure X),
    IsProbabilityMeasure P → IsProbabilityMeasure Q → AntitoneOn (fun α => trimmedDisc Δ α P Q) (Ico 0 1)

/-! #### TM `lem:tcompact` -/

/-- For every measurable `f` with `|f| ≤ κ` (in particular every `f ∈ B_H` under `ass:regularity`), every probability
law `R` and `α ∈ [0,1)`, the infimum of `A(t) = t + (1 − α)⁻¹ E_R[(f − t)_+]` over `t ∈ ℝ` is attained at some
`t⋆ ∈ [−κ, κ]`. -/
def tcompact : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (R : Measure X) [IsProbabilityMeasure R] (f : X → ℝ) (κ α : ℝ),
    Measurable f → (∀ x, |f x| ≤ κ) → 0 ≤ α → α < 1 →
      ∃ t ∈ Icc (-κ) κ, ∀ s : ℝ, cvarObj R α f t ≤ cvarObj R α f s

/-! #### A `cor:app-hard-envelope` -/

/-- The envelope lemma: if `A_K(n) → 0` as `n → ∞` for every `K` and `S(K) → 0`, there is a nondecreasing `K*_n → ∞`
such that every error `e(n, K) ∈ [0, A_K(n) + S(K)]` tends to `0` along every `K_n → ∞` with `K_n ≤ K*_n`
eventually, monotone or not. -/
def app_hard_envelope : Prop :=
  ∀ (A : ℕ → ℕ → ℝ) (S : ℕ → ℝ), (∀ K, Tendsto (A K) atTop (𝓝 0)) → Tendsto S atTop (𝓝 0) →
    ∃ Kstar : ℕ → ℕ, Monotone Kstar ∧ Tendsto Kstar atTop atTop ∧
      ∀ (e : ℕ → ℕ → ℝ) (Kn : ℕ → ℕ), (∀ n K, 0 ≤ e n K) → (∀ n K, e n K ≤ A K n + S K) →
        Tendsto Kn atTop atTop → (∀ᶠ n in atTop, Kn n ≤ Kstar n) → Tendsto (fun n => e n (Kn n)) atTop (𝓝 0)

/-! #### A and B `thm:consistency` -/

/-- A: if the semi-discrete maps converge to `F_{+,K}` uniformly on a compact `𝒦` almost surely (the conclusion of
Ghosal–Sen, `thm:app-ghosalsen-rate`), the depths `1 − ‖F̂(Π_K x)‖_{M_K}` (`‖u‖_{M_K} = ‖L u‖`) converge to
`1 − ‖F(Π_K x)‖_{M_K}` almost surely, uniformly over `{x : Π_K x ∈ 𝒦}`. -/
def consistency_A : Prop :=
  ∀ (Ω E H : Type) [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E] (P : Measure Ω)
    (PiK : H → E) (L : E →L[ℝ] E) (F : E → E) (Fh : ℕ → Ω → E → E) (𝒦 : Set E),
    (∀ᵐ ω ∂P, TendstoUniformlyOn (fun n => Fh n ω) F atTop 𝒦) →
      ∀ᵐ ω ∂P, TendstoUniformlyOn (fun n x => 1 - ‖L (Fh n ω (PiK x))‖) (fun x => 1 - ‖L (F (PiK x))‖) atTop
        {x | PiK x ∈ 𝒦}

/-- B: for a gauge `g` (subadditive, symmetric, `g ≤ c'‖·‖₂`) and a continuous CDF `c_K`, with `F` valued in the unit
gauge ball on `𝒦`: deterministically `|D̂^geom − D^geom| ≤ c'‖F̂ − F‖` at every point, and if `F̂ → F` uniformly on
`𝒦` almost surely, both `D̂^geom = 1 − g(F̂(Π_K x))` and `D̂^prob = 1 − c_K(g(F̂(Π_K x)))` converge almost surely,
uniformly over `{x : Π_K x ∈ 𝒦}`. -/
def consistency_B : Prop :=
  ∀ (Ω E H : Type) [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E] (P : Measure Ω)
    (PiK : H → E) (g : E → ℝ) (cK : ℝ → ℝ) (c' : ℝ) (F : E → E) (Fh : ℕ → Ω → E → E) (𝒦 : Set E),
    (∀ a b, g (a + b) ≤ g a + g b) → (∀ a, g (-a) = g a) → (∀ a, g a ≤ c' * ‖a‖) → Continuous cK →
    (∀ z ∈ 𝒦, g (F z) ≤ 1) →
      (∀ n ω x, |(1 - g (Fh n ω (PiK x))) - (1 - g (F (PiK x)))| ≤ c' * ‖Fh n ω (PiK x) - F (PiK x)‖) ∧
      ((∀ᵐ ω ∂P, TendstoUniformlyOn (fun n => Fh n ω) F atTop 𝒦) →
        ∀ᵐ ω ∂P, TendstoUniformlyOn (fun n x => 1 - g (Fh n ω (PiK x))) (fun x => 1 - g (F (PiK x))) atTop
            {x | PiK x ∈ 𝒦} ∧
          TendstoUniformlyOn (fun n x => 1 - cK (g (Fh n ω (PiK x)))) (fun x => 1 - cK (g (F (PiK x)))) atTop
            {x | PiK x ∈ 𝒦})

/-! #### B `lem:lin-lipschitz` -/

/-- If `L` is a (continuous) linear automorphism and `Γ` a Lipschitz hypersurface, so is `LΓ`. -/
def lin_lipschitz : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (L : H ≃L[ℝ] H) (Γ : Set H),
    StatFormal.OTFD.Wave1.IsLipHyp Γ → StatFormal.OTFD.Wave1.IsLipHyp (L '' Γ)

/-- Consequently `L#P ∈ 𝒫^ℓ` if and only if `P ∈ 𝒫^ℓ` (frozen `PellClass`: probability, finite second moment, null on
every Lipschitz hypersurface). -/
def lin_lipschitz_pell : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H] (L : H ≃L[ℝ] H)
    (P : Measure H), StatFormal.OTFD.Wave1.PellClass (P.map L) ↔ StatFormal.OTFD.Wave1.PellClass P

/-! #### B `cor:band-saturation-limit` -/

/-- The sandwich `x̂↑ ≤ x̄↑,sat ≤ x̄↑` (relative to `𝔪(t)`): if the fitted weights `q(u)` of `Q̂(u) = Σ_j q_j(u) Z_j`
lie in the simplex and below both caps `κ` and `κ^sat` on `A` (validity, `prop:band-certificate`(iii) and
`prop:band-saturation`), the fitted edge `sup_{u∈A} ⟨v, Q̂(u)⟩` is at most the knapsack value with caps `κ ∧ κ^sat`,
which is at most the knapsack value with caps `κ`. -/
def band_saturation_sandwich : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n : ℕ) (Z : Fin n → E) (q : E → Fin n → ℝ)
    (A : Set E) (κ κsat : Fin n → ℝ) (v : E),
    (∀ u ∈ A, q u ∈ StatFormal.OTFD.Bands.simplex n) → (∀ u ∈ A, ∀ j, q u j ≤ κ j) →
    (∀ u ∈ A, ∀ j, q u j ≤ κsat j) →
      (⨆ u ∈ A, ((⟪v, ∑ j, q u j • Z j⟫ : ℝ) : EReal)) ≤ knapVal (κ ⊓ κsat) (fun j => ⟪v, Z j⟫) ∧
        knapVal (κ ⊓ κsat) (fun j => ⟪v, Z j⟫) ≤ knapVal κ (fun j => ⟪v, Z j⟫)

/-! #### C `cor:conditional-uniform-x` -/

/-- Uniformity in the query, maps: on a compact query set `D₀`, with population potentials `χ_x` differentiable on an
open `O ⊇ S_r = cthickening r S` (`S` compact, `r > 0`) with gradient `Q_x`, `(u, x) ↦ Q_x(u)` jointly continuous on
`O × D₀`, fitted maps `T_{n,x}(u)` subgradients of `g_{n,x}` (tested on `S_r`) at every `u ∈ S`, and
`sup_{x∈D₀} sup_{S_r} |g_{n,x} − χ_x| → 0`: then `sup_{x∈D₀} sup_{u∈S} ‖T_{n,x}(u) − Q_x(u)‖ → 0`. -/
def conditional_uniform_x_maps : Prop :=
  ∀ (K : ℕ) (X : Type) [PseudoMetricSpace X] (D0 : Set X) (S O : Set (StatFormal.Wave12b.Euc K)) (r : ℝ)
    (χ : X → StatFormal.Wave12b.Euc K → ℝ) (Q : X → StatFormal.Wave12b.Euc K → StatFormal.Wave12b.Euc K)
    (g : ℕ → X → StatFormal.Wave12b.Euc K → ℝ) (T : ℕ → X → StatFormal.Wave12b.Euc K → StatFormal.Wave12b.Euc K),
    IsCompact D0 → IsCompact S → 0 < r → IsOpen O → Metric.cthickening r S ⊆ O →
    (∀ x ∈ D0, ∀ u ∈ O, HasGradientAt (χ x) (Q x u) u) → ContinuousOn (fun p => Q p.2 p.1) (O ×ˢ D0) →
    (∀ n, ∀ x ∈ D0, ∀ u ∈ S, ∀ y ∈ Metric.cthickening r S, g n x u + ⟪T n x u, y - u⟫ ≤ g n x y) →
    (∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ x ∈ D0, ∀ u ∈ Metric.cthickening r S, |g n x u - χ x u| ≤ η) →
      ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ x ∈ D0, ∀ u ∈ S, ‖T n x u - Q x u‖ ≤ η

/-- Uniformity in the query, bands: under the premises of `conditional_uniform_x_maps`, with the frozen level regions
`A_p ⊆ S` (`0 < p ≤ 1 − δ`, compact convex with interior, in `supp μ_K`), every band edge is eventually within `η` of
the population edge, uniformly in `x ∈ D₀`, `p` and `t` (`eq:conditional-two-sided` with `sup_{x∈D₀}`). -/
def conditional_uniform_x : Prop :=
  ∀ (K : ℕ) (X 𝒯 : Type) [PseudoMetricSpace X] (D0 : Set X) (μ : Measure (StatFormal.Wave12b.Euc K))
    (A : ℝ → Set (StatFormal.Wave12b.Euc K)) (S O : Set (StatFormal.Wave12b.Euc K)) (r δ EK : ℝ)
    (χ : X → StatFormal.Wave12b.Euc K → ℝ) (Q : X → StatFormal.Wave12b.Euc K → StatFormal.Wave12b.Euc K)
    (g : ℕ → X → StatFormal.Wave12b.Euc K → ℝ) (T : ℕ → X → StatFormal.Wave12b.Euc K → StatFormal.Wave12b.Euc K)
    (e : 𝒯 → StatFormal.Wave12b.Euc K),
    IsCompact D0 → IsCompact S → 0 < r → IsOpen O → Metric.cthickening r S ⊆ O →
    (∀ x ∈ D0, ∀ u ∈ O, HasGradientAt (χ x) (Q x u) u) → ContinuousOn (fun p => Q p.2 p.1) (O ×ˢ D0) →
    (∀ n, ∀ x ∈ D0, ∀ u ∈ S, ∀ y ∈ Metric.cthickening r S, g n x u + ⟪T n x u, y - u⟫ ≤ g n x y) →
    (∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ x ∈ D0, ∀ u ∈ Metric.cthickening r S, |g n x u - χ x u| ≤ η) →
    (∀ t, ‖e t‖ ≤ EK) →
    (∀ p, 0 < p → p ≤ 1 - δ → IsCompact (A p) ∧ Convex ℝ (A p) ∧ (interior (A p)).Nonempty ∧
      A p ⊆ μ.support ∧ A p ⊆ S) →
      ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ x ∈ D0, ∀ p, 0 < p → p ≤ 1 - δ → ∀ t,
        ∀ v ∈ ({e t, -e t} : Set (StatFormal.Wave12b.Euc K)),
          ∃ a b : ℝ, StatFormal.Wave17a.hPop μ (A p) (Q x) v = a ∧ StatFormal.Wave21b.supE (A p) (T n x) v = b ∧
            |b - a| ≤ η

/-! #### C `lem:neural-law-to-map` -/

/-- Proper predictive laws determine the convex transport: for a source `μ_K ≪ Leb` with finite second moment, maps
`T_n` that are `μ_K`-a.e. subgradients of functions `φ_n` (convex-gradient maps) with values in a common ball, and a
population map `Q` that is a `μ_K`-a.e. subgradient of some `ψ` with values in that ball, `W₁(T_n#μ_K, Q#μ_K) → 0`
implies `∫ ‖T_n − Q‖² dμ_K → 0`. -/
def neural_law_to_map : Prop :=
  ∀ (K : ℕ) (μ : Measure (StatFormal.Wave12b.Euc K)) [IsProbabilityMeasure μ]
    (T : ℕ → StatFormal.Wave12b.Euc K → StatFormal.Wave12b.Euc K) (Q : StatFormal.Wave12b.Euc K → StatFormal.Wave12b.Euc K)
    (φ : ℕ → StatFormal.Wave12b.Euc K → EReal) (ψ : StatFormal.Wave12b.Euc K → EReal) (R : ℝ),
    μ ≪ volume → ∫⁻ u, ‖u‖ₑ ^ 2 ∂μ < ⊤ → (∀ n, Measurable (T n)) → Measurable Q →
    (∀ n, ∀ᵐ u ∂μ, T n u ∈ TauCeti.subdifferential (innerₗ (StatFormal.Wave12b.Euc K)) (φ n) u) →
    (∀ᵐ u ∂μ, Q u ∈ TauCeti.subdifferential (innerₗ (StatFormal.Wave12b.Euc K)) ψ u) →
    (∀ n u, ‖T n u‖ ≤ R) → (∀ u, ‖Q u‖ ≤ R) →
    Tendsto (fun n => TauCeti.wassersteinEDist 1 (μ.map (T n)) (μ.map Q)) atTop (𝓝 0) →
      Tendsto (fun n => ∫⁻ u, ‖T n u - Q u‖ₑ ^ 2 ∂μ) atTop (𝓝 0)

/-- The uniform upgrade: if moreover `Q` is continuous on an open `O ⊆ supp μ_K` containing the compact `S`, and each
`T_n` is a subgradient of `φ_n` at every point of `O`, then `T_n → Q` uniformly on `S`. -/
def neural_law_to_map_uniform : Prop :=
  ∀ (K : ℕ) (μ : Measure (StatFormal.Wave12b.Euc K)) [IsProbabilityMeasure μ]
    (T : ℕ → StatFormal.Wave12b.Euc K → StatFormal.Wave12b.Euc K) (Q : StatFormal.Wave12b.Euc K → StatFormal.Wave12b.Euc K)
    (φ : ℕ → StatFormal.Wave12b.Euc K → EReal) (ψ : StatFormal.Wave12b.Euc K → EReal) (R : ℝ)
    (S O : Set (StatFormal.Wave12b.Euc K)),
    μ ≪ volume → ∫⁻ u, ‖u‖ₑ ^ 2 ∂μ < ⊤ → (∀ n, Measurable (T n)) → Measurable Q →
    (∀ n, ∀ᵐ u ∂μ, T n u ∈ TauCeti.subdifferential (innerₗ (StatFormal.Wave12b.Euc K)) (φ n) u) →
    (∀ᵐ u ∂μ, Q u ∈ TauCeti.subdifferential (innerₗ (StatFormal.Wave12b.Euc K)) ψ u) →
    (∀ n u, ‖T n u‖ ≤ R) → (∀ u, ‖Q u‖ ≤ R) →
    Tendsto (fun n => TauCeti.wassersteinEDist 1 (μ.map (T n)) (μ.map Q)) atTop (𝓝 0) →
    IsCompact S → IsOpen O → S ⊆ O → O ⊆ μ.support → ContinuousOn Q O →
    (∀ n, ∀ u ∈ O, T n u ∈ TauCeti.subdifferential (innerₗ (StatFormal.Wave12b.Euc K)) (φ n) u) →
      TendstoUniformlyOn T Q atTop S

/-! #### B `prop:rk-paths` -/

/-- (i) Monotone in their own direction: for any selection `T(u) ∈ ½M⁻¹∂ψ(u)` of a convex `ψ` (the frozen form of
`prop:band-boundary`) and any nondecreasing level-to-radius map `p ↦ τ_p` on `𝒫_v`, `p ↦ ⟨v, T(τ_p v)⟩_M =
(Mv) · T(τ_p v)` is nondecreasing on `𝒫_v`. -/
def rk_paths_mono : Prop :=
  ∀ (K : ℕ) (M : Matrix (Fin K) (Fin K) ℝ) (ψ : (Fin K → ℝ) → ℝ) (T : (Fin K → ℝ) → Fin K → ℝ) (v : Fin K → ℝ)
    (τ : ℝ → ℝ) (Pv : Set ℝ),
    M.PosDef → ConvexOn ℝ Set.univ ψ → (∀ u y, ψ u + (2 • (M *ᵥ T u)) ⬝ᵥ (y - u) ≤ ψ y) → MonotoneOn τ Pv →
      MonotoneOn (fun p => (M *ᵥ v) ⬝ᵥ T (τ p • v)) Pv

/-- (ii) Exact level labels: if `F(Q(z)) = z` on `int U_K`, the gauge `ρ` is positively homogeneous with `ρ(v) = 1`
and `c_K` is continuous on `[0,1]` with `c_K(0) = 0`, `c_K(1) = 1`, then for `0 < p ≤ 1` with `τ_{K,p} v ∈ int U_K`
(`τ_{K,p} = c_K^{-1}(p)`, frozen `cdfKInv`), the point `Q(τ_{K,p} v)` has probability depth `1 − c_K(ρ(F(·))) = 1 − p`
and sign `F(·)/ρ(F(·)) = v`. -/
def rk_paths_labels : Prop :=
  ∀ (K : ℕ) (μ : Measure (StatFormal.Wave12b.Euc K)) (ρ : StatFormal.Wave12b.Euc K → ℝ)
    (Q F : StatFormal.Wave12b.Euc K → StatFormal.Wave12b.Euc K) (U : Set (StatFormal.Wave12b.Euc K))
    (v : StatFormal.Wave12b.Euc K) (p : ℝ),
    ContinuousOn (StatFormal.Wave23a.cdfK μ ρ) (Icc 0 1) → StatFormal.Wave23a.cdfK μ ρ 0 = 0 →
    StatFormal.Wave23a.cdfK μ ρ 1 = 1 → (∀ t : ℝ, 0 ≤ t → ∀ z, ρ (t • z) = t * ρ z) → ρ v = 1 →
    (∀ z ∈ interior U, F (Q z) = z) → 0 < p → p ≤ 1 → StatFormal.Wave23a.cdfKInv μ ρ p • v ∈ interior U →
      1 - StatFormal.Wave23a.cdfK μ ρ (ρ (F (Q (StatFormal.Wave23a.cdfKInv μ ρ p • v)))) = 1 - p ∧
        (ρ (F (Q (StatFormal.Wave23a.cdfKInv μ ρ p • v))))⁻¹ • F (Q (StatFormal.Wave23a.cdfKInv μ ρ p • v)) = v

/-- (iii) Uniform consistency, under the hypotheses of `thm:band-consistency` (convex potentials converging locally
uniformly on the open convex `C`, `χ` differentiable on the open `O ⊆ C`, fitted maps subgradient selections on the
compact level region `A_{K,1−δ} ⊆ O`, population map `∇χ`): if every `τ_{K,p} w` (`w ∈ 𝕊_K`, `p ∈ 𝒫_w`, `p ≤ 1 − δ`)
lies in `A_{K,1−δ}`, then `sup_w sup_p ‖Q̂_n(τ_p w) − ∇χ(τ_p w)‖ → 0`; and for directions `v̂_n → v` with
`τ_p v̂_n, τ_p v ∈ A_{K,1−δ}` and bounded radii, `sup_p ‖Q̂_n(τ_p v̂_n) − ∇χ(τ_p v)‖ → 0`. -/
def rk_paths_consistency : Prop :=
  ∀ (K : ℕ) (C O A1 SK : Set (StatFormal.Wave12b.Euc K)) (χ : StatFormal.Wave12b.Euc K → ℝ)
    (g : ℕ → StatFormal.Wave12b.Euc K → ℝ) (T : ℕ → StatFormal.Wave12b.Euc K → StatFormal.Wave12b.Euc K)
    (τ : ℝ → ℝ) (P : StatFormal.Wave12b.Euc K → Set ℝ) (v : StatFormal.Wave12b.Euc K)
    (vh : ℕ → StatFormal.Wave12b.Euc K),
    IsOpen C → Convex ℝ C → ConvexOn ℝ C χ → (∀ n, ConvexOn ℝ C (g n)) →
    (∀ S' ⊆ C, IsCompact S' → TendstoUniformlyOn g χ atTop S') → IsOpen O → O ⊆ C →
    (∀ u ∈ O, DifferentiableAt ℝ χ u) → IsCompact A1 → A1 ⊆ O →
    (∀ n, ∀ u ∈ A1, T n u ∈ TauCeti.subdifferential (innerₗ (StatFormal.Wave12b.Euc K))
      (StatFormal.OTFD.Wave19a.extTop C (g n)) u) →
    (∀ w ∈ SK, ∀ p ∈ P w, τ p • w ∈ A1) →
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ w ∈ SK, ∀ p ∈ P w, ‖T n (τ p • w) - gradient χ (τ p • w)‖ ≤ ε) ∧
      ((∀ p ∈ P v, τ p • v ∈ A1) → (∀ n, ∀ p ∈ P v, τ p • vh n ∈ A1) → (∃ B, ∀ p ∈ P v, |τ p| ≤ B) →
        Tendsto vh atTop (𝓝 v) →
          ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ p ∈ P v, ‖T n (τ p • vh n) - gradient χ (τ p • v)‖ ≤ ε)

/-! #### A `prop:parsimony` -/

/-- The reference-only tolerance: the upper `γ`-quantile `s_n` of the energy distance between `n_v` and `m_v`
independent draws `Υ(U)`, `U ∼ μ`, from `Υ#μ` (`‖Υ‖ ≤ R_Υ`) satisfies `s_n ≤ 2R_Υ h + R_Υ(32h log(2/γ))^{1/2}`. -/
def parsimony_tolerance : Prop :=
  ∀ (𝒰 E : Type) [MeasurableSpace 𝒰] [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (μ : Measure 𝒰) [IsProbabilityMeasure μ] (Υ : 𝒰 → E) (R γ : ℝ) (nv mv : ℕ),
    Measurable Υ → (∀ u, ‖Υ u‖ ≤ R) → 1 ≤ nv → 1 ≤ mv → 0 < γ → γ < 1 →
      upperQuantile (Measure.pi fun _ : Fin nv ⊕ Fin mv => μ)
          (fun z => edVstat (fun i => Υ (z (Sum.inl i))) (fun j => Υ (z (Sum.inr j)))) γ ≤ parsBound R γ nv mv

/-- … and the bound tends to `0` as `n_v, m_v → ∞` (fixed `γ ∈ (0,1)`). -/
def parsimony_tolerance_tendsto : Prop :=
  ∀ (R γ : ℝ) (nv mv : ℕ → ℕ), 0 < γ → γ < 1 → Tendsto nv atTop atTop → Tendsto mv atTop atTop →
    Tendsto (fun k => parsBound R γ (nv k) (mv k)) atTop (𝓝 0)

/-! #### T `eq:basebridge` (`prop:base`) -/

/-- The two-leg comparison of two base curves, abstract skeleton: `Ex_t = Exp_{m(t)}`, `Exh_t = Exp_{m̂(t)}` (tangent
spaces identified with `V`), `J_t` an isometry (parallel transport); the vertical leg uses the frozen `LengthBound`
of `lem:exp` at `m̂(t)` (constant `L_b = Lb Dh b`); the horizontal leg is the curve `σ ↦ Exp_{γ_t(σ)}(P_σ x)` from
`Exp_{m(t)} x` to `Exp_{m̂(t)}(J_t x)`, whose length (bounding the distance of its ends) has speed at most `C_b`
times the speed of the minimising geodesic `γ_t`, whose length is `d(m(t), m̂(t))`. Then
`D_∞(E_{m̂} v̂, E_m v) ≤ C_b D_∞(m̂, m) + L_b sup_t ‖v̂(t) − J_t v(t)‖` for fields bounded by `b`. -/
def basebridge : Prop :=
  ∀ (T V W M : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [PseudoEMetricSpace M] (m mh : T → M) (Ex Exh : T → V → M) (Dh : T → V → V →L[ℝ] W) (J : T → V → V)
    (Hc : T → V → ℝ → M) (spd : T → V → ℝ → ℝ≥0∞) (gspd : T → ℝ → ℝ≥0∞) (Cb : ℝ≥0) (b : ℝ) (v vh : T → V),
    StatFormal.OTFD.Wave22b.LengthBound Exh Dh → (∀ t x, ‖J t x‖ = ‖x‖) →
    (∀ t x, Hc t x 0 = Ex t x ∧ Hc t x 1 = Exh t (J t x)) →
    (∀ t x, edist (Hc t x 0) (Hc t x 1) ≤ ∫⁻ σ in Icc (0 : ℝ) 1, spd t x σ) →
    (∀ t x σ, ‖x‖ ≤ b → spd t x σ ≤ (Cb : ℝ≥0∞) * gspd t σ) →
    (∀ t, ∫⁻ σ in Icc (0 : ℝ) 1, gspd t σ = edist (m t) (mh t)) →
    (∀ t, ‖v t‖ ≤ b) → (∀ t, ‖vh t‖ ≤ b) →
      (⨆ t, edist (Exh t (vh t)) (Ex t (v t))) ≤
        (Cb : ℝ≥0∞) * (⨆ t, edist (mh t) (m t)) + StatFormal.OTFD.Wave22b.Lb Dh b * ⨆ t, ‖vh t - J t (v t)‖ₑ

/-! #### A `cor:app-bijective-rate` (a) and `cor:app-entropic-rate` -/

/-- `cor:app-bijective-rate`(a), consistency: `P ∈ 𝒫^ℓ(H)` (with finite second moment), a coherent reference bounded
by `M` with the population maps of `prop:integrated-sieve-strong` (`F = 𝔽_P`, `F_{+,K}`), `X_1, …, X_n` i.i.d. `P`,
`K_n → ∞`, the bijective grid `m_n = n` with `ass:app-weak-conditioning` along `K_n` (as in the frozen
`emp_bijective_weak`) and any optimal assignments `σ̂`: if
`B_n = (4/α_{K_n})(β²_{K_n} + σ²_{K_n})^{1/2} {20M²(K_n+1)n^{−2/(K_n+4)} + W₂²(μ_{K_n,n}, μ_{K_n})}^{1/2} → 0`
then `E[n⁻¹ Σ_i ‖ι_{K_n} F̂^{(n)}(x_i) − 𝔽_P(X_i)‖²_H] → 0` (`S(K_n) → 0` is derived, not assumed). -/
def app_bijective_rate : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (e : ℕ → H) (P μ : ProbabilityMeasure H) (F : H → H)
    (M : ℝ) (FK : (K : ℕ) → StatFormal.Wave12b.Euc K → StatFormal.Wave12b.Euc K) (Ω : Type) [MeasurableSpace Ω]
    (Pr : Measure Ω) [IsProbabilityMeasure Pr] (Kn : ℕ → ℕ) (X : (n : ℕ) → Fin n → Ω → H)
    (α β : ℕ → ℝ) (u s : (n : ℕ) → Fin n → StatFormal.Wave12b.Euc (Kn n))
    (f : (n : ℕ) → StatFormal.Wave12b.Euc (Kn n) → ℝ) (σ : (n : ℕ) → Ω → Equiv.Perm (Fin n)),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    StatFormal.OTFD.WaveL1.LipNull (P : Measure H) → ∫⁻ x, ‖x‖ₑ ^ 2 ∂(P : Measure H) < ⊤ →
    (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 → Measurable F → (P : Measure H).map F = μ →
    StatFormal.OTFD.WaveL1.IsCMMapAE (P : Measure H) F → (∀ K, Measurable (FK K)) →
    (∀ K, ((P : Measure H).map (StatFormal.OTFD.Wave1.truncK e K)).map (FK K) =
      (μ : Measure H).map (StatFormal.OTFD.Wave1.truncK e K)) →
    (∀ K, StatFormal.OTFD.WaveL1.IsCMMapAE ((P : Measure H).map (StatFormal.OTFD.Wave1.truncK e K)) (FK K)) →
    (∀ n i, Measurable (X n i)) → (∀ n, iIndepFun (X n) Pr) → (∀ n i, Pr.map (X n i) = P) →
    Tendsto Kn atTop atTop →
    (∀ n, 0 < α n) → (∀ n : ℕ, (1 / (n : ℝ)) * ∑ j, ‖s n j‖ ^ 2 ≤ β n ^ 2) →
    (∀ n, ∀ᵐ ω ∂Pr,
      StatFormal.OTFD.Wave8b.SubgradAt (f n) (u n) (s n)
        (fun i => FK (Kn n) (StatFormal.OTFD.Wave1.truncK e (Kn n) (X n i ω))) ∧
      StatFormal.OTFD.Wave8b.OneSidedAt (α n) (f n) (u n) (fun i => StatFormal.OTFD.Wave1.truncK e (Kn n) (X n i ω))
        (fun i => FK (Kn n) (StatFormal.OTFD.Wave1.truncK e (Kn n) (X n i ω)))) →
    (∀ n ω, StatFormal.OTFD.Wave8b.IsOptAssign (fun i => StatFormal.OTFD.Wave1.truncK e (Kn n) (X n i ω)) (u n)
      (σ n ω)) →
    Tendsto (fun n => ENNReal.ofReal (4 / α n * √(β n ^ 2 +
        ∫ z, ‖z‖ ^ 2 ∂((P : Measure H).map (StatFormal.OTFD.Wave1.truncK e (Kn n))))) *
      (ENNReal.ofReal (20 * M ^ 2 * (Kn n + 1) * (n : ℝ) ^ (-(2 : ℝ) / (Kn n + 4))) +
        TauCeti.wassersteinEDist 2 (StatFormal.OTFD.Wave6b.empMeasure (u n))
          ((μ : Measure H).map (StatFormal.OTFD.Wave1.truncK e (Kn n))) ^ 2) ^ (1 / 2 : ℝ)) atTop (𝓝 0) →
      Tendsto (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal ((1 / (n : ℝ)) * ∑ i,
          ‖StatFormal.OTFD.Wave8b.embed e (Kn n) (u n (σ n ω i)) - F (X n i ω)‖ ^ 2) ∂Pr) atTop (𝓝 0)

/-- `cor:app-entropic-rate`: under the same population and sample hypotheses, deterministic grids of arbitrary sizes
`m_n ≥ 1`, `ass:app-weak-conditioning` along `K_n` and any entropic plans `π^{(n)}` at `ε_n > 0` (`IsEntPlan`), the
joint conditions `eq:app-entropic-joint-wass`
(`(β² + σ²)^{1/2}/α · {(K_n+1)n^{−2/(K_n+4)} + W₂²(μ_{K_n,m_n}, μ_{K_n})}^{1/2} → 0`) and `eq:app-entropic-joint-eps`
(`(ε_n/α) log min(n, m_n) → 0`) give `E[n⁻¹ Σ_i ‖ι_{K_n} F̂^{(n),bar}(x_i) − 𝔽_P(X_i)‖²_H] → 0`. -/
def app_entropic_rate : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (e : ℕ → H) (P μ : ProbabilityMeasure H) (F : H → H)
    (M : ℝ) (FK : (K : ℕ) → StatFormal.Wave12b.Euc K → StatFormal.Wave12b.Euc K) (Ω : Type) [MeasurableSpace Ω]
    (Pr : Measure Ω) [IsProbabilityMeasure Pr] (Kn : ℕ → ℕ) (X : (n : ℕ) → Fin n → Ω → H)
    (mn : ℕ → ℕ) (α β ε : ℕ → ℝ) (u s : (n : ℕ) → Fin (mn n) → StatFormal.Wave12b.Euc (Kn n))
    (f : (n : ℕ) → StatFormal.Wave12b.Euc (Kn n) → ℝ) (π : (n : ℕ) → Ω → Matrix (Fin n) (Fin (mn n)) ℝ),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    StatFormal.OTFD.WaveL1.LipNull (P : Measure H) → ∫⁻ x, ‖x‖ₑ ^ 2 ∂(P : Measure H) < ⊤ →
    (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 → Measurable F → (P : Measure H).map F = μ →
    StatFormal.OTFD.WaveL1.IsCMMapAE (P : Measure H) F → (∀ K, Measurable (FK K)) →
    (∀ K, ((P : Measure H).map (StatFormal.OTFD.Wave1.truncK e K)).map (FK K) =
      (μ : Measure H).map (StatFormal.OTFD.Wave1.truncK e K)) →
    (∀ K, StatFormal.OTFD.WaveL1.IsCMMapAE ((P : Measure H).map (StatFormal.OTFD.Wave1.truncK e K)) (FK K)) →
    (∀ n i, Measurable (X n i)) → (∀ n, iIndepFun (X n) Pr) → (∀ n i, Pr.map (X n i) = P) →
    Tendsto Kn atTop atTop →
    (∀ n, 1 ≤ mn n) → (∀ n, 0 < α n) → (∀ n, 0 < ε n) → (∀ n : ℕ, (1 / (mn n : ℝ)) * ∑ j, ‖s n j‖ ^ 2 ≤ β n ^ 2) →
    (∀ n, ∀ᵐ ω ∂Pr,
      StatFormal.OTFD.Wave8b.SubgradAt (f n) (u n) (s n)
        (fun i => FK (Kn n) (StatFormal.OTFD.Wave1.truncK e (Kn n) (X n i ω))) ∧
      StatFormal.OTFD.Wave8b.OneSidedAt (α n) (f n) (u n) (fun i => StatFormal.OTFD.Wave1.truncK e (Kn n) (X n i ω))
        (fun i => FK (Kn n) (StatFormal.OTFD.Wave1.truncK e (Kn n) (X n i ω)))) →
    (∀ n ω, StatFormal.OTFD.Wave8b.IsEntPlan (ε n) (fun i => StatFormal.OTFD.Wave1.truncK e (Kn n) (X n i ω)) (u n)
      (π n ω)) →
    Tendsto (fun n => ENNReal.ofReal (√(β n ^ 2 +
        ∫ z, ‖z‖ ^ 2 ∂((P : Measure H).map (StatFormal.OTFD.Wave1.truncK e (Kn n)))) / α n) *
      (ENNReal.ofReal ((Kn n + 1) * (n : ℝ) ^ (-(2 : ℝ) / (Kn n + 4))) +
        TauCeti.wassersteinEDist 2 (StatFormal.OTFD.Wave6b.empMeasure (u n))
          ((μ : Measure H).map (StatFormal.OTFD.Wave1.truncK e (Kn n))) ^ 2) ^ (1 / 2 : ℝ)) atTop (𝓝 0) →
    Tendsto (fun n => ε n / α n * Real.log (min n (mn n))) atTop (𝓝 0) →
      Tendsto (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal ((1 / (n : ℝ)) * ∑ i,
          ‖StatFormal.OTFD.Wave8b.embed e (Kn n) (StatFormal.OTFD.Wave8b.entBary (π n ω) (u n) i) -
            F (X n i ω)‖ ^ 2) ∂Pr) atTop (𝓝 0)

end Claims

end StatFormal.Wave24a
