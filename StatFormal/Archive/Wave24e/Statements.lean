import StatFormal.Archive.Wave23a.Statements
import StatFormal.Archive.Wave23c.Statements
import Mathlib.Probability.ProductMeasure
import Mathlib.Analysis.InnerProductSpace.l2Space
import StatFormal.Archive.Wave18a.Statements
import StatFormal.Archive.SBFairness.Stability.Statements
import Mathlib.Probability.Moments.Covariance
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import StatFormal.Archive.Wave9b.Statements
import StatFormal.Archive.OTFD.Wave22b.Statements
import Mathlib.Probability.Distributions.Gamma
import StatFormal.Archive.OTFD.WaveL4.Statements
import StatFormal.Archive.Wave11b.Statements

/-!
# FROZEN STATEMENTS — wave 24e (QUEUE rows 360–379): ICL `thm:cond-consistency`, `cor:inference`, `lem:cond-vstat`,
# `lem:e-vstat`; otfd A `cor:ghs-tukey-degeneracy`; R `lem:cm-null`, `cor:gaussian-t`; B `lem:refs-ac`,
# `lem:band-pointwise-lower`, `thm:band-consistency-shell`, `lem:band-containment-relative`, `prop:band-injectivity`;
# C `lem:cond-rank-consistency`; G `prop:reference`, `thm:epszero`, `prop:firstmoment`, `cor:onlyL2`; SB `cor:field-cop`;
# TM `lem:rffkernel` (row 360, ICL `cor:iid-consistency`, skipped)

Sources (current text after the 2026-10-16 corrections; verbatim in `lean-formalisation/inventory/extracted/`):
* ICL (`context-distribution-ICL/paper/v3`): `thm:cond-consistency` (`sections/06b_cond_theory.tex:61-79`, proof
  `supp/proofs_conditional.tex:563-614`), `cor:inference` (`sections/06_estimation.tex:154-170`), `lem:cond-vstat`
  (`supp/proofs_conditional.tex:544-551`), `lem:e-vstat` (`supp/proofs_score.tex:124-130`), with `as:compact`,
  `as:score` (`supp/proofs_score.tex:14-23`).
* otfd A `cor:ghs-tukey-degeneracy` (`A_sieves/supplement.tex:353-371`), the cubic law (`A_sieves/main.tex:613-638`).
* otfd R `lem:cm-null` (`R_robustness/sections/appendix_a.tex:58-72`), `cor:gaussian-t` (`sections/s3_infinite.tex:74-84`).
* otfd B (`B_bands/supplement.tex`): `lem:refs-ac` (`:485-490`), `lem:band-pointwise-lower` (`:837-848`, proof
  `:2070-2084`), `thm:band-consistency-shell` (`:871-897`, proof `:2101-2167`), `lem:band-containment-relative`
  (`:2033-2046`, proof `:2048-2068`), `prop:band-injectivity` (`:4474-4500`, proof `:4502-4523`).
* otfd C `lem:cond-rank-consistency` (`C_conditional/main.tex:1002-1009`, `eq:cond-rank-map` `:914-919`, proof
  `supplement.tex:2062-2118`).
* otfd G (`G_geodesic`): `prop:reference` (`main.tex:371-401`, `def:reference` `:323-331`), `thm:epszero`
  (`main.tex:801-823`), `prop:firstmoment` (`supp_moved.tex:5-47`), `cor:onlyL2` (`supp_moved.tex:442-470`, proof
  `:472-500`).
* SB `cor:field-cop` (`data-fairness-repair/schrodinger_bridge_fairness_repair.tex:1025-1044`), `def:standardisable`,
  `thm:field` (`:933-973`).
* TM `lem:rffkernel` (`trimmed-mmd/paper.tex:1683-1708`).
Imports the frozen `Wave23a` (`popSupp`, `fitSupp`), `Wave23c` (`FixedKOOS`, `entMap`, `lagPot`, `ellF1`), `OTFD/Wave13a`
(`tukeyDepthH`), `OTFD/Wave8c` (`unifSym`), `Wave18a` (`transportPolytope`, `frob`, `IsRegMin`, `entReg`),
`SBFairness/Stability` (`tv`), `Wave9b` (`Standardises`), `Wave11b` (`collision`, `swoExp`, `iidExp`), `OTFD/Wave22b` (`cubicLaw`) and `OTFD/WaveL4` (`WeightedFit`;
through it `OTFD/WaveL3` `RefLaw`, `Mom1`, `OTFD/WaveL1` `IsCMMapAE`) statements, not copied.

Covered:
* `lem:band-pointwise-lower`: `band_pointwise_lower_core` (deterministic, any measurable region, so simultaneously in
  `p`), `band_pointwise_lower` (DISCHARGED under `FixedKOOS` through the certified Wave 23c `potential_consistency_maps`).
* `lem:band-containment-relative`: `band_containment_relative` (population-only net `u_l ∈ A ∩ G`, bound for every `n`,
  `v` and every sequence `Q̂_n`, `ε_n(η) → 0` when `Q̂_n → Q` on `G`).
* `thm:band-consistency-shell`: `band_consistency_shell` (Steps 0–4: `h^pop_p(v) = max_{g = τ_p} ⟨v, Q⟩`, attained;
  `|ĥ_p − h^pop_p| ≤ ‖v‖ sup_Σ ‖Q̂ − Q‖`, every `p ∈ [p₀, 1 − δ]`).
* `prop:band-injectivity` (ii): `band_injectivity_entropic` (injective ⇔ affine span; constant along a line otherwise;
  `n ≥ K + 1`); (i), one inclusion: `band_injectivity_boundary` (`Q̂(∂A) ⊆ ∂Q̂(A)`).
* `lem:refs-ac`: `refs_ac_cubic_cK` (continuity of the cubic `c_K`).
* `lem:cond-vstat`: `cond_vstat` (the full lemma). `lem:e-vstat`: `e_vstat` (the full lemma).
* `thm:cond-consistency` (i): `cond_consistency_replacement` (Step 1: `|E[f|D] − E f| ≤ Bp/(1 − p)`,
  `p ≤ C(M,2) max_j w_j`; the union bound `p ≤ C(M,2) Σ w_j²` is the frozen Wave 11b `swor_collision` and the
  identity behind the first bound is in the frozen `swor_perturb`, whose bound `2Fp/(1 − p)` is for `|f| ≤ F`),
  `cond_consistency_values` (Step 5: `J(θ̂) → min J`, `J_pool(θ̂) → min J`, along any filter; overlaps the frozen
  Wave 23a `score_argmin`, which has `inf J_n → min J` and cluster points, not the values at `θ̂`).
* `cor:inference`: `inference_linear` (the influence function `τ_θ` of the plug-in: chain rule and `∫ τ dP₀ = 0`).
* `cor:ghs-tukey-degeneracy`, cubic law: `ghs_cubic_ae_zero` (`TD_H = 0` `μ`-a.e.), `ghs_cubic_center` (`TD_H(0) = 1/2`).
* `lem:cm-null`: `cm_null`. `cor:gaussian-t`: `gaussian_t_moment` (`E W < ∞ ⇔ ν > 2`), `gaussian_t_tail`
  (`c r^{−ν} ≤ F_{t_ν}(−r) ≤ C r^{−ν}`, `r ≥ 1`).
* `lem:cond-rank-consistency`: `cond_rank_sandwich` (Steps 1–3 and `F̂ ∈ ∂Φ`), `cond_rank_consistency` (CONDITIONAL on
  Step 4, the conjugate-potential convergence of `prop:conditional-potentials`, and on `δ_n`-dense grids),
  `cond_rank_consistency_uncond` (DISCHARGED: both premises derived from `RefLaw`, `m₁(P) < ∞`, the population map and
  `WeightedFit` through the certified OTFD wave-L4 `cond_potentials_weighted`; the limit pinned as the population
  rank potential `X = (χ + ι_{int 𝒰_K})^*`, `χ` the normalised population quantile potential).
* `prop:reference`: `reference_calibration` ((a), (c)), `reference_truncation` ((b), both couplings).
* `thm:epszero` (a), discrete marginals: `epszero_discrete`.
* `prop:firstmoment` (a): `firstmoment_cost`, `firstmoment_plan`; (b): `firstmoment_kernel`.
* `cor:onlyL2` (b), eigenfunction step and `eq:H1cov` with (b2)'s deduction: `onlyL2_dirichlet`; (c): `onlyL2_reference`.
* `cor:field-cop`: `field_cop_standardises`, `field_cop_exact`.
* `lem:rffkernel`: `rff_unbiased` (phased features are unbiased), `rff_finite` (finite-set Hoeffding/union bound).

Not covered (declared):
* `cor:iid-consistency` (row 360): SKIPPED. Its only new content is the pool approximation of the population optimum
  for the i.i.d. objective (`inf_w R^iid(μ_w) → R^iid⋆`, a Varadarajan-type argument through the KL penalty and
  `λ_{KL,n} log n → 0`); the rest is the frozen `cor:oracle`/`thm:joint` chain, and a claim taking the approximation as
  a hypothesis would be bookkeeping. The same piece is missing for its twin `cor:consistency`.
* `thm:cond-consistency`: (i)'s a.s. uniform law for policies (Steps 2–4 assembled: query-indexed V-statistics via
  `cond_vstat`, the penalty, `h^n → h`) and "limit points minimise" (the frozen Wave 23a `score_argmin`); (ii) (sieve
  over `R_n` gates, Lusin, grid construction).
* `cor:inference`: the delta method and the joint CLT of `thm:score` (missing), `∇T(θ)`, the `σ²_Ψ` formula.
* `cor:gaussian-t`: `E‖X‖² = E W · tr Σ` (independence and Fubini; only `E W < ∞ ⇔ ν > 2` is stated).
* `cor:ghs-tukey-degeneracy`: the ball law (Gaussian direction on `H`), the radial-shell statement (calibrations of
  `sec:depth-adapt`), the breakdown consequences (`thm:sieve-breakdown`). The a.e. clause is also an instance of the
  frozen Wave 21b `nullmass_a`; it is proved directly here.
* `cor:gaussian-t`: the depth identities `TD_H = Φ(−‖x‖_CM)`, `F_{t_ν}(−‖x‖_CM)` (the frozen Wave 23c
  `elliptical_depth` at `W ≡ 1`, resp. the InvGamma `W`); that `√W ξ ∼ t_ν` (no Student law in Mathlib: `F_{t_ν}` is
  defined as `F₁`).
* `lem:refs-ac`: naive law (frozen OTFD Wave 8c `naive_density`), cubic absolute continuity and bounded support (frozen
  OTFD Wave 22b `cubic_density`), ball law (absolute continuity needs the change of variables through
  `y ↦ ry/(‖y‖² + w)^{1/2}`; its `c_K` continuity is the frozen Wave 22b `cK_shape`).
* `lem:band-pointwise-lower`: the hard-map and certified-edge variants (follow from the core given their a.e.
  convergence). `lem:band-containment-relative`: the "in particular" liminf (immediate).
* `thm:band-consistency-shell`: `Δ_n → 0` (`prop:app-potential-consistency` + `lem:app-subgradient-convergence`(b)),
  the hard-map and full-subdifferential edges.
* `prop:band-injectivity`: (i) `⊇` direction's converse (invariance of domain, missing), (iii) (quadratic/Karp maps).
* `lem:cond-rank-consistency`: identification `∇X = F_{K,x}` (McCann; `X` is pinned as the conjugate of the
  population quantile potential), Step 6 (in probability for an independent `Z`); the "almost surely" is per sample
  path (deterministic sequences, as in wave L4); nonvacuity of `WeightedFit` jointly with the column equations of
  the same duals `f_n` (the paper's `lem:weighted-duality` remark) is not claimed.
* `prop:reference` (d) (isometry equivariance; Riemannian Exp, Log on the cut locus); (b)'s "the sieve laws keep the
  exact calibration".
* `thm:epszero`: (a) for general marginals (tightness, Nutz 5.10), (b) beyond the frozen discrete Wave 18a
  `entropy_zero_entropic`, (c) (trap: `F₀` only measurable), (d) `H(u) = E min{1, u/W_K}` (this is the frozen T
  `lem:cK`, OTFD Wave 22b `cK_formula`, `cK_shape`; not restated).
* `prop:firstmoment`: existence/uniqueness of `π̃_ε` and of `(f, g)` (Nutz; missing), `Z_f < ∞` for the actual
  potential (hypothesis), `g̃ = g` `P`-a.e. and the disintegration of `π̃_ε` by the kernel, (c) (quantiles).
* `cor:onlyL2`: (a) and (b1), (b3), (b4) (need `prop:onlyL2`(iii), not frozen), the Sobolev field `H¹_m`
  (encoded abstractly), the TV limit along `s → 0`.
* `cor:field-cop`: the `√(d/n)` rate (quantile-process theory). `field_cop_exact` is also obtainable from the frozen
  Wave 9b `field_exact` with `field_cop_standardises`; it is kept as the printed clause.
* `lem:rffkernel`: the supremum over the compact domain (net, Lipschitz constant through `σ_Λ`), the `r^{−1/2}`
  optimality claim.

Encodings (to be checked by the critic):
* B: `ℝ^K = EuclideanSpace ℝ (Fin K)`, `M_K = I`; edges in `EReal` as in Wave 23a; regions `A_p = {g ≤ τ_p}` for a
  continuous, positively homogeneous, coercive gauge `g` (the paper's norm `g_K`; generalisation); `τ` any function
  nondecreasing on `[p₀, 1 − δ]` with `τ_{p₀} > 0`; `C` plays `int 𝒰_K`; `supp μ_K ⊇ A_{1−δ}` as positivity of open
  sets meeting `A_{1−δ}`; (b′) in its "Q continuous" form, `Q` a subgradient selection on `C` (the continuous version of
  `∇χ_K`; `h^pop` is version-free); `Q̂` a subgradient selection of a finite convex `χ̂` (paper: `∇χ̂_n`); the bound in
  the form "`‖Q̂ − Q‖ ≤ D` on `Σ` ⇒ …" (the sup is the least such `D`). Relative lemma: `G` the differentiability set,
  `ε_n(η)` an `ℝ≥0` max. Injectivity: `entMap` of Wave 23c; affine spanning `affineSpan ℝ (range Z) = ⊤`.
* ICL: pool `Z_0, Z_1, …` i.i.d. (`iIndepFun`, laws `= P₀`), the `n`-th statistic uses `Z_0, …, Z_{n−1}`; `𝒵`, `A`, `Θ`
  compact metric, Borel; `vStat` with `n^{−M}` (junk only at `n = 0`); `μ_θ^{⊗M}` in density form
  `∫ ∏_k (s_θ(t_k)/c_θ) H dP₀^{⊗M}`; collision probability and the conditioned law `Π_w` the frozen Wave 11b finite
  sums over `[n]^M`, `p < 1` assumed; ε-minimisers as `J_{n,m}(θ̂) ≤ J_{n,m}(θ) + ε_opt` for all `θ`; `cor:inference` at a fixed
  `θ` with `Γ` differentiable at `m` (paper: `C¹`), `L` pinned by `HasFDerivAt`.
* A: `H` a Hilbert space with Hilbert basis `(e_k)`; `X_cub = Σ' λ_k V_k e_k` on `ℕ → ℝ` with `infinitePi` of the frozen
  `unifSym (1/2)` (the map is a.e. measurable and the series converges on the support, both proved); `TD_H` = frozen
  `tukeyDepthH`.
* R: KL form of `G ∼ N(0,Σ)` (`⟨e_k, G⟩ = √λ_k ξ_k` a.s., `ξ_k` i.i.d. `N(0,1)`), `Σ^{1/2}` any bounded `S` with
  `S e_k = √λ_k e_k`; outer measure of `{√W G ∈ ran S}`. Student: `1/W ∼ gammaMeasure (ν/2) (ν/2)`, `F_{t_ν} = ellF1`.
* C: `N = n + 1` responses, `m = M + 1` grid points, `b_j = 1/m`; `χ` = frozen `lagPot`; `X = sup_{w ∈ 𝒰}` via `sSup`
  (bounded above under the hypotheses); Step 4 assumed as pointwise convergence after arbitrary constants `c_n` (the
  paper's normalised locally uniform convergence implies it); the grids' `δ_n`-density is a hypothesis (the paper
  derives it from weak convergence, Step 3).
* G: `V = τ G/‖G‖` with `‖0‖⁻¹ = 0` (only on `{G = 0}`, null); `Y v = E_m(sv)` abstract with `D(m, E_m(sv)) ≤ s‖v‖`;
  `Π_K` through an orthonormal sequence, `G` in its closed span (as for the Karhunen–Loève series); sieve `V_K` uses
  `Π_K G` (where `Π_K G = 0`, eventually never a.s., the value is `0`); `cor:onlyL2`(b): `ι : H¹ → H` bounded injective,
  `D` bounded (the covariant derivative), eigen-equation in weak form through Mathlib `cov`.
* SB: copula measure in PIT form `C_μ = (S_μ)_#μ` (for continuous marginals the usual definition), marginals via
  coordinate pushforwards, inverse = Tau Ceti quantiles; `Standardises` frozen (Wave 9b).
* TM: phased features `√(2/r) κ cos(ωᵀx + b)`, `b ∼ unifCircle = Unif[0, 2π]`; `k` through Bochner as
  `κ² ∫ cos(ωᵀ(x − y)) dΛ`; features i.i.d. pairs (`iIndepFun`, laws `Λ ⊗ Unif`); event measurable.

Critic notes:
* All 32 claims are proved in `Wave24e/Route{Band,Shell,Inject,RefsAC,VStat,ICL,CubicH,CM,Student,CondRank,
  CondRankUncond,Geo,Ref,Dirichlet,Cop,RFF}.lean`. Reused: certified Wave 23c `potential_consistency_maps`, Wave 18a `entropy_zero_entropic`,
  OTFD Wave 22b `cubic_density`, OTFD Wave 8c `unifSym_prob`; Foundations `Empirical` (Varadarajan), `Convex`
  (Rockafellar 24.5, Thm 10.8 limit convexity); Tau Ceti (quantile/PIT, Rademacher for convex functions); Mathlib
  (`ProbabilityMeasure.continuous_pi`, strong law, Hoeffding, Gamma integrals).
* CONDITIONAL claims: `cond_rank_consistency` (Step 4 of the printed proof, i.e. `prop:conditional-potentials`, and
  grid density); discharged by `cond_rank_consistency_uncond` (`Wave24e/RouteCondRankUncond.lean`, from the certified
  OTFD wave-L4 route theorem `cond_potentials_weighted`). SPECIALISED: `band_pointwise_lower` (`FixedKOOS`: second
  moment and exact duals, where `ass:fixedK-oos` has a first moment and `r_n → 0`).
* Observations: (1) `lem:cond-vstat` and `lem:e-vstat` hold as printed; the proof here uses weak convergence of
  `P_n^{⊗M}` instead of Stone–Weierstrass. (2) `thm:band-consistency-shell` Step 1 needs neither convexity of the
  regions nor absolute continuity; it needs `K ≥ 1`. (3) `lem:cm-null` needs neither independence of `W` and `G` nor
  `Σ λ_k < ∞` beyond existence of `G`. (4) `lem:rffkernel`: the printed deviation term `2√(2 log(1/δ))` is CORRECT
  (already fixed as DEFECTS #23, REVISION_LEDGER I42): McDiarmid applied to the single function `sup |ẑ − k|` is
  one-sided with bounded differences `4κ²/r` (phased summands have range `4κ²/r`), giving exactly
  `2κ²√(2 log(1/δ)/r)` above the expectation `κ² h/√r`. The `2|S|` inside the logarithm of `rff_finite` comes only
  from its own route (two-sided Hoeffding per pair and a union bound); `rff_finite` is a finite-set substitute,
  neither implied by nor implying the printed lemma. (5) No statement was found false.
* Critic (2026-10-16): ACCEPT-WITH-NOTE after fixes. `cond_consistency_replacement` restated the frozen Wave 11b
  `swor_collision` and duplicated `ICL.Cond.iidLaw`/`Wave11b.collision`: now stated with the frozen `collision`,
  `swoExp`, `iidExp`, the union-bound clause removed. `cond_rank_consistency_uncond` added (Step 4 and the grid density
  discharged; mechanical diff against the frozen wave-L4 `cond_potentials_weighted`: the same `RefLaw`, `Mom1`, `Q`,
  `IsCMMapAE`, `WeightedFit` premises with `χ_n = g_n = lagPot Z_n f_n`, plus the paper's grid, column-equation,
  ball and `ε_n log(m_n N_n) → 0` premises). The gauge `g` of `band_consistency_shell` is a generalisation containing
  the paper's `g_K = ρ_{μ_K}` (a norm). No junk: `sSup` in `contConj` and in the pinned `X` is of a nonempty set bounded
  above (`χ ≥ 0` on `int 𝒰_K`, `𝒰_K` bounded); `gradient` junk lies off the differentiability set.

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave24e

open StatFormal.Wave23a (popSupp fitSupp)
open StatFormal.Wave23c (FixedKOOS entMap lagPot)
open TauCeti (IsKantorovichOptimalTransportMap)
open StatFormal.OTFD.Wave13a (tukeyDepthH)
open StatFormal.OTFD.Wave8c (unifSym)
open StatFormal.Wave18a (transportPolytope frob IsRegMin entReg)
open StatFormal.SBFairness.Stability (tv)
open StatFormal.Wave9b (Standardises)
open StatFormal.Wave23c (ellF1)

/-! ### ICL: V-statistics -/

/-- The V-statistic `P_n^{⊗M} ψ_a = n^{-M} Σ_{j ∈ [n]^M} ψ(a, Z_{j_1}, …, Z_{j_M})` of the first `n` pool points. -/
def vStat {A Z : Type*} {M n : ℕ} (ψ : A × (Fin M → Z) → ℝ) (z : Fin n → Z) (a : A) : ℝ :=
  (1 / (n : ℝ) ^ M) * ∑ j : Fin M → Fin n, ψ (a, z ∘ j)

/-- The weighted V-statistic `∫ H_θ dμ_{θ,n}^{⊗M} = Σ_{j ∈ [n]^M} ∏_k w_{j_k}(θ) H(θ, Z_{j_1}, …, Z_{j_M})`, with the
score-induced weights `w_j(θ) = s_θ(Z_j)/Σ_l s_θ(Z_l)`. -/
def wVStat {Θ Z : Type*} {M n : ℕ} (s : Θ × Z → ℝ) (H : Θ × (Fin M → Z) → ℝ) (z : Fin n → Z) (θ : Θ) : ℝ :=
  ∑ j : Fin M → Fin n, (∏ k, (s (θ, z (j k)) / ∑ l, s (θ, z l))) * H (θ, z ∘ j)

/-- `∫ H_θ dμ_θ^{⊗M}` for `μ_θ = g_θ P₀`, `g_θ = s_θ/c_θ`, `c_θ = ∫ s_θ dP₀`, in density form
`∫ ∏_k g_θ(t_k) H(θ, t) dP₀^{⊗M}(t)`. -/
def wPop {Θ Z : Type*} [MeasurableSpace Z] {M : ℕ} (P₀ : Measure Z) (s : Θ × Z → ℝ) (H : Θ × (Fin M → Z) → ℝ)
    (θ : Θ) : ℝ :=
  ∫ t, (∏ k, (s (θ, t k) / ∫ z, s (θ, z) ∂P₀)) * H (θ, t) ∂(Measure.pi fun _ : Fin M => P₀)

/-! ### otfd A: the cubic law on `H` -/

/-- The point `X_cub(v) = Σ_k λ_k v_k e_k` of `H` built from a coordinate sequence `v` (a genuine sum on the
support `|v_k| ≤ 1/2`, where `Σ λ_k² v_k² < ∞`). -/
def cubicPt {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (e : HilbertBasis ℕ ℝ H) (lam : ℕ → ℝ)
    (v : ℕ → ℝ) : H :=
  ∑' k, (lam k * v k) • e k

/-- The cubic law `μ^cub = 𝓛(Σ_k λ_k V_k e_k)`, `V_k` i.i.d. `Unif(−1/2, 1/2)` (the frozen `unifSym (1/2)`). -/
def cubicLawH {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
    (e : HilbertBasis ℕ ℝ H) (lam : ℕ → ℝ) : Measure H :=
  (Measure.infinitePi fun _ : ℕ => unifSym (1 / 2)).map (cubicPt e lam)

/-! ### otfd G: the reference and the recentred cost -/

/-- The Gaussian-direction reference point `V = τ G/‖G‖` (`def:reference`). -/
def refV {Ω H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (G : Ω → H) (τ : Ω → ℝ) (ω : Ω) : H :=
  τ ω • (‖G ω‖⁻¹ • G ω)

/-- `Π_K x = Σ_{k<K} ⟨φ_k, x⟩ φ_k`, the orthogonal projection onto `span{φ_1, …, φ_K}` (orthonormal `φ`). -/
def projK {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (φ : ℕ → H) (K : ℕ) (x : H) : H :=
  ∑ k ∈ Finset.range K, ⟪φ k, x⟫ • φ k

/-- The geodesic cost `c_s(v, x) = ½ D(E_m(sv), x)²`, with `Y v = E_m(sv)`. -/
def cCost {H 𝒳 : Type*} [PseudoMetricSpace 𝒳] (Y : H → 𝒳) (v : H) (x : 𝒳) : ℝ := dist (Y v) x ^ 2 / 2

/-- The recentred cost `c̃_s(v, x) = c_s(v, x) − ½ D(m, x)²` (`prop:firstmoment`). -/
def cTilde {H 𝒳 : Type*} [PseudoMetricSpace 𝒳] (m : 𝒳) (Y : H → 𝒳) (v : H) (x : 𝒳) : ℝ :=
  cCost Y v x - dist m x ^ 2 / 2

/-- `g̃(x) = −ε log ∫ e^{(f(v) − c̃_s(v,x))/ε} μ(dv)`. -/
def gTilde {H 𝒳 : Type*} [MeasurableSpace H] [PseudoMetricSpace 𝒳] (μ : Measure H) (m : 𝒳) (Y : H → 𝒳)
    (ε : ℝ) (f : H → ℝ) (x : 𝒳) : ℝ :=
  -ε * Real.log (∫ v, Real.exp ((f v - cTilde m Y v x) / ε) ∂μ)

/-! ### otfd C: the conditional rank map -/

section CondRank

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The exact column equation of the entropic response fit with grid weights `b_j = 1/m` (`m = M + 1` grid points,
`N = n + 1` retained responses): `g_j = ε log b_j − ε log Σ_i e^{(f_i − ‖u_j − Z_i‖²)/ε}`. -/
def ColumnEq {n M : ℕ} (ε : ℝ) (z : Fin (n + 1) → E) (f : Fin (n + 1) → ℝ) (u : Fin (M + 1) → E)
    (g : Fin (M + 1) → ℝ) : Prop :=
  ∀ j, g j = ε * Real.log (1 / ((M : ℝ) + 1)) - ε * Real.log (∑ i, Real.exp ((f i - ‖u j - z i‖ ^ 2) / ε))

/-- The potential of the rank map, `Φ(y) = (ε/2) log Σ_j exp((g_j − ‖u_j‖² + 2⟨u_j, y⟩)/ε)`. -/
def rankPot {M : ℕ} (ε : ℝ) (u : Fin M → E) (g : Fin M → ℝ) (y : E) : ℝ :=
  ε / 2 * Real.log (∑ j, Real.exp ((g j - ‖u j‖ ^ 2 + 2 * ⟪u j, y⟫) / ε))

/-- The conditional rank map `F̂(y) = Σ_j softmax_j((g_j − ‖y − u_j‖²)/ε) u_j` (`eq:cond-rank-map`). -/
def rankMap {M : ℕ} (ε : ℝ) (u : Fin M → E) (g : Fin M → ℝ) (y : E) : E :=
  ∑ j, (Real.exp ((g j - ‖y - u j‖ ^ 2) / ε) / ∑ l, Real.exp ((g l - ‖y - u l‖ ^ 2) / ε)) • u j

/-- The grid conjugate `φ(y) = max_j (⟨u_j, y⟩ − χ(u_j))`, `χ` the fitted quantile potential (frozen `lagPot`). -/
def gridConj {n M : ℕ} (z : Fin (n + 1) → E) (f : Fin (n + 1) → ℝ) (u : Fin (M + 1) → E) (y : E) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun j => ⟪u j, y⟫ - lagPot z f (u j)

/-- The continuum conjugate `X(y) = (χ + ι_𝒰)^*(y) = sup_{w ∈ 𝒰} (⟨w, y⟩ − χ(w))`. -/
def contConj {n : ℕ} (z : Fin (n + 1) → E) (f : Fin (n + 1) → ℝ) (U : Set E) (y : E) : ℝ :=
  sSup ((fun w => ⟪w, y⟫ - lagPot z f w) '' U)

end CondRank

/-! ### SB: the copula standardisation -/

/-- The marginal distribution functions applied coordinatewise, `S_μ(x) = (F_{μ,1}(x_1), …, F_{μ,d}(x_d))`. -/
def copStd {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun k => cdf (μ.map fun y : EuclideanSpace ℝ (Fin d) => y k) (x k)

/-- The coordinatewise marginal quantile functions, `S_μ^{-1}(u) = (F_{μ,1}^{-1}(u_1), …, F_{μ,d}^{-1}(u_d))`
(Tau Ceti's generalised inverse `inf{t : u ≤ F(t)}`). -/
def copInv {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) (u : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun k => (μ.map fun y : EuclideanSpace ℝ (Fin d) => y k).quantile (u k)

/-! ### TM: random Fourier features -/

/-- The phase law `Unif[0, 2π]`. -/
def unifCircle : Measure ℝ := ENNReal.ofReal (1 / (2 * Real.pi)) • volume.restrict (Icc 0 (2 * Real.pi))

/-- The phased random-feature kernel `ẑ(x, y) = z_r(x)ᵀ z_r(y) = (2κ²/r) Σ_j cos(ω_jᵀx + b_j) cos(ω_jᵀy + b_j)`,
`z_r(x) = κ √(2/r) [cos(ω_jᵀx + b_j)]_{j ≤ r}`. -/
def rffKernel {d r : ℕ} (κ : ℝ) (w : Fin r → EuclideanSpace ℝ (Fin d)) (b : Fin r → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  2 * κ ^ 2 / r * ∑ j, Real.cos (⟪w j, x⟫ + b j) * Real.cos (⟪w j, y⟫ + b j)

/-- The shift-invariant kernel through Bochner's representation, `k(x, y) = κ² ∫ cos(ωᵀ(x − y)) dΛ(ω)`. -/
def bochnerKernel {d : ℕ} (κ : ℝ) (Λ : Measure (EuclideanSpace ℝ (Fin d))) (x y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  κ ^ 2 * ∫ ω, Real.cos ⟪ω, x - y⟫ ∂Λ

namespace Claims

/-! ### otfd B: band edges -/

/-- `lem:band-pointwise-lower`, deterministic core: if `Q̂_n(u) → Q(u)` for `μ`-a.e. `u`, then for EVERY measurable
region `A` (so simultaneously for every level `p`, `A = A_{K,p}`) and every `v`,
`liminf_n ĥ_n(v) ≥ h^pop(v) ∈ (−∞, +∞]`; no bounded-range hypothesis. -/
def band_pointwise_lower_core : Prop :=
  ∀ (K : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin K))) (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (Qn : ℕ → EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)),
    (∀ᵐ u ∂μ, Tendsto (fun n => Qn n u) atTop (𝓝 (Q u))) →
      ∀ A : Set (EuclideanSpace ℝ (Fin K)), MeasurableSet A → ∀ v : EuclideanSpace ℝ (Fin K),
        popSupp μ A Q v ≤ liminf (fun n => fitSupp A (Qn n) v) atTop

/-- `lem:band-pointwise-lower` under `ass:fixedK-oos` (specialised as `FixedKOOS`), with `Q_{±,K}` a Brenier map `T`
and `Q̂_n` the fitted entropic maps: almost surely, simultaneously for every measurable region `A` and every `v`,
`liminf_n ĥ_n(v) ≥ h^pop(v)`. -/
def band_pointwise_lower : Prop :=
  ∀ (K : ℕ) (μ P : ProbabilityMeasure (EuclideanSpace ℝ (Fin K)))
    (μs : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin K))) (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω)
    [IsProbabilityMeasure Pr] (Z : ℕ → Ω → EuclideanSpace ℝ (Fin K)) (ε : ℕ → ℝ)
    (f : (n : ℕ) → Ω → Fin (n + 1) → ℝ) (T : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)),
    FixedKOOS μ P μs Pr Z ε f →
    IsKantorovichOptimalTransportMap (fun z => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
      (μ : Measure (EuclideanSpace ℝ (Fin K))) (P : Measure (EuclideanSpace ℝ (Fin K))) T →
      ∀ᵐ ω ∂Pr, ∀ A : Set (EuclideanSpace ℝ (Fin K)), MeasurableSet A → ∀ v : EuclideanSpace ℝ (Fin K),
        popSupp (μ : Measure (EuclideanSpace ℝ (Fin K))) A T v ≤
          liminf (fun n => fitSupp A (entMap (ε n) (fun i : Fin (n + 1) => Z i ω) (f n ω)) v) atTop

/-- `lem:band-containment-relative`: with bounded essential range of `Q` on `A` and a set `G` of full `μ|A`-measure
(the differentiability points), for every `η > 0` there are finitely many `u_1, …, u_L ∈ A ∩ G`, chosen from the
population objects only, such that for EVERY sequence of maps `Q̂_n`, every `n` and every `v`,
`ĥ_n(v) ≥ h^pop(v) − ‖v‖(η + ε_n(η))` with `ε_n(η) = max_l ‖Q̂_n(u_l) − Q(u_l)‖`, and `ε_n(η) → 0` whenever
`Q̂_n → Q` at every point of `G`. -/
def band_containment_relative : Prop :=
  ∀ (K : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin K))) (A G : Set (EuclideanSpace ℝ (Fin K)))
    (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)),
    MeasurableSet A → (∃ R : ℝ, ∀ᵐ u ∂μ.restrict A, ‖Q u‖ ≤ R) → (∀ᵐ u ∂μ.restrict A, u ∈ G) →
      ∀ η : ℝ, 0 < η → ∃ (L : ℕ) (u : Fin L → EuclideanSpace ℝ (Fin K)), (∀ l, u l ∈ A ∩ G) ∧
        ∀ Qn : ℕ → EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K),
          (∀ n v, popSupp μ A Q v ≤ fitSupp A (Qn n) v +
              ((‖v‖ * (η + (Finset.univ.sup fun l => ‖Qn n (u l) - Q (u l)‖₊ : ℝ≥0)) : ℝ) : EReal)) ∧
          ((∀ w ∈ G, Tendsto (fun n => Qn n w) atTop (𝓝 (Q w))) →
            Tendsto (fun n => ((Finset.univ.sup fun l => ‖Qn n (u l) - Q (u l)‖₊ : ℝ≥0) : ℝ)) atTop (𝓝 0))

/-- `thm:band-consistency-shell`, deterministic core (Steps 0–4 of the proof). Regions `A_p = {g ≤ τ_p}` of a
continuous, positively homogeneous, coercive gauge `g` (`g` a norm in the paper); `0 < τ_{p₀}`, `τ` nondecreasing on
`[p₀, 1 − δ]`; shell `Σ = {τ_{p₀} ≤ g ≤ τ_{1−δ}}`. Population: `Q` a subgradient selection of `χ` on a set `C ⊇ A_{1−δ}`
(`C = int 𝒰_K`), continuous on an open `O` with `Σ ⊆ O ⊆ C` ((b′), the "equivalently" form), and
`A_{1−δ} ⊆ supp μ`. Fitted: `Q̂` a subgradient selection of a finite convex `χ̂` on `ℝ^K`. Then for every
`p ∈ [p₀, 1 − δ]` and `v`: `h^pop_p(v) = max{⟨v, Q(w)⟩ : g(w) = τ_p}` (attained), and whenever
`‖Q̂ − Q‖ ≤ D` on `Σ`, `|ĥ_p(v) − h^pop_p(v)| ≤ ‖v‖ D`. -/
def band_consistency_shell : Prop :=
  ∀ (K : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin K))) (g : EuclideanSpace ℝ (Fin K) → ℝ)
    (C O : Set (EuclideanSpace ℝ (Fin K))) (χ χh : EuclideanSpace ℝ (Fin K) → ℝ)
    (Q Qh : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (τ : ℝ → ℝ) (p₀ δ : ℝ),
    1 ≤ K → Continuous g → (∀ (c : ℝ) (u : EuclideanSpace ℝ (Fin K)), 0 ≤ c → g (c • u) = c * g u) →
    (∃ c : ℝ, 0 < c ∧ ∀ u, c * ‖u‖ ≤ g u) →
    0 < p₀ → p₀ ≤ 1 - δ → 0 < τ p₀ → MonotoneOn τ (Icc p₀ (1 - δ)) →
    {u | g u ≤ τ (1 - δ)} ⊆ C → IsOpen O → {u | τ p₀ ≤ g u ∧ g u ≤ τ (1 - δ)} ⊆ O → O ⊆ C →
    (∀ u ∈ C, ∀ y ∈ C, χ u + ⟪Q u, y - u⟫ ≤ χ y) → ContinuousOn Q O →
    (∀ U : Set (EuclideanSpace ℝ (Fin K)), IsOpen U → (U ∩ {u | g u ≤ τ (1 - δ)}).Nonempty → 0 < μ U) →
    (∀ u y, χh u + ⟪Qh u, y - u⟫ ≤ χh y) →
      ∀ p ∈ Icc p₀ (1 - δ), ∀ v : EuclideanSpace ℝ (Fin K),
        (∃ w, g w = τ p ∧ popSupp μ {u | g u ≤ τ p} Q v = ((⟪v, Q w⟫ : ℝ) : EReal) ∧
          ∀ w', g w' = τ p → ⟪v, Q w'⟫ ≤ ⟪v, Q w⟫) ∧
        ∀ D : ℝ, (∀ u, τ p₀ ≤ g u → g u ≤ τ (1 - δ) → ‖Qh u - Q u‖ ≤ D) →
          fitSupp {u | g u ≤ τ p} Qh v ≤ popSupp μ {u | g u ≤ τ p} Q v + ((‖v‖ * D : ℝ) : EReal) ∧
          popSupp μ {u | g u ≤ τ p} Q v ≤ fitSupp {u | g u ≤ τ p} Qh v + ((‖v‖ * D : ℝ) : EReal)

/-- `prop:band-injectivity` (ii): for `ε > 0`, the entropic out-of-sample map `Q̂ = entMap ε Z f` (`M_K = I`) is
injective on `ℝ^K` iff the data points affinely span `ℝ^K`; if they do not, `Q̂` is constant along a fixed line;
and spanning requires `n ≥ K + 1`. -/
def band_injectivity_entropic : Prop :=
  ∀ (K N : ℕ) (ε : ℝ) (z : Fin N → EuclideanSpace ℝ (Fin K)) (f : Fin N → ℝ), 1 ≤ K → 0 < ε →
    (Function.Injective (entMap ε z f) ↔ affineSpan ℝ (range z) = ⊤) ∧
    (affineSpan ℝ (range z) ≠ ⊤ → ∃ x : EuclideanSpace ℝ (Fin K), x ≠ 0 ∧
        ∀ (u : EuclideanSpace ℝ (Fin K)) (t : ℝ), entMap ε z f (u + t • x) = entMap ε z f u) ∧
    (affineSpan ℝ (range z) = ⊤ → K + 1 ≤ N)

/-- `prop:band-injectivity` (i), the inclusion `Q̂(∂A) ⊆ ∂Q̂(A)`: for `Q̂` continuous and injective on an open
`U ⊇ A`, `A` closed, the image of the reference contour lies in the boundary of the image region. -/
def band_injectivity_boundary : Prop :=
  ∀ (K : ℕ) (Qh : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (U A : Set (EuclideanSpace ℝ (Fin K))),
    IsOpen U → A ⊆ U → IsClosed A → ContinuousOn Qh U → InjOn Qh U → Qh '' frontier A ⊆ frontier (Qh '' A)

/-! ### ICL: uniform laws for V-statistics -/

/-- `lem:cond-vstat`: `A` compact metric, `ψ` continuous on `A × 𝒵^M`, `𝒵` compact metric, the pool an i.i.d. `P₀`
sequence (nested samples, `as:compact`): almost surely `sup_{a ∈ A} |P_n^{⊗M} ψ_a − P₀^{⊗M} ψ_a| → 0`. -/
def cond_vstat : Prop :=
  ∀ (A Z Ω : Type) [MetricSpace A] [CompactSpace A] [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (P₀ : Measure Z)
    [IsProbabilityMeasure P₀] (M : ℕ) (ψ : A × (Fin M → Z) → ℝ) (Zs : ℕ → Ω → Z),
    Continuous ψ → (∀ i, Measurable (Zs i)) → iIndepFun Zs P → (∀ i, P.map (Zs i) = P₀) →
      ∀ᵐ ω ∂P, TendstoUniformly (fun n a => vStat ψ (fun i : Fin n => Zs i ω) a)
        (fun a => ∫ t, ψ (a, t) ∂(Measure.pi fun _ : Fin M => P₀)) atTop

/-- `lem:e-vstat`: `Θ` compact metric, `s` continuous with `0 < s₋ ≤ s ≤ s₊` (`as:score`), `H` continuous on
`Θ × 𝒵^M`: almost surely `sup_θ |∫ H_θ dμ_{θ,n}^{⊗M} − ∫ H_θ dμ_θ^{⊗M}| → 0`. -/
def e_vstat : Prop :=
  ∀ (Θ Z Ω : Type) [MetricSpace Θ] [CompactSpace Θ] [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (P₀ : Measure Z)
    [IsProbabilityMeasure P₀] (M : ℕ) (s : Θ × Z → ℝ) (H : Θ × (Fin M → Z) → ℝ) (sLo sHi : ℝ) (Zs : ℕ → Ω → Z),
    Continuous s → Continuous H → 0 < sLo → (∀ x, sLo ≤ s x ∧ s x ≤ sHi) →
    (∀ i, Measurable (Zs i)) → iIndepFun Zs P → (∀ i, P.map (Zs i) = P₀) →
      ∀ᵐ ω ∂P, TendstoUniformly (fun n θ => wVStat s H (fun i : Fin n => Zs i ω) θ) (wPop P₀ s H) atTop

/-! ### ICL: consistency of policies and inference (cores) -/

/-- `thm:cond-consistency`, Step 1 of the proof (with and without replacement), with the frozen Wave 11b objects
(`collision` = `p`, `swoExp` = `E[· | D]`, the context law `Π_w`, `iidExp` = `E` under `w^{⊗M}`): for a probability
vector `w` on the pool and `f` with values in `[0, B]` on index tuples, `p < 1`, `|E[f | D] − E f| ≤ B p/(1 − p)`, and
`p ≤ C(M,2) c` whenever every `w_j ≤ c` (the union bound `p ≤ C(M,2) Σ_j w_j²` is the frozen Wave 11b
`swor_collision`, not restated). -/
def cond_consistency_replacement : Prop :=
  ∀ (n M : ℕ) (w : Fin n → ℝ) (f : (Fin M → Fin n) → ℝ) (B : ℝ),
    (∀ j, 0 ≤ w j) → ∑ j, w j = 1 → (∀ t, 0 ≤ f t ∧ f t ≤ B) → StatFormal.Wave11b.collision w M < 1 →
      |StatFormal.Wave11b.swoExp w M f - StatFormal.Wave11b.iidExp w M f| ≤
          B * StatFormal.Wave11b.collision w M / (1 - StatFormal.Wave11b.collision w M) ∧
        ∀ c : ℝ, (∀ j, w j ≤ c) → StatFormal.Wave11b.collision w M ≤ (M.choose 2 : ℝ) * c

/-- `thm:cond-consistency` (i), Step 5 of the proof: on a compact parameter set, if `sup_Θ |J_{n,m} − J| → 0` and
`sup_Θ |J_pool − J| → 0` (along any filter, so `n, m → ∞` in any manner) and `θ̂` minimises `J_{n,m}` up to
`ε_opt → 0`, then `J(θ̂) → min_Θ J` and `J_pool(θ̂) → min_Θ J`. -/
def cond_consistency_values : Prop :=
  ∀ (Θ ι : Type) [TopologicalSpace Θ] [CompactSpace Θ] [Nonempty Θ] (l : Filter ι) (J : Θ → ℝ)
    (Jnm Jpool : ι → Θ → ℝ) (θh : ι → Θ) (εopt : ι → ℝ),
    Continuous J → TendstoUniformly Jnm J l → TendstoUniformly Jpool J l → Tendsto εopt l (𝓝 0) →
    (∀ i θ, Jnm i (θh i) ≤ Jnm i θ + εopt i) →
      ∃ θs : Θ, (∀ θ, J θs ≤ J θ) ∧ Tendsto (fun i => J (θh i)) l (𝓝 (J θs)) ∧
        Tendsto (fun i => Jpool i (θh i)) l (𝓝 (J θs))

/-- `cor:inference`, the influence function of the plug-in at a fixed parameter: for `Ψ(μ) = Γ(∫ φ dμ)` and
`μ = (s/c) P₀`, `c = ∫ s dP₀ > 0`, `m = ∫ φ dμ = c⁻¹ ∫ s φ dP₀`, the map `(a, b) ↦ Γ(a/b)` (so that
`Ψ(μ_{θ,n}) = Γ(P_n(sφ)/P_n s)`) is differentiable at `(P₀(sφ), P₀ s)` whenever `Γ` is differentiable at `m`, and
its derivative applied to `(ν(sφ) − P₀(sφ), ν s − P₀ s)` is `∫ τ dν` for every measure `ν` integrating `s, sφ`,
where `τ = (s/c) ∇Γ(m)ᵀ(φ − m)` has `∫ τ dP₀ = 0`. -/
def inference_linear : Prop :=
  ∀ (Z : Type) [MeasurableSpace Z] (P₀ : Measure Z) (k : ℕ) (φ : Z → (Fin k → ℝ)) (s : Z → ℝ)
    (Γ : (Fin k → ℝ) → ℝ) (DΓ : (Fin k → ℝ) →L[ℝ] ℝ),
    Integrable s P₀ → Integrable (fun z => s z • φ z) P₀ → 0 < ∫ z, s z ∂P₀ →
    HasFDerivAt Γ DΓ ((∫ z, s z ∂P₀)⁻¹ • ∫ z, s z • φ z ∂P₀) →
      ∃ L : (Fin k → ℝ) × ℝ →L[ℝ] ℝ,
        HasFDerivAt (fun q : (Fin k → ℝ) × ℝ => Γ (q.2⁻¹ • q.1)) L
            (∫ z, s z • φ z ∂P₀, ∫ z, s z ∂P₀) ∧
          (∀ ν : Measure Z, Integrable s ν → Integrable (fun z => s z • φ z) ν →
            L (∫ z, s z • φ z ∂ν - ∫ z, s z • φ z ∂P₀, ∫ z, s z ∂ν - ∫ z, s z ∂P₀) =
              ∫ z, s z / (∫ x, s x ∂P₀) * DΓ (φ z - (∫ x, s x ∂P₀)⁻¹ • ∫ x, s x • φ x ∂P₀) ∂ν) ∧
          ∫ z, s z / (∫ x, s x ∂P₀) * DΓ (φ z - (∫ x, s x ∂P₀)⁻¹ • ∫ x, s x • φ x ∂P₀) ∂P₀ = 0

/-! ### otfd A: the coherent limit for the cubic reference -/

/-- `cor:ghs-tukey-degeneracy`, cubic law: `TD_H(u; μ^cub) = 0` for `μ^cub`-almost every `u` (`λ_k > 0`,
`Σ λ_k² < ∞`, `(e_k)` an orthonormal basis of `H`). -/
def ghs_cubic_ae_zero : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    [BorelSpace H] (e : HilbertBasis ℕ ℝ H) (lam : ℕ → ℝ),
    (∀ k, 0 < lam k) → Summable (fun k => lam k ^ 2) →
      ∀ᵐ u ∂cubicLawH e lam, tukeyDepthH (cubicLawH e lam) u = 0

/-- `cor:ghs-tukey-degeneracy`, cubic law: `TD_H(0; μ^cub) = 1/2`. -/
def ghs_cubic_center : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    [BorelSpace H] (e : HilbertBasis ℕ ℝ H) (lam : ℕ → ℝ),
    (∀ k, 0 < lam k) → Summable (fun k => lam k ^ 2) → tukeyDepthH (cubicLawH e lam) 0 = 1 / 2

/-! ### otfd R: Cameron–Martin nullity -/

/-- `lem:cm-null`: `G ∼ N(0, Σ)` in Karhunen–Loève form (`Σ e_k = λ_k e_k`, `λ_k > 0`, `Σ λ_k < ∞`, `(e_k)` an
orthonormal basis, `⟨e_k, G⟩ = √λ_k ξ_k` with `ξ_k` i.i.d. `N(0,1)`), `Σ^{1/2}` any bounded `S` with
`S e_k = √λ_k e_k`, and `W > 0` almost surely (no integrability, no independence needed): the event
`{√W G ∈ ran Σ^{1/2}}` has (outer) probability `0`, so `μ(ran Σ^{1/2}) = 0` for `μ = 𝓛(√W G)`. -/
def cm_null : Prop :=
  ∀ (H Ω : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace Ω]
    (Pr : Measure Ω) [IsProbabilityMeasure Pr] (e : HilbertBasis ℕ ℝ H) (lam : ℕ → ℝ) (S : H →L[ℝ] H)
    (ξ : ℕ → Ω → ℝ) (G : Ω → H) (W : Ω → ℝ),
    (∀ k, 0 < lam k) → Summable lam → (∀ k, S (e k) = Real.sqrt (lam k) • e k) →
    (∀ k, Measurable (ξ k)) → iIndepFun ξ Pr → (∀ k, Pr.map (ξ k) = gaussianReal 0 1) →
    (∀ᵐ ω ∂Pr, ∀ k, ⟪e k, G ω⟫ = Real.sqrt (lam k) * ξ k ω) → (∀ᵐ ω ∂Pr, 0 < W ω) →
      Pr {ω | Real.sqrt (W ω) • G ω ∈ Set.range S} = 0

/-! ### otfd G: properties of the reference, vanishing temperature, first moments, the flat limit -/

/-- `prop:reference` (a) and (c): for `G ≠ 0` a.s. and `τ ∼ Unif[0,1]` independent of `G`, `‖V‖ = τ` a.s., so
`μ(‖v‖ ≤ r) = r` on `[0,1]`; the sign `V/‖V‖` is independent of the radius `‖V‖`; `‖V‖ ≤ 1` a.s. and, whenever
`D(m, E_m(sv)) ≤ s‖v‖`, `D(m, Y) ≤ s` a.s. for `Y = E_m(sV)`. -/
def reference_calibration : Prop :=
  ∀ (Ω H 𝒳 : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [PseudoMetricSpace 𝒳]
    (G : Ω → H) (τ : Ω → ℝ) (m : 𝒳) (Em : H → 𝒳) (s : ℝ),
    Measurable G → Measurable τ → IndepFun τ G Pr → Pr.map τ = volume.restrict (Icc 0 1) →
    (∀ᵐ ω ∂Pr, G ω ≠ 0) → (∀ v, dist m (Em (s • v)) ≤ s * ‖v‖) →
      (∀ᵐ ω ∂Pr, ‖refV G τ ω‖ = τ ω) ∧
      (∀ r ∈ Icc (0 : ℝ) 1, Pr {ω | ‖refV G τ ω‖ ≤ r} = ENNReal.ofReal r) ∧
      IndepFun (fun ω => ‖refV G τ ω‖) (fun ω => ‖refV G τ ω‖⁻¹ • refV G τ ω) Pr ∧
      (∀ᵐ ω ∂Pr, ‖refV G τ ω‖ ≤ 1 ∧ dist m (Em (s • refV G τ ω)) ≤ s)

/-- `prop:reference` (b): if `G` lies a.s. in the closed span of the orthonormal eigenfields `φ_k` (as for
`G = Σ_k √λ_k Z_k φ_k`), `G ≠ 0` a.s. and `τ ∈ [0,1]`, then `E‖V − Π_K V‖ → 0` and, for the rank-`K` sieve
`V_K = τ Π_K G/‖Π_K G‖`, `E‖V − V_K‖ → 0`. -/
def reference_truncation : Prop :=
  ∀ (Ω H : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (φ : ℕ → H) (G : Ω → H) (τ : Ω → ℝ),
    Orthonormal ℝ φ → Measurable G → Measurable τ → (∀ᵐ ω ∂Pr, τ ω ∈ Icc (0 : ℝ) 1) →
    (∀ᵐ ω ∂Pr, G ω ≠ 0) → (∀ᵐ ω ∂Pr, HasSum (fun k => ⟪φ k, G ω⟫ • φ k) (G ω)) →
      Tendsto (fun K => ∫ ω, ‖refV G τ ω - projK φ K (refV G τ ω)‖ ∂Pr) atTop (𝓝 0) ∧
      Tendsto (fun K => ∫ ω, ‖refV G τ ω - refV (fun ω => projK φ K (G ω)) τ ω‖ ∂Pr) atTop (𝓝 0)

/-- `thm:epszero` (a), discrete marginals: every limit point, as `ε ↓ 0`, of entropic plans
`π_ε ∈ argmin_{Π(a,b)} ⟨C, π⟩ + ε KL(π | a ⊗ b)` is an optimal plan of the unregularised problem. -/
def epszero_discrete : Prop :=
  ∀ (n m : ℕ) (a : Fin n → ℝ) (b : Fin m → ℝ) (C : Fin n → Fin m → ℝ) (πε : ℝ → Fin n → Fin m → ℝ)
    (πbar : Fin n → Fin m → ℝ), (∀ i, 0 < a i) → (∀ j, 0 < b j) →
    (∀ ε > 0, IsRegMin (transportPolytope a b) C (entReg a b ε) (πε ε)) → MapClusterPt πbar (𝓝[>] 0) πε →
      πbar ∈ transportPolytope a b ∧ ∀ π ∈ transportPolytope a b, frob C πbar ≤ frob C π

/-- `prop:firstmoment` (a), pointwise: `|c̃_s(v, x)| ≤ s‖v‖ D(m, x) + ½ s²‖v‖²` whenever `D(m, E_m(sv)) ≤ s‖v‖`. -/
def firstmoment_cost : Prop :=
  ∀ (H 𝒳 : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [PseudoMetricSpace 𝒳] (m : 𝒳) (Y : H → 𝒳)
    (s : ℝ), 0 ≤ s → (∀ v, dist m (Y v) ≤ s * ‖v‖) →
      ∀ v x, |cTilde m Y v x| ≤ s * ‖v‖ * dist m x + s ^ 2 * ‖v‖ ^ 2 / 2

/-- `prop:firstmoment` (a), integrated: if `E D(m, X) < ∞` (a condition that holds for every base point `m'` once it
holds for one), then for every coupling `π` with second marginal `P` and first marginal carried by the unit ball,
`c̃_s` is `π`-integrable and `|∫ c̃_s dπ| ≤ P(β)`, `β(x) = s D(m, x) + ½ s²`. -/
def firstmoment_plan : Prop :=
  ∀ (H 𝒳 : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    [SecondCountableTopology H] [PseudoMetricSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳]
    [SecondCountableTopology 𝒳] (m : 𝒳) (Y : H → 𝒳) (s : ℝ) (P : Measure 𝒳) [IsProbabilityMeasure P]
    (π : Measure (H × 𝒳)) [IsProbabilityMeasure π],
    0 ≤ s → (∀ v, dist m (Y v) ≤ s * ‖v‖) → Continuous Y → π.map Prod.snd = P → (∀ᵐ p ∂π, ‖p.1‖ ≤ 1) →
    Integrable (fun x => dist m x) P →
      (∀ m' : 𝒳, Integrable (fun x => dist m' x) P) ∧ Integrable (fun p => cTilde m Y p.1 p.2) π ∧
        |∫ p, cTilde m Y p.1 p.2 ∂π| ≤ ∫ x, (s * dist m x + s ^ 2 / 2) ∂P

/-- `prop:firstmoment` (b), for every first potential `f` with `Z_f = ∫ e^{f/ε} dμ < ∞` and every curve `x`:
`e^{(f − c̃_s(·,x))/ε}` is `μ`-integrable with positive integral, `|g̃(x) + ε log Z_f| ≤ β(x)`, and the kernel
`e^{(f + g̃(x) − c̃_s)/ε} μ` equals `e^{(f − c_s(·,x))/ε} μ / ∫ e^{(f − c_s(·,x))/ε} dμ` and is a probability
measure. -/
def firstmoment_kernel : Prop :=
  ∀ (H 𝒳 : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    [PseudoMetricSpace 𝒳] (μ : Measure H) [IsProbabilityMeasure μ] (m : 𝒳) (Y : H → 𝒳) (s ε : ℝ) (f : H → ℝ),
    0 ≤ s → 0 < ε → (∀ v, dist m (Y v) ≤ s * ‖v‖) → Continuous Y → (∀ᵐ v ∂μ, ‖v‖ ≤ 1) → Measurable f →
    Integrable (fun v => Real.exp (f v / ε)) μ → ∀ x : 𝒳,
      Integrable (fun v => Real.exp ((f v - cTilde m Y v x) / ε)) μ ∧
      0 < ∫ v, Real.exp ((f v - cTilde m Y v x) / ε) ∂μ ∧
      |gTilde μ m Y ε f x + ε * Real.log (∫ v, Real.exp (f v / ε) ∂μ)| ≤ s * dist m x + s ^ 2 / 2 ∧
      (∀ v, Real.exp ((f v + gTilde μ m Y ε f x - cTilde m Y v x) / ε) =
        Real.exp ((f v - cCost Y v x) / ε) / ∫ w, Real.exp ((f w - cCost Y w x) / ε) ∂μ) ∧
      ∫ v, Real.exp ((f v + gTilde μ m Y ε f x - cTilde m Y v x) / ε) ∂μ = 1

/-- `cor:onlyL2` (b), eigenfunction step and `eq:H1cov`: let `ι : H¹ → H` be a bounded injective embedding and
`D : H¹ → H` a bounded linear map (the derivative along `m`), `Y` a random element of `H¹` with `E‖Y‖²_{H¹} < ∞`,
and `φ` a unit eigenvector of the covariance of `ιY` with eigenvalue `λ > 0` (weak form). Then `φ = ιψ` for some
`ψ ∈ H¹`, `Cov(⟨Dψ, DY⟩, ⟨φ, ιY⟩) = λ‖Dψ‖²`, and if `⟨Dψ, DY⟩ − c⟨φ, ιY⟩` is a.s. constant then `‖Dψ‖² = c`
((b2) with `c = η₁/η − 1`). -/
def onlyL2_dirichlet : Prop :=
  ∀ (Ω H₁ H : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] [NormedAddCommGroup H₁]
    [InnerProductSpace ℝ H₁] [CompleteSpace H₁] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (ι D : H₁ →L[ℝ] H) (Y : Ω → H₁) (φ : H) (lam c : ℝ),
    Function.Injective ι → AEStronglyMeasurable Y Pr → Integrable (fun ω => ‖Y ω‖ ^ 2) Pr → ‖φ‖ = 1 → 0 < lam →
    (∀ w : H, cov[fun ω => ⟪φ, ι (Y ω)⟫, fun ω => ⟪w, ι (Y ω)⟫; Pr] = lam * ⟪φ, w⟫) →
      ∃ ψ : H₁, ι ψ = φ ∧
        cov[fun ω => ⟪D ψ, D (Y ω)⟫, fun ω => ⟪φ, ι (Y ω)⟫; Pr] = lam * ‖D ψ‖ ^ 2 ∧
        ((∃ a : ℝ, ∀ᵐ ω ∂Pr, ⟪D ψ, D (Y ω)⟫ - c * ⟪φ, ι (Y ω)⟫ = a) → ‖D ψ‖ ^ 2 = c)

/-- `cor:onlyL2` (c): for any law `μ' ≠ μ` and any couplings `π ∈ Π(μ, P)`, `π' ∈ Π(μ', P)`,
`TV(π, π') ≥ TV(μ, μ') > 0` (so no plan with another reference is a flat limit of the geodesic route). -/
def onlyL2_reference : Prop :=
  ∀ (H 𝒳 : Type) [MeasurableSpace H] [MeasurableSpace 𝒳] (μ μ' : Measure H) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] (π π' : Measure (H × 𝒳)) [IsProbabilityMeasure π] [IsProbabilityMeasure π'],
    π.map Prod.fst = μ → π'.map Prod.fst = μ' → μ ≠ μ' → tv μ μ' ≤ tv π π' ∧ 0 < tv μ μ'

/-! ### otfd C: conditional rank-map consistency -/

/-- `lem:cond-rank-consistency`, Steps 1–3 of the proof (deterministic, one fit): for an exact column equation,
responses in `B̄(0, R)`, and a grid in `𝒰` that is `δ`-dense in `𝒰`: `|Φ − φ| ≤ ½ ε log(mN)`,
`0 ≤ X − φ ≤ (‖y‖ + R) δ`, and `F̂(y)` is a subgradient of `Φ` at every `y` (so `Φ` is convex and `F̂ = ∇Φ`
wherever `Φ` is differentiable). -/
def cond_rank_sandwich : Prop :=
  ∀ (K n M : ℕ) (ε R δ : ℝ) (z : Fin (n + 1) → EuclideanSpace ℝ (Fin K)) (f : Fin (n + 1) → ℝ)
    (u : Fin (M + 1) → EuclideanSpace ℝ (Fin K)) (g : Fin (M + 1) → ℝ) (U : Set (EuclideanSpace ℝ (Fin K))),
    0 < ε → ColumnEq ε z f u g → (∀ i, ‖z i‖ ≤ R) → (∀ j, u j ∈ U) → (∀ w ∈ U, ∃ j, ‖w - u j‖ ≤ δ) →
      ∀ y, |rankPot ε u g y - gridConj z f u y| ≤ ε / 2 * Real.log (((M : ℝ) + 1) * ((n : ℝ) + 1)) ∧
        gridConj z f u y ≤ contConj z f U y ∧ contConj z f U y - gridConj z f u y ≤ (‖y‖ + R) * δ ∧
        ∀ y', rankPot ε u g y + ⟪rankMap ε u g y, y' - y⟫ ≤ rankPot ε u g y'

/-- `lem:cond-rank-consistency`, CONDITIONAL on Step 4 of the proof (the conjugate-potential convergence supplied by
`prop:conditional-potentials`: after normalisation, `X_n − c_n → X` pointwise for a finite `X`): if
`ε_n log(N_n m_n) → 0` and the grids are `δ_n`-dense in `𝒰` with `δ_n → 0`, then `F̂_n(y) → ∇X(y)` at every
differentiability point `y` of `X`, hence `P`-a.e. for every `P ≪ Leb`. -/
def cond_rank_consistency : Prop :=
  ∀ (K : ℕ) (n M : ℕ → ℕ) (ε δ : ℕ → ℝ) (R : ℝ) (z : ∀ k, Fin (n k + 1) → EuclideanSpace ℝ (Fin K))
    (f : ∀ k, Fin (n k + 1) → ℝ) (u : ∀ k, Fin (M k + 1) → EuclideanSpace ℝ (Fin K)) (g : ∀ k, Fin (M k + 1) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin K))) (X : EuclideanSpace ℝ (Fin K) → ℝ) (c : ℕ → ℝ)
    (P : Measure (EuclideanSpace ℝ (Fin K))),
    (∀ k, 0 < ε k) → Tendsto (fun k => ε k * Real.log (((M k : ℝ) + 1) * ((n k : ℝ) + 1))) atTop (𝓝 0) →
    Tendsto δ atTop (𝓝 0) → (∀ k, ColumnEq (ε k) (z k) (f k) (u k) (g k)) → (∀ k i, ‖z k i‖ ≤ R) →
    (∀ k j, u k j ∈ U) → (∀ k, ∀ w ∈ U, ∃ j, ‖w - u k j‖ ≤ δ k) →
    (∀ y, Tendsto (fun k => contConj (z k) (f k) U y - c k) atTop (𝓝 (X y))) → P ≪ volume →
      (∀ y, DifferentiableAt ℝ X y → Tendsto (fun k => rankMap (ε k) (u k) (g k) y) atTop (𝓝 (gradient X y))) ∧
        ∀ᵐ y ∂P, Tendsto (fun k => rankMap (ε k) (u k) (g k) y) atTop (𝓝 (gradient X y))

/-- `lem:cond-rank-consistency`, UNCONDITIONAL (Step 4 discharged through the certified OTFD wave-L4
`cond_potentials_weighted`, i.e. `prop:conditional-potentials` under the verbatim `ass:conditional-oos`): let
`RefLaw` hold for `μ_K` and `𝒰_K` (`μ_K ≪ Leb`, carried by the compact convex `𝒰_K`, `int 𝒰_K ⊆ supp μ_K`), let
`P = P_{K,x}` have a first moment with population map `Q` (Borel, `Q#μ_K = P`, `μ_K`-a.e. cyclically monotone), and
let the fits satisfy `WeightedFit` (grids `α_n ⇀ μ_K`, weighted targets `ν_n ⇀ P`, hard semi-dual gaps `ζ_n → 0`)
with `χ_n` the Laguerre potential of the entropic duals `f_n` on the retained responses (also playing `g_n`), the
reference grids `α_n = m_n⁻¹ Σ_j δ_{u_j}` in `𝒰_K`, exact column equations, responses in `B̄(0, R)` and
`ε_n log(m_n N_n) → 0`. Then a normalised population quantile potential `χ` exists (convex on `int 𝒰_K`,
`∇χ = Q` `μ_K`-a.e., `inf χ = 0`), and for every such `χ`, with the population rank potential
`X(y) = sup_{w ∈ int 𝒰_K} (⟨w, y⟩ − χ(w))`, `F̂_n(y) → ∇X(y)` at every differentiability point `y` of `X`, hence
`ρ`-a.e. for every `ρ ≪ Leb` (in particular `ρ = P_{K,x}` when it is absolutely continuous). -/
def cond_rank_consistency_uncond : Prop :=
  ∀ (K : ℕ) (n M : ℕ → ℕ) (ε : ℕ → ℝ) (R : ℝ) (z : ∀ k, Fin (n k + 1) → EuclideanSpace ℝ (Fin K))
    (f : ∀ k, Fin (n k + 1) → ℝ) (u : ∀ k, Fin (M k + 1) → EuclideanSpace ℝ (Fin K)) (g : ∀ k, Fin (M k + 1) → ℝ)
    (μ P : ProbabilityMeasure (EuclideanSpace ℝ (Fin K))) (U : Set (EuclideanSpace ℝ (Fin K)))
    (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (α ν : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin K))) (ζ : ℕ → ℝ) (ρ : Measure (EuclideanSpace ℝ (Fin K))),
    StatFormal.OTFD.WaveL3.RefLaw (μ : Measure (EuclideanSpace ℝ (Fin K))) U →
    StatFormal.OTFD.WaveL3.Mom1 (P : Measure (EuclideanSpace ℝ (Fin K))) ≠ ∞ → Measurable Q →
    (μ : Measure (EuclideanSpace ℝ (Fin K))).map Q = P →
    StatFormal.OTFD.WaveL1.IsCMMapAE (μ : Measure (EuclideanSpace ℝ (Fin K))) Q →
    StatFormal.OTFD.WaveL4.WeightedFit μ P U α ν (fun k => lagPot (z k) (f k)) (fun k => lagPot (z k) (f k)) ζ →
    (∀ k, (α k : Measure (EuclideanSpace ℝ (Fin K))) =
      ∑ j, ENNReal.ofReal (1 / ((M k : ℝ) + 1)) • Measure.dirac (u k j)) → (∀ k j, u k j ∈ U) →
    (∀ k, 0 < ε k) → Tendsto (fun k => ε k * Real.log (((M k : ℝ) + 1) * ((n k : ℝ) + 1))) atTop (𝓝 0) →
    (∀ k, ColumnEq (ε k) (z k) (f k) (u k) (g k)) → (∀ k i, ‖z k i‖ ≤ R) → ρ ≪ volume →
      (∃ χ : EuclideanSpace ℝ (Fin K) → ℝ, ConvexOn ℝ (interior U) χ ∧
          Q =ᵐ[(μ : Measure (EuclideanSpace ℝ (Fin K)))] gradient χ ∧ IsGLB (χ '' interior U) 0) ∧
        ∀ χ : EuclideanSpace ℝ (Fin K) → ℝ, ConvexOn ℝ (interior U) χ →
          Q =ᵐ[(μ : Measure (EuclideanSpace ℝ (Fin K)))] gradient χ → IsGLB (χ '' interior U) 0 →
          (∀ y, DifferentiableAt ℝ (fun y' => sSup ((fun w => ⟪w, y'⟫ - χ w) '' interior U)) y →
            Tendsto (fun k => rankMap (ε k) (u k) (g k) y) atTop
              (𝓝 (gradient (fun y' => sSup ((fun w => ⟪w, y'⟫ - χ w) '' interior U)) y))) ∧
          ∀ᵐ y ∂ρ, Tendsto (fun k => rankMap (ε k) (u k) (g k) y) atTop
            (𝓝 (gradient (fun y' => sSup ((fun w => ⟪w, y'⟫ - χ w) '' interior U)) y))

/-! ### SB: common copula, arbitrary marginals -/

/-- `cor:field-cop`, standardisation: for a law `μ` on `ℝ^d` with continuous (atomless) marginals, the copula
measure `C_μ = (S_μ)_#μ` has uniform marginals, and `S_μ` standardises `μ` onto `C_μ` in the sense of
`def:standardisable`(i) (frozen `Standardises`: measurable, `(S_μ)_#μ = C_μ`, inverse `S_μ^{-1}` a.e. on both
sides). -/
def field_cop_standardises : Prop :=
  ∀ (d : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ],
    (∀ k (t : ℝ), (μ.map fun y : EuclideanSpace ℝ (Fin d) => y k) {t} = 0) →
      (∀ k, ((μ.map (copStd μ)).map fun u : EuclideanSpace ℝ (Fin d) => u k) = volume.restrict (Icc 0 1)) ∧
        Standardises μ (μ.map (copStd μ)) (copStd μ) (copInv μ)

/-- `cor:field-cop`, exactness of the coordinatewise quantile repair: if `R_s` and `ν` have continuous marginals
and the same copula (`(S_{R_s})_#R_s = (S_ν)_#ν`; the marginals are arbitrary), then
`T_s = S_ν^{-1} ∘ S_{R_s}`, i.e. `T_s(x) = (G_1^{-1}(F_{s,1}(x_1)), …, G_d^{-1}(F_{s,d}(x_d)))`, satisfies
`(T_s)_#R_s = ν` exactly. -/
def field_cop_exact : Prop :=
  ∀ (d : ℕ) (R ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure R] [IsProbabilityMeasure ν],
    (∀ k (t : ℝ), (R.map fun y : EuclideanSpace ℝ (Fin d) => y k) {t} = 0) →
    (∀ k (t : ℝ), (ν.map fun y : EuclideanSpace ℝ (Fin d) => y k) {t} = 0) →
    R.map (copStd R) = ν.map (copStd ν) → R.map (copInv ν ∘ copStd R) = ν

/-! ### TM: uniform random-feature approximation (finite-set core) -/

/-- `lem:rffkernel`, unbiasedness of the phased features: for `ω ∼ Λ` and `b ∼ Unif[0, 2π]` independent,
`E[2 cos(ωᵀx + b) cos(ωᵀy + b)] = E cos(ωᵀ(x − y))`, so `E ẑ(x, y) = k(x, y)`. -/
def rff_unbiased : Prop :=
  ∀ (d : ℕ) (Λ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure Λ] (β : Measure ℝ)
    [IsProbabilityMeasure β], β = unifCircle → ∀ x y : EuclideanSpace ℝ (Fin d),
      ∫ p, 2 * Real.cos (⟪p.1, x⟫ + p.2) * Real.cos (⟪p.1, y⟫ + p.2) ∂(Λ.prod β) = ∫ ω, Real.cos ⟪ω, x - y⟫ ∂Λ

/-- `lem:rffkernel` on a finite set of pairs (Hoeffding and a union bound; the supremum over the compact domain
needs a net and a Lipschitz bound, not done): with i.i.d. features `(ω_j, b_j) ∼ Λ ⊗ Unif[0, 2π]`, for every
finite `S ⊆ 𝒳 × 𝒳` and `δ ∈ (0, 1)`, with probability at least `1 − δ` (a measurable event),
`|ẑ(x, y) − k(x, y)| ≤ 2κ² (2 log(2|S|/δ)/r)^{1/2}` simultaneously for all `(x, y) ∈ S`. -/
def rff_finite : Prop :=
  ∀ (d r : ℕ) (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (Λ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure Λ] (β : Measure ℝ) [IsProbabilityMeasure β]
    (W : Fin r → Ω → EuclideanSpace ℝ (Fin d)) (B : Fin r → Ω → ℝ) (κ δ : ℝ)
    (S : Finset (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))),
    β = unifCircle → 0 < r → 0 < δ → δ < 1 → (∀ j, Measurable (W j)) → (∀ j, Measurable (B j)) →
    iIndepFun (fun j ω => (W j ω, B j ω)) Pr → (∀ j, Pr.map (fun ω => (W j ω, B j ω)) = Λ.prod β) →
      ∃ A : Set Ω, MeasurableSet A ∧ ENNReal.ofReal (1 - δ) ≤ Pr A ∧
        ∀ ω ∈ A, ∀ p ∈ S, |rffKernel κ (fun j => W j ω) (fun j => B j ω) p.1 p.2 - bochnerKernel κ Λ p.1 p.2| ≤
          2 * κ ^ 2 * Real.sqrt (2 * Real.log (2 * S.card / δ) / r)

/-! ### otfd B: the three references -/

/-- `lem:refs-ac`, cubic law, the clause not already frozen (absolute continuity and bounded support are the
certified OTFD Wave 22b `cubic_density`): `c_K(τ) = μ_K(ρ_box ≤ τ)`, `ρ_box(u) = ‖u‖₂/D_∞`, is continuous (`K ≥ 1`;
the spheres `{‖u‖₂ = τ D_∞}` are Lebesgue-null). -/
def refs_ac_cubic_cK : Prop :=
  ∀ (K : ℕ) (lam : Fin K → ℝ) (Dinf : ℝ), 1 ≤ K → (∀ k, 0 < lam k) → 0 < Dinf →
    Continuous fun τ : ℝ => (StatFormal.OTFD.Wave22b.cubicLaw lam).real {u | ‖u‖ / Dinf ≤ τ}

/-! ### otfd R: Gaussian and Student references -/

/-- `cor:gaussian-t`, the moment clause: for `W ∼ InvGamma(ν/2, ν/2)` (`W > 0`, `1/W ∼ Gamma(ν/2, rate ν/2)`),
`E W < ∞` iff `ν > 2` (so `E‖X‖² = E W · tr Σ < ∞` iff `ν > 2`). -/
def gaussian_t_moment : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (W : Ω → ℝ) (ν : ℝ),
    0 < ν → Measurable W → (∀ᵐ ω ∂Pr, 0 < W ω) → Pr.map (fun ω => (W ω)⁻¹) = gammaMeasure (ν / 2) (ν / 2) →
      (Integrable W Pr ↔ 2 < ν)

/-- `cor:gaussian-t`, the tail clause: for the Student reference (`√W ξ ∼ t_ν`, `F_{t_ν} = F₁` of the frozen
`ellF1`), there are `0 < c_ν ≤ C_ν` with `c_ν r^{−ν} ≤ F_{t_ν}(−r) ≤ C_ν r^{−ν}` for all `r ≥ 1`. -/
def gaussian_t_tail : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (W : Ω → ℝ) (ν : ℝ),
    0 < ν → Measurable W → (∀ᵐ ω ∂Pr, 0 < W ω) → Pr.map (fun ω => (W ω)⁻¹) = gammaMeasure (ν / 2) (ν / 2) →
      ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ r : ℝ, 1 ≤ r →
        c * r ^ (-ν) ≤ ellF1 Pr W (-r) ∧ ellF1 Pr W (-r) ≤ C * r ^ (-ν)

end Claims

end StatFormal.Wave24e
