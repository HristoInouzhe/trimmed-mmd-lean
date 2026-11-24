import StatFormal.Archive.Wave19b.Statements
import StatFormal.Archive.Wave22c.Statements
import StatFormal.Archive.Defects2.Statements
import StatFormal.Archive.SBFairness.Statements
import StatFormal.Archive.OTFD.Wave3.Statements

/-!
# FROZEN STATEMENTS — wave 23a (QUEUE rows 269–272, 282–287): robust equality `thm:ep-limit0`; SB `prop:debiased`,
# `prop:sbbary`, `lem:qgrowth`; ICL `thm:score`; NN `lem:factmom` (with partial discharges of Wave 22c `thm:comb`,
# `cor:tube-threshold`); otfd R `prop:symmetry`, B `prop:width`, `thm:prob-content`, `thm:band-containment`

Sources (verbatim in `lean-formalisation/inventory/extracted/{robust-equality-jasa,data-fairness-repair,
context-distribution-icl,proliferation-nns,otfd-R_robustness,otfd-B_bands}.md`; current text after the 2026-10-15
corrections):
* JASA `thm:ep-limit0` (`robust-equality-outcomes-under-distribution-shift/jasa/supp_eps.tex:177-202`, proof
  `:204-237`), with `def:ep-member` (`:40-52`, `R_0`) and the file-header notation (`:6-17`, `R_ε`).
* SB `prop:sbbary` (`data-fairness-repair/schrodinger_bridge_fairness_repair.tex:2197-2215`, proof `:2818-2858`),
  `prop:debiased` (`:2246-2261`, proof `:2860-2906`), with `eq:ceps` (`lem:gaussplan`, `:2163-2177`).
* SB `lem:qgrowth` (`schrodinger_bridge_fairness_repair.tex:1243-1253`, proof `:1255-1261`), with `eq:repaircost`
  (`:1203-1208`: `F(ν) = Σ_s p_s W₂²(R_s, ν)`, `ν⋆` the Wasserstein barycenter).
* ICL `thm:score` (`context-distribution-ICL/paper/v3/sections/06_estimation.tex:136-148`).
* NN `lem:factmom` (`proliferation-and-geometry-in-nns/paper_revised.tex:731-737`, proof `app:moment`
  `:1725-1779`, with `eq:factmom-twosided` `:1781-1784`), and `thm:comb`, `cor:tube-threshold` (frozen Wave 22c).
* otfd R `prop:symmetry` (`otfd/papers/R_robustness/sections/s8_unbalanced.tex:169-175`, proof `:177-185`).
* otfd B `prop:width` (`otfd/papers/B_bands/main.tex:943-958`, proof `supplement.tex:3244-3261`), with
  `def:cal-score` (`main.tex:881-905`, frozen in `OTFD/Wave3`).
* otfd B `thm:prob-content` (`otfd/papers/B_bands/supplement.tex:6367-6392`, proof `:529-576`), with
  `def:depth-family` (`main.tex:502-516`).
* otfd B `thm:band-containment` (`otfd/papers/B_bands/supplement.tex:805-824`, proof `:2011-2031`), with the
  population band (`:779-793`) and `lem:band-containment-relative` (`:2033-2046`).
Imports the frozen `Wave19b` (`floorW`, `floorZero`), `Wave22c` (`IsLambertW`, `factMoment`, `nBlocks`, and the claims
`comb`, `tube_threshold`; through it `NNFibers`: `bell`, `T`), `Defects2` (`DebiasedEq`), `SBFairness` (`cEps`) and
`OTFD/Wave3` (`ordStat`, `calIdx`, `bandScore`, `inflBand`) statements, not copied; Mathlib and Tau Ceti
(`wassersteinEDist`, `HasFiniteMoment`) otherwise.

Covered:
* `thm:ep-limit0` (i): `ep_limit0_floor` (`R_ε ↓ R_0` as `ε ↓ 0`: monotone, `≥ R_0`, and the limit, for every finite
  reference with `0 < ν(K) ≤ 1`), `ep_limit0_atoms` (finitely many atoms: `0 ≤ R_ε − R_0 ≤ ε E log(1/ν_{j*}) ≤
  ε log(1/min_j ν_j)`).
* `prop:sbbary` (scalar layer): `sbbary_root_unique` (exactly one `τ > 0` with `Ψ_ε(τ) = 1`, every `ε ≥ 0`),
  `sbbary_root_zero` (`τ_0 = Σ_s p_s σ_s`), `sbbary_strictMono` (`τ_ε` strictly increasing in `ε`),
  `sbbary_limits` (`τ_ε → τ_0` as `ε ↓ 0`, `τ_ε/√ε → 1` as `ε → ∞`).
* `prop:debiased`: `debiased_limits` (both limits of `τ^S_ε`; uniqueness and the bracket are the certified Defects2
  `debiased_root_unique`, `debiased_root_between`).
* `lem:qgrowth`: (i) `qgrowth_one_dim` (`d = 1`: a barycenter exists, `F(ω) = F(ν⋆) + W₂²(ω,ν⋆)` on `𝒫₂(ℝ)` for every
  barycenter `ν⋆`, and `c = 1`); (ii) `qgrowth_equal` (`R_0 = R_1` in `ℝ^d`, `d ≥ 1`: `F = W₂²(R_0,·)`, `ν⋆ = R_0` is
  the unique barycenter, `c = 1`).
* `thm:score` (deterministic core): `score_argmin` (on a compact `Θ` with `J` continuous and `sup_Θ |J_n − J| → 0`: `J`
  attains its minimum, so does every continuous `J_n`, `inf J_n → min J`, and every cluster point of approximate
  minimisers `θ̂_n` minimises `J`).
* `lem:factmom`: `factmom_poisson_binomial` (factorial moments of a Poisson-binomial law are the distinct-index sums
  `D_s`), `factmom_twosided` (`(1 − C(s,2)/μ) μ^s ≤ D_s ≤ μ^s`, every `p ∈ [0,1]^n`), `factmom_twosided_Km`
  (`eq:factmom-twosided` for `K_m`, CONDITIONAL on Harper's representation at `m`), `factmom` — CONDITIONAL on
  Harper's representation (eventually in `m`) and the mean asymptotic `E[K_m] ∼ m/W(m)`: `E[(K_m)_s] ∼ (m/W(m))^s`.
  PARTIAL DISCHARGES of Wave 22c: `comb_discharged`, `tube_threshold_discharged` (the frozen `comb`, `tube_threshold`
  with their `lem:factmom` hypotheses replaced by these two classical inputs).
* `prop:symmetry` (finitely supported laws): `schrodinger_unique` (solutions of the discrete Schrödinger system are
  unique up to `(f + C, g − C)`), `symmetry_blind` (`F̂_ε(2m − x) = −F̂_ε(x)` for every `x`, `F̂_ε(m) = 0`, so `m` has the
  smallest rank norm).
* `prop:width`: `width_sandwich` ((ii): the event of the width sandwich, simultaneously for all `θ`, is measurable
  and has probability `≥ 1 − 1/n₂`), `width_coverage` ((i): `P(X_{n+1} ∈ B̂_θ̂^{ω̂_θ̂}) ≥ 1 − α − t − 1/n₂`, event
  measurable) — both CONDITIONAL on the Dvoretzky–Kiefer–Wolfowitz inequality with Massart's constant for each `θ`.
* `thm:prob-content`: `prob_content_b` ((b): `P_K(F⁻¹{u ∈ supp μ_K : ρ(u) ≤ τ}) = c_K(τ)` for every Borel `F` with
  `F#P_K = μ_K`, and `= p` at `τ = c_K^{-1}(p)`), `prob_content_e` ((e): the image form, CONDITIONAL on the two
  subdifferential-inversion properties of `Q'` used in the proof).
* `thm:band-containment`: `band_containment` — CONDITIONAL on `prop:app-potential-consistency` (a.e. convergence of the
  fitted map on `A_{K,p}`): for every `η > 0`, eventually `x↑pop ≤ x̂↑_n + η` and `x̂↓_n ≤ x↓pop + η`, uniformly in `t`.

Not covered (declared):
* `thm:ep-limit0`: (i) the density bounds `(d/2) ε log(1/(πε)) − ε log q_max ≤ R_ε ≤ …` (Lebesgue integrals over
  `B(x,√ε) ∩ K`) and the free class `R^{𝒫(K)}_ε ≤ min{ε log n, …}` (KL of the diagonal coupling, discrete
  Radon–Nikodym computation not done); a general (non-discrete) centre `P̂`; (ii) Γ-convergence and Hausdorff
  convergence of the balls in `(𝒫(K), W₂)` (portmanteau, Genevay et al.'s bound); (iii) the certificates (Laplace
  limit, Dini) and the worst-case disparities.
* `prop:sbbary`: that `N(a⋆, τ_ε²)` minimises `eq:sbbary` over all of `𝒫₂(ℝ)` (general entropic OT and the joint
  strict convexity argument), and `a⋆ = Σ_s p_s a_s`.
* `prop:debiased`: that the minimiser over Gaussian targets has mean `a⋆` and scale `τ^S_ε` (envelope-theorem
  derivative of `eq:cepsval`; `eq:cepsval` itself rests on `lem:gaussplan`, of which only the root is frozen).
* `lem:qgrowth` (iii): `d ≥ 2`, `c` arbitrarily small (Gaussian barycenter fixed point over `𝒫₂(ℝ^d)`, Gelbrich bound;
  missing).
* `thm:score`: the almost-sure uniform law (`sup_Θ |J_{n,m} − J| → 0` a.s.: V-statistic ULLN and the
  without-replacement perturbation), attainment by the random `J_{n,m}` (continuity of the random objective), and the
  asymptotic normality (M-estimator CLT, `as:smooth`–`as:interior`).
* `lem:factmom`: Harper's real-rootedness theorem (`HarperRep`) and the Moser–Wyman ratio `B_{m+1}/B_m ∼ m/W(m)`
  (hypotheses; the paper's input is the ratio, equivalent to the mean form through `E[K_m] = B_{m+1}/B_m − 1`, not
  formalised); the remark on uniformity over `s = o(μ_m^{1/2})` (only fixed `s`).
* `prop:symmetry`: continuous or semi-discrete laws (general entropic OT and potential uniqueness); existence of a
  solution of the Schrödinger system (Sinkhorn; the claims hold for every solution).
* `prop:width`: DKW–Massart itself (hypothesis), the case "selected on a separate fold" of (i) (that is
  `prop:cal-coverage`, frozen and certified in `OTFD/Wave3`).
* `thm:prob-content`: (a), (c), (d) (McCann/GHS existence and uniqueness of `M_K`-monotone maps for `𝒫^ℓ` laws
  without moments; `lem:refs-ac`); in (e) the derivation of the two inversion properties from
  `∂φ* = (∂φ)^{-1}` (Rockafellar 23.5.1, 25.1, 25.5); the naive-law specialisation `c_K(τ) = τ` (immediate).
* `thm:band-containment`: `prop:app-potential-consistency` and `lem:app-subgradient-convergence` (hypothesis); the
  sufficient conditions for bounded essential range; the certified band `B̄_K(p)` (monotonicity, `prop:band-certificate`).

Encodings (to be checked by the critic):
* ep-limit0: centre `P̂ = Σ_i a_i δ_{x_i}` (`a_i > 0`, `Σ a_i = 1`), cost `c = dist²` bounded on the centre (`K`
  compact), the frozen `floorW` (`R_ε`) and `floorZero` (`R_0`, `S_ν = supp ν`); `K` a second-countable metric space;
  the atomic reference is `atomRef w y = Σ_j w_j δ_{y_j}` (`w_j > 0`, `Σ w_j ≤ 1`), `j*(i)` any nearest atom, and
  `min_j ν_j = ⨅ j, w j` (finite nonempty index).
* SB: `Ψ_ε(τ) = psiSB` with the frozen `SBFairness.cEps` (`eq:ceps`, `> 0` for `σ, τ > 0`, `ε ≥ 0`, so no junk
  division); `τ_ε` is any function with `τ_ε > 0`, `Ψ_ε(τ_ε) = 1` (by `sbbary_root_unique` it is THE root); `τ^S_ε` is
  any function with `τ^S_ε > 0` solving the frozen `DebiasedEq` (unique by Defects2); groups `Fin S`, `p_s > 0`,
  `Σ p_s = 1`, `σ_s > 0`.
* qgrowth: `F(ω) = barF p R ω = Σ_s p_s W₂²(R_s, ω)` in `[0,∞]` (Tau Ceti `wassersteinEDist 2`), weights `p : Fin S →
  ℝ≥0`, `Σ p = 1`; `𝒫₂` = probability measures with `HasFiniteMoment 2`; a barycenter (`IsBarycenter`) is a minimiser
  of `F` over `𝒫₂`; `c(R_0,R_1) = qgrowthC = ⨅_{ω ∈ 𝒫₂, ω ≠ ν⋆} (F(ω) − F(ν⋆))/W₂²(ω,ν⋆)` in `[0,∞]` (numerator and
  denominator finite, denominator `> 0`; the index set is nonempty because `d ≥ 1`); `F(ω) − F(ν⋆) = W₂²` is stated
  additively. (i) is for any number of groups (generalisation), (ii) for two groups `![R, R]`.
* score: `Θ` compact topological (paper: compact metric), `J_n → J` uniformly is `TendstoUniformly`, `θ̂_n` are
  `ε_n`-minimisers with `ε_n → 0` (paper: exact minimisers, `ε_n = 0`), limit points are `MapClusterPt`.
* factmom: `D_s(p) = distinctMoment p s` (sum over injective `f : Fin s → Fin n` of `∏_j p_{f(j)}` = `s! e_s(p)`);
  the Poisson-binomial law `poisBinom p q = Σ_{|S| = q} ∏_{i∈S} p_i ∏_{i∉S}(1 − p_i)`; Harper's theorem is
  `HarperRep m` (`P(K_m = q) = #{q blocks}/B_m` is Poisson-binomial for some `p ∈ [0,1]^m`, every `q`); `μ_m =
  E[K_m] = factMoment 1 m`; the frozen `factMoment` (`E[(K_m)_s]`); `C(s,2) = s.choose 2`; `μ > 0` assumed (no junk).
* symmetry: `P = Σ_i a_i δ_{x_i}`, `ν = Σ_j b_j δ_{u_j}` on a real inner product space `E`, `a_i, b_j > 0`; "symmetric
  about `m`" / "about `0`" is an involution of the atom labels `σ`, `τ` (permutations) with `x_{σ i} = 2m − x_i`,
  `a_{σ i} = a_i`, `u_{τ j} = −u_j`, `b_{τ j} = b_j` (equivalent to `R#P = P` when the atoms are distinct); cost
  `½‖u − x‖²`; the population entropic problem is the Schrödinger system `IsSchrodinger` (plan `a_i b_j
  e^{(f_i + g_j − ½‖u_j − x_i‖²)/ε}` with marginals `a`, `b`); `F̂_ε = entRank`, the extension through `g` printed
  in the proof. "Largest transport depth" is read as smallest `‖F̂_ε‖` (any depth decreasing in the rank norm).
* width: curves `T → ℝ` with the product σ-algebra; candidates `Θ` finite nonempty, shapes `(c_θ, w_θ)`, `w_θ ≥ 0`
  fixed (conditioning on `𝓘₁`); `V_θ = bandScore` (frozen, `[0,∞]`), measurable; calibration sample `y : Fin n → (T →
  ℝ)` with law `μ^{⊗n}` (`Measure.pi`), `X_{n+1} ∼ μ` independent (product measure); `ω̂_θ = ordStat (calIdx n α)` of
  the calibration scores (`+∞` past `n`); `W_θ = ω̂_θ w̄_θ` in `[0,∞]`, `w̄_θ > 0`; `θ̂` any measurable argmin of `W`
  (each fibre measurable); `G_θ(s) = μ(V_θ ≤ s)`, `q_θ(β) = inf{s ∈ [0,∞] : G_θ(s) ≥ β}` (`scoreQuant`, `inf ∅ = ∞`,
  scores are nonnegative); `Ĝ_θ` the empirical distribution function; `t = (log(2n|Θ|)/(2n))^{1/2}`; DKW–Massart:
  `P(∃ s, |Ĝ_θ(s) − G_θ(s)| > t) ≤ 2e^{−2nt²}` for each `θ` (outer measure), only at this one level `t` (an instance
  of the inequality `P(sup_s |Ĝ − G| > λ) ≤ 2e^{−2nλ²}`, valid for every `λ > 0` and every law of `V_θ`, atoms and the
  value `+∞` included, via an order-preserving map of `[0,∞]` onto `[0,1]`). `0 < α < 1`, `n ≥ 1`. Added to the
  printed hypotheses: `V_θ` measurable and `{θ̂ = θ}` measurable (needed for the events to have a probability).
* prob-content: `ℝ^K = EuclideanSpace ℝ (Fin K)`; `F` any measurable map with `F#P_K = μ_K` (this is all (b) uses; (a)
  supplies it); `ρ` measurable; `c_K(τ) = μ_K(ρ ≤ τ)` (`cdfK`, as in `def:depth-family`), continuous on `[0,1]` with
  `c_K(0) = 0`, `c_K(1) = 1`; `c_K^{-1}(p) = inf{t ∈ [0,1] : c_K(t) ≥ p}` (nonempty, bounded below). (e): `Q'` any
  map; `G'` (the proof's `E`) and `D` (the proof's `L^{-1}(D)`) Borel of full `P_K`-measure with `Q'(F z) = z` on `G'`
  and `Q'(u) = z ∈ D ⇒ F z = u`; `Q'(A)` is `P_K`-null-measurable (completion) with `P_K(Q'(A)) = μ_K(A)`. `Q'` is total, while the
  paper's selection is defined on `dom ∂φ*` only; it is instantiated by sending every `u ∉ dom ∂φ*` to one point `z₀`
  with `P_K{z₀} = 0` (`P_K ∈ 𝒫^ℓ` has no atoms) and replacing `D` by `D \ {z₀}`; this changes `Q'(A)` by at most `{z₀}`.
* band-containment: `A = A_{K,p}` measurable, `Q = Q_{±,K}` any map, `Q̂_n` the fitted maps; the edges are `EReal`:
  `h^pop(v) = essSup_{μ|A} ⟨v, Q(·)⟩` (`popSupp`, `⊥` if `μ(A) = 0`), `ĥ_n(v) = sup_{u ∈ A} ⟨v, Q̂_n(u)⟩` (`fitSupp`),
  `x↑ = 𝔪 + h(e)`, `x↓ = 𝔪 − h(−e)`; bounded essential range is `‖Q‖ ≤ R` `μ|A`-a.e.; `E_K < ∞` is `‖e(t)‖ ≤ C`; the
  hypothesis is `Q̂_n(u) → Q(u)` for `μ|A`-a.e. `u` (what `prop:app-potential-consistency` with
  `lem:app-subgradient-convergence`(a) give on `Ω₀`); the conclusion is the theorem's "equivalently" form, which is the
  liminf/limsup display for finite edges.

Critic notes:
* All 23 claims are proved in `Wave23a/Route{EpLimit0,SB,QGrowth,Score,Factmom,Symmetry,Width,ProbContent,Band}.lean`
  (axioms: propext, Classical.choice, Quot.sound). Routes reuse the certified Wave 19b `ep_nested_floor`, Defects2
  `debiased_root_between`, `sq_div_cEps`, Wave 22c `comb`, `tube_threshold`, `factMoment_eq`, `lambertW_div_equiv`,
  `NNFibers.Wave1.T_pos`, OTFD Wave 3 `band_mem_iff`, `ordStat_le_iff`, and Tau Ceti's
  `sum_mul_wassersteinEDist_sq_eq_add`, `sum_mul_wassersteinEDist_sq_le_iff_eq_quantileBarycenter`,
  `hasFiniteMoment_quantileBarycenter`.
* CONDITIONAL claims and their uncertified inputs: `factmom`, `factmom_twosided_Km`, `comb_discharged`,
  `tube_threshold_discharged` (Harper's real-rootedness; Moser–Wyman); `width_sandwich`, `width_coverage`
  (DKW with Massart's constant); `prob_content_e` (the convex-duality inversion properties); `band_containment`
  (`prop:app-potential-consistency`). The Wave 22c discharges are PARTIAL: `comb` and `tube_threshold` no longer need
  `lem:factmom`, but now need Harper and Moser–Wyman (both classical; `tube_threshold` keeps its two tube hypotheses).
* No statement was found false. Observations: (1) `lem:qgrowth`'s `c` is an infimum over `ω ≠ ν⋆`, which needs a
  space with two points (`d ≥ 1`; for `d = 0` the index set is empty). (2) `prop:debiased`'s `ε → ∞` limit, as proved
  here, needs only the bracket and `√(ε² + x) − ε ∈ [x/(2ε + √x), x/(2ε)]`, not the `O(ε^{-3})` expansion of the
  printed proof. (3) `prop:symmetry` needs no atom at `m`; the conclusion holds for every solution of the Schrödinger
  system, and existence (Sinkhorn) is not used.
* Critic (2026-10-15): ACCEPT-WITH-NOTE, all 23 TRUE, none tautological, no junk value reachable on the hypotheses
  (`⨅ j, w j` has `m ≥ 1` since `k ≥ 1`; `cEps > 0`; `entRank`'s normaliser `> 0` for `N ≥ 1`; `qgrowthC`'s
  denominators finite and `> 0`; `cdfKInv`'s set nonempty and bounded below; `⨅ θ, J_n θ` is genuine eventually; the
  `EReal` edges are `⊥` only when `μ(A) = 0`, where both sides degenerate as in the paper). The assumed classical
  inputs are stated no stronger than the real theorems: `HarperRep m` holds for every `m` (Harper 1967; the
  hypothesis asks only eventually); `E[K_m] ∼ m/W(m)` is the Moser–Wyman ratio `B_{m+1}/B_m ∼ (m+1)/W(m+1)` minus
  `1`; the DKW event is Massart's two-sided bound at one level. Specialisations: discrete centre `P̂` and finite
  reference (ep-limit0); finitely supported `P`, `ν` (symmetry); deterministic cores of the almost-sure statements
  (score: the uniform law is a hypothesis; band: the realisation on `Ω₀`); conditioning on `𝓘₁` (width). The
  discharges `comb_discharged`, `tube_threshold_discharged` apply the certified frozen `Wave22c.comb`,
  `Wave22c.tube_threshold` to the same objects, with only their two `lem:factmom` premises replaced.

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Asymptotics Finset TauCeti
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave23a

/-! ### Robust equality: atomic references -/

/-- The atomic reference `ν = Σ_j w_j δ_{y_j}`. -/
def atomRef {K : Type*} [MeasurableSpace K] {m : ℕ} (w : Fin m → ℝ) (y : Fin m → K) : Measure K :=
  ∑ j, ENNReal.ofReal (w j) • Measure.dirac (y j)

/-! ### SB: the Schrödinger barycenter scale -/

/-- `Ψ_ε(τ) = Σ_s p_s σ_s² / c_ε(σ_s, τ)` (`prop:sbbary`). -/
def psiSB {S : ℕ} (ε : ℝ) (p σ : Fin S → ℝ) (τ : ℝ) : ℝ :=
  ∑ s, p s * σ s ^ 2 / StatFormal.SBFairness.cEps ε (σ s) τ

/-! ### SB: quadratic growth of the barycenter functional -/

/-- `F(ω) = Σ_s p_s W₂²(R_s, ω)` (`eq:repaircost`), in `[0,∞]`. -/
def barF {X : Type*} [MeasurableSpace X] [PseudoEMetricSpace X] {S : ℕ} (p : Fin S → ℝ≥0)
    (R : Fin S → Measure X) (ω : Measure X) : ℝ≥0∞ :=
  ∑ s, (p s : ℝ≥0∞) * wassersteinEDist 2 (R s) ω ^ 2

/-- `ν` is a Wasserstein barycenter: a minimiser of `F` over `𝒫₂`. -/
def IsBarycenter {X : Type*} [MeasurableSpace X] [PseudoEMetricSpace X] {S : ℕ} (p : Fin S → ℝ≥0)
    (R : Fin S → Measure X) (ν : Measure X) : Prop :=
  IsProbabilityMeasure ν ∧ HasFiniteMoment 2 ν ∧
    ∀ ω : Measure X, IsProbabilityMeasure ω → HasFiniteMoment 2 ω → barF p R ν ≤ barF p R ω

/-- `c = inf_{ω ∈ 𝒫₂, ω ≠ ν⋆} (F(ω) − F(ν⋆))/W₂²(ω, ν⋆)` (`lem:qgrowth`). -/
def qgrowthC {X : Type*} [MeasurableSpace X] [PseudoEMetricSpace X] {S : ℕ} (p : Fin S → ℝ≥0)
    (R : Fin S → Measure X) (νstar : Measure X) : ℝ≥0∞ :=
  ⨅ ω ∈ {ω : Measure X | IsProbabilityMeasure ω ∧ HasFiniteMoment 2 ω ∧ ω ≠ νstar},
    (barF p R ω - barF p R νstar) / wassersteinEDist 2 ω νstar ^ 2

/-! ### NN: Poisson-binomial factorial moments -/

/-- `D_s(p) = Σ_{f : Fin s → Fin n injective} ∏_j p_{f(j)}` (`= s! e_s(p)`). -/
def distinctMoment {n : ℕ} (p : Fin n → ℝ) (s : ℕ) : ℝ :=
  ∑ f ∈ (Finset.univ : Finset (Fin s → Fin n)).filter Function.Injective, ∏ j, p (f j)

/-- The law of `Σ_i Ber(p_i)` (independent): `P(K = q) = Σ_{|S| = q} ∏_{i∈S} p_i ∏_{i∉S} (1 − p_i)`. -/
def poisBinom {n : ℕ} (p : Fin n → ℝ) (q : ℕ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card = q),
    (∏ i ∈ S, p i) * ∏ i ∈ Sᶜ, (1 - p i)

/-- Harper's theorem at `m`: `K_m` (the block count of a uniform partition of `[m]`) has the law of a sum of `m`
independent Bernoulli variables. -/
def HarperRep (m : ℕ) : Prop :=
  ∃ p : Fin m → ℝ, (∀ i, 0 ≤ p i ∧ p i ≤ 1) ∧
    ∀ q, (StatFormal.Wave22c.nBlocks m q : ℝ) / (StatFormal.NNFibers.bell m : ℝ) = poisBinom p q

/-! ### otfd R: the discrete entropic problem -/

/-- `(f, g)` solves the Schrödinger system of `P = Σ a_i δ_{x_i}`, `ν = Σ b_j δ_{u_j}` at temperature `ε`, cost
`½‖u − x‖²`: the plan `a_i b_j e^{(f_i + g_j − ½‖u_j − x_i‖²)/ε}` has marginals `a` and `b`. -/
def IsSchrodinger {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n N : ℕ} (ε : ℝ) (a : Fin n → ℝ)
    (x : Fin n → E) (b : Fin N → ℝ) (u : Fin N → E) (f : Fin n → ℝ) (g : Fin N → ℝ) : Prop :=
  (∀ i, ∑ j, b j * Real.exp ((f i + g j - ‖u j - x i‖ ^ 2 / 2) / ε) = 1) ∧
    ∀ j, ∑ i, a i * Real.exp ((f i + g j - ‖u j - x i‖ ^ 2 / 2) / ε) = 1

/-- The entropic rank map extended through the dual potential `g`:
`F̂_ε(z) = Σ_j b_j u_j e^{(g_j − ½‖u_j − z‖²)/ε} / Σ_j b_j e^{(g_j − ½‖u_j − z‖²)/ε}`. -/
def entRank {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {N : ℕ} (ε : ℝ) (b : Fin N → ℝ)
    (u : Fin N → E) (g : Fin N → ℝ) (z : E) : E :=
  (∑ j, b j * Real.exp ((g j - ‖u j - z‖ ^ 2 / 2) / ε))⁻¹ •
    ∑ j, (b j * Real.exp ((g j - ‖u j - z‖ ^ 2 / 2) / ε)) • u j

/-! ### otfd B: selecting by width -/

/-- `G(s) = μ(V ≤ s)`. -/
def scoreCDF {𝒳 : Type*} [MeasurableSpace 𝒳] (μ : Measure 𝒳) (V : 𝒳 → ℝ≥0∞) (s : ℝ≥0∞) : ℝ≥0∞ :=
  μ {x | V x ≤ s}

/-- `q(β) = inf{s ∈ [0,∞] : G(s) ≥ β}` (`inf ∅ = ∞`). -/
def scoreQuant {𝒳 : Type*} [MeasurableSpace 𝒳] (μ : Measure 𝒳) (V : 𝒳 → ℝ≥0∞) (β : ℝ) : ℝ≥0∞ :=
  sInf {s | ENNReal.ofReal β ≤ scoreCDF μ V s}

/-- The empirical distribution function `Ĝ(s) = #{i : V(y_i) ≤ s}/n`. -/
def empCDF {𝒳 : Type*} {n : ℕ} (V : 𝒳 → ℝ≥0∞) (y : Fin n → 𝒳) (s : ℝ≥0∞) : ℝ :=
  (#(Finset.univ.filter fun i => V (y i) ≤ s) : ℝ) / n

/-- `ω̂ = ` the `⌈(n+1)(1−α)⌉`-th smallest calibration score (`+∞` past `n`). -/
def omegaHat {𝒳 : Type*} {n : ℕ} (α : ℝ) (V : 𝒳 → ℝ≥0∞) (y : Fin n → 𝒳) : ℝ≥0∞ :=
  StatFormal.OTFD.Wave3.ordStat (StatFormal.OTFD.Wave3.calIdx n α) fun i => V (y i)

/-- `t = (log(2n|Θ|)/(2n))^{1/2}`. -/
def tWidth (n card : ℕ) : ℝ := √(Real.log (2 * n * card) / (2 * n))

/-! ### otfd B: probability content -/

/-- `c_K(τ) = μ_K(ρ ≤ τ)`. -/
def cdfK {E : Type*} [MeasurableSpace E] (μ : Measure E) (ρ : E → ℝ) (τ : ℝ) : ℝ := μ.real {u | ρ u ≤ τ}

/-- `c_K^{-1}(p) = inf{t ∈ [0,1] : c_K(t) ≥ p}`. -/
def cdfKInv {E : Type*} [MeasurableSpace E] (μ : Measure E) (ρ : E → ℝ) (p : ℝ) : ℝ :=
  sInf {t ∈ Icc (0 : ℝ) 1 | p ≤ cdfK μ ρ t}

/-! ### otfd B: band edges -/

/-- `h^pop(v) = μ-ess sup_{u ∈ A} ⟨v, Q(u)⟩`, in `EReal`. -/
def popSupp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] (μ : Measure E)
    (A : Set E) (Q : E → E) (v : E) : EReal :=
  essSup (fun u => ((⟪v, Q u⟫ : ℝ) : EReal)) (μ.restrict A)

/-- `ĥ_n(v) = sup_{u ∈ A} ⟨v, Q̂_n(u)⟩`, in `EReal`. -/
def fitSupp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : Set E) (Qn : E → E) (v : E) : EReal :=
  ⨆ u ∈ A, ((⟪v, Qn u⟫ : ℝ) : EReal)

namespace Claims

open StatFormal.Wave19b (floorW floorZero)

/-! #### JASA `thm:ep-limit0` (i) -/

/-- (i) Floors: `R_ε ↓ R_0` as `ε ↓ 0`, for every reference `ν` with `0 < ν(K) ≤ 1` (discrete centre, `c = dist²`). -/
def ep_limit0_floor : Prop :=
  ∀ (K : Type) [MetricSpace K] [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
    (k : ℕ) (a : Fin k → ℝ) (x : Fin k → K) (ν : Measure K) [IsFiniteMeasure ν],
    (∀ i, 0 < a i) → ∑ i, a i = 1 → (∃ B, ∀ i z, dist (x i) z ^ 2 ≤ B) → ν Set.univ ≠ 0 → ν Set.univ ≤ 1 →
      MonotoneOn (fun ε => floorW ε a (fun i z => dist (x i) z ^ 2) ν) (Ioi 0) ∧
        (∀ ε, 0 < ε → floorZero a x ν ≤ floorW ε a (fun i z => dist (x i) z ^ 2) ν) ∧
        Tendsto (fun ε => floorW ε a (fun i z => dist (x i) z ^ 2) ν) (𝓝[>] 0) (𝓝 (floorZero a x ν))

/-- (i) Atoms: for `ν = Σ_j ν_j δ_{y_j}`, `0 ≤ R_ε − R_0 ≤ ε E_{P̂} log(1/ν_{j*(x₀)}) ≤ ε log(1/min_j ν_j)`, `j*`
a nearest atom. -/
def ep_limit0_atoms : Prop :=
  ∀ (K : Type) [MetricSpace K] [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
    (k m : ℕ) (a : Fin k → ℝ) (x : Fin k → K) (w : Fin m → ℝ) (y : Fin m → K) (jstar : Fin k → Fin m) (ε : ℝ),
    0 < ε → (∀ i, 0 < a i) → ∑ i, a i = 1 → (∀ j, 0 < w j) → ∑ j, w j ≤ 1 →
    (∀ i j, dist (x i) (y (jstar i)) ≤ dist (x i) (y j)) →
      0 ≤ floorW ε a (fun i z => dist (x i) z ^ 2) (atomRef w y) - floorZero a x (atomRef w y) ∧
        floorW ε a (fun i z => dist (x i) z ^ 2) (atomRef w y) - floorZero a x (atomRef w y) ≤
          ε * ∑ i, a i * Real.log (1 / w (jstar i)) ∧
        ε * ∑ i, a i * Real.log (1 / w (jstar i)) ≤ ε * Real.log (1 / ⨅ j, w j)

/-! #### SB `prop:sbbary` (scalar layer) -/

/-- For every `ε ≥ 0` there is exactly one `τ > 0` with `Ψ_ε(τ) = 1`. -/
def sbbary_root_unique : Prop :=
  ∀ (S : ℕ) (ε : ℝ) (p σ : Fin S → ℝ), 0 ≤ ε → (∀ s, 0 < p s) → ∑ s, p s = 1 → (∀ s, 0 < σ s) →
    ∃! τ : ℝ, 0 < τ ∧ psiSB ε p σ τ = 1

/-- `τ_0 = Σ_s p_s σ_s`, the Wasserstein barycenter scale. -/
def sbbary_root_zero : Prop :=
  ∀ (S : ℕ) (p σ : Fin S → ℝ) (τ : ℝ), (∀ s, 0 < p s) → ∑ s, p s = 1 → (∀ s, 0 < σ s) → 0 < τ →
    (psiSB 0 p σ τ = 1 ↔ τ = ∑ s, p s * σ s)

/-- `τ_ε` is strictly increasing in `ε ≥ 0`. -/
def sbbary_strictMono : Prop :=
  ∀ (S : ℕ) (p σ : Fin S → ℝ) (ε ε' τ τ' : ℝ), (∀ s, 0 < p s) → ∑ s, p s = 1 → (∀ s, 0 < σ s) →
    0 ≤ ε → ε < ε' → 0 < τ → psiSB ε p σ τ = 1 → 0 < τ' → psiSB ε' p σ τ' = 1 → τ < τ'

/-- `τ_ε → τ_0 = Σ_s p_s σ_s` as `ε ↓ 0`, and `τ_ε/√ε → 1` as `ε → ∞`. -/
def sbbary_limits : Prop :=
  ∀ (S : ℕ) (p σ : Fin S → ℝ) (τ : ℝ → ℝ), (∀ s, 0 < p s) → ∑ s, p s = 1 → (∀ s, 0 < σ s) →
    (∀ ε, 0 < ε → 0 < τ ε ∧ psiSB ε p σ (τ ε) = 1) →
      Tendsto τ (𝓝[>] 0) (𝓝 (∑ s, p s * σ s)) ∧ Tendsto (fun ε => τ ε / √ε) atTop (𝓝 1)

/-! #### SB `prop:debiased` -/

/-- `τ^S_ε → Σ_s p_s σ_s` as `ε ↓ 0` and `τ^S_ε → (Σ_s p_s σ_s²)^{1/2}` as `ε → ∞`. -/
def debiased_limits : Prop :=
  ∀ (S : ℕ) (p σ : Fin S → ℝ) (τS : ℝ → ℝ), (∀ s, 0 < p s) → ∑ s, p s = 1 → (∀ s, 0 < σ s) →
    (∀ ε, 0 < ε → 0 < τS ε ∧ StatFormal.Defects2.DebiasedEq ε p σ (τS ε)) →
      Tendsto τS (𝓝[>] 0) (𝓝 (∑ s, p s * σ s)) ∧ Tendsto τS atTop (𝓝 (√(∑ s, p s * σ s ^ 2)))

/-! #### SB `lem:qgrowth` -/

/-- (i) `d = 1`: a barycenter exists, and for every barycenter `ν⋆`, `F(ω) − F(ν⋆) = W₂²(ω, ν⋆)` on `𝒫₂(ℝ)` and
`c = 1`. -/
def qgrowth_one_dim : Prop :=
  ∀ (S : ℕ) (p : Fin S → ℝ≥0) (R : Fin S → Measure ℝ), ∑ s, p s = 1 → (∀ s, IsProbabilityMeasure (R s)) →
    (∀ s, HasFiniteMoment 2 (R s)) →
      (∃ ν, IsBarycenter p R ν) ∧
        ∀ νstar, IsBarycenter p R νstar →
          (∀ ω : Measure ℝ, IsProbabilityMeasure ω → HasFiniteMoment 2 ω →
              barF p R ω = barF p R νstar + wassersteinEDist 2 ω νstar ^ 2) ∧
            qgrowthC p R νstar = 1

/-- (ii) `R_0 = R_1` in `ℝ^d`, `d ≥ 1`: `F(ω) = W₂²(R_0, ω)`, `ν⋆ = R_0` is the unique barycenter, and `c = 1`. -/
def qgrowth_equal : Prop :=
  ∀ (d : ℕ) (p : Fin 2 → ℝ≥0) (R₀ : Measure (EuclideanSpace ℝ (Fin d))), 1 ≤ d → ∑ s, p s = 1 →
    IsProbabilityMeasure R₀ → HasFiniteMoment 2 R₀ →
      (∀ ω, barF p ![R₀, R₀] ω = wassersteinEDist 2 R₀ ω ^ 2) ∧ IsBarycenter p ![R₀, R₀] R₀ ∧
        (∀ ν, IsBarycenter p ![R₀, R₀] ν → ν = R₀) ∧ qgrowthC p ![R₀, R₀] R₀ = 1

/-! #### ICL `thm:score` (deterministic core) -/

/-- On a compact `Θ`, if `J` is continuous and `sup_Θ |J_n − J| → 0`, then `J` attains its minimum, every continuous
`J_n` attains its minimum, `inf J_n → min J`, and every cluster point of `ε_n`-minimisers `θ̂_n` of `J_n`
(`ε_n → 0`) minimises `J`. -/
def score_argmin : Prop :=
  ∀ (Θ : Type) [TopologicalSpace Θ] [CompactSpace Θ] [Nonempty Θ] (J : Θ → ℝ) (Jn : ℕ → Θ → ℝ) (θn : ℕ → Θ)
    (εn : ℕ → ℝ), Continuous J → TendstoUniformly Jn J atTop → Tendsto εn atTop (𝓝 0) →
    (∀ n θ, Jn n (θn n) ≤ Jn n θ + εn n) →
      (∃ θ, ∀ θ', J θ ≤ J θ') ∧ (∀ n, Continuous (Jn n) → ∃ θ, ∀ θ', Jn n θ ≤ Jn n θ') ∧
        Tendsto (fun n => ⨅ θ, Jn n θ) atTop (𝓝 (⨅ θ, J θ)) ∧
        ∀ θ, MapClusterPt θ atTop θn → ∀ θ', J θ ≤ J θ'

/-! #### NN `lem:factmom` -/

/-- The factorial moments of `Σ_i Ber(p_i)` are the distinct-index sums: `E[(K)_s] = D_s(p)`. -/
def factmom_poisson_binomial : Prop :=
  ∀ (n : ℕ) (p : Fin n → ℝ) (s : ℕ),
    ∑ q ∈ Finset.range (n + 1), ((q.descFactorial s : ℕ) : ℝ) * poisBinom p q = distinctMoment p s

/-- The two-sided bound of `app:moment`: for `p ∈ [0,1]^n`, `μ = Σ_i p_i > 0`,
`(1 − C(s,2)/μ) μ^s ≤ D_s(p) ≤ μ^s`. -/
def factmom_twosided : Prop :=
  ∀ (n : ℕ) (p : Fin n → ℝ) (s : ℕ), (∀ i, 0 ≤ p i ∧ p i ≤ 1) → 0 < ∑ i, p i →
    (1 - (s.choose 2 : ℝ) / ∑ i, p i) * (∑ i, p i) ^ s ≤ distinctMoment p s ∧
      distinctMoment p s ≤ (∑ i, p i) ^ s

/-- `eq:factmom-twosided` for the block count, CONDITIONAL on Harper's representation at `m`:
`(1 − C(s,2)/μ_m) μ_m^s ≤ E[(K_m)_s] ≤ μ_m^s`, `μ_m = E[K_m]`. -/
def factmom_twosided_Km : Prop :=
  ∀ m s : ℕ, 1 ≤ m → HarperRep m →
    (1 - (s.choose 2 : ℝ) / StatFormal.Wave22c.factMoment 1 m) * StatFormal.Wave22c.factMoment 1 m ^ s ≤
        StatFormal.Wave22c.factMoment s m ∧
      StatFormal.Wave22c.factMoment s m ≤ StatFormal.Wave22c.factMoment 1 m ^ s

/-- `lem:factmom`, CONDITIONAL on Harper's representation (eventually in `m`) and the mean asymptotic
`E[K_m] ∼ m/W(m)` (Moser–Wyman): `E[(K_m)_s] ∼ (m/W(m))^s` for every fixed `s`. -/
def factmom : Prop :=
  ∀ W : ℝ → ℝ, StatFormal.Wave22c.IsLambertW W → (∀ᶠ m in atTop, HarperRep m) →
    (fun m : ℕ => StatFormal.Wave22c.factMoment 1 m) ~[atTop] (fun m : ℕ => (m : ℝ) / W m) →
      ∀ s : ℕ, (fun m : ℕ => StatFormal.Wave22c.factMoment s m) ~[atTop] (fun m : ℕ => ((m : ℝ) / W m) ^ s)

/-- PARTIAL DISCHARGE of Wave 22c `comb` (relative to Harper and Moser–Wyman): `T(r,m)/T(k,m) ∼ (W(m)/m)^{k−r}`
and `∼ (log m/m)^{k−r}`. -/
def comb_discharged : Prop :=
  ∀ (W : ℝ → ℝ) (r k : ℕ), StatFormal.Wave22c.IsLambertW W → 1 ≤ r → r < k → (∀ᶠ m in atTop, HarperRep m) →
    (fun m : ℕ => StatFormal.Wave22c.factMoment 1 m) ~[atTop] (fun m : ℕ => (m : ℝ) / W m) →
      (fun m : ℕ => (StatFormal.NNFibers.T r m : ℝ) / (StatFormal.NNFibers.T k m : ℝ)) ~[atTop]
          (fun m : ℕ => (W m / m) ^ (k - r)) ∧
        (fun m : ℕ => (StatFormal.NNFibers.T r m : ℝ) / (StatFormal.NNFibers.T k m : ℝ)) ~[atTop]
          (fun m : ℕ => (Real.log m / m) ^ (k - r))

/-- PARTIAL DISCHARGE of Wave 22c `tube_threshold` (relative to Harper and Moser–Wyman, the remaining hypotheses
`lem:tube-reduction` and `prop:average-offset-penalty` unchanged). -/
def tube_threshold_discharged : Prop :=
  ∀ (W : ℝ → ℝ) (d r k : ℕ) (δ σ : ℝ) (θr : Fin r → StatFormal.NNFibers.Wave1.Neuron d d)
    (θk : Fin k → StatFormal.NNFibers.Wave1.Neuron d d),
    StatFormal.Wave22c.IsLambertW W → 1 ≤ d → 1 ≤ r → r < k → 0 < δ → 0 < σ →
    (fun m : ℕ => StatFormal.Wave22c.Gbar d d δ σ θr m) ~[atTop]
        (fun m : ℕ => Real.exp (-StatFormal.Wave22c.tubeT δ σ) * StatFormal.Wave22c.Ubar d d δ σ θr m /
          (StatFormal.NNFibers.T r m : ℝ)) →
    (fun m : ℕ => StatFormal.Wave22c.Gbar d d δ σ θk m) ~[atTop]
        (fun m : ℕ => Real.exp (-StatFormal.Wave22c.tubeT δ σ) * StatFormal.Wave22c.Ubar d d δ σ θk m /
          (StatFormal.NNFibers.T k m : ℝ)) →
    (fun m : ℕ => StatFormal.Wave22c.avgOffset σ θr m) ~[atTop]
        (fun m : ℕ => (W m / m) ^ StatFormal.Wave22c.etaQ σ θr) →
    (fun m : ℕ => StatFormal.Wave22c.avgOffset σ θk m) ~[atTop]
        (fun m : ℕ => (W m / m) ^ StatFormal.Wave22c.etaQ σ θk) →
    (∀ᶠ m in atTop, HarperRep m) →
    (fun m : ℕ => StatFormal.Wave22c.factMoment 1 m) ~[atTop] (fun m : ℕ => (m : ℝ) / W m) →
      (fun m : ℕ => StatFormal.Wave22c.Gbar d d δ σ θr m / StatFormal.Wave22c.Gbar d d δ σ θk m) ~[atTop]
          (fun m : ℕ => ((d : ℝ) * σ ^ 2 / δ ^ 2) ^ ((d : ℝ) * ((k : ℝ) - r) / 2) *
            (m : ℝ) ^ ((d : ℝ) * ((k : ℝ) - r) / 2) *
              (W m / m) ^ (StatFormal.Wave22c.etaQ σ θr - StatFormal.Wave22c.etaQ σ θk)) ∧
        (fun m : ℕ => StatFormal.Wave22c.Qtube d d δ σ θr θk m) ~[atTop]
          (fun m : ℕ => ((d : ℝ) * σ ^ 2 / δ ^ 2) ^ ((d : ℝ) * ((k : ℝ) - r) / 2) *
            W m ^ ((d : ℝ) * ((k : ℝ) - r) / 2) * (W m / m) ^ StatFormal.Wave22c.Erk d σ θr θk) ∧
        (0 < StatFormal.Wave22c.Erk d σ θr θk →
          Tendsto (fun m : ℕ => StatFormal.Wave22c.Qtube d d δ σ θr θk m) atTop (𝓝 0)) ∧
        (StatFormal.Wave22c.Erk d σ θr θk ≤ 0 →
          Tendsto (fun m : ℕ => StatFormal.Wave22c.Qtube d d δ σ θr θk m) atTop atTop)

/-! #### otfd R `prop:symmetry` (finitely supported laws) -/

/-- Uniqueness of the discrete Schrödinger potentials up to constants: two solutions satisfy `f' = f + C`,
`g' = g − C`. -/
def schrodinger_unique : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n N : ℕ) (ε : ℝ) (a : Fin n → ℝ) (x : Fin n → E)
    (b : Fin N → ℝ) (u : Fin N → E) (f f' : Fin n → ℝ) (g g' : Fin N → ℝ),
    0 < ε → (∀ i, 0 < a i) → (∀ j, 0 < b j) → IsSchrodinger ε a x b u f g → IsSchrodinger ε a x b u f' g' →
      ∃ C : ℝ, (∀ i, f' i = f i + C) ∧ ∀ j, g' j = g j - C

/-- `prop:symmetry`: if `ν` is symmetric about `0` and `P` about `m`, then `F̂_ε(2m − x) = −F̂_ε(x)` for every `x`, and
`F̂_ε(m) = 0`, the smallest rank norm (whatever the mass of `P` at `m`). -/
def symmetry_blind : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n N : ℕ) (ε : ℝ) (a : Fin n → ℝ) (x : Fin n → E)
    (b : Fin N → ℝ) (u : Fin N → E) (f : Fin n → ℝ) (g : Fin N → ℝ) (m : E) (σ : Equiv.Perm (Fin n))
    (τ : Equiv.Perm (Fin N)),
    0 < ε → (∀ i, 0 < a i) → (∀ j, 0 < b j) → (∀ i, x (σ i) = (2 : ℝ) • m - x i) → (∀ i, a (σ i) = a i) →
    (∀ j, u (τ j) = -u j) → (∀ j, b (τ j) = b j) → IsSchrodinger ε a x b u f g →
      (∀ z, entRank ε b u g ((2 : ℝ) • m - z) = -entRank ε b u g z) ∧ entRank ε b u g m = 0 ∧
        ∀ z, ‖entRank ε b u g m‖ ≤ ‖entRank ε b u g z‖

/-! #### otfd B `prop:width` -/

/-- (ii) CONDITIONAL on DKW–Massart for each candidate: with probability at least `1 − 1/n₂`, simultaneously for all
`θ`, `q_θ̂(1−α−t) w̄_θ̂ ≤ W_θ̂ ≤ W_θ ≤ q_θ(1−α+t+2/n₂) w̄_θ` (the event is measurable). -/
def width_sandwich : Prop :=
  ∀ (T : Type) (Θ : Type) [Fintype Θ] [Nonempty Θ] (c w : Θ → T → ℝ) (wbar : Θ → ℝ≥0) (μ : Measure (T → ℝ))
    [IsProbabilityMeasure μ] (n : ℕ) (α : ℝ) (θhat : (Fin n → T → ℝ) → Θ),
    1 ≤ n → 0 < α → α < 1 → (∀ θ t, 0 ≤ w θ t) → (∀ θ, 0 < wbar θ) →
    (∀ θ, Measurable (StatFormal.OTFD.Wave3.bandScore (c θ) (w θ))) →
    (∀ θ, MeasurableSet {y | θhat y = θ}) →
    (∀ y θ, omegaHat α (StatFormal.OTFD.Wave3.bandScore (c (θhat y)) (w (θhat y))) y * wbar (θhat y) ≤
      omegaHat α (StatFormal.OTFD.Wave3.bandScore (c θ) (w θ)) y * wbar θ) →
    (∀ θ, (Measure.pi fun _ : Fin n => μ)
        {y | ∃ s, tWidth n (Fintype.card Θ) < |empCDF (StatFormal.OTFD.Wave3.bandScore (c θ) (w θ)) y s -
          (scoreCDF μ (StatFormal.OTFD.Wave3.bandScore (c θ) (w θ)) s).toReal|} ≤
        ENNReal.ofReal (2 * Real.exp (-2 * n * tWidth n (Fintype.card Θ) ^ 2))) →
      MeasurableSet {y : Fin n → T → ℝ | ∀ θ,
          scoreQuant μ (StatFormal.OTFD.Wave3.bandScore (c (θhat y)) (w (θhat y)))
              (1 - α - tWidth n (Fintype.card Θ)) * wbar (θhat y) ≤
            omegaHat α (StatFormal.OTFD.Wave3.bandScore (c (θhat y)) (w (θhat y))) y * wbar (θhat y) ∧
          omegaHat α (StatFormal.OTFD.Wave3.bandScore (c (θhat y)) (w (θhat y))) y * wbar (θhat y) ≤
            omegaHat α (StatFormal.OTFD.Wave3.bandScore (c θ) (w θ)) y * wbar θ ∧
          omegaHat α (StatFormal.OTFD.Wave3.bandScore (c θ) (w θ)) y * wbar θ ≤
            scoreQuant μ (StatFormal.OTFD.Wave3.bandScore (c θ) (w θ))
              (1 - α + tWidth n (Fintype.card Θ) + 2 / n) * wbar θ} ∧
        ENNReal.ofReal (1 - 1 / n) ≤ (Measure.pi fun _ : Fin n => μ) {y | ∀ θ,
          scoreQuant μ (StatFormal.OTFD.Wave3.bandScore (c (θhat y)) (w (θhat y)))
              (1 - α - tWidth n (Fintype.card Θ)) * wbar (θhat y) ≤
            omegaHat α (StatFormal.OTFD.Wave3.bandScore (c (θhat y)) (w (θhat y))) y * wbar (θhat y) ∧
          omegaHat α (StatFormal.OTFD.Wave3.bandScore (c (θhat y)) (w (θhat y))) y * wbar (θhat y) ≤
            omegaHat α (StatFormal.OTFD.Wave3.bandScore (c θ) (w θ)) y * wbar θ ∧
          omegaHat α (StatFormal.OTFD.Wave3.bandScore (c θ) (w θ)) y * wbar θ ≤
            scoreQuant μ (StatFormal.OTFD.Wave3.bandScore (c θ) (w θ))
              (1 - α + tWidth n (Fintype.card Θ) + 2 / n) * wbar θ}

/-- (i) CONDITIONAL on DKW–Massart for each candidate: the selected recalibrated band covers a new curve with
probability at least `1 − α − t − 1/n₂` (the event is measurable). -/
def width_coverage : Prop :=
  ∀ (T : Type) (Θ : Type) [Fintype Θ] [Nonempty Θ] (c w : Θ → T → ℝ) (μ : Measure (T → ℝ))
    [IsProbabilityMeasure μ] (n : ℕ) (α : ℝ) (θhat : (Fin n → T → ℝ) → Θ),
    1 ≤ n → 0 < α → α < 1 → (∀ θ t, 0 ≤ w θ t) →
    (∀ θ, Measurable (StatFormal.OTFD.Wave3.bandScore (c θ) (w θ))) →
    (∀ θ, MeasurableSet {y | θhat y = θ}) →
    (∀ θ, (Measure.pi fun _ : Fin n => μ)
        {y | ∃ s, tWidth n (Fintype.card Θ) < |empCDF (StatFormal.OTFD.Wave3.bandScore (c θ) (w θ)) y s -
          (scoreCDF μ (StatFormal.OTFD.Wave3.bandScore (c θ) (w θ)) s).toReal|} ≤
        ENNReal.ofReal (2 * Real.exp (-2 * n * tWidth n (Fintype.card Θ) ^ 2))) →
      MeasurableSet {z : (Fin n → T → ℝ) × (T → ℝ) | z.2 ∈ StatFormal.OTFD.Wave3.inflBand (c (θhat z.1))
          (w (θhat z.1)) (omegaHat α (StatFormal.OTFD.Wave3.bandScore (c (θhat z.1)) (w (θhat z.1))) z.1)} ∧
        ENNReal.ofReal (1 - α - tWidth n (Fintype.card Θ) - 1 / n) ≤
          ((Measure.pi fun _ : Fin n => μ).prod μ)
            {z | z.2 ∈ StatFormal.OTFD.Wave3.inflBand (c (θhat z.1)) (w (θhat z.1))
              (omegaHat α (StatFormal.OTFD.Wave3.bandScore (c (θhat z.1)) (w (θhat z.1))) z.1)}

/-! #### otfd B `thm:prob-content` -/

/-- (b) For every Borel `F` with `F#P_K = μ_K`: `P_K(F⁻¹{u ∈ supp μ_K : ρ(u) ≤ τ}) = c_K(τ)` for every `τ`, and, `c_K`
being continuous with `c_K(0) = 0`, `c_K(1) = 1`, `P_K(F⁻¹{u ∈ supp μ_K : ρ(u) ≤ c_K^{-1}(p)}) = p` for `p ∈ [0,1]`. -/
def prob_content_b : Prop :=
  ∀ (K : ℕ) (P μ : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (ρ : EuclideanSpace ℝ (Fin K) → ℝ),
    Measurable F → P.map F = μ → Measurable ρ →
      (∀ τ, P.real (F ⁻¹' {u | u ∈ μ.support ∧ ρ u ≤ τ}) = cdfK μ ρ τ) ∧
        (ContinuousOn (cdfK μ ρ) (Icc 0 1) → cdfK μ ρ 0 = 0 → cdfK μ ρ 1 = 1 →
          ∀ p ∈ Icc (0 : ℝ) 1, P.real (F ⁻¹' {u | u ∈ μ.support ∧ ρ u ≤ cdfKInv μ ρ p}) = p)

/-- (e) Image form, CONDITIONAL on the two inversion properties the proof derives from `∂φ* = (∂φ)^{-1}`: for every
Borel `A`, `F⁻¹(A) ∩ G' ⊆ Q'(A) ⊆ F⁻¹(A) ∪ Dᶜ`, `Q'(A)` is `P_K`-null-measurable and `P_K(Q'(A)) = μ_K(A)`; in
particular `P_K(Q'({ρ ≤ τ} ∩ supp μ_K)) = c_K(τ)`. -/
def prob_content_e : Prop :=
  ∀ (K : ℕ) (P μ : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    (F Q' : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (ρ : EuclideanSpace ℝ (Fin K) → ℝ)
    (G' D : Set (EuclideanSpace ℝ (Fin K))),
    Measurable F → P.map F = μ → Measurable ρ → MeasurableSet G' → MeasurableSet D → P G'ᶜ = 0 → P Dᶜ = 0 →
    (∀ z ∈ G', Q' (F z) = z) → (∀ u z, z ∈ D → Q' u = z → F z = u) →
      (∀ A : Set (EuclideanSpace ℝ (Fin K)), MeasurableSet A →
          F ⁻¹' A ∩ G' ⊆ Q' '' A ∧ Q' '' A ⊆ F ⁻¹' A ∪ Dᶜ ∧ NullMeasurableSet (Q' '' A) P ∧ P (Q' '' A) = μ A) ∧
        ∀ τ, P.real (Q' '' {u | ρ u ≤ τ ∧ u ∈ μ.support}) = cdfK μ ρ τ

/-! #### otfd B `thm:band-containment` -/

/-- CONDITIONAL on `prop:app-potential-consistency` (a.e. convergence of the fitted map on `A_{K,p}`), with bounded
essential range: for every `η > 0`, eventually, for all `t`, `x↑pop(t) ≤ x̂↑_n(t) + η` and `x̂↓_n(t) ≤ x↓pop(t) + η`. -/
def band_containment : Prop :=
  ∀ (K : ℕ) (T : Type) (μ : Measure (EuclideanSpace ℝ (Fin K))) (A : Set (EuclideanSpace ℝ (Fin K)))
    (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (Qn : ℕ → EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (mfrak : T → ℝ)
    (e : T → EuclideanSpace ℝ (Fin K)),
    MeasurableSet A → (∃ R : ℝ, ∀ᵐ u ∂μ.restrict A, ‖Q u‖ ≤ R) → (∃ C : ℝ, ∀ t, ‖e t‖ ≤ C) →
    (∀ᵐ u ∂μ.restrict A, Tendsto (fun n => Qn n u) atTop (𝓝 (Q u))) →
      ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t,
        (mfrak t : EReal) + popSupp μ A Q (e t) ≤ (mfrak t : EReal) + fitSupp A (Qn n) (e t) + (η : EReal) ∧
          (mfrak t : EReal) - fitSupp A (Qn n) (-e t) ≤ (mfrak t : EReal) - popSupp μ A Q (-e t) + (η : EReal)

end Claims

end StatFormal.Wave23a
