import StatFormal.Archive.Wave21b.Statements
import StatFormal.Archive.OTFD.Wave19a.Statements
import StatFormal.Archive.OTFD.Wave2.Statements
import StatFormal.Archive.Wave12b.Statements
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# FROZEN STATEMENTS — wave 22b (QUEUE rows 241, 250–259): otfd T `eq:L` (`lem:exp`), `eq:cK` (`lem:cK`),
# `lem:verified-content`, `prop:cf-M`; B `prop:certified-band-limit`, `thm:band-consistency`; C `thm:self-localization`,
# `lem:conditional-weights-unbounded`, `lem:full-support-region`, `prop:cond-transfer-consistency` (C
# `prop:conditional-potentials` skipped); discharge of the frozen Wave 21b band-limit / test-coverage premises

Sources (verbatim in `lean-formalisation/inventory/extracted/{otfd-T_tangent,otfd-B_bands,otfd-C_conditional}.md`;
current text under `otfd/papers/`):
* T `lem:exp` (`T_tangent/supp_moved.tex:833-848`, `eq:L`, `eq:expbounds`), `lem:cK` (`:607-627`, `eq:cK`),
  `lem:verified-content` (`:670-698`), `prop:cf-M` (`T_tangent/supp_toolkit.tex:442-482`, proof `:484-539`, with
  `def:cf-M` `:382-388`, `eq:tk-domain` `:67-70` and the population maps of `prop:transfer-M`).
* B `thm:band-consistency` (`B_bands/supplement.tex:851-869`, proof `:2085-2099`), `prop:certified-band-limit`
  (`:1127-1154`, proof `:2379-2398`, Laguerre potential `:1784-1797`).
* C `thm:self-localization` (`C_conditional/main.tex:498-515`, proof `supplement.tex:654-701`, `lem:self-potentials`
  bounds `:560-573`, weights `main.tex:335-347`), `lem:conditional-weights-unbounded` (`supplement.tex:114-133`, proof
  `:135-197`), `lem:full-support-region` (`:1035-1048`, proof `:1050-1078`), `prop:conditional-potentials`
  (`:1082-1086`), `prop:cond-transfer-consistency` (`main.tex:1017-1025`, proof `supplement.tex:2116-2153`), with
  `ass:conditional-oos` (`main.tex:654-661`); Wave 21b `thm:conditional-band-limits`, `cor:conditional-test-coverage`.
Imports the frozen `Wave21b` (`supE`, `cond_band_*`; through it `Wave17a` `hPop`, `Gaps1`), `OTFD/Wave19a` (`extTop`,
Tau Ceti `subdifferential`; through it `OTFD/Wave8c` `IsRankPair`), `OTFD/Wave2` (`cappedSimplex`; through it `Bands`
`score`, `gap`, `softmax`, `simplex`, `IsSimplexProj`) and `Wave12b` (`Euc`, `wEmp`, `locMass`, `vn`, Tau Ceti
`wassersteinEDist`) statements, not copied. No `StatFormal/Foundations` library file is imported.

Covered:
* B `thm:band-consistency` and C `thm:conditional-band-limits` (two-sided), DISCHARGED from potential convergence:
  `band_consistency` (uniform in `p ≤ 1 − δ` and `t`, every subgradient selection, finite population edges).
* C one-sided band limit and test coverage, DISCHARGED from potential convergence: `cond_maps_ae` (the Wave 21b premise
  `Q_n → Q` `μ_K`-a.e.), `cond_band_one_sided_potentials`, `cond_test_coverage_potentials` (inflated bands).
* C `prop:cond-transfer-consistency`: `cond_transfer_consistency` (a.s., every hard selection; `F(Z) ∈ int U_K` at a
  differentiability point), `cond_transfer_consistency_prob` ("hence in probability").
* B `prop:certified-band-limit`: `cert_hpartial` (`H^∂ = max_{J_0}⟨v, Z_j⟩`, bounds every selected hard map),
  `cert_slack` (the slack display), `cert_band_consistency` (certified edges converge when the slack vanishes).
* T `lem:exp`: `exp_bounds` (`eq:expbounds`), `exp_bounds_embed` (the `L_bΛ` bound), `exp_Lb_finite` (`L_b < ∞`).
* T `lem:cK`: `cK_formula` (`eq:cK`), `cK_shape`, `cK_strict` ((i)), `cK_convexity` ((ii)), `cK_proj` (the finite-`D`
  projected ball law: `0 < W_K ≤ 1` a.s., `W_K < 1` iff `K < D`, `‖Π_K U‖ = R W_K`, independence).
* T `lem:verified-content`: `vc_content` ((i), (ii) on the DKW event), `vc_prob` (probability `≥ 1 − δ`, conditional
  on one-sided DKW–Massart per half), `vc_numeric` (`κ_N(10⁻⁶) + 1/(4N) ≤ 0.00852`, `N = 10⁵`).
* C `thm:self-localization`: `selfloc_weight_ent`, `selfloc_weight_quad` (`eq:self-effective-bounds`),
  `selfloc_staircase` (the diagonal-schedule lemma), `selfloc_consistency` ("Consequently …", conditional).
* C `lem:full-support-region` (ii), (iii) for the cubic law: `cubic_density`, `cubic_region` ((i) is Gaps 1).
* C `lem:conditional-weights-unbounded`: `cwu_truncation` (`eq:unbounded-truncation`), `cwu_prob` (the in-probability
  statement, from the certified bounded Wave 12b `cw_prob`).
* T `prop:cf-M`: `cfM_i`, `cfM_ii` ((i), (ii) in fixed charts), `cfM_step0` ((iv) Step 0), `cfM_iv` ((iv), conditional
  on C's Lemma 8.3 and Theorem 5.6 conclusions).

Not covered (declared):
* C `prop:conditional-potentials` (SKIPPED, far harder than its L3 estimate: identifying the limit needs Brenier–McCann
  uniqueness of the convex potential on `int U_K`, Arzelà–Ascoli on conjugates, the duality sandwich under weak
  convergence of the weighted laws and conjugate epi-convergence; its conclusion — local uniform convergence of the
  normalized potentials on `int U_K` — is the explicit premise of every discharge claim above). So C band limits,
  test coverage and counterfactuals remain conditional on exactly this lemma (plus, for counterfactuals, C's
  `lem:cond-rank-consistency`).
* B `thm:band-consistency`: the limit `→ 0` of `E_K sup_S ‖Q̂_n − Q‖` needs `prop:app-potential-consistency` (L3, same
  obstruction; premise); the a.s. wrapper (claims are per realisation); the bound itself is Wave 21b.
* B `prop:certified-band-limit`: the lower inequality `x̂ ≤ x̄` (`prop:band-certificate`(iv), certified); "for example
  when `P_K` is boundedly supported and `Σ_n(p) → 0`" (with the certified `Bands`/`Wave2` bounds it is arithmetic);
  the window version (`thm:band-consistency-shell`, not in this queue).
* T `lem:exp`: `d_M` as the infimum of lengths on a Riemannian `M` (encoded by `LengthBound`); smoothness of `Exp`.
* T `lem:cK`: `D = ∞` (Gaussian measures on `H`); that a nondegenerate Gaussian on `ℝ^D` has a density (hypothesis
  `P.map G ≪ Leb`; "`C` injective").
* T `lem:verified-content`: the one-sided DKW inequality with Massart's constant (missing; hypothesis per half); the
  sentence about the levels `p = 0.25, 0.5, 0.9` (`2Np` integer: the third clause of (i)).
* C `thm:self-localization`: the fixed-strength a.s. uniform convergence (uniform SLLN over an equicontinuous class)
  and the small-strength uniform convergence (uniform Laplace principle, `lem:self-potentials`): premises of
  `selfloc_consistency`; the quadratic `n η_n/log n → ∞` and counting-normalisation sentences.
* C `lem:full-support-region` (ii), (iii) for the ball law (Gaussian mixture density; reshaping).
* C `lem:conditional-weights-unbounded`: the almost-sure version (needs an a.s. bounded lemma; Wave 12b certifies the
  in-probability one only).
* T `prop:cf-M` (iii) (flat case = paper C through `prop:chart`(ii)); the moving-chart remarks; (iv)'s W₁ convergence of
  the weighted laws (`lem:cf-schedule`) and C's Lemma 8.3 / Theorem 5.6 / Assumption 5.5 (premises: their
  conclusions); "with in-probability premises … in probability".

Encodings (to be checked by the critic):
* `ℝ^K = Euc K = EuclideanSpace ℝ (Fin K)` (B claims in `Bands` coordinates `Fin K → ℝ` with `⬝ᵥ`); convex potentials
  are real functions convex on the open convex `C = int U_K`; `∂g(u)` is Tau Ceti's subdifferential of the
  `+∞`-extension `extTop C g` (fitted maps: any selection, entropic gradients included); potential convergence is
  `TendstoUniformlyOn` on every compact `S ⊆ C`; `Q = ∇χ` `μ`-a.e. (`gradient`, junk `0` only on the null set of
  non-differentiability points); limits "→ 0" as "for every `η > 0` eventually `≤ η`"; claims are per realisation
  (the a.s. wrappers are immediate), except `cond_transfer_consistency` (a.s. over `Ω`).
* `supp μ_K` convex `U_K` with `μ_K ≪ Leb` encoded as `Convex ℝ U`, `μ Uᶜ = 0` (compactness unused).
* certified-band-limit: `χ_n = laguerre` (max of the scores, `b_j = Z_j`), `∂χ_n = fullSub` (global subgradients),
  `H^∂(v)` as the `IsGreatest` of `subVals` (attained), `J_0 = {j : δ_j = 0}`, caps `e^{−δ_j/ε}`, `x̄^↑ − 𝔪` any `q` in
  the capped simplex; `cert_band_consistency`: `x̄_n(t) − 𝔪` any real squeezed as printed, `χ_n` any convex potentials
  (`g`), the fitted map a selection for convex `ĝ_n` (`gh`) converging to the same `χ`.
* lem:exp: `Exp_{m(t)} = Ex t : V → M` (pseudo-e-metric `M`), `d(Exp_{m(t)})_v = D t v : V →L W` (an isometric copy `W`
  of the tangent spaces), `LengthBound`, `L_b = Lb` in `ℝ≥0∞` (no junk), `D_2² = ∫⁻ d_M²` for any measure on `T`
  (measurable `‖v − w‖`), `D_∞` an `⨆` in `ℝ≥0∞`; `eq:Hembed` as linear `ι : H → (T → V)` with `‖ι x t‖ ≤ Λ‖x‖`.
* lem:cK: `RadialLaw` (`W ∈ (0,1]` a.s., `R ~ Unif[0,1]` independent); `c_K = cK = P(RW ≤ ρ)`, `f_K = fK` (Bochner;
  integrable for `x > 0`, used only there and as an interval integrand); `w* = ess sup W` characterised by
  `W ≤ w*` a.s. and `P(W > w) > 0` for `w < w*`; `‖Π_K x‖ = normProj` (first `K` coordinates), `W_K = Wproj`.
* verified-content: radii indexed by `Fin 2 × Fin N` (antithetic halves), `ĉ = empCount/(2N)`, order statistics
  `ordStat` (`sInf`; attained for `1 ≤ j ≤ 2N`, the only indices used), `j_p = max{1, r}` for any integer `r` with
  `|r − 2Np| ≤ 1/2` (any tie rule), DKW per half as an outer-probability hypothesis, the good event a measurable subset.
* self-localization: the quadratic weights are the simplex projection `P_Δ` of the printed scores, with the
  out-of-sample threshold `H(x)` of `eq:self-pop` as a hypothesis (`Σ_i [H(x) + H_i − ‖x − C_i‖²]_+ = nη`) and the
  potential bounds of `lem:self-potentials`; `W₁` abstracted to any pseudo-e-metric space of laws; strengths
  `σ_j ↓ 0` indexed by `j`, the schedule `ε_{X,n} = σ_{s(n)}`; `n_eff ≥ 1/max_i w_i` via `log n · max_i w_i → 0`.
* cubic law: `⊗_k Unif(−λ_k/2, λ_k/2)` on `Fin K → ℝ` transported by `toLp`; `A_{K,p} = U_K ∩ B̄(0, r)`, `r = τ_p D_∞ > 0`.
* unbounded weights: the triangular-array model of Wave 12b `cw_prob`; `π_L = radProj`, `‖z‖1{‖z‖ > L} = tailNorm`;
  (ii) weak continuity at `x` within `D = supp P_C` (bounded continuous tests); (iv) in the weaker "∃ L, eventually ≤ θ"
  form; events as outer probabilities.
* cf-M: charts `QueryChart` (`Φ`, `Φ⁻¹` measurable, inverse on `B̄_B`, `ν_a(B̄_Bᶜ) = 0`), curve space `Y` with a
  measurable diagonal; population rank pairs `IsRankPair` (frozen Wave 8c; `F#ν = μ`, `Q#μ = ν`, mutually inverse
  a.e.); "preserves conditional depth and sign" as "preserves the rank `F`" (equivalent: depth and sign determine a
  nonzero rank since `c_K` is strictly increasing); Step 0 with `ξ ↦ ν_ξ` weakly continuous within `supp P_W`
  (implied by `W₁`-continuity); (iv) with `Φ_{x'}(z) = (t ↦ Exp_t(v̄(t) + ι z(t)))`.

Critic notes:
* All 32 claims are proved in `OTFD/Wave22b/Route{Convex,Cert,Exp,CK,VC,SelfLoc,Cubic,Unbounded,CfM}.lean` (axioms:
  propext, Classical.choice, Quot.sound). Routes use the certified routes of Wave 19a (`subgrad_conv_point`,
  `subgrad_conv_unif`, `grad_mem_subdiff`), Wave 21b (`cond_band_*`, `cond_test_coverage_inflated`), Gaps 1
  (`full_support_region`), Bands (`band_gap_zero_iff`), Wave 2 (`weighted_slack`), Wave 12b (`cw_prob`), Tau Ceti
  (W₁ triangle, displacement bound, weak + moments ⇒ W₁) and Mathlib (Rademacher, `Convex.addHaar_frontier`,
  portmanteau, Borel–Cantelli).
* Near-definitional / compositional (flag for the critic): `exp_bounds`, `exp_bounds_embed` (the mean-value step from
  `LengthBound`, not a Lipschitz hypothesis — unlike the Wave 21b `tubes_metric` tautology); `cert_slack`,
  `cert_band_consistency`, `cond_band_one_sided_potentials`, `cond_test_coverage_potentials`, `cfM_iv` (compositions
  of certified results with the new convex-analysis steps); `cfM_i`, `cfM_ii` (conjugation of Wave 8c).
* No statement was found false. `eq:self-effective-bounds` (quadratic) needs the extension's threshold `H(x)` (the
  scores' range alone gives only `(η + 7d²/2)/(nη)`); the printed entropic constant `3d²` is not sharp (`5d²/2`).
* Discharge: the Wave 21b premises `sup_S ‖T − Q‖ ≤ η` and `Q_n → Q` `μ_K`-a.e. on `A` are now theorems of potential
  convergence (`band_consistency`, `cond_maps_ae`); the C limits remain conditional on `prop:conditional-potentials`.
* Critic (2026-10-15): ACCEPT-WITH-NOTE, all 32 TRUE, none tautological. `band_consistency` is conditional on B
  `prop:app-potential-consistency` (its hypotheses are exactly B's (a)/(b)). Genuinely discharged from Wave21b:
  `Q_n → Q` μ-a.e. (Rademacher + null boundary + Rockafellar 24.5) and the edge-deficit premise of
  `cond_test_coverage_inflated`; `sup_S‖T−Q‖ ≤ η` only implicitly (folded into the edge limit); `cond_test_coverage_nested`
  not discharged. All C claims remain conditional on `prop:conditional-potentials` (counterfactual claims also on
  `lem:cond-rank-consistency`). NOT COVERED (declared): the "in-probability premises ⇒ in-probability conclusions" forms of
  C `thm:conditional-band-limits` and `prop:cond-transfer-consistency`. `selfloc_consistency` covers only the
  "Consequently" step (fixed-strength uniform a.s. convergence and bias → 0 remain uncertified). `vc_prob` assumes
  DKW–Massart for each half (Massart Thm 1). `exp_bounds` is near-definitional. The quadratic self-localization bound
  holds as printed (H(x) ≤ η/2 + 3d²/2 from `lem:self-potentials`); C's proof does not justify measurability of
  `sup_{x∈D}` (minor; T's `lem:cf-schedule` does).
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/
set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace BoundedContinuousFunction

namespace StatFormal.OTFD.Wave22b

open StatFormal.OTFD.Wave19a (extTop)
open StatFormal.Wave12b (Euc wEmp locMass vn)

/-! ### Shared: subgradient supports (B, C) -/

/-- The full subdifferential support `H^∂(v) = sup_{u ∈ A} sup_{ξ ∈ ∂g(u)} ⟨v, ξ⟩` of the `+∞`-extension of `g` off
the open set `C`, in `EReal`. -/
def supSub {K : ℕ} (C A : Set (Euc K)) (g : Euc K → ℝ) (v : Euc K) : EReal :=
  ⨆ u ∈ A, ⨆ ξ ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop C g) u, ((⟪v, ξ⟫ : ℝ) : EReal)

/-! ### B `prop:certified-band-limit` (coordinates `Fin K → ℝ`, as in the frozen `Bands`) -/

section CertLimit
variable {n K : ℕ}

/-- The Laguerre potential `χ_n(u) = max_j (a_j + ⟨b_j, u⟩)` of the scores (`b_j = Z_j`). -/
def laguerre (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ) (u : Fin K → ℝ) : ℝ :=
  ⨆ j, StatFormal.OTFD.Bands.score a b j u

/-- The (global) subdifferential `∂χ(u) = {ξ : χ(y) ≥ χ(u) + ⟨ξ, y − u⟩ ∀ y}` of a real function on `ℝ^K`. -/
def fullSub (χ : (Fin K → ℝ) → ℝ) (u : Fin K → ℝ) : Set (Fin K → ℝ) :=
  {ξ | ∀ y, χ u + ξ ⬝ᵥ (y - u) ≤ χ y}

/-- The set `{⟨v, ξ⟩ : u ∈ A, ξ ∈ ∂χ(u)}` whose supremum is `H^∂(v)`. -/
def subVals (χ : (Fin K → ℝ) → ℝ) (A : Set (Fin K → ℝ)) (v : Fin K → ℝ) : Set ℝ :=
  {r | ∃ u ∈ A, ∃ ξ ∈ fullSub χ u, r = v ⬝ᵥ ξ}

end CertLimit

/-! ### T `lem:exp` (`eq:L`) -/

section Exp
variable {T V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- `L_b = sup_{t, ‖v‖ ≤ b} ‖d(Exp_{m(t)})_v‖_op`, in `ℝ≥0∞` (`eq:L`); `D t v` is the differential of `Exp_{m(t)}` at
`v`, read in an isometric copy `W` of the tangent spaces. -/
def Lb (D : T → V → V →L[ℝ] W) (b : ℝ) : ℝ≥0∞ :=
  ⨆ t, ⨆ v ∈ Metric.closedBall (0 : V) b, ‖D t v‖ₑ

/-- The Riemannian length bound for the exponential image of a segment:
`d_M(Exp v, Exp w) ≤ ∫_0^1 ‖d(Exp)_{v + s(w − v)}(w − v)‖ ds` (`d_M` is the infimum of lengths). -/
def LengthBound {M : Type*} [PseudoEMetricSpace M] (Ex : T → V → M) (D : T → V → V →L[ℝ] W) : Prop :=
  ∀ t v w, edist (Ex t v) (Ex t w) ≤ ∫⁻ s in Icc (0 : ℝ) 1, ‖D t (v + s • (w - v)) (w - v)‖ₑ

end Exp

/-! ### T `lem:cK` (`eq:cK`) -/

section CK
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The radial distribution function `c_K(ρ) = P(R W_K ≤ ρ) = μ_K{‖u‖ ≤ ρ}` (`‖Π_K U‖ = R W_K`). -/
def cK (P : Measure Ω) (W R : Ω → ℝ) (ρ : ℝ) : ℝ := P.real {ω | R ω * W ω ≤ ρ}

/-- The density `f_K(x) = E[W_K⁻¹ 1{W_K > x}]`. -/
def fK (P : Measure Ω) (W : Ω → ℝ) (x : ℝ) : ℝ := ∫ ω, {ω | x < W ω}.indicator (fun ω => (W ω)⁻¹) ω ∂P

/-- The setting of `lem:cK`: `W ∈ (0,1]` a.s., `R ~ Unif(0,1)` independent of `W`. -/
def RadialLaw (P : Measure Ω) (W R : Ω → ℝ) : Prop :=
  IsProbabilityMeasure P ∧ Measurable W ∧ Measurable R ∧ IndepFun W R P ∧
    P.map R = volume.restrict (Icc (0 : ℝ) 1) ∧ ∀ᵐ ω ∂P, 0 < W ω ∧ W ω ≤ 1

/-- `‖Π_K x‖ = (Σ_{k < K} x_k²)^{1/2}` on `ℝ^D` (the first `K` coordinates of the orthonormal basis). -/
def normProj {D : ℕ} (K : ℕ) (x : Euc D) : ℝ :=
  Real.sqrt (∑ i ∈ Finset.univ.filter (fun i : Fin D => (i : ℕ) < K), x i ^ 2)

/-- `W_K = ‖Π_K G‖ / ‖G‖`. -/
def Wproj {D : ℕ} (K : ℕ) (G : Ω → Euc D) (ω : Ω) : ℝ := normProj K (G ω) / ‖G ω‖

end CK

/-! ### T `lem:verified-content` -/

section VC
variable {ι : Type*} [Fintype ι]

/-- `#{i : x_i ≤ r}` (so `ĉ(r) = #{i : x_i ≤ r}/m`). -/
def empCount (x : ι → ℝ) (r : ℝ) : ℕ := (Finset.univ.filter (fun i => x i ≤ r)).card

/-- The order statistic `x_{(j)} = inf{r : #{i : x_i ≤ r} ≥ j}` (the `j`-th smallest value for `1 ≤ j ≤ m`). -/
def ordStat (x : ι → ℝ) (j : ℕ) : ℝ := sInf {r | j ≤ empCount x r}

/-- `κ_N(δ) = (log(2/δ)/(2N))^{1/2}`. -/
def kappaN (N : ℕ) (δ : ℝ) : ℝ := Real.sqrt (Real.log (2 / δ) / (2 * N))

/-- The conclusions (i), (ii) of `lem:verified-content` for the `2N` radii `x`, the radial distribution function `c`
and the loss `κ`, simultaneously for every `p ∈ (0,1]`: `j_p = max{1, r}` with `r` any nearest integer to `2Np`;
`ρ̂⁺(p) = x_{(⌈2N(p+κ)⌉)}` if `p + κ ≤ 1` and `1` otherwise. -/
def VCGood (N : ℕ) (x : ι → ℝ) (c : ℝ → ℝ) (κ : ℝ) : Prop :=
  ∀ p : ℝ, 0 < p → p ≤ 1 →
    (∀ (r : ℤ) (j : ℕ), |(r : ℝ) - 2 * N * p| ≤ 1 / 2 → (j : ℤ) = max 1 r →
      (j : ℝ) / (2 * N) - κ ≤ c (ordStat x j) ∧ p - κ - 1 / (4 * N) ≤ (j : ℝ) / (2 * N) - κ ∧
      ((∃ k : ℤ, (k : ℝ) = 2 * N * p) → p - κ ≤ c (ordStat x j))) ∧
    p ≤ c (if p + κ ≤ 1 then ordStat x ⌈2 * N * (p + κ)⌉₊ else 1)

end VC

/-! ### C `thm:self-localization` -/

/-! ### C `lem:full-support-region` (cubic law) -/

section Cubic
variable {K : ℕ}

/-- The closed box `U_K = ∏_k [−λ_k/2, λ_k/2]`. -/
def closedBox (lam : Fin K → ℝ) : Set (Euc K) := {u | ∀ k, |u k| ≤ lam k / 2}

/-- The open box `∏_k (−λ_k/2, λ_k/2)`. -/
def openBox (lam : Fin K → ℝ) : Set (Euc K) := {u | ∀ k, |u k| < lam k / 2}

/-- The cubic law `μ_K = ⊗_k Unif(−λ_k/2, λ_k/2)`, transported from `Fin K → ℝ` to `ℝ^K`. -/
def cubicLaw (lam : Fin K → ℝ) : Measure (Euc K) :=
  (Measure.pi fun k => (ENNReal.ofReal (lam k))⁻¹ • volume.restrict (Ioo (-(lam k / 2)) (lam k / 2))).map
    (WithLp.toLp 2 : (Fin K → ℝ) → Euc K)

end Cubic

/-! ### C `lem:conditional-weights-unbounded` -/

section Unbounded
variable {K : ℕ}

/-- The radial projection `π_L` onto `B̄(0, L)`. -/
def radProj (L : ℝ) (z : Euc K) : Euc K := if ‖z‖ ≤ L then z else (L / ‖z‖) • z

/-- `‖z‖ 1{‖z‖ > L}`. -/
def tailNorm (L : ℝ) (z : Euc K) : ℝ := if L < ‖z‖ then ‖z‖ else 0

end Unbounded

/-! ### T `prop:cf-M` -/

section CfM
variable {K : ℕ} {Y : Type*} [MeasurableSpace Y]

/-- A query chart: `Φ_a(z) = E_{c_a}(v̄ + ι_K z)` and `Φ_a⁻¹ = Π_K(L_{c_a} − v̄)` measurable, mutually inverse on the
coefficient ball `B̄_B` (`eq:tk-domain`), the coefficient law `ν_a` carried by `B̄_B`. -/
def QueryChart (B : ℝ) (Φ : Euc K → Y) (Φinv : Y → Euc K) (ν : Measure (Euc K)) : Prop :=
  Measurable Φ ∧ Measurable Φinv ∧ (∀ z ∈ Metric.closedBall (0 : Euc K) B, Φinv (Φ z) = z) ∧
    ν (Metric.closedBall (0 : Euc K) B)ᶜ = 0

/-- `T_{x→x'} = Φ_{x'} ∘ Q_{x'} ∘ F_x ∘ Φ_x⁻¹` (`def:cf-M`). -/
def cfT (Φ' : Euc K → Y) (Q' F : Euc K → Euc K) (Φinv : Y → Euc K) (y : Y) : Y := Φ' (Q' (F (Φinv y)))

end CfM

namespace Claims

open StatFormal.Wave17a (hPop)
open StatFormal.Wave21b (supE)
open StatFormal.OTFD.Bands (score gap)
open StatFormal.OTFD.Wave2 (cappedSimplex)
open StatFormal.OTFD.Wave8c (IsRankPair)

/-! #### B `thm:band-consistency` and C `thm:conditional-band-limits` (two-sided): potentials ⇒ edges -/

/-- Uniform two-sided band consistency on `0 < p ≤ 1 − δ` from local uniform convergence of the convex potentials
(the conclusion of B `prop:app-potential-consistency` / C `prop:conditional-potentials`, a premise here):
`χ` convex on the open convex `C = int U_K`, differentiable on an open `O` with `A_{1−δ} ⊆ O ⊆ C` (interior levels (a),
local continuity (b)), `Q = ∇χ` `μ`-a.e. on `O`, nested compact convex level regions with nonempty interior inside
`supp μ`, and fitted maps `T_n` any subgradient selections of the fitted potentials on `A_{1−δ}` (entropic gradients
or hard Laguerre selections at ties). Then for every `η > 0`, eventually every band edge is within `η` of the
population edge, uniformly in `p ≤ 1 − δ` and `t` (and the population edges are finite). -/
def band_consistency : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ : Measure (Euc K)) (A : ℝ → Set (Euc K)) (C O : Set (Euc K)) (χ : Euc K → ℝ)
    (g : ℕ → Euc K → ℝ) (Q : Euc K → Euc K) (T : ℕ → Euc K → Euc K) (e : 𝒯 → Euc K) (δ EK : ℝ),
    IsOpen C → Convex ℝ C → ConvexOn ℝ C χ → (∀ n, ConvexOn ℝ C (g n)) →
    (∀ S ⊆ C, IsCompact S → TendstoUniformlyOn g χ atTop S) →
    IsOpen O → A (1 - δ) ⊆ O → O ⊆ C → (∀ u ∈ O, DifferentiableAt ℝ χ u) →
    (∀ᵐ u ∂μ, u ∈ O → Q u = gradient χ u) → IsCompact (A (1 - δ)) →
    (∀ p, 0 < p → p ≤ 1 - δ → IsCompact (A p) ∧ Convex ℝ (A p) ∧ (interior (A p)).Nonempty ∧
      A p ⊆ μ.support ∧ A p ⊆ A (1 - δ)) →
    (∀ n, ∀ u ∈ A (1 - δ), T n u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop C (g n)) u) →
    (∀ t, ‖e t‖ ≤ EK) →
      ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ p, 0 < p → p ≤ 1 - δ → ∀ t, ∀ v ∈ ({e t, -e t} : Set (Euc K)),
        ∃ r s : ℝ, hPop μ (A p) Q v = r ∧ supE (A p) (T n) v = s ∧ |s - r| ≤ η

/-! #### C `thm:conditional-band-limits` (one-sided): discharge of the Wave 21b premise -/

/-- One-sided band limit from potential convergence: `μ_K ≪ Leb` carried by a convex `U_K`, the convex potentials
converge locally uniformly on `int U_K` to `χ` with `Q = ∇χ` `μ_K`-a.e., and the fitted maps are subgradient selections
of the fitted potentials on `int U_K`. At a level with bounded essential range, the edge deficit vanishes. (This
discharges the premise `Q_n → Q` `μ_K`-a.e. on `A` of the frozen Wave 21b `cond_band_one_sided`.) -/
def cond_band_one_sided_potentials : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ : Measure (Euc K)) (U A : Set (Euc K)) (χ : Euc K → ℝ) (g : ℕ → Euc K → ℝ)
    (Q : Euc K → Euc K) (Qn : ℕ → Euc K → Euc K) (e : 𝒯 → Euc K) (R EK : ℝ),
    μ ≪ volume → Convex ℝ U → μ Uᶜ = 0 → ConvexOn ℝ (interior U) χ → (∀ n, ConvexOn ℝ (interior U) (g n)) →
    (∀ S ⊆ interior U, IsCompact S → TendstoUniformlyOn g χ atTop S) → Q =ᵐ[μ] gradient χ →
    (∀ n, ∀ u ∈ interior U, Qn n u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n)) u) →
    MeasurableSet A → (∀ᵐ u ∂μ.restrict A, ‖Q u‖ ≤ R) → (∀ t, ‖e t‖ ≤ EK) →
      ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t,
        hPop μ A Q (e t) ≤ supE A (Qn n) (e t) + η ∧ hPop μ A Q (-e t) ≤ supE A (Qn n) (-e t) + η

/-- The pointwise premise itself: under the same hypotheses, `Q_n(u) → Q(u)` for `μ_K`-a.e. `u` (every `u` that lies in
`int U_K`, is a differentiability point of `χ` and has `Q(u) = ∇χ(u)`, a set of full `μ_K`-measure). -/
def cond_maps_ae : Prop :=
  ∀ (K : ℕ) (μ : Measure (Euc K)) (U : Set (Euc K)) (χ : Euc K → ℝ) (g : ℕ → Euc K → ℝ)
    (Q : Euc K → Euc K) (Qn : ℕ → Euc K → Euc K),
    μ ≪ volume → Convex ℝ U → μ Uᶜ = 0 → ConvexOn ℝ (interior U) χ → (∀ n, ConvexOn ℝ (interior U) (g n)) →
    (∀ S ⊆ interior U, IsCompact S → TendstoUniformlyOn g χ atTop S) → Q =ᵐ[μ] gradient χ →
    (∀ n, ∀ u ∈ interior U, Qn n u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n)) u) →
      ∀ᵐ u ∂μ, u ∈ interior U ∧ DifferentiableAt ℝ χ u ∧ Tendsto (fun n => Qn n u) atTop (𝓝 (Q u))

/-! #### C `prop:cond-transfer-consistency` -/

/-- Consistent counterfactuals: the rank-map consistency of `lem:cond-rank-consistency` at `x` (a.s., `F̂_n(z) → F(z)` at
every `z` of a set `D_F` carrying `Z`), `F#P_{K,x} = μ_K` with `μ_K ≪ Leb` carried by a convex `U_K`, and a.s. local
uniform convergence on `int U_K` of the convex fitted potentials at `x'` to `χ'` with `Q' = ∇χ'` `μ_K`-a.e. Then a.s.
`F(Z)` lies in `int U_K` at a differentiability point of `χ'`, `T(Z) = Q'(F(Z)) = ∇χ'(F(Z))`, and every subgradient
selection `Q̂_n` of the fitted potential gives `Q̂_n(F̂_n(Z)) → T(Z)`. -/
def cond_transfer_consistency : Prop :=
  ∀ (K : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (μ : Measure (Euc K)) (U DF : Set (Euc K))
    (Z : Ω → Euc K) (F : Euc K → Euc K) (Fh : ℕ → Ω → Euc K → Euc K) (χ' : Euc K → ℝ)
    (g : ℕ → Ω → Euc K → ℝ) (Q' : Euc K → Euc K) (Qh : ℕ → Ω → Euc K → Euc K),
    μ ≪ volume → Convex ℝ U → μ Uᶜ = 0 → Measurable Z → Measurable F → P.map (fun ω => F (Z ω)) = μ →
    (∀ᵐ ω ∂P, Z ω ∈ DF) → (∀ᵐ ω ∂P, ∀ z ∈ DF, Tendsto (fun n => Fh n ω z) atTop (𝓝 (F z))) →
    ConvexOn ℝ (interior U) χ' → Q' =ᵐ[μ] gradient χ' →
    (∀ᵐ ω ∂P, (∀ n, ConvexOn ℝ (interior U) (g n ω)) ∧
      ∀ S ⊆ interior U, IsCompact S → TendstoUniformlyOn (fun n => g n ω) χ' atTop S) →
    (∀ n ω, ∀ u ∈ interior U, Qh n ω u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n ω)) u) →
      ∀ᵐ ω ∂P, F (Z ω) ∈ interior U ∧ DifferentiableAt ℝ χ' (F (Z ω)) ∧ Q' (F (Z ω)) = gradient χ' (F (Z ω)) ∧
        Tendsto (fun n => Qh n ω (Fh n ω (Z ω))) atTop (𝓝 (Q' (F (Z ω))))

/-- "… hence in probability": under the same hypotheses, a finite `P` and measurable fitted counterfactuals, the
convergence holds in `P`-probability. -/
def cond_transfer_consistency_prob : Prop :=
  ∀ (K : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] (μ : Measure (Euc K))
    (U DF : Set (Euc K)) (Z : Ω → Euc K) (F : Euc K → Euc K) (Fh : ℕ → Ω → Euc K → Euc K) (χ' : Euc K → ℝ)
    (g : ℕ → Ω → Euc K → ℝ) (Q' : Euc K → Euc K) (Qh : ℕ → Ω → Euc K → Euc K),
    μ ≪ volume → Convex ℝ U → μ Uᶜ = 0 → Measurable Z → Measurable F → P.map (fun ω => F (Z ω)) = μ →
    (∀ᵐ ω ∂P, Z ω ∈ DF) → (∀ᵐ ω ∂P, ∀ z ∈ DF, Tendsto (fun n => Fh n ω z) atTop (𝓝 (F z))) →
    ConvexOn ℝ (interior U) χ' → Q' =ᵐ[μ] gradient χ' →
    (∀ᵐ ω ∂P, (∀ n, ConvexOn ℝ (interior U) (g n ω)) ∧
      ∀ S ⊆ interior U, IsCompact S → TendstoUniformlyOn (fun n => g n ω) χ' atTop S) →
    (∀ n ω, ∀ u ∈ interior U, Qh n ω u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n ω)) u) →
    (∀ n, AEStronglyMeasurable (fun ω => Qh n ω (Fh n ω (Z ω))) P) →
      TendstoInMeasure P (fun n ω => Qh n ω (Fh n ω (Z ω))) atTop (fun ω => Q' (F (Z ω)))

/-! #### B `prop:certified-band-limit` -/

/-- `H^∂(v) = max_{j ∈ J_0} ⟨v, Z_j⟩`: on a nonempty compact region, `J_0 = {j : δ_j = 0}` is nonempty, and whenever
`M_0` is the maximum of `⟨v, b_j⟩` over `J_0`, it is the maximum of `⟨v, ξ⟩` over `u ∈ A` and all subgradients
`ξ ∈ ∂χ_n(u)` of the Laguerre potential (so it bounds the edge of every selected hard map). -/
def cert_hpartial : Prop :=
  ∀ (n K : ℕ) (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ) (A : Set (Fin K → ℝ)) (v : Fin K → ℝ),
    0 < n → IsCompact A → A.Nonempty →
      {j | gap a b A j = 0}.Nonempty ∧
      ∀ M0, IsGreatest ((fun j => v ⬝ᵥ b j) '' {j | gap a b A j = 0}) M0 →
        IsGreatest (subVals (laguerre a b) A v) M0

/-- The slack display: for every `q` in the capped simplex of the exact-gap entropic caps (in particular the knapsack
optimum defining `x̄^↑ − 𝔪`), `Σ_j q_j c_j ≤ H^∂ + min{1, Σ_n(p)} [max_j c_j − H^∂]`, `c_j = ⟨v, Z_j⟩`, `v = 𝐞(t)`. -/
def cert_slack : Prop :=
  ∀ (n K : ℕ) (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ) (A : Set (Fin K → ℝ)) (v : Fin K → ℝ) (ε Hd : ℝ),
    0 < n → 0 < ε → IsCompact A → A.Nonempty → IsGreatest (subVals (laguerre a b) A v) Hd →
      ∀ q ∈ cappedSimplex (fun j => Real.exp (-gap a b A j / ε)),
        ∑ j, q j * (v ⬝ᵥ b j) ≤
          Hd + min 1 (∑ j ∈ Finset.univ.filter (fun j => gap a b A j ≠ 0), Real.exp (-gap a b A j / ε)) *
            ((⨆ j, v ⬝ᵥ b j) - Hd)

/-- Certificate consistency: under the hypotheses of `thm:band-consistency` at a fixed level region `A ⊆ S`, a certified
edge `x̄_n(t)` (relative to `𝔪`) squeezed between the fitted edge of a subgradient selection `T_n` of convex potentials
`ĝ_n` and the full-subdifferential support of the Laguerre potentials `χ_n` plus a slack converges to the population
edge uniformly in `t`, along every sequence on which the slack tends to `0` uniformly in `t`. (The lower edge is the
same statement with `−𝐞`.) -/
def cert_band_consistency : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ : Measure (Euc K)) (A S C O : Set (Euc K)) (χ : Euc K → ℝ) (g gh : ℕ → Euc K → ℝ)
    (Q : Euc K → Euc K) (T : ℕ → Euc K → Euc K) (e : 𝒯 → Euc K) (EK : ℝ) (xbar slack : ℕ → 𝒯 → ℝ),
    IsOpen C → Convex ℝ C → ConvexOn ℝ C χ → (∀ n, ConvexOn ℝ C (g n)) → (∀ n, ConvexOn ℝ C (gh n)) →
    (∀ S' ⊆ C, IsCompact S' → TendstoUniformlyOn g χ atTop S') →
    (∀ S' ⊆ C, IsCompact S' → TendstoUniformlyOn gh χ atTop S') →
    IsOpen O → S ⊆ O → O ⊆ C → (∀ u ∈ O, DifferentiableAt ℝ χ u) → (∀ᵐ u ∂μ, u ∈ O → Q u = gradient χ u) →
    IsCompact S → IsCompact A → Convex ℝ A → (interior A).Nonempty → A ⊆ μ.support → A ⊆ S →
    (∀ n, ∀ u ∈ S, T n u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop C (gh n)) u) → (∀ t, ‖e t‖ ≤ EK) →
    (∀ n t, supE A (T n) (e t) ≤ (xbar n t : EReal) ∧ (xbar n t : EReal) ≤ supSub C A (g n) (e t) + (slack n t : EReal)) →
    (∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t, slack n t ≤ η) →
      ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t, ∃ r : ℝ, hPop μ A Q (e t) = r ∧ |xbar n t - r| ≤ η

/-! #### T `lem:exp` -/

/-- `eq:expbounds`: for fields bounded by `b`, pointwise `d_M ≤ L_b ‖v − w‖`, `D_2² = ∫ d_M² ≤ L_b² ‖v − w‖²_{H_0}` and
`D_∞ = sup_t d_M ≤ L_b sup_t ‖v(t) − w(t)‖`, from the length bound of the exponential image of a segment (the ball is
convex); the fields' difference is measurable (`v, w ∈ H_0`). -/
def exp_bounds : Prop :=
  ∀ (T V W M : Type) [MeasurableSpace T] [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
    [NormedSpace ℝ W] [PseudoEMetricSpace M] (lam : Measure T) (Ex : T → V → M) (D : T → V → V →L[ℝ] W) (b : ℝ)
    (v w : T → V),
    LengthBound Ex D → (∀ t, ‖v t‖ ≤ b) → (∀ t, ‖w t‖ ≤ b) → AEMeasurable (fun t => ‖v t - w t‖ₑ) lam →
      (∀ t, edist (Ex t (v t)) (Ex t (w t)) ≤ Lb D b * ‖v t - w t‖ₑ) ∧
      (∫⁻ t, edist (Ex t (v t)) (Ex t (w t)) ^ 2 ∂lam ≤ Lb D b ^ 2 * ∫⁻ t, ‖v t - w t‖ₑ ^ 2 ∂lam) ∧
      (⨆ t, edist (Ex t (v t)) (Ex t (w t))) ≤ Lb D b * ⨆ t, ‖v t - w t‖ₑ

/-- "If `eq:Hembed` holds, the last bound is at most `L_b Λ ‖v − w‖_H`": fields `v = ι h`, `w = ι h'` of a linear
`ι : H → (T → V)` with `sup_t ‖(ι x)(t)‖ ≤ Λ ‖x‖_H`. -/
def exp_bounds_embed : Prop :=
  ∀ (T V W M H : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [PseudoEMetricSpace M] [NormedAddCommGroup H] [NormedSpace ℝ H] (Ex : T → V → M) (D : T → V → V →L[ℝ] W)
    (ι : H →ₗ[ℝ] (T → V)) (b Λ : ℝ) (h h' : H),
    LengthBound Ex D → (∀ x t, ‖ι x t‖ ≤ Λ * ‖x‖) → (∀ t, ‖ι h t‖ ≤ b) → (∀ t, ‖ι h' t‖ ≤ b) →
      (⨆ t, edist (Ex t (ι h t)) (Ex t (ι h' t))) ≤ Lb D b * ENNReal.ofReal (Λ * ‖h - h'‖)

/-- `L_b < ∞` (`eq:L`) when `T` is compact, the tangent space finite-dimensional and the differential continuous. -/
def exp_Lb_finite : Prop :=
  ∀ (T V W : Type) [TopologicalSpace T] [CompactSpace T] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] (D : T → V → V →L[ℝ] W) (b : ℝ),
    Continuous (fun p : T × V => D p.1 p.2) → Lb D b < ⊤

/-! #### T `lem:cK` -/

/-- `eq:cK`: `c_K(ρ) = E min(ρ/W_K, 1) = ∫_0^ρ f_K` for `ρ ≥ 0`. -/
def cK_formula : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W R : Ω → ℝ), RadialLaw P W R →
    ∀ ρ : ℝ, 0 ≤ ρ → cK P W R ρ = ∫ ω, min (ρ / W ω) 1 ∂P ∧ cK P W R ρ = ∫ x in (0 : ℝ)..ρ, fK P W x

/-- (i): `c_K` is continuous, nondecreasing and concave on `[0, ∞)` with `c_K(0) = 0`, `f_K` is nonincreasing on
`(0, ∞)`, and `ρ_K(p) = c_K⁻¹(p)` is well defined for `p ∈ (0,1)`. -/
def cK_shape : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W R : Ω → ℝ), RadialLaw P W R →
    cK P W R 0 = 0 ∧ ContinuousOn (cK P W R) (Ici 0) ∧ MonotoneOn (cK P W R) (Ici 0) ∧
    ConcaveOn ℝ (Ici 0) (cK P W R) ∧ AntitoneOn (fK P W) (Ioi 0) ∧
    ∀ p ∈ Ioo (0 : ℝ) 1, ∃! ρ : ℝ, 0 ≤ ρ ∧ cK P W R ρ = p

/-- (i): with `w* = ess sup W_K` (characterised by `W ≤ w*` a.s. and `P(W > w) > 0` for `w < w*`), `c_K` is strictly
increasing on `[0, w*]` and equal to `1` beyond. -/
def cK_strict : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W R : Ω → ℝ) (ws : ℝ), RadialLaw P W R →
    (∀ᵐ ω ∂P, W ω ≤ ws) → (∀ w < ws, 0 < P {ω | w < W ω}) →
      StrictMonoOn (cK P W R) (Icc 0 ws) ∧ ∀ ρ, ws ≤ ρ → cK P W R ρ = 1

/-- (ii): `W_K < 1` a.s. (truncation) gives `c_K(ρ) > ρ` on `(0,1)`, so `c_K` is not convex on `[0,1]`; `W_K ≡ 1` gives
`c_K(ρ) = ρ` on `[0,1]`; `c_K` is convex on `[0,1]` iff `W_K = 1` a.s. -/
def cK_convexity : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W R : Ω → ℝ), RadialLaw P W R →
    ((∀ᵐ ω ∂P, W ω < 1) → (∀ ρ ∈ Ioo (0 : ℝ) 1, ρ < cK P W R ρ) ∧ ¬ ConvexOn ℝ (Icc 0 1) (cK P W R)) ∧
    ((∀ᵐ ω ∂P, W ω = 1) → ∀ ρ ∈ Icc (0 : ℝ) 1, cK P W R ρ = ρ) ∧
    (ConvexOn ℝ (Icc 0 1) (cK P W R) ↔ ∀ᵐ ω ∂P, W ω = 1)

/-- The finite-dimensional projected ball law (`D = Jd` in Algorithm 1): for `G` on `ℝ^D` with a Lebesgue density (a
nondegenerate Gaussian, `C` injective) and `1 ≤ K ≤ D`: `G ≠ 0` and `0 < W_K ≤ 1` a.s.; `W_K < 1` a.s. if `K < D`;
`W_K = 1` if `K = D`; `‖Π_K U‖ = R W_K` for `U = R G/‖G‖`; and `W_K` is independent of `R` when `G` is. -/
def cK_proj : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (D K : ℕ) (G : Ω → Euc D) (R : Ω → ℝ),
    1 ≤ K → K ≤ D → Measurable G → P.map G ≪ volume →
      (∀ᵐ ω ∂P, G ω ≠ 0 ∧ 0 < Wproj K G ω ∧ Wproj K G ω ≤ 1) ∧
      (K < D → ∀ᵐ ω ∂P, Wproj K G ω < 1) ∧ (K = D → ∀ ω, G ω ≠ 0 → Wproj K G ω = 1) ∧
      (∀ ω, 0 ≤ R ω → normProj K (R ω • ‖G ω‖⁻¹ • G ω) = R ω * Wproj K G ω) ∧
      (IndepFun G R P → IndepFun (Wproj K G) R P)

/-! #### T `lem:verified-content` -/

/-- (i), (ii) on the one-sided DKW event `sup_r (ĉ(r) − c(r)) ≤ κ` of the `2N` radii, deterministically, for every
`p ∈ (0,1]` (`c` any function with `c(1) = 1`, e.g. `c_K`). -/
def vc_content : Prop :=
  ∀ (ι : Type) [Fintype ι] (N : ℕ) (x : ι → ℝ) (c : ℝ → ℝ) (κ : ℝ),
    1 ≤ N → Fintype.card ι = 2 * N → 0 ≤ κ → c 1 = 1 →
    (∀ r, (empCount x r : ℝ) / (2 * N) - c r ≤ κ) → VCGood N x c κ

/-- The probability statement for the antithetic radii `ϱ_j = R_j W_j`, `ϱ'_j = R'_j W_j` (indexed by `Fin 2 × Fin N`),
CONDITIONAL on the one-sided DKW–Massart bound for each half (`P*{sup_r(ĉ_h − c) > κ_N(δ)} ≤ δ/2`; the halves are iid,
the pairs are not): with probability at least `1 − δ`, (i), (ii) hold simultaneously for every `p`. -/
def vc_prob : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (N : ℕ) (Rr Rr' Wr : Fin N → Ω → ℝ)
    (c : ℝ → ℝ) (δ : ℝ),
    1 ≤ N → 0 < δ → δ < 1 → c 1 = 1 →
    P {ω | ∃ r, kappaN N δ < (empCount (fun j => Rr j ω * Wr j ω) r : ℝ) / N - c r} ≤ ENNReal.ofReal (δ / 2) →
    P {ω | ∃ r, kappaN N δ < (empCount (fun j => Rr' j ω * Wr j ω) r : ℝ) / N - c r} ≤ ENNReal.ofReal (δ / 2) →
      ∃ E : Set Ω, MeasurableSet E ∧ 1 - ENNReal.ofReal δ ≤ P E ∧ ∀ ω ∈ E,
        VCGood N (fun ij : Fin 2 × Fin N => if ij.1 = 0 then Rr ij.2 ω * Wr ij.2 ω else Rr' ij.2 ω * Wr ij.2 ω)
          c (kappaN N δ)

/-- The numerical certificate: `N = 10⁵`, `δ = 10⁻⁶`: `κ_N(δ) + 1/(4N) ≤ 0.00852` (`\ContentKappa`). -/
def vc_numeric : Prop :=
  kappaN (10 ^ 5) (1 / 10 ^ 6) + 1 / (4 * 10 ^ 5) ≤ 0.00852

/-! #### C `thm:self-localization` -/

/-- `eq:self-effective-bounds`, entropic: with `−d²/2 ≤ F_i ≤ d²` (`lem:self-potentials`) and covariates, query in a set
of diameter `≤ d`, `max_i w^E_i(x) ≤ e^{3d²/ε}/n`, hence `Σ_i w_i² ≤ e^{3d²/ε}/n` (`n_eff ≥ n e^{−3d²/ε}`). -/
def selfloc_weight_ent : Prop :=
  ∀ (q n : ℕ) (Dc : Set (Euc q)) (d ε : ℝ) (Cc : Fin n → Euc q) (F : Fin n → ℝ) (x : Euc q),
    0 < n → 0 < ε → (∀ a ∈ Dc, ∀ b ∈ Dc, dist a b ≤ d) → x ∈ Dc → (∀ i, Cc i ∈ Dc) →
    (∀ i, -d ^ 2 / 2 ≤ F i ∧ F i ≤ d ^ 2) →
      (∀ i, StatFormal.OTFD.Bands.softmax (fun i => (F i - ‖x - Cc i‖ ^ 2) / ε) i ≤ Real.exp (3 * d ^ 2 / ε) / n) ∧
      ∑ i, StatFormal.OTFD.Bands.softmax (fun i => (F i - ‖x - Cc i‖ ^ 2) / ε) i ^ 2 ≤ Real.exp (3 * d ^ 2 / ε) / n

/-- `eq:self-effective-bounds`, quadratic: `w^Q(x) = P_Δ((H_i − ‖x − C_i‖²)/(nη))`, with the potentials and the
out-of-sample threshold `H(x)` (`Σ_i [H(x) + H_i − ‖x − C_i‖²]_+ = nη`) in `[η/2 − d², η/2 + 3d²/2]`, satisfies
`w_i = [H(x) + H_i − ‖x − C_i‖²]_+/(nη) ≤ (η + 3d²)/(nη)`, hence `Σ_i w_i² ≤ (η + 3d²)/(nη)`. -/
def selfloc_weight_quad : Prop :=
  ∀ (q n : ℕ) (Dc : Set (Euc q)) (d η : ℝ) (Cc : Fin n → Euc q) (H : Fin n → ℝ) (Hx : ℝ) (x : Euc q)
    (w : Fin n → ℝ),
    0 < n → 0 < η → (∀ a ∈ Dc, ∀ b ∈ Dc, dist a b ≤ d) → x ∈ Dc → (∀ i, Cc i ∈ Dc) →
    (∀ i, η / 2 - d ^ 2 ≤ H i ∧ H i ≤ η / 2 + 3 * d ^ 2 / 2) → η / 2 - d ^ 2 ≤ Hx → Hx ≤ η / 2 + 3 * d ^ 2 / 2 →
    ∑ i, max 0 (Hx + H i - ‖x - Cc i‖ ^ 2) = n * η →
    StatFormal.OTFD.Bands.IsSimplexProj (fun i => (H i - ‖x - Cc i‖ ^ 2) / (n * η)) w →
      (∀ i, w i = max 0 (Hx + H i - ‖x - Cc i‖ ^ 2) / (n * η) ∧ w i ≤ (η + 3 * d ^ 2) / (n * η)) ∧
      ∑ i, w i ^ 2 ≤ (η + 3 * d ^ 2) / (n * η)

/-- The staircase (diagonal schedule) lemma: if at each fixed strength index `j` the errors `E_{j,n} → 0` a.s., the biases
`β_j → 0`, and deterministic `c_{j,n} → 0` as `n → ∞` for each `j`, there is a deterministic nondecreasing schedule
`s(n) → ∞` with `β_{s(n)} + c_{s(n),n} → 0` and, almost surely, `E_{s(n),n} → 0`. -/
def selfloc_staircase : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (E : ℕ → ℕ → Ω → ℝ≥0∞)
    (β : ℕ → ℝ≥0∞) (c : ℕ → ℕ → ℝ≥0∞),
    (∀ j n, Measurable (E j n)) → (∀ j, ∀ᵐ ω ∂P, Tendsto (fun n => E j n ω) atTop (𝓝 0)) →
    Tendsto β atTop (𝓝 0) → (∀ j, Tendsto (c j) atTop (𝓝 0)) →
      ∃ s : ℕ → ℕ, Monotone s ∧ Tendsto s atTop atTop ∧ Tendsto (fun n => β (s n) + c (s n) n) atTop (𝓝 0) ∧
        ∀ᵐ ω ∂P, Tendsto (fun n => E (s n) n ω) atTop (𝓝 0)

/-- "Consequently …": in any pseudo-metric space of laws (`W₁`), CONDITIONAL on the fixed-strength uniform a.s.
convergence of the weighted laws to the smoothed laws and the uniform convergence of the smoothed laws as the strength
`σ_j ↓ 0` (both declared), there is a deterministic schedule `ε_{X,n} = σ_{s(n)} ↓ 0` with
`sup_{x ∈ D} W₁(P̂_{n,x}, P_{K,x}) → 0` a.s. and, given the weight bound `max_i w_i ≤ e^{3d²/σ}/n`, uniformly in the
sample and `x`, `log n · max_i w_i → 0` (so `inf_x n_eff(x)/log n → ∞`). -/
def selfloc_consistency : Prop :=
  ∀ (Ω X 𝓛 : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] [PseudoEMetricSpace 𝓛] (Dc : Set X)
    (σ : ℕ → ℝ) (Phat : ℕ → ℕ → Ω → X → 𝓛) (Pbar : ℕ → X → 𝓛) (Pt : X → 𝓛) (wmax : ℕ → ℕ → Ω → X → ℝ) (d : ℝ),
    (∀ j, 0 < σ j) → Antitone σ → Tendsto σ atTop (𝓝 0) →
    (∀ j n, Measurable (fun ω => ⨆ x ∈ Dc, edist (Phat j n ω x) (Pbar j x))) →
    (∀ j, ∀ᵐ ω ∂P, Tendsto (fun n => ⨆ x ∈ Dc, edist (Phat j n ω x) (Pbar j x)) atTop (𝓝 0)) →
    Tendsto (fun j => ⨆ x ∈ Dc, edist (Pbar j x) (Pt x)) atTop (𝓝 0) →
    (∀ j n ω, ∀ x ∈ Dc, wmax j n ω x ≤ Real.exp (3 * d ^ 2 / σ j) / n) →
      ∃ s : ℕ → ℕ, Monotone s ∧ Antitone (fun n => σ (s n)) ∧ Tendsto (fun n => σ (s n)) atTop (𝓝 0) ∧
        (∀ᵐ ω ∂P, Tendsto (fun n => ⨆ x ∈ Dc, edist (Phat (s n) n ω x) (Pt x)) atTop (𝓝 0)) ∧
        ∀ θ : ℝ, 0 < θ → ∀ᶠ n : ℕ in atTop, ∀ ω, ∀ x ∈ Dc, Real.log (n : ℝ) * wmax (s n) n ω x ≤ θ

/-! #### C `lem:full-support-region` (ii), (iii) for the cubic law -/

/-- (iii) cubic: `μ_K` is a probability law with Lebesgue density `(∏_k λ_k)⁻¹` on the open box (and `0` off it). -/
def cubic_density : Prop :=
  ∀ (K : ℕ) (lam : Fin K → ℝ), (∀ k, 0 < lam k) →
    IsProbabilityMeasure (cubicLaw lam) ∧
    cubicLaw lam = volume.withDensity ((openBox lam).indicator fun _ => (∏ k, ENNReal.ofReal (lam k))⁻¹)

/-- (ii) cubic, with (i) applied: `supp μ_K = U_K` (the closed box), and for every radius `r > 0` the level region
`A = U_K ∩ B̄(0, r)` (`r = τ_{K,p} D_∞`) is compact, convex, contains `0` in its interior, lies in `supp μ_K`, and every
continuous `g` on `A` has `μ_K`-ess sup over `A` equal to `sup_A g`. -/
def cubic_region : Prop :=
  ∀ (K : ℕ) (lam : Fin K → ℝ) (r : ℝ), (∀ k, 0 < lam k) → 0 < r →
    (cubicLaw lam).support = closedBox lam ∧
    IsCompact (closedBox lam ∩ Metric.closedBall 0 r) ∧ Convex ℝ (closedBox lam ∩ Metric.closedBall 0 r) ∧
    (0 : Euc K) ∈ interior (closedBox lam ∩ Metric.closedBall 0 r) ∧
    closedBox lam ∩ Metric.closedBall 0 r ⊆ (cubicLaw lam).support ∧
    ∀ g : Euc K → ℝ, ContinuousOn g (closedBox lam ∩ Metric.closedBall 0 r) →
      essSup (fun u => ((g u : ℝ) : EReal)) ((cubicLaw lam).restrict (closedBox lam ∩ Metric.closedBall 0 r)) =
        ⨆ u ∈ closedBox lam ∩ Metric.closedBall 0 r, ((g u : ℝ) : EReal)

/-! #### C `lem:conditional-weights-unbounded` -/

/-- The truncation inequality `eq:unbounded-truncation`: for probability laws on `ℝ^K` and `L ≥ 0`,
`W₁(P, Q) ≤ W₁(π_L#P, π_L#Q) + ∫ ‖z‖1{‖z‖ > L} dP + ∫ ‖z‖1{‖z‖ > L} dQ` (in `ℝ≥0∞`). -/
def cwu_truncation : Prop :=
  ∀ (K : ℕ) (P Q : Measure (Euc K)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (L : ℝ), 0 ≤ L →
    TauCeti.wassersteinEDist 1 P Q ≤ TauCeti.wassersteinEDist 1 (P.map (radProj L)) (Q.map (radProj L)) +
      ∫⁻ z, ENNReal.ofReal (tailNorm L z) ∂P + ∫⁻ z, ENNReal.ofReal (tailNorm L z) ∂Q

/-- `lem:conditional-weights-unbounded`, in probability, in the triangular-array model of the frozen Wave 12b
`cw_prob` (covariates in `ℝ^q`, conditional law a Markov kernel `κ`): (i) locality and averaging in probability,
(ii) `c ↦ κ c` weakly continuous at `x ∈ D = supp P_C` relative to `D`, (iii) `∫ ‖z‖ dκ_x < ∞`, (iv) for every `a, θ > 0`
some `L` with `P{Σ_i w_i ‖Z_i‖1{‖Z_i‖ > L} > a} ≤ θ` eventually (implied by the printed `lim_L limsup_n … = 0`). Then
`W₁(P̂_{K,n,x}, P_{K,x}) → 0` in probability (outer probability of the bad event). -/
def cwu_prob : Prop :=
  ∀ (q K : ℕ) (PC : Measure (Euc q)) [IsProbabilityMeasure PC] (κ : Kernel (Euc q) (Euc K)) [IsMarkovKernel κ]
    (W : ∀ n : ℕ, (Fin n → Euc q) → Fin n → ℝ) (x : Euc q),
    x ∈ PC.support →
    (∀ n, 0 < n → Measurable (W n) ∧ ∀ c, (∀ i, 0 ≤ W n c i) ∧ ∑ i, W n c i = 1) →
    (∀ a, 0 < a → ∀ η, 0 < η → Tendsto (fun n => Measure.pi (fun _ : Fin n => PC ⊗ₘ κ)
        {s | η ≤ locMass (W n (fun i => (s i).1)) (fun i => (s i).1) x a}) atTop (𝓝 0)) →
    (∀ η, 0 < η → Tendsto (fun n => Measure.pi (fun _ : Fin n => PC ⊗ₘ κ)
        {s | η ≤ vn (W n (fun i => (s i).1))}) atTop (𝓝 0)) →
    (∀ f : Euc K →ᵇ ℝ, Tendsto (fun c => ∫ z, f z ∂(κ c)) (𝓝[PC.support] x) (𝓝 (∫ z, f z ∂(κ x)))) →
    Integrable (fun z => ‖z‖) (κ x) →
    (∀ a, 0 < a → ∀ θ, 0 < θ → ∃ L, 0 ≤ L ∧ ∀ᶠ n in atTop, Measure.pi (fun _ : Fin n => PC ⊗ₘ κ)
        {s | a < ∑ i, W n (fun i => (s i).1) i * tailNorm L (s i).2} ≤ ENNReal.ofReal θ) →
    ∀ η, 0 < η → Tendsto (fun n => Measure.pi (fun _ : Fin n => PC ⊗ₘ κ)
        {s | ENNReal.ofReal η ≤
          TauCeti.wassersteinEDist 1 (wEmp (W n (fun i => (s i).1)) (fun i => (s i).2)) (κ x)}) atTop (𝓝 0)

/-! #### T `prop:cf-M` (i), (ii) in fixed charts; (iv) Step 0 -/

/-- (i): with population rank pairs `(F_a, Q_a)` from the common reference `μ_K` to `ν_{a,K}` and query charts,
`T_{x→x'}#P^K_x = P^K_{x'}`, `F_{x'}∘Φ_{x'}⁻¹∘T_{x→x'} = F_x∘Φ_x⁻¹` `P^K_x`-a.e., and `T_{x→x'}` is the `P^K_x`-a.e.
unique measurable map with both properties (curve space `Y` with a measurable diagonal, e.g. standard Borel). -/
def cfM_i : Prop :=
  ∀ (K : ℕ) (Y : Type) [MeasurableSpace Y] [MeasurableEq Y] (B : ℝ) (μ ν ν' : Measure (Euc K)) (F Q F' Q' : Euc K → Euc K)
    (Φ Φ' : Euc K → Y) (Φinv Φinv' : Y → Euc K),
    IsRankPair μ ν F Q → IsRankPair μ ν' F' Q' → QueryChart B Φ Φinv ν → QueryChart B Φ' Φinv' ν' →
      (ν.map Φ).map (cfT Φ' Q' F Φinv) = ν'.map Φ' ∧
      (∀ᵐ y ∂(ν.map Φ), F' (Φinv' (cfT Φ' Q' F Φinv y)) = F (Φinv y)) ∧
      ∀ S : Y → Y, Measurable S → (ν.map Φ).map S = ν'.map Φ' →
        (∀ᵐ y ∂(ν.map Φ), F' (Φinv' (S y)) = F (Φinv y)) → S =ᵐ[ν.map Φ] cfT Φ' Q' F Φinv

/-- (ii): `T_{x→x} = Id` and `T_{x'→x''}∘T_{x→x'} = T_{x→x''}`, `P^K_x`-a.e. -/
def cfM_ii : Prop :=
  ∀ (K : ℕ) (Y : Type) [MeasurableSpace Y] [MeasurableEq Y] (B : ℝ) (μ ν ν' ν'' : Measure (Euc K)) (F Q F' Q' F'' Q'' : Euc K → Euc K)
    (Φ Φ' Φ'' : Euc K → Y) (Φinv Φinv' Φinv'' : Y → Euc K),
    IsRankPair μ ν F Q → IsRankPair μ ν' F' Q' → IsRankPair μ ν'' F'' Q'' →
    QueryChart B Φ Φinv ν → QueryChart B Φ' Φinv' ν' → QueryChart B Φ'' Φinv'' ν'' →
      cfT Φ Q F Φinv =ᵐ[ν.map Φ] id ∧
      (fun y => cfT Φ'' Q'' F' Φinv' (cfT Φ' Q' F Φinv y)) =ᵐ[ν.map Φ] cfT Φ'' Q'' F Φinv

/-- (iv) Step 0: if `ξ ↦ ν_ξ` is weakly continuous at `a ∈ D = supp P_W` relative to `D`, and `ν_ξ(B̄_B) = 1` for
`P_W`-a.e. `ξ` (hypothesis (H1)), then `ν_a(B̄_B) = 1` (portmanteau). -/
def cfM_step0 : Prop :=
  ∀ (q K : ℕ) (PW : Measure (Euc q)) (ν : Euc q → ProbabilityMeasure (Euc K)) (a : Euc q) (B : ℝ),
    a ∈ PW.support → ContinuousWithinAt ν PW.support a →
    (∀ᵐ ξ ∂PW, (ν ξ : Measure (Euc K)) (Metric.closedBall 0 B) = 1) →
      (ν a : Measure (Euc K)) (Metric.closedBall 0 B) = 1

/-- (iv) Consistency on `M` (Steps 2–4), CONDITIONAL on the conclusions of C's Lemma 8.3 at `x` (a.s. rank-map
convergence on a set carrying `Z`) and Theorem 5.6 at `x'` (a.s. local uniform convergence of the convex fitted
potentials on `int U_K`), the premises of `cond_transfer_consistency`: with the chart `Φ_{x'}(z) = (t ↦ Exp_t(v̄(t) +
ι_K z(t)))`, `ι_K` linear with `sup_t ‖ι_K z(t)‖ ≤ Λ‖z‖` (`eq:Hembed`), fields bounded by `b` on `B̄_B` (`eq:tk-domain`:
`‖v̄(t)‖ + ΛB ≤ b`), fitted maps valued in `B̄_B` ((H1): convex combinations of the responses), `Q'` valued in `B̄_B`
`μ_K`-a.e. (Step 0), `L_b < ∞` and the length bound of `lem:exp`: almost surely, for every `n`,
`D_∞(T̂_{x→x'}Y, T_{x→x'}Y) ≤ L_b Λ ‖Q̂_{x'}F̂_xZ − Q_{x'}F_xZ‖`, and `D_∞(T̂Y, TY) → 0`. -/
def cfM_iv : Prop :=
  ∀ (K : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (μ : Measure (Euc K)) (U DF : Set (Euc K))
    (Z : Ω → Euc K) (F : Euc K → Euc K) (Fh : ℕ → Ω → Euc K → Euc K) (χ' : Euc K → ℝ)
    (g : ℕ → Ω → Euc K → ℝ) (Q' : Euc K → Euc K) (Qh : ℕ → Ω → Euc K → Euc K)
    (T V W M : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [PseudoEMetricSpace M] (Ex : T → V → M) (D : T → V → V →L[ℝ] W) (vbar : T → V) (ι : Euc K →ₗ[ℝ] (T → V))
    (b B Λ : ℝ),
    μ ≪ volume → Convex ℝ U → μ Uᶜ = 0 → Measurable Z → Measurable F → P.map (fun ω => F (Z ω)) = μ →
    (∀ᵐ ω ∂P, Z ω ∈ DF) → (∀ᵐ ω ∂P, ∀ z ∈ DF, Tendsto (fun n => Fh n ω z) atTop (𝓝 (F z))) →
    ConvexOn ℝ (interior U) χ' → Q' =ᵐ[μ] gradient χ' →
    (∀ᵐ ω ∂P, (∀ n, ConvexOn ℝ (interior U) (g n ω)) ∧
      ∀ S ⊆ interior U, IsCompact S → TendstoUniformlyOn (fun n => g n ω) χ' atTop S) →
    (∀ n ω, ∀ u ∈ interior U, Qh n ω u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n ω)) u) →
    LengthBound Ex D → Lb D b ≠ ⊤ → 0 ≤ Λ → (∀ z t, ‖ι z t‖ ≤ Λ * ‖z‖) → (∀ t, ‖vbar t‖ + Λ * B ≤ b) →
    (∀ n ω u, ‖Qh n ω u‖ ≤ B) → (∀ᵐ u ∂μ, ‖Q' u‖ ≤ B) →
      ∀ᵐ ω ∂P,
        (∀ n, (⨆ t, edist (Ex t (vbar t + ι (Qh n ω (Fh n ω (Z ω))) t)) (Ex t (vbar t + ι (Q' (F (Z ω))) t))) ≤
          Lb D b * ENNReal.ofReal (Λ * ‖Qh n ω (Fh n ω (Z ω)) - Q' (F (Z ω))‖)) ∧
        Tendsto (fun n => ⨆ t, edist (Ex t (vbar t + ι (Qh n ω (Fh n ω (Z ω))) t))
          (Ex t (vbar t + ι (Q' (F (Z ω))) t))) atTop (𝓝 0)

/-- C `cor:conditional-test-coverage` (inflated band) with its edge premise discharged from potential convergence:
under the hypotheses of `cond_band_one_sided_potentials`, for any band `[L_n, U_n]` containing the fitted band of the
selections `Q_n` (`U_n ≥ 𝔪 + ĥ_n(𝐞)`, `L_n ≤ 𝔪 − ĥ_n(−𝐞)`: the fitted band itself or a certified outer band), every
fixed inflation `κ > 0` has test coverage `≥ p` for all large `n`. -/
def cond_test_coverage_potentials : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ : Measure (Euc K)) [IsProbabilityMeasure μ] (U A : Set (Euc K)) (χ : Euc K → ℝ)
    (g : ℕ → Euc K → ℝ) (Q : Euc K → Euc K) (Qn : ℕ → Euc K → Euc K) (m : 𝒯 → ℝ) (e : 𝒯 → Euc K)
    (Ue Le : ℕ → 𝒯 → EReal) (R EK p κ : ℝ),
    μ ≪ volume → Convex ℝ U → μ Uᶜ = 0 → ConvexOn ℝ (interior U) χ → (∀ n, ConvexOn ℝ (interior U) (g n)) →
    (∀ S ⊆ interior U, IsCompact S → TendstoUniformlyOn g χ atTop S) → Q =ᵐ[μ] gradient χ →
    (∀ n, ∀ u ∈ interior U, Qn n u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n)) u) →
    Measurable Q → MeasurableSet A → (∀ᵐ u ∂μ.restrict A, ‖Q u‖ ≤ R) → (∀ t, ‖e t‖ ≤ EK) →
    ENNReal.ofReal p ≤ μ A → 0 < κ →
    (∀ n t, (m t : EReal) + supE A (Qn n) (e t) ≤ Ue n t ∧ Le n t ≤ (m t : EReal) - supE A (Qn n) (-e t)) →
      ∀ᶠ n in atTop, ∃ E : Set (Euc K), MeasurableSet E ∧
        E ⊆ {z | ∀ t, Le n t - κ ≤ ((m t + ⟪e t, z⟫ : ℝ) : EReal) ∧ ((m t + ⟪e t, z⟫ : ℝ) : EReal) ≤ Ue n t + κ} ∧
        ENNReal.ofReal p ≤ μ.map Q E

end Claims
end StatFormal.OTFD.Wave22b
