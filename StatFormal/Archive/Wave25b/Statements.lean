import StatFormal.Archive.OTFD.WaveL6.Statements
import StatFormal.Archive.OTFD.WaveL2.Statements
import StatFormal.Archive.OTFD.Ranks.Statements
import StatFormal.Archive.Wave21a.Statements
import StatFormal.Archive.Wave24c.Statements
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Probability.Independence.Basic
import TauCeti.Analysis.Convex.Subdifferential

/-!
# FROZEN STATEMENTS — wave 25b (QUEUE rows 394–410): A `thm:app-hard-diagonal`, `thm:app-entropic-diagonal`,
# `thm:app-ghs-existence`, `thm:app-ghs-stability` (i), (ii), `lem:rt-pooled-graph`; T `thm:empirical` and the
# DISCHARGE of Wave 24c `smooth_consistency`

Sources (verbatim in `lean-formalisation/inventory/extracted/otfd-{A_sieves,T_tangent}.md`; current text of
`otfd/papers/{A_sieves,T_tangent}/`):
* `thm:app-hard-diagonal` (`main.tex:900-918`), with `def:ghs-rank` (`main.tex:721-736`), the hard estimator of
  `subsec:hard-ot` and the proof `subsec:app-hard-diagonal` (`supplement.tex:3952-`, with `lem:app-graph-empirical`).
* `thm:app-entropic-diagonal` (`main.tex:932-953`), with the estimator display (`main.tex:866-873`) and the proof outline
  (`main.tex:955-965`, `subsec:app-entropic-softness`, `supplement.tex:3413-`).
* `thm:app-ghs-existence` (`supplement.tex:1061-1065`, GHS Thm 2.3), with `cor:app-ghs-lipschitz` (`:1067-1078`).
* `thm:app-ghs-stability` (`supplement.tex:1080-1112`, GHS Thm 3.1(i) and the corrected (iii)).
* `lem:rt-pooled-graph` (`supplement.tex:4298-4302`, proof `:4304-4325`) under the hypotheses of `thm:rt-fixedK`
  (`main.tex:1462-`, frozen as `FixedKSetting` in `OTFD/WaveL2`).
* T `thm:empirical` (`T_tangent/sec_tangent_theory.tex:301-314`, with `ass:model` `:89-95`, `eq:quantize`,
  `eq:entropicobjective`, `eq:binned` `:280-299`; proof `app_proofs.tex:115-146`); T `cor:smooth` (`eq:smooth`,
  `supp_moved.tex:872-885`, proof `app_proofs.tex:148-157`; frozen Wave 24c `smooth_consistency`, conditional on
  `thm:empirical`).
Imports the frozen `OTFD/WaveL6` (through it `OTFD/WaveL3` `Mom1`, `OTFD/WaveL1` `CycMon`, `CMConc`, `IsCMMapAE`,
`LipNull`, `Euc`, `OTFD/Wave1` `PellClass`, `truncK`, `OTFD/Wave8b` `embed`, `OTFD/Wave22a` `IsSubgrad`), `OTFD/WaveL2`
(`FixedKSetting`, `pool`), `OTFD/Ranks` (`IsMin`), `Wave21a` (`Jemp`, `baryT`) and `Wave24c` (`smoothMap`) statements, not copied; Tau Ceti
(`subdifferential`) and Mathlib otherwise.

Covered:
* `thm:app-hard-diagonal`: `app_hard_diagonal` (a staircase `K_n ↑ ∞` with
  `E[n⁻¹ Σ_i ‖ι_{K_n} û_i − 𝔽_P(X_i)‖²] → 0`, `û_i` the bijective hard assignment with a measurable tie-breaking rule).
* `thm:app-entropic-diagonal`: `app_entropic_diagonal` (staircases `K_n ↑ ∞`, `m_n ↑ ∞`, `ε_n ↓ 0` for the embedded
  entropic barycentric ranks).
* `thm:app-ghs-existence`: `app_ghs_existence` (any target `Q`, no moment of `Q`).
* `thm:app-ghs-stability`: `app_ghs_stability_weak` ((i)), `app_ghs_stability_norm` ((ii) under (⋆)),
  `app_ghs_stability_fd` ((ii), last sentence: finite dimension, no (⋆)).
* `lem:rt-pooled-graph`: `rt_pooled_graph` (`Δ_N → 0` almost surely for every sequence of optimal assignments; for a
  measurable selection: measurable, in probability, in expectation).
* T `thm:empirical`: `empirical_quantile` (`eq:empQ` almost surely, for ANY entropic minimiser).
* DISCHARGE: `smooth_consistency_discharged` — the frozen Wave 24c `smooth_consistency` with its `thm:empirical`
  premise replaced by the setting of `thm:empirical` and an exact Gibbs-form solver (the plan of the frozen
  `smooth_exact`): almost surely, `ε_n⁻² h_n² → 0` gives `eq:empQ` for `Q^sm_n(P_{K_n} u)`.

Not covered (declared):
* A `prop:integrated-quantile`, `lem:plan-stability-H`, `thm:moment-sieve`, R `lem:plan-w2`: ALREADY CERTIFIED (waves L1
  and L3, `_uncond` forms). T `thm:pop-sieve`: its display `eq:popQ` and the forward analogue are the certified L3
  `integrated_quantile_uncond`, `sieve_strong_limit_uncond` (any separable `H`, `ν = P` boundedly supported in `𝒫^ℓ`,
  optimal maps are a.e. cyclically monotone), so no new claim; the existence parenthetical is the certified
  `lem:app-pullback` with Brenier existence; the exponential-reconstruction sentences need the manifold layer.
* `thm:app-ghs-stability` (iii) as printed: false in infinite dimension (`prop:ghs-iii-counterexample`, certified
  earlier); the corrected (⋆) form is `app_ghs_stability_norm`.
* `cor:estimated-basis-sample`: needs `prop:estimated-basis` (ii), (iv) (FPCA perturbation of the held-out basis,
  uncertified) and the reference's dependence on the estimated basis; skipped.
* `thm:app-ghosalsen-rate`: given `app_ghs_stability_fd` and Varadarajan it reduces to two missing inputs — the
  semi-discrete (unregularised, continuum reference) empirical OT potentials themselves, and Rockafellar 25.6
  (differentiability of the population potential on `int Y_K` from the homeomorphism hypothesis); skipped.
* T `thm:empirical`: the continuum-reference sentence (exact continuum-reference entropic solution), the approximate
  solver sentence, and the reconstruction (`lem:exp`, `D_∞`) sentences; "no dimension-free rate" (nothing to prove).
* B `prop:band-two-stage`, `prop:vector-transfer`; G `prop:ratesgeneral`; T `supp:1018` (`prop:Cb`): beyond reach here
  (band edges as essential suprema over `A_{K,p}` with `lem:app-esssup-subgradients` and the band-containment schedule;
  `prop:vector-transfer` (a) is the frozen Hilbert-space claims applied to `H_d` (a restatement) and (c) is the
  certified `empirical_wass_rate20` at dimension `dK`; Riemannian comparison geometry for G and T).
* `thm:app-hard-diagonal`, `thm:app-entropic-diagonal`: the envelope versions (`cor:app-hard-envelope` is certified,
  wave 24a; `rem:app-entropic-envelope`); the two named references specifically (generalised to any boundedly
  supported `μ`); rates (none claimed by the paper).

Encodings (to be checked by the critic):
* `H : Type` a separable real Hilbert space with its Borel σ-algebra; `e` orthonormal with dense span; `Π_K = truncK e K`,
  `ι_K = embed e K`, `μ_K = Π_K#μ`; `P ∈ 𝒫^ℓ(H)` is the frozen `PellClass` (with A's second moment); "boundedly supported
  `μ`" is `μ (closedBall 0 M)ᶜ = 0`; `𝔽_P` is any Borel `F` with `F#P = μ`, `P`-a.e. cyclically monotone (wave L3 encoding).
* Samples: `X i` measurable, `iIndepFun`, each with law `P`; the first `n` curves are `X 0, …, X (n−1)`. Expectations are
  lower Lebesgue integrals `∫⁻` of `ℝ≥0∞` averages `(n : ℝ≥0∞)⁻¹ * Σ_{i < n}` (the `n = 0` term is `0`).
* Grids: `u K n : Fin n → ℝ^K`; the paper's "uniform laws on `n` distinct points of `supp μ_K` with `W₂(μ_{K,n}, μ_K) → 0`"
  is generalised to: points bounded for each fixed `K` and `n⁻¹ Σ f(u_i) → ∫ f dμ_K` for bounded continuous `f` (implied by
  the printed hypotheses); the entropic theorem keeps "distinct" (`Function.Injective`), used by the Gibbs bound.
* Hard estimator: `u_{σ̂(i)}` with `σ̂ = sel K n (Π_K X_0, …)`, `sel` any rule returning optimal assignments (frozen
  `IsMin`) with measurable fibres (the paper's "fixed measurable tie-breaking rule").
* Entropic estimator: the barycentric rank at a minimiser of the empirical semi-dual, `baryT ε u ĝ (Π_K X_i)` with `ĝ`
  ANY minimiser of the frozen `Jemp` (for `n, m ≥ 1`, `ε > 0`; no minimiser exists at `n = 0`, so the hypothesis is
  restricted to `0 < n`); this is Wave 21a's frozen encoding of `R^{bar}_{i,K,ε}`. Staircases: `Monotone`, `Antitone`,
  `Tendsto … atTop`. The `∫⁻` over `ω` is not a lower-integral artefact of a non-measurable selection: `Jemp` is
  strictly convex modulo constants (Hessian `Σ_i (diag p_i − p_i p_iᵀ)/(nε)`, kernel `ℝ𝟙`) and `baryT` is invariant
  under `g ↦ g + c`, so the integrand does not depend on the chosen minimiser and is a continuous function of the data.
* `thm:app-ghs-existence`: `ψ : H → EReal` proper (never `⊥`, somewhere finite), convex (convex epigraph in `H × ℝ`),
  lower semicontinuous (Tau Ceti's encoding); `∇ψ#P = Q` is read as: a Borel `F` with `F#P = Q` and `∂ψ(x) = {F x}` for
  `P`-a.e. `x` (the `P`-a.e. unique subgradient; `∂ψ` is single-valued off a countable union of Lipschitz
  hypersurfaces, Zajíček, hence `P`-a.e. on `dom ∂ψ`). Relation to Gâteaux gradients: at `x ∈ int dom ψ` (where the lsc convex `ψ` is continuous)
  `∂ψ(x) = {F x}` iff `ψ` is Gâteaux differentiable at `x` with gradient `F x`; for boundedly supported `Q` the
  potential has the finite Lipschitz representative of `cor:app-ghs-lipschitz`, so the two readings coincide. For
  unbounded `Q` the reading "Gâteaux gradient on `int dom ψ`, `P(int dom ψ) = 1`" would make the theorem FALSE:
  `P = Law(Σ_j j⁻¹ ξ_j e_j)` (`ξ_j` iid `N(0,1)`, in `𝒫^ℓ`), `Q = F#P`, `F(x) = Σ_j j^{1/4} x_j e_j`; any admissible
  `ψ` is locally Lipschitz on `int dom ψ`, so `F` would be `P`-essentially bounded on a ball, but every ball has
  positive mass on `{‖F‖ > C}` (move one coordinate `x_J ≈ r/5`, `J` large), so `int dom ψ = ∅` for EVERY admissible
  `ψ`. Hence the encoding is not easier than the paper: it is the only reading under which the paper is true.
* `thm:app-ghs-stability`: `P ∈ 𝒫^ℓ(H)` is `LipNull P` (no moment, as in GHS); "`supp γ_n ⊆ ∂ψ_n`, `ψ_n` proper lsc convex" is `supp γ_n ⊆ {p | IsSubgradOn D_n ψ_n p.1 p.2}`
  with `IsSubgradOn D f x y := x ∈ D ∧ ∀ z ∈ D, f x + ⟪y, z − x⟫ ≤ f z` (`∂` of the function `f` on `D`, `+∞` off `D`;
  convexity and lower semicontinuity of `ψ_n` are not needed: generalisation); `sup_{(x,y) ∈ ∂ψ_n, x ∈ 𝒦₀} … → 0` is
  `∀ ε > 0, ∀ᶠ n, ∀ x ∈ 𝒦₀, ∀ y, IsSubgradOn … → … ≤ ε` (no `sSup` junk); the limit potential `ψ` is the
  everywhere-finite Lipschitz representative of `cor:app-ghs-lipschitz` (as in wave L6), `𝔽 = ∇ψ` a Borel `P`-a.e.
  subgradient selection with `𝔽#P = Q`; "`𝒦₀ ⊆ int(dom ∇ψ) ∩ int(supp P)`" is `𝒦₀ ⊆ int (supp P)` plus Gâteaux
  differentiability of `ψ` with gradient `𝔽 x` at each `x ∈ 𝒦₀` (weaker: no neighbourhood). Taking `ψ` Lipschitz loses
  nothing: the paper's `ψ` agrees `P`-a.e. with `ψ̃` (`cor:app-ghs-lipschitz`), both are continuous on the open
  `U = int(dom ∇ψ) ∩ int(supp P)` and `P` charges every nonempty open subset of `U`, so `ψ = ψ̃` on `U` and their
  gradients agree on `𝒦₀`. `supp Q_n, supp Q ⊆ B̄(0,M)` as measure-zero
  complements; the uniform subgradient bound (`eq:app-uniform-subgradient`) for `n ≥ N₀`.
* T `thm:empirical`: `ν` bounded (`ν ∈ 𝒫^ℓ` dropped: unused), `μ` null on Lipschitz hypersurfaces and bounded, `Q_ν` any
  Borel `μ`-a.e. cyclically monotone map with `Q_ν#μ = ν`; `V_j` iid `ν`; `P_K = ι_K Π_K`; the quantiser is
  `ξ_n = a_n ∘ bin_n` with finitely many atoms `a_n : Fin M_n → H` and a Borel bin index (values in `P_{K_n}H` not
  required), `‖ξ_n‖ ≤ B_μ` `μ`-a.e., `r_n² → 0`; `μ_n` has weights `w_k = μ(bin_n⁻¹{k})`. The entropic program is written
  in its finite form over coupling matrices `p ∈ ℝ^{M_n × n}` (rows `w`, columns `1/n`; target LABELS retained, as the
  proof says), `entObj = Σ p‖a_k − y_j‖² + ε Σ p log(p n / w)` (`= KL(π | μ_n ⊗ ν_n)` on labels; `0 log 0 = 0` via
  `Real.log 0 = 0`), `π_n` any minimiser (`IsEntropicMin`); `Q̄_n(u) = binBary = Σ_j (p_{kj}/w_k) y_j` at `k = bin_n u`
  (the division is junk only on `μ`-null bins); the error is `∫⁻ ‖Q̄_n − Q_ν‖ₑ² dμ`, almost surely in `ω` (`∀ᵐ` is
  the complete-measure form; the minimiser is unique by strict convexity of `p log p`, so `p n ω` is a function of
  the data anyway). Labelled source rows: if `a_n` is not injective the paper's `μ_n = ξ_n#μ` merges bins, but the
  labelled minimiser splits the merged one proportionally to `w`, so `Q̄_n` is unchanged (generalisation).
  `ξ_n = a_n ∘ bin_n` is no restriction (any finite-valued Borel `ξ_n` factors through the index of its range).
  DISCHARGE: Gibbs matrix `w_k n⁻¹ e^{(g_k + f_j − ‖a_k − y_j‖²)/ε}` with the right marginals (exact solver; it is then a
  minimiser, proved); all other objects are the frozen Wave 24c ones (`smoothMap`, `P n = P_{K_n}`, `ξ n`).
* `lem:rt-pooled-graph`: the frozen `FixedKSetting` (two iid groups in `ℝ^K`, pooled sample `pool`, grids, `F^Λ_K` a.e.
  gradient of a finite convex function); `Δ_N = poolDisc F (u ν) (pool …) σ = N⁻¹ Σ_i ‖u_{σ i} − F(z_i)‖²` (real);
  expectation `∫⁻ ofReal Δ_N`; in probability is `TendstoInMeasure` to `0`.

Critic notes:
* All 10 claims are proved in `Wave25b/Route{Conc,Hard,HardMain,GHS,GHSMain,Pooled,PooledMain,Exist,SoftZero,
  SoftZero2,Ent,EntMain,EmpMat,EmpConv,EmpPlan,EmpStab,EmpMain,EmpGibbs,SmoothDis}.lean` (axioms: propext,
  Classical.choice, Quot.sound). Routes use the certified WaveL3 `plan_stab_a_uncond`, `plan_stab_b_uncond`,
  `plan_stab_b_map_uncond`, `sieve_strong_limit_uncond`, `brenier_exists_H`, `cycmon_iff`, `lipnull_of_ac`, WaveL1
  `plan_stab_a`, WaveL8 `brenier_uniq_H` (moment-free uniqueness: GHS stability and `thm:empirical`), Wave1 `pullback`,
  Wave19a `app_graph_barycenter`, Wave21a `fixed_soft_consistency`, `exists_isMinOn_Jpop`, `slln_avg`, Wave24c
  `smooth_consistency`, and untrusted libraries (`Foundations/Empirical` Varadarajan,
  `Foundations/ConvexH`, `Foundations/OTLimits`, `Foundations/Potentials` AGS 6.2.10 and the Lipschitz-hypersurface
  cover, wave-19a/L2 route lemmas, Tau Ceti Prokhorov-for-couplings and Rockafellar) — routes only.
* Proof routes: hard diagonal — at fixed `K` everything lives in `H` (no pullback needed): assignment plans are
  cyclically monotone, plan stability gives `⇀ (Id × G_K)#P`, and the strong law for countably many test functions
  (wave-19a) gives `L²` graph concentration with empirical first marginals; `G_K → 𝔽_P` by plan stability; diagonal.
  Entropic diagonal — new zero-temperature step: first-order condition of `𝒥_ε` (grid marginal), the Gibbs identity and
  weak duality give `cost(γ_ε) ≤ OT + ε log m`; limit points are optimal, hence the unique semi-discrete plan; then
  `app_graph_barycenter`; grid step by `plan_stab_b_uncond`; triple staircase. GHS existence — truncate `Q`, Brenier maps
  onto `Q_n`, Prokhorov limit with cyclically monotone support, Rockafellar potential, a.e. single-valuedness from the
  Lipschitz-hypersurface cover. GHS stability — plan stability `γ_n ⇀ (Id × 𝔽)#P` plus the portmanteau theorem on an open
  set `{x' ∈ B(x − th, r), ⟪y', h⟫ > ⟪𝔽 x, h⟫ − 3ε}` of positive limit mass replaces the fixed-marginal convergence in
  measure of wave L6; compactness for uniformity; (⋆) or finite dimension for norms.
* No tautology: every conclusion is a limit or an existence statement not among the hypotheses; no hypothesis states a
  convergence of the estimators.
* Strengthenings found: A's GHS existence holds for every target (no moment); GHS stability needs no moment of `P`
  (only null Lipschitz hypersurfaces: wave L8); `thm:empirical` holds for every minimiser and needs no `ν ∈ 𝒫^ℓ`; hard/entropic diagonals hold for any
  boundedly supported reference and weakly convergent bounded grids (the hard one without distinct points);
  `lem:rt-pooled-graph` holds almost surely for every sequence of optimal assignments; GHS stability does not need
  convexity or lower semicontinuity of `ψ_n`.
* No statement was found false.
* Critic review (wave 25b): all 10 claims faithful to the current text (fixes: source line ranges; the encoding notes on
  the `∇ψ` reading of `thm:app-ghs-existence` with the Gaussian example showing `int dom ψ` can be empty for every
  admissible `ψ`, on the Lipschitz representative in the stability claims, on selection-independence of the entropic
  integrands, on labelled source rows). DISCHARGE diff against the frozen Wave 24c `smooth_consistency` (second
  conjunct): `μ` a probability law (`LipNull`, bounded), `P n = ι_{K_n}Π_{K_n}`, `ξ n = a n ∘ bin n`, `m n = n`,
  `y n = P_{K_n} V_j(ω)`, `f n = f n ω`, `Q̄_n = Q^sm_n ∘ ξ_n`; the bound `‖y‖ ≤ B` is derived (`ν` bounded) and the
  premise `Q̄_n → Q_ν` is removed (it follows from `empirical_quantile` once the Gibbs matrix is shown to be an
  `IsEntropicMin`, `gibbs_isEntropicMin`, plus `binBary = Q^sm` at occupied atoms); the added hypotheses are exactly
  `thm:empirical`'s setting and `cor:smooth`'s "exact solver with target duals `f_{nj}`". GHS (iii): no claim
  reasserts it; `app_ghs_stability_norm` needs (⋆), which fails in `prop:ghs-iii-counterexample` (`e_n` has no compact
  range), and the counterexample satisfies the conclusion of `app_ghs_stability_weak` (`⟪e_n, h⟫ → 0`).

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace BoundedContinuousFunction

namespace StatFormal.Wave25b

open StatFormal.OTFD.WaveL1 (CycMon CMConc IsCMMapAE Graph LipNull Mom2 Euc)
open StatFormal.OTFD.WaveL3 (Mom1)
open StatFormal.OTFD.Wave1 (PellClass truncK)
open StatFormal.OTFD.Wave8b (embed)
open StatFormal.OTFD.Ranks (IsMin)
open StatFormal.OTFD.Wave22a (IsSubgrad)
open StatFormal.OTFD.WaveL2 (FixedKSetting pool)

section Defs
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `y ∈ ∂ψ(x)` for the extended-valued function `ψ` equal to `f` on `D` and `+∞` off `D`:
`x ∈ D` and `f x + ⟪y, z − x⟫ ≤ f z` for every `z ∈ D`. -/
def IsSubgradOn (D : Set H) (f : H → ℝ) (x y : H) : Prop := x ∈ D ∧ ∀ z ∈ D, f x + ⟪y, z - x⟫ ≤ f z

end Defs

section Entropic
variable {E : Type*} [NormedAddCommGroup E]

/-- `p` is a coupling matrix of the row weights `w` (source atoms) and the uniform target label weights `1/n`. -/
def IsCouplingMat {M n : ℕ} (w : Fin M → ℝ) (p : Fin M → Fin n → ℝ) : Prop :=
  (∀ k j, 0 ≤ p k j) ∧ (∀ k, ∑ j, p k j = w k) ∧ ∀ j, ∑ k, p k j = 1 / (n : ℝ)

/-- The entropic objective `∫ ‖x − y‖² dπ + ε KL(π | μ_n ⊗ ν_n)` in its finite form,
`Σ_{k,j} p_{kj} ‖a_k − y_j‖² + ε Σ_{k,j} p_{kj} log(p_{kj} / (w_k n⁻¹))` (`0 log 0 = 0`). -/
def entObj {M n : ℕ} (ε : ℝ) (w : Fin M → ℝ) (a : Fin M → E) (y : Fin n → E) (p : Fin M → Fin n → ℝ) : ℝ :=
  ∑ k, ∑ j, p k j * ‖a k - y j‖ ^ 2 + ε * ∑ k, ∑ j, p k j * Real.log (p k j * n / w k)

/-- `p` minimises the entropic objective over the coupling matrices. -/
def IsEntropicMin {M n : ℕ} (ε : ℝ) (w : Fin M → ℝ) (a : Fin M → E) (y : Fin n → E) (p : Fin M → Fin n → ℝ) : Prop :=
  IsCouplingMat w p ∧ ∀ q, IsCouplingMat w q → entObj ε w a y p ≤ entObj ε w a y q

variable [Module ℝ E]

/-- The binned barycentric estimator at the bin `k`: `∫ y π_n(dy | a_k) = Σ_j (p_{kj}/w_k) y_j`. -/
def binBary {M n : ℕ} (w : Fin M → ℝ) (y : Fin n → E) (p : Fin M → Fin n → ℝ) (k : Fin M) : E :=
  ∑ j, (p k j / w k) • y j

end Entropic

/-- The pooled squared graph discrepancy `Δ_N = N⁻¹ Σ_{i ≤ N} ‖R_i − F(Z_i)‖²` of the ranks `R = u ∘ σ` of the pooled
points `z`. -/
def poolDisc {K N : ℕ} (F : Euc K → Euc K) (u z : Fin N → Euc K) (σ : Equiv.Perm (Fin N)) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, ‖u (σ i) - F (z i)‖ ^ 2

namespace Claims

/-- A `thm:app-hard-diagonal`: a deterministic staircase `K_n ↑ ∞` with
`E[n⁻¹ Σ_{i < n} ‖ι_{K_n} u_{σ̂(i)} − 𝔽_P(X_i)‖²] → 0`, `σ̂` the bijective hard assignment of the projected sample to
the `n`-point grid (measurable tie-breaking). -/
def app_hard_diagonal : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (P μ : ProbabilityMeasure H) (F : H → H) (M : ℝ)
    (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (X : ℕ → Ω → H)
    (u : (K n : ℕ) → Fin n → Euc K) (sel : (K n : ℕ) → (Fin n → Euc K) → Equiv.Perm (Fin n)),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    PellClass (P : Measure H) → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
    Measurable F → (P : Measure H).map F = μ → IsCMMapAE (P : Measure H) F →
    (∀ i, Measurable (X i)) → iIndepFun X Pr → (∀ i, Pr.map (X i) = P) →
    (∀ K, ∃ R : ℝ, ∀ n i, ‖u K n i‖ ≤ R) →
    (∀ K (f : Euc K →ᵇ ℝ), Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i, f (u K n i)) atTop
      (𝓝 (∫ z, f z ∂((μ : Measure H).map (truncK e K))))) →
    (∀ K n z, IsMin (u K n) z (sel K n z)) → (∀ K n h, MeasurableSet {z | sel K n z = h}) →
      ∃ Kn : ℕ → ℕ, Monotone Kn ∧ Tendsto Kn atTop atTop ∧
        Tendsto (fun n : ℕ => ∫⁻ ω, (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n,
          ‖embed e (Kn n) (u (Kn n) n (sel (Kn n) n (fun j => truncK e (Kn n) (X j ω)) i)) - F (X i ω)‖ₑ ^ 2 ∂Pr)
          atTop (𝓝 0)

/-- A `thm:app-entropic-diagonal`: deterministic staircases `K_n ↑ ∞`, `m_n ↑ ∞`, `ε_n ↓ 0` along which the embedded
entropic barycentric ranks (frozen Wave 21a objects: `baryT` at a minimiser of the empirical semi-dual `Jemp` of the
projected data against the `m`-point grid) converge to `𝔽_P` in mean square. -/
def app_entropic_diagonal : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (P μ : ProbabilityMeasure H) (F : H → H) (M : ℝ)
    (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (X : ℕ → Ω → H)
    (u : (K m : ℕ) → Fin m → Euc K) (ghat : (K m : ℕ) → ℝ → (n : ℕ) → Ω → Fin m → ℝ),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    PellClass (P : Measure H) → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
    Measurable F → (P : Measure H).map F = μ → IsCMMapAE (P : Measure H) F →
    (∀ i, Measurable (X i)) → iIndepFun X Pr → (∀ i, Pr.map (X i) = P) →
    (∀ K m, Function.Injective (u K m)) → (∀ K, ∃ R : ℝ, ∀ m j, ‖u K m j‖ ≤ R) →
    (∀ K (f : Euc K →ᵇ ℝ), Tendsto (fun m : ℕ => (m : ℝ)⁻¹ * ∑ j, f (u K m j)) atTop
      (𝓝 (∫ z, f z ∂((μ : Measure H).map (truncK e K))))) →
    (∀ K m (ε : ℝ) (n : ℕ) ω, 0 < m → 0 < ε → 0 < n →
      IsMinOn (StatFormal.Wave21a.Jemp ε (u K m) fun i : Fin n => truncK e K (X i ω)) univ (ghat K m ε n ω)) →
      ∃ (Kn mn : ℕ → ℕ) (εn : ℕ → ℝ), Monotone Kn ∧ Tendsto Kn atTop atTop ∧ Monotone mn ∧
        Tendsto mn atTop atTop ∧ Antitone εn ∧ (∀ n, 0 < εn n) ∧ Tendsto εn atTop (𝓝 0) ∧
        Tendsto (fun n : ℕ => ∫⁻ ω, (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n,
          ‖embed e (Kn n) (StatFormal.Wave21a.baryT (εn n) (u (Kn n) (mn n)) (ghat (Kn n) (mn n) (εn n) n ω)
            (truncK e (Kn n) (X i ω))) - F (X i ω)‖ₑ ^ 2 ∂Pr) atTop (𝓝 0)

/-- A `thm:app-ghs-existence` (GHS Thm 2.3): for `P ∈ 𝒫^ℓ(H)` and any Borel probability `Q` on `H` (no moment), a
proper (never `⊥`, somewhere finite) convex lower semicontinuous `ψ : H → (−∞, ∞]` with `∇ψ#P = Q`, `∇ψ` read as the
`P`-a.e. unique subgradient: `∂ψ(x) = {F x}` for `P`-a.e. `x`, `F` Borel, `F#P = Q`. -/
def app_ghs_existence : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (P Q : ProbabilityMeasure H),
    PellClass (P : Measure H) →
      ∃ (ψ : H → EReal) (F : H → H), Convex ℝ {p : H × ℝ | ψ p.1 ≤ p.2} ∧ LowerSemicontinuous ψ ∧
        (∀ x, ψ x ≠ ⊥) ∧ (∃ x, ψ x ≠ ⊤) ∧ Measurable F ∧ (P : Measure H).map F = Q ∧
        ∀ᵐ x ∂(P : Measure H), TauCeti.subdifferential (innerₗ H) ψ x = {F x}

/-- A `thm:app-ghs-stability` (i) (GHS Thm 3.1(i), with the absolute value): weak local-uniform convergence of the
subgradients `∂ψ_n` to `∇ψ` on a strongly compact `𝒦₀ ⊆ int (supp P)` of Gâteaux points of `ψ`. -/
def app_ghs_stability_weak : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (Pn Qn : ℕ → ProbabilityMeasure H) (P Q : ProbabilityMeasure H) (γ : ℕ → ProbabilityMeasure (H × H))
    (D : ℕ → Set H) (ψn : ℕ → H → ℝ) (ψ : H → ℝ) (F : H → H) (M L : ℝ) (N₀ : ℕ) (K₀ : Set H) (h : H),
    Tendsto Pn atTop (𝓝 P) → LipNull (P : Measure H) → Tendsto Qn atTop (𝓝 Q) →
    (∀ n, (Qn n : Measure H) (Metric.closedBall 0 M)ᶜ = 0) → (Q : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
    (∀ n, (γ n : Measure (H × H)).fst = Pn n) → (∀ n, (γ n : Measure (H × H)).snd = Qn n) →
    (∀ n, (γ n : Measure (H × H)).support ⊆ {p | IsSubgradOn (D n) (ψn n) p.1 p.2}) →
    ConvexOn ℝ univ ψ → (∀ x x', |ψ x - ψ x'| ≤ L * ‖x - x'‖) →
    Measurable F → (P : Measure H).map F = Q → (∀ᵐ x ∂(P : Measure H), IsSubgrad ψ x (F x)) →
    IsCompact K₀ → K₀ ⊆ interior (P : Measure H).support →
    (∀ x ∈ K₀, ∀ v, HasLineDerivAt ℝ ψ ⟪F x, v⟫ x v) →
    (∀ n, N₀ ≤ n → ∀ x ∈ K₀, ∀ y, IsSubgradOn (D n) (ψn n) x y → ‖y‖ ≤ M) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x ∈ K₀, ∀ y, IsSubgradOn (D n) (ψn n) x y → |⟪y - F x, h⟫| ≤ ε

/-- A `thm:app-ghs-stability` (ii): under the common strongly compact range (⋆), the convergence is in norm. -/
def app_ghs_stability_norm : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (Pn Qn : ℕ → ProbabilityMeasure H) (P Q : ProbabilityMeasure H) (γ : ℕ → ProbabilityMeasure (H × H))
    (D : ℕ → Set H) (ψn : ℕ → H → ℝ) (ψ : H → ℝ) (F : H → H) (M L : ℝ) (N₀ : ℕ) (K₀ C : Set H),
    Tendsto Pn atTop (𝓝 P) → LipNull (P : Measure H) → Tendsto Qn atTop (𝓝 Q) →
    (∀ n, (Qn n : Measure H) (Metric.closedBall 0 M)ᶜ = 0) → (Q : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
    (∀ n, (γ n : Measure (H × H)).fst = Pn n) → (∀ n, (γ n : Measure (H × H)).snd = Qn n) →
    (∀ n, (γ n : Measure (H × H)).support ⊆ {p | IsSubgradOn (D n) (ψn n) p.1 p.2}) →
    ConvexOn ℝ univ ψ → (∀ x x', |ψ x - ψ x'| ≤ L * ‖x - x'‖) →
    Measurable F → (P : Measure H).map F = Q → (∀ᵐ x ∂(P : Measure H), IsSubgrad ψ x (F x)) →
    IsCompact K₀ → K₀ ⊆ interior (P : Measure H).support →
    (∀ x ∈ K₀, ∀ v, HasLineDerivAt ℝ ψ ⟪F x, v⟫ x v) →
    (∀ n, N₀ ≤ n → ∀ x ∈ K₀, ∀ y, IsSubgradOn (D n) (ψn n) x y → ‖y‖ ≤ M) →
    IsCompact C → (∀ n, ∀ x ∈ K₀, ∀ y, IsSubgradOn (D n) (ψn n) x y → y ∈ C) → (∀ x ∈ K₀, F x ∈ C) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x ∈ K₀, ∀ y, IsSubgradOn (D n) (ψn n) x y → ‖y - F x‖ ≤ ε

/-- A `thm:app-ghs-stability` (ii), last sentence: in finite dimension the norm conclusion holds without (⋆). -/
def app_ghs_stability_fd : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [MeasurableSpace H] [BorelSpace H]
    (Pn Qn : ℕ → ProbabilityMeasure H) (P Q : ProbabilityMeasure H) (γ : ℕ → ProbabilityMeasure (H × H))
    (D : ℕ → Set H) (ψn : ℕ → H → ℝ) (ψ : H → ℝ) (F : H → H) (M L : ℝ) (N₀ : ℕ) (K₀ : Set H),
    Tendsto Pn atTop (𝓝 P) → LipNull (P : Measure H) → Tendsto Qn atTop (𝓝 Q) →
    (∀ n, (Qn n : Measure H) (Metric.closedBall 0 M)ᶜ = 0) → (Q : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
    (∀ n, (γ n : Measure (H × H)).fst = Pn n) → (∀ n, (γ n : Measure (H × H)).snd = Qn n) →
    (∀ n, (γ n : Measure (H × H)).support ⊆ {p | IsSubgradOn (D n) (ψn n) p.1 p.2}) →
    ConvexOn ℝ univ ψ → (∀ x x', |ψ x - ψ x'| ≤ L * ‖x - x'‖) →
    Measurable F → (P : Measure H).map F = Q → (∀ᵐ x ∂(P : Measure H), IsSubgrad ψ x (F x)) →
    IsCompact K₀ → K₀ ⊆ interior (P : Measure H).support →
    (∀ x ∈ K₀, ∀ v, HasLineDerivAt ℝ ψ ⟪F x, v⟫ x v) →
    (∀ n, N₀ ≤ n → ∀ x ∈ K₀, ∀ y, IsSubgradOn (D n) (ψn n) x y → ‖y‖ ≤ M) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x ∈ K₀, ∀ y, IsSubgradOn (D n) (ψn n) x y → ‖y - F x‖ ≤ ε

/-- A `lem:rt-pooled-graph`: under the hypotheses of `thm:rt-fixedK` (frozen `FixedKSetting`), almost surely
`Δ_N → 0` for every sequence of optimal assignments of the pooled sample; for a measurable selection rule, `Δ_N` is
measurable and `Δ_N → 0` in probability and in expectation. -/
def rt_pooled_graph : Prop :=
  ∀ (K : ℕ) (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (P Q μ : Measure (Euc K))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure μ] (θ R : ℝ) (F : Euc K → Euc K)
    (Z W : ℕ → Ω → Euc K) (n₁ n₂ : ℕ → ℕ) (u : ∀ ν, Fin (n₁ ν + n₂ ν) → Euc K)
    (sel : ∀ ν, (Fin (n₁ ν + n₂ ν) → Euc K) → Equiv.Perm (Fin (n₁ ν + n₂ ν))),
    FixedKSetting K Pr P Q μ θ R F Z W n₁ n₂ u →
    (∀ ν z, IsMin (u ν) z (sel ν z)) → (∀ ν h, MeasurableSet {z | sel ν z = h}) →
      (∀ᵐ ω ∂Pr, ∀ σ : ∀ ν, Equiv.Perm (Fin (n₁ ν + n₂ ν)),
        (∀ ν, IsMin (u ν) (pool (n₁ ν) (n₂ ν) Z W ω) (σ ν)) →
          Tendsto (fun ν => poolDisc F (u ν) (pool (n₁ ν) (n₂ ν) Z W ω) (σ ν)) atTop (𝓝 0)) ∧
      (∀ ν, Measurable fun ω => poolDisc F (u ν) (pool (n₁ ν) (n₂ ν) Z W ω) (sel ν (pool (n₁ ν) (n₂ ν) Z W ω))) ∧
      TendstoInMeasure Pr (fun ν ω => poolDisc F (u ν) (pool (n₁ ν) (n₂ ν) Z W ω) (sel ν (pool (n₁ ν) (n₂ ν) Z W ω)))
        atTop (fun _ => 0) ∧
      Tendsto (fun ν => ∫⁻ ω, ENNReal.ofReal
        (poolDisc F (u ν) (pool (n₁ ν) (n₂ ν) Z W ω) (sel ν (pool (n₁ ν) (n₂ ν) Z W ω))) ∂Pr) atTop (𝓝 0)

/-- T `thm:empirical` (`eq:empQ`), under `ass:model` and `eq:quantize`: if `ε_n log n → 0`, then almost surely
`∫ ‖Q̄_n(u) − Q_ν(u)‖² dμ(u) → 0`, `Q̄_n(u) = binBary` at the bin of `u` of the entropic minimiser between the binned
reference `μ_n = ξ_n#μ` and the projected empirical target `ν_n = n⁻¹ Σ_{j<n} δ_{P_{K_n} V_j}`. -/
def empirical_quantile : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (μ ν : ProbabilityMeasure H) (Qν : H → H) (Bμ B : ℝ)
    (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (V : ℕ → Ω → H)
    (K Mq : ℕ → ℕ) (a : ∀ n, Fin (Mq n) → H) (bin : ∀ n, H → Fin (Mq n)) (ε : ℕ → ℝ)
    (p : ∀ n, Ω → Fin (Mq n) → Fin n → ℝ),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    LipNull (μ : Measure H) → (μ : Measure H) (Metric.closedBall 0 Bμ)ᶜ = 0 →
    (ν : Measure H) (Metric.closedBall 0 B)ᶜ = 0 →
    Measurable Qν → (μ : Measure H).map Qν = ν → IsCMMapAE (μ : Measure H) Qν →
    (∀ j, Measurable (V j)) → iIndepFun V Pr → (∀ j, Pr.map (V j) = ν) →
    Tendsto K atTop atTop → (∀ n, Measurable (bin n)) →
    (∀ n, ∀ᵐ u ∂(μ : Measure H), ‖a n (bin n u)‖ ≤ Bμ) →
    Tendsto (fun n => ∫⁻ u, ‖u - a n (bin n u)‖ₑ ^ 2 ∂(μ : Measure H)) atTop (𝓝 0) →
    (∀ n, 0 < ε n) → Tendsto (fun n : ℕ => ε n * Real.log n) atTop (𝓝 0) →
    (∀ n ω, 0 < n → IsEntropicMin (ε n) (fun k => ((μ : Measure H) (bin n ⁻¹' {k})).toReal) (a n)
      (fun j : Fin n => embed e (K n) (truncK e (K n) (V j ω))) (p n ω)) →
      ∀ᵐ ω ∂Pr, Tendsto (fun n => ∫⁻ u, ‖binBary (fun k => ((μ : Measure H) (bin n ⁻¹' {k})).toReal)
        (fun j : Fin n => embed e (K n) (truncK e (K n) (V j ω))) (p n ω) (bin n u) - Qν u‖ₑ ^ 2
          ∂(μ : Measure H)) atTop (𝓝 0)

/-- DISCHARGE of the frozen Wave 24c `smooth_consistency` (T `cor:smooth`): its `thm:empirical` premise is replaced by
the setting of `thm:empirical` with an exact entropic solver in Gibbs form (`p_{kj} = w_k n⁻¹ e^{(g_k + f_j − ‖a_k −
y_j‖²)/ε}` with the right marginals, the plan of `smooth_exact`); then almost surely `ε_n⁻² h_n² → 0` implies `eq:empQ`
for the smooth extension `Q^sm_n(P_{K_n} u) = smoothMap ε_n f_n y_n (P_{K_n} u)` (frozen `smoothMap`). -/
def smooth_consistency_discharged : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (μ ν : ProbabilityMeasure H) (Qν : H → H) (Bμ B : ℝ)
    (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (V : ℕ → Ω → H)
    (K Mq : ℕ → ℕ) (a : ∀ n, Fin (Mq n) → H) (bin : ∀ n, H → Fin (Mq n)) (ε : ℕ → ℝ)
    (g : ∀ n, Ω → Fin (Mq n) → ℝ) (f : ∀ n, Ω → Fin n → ℝ),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    LipNull (μ : Measure H) → (μ : Measure H) (Metric.closedBall 0 Bμ)ᶜ = 0 →
    (ν : Measure H) (Metric.closedBall 0 B)ᶜ = 0 →
    Measurable Qν → (μ : Measure H).map Qν = ν → IsCMMapAE (μ : Measure H) Qν →
    (∀ j, Measurable (V j)) → iIndepFun V Pr → (∀ j, Pr.map (V j) = ν) →
    Tendsto K atTop atTop → (∀ n, Measurable (bin n)) →
    (∀ n, ∀ᵐ u ∂(μ : Measure H), ‖a n (bin n u)‖ ≤ Bμ) →
    Tendsto (fun n => ∫⁻ u, ‖u - a n (bin n u)‖ₑ ^ 2 ∂(μ : Measure H)) atTop (𝓝 0) →
    (∀ n, 0 < ε n) → Tendsto (fun n : ℕ => ε n * Real.log n) atTop (𝓝 0) →
    (∀ n ω, 0 < n → IsCouplingMat (fun k => ((μ : Measure H) (bin n ⁻¹' {k})).toReal)
      (fun k j => ((μ : Measure H) (bin n ⁻¹' {k})).toReal * (n : ℝ)⁻¹ *
        Real.exp ((g n ω k + f n ω j - ‖a n k - embed e (K n) (truncK e (K n) (V j ω))‖ ^ 2) / ε n))) →
      ∀ᵐ ω ∂Pr, Tendsto (fun n => ENNReal.ofReal ((ε n)⁻¹ ^ 2) *
          ∫⁻ u, ‖embed e (K n) (truncK e (K n) u) - a n (bin n u)‖ₑ ^ 2 ∂(μ : Measure H)) atTop (𝓝 0) →
        Tendsto (fun n => ∫⁻ u, ‖StatFormal.Wave24c.smoothMap (ε n) (f n ω)
          (fun j : Fin n => embed e (K n) (truncK e (K n) (V j ω))) (embed e (K n) (truncK e (K n) u)) -
            Qν u‖ₑ ^ 2 ∂(μ : Measure H)) atTop (𝓝 0)

end Claims

end StatFormal.Wave25b
