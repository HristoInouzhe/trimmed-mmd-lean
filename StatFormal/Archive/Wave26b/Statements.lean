import StatFormal.Archive.Wave20a.Statements
import StatFormal.Archive.ICL.Joint.Statements
import StatFormal.Archive.ICL.Diag.Statements
import StatFormal.Archive.Wave12b.Statements
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# FROZEN STATEMENTS — wave 26b (QUEUE rows 328, 360): otfd C `prop:metric-uniform-localization` (entropic
# penalty), ICL `cor:iid-consistency`

Sources:
* otfd C `prop:metric-uniform-localization` (`otfd/papers/C_conditional/supplement.tex:713-763`, proof `:765-860`),
  with `lem:self-potentials` (`:558-573`), the self-transport weights (`eq:self-ent-weights`, `:545-555`; main
  `eq:self-ent`, `main.tex:335-347`), `thm:self-localization` and `eq:self-conditional-consistency`
  (`main.tex:498-512`), `n_eff = 1/Σ_i w_i²` (`main.tex:353`).
* ICL `cor:iid-consistency` (`context-distribution-ICL/paper/v3/supp/iid.tex:22-31`, proof
  `supp/proofs_main.tex:162-168`), with the i.i.d. objective (`supp/iid.tex:9-20`), `J_m` and `J_pool`
  (`sections/03_framework.tex:60-75`), the coverage `ρ_μ`, `Φ` (`sections/04_selector.tex:5-14`) and the reduction of
  `cor:consistency` (`supp/proofs_main.tex:123-133`).
Imports the frozen `Wave20a` (`rhoC`, `PhiC`), `ICL/Joint` (`ProbVec`), `ICL/Diag` (`klUnif`) and `Wave12b` (`Euc`;
through it `OTFD/Bands` `softmax`, Tau Ceti `wassersteinEDist`, `Measure.compProd`) statements; Mathlib otherwise.

Covered:
* C `prop:metric-uniform-localization`, entropic penalty: `metric_uniform_localization` (the main display uniform
  over `𝒮_j × D_X`, `inf n_eff/log n → ∞` over `𝒮_j × D_X`, and (i) for metrics and scales that eventually stay in a
  compact subset of `GL_q × (0,∞)` or converge almost surely there, with the same schedule; (ii) is (i) for a
  constant sequence), `metric_fixed_strength` ((iii)), `metric_selfpot_exists_unique` (the reduction step:
  existence and uniqueness of the population self-potential on `D_X` and of the empirical one, for every metric).
  No conditional premise. The uniform self-localization theory is the new library
  `StatFormal/Foundations/Localization` (self-potentials on a compact metric space: bounds, Lipschitz modulus,
  uniqueness, a quantitative Laplace bound `|F| ≤ η + (ε/2) log(1/β)`, finite (Sinkhorn) existence, stability under
  weak convergence and cost perturbation by Arzelà–Ascoli; joint `W₁`-continuity of localized laws; the bias bound by
  Kantorovich–Rubinstein; uniformity over sequentially compact parameter sets of `GL_q × ℝ`), with Varadarajan
  (Foundations), the Giry = Borel identification (Foundations) and the frozen Wave 22b `selfloc_staircase` and
  `selfloc_weight_ent`.
* ICL `cor:iid-consistency`: `iid_consistency`, in full (no conditional premise). The proof chains the frozen
  `thm:joint` (`ICL/JointFull` `joint_full`, at `δ = 1/m`, for the product laws `Π = w^{⊗M}`), `cor:oracle`
  (`ICL/Diag` `oracle`) and the frozen consistency chain (`Wave24d` `icl_consistency`) with the steps that were
  hypotheses there and are proved here: the reduction `J_pool(w) = R^iid(μ_w) + λ_KL KL(w|u_n)` with
  `0 ≤ KL ≤ log n`, the identity `J_m − J_pool = devFull(w^{⊗M})` (one-slot marginal of `w^{⊗M}` is `w`,
  `μ_w^{⊗M} = Σ_t Π_s w_{t_s} δ_{z_t}`), the almost-sure pool event (pool points in `supp P₀` and eventually dense in
  it), weak continuity of `R^iid` on `𝒫(𝒵)` and the existence of the minimiser `μ⋆` over `𝒫(supp P₀)`, and the
  approximation `min_w R^iid(μ_w) → R^{iid⋆}` by pool quantisations of `μ⋆`.

Not covered (declared):
* C: the quadratic penalty throughout (the `η_n` schedule, the `P̂^Q` display, `n η_n/log n → ∞`, the quadratic half
  of `n_eff` and of (iii)): it needs the hinge self-potential theory (existence of the finite quadratic self-transport
  plan, uniqueness via the strictly convex quadratic programme, the threshold-extension bounds, stability), not
  built here. The examples sentence of (i) (standardisation, whitening by the inverse Cholesky factor, median-distance
  scales; informal, they rely on package conventions), (ii) as a separate statement, and the remark "the limit is not
  `P_{K,x}` in general" of (iii) (informal).
* ICL: `𝒜 = CVaR_α` (only the mean risk, as printed: "`𝒜` the mean risk").

Encodings (to be checked by the critic):
* C: `ℝ^q = Euc q`; `GL_q = (Euc q →L[ℝ] Euc q)ˣ` with the units topology (`GLq`); `𝒮_j` (`sSet`) with operator norms
  and `s ∈ (0,∞)` as printed (so `𝒮_0 = ∅`); `D_X = supp P_X` (`Measure.support`), compact; the model `LocModel`:
  `(X_i, Z_i)` i.i.d. (`iIndepFun` of the pairs) with law `P_X ⊗ κ`, `κ` a Markov kernel (the conditional law;
  `P_{K,x} = κ x`), `κ x` carried by `B̄(0, R)` and `W₁`-continuous in `x ∈ D_X` (pointwise ε–δ form) — the bounded
  response is stated for the version on `D_X` (implied by `Z ∈ B̄(0,R)` a.s. and `W₁`-continuity); sample size `n`
  uses `X_0, …, X_{n−1}` (`Fin n`); the empirical self-potential is any solution of the sample-point equations
  `IsEmpSelfPot` (unique by `metric_selfpot_exists_unique`), the weights the softmax of
  `(F_i − ‖Λ(x − X_i)‖²)/ε` (`entW`, = `eq:self-ent-weights` in whitened coordinates `C_i = ΛX_i`, query `Λx`), the
  localized law `Σ_i w_i δ_{Z_i}` (`locEmp`); population potentials `IsPopSelfPot` (continuous on `D_X`, equation on
  `D_X`), smoothed law `locPop` (`(α(·|x)·P_X).bind κ`); `W₁ = TauCeti.wassersteinEDist 1` (`ℝ≥0∞`, suprema as
  `⨆` in `ℝ≥0∞`, no junk); `n_eff = (Σ_i w_i²)⁻¹`, "`inf n_eff/log n → ∞`" as `∀ C, eventually C log n ≤ n_eff`
  uniformly; the schedule `ε_{X,n}` positive, antitone, `→ 0`, deterministic (not a function of `ω`, and chosen
  before the potentials `Fn` and before `Λ̂_n`, `ŝ_n`, so (i), and (ii) as its constant case, use one schedule), quantified after the
  probability space and the sample (as in the frozen Wave 22b `selfloc_consistency`; "law-dependent" read as
  dependent on `(Ω, P, X, Z)`, whose law is fixed by `P_X ⊗ P_{K,·}`); "almost surely" is `∀ᵐ` (the exceptional
  set lies in a `P`-null set; no measurability of the event is claimed or needed); the scales `ŝ_n`, metrics `Λ̂_n` arbitrary functions
  of `(n, ω)` (no measurability needed; the paper assumes measurable), the compact set and the limits may depend on
  `ω`; "`ε_{X}` fixed" in (iii) is `ε₀ > 0`.
* ICL: `𝒵` a compact metric space with its Borel σ-algebra; `L : 𝒵 × 𝒵^M → [0, B_L]` continuous (`𝒵^M = Fin M → 𝒵`;
  `L ≥ 0` is the standing `thm:joint` normalisation, without loss of generality by a shift), `K` continuous with
  values in `[K_min, K_max]`, `0 < K_min`; `λ_cov ≥ 0`, `λ_{KL,n} ≥ 0`, `M ≥ 1`.
* ICL: the pool is the first `n_j` points of an i.i.d. `P₀` sequence `Zs` on `(Ω₀, Q)` (nested pools); the claim holds
  for `Q`-almost every pool sequence and then for every validation probability space `(Ω, P)` carrying, for each `j`,
  an i.i.d. `P₀` validation sample of size `m_j` and any `ε_opt,j`-minimiser `ŵ_j(ω)` of `J^iid_m` over `Δ^{n_j−1}`
  ("conditionally on the pool"; `ε_opt`-minimiser stated as `J_m(ŵ) ≤ J_m(w) + ε_opt` for every `w ∈ Δ`, no infimum).
* ICL: `μ_w = Σ_j w_j δ_{z_j}` (`poolLaw`), `R^iid(μ) = ∫ G^iid_μ dP₀ + λ_cov Φ(μ)` with
  `G^iid_μ(z) = ∫ L(z; t) dμ^{⊗M}(t)` (`gIid`, `riskIid`), `Φ = PhiC` (one-slot marginal of `μ^{⊗M}` is `μ`);
  `J^iid_m(w) = m⁻¹ Σ_i G^iid_i(w) − λ_cov m⁻¹ Σ_i log ρ_w(z̃_i) + λ_KL KL(w|u_n)` with
  `G^iid_i(w) = Σ_{t ∈ [n]^M} Π_s w_{t_s} L(z̃_i; z_{t_1}, …, z_{t_M})`, `ρ_w = Σ_j w_j K(·, z_j)` (`jIidEmp`).
* ICL: `R^{iid⋆} = min_{μ ∈ 𝒫(supp P₀)} R^iid(μ)` as `IsLeast` (attained, no infimum); "in probability" is Mathlib
  `TendstoInMeasure` (no measurability of `ŵ` needed: the probability of a possibly non-measurable deviation event
  is its outer measure, so this is convergence in outer probability, at least as strong as the printed claim);
  `m_j → ∞` is stated (with Lean's `x/0 = 0`, `log n/m → 0`
  alone does not force it).

Critic notes:
* All 4 claims are proved: `iid_consistency` in `Wave26b/RouteICL.lean` (with `RouteICL{Alg,Obj,Top}`),
  `metric_uniform_localization` in `Wave26b/RouteLocMain.lean`, `metric_fixed_strength` and
  `metric_selfpot_exists_unique` in `Wave26b/RouteLocFixed.lean` (with `RouteLoc{Setup,Emp,Core,Bias,Aux}`);
  axioms `propext`, `Classical.choice`, `Quot.sound`.
* Manuscript remarks (C): (1) Step 4 bounds `P{sup_{n≥N_j} E_n(Θ_j) > 1/j}`, which needs measurability of the
  supremum; the printed proof supplies it by the end-of-Step-1 remark "suprema may be taken over countable dense
  subsets", which tacitly also needs continuity in `x` at fixed `n` and measurability in the sample of each term
  (both routine; a presentation gap, not an error). The route avoids it by working with open neighbourhoods of the
  population joint law (Giry = Borel), so the remark is not needed. (2) Step 3's subsequence argument for
  `sup ‖F‖ → 0` can be replaced by the quantitative bound `‖F_{(Λ,ε)}‖_∞ ≤ L_c r + (ε/2) log(1/β(r))` (`L_c r` the
  cost oscillation on `r`-balls, `β(r)` the smallest `P_X`-mass of an `r`-ball centred in `D_X`), uniform over
  compact sets of metrics. (3) (i) holds for arbitrary (not necessarily measurable) `Λ̂_n`, `ŝ_n`.
* Manuscript remarks (ICL): the corollary's proof uses `L ≥ 0` (through `thm:joint`) and the boundedness of `K` from
  above (`K ≤ K_max`); "pools nested" is used for the quantisation step (a weight on the first `N` pool points is a
  weight on every larger pool).

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/
set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.Wave26b

open StatFormal.Wave20a (rhoC PhiC)
open StatFormal.ICL.Joint (ProbVec)
open StatFormal.ICL.Diag (klUnif)
open StatFormal.Wave12b (Euc)

/-! ### ICL `cor:iid-consistency` -/

section ICL
variable {Z : Type*} [MeasurableSpace Z]

/-- The pool law `μ_w = Σ_j w_j δ_{z_j}`. -/
def poolLaw {n : ℕ} (z : Fin n → Z) (w : Fin n → ℝ) : Measure Z :=
  ∑ j, ENNReal.ofReal (w j) • Measure.dirac (z j)

/-- The i.i.d. per-query risk `G^iid_μ(z) = ∫ L(z; t) dμ^{⊗M}(t)`. -/
def gIid {M : ℕ} (L : Z → (Fin M → Z) → ℝ) (μ : Measure Z) (z : Z) : ℝ :=
  ∫ t, L z t ∂(Measure.pi fun _ : Fin M => μ)

/-- The i.i.d. population objective `R^iid(μ) = ∫ G^iid_μ dP₀ + λ_cov Φ(μ)`. -/
def riskIid {M : ℕ} (L : Z → (Fin M → Z) → ℝ) (Kk : Z → Z → ℝ) (lcov : ℝ) (P₀ μ : Measure Z) : ℝ :=
  ∫ z, gIid L μ z ∂P₀ + lcov * PhiC Kk P₀ μ

/-- The pool per-query risk `G^iid_i(w) = Σ_{t ∈ [n]^M} w_{t_1}⋯w_{t_M} L(x; z_{t_1}, …, z_{t_M})`. -/
def gIidPool {n M : ℕ} (L : Z → (Fin M → Z) → ℝ) (z : Fin n → Z) (w : Fin n → ℝ) (x : Z) : ℝ :=
  ∑ t : Fin M → Fin n, (∏ s, w (t s)) * L x (z ∘ t)

/-- The pool coverage `ρ_w(x) = Σ_j w_j K(x, z_j)`. -/
def rhoPool {n : ℕ} (Kk : Z → Z → ℝ) (z : Fin n → Z) (w : Fin n → ℝ) (x : Z) : ℝ :=
  ∑ j, w j * Kk x (z j)

/-- The i.i.d. empirical objective
`J^iid_m(w) = m⁻¹ Σ_i G^iid_i(w) + λ_cov(−m⁻¹ Σ_i log ρ_w(z̃_i)) + λ_KL KL(w|u_n)`. -/
def jIidEmp {n m M : ℕ} (L : Z → (Fin M → Z) → ℝ) (Kk : Z → Z → ℝ) (lcov lKL : ℝ) (z : Fin n → Z)
    (xs : Fin m → Z) (w : Fin n → ℝ) : ℝ :=
  (1 / (m : ℝ)) * ∑ i, gIidPool L z w (xs i) +
    lcov * (-(1 / (m : ℝ)) * ∑ i, Real.log (rhoPool Kk z w (xs i))) + lKL * klUnif n w

end ICL

/-! ### otfd C `prop:metric-uniform-localization` -/

section Loc

/-- `GL_q`, the units of the operator algebra of `ℝ^q` (with the induced topology). -/
abbrev GLq (q : ℕ) := (Euc q →L[ℝ] Euc q)ˣ

/-- `𝒮_j = {(Λ, s) ∈ GL_q × (0,∞) : ‖Λ‖ ≤ j, ‖Λ⁻¹‖ ≤ j, 1/j ≤ s ≤ j}` (operator norms). -/
def sSet (q j : ℕ) : Set (GLq q × ℝ) :=
  {p | ‖((p.1 : GLq q) : Euc q →L[ℝ] Euc q)‖ ≤ j ∧ ‖((p.1⁻¹ : GLq q) : Euc q →L[ℝ] Euc q)‖ ≤ j ∧
    0 < p.2 ∧ 1 / (j : ℝ) ≤ p.2 ∧ p.2 ≤ j}

/-- The entropic scores `(F_i − ‖Λ(x − X_i)‖²)/ε` of the whitened covariates `C_i = ΛX_i` at the query `Λx`. -/
def entScore {q n : ℕ} (Λ : GLq q) (ε : ℝ) (xs : Fin n → Euc q) (F : Fin n → ℝ) (x : Euc q) (i : Fin n) : ℝ :=
  (F i - ‖((Λ : GLq q) : Euc q →L[ℝ] Euc q) (x - xs i)‖ ^ 2) / ε

/-- The entropic self-transport weights `w^E_{n,i}(x)` (`eq:self-ent-weights`): the softmax of the scores. -/
def entW {q n : ℕ} (Λ : GLq q) (ε : ℝ) (xs : Fin n → Euc q) (F : Fin n → ℝ) (x : Euc q) (i : Fin n) : ℝ :=
  StatFormal.OTFD.Bands.softmax (entScore Λ ε xs F x) i

/-- The empirical symmetric entropic self-potential at the sample points (`eq:ent-self-pop` for `P̂_{C,n}`,
`C_i = ΛX_i`): `e^{F_i/ε} n⁻¹ Σ_l e^{(F_l − ‖Λ(X_i − X_l)‖²)/ε} = 1` for every `i`. -/
def IsEmpSelfPot {q n : ℕ} (Λ : GLq q) (ε : ℝ) (xs : Fin n → Euc q) (F : Fin n → ℝ) : Prop :=
  ∀ i, Real.exp (F i / ε) *
    ((1 / (n : ℝ)) * ∑ l, Real.exp ((F l - ‖((Λ : GLq q) : Euc q →L[ℝ] Euc q) (xs i - xs l)‖ ^ 2) / ε)) = 1

/-- The localized law `P̂^E_{K,n,x}[Λ, ε] = Σ_i w^E_{n,i}(x) δ_{Z_i}`. -/
def locEmp {q K n : ℕ} (Λ : GLq q) (ε : ℝ) (xs : Fin n → Euc q) (zs : Fin n → Euc K) (F : Fin n → ℝ)
    (x : Euc q) : Measure (Euc K) :=
  ∑ i, ENNReal.ofReal (entW Λ ε xs F x i) • Measure.dirac (zs i)

/-- The population symmetric entropic self-potential on `D_X = supp P_X` for the metric `Λ`: continuous on `D_X`
with `e^{F(x)/ε} ∫ e^{(F(y) − ‖Λ(x − y)‖²)/ε} dP_X(y) = 1` for `x ∈ D_X`. -/
def IsPopSelfPot {q : ℕ} (PX : Measure (Euc q)) (Λ : GLq q) (ε : ℝ) (F : Euc q → ℝ) : Prop :=
  ContinuousOn F PX.support ∧ ∀ x ∈ PX.support,
    Real.exp (F x / ε) * ∫ y, Real.exp ((F y - ‖((Λ : GLq q) : Euc q →L[ℝ] Euc q) (x - y)‖ ^ 2) / ε) ∂PX = 1

/-- The population smoothed law `P^E_{K,x}[Λ, ε] = ∫ P_{K,y} α(y | x) dP_X(y)`,
`α(y | x) = e^{(F(x) + F(y) − ‖Λ(x − y)‖²)/ε}`. -/
def locPop {q K : ℕ} (PX : Measure (Euc q)) (κ : Kernel (Euc q) (Euc K)) (Λ : GLq q) (ε : ℝ) (F : Euc q → ℝ)
    (x : Euc q) : Measure (Euc K) :=
  (PX.withDensity fun y =>
    ENNReal.ofReal (Real.exp ((F x + F y - ‖((Λ : GLq q) : Euc q →L[ℝ] Euc q) (x - y)‖ ^ 2) / ε))).bind κ

/-- The standing model of `subsec:supp-estimated-metric`: `D_X = supp P_X` compact; `(X_i, Z_i)` i.i.d. with law
`P_X ⊗ P_{K,·}`; `P_{K,x}` carried by `B̄(0, R)` and `W₁`-continuous in `x ∈ D_X`. -/
def LocModel {q K : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (PX : Measure (Euc q))
    (κ : Kernel (Euc q) (Euc K)) (R : ℝ) (Xs : ℕ → Ω → Euc q) (Zs : ℕ → Ω → Euc K) : Prop :=
  IsCompact PX.support ∧ (∀ x ∈ PX.support, κ x (Metric.closedBall 0 R)ᶜ = 0) ∧
    (∀ x ∈ PX.support, ∀ η > 0, ∃ δ > 0, ∀ y ∈ PX.support, dist y x < δ →
      TauCeti.wassersteinEDist 1 (κ y) (κ x) < ENNReal.ofReal η) ∧
    (∀ i, Measurable (Xs i)) ∧ (∀ i, Measurable (Zs i)) ∧
    iIndepFun (fun i ω => (Xs i ω, Zs i ω)) P ∧ ∀ i, P.map (fun ω => (Xs i ω, Zs i ω)) = PX ⊗ₘ κ

end Loc

namespace Claims

/-- ICL `cor:iid-consistency`: `𝒵` compact, `L` and `K` bounded and continuous, `K ≥ K_min > 0`, mean risk, `M`
fixed, nested i.i.d. pools, `λ_{KL,n} log n → 0`. The population minimum `R^{iid⋆}` over `𝒫(supp P₀)` is attained,
and for almost every pool sequence: if `ŵ` minimises `J^iid_m` over `Δ^{n−1}` up to `ε_opt → 0`, `n, m → ∞` and
`log n/m → 0`, then `R^iid(μ_ŵ) → R^{iid⋆}` in probability (over the validation sample). -/
def iid_consistency : Prop :=
  ∀ (Z Ω₀ : Type) [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z] [MeasurableSpace Ω₀]
    (P₀ : Measure Z) [IsProbabilityMeasure P₀] (Q : Measure Ω₀) [IsProbabilityMeasure Q] (Zs : ℕ → Ω₀ → Z)
    (M : ℕ) (L : Z → (Fin M → Z) → ℝ) (Kk : Z → Z → ℝ) (BL Kmin Kmax lcov : ℝ),
    1 ≤ M → Continuous (fun p : Z × (Fin M → Z) => L p.1 p.2) → (∀ z t, 0 ≤ L z t ∧ L z t ≤ BL) →
    Continuous (Function.uncurry Kk) → 0 < Kmin → (∀ z z', Kmin ≤ Kk z z' ∧ Kk z z' ≤ Kmax) → 0 ≤ lcov →
    (∀ i, Measurable (Zs i)) → iIndepFun Zs Q → (∀ i, Q.map (Zs i) = P₀) →
    ∃ Rstar : ℝ,
      IsLeast {r | ∃ μ : Measure Z, IsProbabilityMeasure μ ∧ μ P₀.supportᶜ = 0 ∧ r = riskIid L Kk lcov P₀ μ} Rstar ∧
      ∀ᵐ ω₀ ∂Q, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (n m : ℕ → ℕ)
        (X : (j : ℕ) → Fin (m j) → Ω → Z) (wh : (j : ℕ) → Ω → Fin (n j) → ℝ) (lamKL eps : ℕ → ℝ),
        (∀ j i, Measurable (X j i)) → (∀ j, iIndepFun (X j) P) → (∀ j i, P.map (X j i) = P₀) →
        (∀ j ω, ProbVec (wh j ω)) → (∀ j, 0 ≤ lamKL j) →
        (∀ j ω (w : Fin (n j) → ℝ), ProbVec w →
          jIidEmp L Kk lcov (lamKL j) (fun i : Fin (n j) => Zs i ω₀) (fun i => X j i ω) (wh j ω) ≤
            jIidEmp L Kk lcov (lamKL j) (fun i : Fin (n j) => Zs i ω₀) (fun i => X j i ω) w + eps j) →
        Tendsto (fun j => (n j : ℝ)) atTop atTop → Tendsto (fun j => (m j : ℝ)) atTop atTop →
        Tendsto (fun j => Real.log (n j) / m j) atTop (𝓝 0) →
        Tendsto (fun j => lamKL j * Real.log (n j)) atTop (𝓝 0) → Tendsto eps atTop (𝓝 0) →
          TendstoInMeasure P
            (fun j ω => riskIid L Kk lcov P₀ (poolLaw (fun i : Fin (n j) => Zs i ω₀) (wh j ω))) atTop
            (fun _ => Rstar)

/-- otfd C `prop:metric-uniform-localization`, main display and (i), entropic penalty: there is a deterministic
schedule `ε_{X,n} ↓ 0` such that, for the (unique) empirical self-potentials, almost surely for every `j`,
`sup_{(Λ,s) ∈ 𝒮_j} sup_{x ∈ D_X} W₁(P̂^E_{K,n,x}[Λ, s ε_{X,n}], P_{K,x}) → 0` and `inf n_eff(x)/log n → ∞`
(`n_eff = (Σ_i w_i²)⁻¹`, the infimum over `𝒮_j × D_X`); and (i) for any metrics `Λ̂_n` and scales `ŝ_n`
(any functions of the data, possibly of the localization sample) that almost surely eventually stay in a compact
subset of `GL_q × (0,∞)`, or converge almost surely to a (random) limit in `GL_q × (0,∞)`,
`sup_{x ∈ D_X} W₁(P̂^E_{K,n,x}[Λ̂_n, ŝ_n ε_{X,n}], P_{K,x}) → 0` and `inf_x n_eff(x)/log n → ∞` almost surely. -/
def metric_uniform_localization : Prop :=
  ∀ (q K : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (PX : Measure (Euc q))
    [IsProbabilityMeasure PX] (κ : Kernel (Euc q) (Euc K)) [IsMarkovKernel κ] (R : ℝ)
    (Xs : ℕ → Ω → Euc q) (Zs : ℕ → Ω → Euc K),
    LocModel P PX κ R Xs Zs →
    ∃ εX : ℕ → ℝ, (∀ n, 0 < εX n) ∧ Antitone εX ∧ Tendsto εX atTop (𝓝 0) ∧
      ∀ Fn : (n : ℕ) → GLq q → ℝ → Ω → Fin n → ℝ,
        (∀ n Λ ε ω, 0 < ε → IsEmpSelfPot Λ ε (fun i : Fin n => Xs i ω) (Fn n Λ ε ω)) →
        (∀ᵐ ω ∂P, ∀ j : ℕ,
          Tendsto (fun n => ⨆ p ∈ sSet q j, ⨆ x ∈ PX.support,
            TauCeti.wassersteinEDist 1 (locEmp p.1 (p.2 * εX n) (fun i : Fin n => Xs i ω) (fun i => Zs i ω)
              (Fn n p.1 (p.2 * εX n) ω) x) (κ x)) atTop (𝓝 0) ∧
          ∀ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ p ∈ sSet q j, ∀ x ∈ PX.support,
            C * Real.log (n : ℝ) ≤
              (∑ i, entW p.1 (p.2 * εX n) (fun i : Fin n => Xs i ω) (Fn n p.1 (p.2 * εX n) ω) x i ^ 2)⁻¹) ∧
        ∀ (Λh : ℕ → Ω → GLq q) (sh : ℕ → Ω → ℝ),
          ((∀ᵐ ω ∂P, ∃ Cs : Set (GLq q × ℝ), IsCompact Cs ∧ (∀ p ∈ Cs, 0 < p.2) ∧
              ∀ᶠ n in atTop, (Λh n ω, sh n ω) ∈ Cs) ∨
            (∀ᵐ ω ∂P, ∃ (Λ : GLq q) (s : ℝ), 0 < s ∧ Tendsto (fun n => (Λh n ω, sh n ω)) atTop (𝓝 (Λ, s)))) →
          ∀ᵐ ω ∂P, Tendsto (fun n => ⨆ x ∈ PX.support,
            TauCeti.wassersteinEDist 1 (locEmp (Λh n ω) (sh n ω * εX n) (fun i : Fin n => Xs i ω)
              (fun i => Zs i ω) (Fn n (Λh n ω) (sh n ω * εX n) ω) x) (κ x)) atTop (𝓝 0) ∧
            ∀ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ x ∈ PX.support,
              C * Real.log (n : ℝ) ≤ (∑ i, entW (Λh n ω) (sh n ω * εX n) (fun i : Fin n => Xs i ω)
                (Fn n (Λh n ω) (sh n ω * εX n) ω) x i ^ 2)⁻¹

/-- otfd C `prop:metric-uniform-localization` (iii), entropic penalty: for a fixed strength `ε_X > 0` and
`(Λ̂_n, ŝ_n) → (Λ, s)` almost surely in `GL_q × (0,∞)` (random limit),
`sup_{x ∈ D_X} W₁(P̂^E_{K,n,x}[Λ̂_n, ŝ_n ε_X], P^E_{K,x}[Λ, s ε_X]) → 0` almost surely, `P^E_{K,x}[Λ, ε]` the
population smoothed law for the metric `Λ` (any population self-potentials). -/
def metric_fixed_strength : Prop :=
  ∀ (q K : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (PX : Measure (Euc q))
    [IsProbabilityMeasure PX] (κ : Kernel (Euc q) (Euc K)) [IsMarkovKernel κ] (R : ℝ)
    (Xs : ℕ → Ω → Euc q) (Zs : ℕ → Ω → Euc K),
    LocModel P PX κ R Xs Zs → ∀ ε₀ : ℝ, 0 < ε₀ →
      ∀ Fn : (n : ℕ) → GLq q → ℝ → Ω → Fin n → ℝ,
        (∀ n Λ ε ω, 0 < ε → IsEmpSelfPot Λ ε (fun i : Fin n => Xs i ω) (Fn n Λ ε ω)) →
      ∀ Fp : GLq q → ℝ → Euc q → ℝ, (∀ Λ ε, 0 < ε → IsPopSelfPot PX Λ ε (Fp Λ ε)) →
      ∀ (Λh : ℕ → Ω → GLq q) (sh : ℕ → Ω → ℝ) (Λ : Ω → GLq q) (s : Ω → ℝ),
        (∀ᵐ ω ∂P, 0 < s ω ∧ Tendsto (fun n => (Λh n ω, sh n ω)) atTop (𝓝 (Λ ω, s ω))) →
        ∀ᵐ ω ∂P, Tendsto (fun n => ⨆ x ∈ PX.support,
          TauCeti.wassersteinEDist 1 (locEmp (Λh n ω) (sh n ω * ε₀) (fun i : Fin n => Xs i ω) (fun i => Zs i ω)
            (Fn n (Λh n ω) (sh n ω * ε₀) ω) x) (locPop PX κ (Λ ω) (s ω * ε₀) (Fp (Λ ω) (s ω * ε₀)) x)) atTop (𝓝 0)

/-- The reduction step of the proof (`lem:self-potentials` for the metric cost `‖Λ(x − y)‖²` on raw covariates):
for every `Λ ∈ GL_q` and `ε > 0`, the population self-potential on a compact `D_X = supp P_X` exists and is unique
on `D_X`, and the empirical self-potential of any sample exists and is unique. -/
def metric_selfpot_exists_unique : Prop :=
  ∀ (q : ℕ) (PX : Measure (Euc q)) [IsProbabilityMeasure PX] (Λ : GLq q) (ε : ℝ), IsCompact PX.support → 0 < ε →
    ((∃ F, IsPopSelfPot PX Λ ε F) ∧
      ∀ F G, IsPopSelfPot PX Λ ε F → IsPopSelfPot PX Λ ε G → EqOn F G PX.support) ∧
    ∀ (n : ℕ) (xs : Fin n → Euc q), (∃ F, IsEmpSelfPot Λ ε xs F) ∧
      ∀ F G, IsEmpSelfPot Λ ε xs F → IsEmpSelfPot Λ ε xs G → F = G

end Claims

end StatFormal.Wave26b
