import StatFormal.Archive.Wave19b.Statements
import StatFormal.Archive.RobustEquality.Coverage.Statements
import StatFormal.Archive.Wave7b.Statements
import StatFormal.Archive.Wave16a.Statements
import Mathlib.Analysis.Matrix.Order
import Mathlib.Probability.CDF

/-!
# FROZEN STATEMENTS — wave 20b (QUEUE rows 218–224): otfd A `prop:lift-dual`; robust equality JASA `lem:cert-betting`,
# `prop:cs-tight`, `thm:ep-limitinf`, `prop:ep-blur`, `prop:drift`; ICL `lem:e-normalizers`

Sources (verbatim in `lean-formalisation/inventory/extracted/{otfd-A_sieves,robust-equality-jasa,context-distribution-icl}.md`;
current text after the 2026-10-13/14/15 corrections; JASA paths under `robust-equality-outcomes-under-distribution-shift/jasa/`):
* otfd A `prop:lift-dual` (`otfd/papers/A_sieves/supplement.tex:5415-5435`, proof `:4820-4848`), with the section's
  standing conventions (`:4798-4806`: references centred, uncorrelated coordinates, `F = ∇ψ` pushes `P_T` to `μ_T`),
  `def:lift` and `sec:lift` (`main.tex:1118-1170`), and the frozen `IsSepTail` of `prop:lift-consistency` (Wave 16a).
* JASA `lem:cert-betting` (`supp_calibration.tex:521-527`, proof `:529-532`).
* JASA `prop:cs-tight` (`supp_common_shift.tex:258-265`, proof `:267-271`), with the Wasserstein differential sets and
  `eq:cs-w2` (`:240-250`).
* JASA `thm:ep-limitinf` (`supp_eps.tex:247-261`, proof `:263-269`) and `prop:ep-blur` (`:300-312`, proof `:314-321`),
  with the file-header notation (`:6-17`: `R_ε`, floor kernel `K^ε_{x₀}`, `f_h`, `T_ε`) and `Ψ_ε` (`:297-298`).
* JASA `prop:drift` (`supp_proofs.tex:709-724`, proof `:726-735`), with `lem:convex` (`:107`) and
  `thm:coverage-general` (`:524`).
* ICL `lem:e-normalizers` (`context-distribution-ICL/paper/v3/supp/proofs_score.tex:74-77`, proof `:79-87`), with
  `as:compact`, `as:score` (`:14-23`) and the notation `c_θ, c_{θ,n}, μ_θ, μ_{θ,n}` (`:51-66`).
Imports the frozen `Wave19b` (`ballEps`, `floorW`, `gibbsK`, `gibbsMix`, `worstDisp`, `centreW`, `floorZero`; through it
`RobustEquality/{Tax,Strong,Certificate,SemidualStrong}`: `Wdisc`, `ballN`, `OTdisc`, `Setting`, `floorRef`, `Tref1`,
`klRef`), `RobustEquality/Coverage` (`empMeasure`), `Wave7b` (`CostSetting`) and `Wave16a` (`IsSepTail`) statements,
not copied. `StatFormal.Distances.tvDist` comes from the `Foundations/Distances/TV` library file, imported only through
the frozen `SemidualStrong` statements. Mathlib (`Analysis.Matrix.Order` for `CFC.sqrt` on matrices, `Probability.CDF`)
and Tau Ceti (`wassersteinEDist`, `Measure.quantile`) otherwise.

Covered:
* `prop:lift-dual`: (i) `lift_dual_conj_split` (`(φ_K ⊕ φ_⊥)* = φ_K* ⊕ φ_⊥*`), `lift_dual_conj_sep` (`(Σ_k φ_k)* =
  Σ_k φ_k*`), `lift_dual_J_split` (`J` splits into the head and tail brackets), `lift_dual_push` (`G_{U_k}^{-1} ∘ G_{X_k}`
  pushes each atomless tail marginal of `P_T` onto that of `μ_T`); (ii) `lift_dual_ii` (conjugate of `½λ(·−m)²`, unique
  minimiser `m = E X_k`, `λ = (E U_k²/Var X_k)^{1/2}`); (iii) `lift_dual_iii` (`Λ*` positive definite, `Λ*Σ_XΛ* = Σ_U`,
  unique minimiser of the reduced objective), `lift_dual_iii_diag` (diagonal covariances give the diagonal `Λ` of (ii)).
* `lem:cert-betting`: `cert_betting` (`E_P g ≤ UCB_B` on an event of probability `≥ 1 − δ'`).
* `prop:cs-tight`: `cs_tight` (the move is feasible, realises the moved laws, and attains `Δ_θ + σ_0 + σ_1` under the
  proviso), `cs_tight_exact` (`eq:cs-w2` is then exact at fixed `θ`), `cs_tight_K_false` (refutation of the `𝒫(K)` reading).
* `thm:ep-limitinf`: `ep_limitinf_kl`, `ep_limitinf_tv`, `ep_limitinf_mono`, `ep_limitinf_collapse`, `ep_limitinf_disp`
  (finiteness and the `(·)^{1/4}` rate), `ep_limitinf_disp_lim`, `ep_limitinf_cert`.
* `prop:ep-blur`: (i) `ep_blur_i`; (ii) `ep_blur_ii_ball`, `ep_blur_ii_disp`, `ep_blur_ii_couple`; (iii) `ep_blur_iii`.
* `prop:drift`: (i) `drift_lookback`; (ii) `drift_forecast`.
* `lem:e-normalizers`: `e_normalizers` (both uniform limits, plus finiteness of the relative entropies).

Not covered (declared):
* lift-dual (i): that the 1-D Brenier potential minimises each bracket (1-D Kantorovich duality; only the split and the
  pushforward of its derivative are stated); (iii): the minimisation over `m` jointly with `Λ` (the reduced objective at
  `m = E X_⊥`, `E U_⊥ = 0`, is stated), and the sentence that `Σ_X ≻ 0` is implied by the existence of `F` (hypothesis
  here); "nothing is gained from off-diagonal tail terms" beyond `lift_dual_iii_diag`.
* cert-betting: the interval property of the confidence set and the independence of `f̂` from `B` (the lemma is stated
  conditionally on the fitting fold, `g = g_{f̂}` fixed); the citation.
* cs-tight: "in general its value is a lower bound on `F_Θ(h)`" (only the feasible pair is stated; `F_Θ` is not
  defined); the equality-case remark (alignment condition of `prop:tight`).
* ep-limitinf: the status paragraph (information budget, `Q(A) ≤ (k_ε + log 2)/log(1/ν(A))`, density lower bound).
* ep-blur (i): "hence every certificate on single-reference sets is at least `(Δ + √𝖡_{ε,0} + √𝖡_{ε,1})²`"; (iii): "a
  single point when the nearest point is unique"; the status paragraph (Fisher-information heuristic).
* drift (i): "may be replaced by any deviation term of `thm:coverage` with `V = 1`"; (iii) monitoring (prose).

Encodings (to be checked by the critic):
* lift-dual: conjugates `conjE`/`conj1` are `⨆` in `EReal` (`+∞` allowed, never `⊥`); `ℝ^K ⊕ ℝ^{T−K}` is `α ⊕ β → ℝ`;
  `J` integrates `toReal` of the conjugates only under the hypotheses that they are finite a.e. and integrable; the
  rearrangement is Tau Ceti's quantile of `μ_k` after Mathlib's `cdf` of `P_k` (`rearrTail`; tail coordinates `k ≥ K`,
  0-indexed); (ii) is one coordinate, `ν = L(X_k)`, `ρ = L(U_k)` with `E U_k = 0` (standing, `supplement.tex:4801`),
  `Var X_k > 0`, `E U_k² > 0`; (iii) `Σ_X = A ≻ 0`, `Σ_U = B ≻ 0`, `Λ* = gelbrich A B` with `CFC.sqrt` (Loewner order,
  `MatrixOrder`), objective `½ tr(ΛΣ_X) + ½ tr(Λ⁻¹Σ_U)` (`gaussObj`) over positive definite `Λ`.
* cert-betting: held-out `Y_j` i.i.d. `P` on any measurable space (`Fin m`, 0-indexed), `ĝ = g` fixed measurable with
  `ℓ ≤ g ≤ ū`, `ℓ < ū`; bets `β_j = bet j (Y_1,…,Y_m)` measurable, in `[0, 0.9]`, depending only on `Y_i`, `i < j`
  (`Predictable`); `𝒦_t` is `kBet`, the confidence set `confSet` (`∀ t, 𝒦_t < 1/δ'`); `E_P g ≤ UCB_B` is encoded without
  `sInf` junk as: `E Z` lies in the set, and `E_P g ≤ ū − (ū − ℓ)b` for every lower bound `b` (this is `≤ UCB_B` when the
  set is bounded below, and vacuous-free otherwise); `δ' > 0` (any `δ'`; `δ' ≥ 1` is trivial).
* cs-tight: `ℝ^d = EuclideanSpace ℝ (Fin d)`, `h = ⟨w,·⟩ + b`, `w ≠ 0`; the centres `T_θ#P̂_s` are any laws `P_s` with
  finite second moments; `q_s` Tau Ceti's quantile of `h#P_s` (`predQ`); `Δ_θ = deltaW` (finite, `> 0` assumed, so `d/‖d‖`
  is genuine); `‖d‖_{L²} = Δ_θ` (1-D quantile formula) so `σ_s d/‖d‖ = κ_s d` with `κ_0 = σ_0/Δ`, `κ_1 = −σ_1/Δ`
  (`movedQ`); "the quantile functions become `q̃_s`" is `h#Q_s = law of q̃_s(U)`, `U ∼ Unif(0,1)` (`unifIoo`); feasibility
  `W₂²(P_s,Q_s) ≤ β_s` in `ℝ≥0∞`; the proviso is `MonotoneOn` on `(0,1)`; populations in `𝒫(ℝ^d)`.
* ep-limitinf/ep-blur: weighted centre `Σ_i a_i δ_i` with costs `c_i` (frozen `Wdisc`, `OTdisc`, `ballEps`, `floorW`);
  `c` any bounded measurable `c ≥ 0` (paper: `|x−y|²` on compact `K`); `E_{P̂⊗ν}c = meanCost`; `TV` is `tvDist`
  (`sup_A |Q(A) − ν(A)|`); "bounded rule" with `osc_K h ≤ D` is `∀ x y, |h x − h y| ≤ D`; `F_ε` is the frozen
  `worstDisp` over the two balls at `R_ε + β_s`; the optimised groupwise term is `Tref1` at `r = floorRef + β`
  (uniform centre, as `eq:T`), `𝖡_ε = blurB` with `K^ε_{x_i} = gibbsK`; `inf_{λ>0}` is `⨅` in `EReal`; (iii): the
  `ε = 0`, `β = 0` groupwise term is the primal value over kernels `Γ_i` carried by `S_ν = ν.support` with
  `Σ a_i E_{Γ_i} dist²(x_i,·) ≤ R_0` (`floorZero`), `K` compact metric, `h` continuous; nearest points `nearest`.
* drift: `P_{t−1}, P_t, P_{t+1} = P₀, P₁, P₂`; samples `x ∼ P₀^n`, `y ∼ P₁^n` independent (product measure on
  `(Fin n → K)²`); `P̂ = n⁻¹Σδ` (`empMeasure`, labelled atoms); `F_t = OTdisc` of the uniform centre `x` against `P̂_t`;
  `𝓑^{𝒫(K)}` is the frozen free ball `ballN {probability laws}`; `0 ≤ c ≤ B_c` measurable (`CostSetting`); `D_t, D_{t+1}`
  are Bochner integrals of `toReal OT` and their integrability is part of the conclusion (no junk); `0 < a < 1`.
* e-normalizers: pool `Z_0, Z_1, …` one i.i.d. `P₀` sequence (nested samples), `P_n` its first `n+1` points (`empN`,
  `empAvg`); `μ_{θ,n}` weights `s_θ(Z_j)/Σ_i s_θ(Z_i)` (`ENNReal.ofReal` of a positive real), `μ_θ = (s_θ/c_θ)P₀`
  (`withDensity`); `KL` is Mathlib's `klDiv` (`ℝ≥0∞`), finiteness is a conclusion and the limits are of `toReal`;
  `sup_θ |·| → 0` is `TendstoUniformly`; `as:score` with `0 < s₋ ≤ s ≤ s₊`, `s` jointly continuous; `Θ, 𝒵` compact metric.

Critic notes:
* All 26 claims are proved in `Wave20b/Route{LiftDual,CertBetting,CsTight,EpBlur,EpLimitInf,Drift,ENormalizers}.lean`
  (axioms: propext, Classical.choice, Quot.sound). Routes use the untrusted Foundations libraries
  (`Distances/W2TV`, `SemiDiscrete/{Convex,RandomFolds}`, `Concentration/EmpiricalProcess`, `Tax/Tax`), Tau Ceti
  (`Gluing`, `Rearrangement`, `Pushforward`, KL change of reference) and the routes of Wave 19b/7b — routes only.
* Suspected paper defect (S3), `prop:cs-tight`: with populations in `𝒫(K)` (the paper's convention, `K` compact) moving
  mass along `w` can leave `K`, and the printed claim fails: `cs_tight_K_false` (`d = 1`, `K = [0,1]`, `P_0 = δ_1`,
  `P_1 = δ_0`, `β_s = ¼`; both moved quantile functions are constant, but every pair in `𝒫(K)` has `W₂² ≤ 1 < 4`). The
  statement holds over `𝒫(ℝ^d)` (`cs_tight`, `cs_tight_exact`), i.e. when `K` contains the moved supports.
* lift-dual (iii) also needs `Σ_U ≻ 0` for a positive definite minimiser (true for the ball and cubic references).
* No other statement was found false. Generalisations: ep-limitinf/ep-blur hold for any bounded measurable cost
  `c ≥ 0` (ep-blur (i)–(ii): any bounded cost, any finite `ν ≠ 0`); cs-tight for any centres with second moments.
* Critic (2026-10-15): ACCEPT-WITH-NOTE, all 26 TRUE. lift-dual: `E U_k = 0` is stated in A's appendix
  (supp:4801, "both references are centred") and needed; `Σ_U ≻ 0` holds in the setting (uncorrelated coordinates
  with positive variances) and is genuinely needed for general `B`; `Σ_X ≻ 0` matches DEFECTS #33. cert-betting: the
  fold-conditional measurable-event form implies the paper's unconditional statement (Fubini). cs-tight: the
  counterexample is fair — JASA `prop:cs-tight` (and the sentence before `eq:cs-w2`) needs `K_Θ` to contain the moved
  supports (or `Q ∈ 𝒫(ℝ^d)`): `K = [0,1]`, `P₀ = δ₁`, `P₁ = δ₀`, `β_s = ¼` gives `W₂² ≤ 1 < 4` (S3, DEFECTS #68).
  ep-limitinf/ep-blur: any `D ≥ osc_K(h)`, bounded measurable costs and finite `ν ≠ 0` are genuine generalisations.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/
set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TauCeti
open scoped ENNReal InnerProductSpace RealInnerProductSpace MatrixOrder

namespace StatFormal.Wave20b

open StatFormal.RobustEquality StatFormal.RobustEquality.Semidual StatFormal.RobustEquality.SemidualStrong
open StatFormal.Wave19b

/-! ### JASA `thm:ep-limitinf`, `prop:ep-blur` -/

section Eps
variable {K : Type*} [MeasurableSpace K] {k : ℕ}

/-- The standing hypotheses on a weighted centre and its costs, without `ε`: `a_i > 0`, `Σ a_i = 1`,
each `c_i` measurable, bounded and nonnegative (paper: `c_i = |x_i − ·|²` on a compact `K`). -/
def CentreHyp (a : Fin k → ℝ) (c : Fin k → K → ℝ) : Prop :=
  (∀ i, 0 < a i) ∧ ∑ i, a i = 1 ∧ (∀ i, Measurable (c i)) ∧ (∃ B, ∀ i z, |c i z| ≤ B) ∧
    ∀ i z, 0 ≤ c i z

/-- `E_{P̂⊗ν} c = Σ_i a_i ∫ c_i dν`. -/
def meanCost (a : Fin k → ℝ) (c : Fin k → K → ℝ) (ν : Measure K) : ℝ :=
  ∑ i, a i * ∫ z, c i z ∂ν

/-- The blur `𝖡_ε(h) = E_{x₀∼P̂} E_{K^ε_{x₀}} f_h(x₀,·)` for the weighted centre `Σ_i a_i δ_{x_i}`, with the
floor kernel `K^ε_{x_i} = gibbsK` (density `e^{−c(x_i,·)/ε}/∫e^{−c(x_i,·)/ε}dν` w.r.t. `ν`). -/
def blurB (ε : ℝ) (a : Fin k → ℝ) (x : Fin k → K) (c : K → K → ℝ) (h : K → ℝ) (ν : Measure K) : ℝ :=
  ∑ i, a i * ∫ z, (h z - h (x i)) ^ 2 ∂(gibbsK ε (fun i => c (x i)) ν i)

/-- The nearest points `{y ∈ S : dist(x, y) = dist(x, S)}`. -/
def nearest {K : Type*} [MetricSpace K] (x : K) (S : Set K) : Set K :=
  {y | y ∈ S ∧ dist x y = Metric.infDist x S}

end Eps


/-! ### JASA `lem:cert-betting` -/

section Betting

/-- The capital process `𝒦_t(t₀) = Π_{j ≤ t} (1 + β_j (Z_j − t₀))`, `t = 1, …, m` (0-indexed `t : Fin m`). -/
def kBet {m : ℕ} (β Z : Fin m → ℝ) (t0 : ℝ) (t : Fin m) : ℝ :=
  ∏ j ∈ Finset.Iic t, (1 + β j * (Z j - t0))

/-- The betting confidence set `{t₀ : max_t 𝒦_t(t₀) < 1/δ'}`. -/
def confSet {m : ℕ} (β Z : Fin m → ℝ) (δ : ℝ) : Set ℝ :=
  {t0 | ∀ t, kBet β Z t0 t < 1 / δ}

/-- Predictable bets: `β_j` is a function of the held-out points `Y_i`, `i < j`, only. -/
def Predictable {Y : Type*} {m : ℕ} (bet : Fin m → (Fin m → Y) → ℝ) : Prop :=
  ∀ j y y', (∀ i, i < j → y i = y' i) → bet j y = bet j y'

end Betting


/-! ### ICL `lem:e-normalizers` -/

section Normalizers
variable {Θ 𝒵 Ω : Type*} [MeasurableSpace 𝒵]

/-- The empirical average `P_n f = (n+1)⁻¹ Σ_{j ≤ n} f(Z_j)` of the first `n + 1` pool points. -/
def empAvg (Zs : ℕ → Ω → 𝒵) (n : ℕ) (f : 𝒵 → ℝ) (ω : Ω) : ℝ :=
  ((n : ℝ) + 1)⁻¹ * ∑ j ∈ Finset.range (n + 1), f (Zs j ω)

/-- The empirical measure `P_n = (n+1)⁻¹ Σ_{j ≤ n} δ_{Z_j}`. -/
def empN (Zs : ℕ → Ω → 𝒵) (n : ℕ) (ω : Ω) : Measure 𝒵 :=
  ((n : ℝ≥0∞) + 1)⁻¹ • ∑ j ∈ Finset.range (n + 1), Measure.dirac (Zs j ω)

/-- `μ_{θ,n} = Σ_j w^{(n)}_j(θ) δ_{Z_j}`, `w^{(n)}_j(θ) = s_θ(Z_j) / Σ_i s_θ(Z_i)`. -/
def muEmp (s : Θ → 𝒵 → ℝ) (θ : Θ) (Zs : ℕ → Ω → 𝒵) (n : ℕ) (ω : Ω) : Measure 𝒵 :=
  ∑ j ∈ Finset.range (n + 1),
    ENNReal.ofReal (s θ (Zs j ω) / ∑ i ∈ Finset.range (n + 1), s θ (Zs i ω)) • Measure.dirac (Zs j ω)

/-- `μ_θ = g_θ P₀`, `g_θ = s_θ / c_θ`, `c_θ = P₀ s_θ`. -/
def muPop (s : Θ → 𝒵 → ℝ) (θ : Θ) (P0 : Measure 𝒵) : Measure 𝒵 :=
  P0.withDensity fun z => ENNReal.ofReal (s θ z / ∫ z', s θ z' ∂P0)

end Normalizers


/-! ### JASA `prop:cs-tight` -/

section CsTight

/-- The uniform law on `(0,1)`, the domain of quantile functions. -/
def unifIoo : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)

/-- The linear rule `h(x) = ⟨w, x⟩ + b`. -/
def linRule {d : ℕ} (w : EuclideanSpace ℝ (Fin d)) (b : ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ := ⟪w, x⟫ + b

/-- The quantile function `q_s` of the prediction law `h#P_s` (Tau Ceti's left-continuous quantile). -/
def predQ {d : ℕ} (w : EuclideanSpace ℝ (Fin d)) (b : ℝ) (P : Measure (EuclideanSpace ℝ (Fin d))) : ℝ → ℝ :=
  (P.map (linRule w b)).quantile

/-- `Δ_θ = W₂(h#P_0, h#P_1)` (real; finite under second moments). -/
def deltaW {d : ℕ} (w : EuclideanSpace ℝ (Fin d)) (b : ℝ) (P₀ P₁ : Measure (EuclideanSpace ℝ (Fin d))) : ℝ :=
  (wassersteinEDist 2 (P₀.map (linRule w b)) (P₁.map (linRule w b))).toReal

/-- The moved quantile function `q + κ (q_0 − q_1)`: `κ = σ_0/‖d‖` for group 0, `κ = −σ_1/‖d‖` for group 1, with
`‖d‖_{L²} = Δ_θ` (one-dimensional quantile formula). -/
def movedQ (q q₀ q₁ : ℝ → ℝ) (κ : ℝ) : ℝ → ℝ := fun t => q t + κ * (q₀ t - q₁ t)

/-- The printed tightness claim with populations in `𝒫(K)` (the paper's convention): for centres carried by a compact
`K`, if both moved quantile functions are nondecreasing, the supremum of `W₂²(h#Q_0, h#Q_1)` over
`Q_s ∈ 𝒫(K)` with `W₂²(P_s, Q_s) ≤ β_s` is attained and equals `(Δ_θ + σ_0 + σ_1)²`. -/
def CsTightOnK : Prop :=
  ∀ (d : ℕ) (w : EuclideanSpace ℝ (Fin d)) (b β₀ β₁ : ℝ) (K : Set (EuclideanSpace ℝ (Fin d)))
    (P₀ P₁ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁],
    IsCompact K → P₀ Kᶜ = 0 → P₁ Kᶜ = 0 → w ≠ 0 → 0 ≤ β₀ → 0 ≤ β₁ → 0 < deltaW w b P₀ P₁ →
    MonotoneOn (movedQ (predQ w b P₀) (predQ w b P₀) (predQ w b P₁) (‖w‖ * √β₀ / deltaW w b P₀ P₁)) (Ioo 0 1) →
    MonotoneOn (movedQ (predQ w b P₁) (predQ w b P₀) (predQ w b P₁) (-(‖w‖ * √β₁) / deltaW w b P₀ P₁)) (Ioo 0 1) →
      IsGreatest {v | ∃ Q₀ Q₁ : Measure (EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure Q₀ ∧
          IsProbabilityMeasure Q₁ ∧ Q₀ Kᶜ = 0 ∧ Q₁ Kᶜ = 0 ∧
          wassersteinEDist 2 P₀ Q₀ ^ 2 ≤ ENNReal.ofReal β₀ ∧ wassersteinEDist 2 P₁ Q₁ ^ 2 ≤ ENNReal.ofReal β₁ ∧
          v = wassersteinEDist 2 (Q₀.map (linRule w b)) (Q₁.map (linRule w b)) ^ 2}
        (ENNReal.ofReal ((deltaW w b P₀ P₁ + ‖w‖ * √β₀ + ‖w‖ * √β₁) ^ 2))

end CsTight


/-! ### otfd A `prop:lift-dual` -/

section LiftDual

/-- The Legendre–Fenchel conjugate `φ*(u) = sup_x {⟨x, u⟩ − φ(x)}` on `ℝ^ι`, in `EReal` (`+∞` allowed). -/
def conjE {ι : Type*} [Fintype ι] (φ : (ι → ℝ) → ℝ) (u : ι → ℝ) : EReal :=
  ⨆ x : ι → ℝ, ((∑ i, x i * u i - φ x : ℝ) : EReal)

/-- The one-dimensional conjugate `φ*(u) = sup_x {x u − φ(x)}`, in `EReal`. -/
def conj1 (φ : ℝ → ℝ) (u : ℝ) : EReal := ⨆ x : ℝ, ((x * u - φ x : ℝ) : EReal)

/-- The one-dimensional semi-dual `J(φ) = E φ(X) + E φ*(U)` (applied only where `φ*` is finite). -/
def semiDual1 (φ : ℝ → ℝ) (ν ρ : Measure ℝ) : ℝ := ∫ x, φ x ∂ν + ∫ u, (conj1 φ u).toReal ∂ρ

/-- The tail map `t_k = G_{U_k}^{-1} ∘ G_{X_k}` of `prop:lift-dual`(i) (Tau Ceti's quantile, Mathlib's `cdf`). -/
def rearrTail {T : ℕ} (P μ : Measure (Fin T → ℝ)) (k : Fin T) (y : ℝ) : ℝ :=
  (μ.map fun u => u k).quantile (cdf (P.map fun x => x k) y)

/-- The diagonal quadratic tail potential `φ_k(x) = ½ λ (x − m)²`. -/
def quadPot (lam m : ℝ) (x : ℝ) : ℝ := lam / 2 * (x - m) ^ 2

/-- The Gaussian transport (Gelbrich) matrix `Σ_X^{-1/2} (Σ_X^{1/2} Σ_U Σ_X^{1/2})^{1/2} Σ_X^{-1/2}` (CFC square root). -/
def gelbrich {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℝ) : Matrix n n ℝ :=
  (CFC.sqrt A)⁻¹ * CFC.sqrt (CFC.sqrt A * B * CFC.sqrt A) * (CFC.sqrt A)⁻¹

/-- The reduced full-quadratic tail objective `½ tr(Λ Σ_X) + ½ tr(Λ⁻¹ Σ_U)`. -/
def gaussObj {n : Type*} [Fintype n] [DecidableEq n] (A B L : Matrix n n ℝ) : ℝ :=
  (L * A).trace / 2 + (L⁻¹ * B).trace / 2

end LiftDual

namespace Claims

local notation "Wdisc" => StatFormal.RobustEquality.Tax.Wdisc
open StatFormal.RobustEquality.Certificate StatFormal.RobustEquality.Strong

/-! #### JASA `thm:ep-limitinf` -/

/-- KL budget: every `Q ∈ 𝓑^ν_ε(R_ε + β)` has `KL(Q‖ν) ≤ k_ε = (R_ε + β − OT_ε(P̂,Q))/ε ≤ (E_{P̂⊗ν}c + β)/ε`. -/
def ep_limitinf_kl : Prop :=
  ∀ (K : Type) [MetricSpace K] [MeasurableSpace K] (k : ℕ) (ε β : ℝ) (a : Fin k → ℝ)
    (c : Fin k → K → ℝ) (ν Q : Measure K) [IsProbabilityMeasure ν],
    Setting ε a c → (∀ i z, 0 ≤ c i z) → 0 ≤ β →
    Q ∈ ballEps ε a c ν (floorW ε a c ν + β) →
      ∃ t : ℝ, OTdisc ε a c Q = (t : EReal) ∧
        klRef Q ν ≤ (((floorW ε a c ν + β - t) / ε : ℝ) : EReal) ∧
        (floorW ε a c ν + β - t) / ε ≤ (meanCost a c ν + β) / ε

/-- Pinsker: every `Q ∈ 𝓑^ν_ε(R_ε + β)` has `TV(Q, ν) ≤ √((E_{P̂⊗ν}c + β)/(2ε))`. -/
def ep_limitinf_tv : Prop :=
  ∀ (K : Type) [MetricSpace K] [MeasurableSpace K] (k : ℕ) (ε β : ℝ) (a : Fin k → ℝ)
    (c : Fin k → K → ℝ) (ν Q : Measure K) [IsProbabilityMeasure ν],
    Setting ε a c → (∀ i z, 0 ≤ c i z) → 0 ≤ β →
    Q ∈ ballEps ε a c ν (floorW ε a c ν + β) →
      StatFormal.Distances.tvDist Q ν ≤ √((meanCost a c ν + β) / (2 * ε))

/-- `ε ↦ (R_ε + β)/ε` is nonincreasing on `(0, ∞)`. -/
def ep_limitinf_mono : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k : ℕ) (β : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (ν : Measure K) [IsProbabilityMeasure ν],
    CentreHyp a c → 0 ≤ β → AntitoneOn (fun ε => (floorW ε a c ν + β) / ε) (Ioi 0)

/-- The sets collapse to `{ν}` in total variation as `ε → ∞`. -/
def ep_limitinf_collapse : Prop :=
  ∀ (K : Type) [MetricSpace K] [MeasurableSpace K] (k : ℕ) (β : ℝ) (a : Fin k → ℝ)
    (c : Fin k → K → ℝ) (ν : Measure K) [IsProbabilityMeasure ν],
    CentreHyp a c → 0 ≤ β →
      ∀ η, 0 < η → ∀ᶠ ε in atTop, ∀ Q ∈ ballEps ε a c ν (floorW ε a c ν + β),
        StatFormal.Distances.tvDist Q ν ≤ η

/-- For a bounded rule (`|h(x) − h(y)| ≤ D`, i.e. `D ≥ osc_K h`), the worst-case disparity `F_ε` is finite and
`|F_ε^{1/2} − W₂(h#ν₀, h#ν₁)| ≤ D Σ_s ((E_{P̂_s⊗ν_s}c + β_s)/(2ε))^{1/4}`. -/
def ep_limitinf_disp : Prop :=
  ∀ (K : Type) [MetricSpace K] [MeasurableSpace K] [BorelSpace K] (k₀ k₁ : ℕ) (ε β₀ β₁ D : ℝ)
    (a₀ : Fin k₀ → ℝ) (a₁ : Fin k₁ → ℝ) (c₀ : Fin k₀ → K → ℝ) (c₁ : Fin k₁ → K → ℝ)
    (ν₀ ν₁ : Measure K) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁] (h : K → ℝ),
    0 < ε → CentreHyp a₀ c₀ → CentreHyp a₁ c₁ → 0 ≤ β₀ → 0 ≤ β₁ → Measurable h →
    (∀ x y, |h x - h y| ≤ D) →
      wassersteinEDist 2 (ν₀.map h) (ν₁.map h) ≠ ⊤ ∧
      worstDisp (ballEps ε a₀ c₀ ν₀ (floorW ε a₀ c₀ ν₀ + β₀))
          (ballEps ε a₁ c₁ ν₁ (floorW ε a₁ c₁ ν₁ + β₁)) h ≠ ⊤ ∧
      |√(worstDisp (ballEps ε a₀ c₀ ν₀ (floorW ε a₀ c₀ ν₀ + β₀))
            (ballEps ε a₁ c₁ ν₁ (floorW ε a₁ c₁ ν₁ + β₁)) h).toReal -
          (wassersteinEDist 2 (ν₀.map h) (ν₁.map h)).toReal| ≤
        D * (((meanCost a₀ c₀ ν₀ + β₀) / (2 * ε)) ^ (1 / 4 : ℝ) +
          ((meanCost a₁ c₁ ν₁ + β₁) / (2 * ε)) ^ (1 / 4 : ℝ))

/-- The worst-case disparity converges: `F_ε → W₂²(h#ν₀, h#ν₁)` as `ε → ∞` (bounded measurable rule). -/
def ep_limitinf_disp_lim : Prop :=
  ∀ (K : Type) [MetricSpace K] [MeasurableSpace K] [BorelSpace K] (k₀ k₁ : ℕ) (β₀ β₁ : ℝ)
    (a₀ : Fin k₀ → ℝ) (a₁ : Fin k₁ → ℝ) (c₀ : Fin k₀ → K → ℝ) (c₁ : Fin k₁ → K → ℝ)
    (ν₀ ν₁ : Measure K) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁] (h : K → ℝ),
    CentreHyp a₀ c₀ → CentreHyp a₁ c₁ → 0 ≤ β₀ → 0 ≤ β₁ → Measurable h → (∃ H, ∀ z, |h z| ≤ H) →
      Tendsto (fun ε => worstDisp (ballEps ε a₀ c₀ ν₀ (floorW ε a₀ c₀ ν₀ + β₀))
          (ballEps ε a₁ c₁ ν₁ (floorW ε a₁ c₁ ν₁ + β₁)) h) atTop
        (𝓝 (wassersteinEDist 2 (ν₀.map h) (ν₁.map h) ^ 2))

/-- The optimised groupwise term is at least `𝖡_ε(h)` (`prop:ep-blur`(i)), and `𝖡_ε(h) → E_{P̂⊗ν} f_h` as
`ε → ∞` (uniform centre, as in `eq:T`). -/
def ep_limitinf_cert : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n : ℕ) (x : Fin n → K) (c : K → K → ℝ) (h : K → ℝ) (β : ℝ)
    (ν : Measure K) [IsProbabilityMeasure ν],
    0 < n → Measurable (Function.uncurry c) → (∀ a b, 0 ≤ c a b) → (∃ B, ∀ a b, c a b ≤ B) →
    Measurable h → (∃ H, ∀ z, |h z| ≤ H) → 0 ≤ β →
      (∀ ε lam, 0 < ε → 0 < lam →
        blurB ε (fun _ => (n : ℝ)⁻¹) x c h ν ≤ Tref1 x c h ε (floorRef x c ε ν + β) lam ν) ∧
      Tendsto (fun ε => blurB ε (fun _ => (n : ℝ)⁻¹) x c h ν) atTop
        (𝓝 ((n : ℝ)⁻¹ * ∑ i, ∫ z, (h z - h (x i)) ^ 2 ∂ν))

/-! #### JASA `prop:ep-blur` -/

/-- (i): `T_ε(λ; R_ε + β) ≥ λβ + 𝖡_ε(h)` for every `λ > 0`; at `β = 0`, `T_ε(λ; R_ε) → 𝖡_ε(h)` as `λ → ∞`,
so `inf_{λ>0} T_ε(λ; R_ε) = 𝖡_ε(h)`. -/
def ep_blur_i : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n : ℕ) (x : Fin n → K) (c : K → K → ℝ) (h : K → ℝ) (ε β : ℝ)
    (ν : Measure K) [IsFiniteMeasure ν],
    0 < n → 0 < ε → 0 ≤ β → Measurable (Function.uncurry c) → (∃ B, ∀ a b, |c a b| ≤ B) →
    Measurable h → (∃ H, ∀ z, |h z| ≤ H) → ν Set.univ ≠ 0 →
      (∀ lam, 0 < lam → lam * β + blurB ε (fun _ => (n : ℝ)⁻¹) x c h ν ≤
          Tref1 x c h ε (floorRef x c ε ν + β) lam ν) ∧
      Tendsto (fun lam => Tref1 x c h ε (floorRef x c ε ν) lam ν) atTop
        (𝓝 (blurB ε (fun _ => (n : ℝ)⁻¹) x c h ν)) ∧
      (⨅ lam ∈ Ioi (0 : ℝ), (Tref1 x c h ε (floorRef x c ε ν) lam ν : EReal)) =
        (blurB ε (fun _ => (n : ℝ)⁻¹) x c h ν : EReal)

/-- (ii): at `β = 0` the ball is the single law `Q* = P̂K^ε`. -/
def ep_blur_ii_ball : Prop :=
  ∀ (K : Type) [MetricSpace K] [MeasurableSpace K] (k : ℕ) (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (ν : Measure K) [IsFiniteMeasure ν],
    Setting ε a c → ν Set.univ ≠ 0 → ballEps ε a c ν (floorW ε a c ν) = {gibbsMix ε a c ν}

/-- (ii): hence the worst-case disparity at `β = 0` is exactly `W₂²(h#P̂₀K^ε₀, h#P̂₁K^ε₁)`. -/
def ep_blur_ii_disp : Prop :=
  ∀ (K : Type) [MetricSpace K] [MeasurableSpace K] (k₀ k₁ : ℕ) (ε : ℝ) (a₀ : Fin k₀ → ℝ) (a₁ : Fin k₁ → ℝ)
    (c₀ : Fin k₀ → K → ℝ) (c₁ : Fin k₁ → K → ℝ) (ν₀ ν₁ : Measure K) [IsFiniteMeasure ν₀]
    [IsFiniteMeasure ν₁] (h : K → ℝ),
    Setting ε a₀ c₀ → Setting ε a₁ c₁ → ν₀ Set.univ ≠ 0 → ν₁ Set.univ ≠ 0 →
      worstDisp (ballEps ε a₀ c₀ ν₀ (floorW ε a₀ c₀ ν₀)) (ballEps ε a₁ c₁ ν₁ (floorW ε a₁ c₁ ν₁)) h =
        wassersteinEDist 2 ((gibbsMix ε a₀ c₀ ν₀).map h) ((gibbsMix ε a₁ c₁ ν₁).map h) ^ 2

/-- (ii), the coupling step: `W₂²(h#P̂, h#Q*) ≤ 𝖡_ε(h)`. -/
def ep_blur_ii_couple : Prop :=
  ∀ (K : Type) [MetricSpace K] [MeasurableSpace K] (k : ℕ) (ε : ℝ) (a : Fin k → ℝ) (x : Fin k → K)
    (c : K → K → ℝ) (h : K → ℝ) (ν : Measure K) [IsFiniteMeasure ν],
    Setting ε a (fun i => c (x i)) → ν Set.univ ≠ 0 → Measurable h → (∃ H, ∀ z, |h z| ≤ H) →
      wassersteinEDist 2 ((centreW a x).map h) ((gibbsMix ε a (fun i => c (x i)) ν).map h) ^ 2 ≤
        ENNReal.ofReal (blurB ε a x c h ν)

/-- (iii): the `ε = 0` member at `β = 0` (`r = R_0`). Over kernels `Γ_i` carried by `S_ν` with
`Σ_i a_i E_{Γ_i} c(x_i,·) ≤ R_0`, the groupwise value `Σ_i a_i E_{Γ_i} f_h(x_i,·)` has greatest element
`Σ_i a_i max_{y* ∈ N(x_i)} f_h(x_i,y*)`, `N(x)` the nearest points of `x` in `S_ν` (the maxima exist); it is `0`
when `S_ν = K`. -/
def ep_blur_iii : Prop :=
  ∀ (K : Type) [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (k : ℕ)
    (a : Fin k → ℝ) (x : Fin k → K) (h : K → ℝ) (ν : Measure K) [IsFiniteMeasure ν],
    (∀ i, 0 < a i) → ∑ i, a i = 1 → Continuous h → ν Set.univ ≠ 0 →
      (∃ m : Fin k → ℝ, ∀ i, IsGreatest ((fun y => (h y - h (x i)) ^ 2) '' nearest (x i) ν.support) (m i)) ∧
      (∀ m : Fin k → ℝ,
        (∀ i, IsGreatest ((fun y => (h y - h (x i)) ^ 2) '' nearest (x i) ν.support) (m i)) →
        IsGreatest {v | ∃ Γ : Fin k → Measure K, (∀ i, IsProbabilityMeasure (Γ i)) ∧
            (∀ i, Γ i (ν.support)ᶜ = 0) ∧
            ∑ i, a i * ∫ z, dist (x i) z ^ 2 ∂(Γ i) ≤ floorZero a x ν ∧
            v = ∑ i, a i * ∫ z, (h z - h (x i)) ^ 2 ∂(Γ i)} (∑ i, a i * m i)) ∧
      (ν.support = Set.univ → ∀ i, IsGreatest ((fun y => (h y - h (x i)) ^ 2) '' nearest (x i) ν.support) 0)


/-! #### JASA `lem:cert-betting` -/

/-- `lem:cert-betting`, conditionally on the fitting fold (`ĝ = g_{f̂}` fixed): for i.i.d. held-out points
`Y_j ∼ P`, `Z_j = (ū − ĝ(Y_j))/(ū − ℓ)` and predictable bets `β_j ∈ [0, 0.9]`, on a measurable event of probability
`≥ 1 − δ'` the true `E Z = (ū − E_P ĝ)/(ū − ℓ)` lies in the confidence set, hence `E_P ĝ ≤ ū − (ū − ℓ) b` for every lower
bound `b` of the set, i.e. `E_P ĝ ≤ UCB_B := ū − (ū − ℓ) inf{t₀ : max_t 𝒦_t(t₀) < 1/δ'}`. -/
def cert_betting : Prop :=
  ∀ (Ω Y : Type) [MeasurableSpace Ω] [MeasurableSpace Y] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (P : Measure Y) [IsProbabilityMeasure P] (m : ℕ) (Yb : Fin m → Ω → Y) (g : Y → ℝ) (ub lb δ : ℝ)
    (bet : Fin m → (Fin m → Y) → ℝ),
    (∀ j, Measurable (Yb j)) → iIndepFun Yb Pr → (∀ j, Pr.map (Yb j) = P) →
    Measurable g → (∀ y, lb ≤ g y ∧ g y ≤ ub) → lb < ub → 0 < δ →
    (∀ j, Measurable (bet j)) → Predictable bet → (∀ j y, 0 ≤ bet j y ∧ bet j y ≤ 0.9) →
      ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - δ) ≤ Pr E ∧ ∀ ω ∈ E,
        (ub - ∫ y, g y ∂P) / (ub - lb) ∈
            confSet (fun j => bet j fun i => Yb i ω) (fun j => (ub - g (Yb j ω)) / (ub - lb)) δ ∧
          ∀ b ∈ lowerBounds (confSet (fun j => bet j fun i => Yb i ω)
              (fun j => (ub - g (Yb j ω)) / (ub - lb)) δ),
            ∫ y, g y ∂P ≤ ub - (ub - lb) * b


/-! #### ICL `lem:e-normalizers` -/

/-- `lem:e-normalizers` (under `as:compact`, `as:score`): the relative entropies are finite and, almost surely,
`sup_θ |c_{θ,n} − c_θ| → 0` and `sup_θ |KL(μ_{θ,n} | P_n) − KL(μ_θ | P₀)| → 0` (uniform convergence on `Θ`), for the
pool `Z_1, Z_2, …` i.i.d. `P₀` (nested samples: initial segments of one sequence). -/
def e_normalizers : Prop :=
  ∀ (Θ 𝒵 Ω : Type) [MetricSpace Θ] [CompactSpace Θ] [MetricSpace 𝒵] [CompactSpace 𝒵] [MeasurableSpace 𝒵]
    [BorelSpace 𝒵] [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (P0 : Measure 𝒵)
    [IsProbabilityMeasure P0] (Zs : ℕ → Ω → 𝒵) (s : Θ → 𝒵 → ℝ) (sm sp : ℝ),
    (∀ j, Measurable (Zs j)) → iIndepFun Zs Pr → (∀ j, Pr.map (Zs j) = P0) →
    Continuous (Function.uncurry s) → 0 < sm → (∀ θ z, sm ≤ s θ z ∧ s θ z ≤ sp) →
      (∀ θ, InformationTheory.klDiv (muPop s θ P0) P0 ≠ ⊤) ∧
      (∀ θ n ω, InformationTheory.klDiv (muEmp s θ Zs n ω) (empN Zs n ω) ≠ ⊤) ∧
      ∀ᵐ ω ∂Pr,
        TendstoUniformly (fun n θ => empAvg Zs n (s θ) ω) (fun θ => ∫ z, s θ z ∂P0) atTop ∧
        TendstoUniformly (fun n θ => (InformationTheory.klDiv (muEmp s θ Zs n ω) (empN Zs n ω)).toReal)
          (fun θ => (InformationTheory.klDiv (muPop s θ P0) P0).toReal) atTop


/-! #### JASA `prop:drift` -/

/-- `prop:drift`(i), certified look-back: for independent i.i.d. samples `x ∼ P_{t−1}^n` (centre `P̂_{t−1}`) and
`y ∼ P_t^n` (`P̂_t`), with `F_t = OT_ε(P̂_{t−1}, P̂_t)`, on a measurable event of probability `≥ 1 − a`,
`P_t ∈ 𝓑^{𝒫(K)}(P̂_{t−1}, F_t + B_c √(log(1/a)/(2n)))`. -/
def drift_lookback : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n : ℕ) (ε B a : ℝ) (c : K → K → ℝ) (P₀ P₁ : Measure K)
    [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁],
    0 < n → 0 < ε → 0 < B → StatFormal.Wave7b.CostSetting c B → 0 < a → a < 1 →
      ∃ E : Set ((Fin n → K) × (Fin n → K)), MeasurableSet E ∧
        ENNReal.ofReal (1 - a) ≤ ((Measure.pi fun _ : Fin n => P₀).prod (Measure.pi fun _ : Fin n => P₁)) E ∧
        ∀ p ∈ E, P₁ ∈ StatFormal.RobustEquality.Tax.ballN {ν | IsProbabilityMeasure ν} ε (fun _ => (n : ℝ)⁻¹)
          (fun i => c (p.1 i))
          (OTdisc ε (fun _ => (n : ℝ)⁻¹) (fun i => c (p.1 i)) (StatFormal.RobustEquality.Coverage.empMeasure p.2) +
            ((B * √(Real.log (1 / a) / (2 * n)) : ℝ) : EReal))

/-- `prop:drift`(ii), forecast under non-growing drift: with `D_t = E OT_ε(P̂_{t−1}, P_t)` and
`D_{t+1} = E OT_ε(P̂_t, P_{t+1})` (both expectations of integrable functions of the samples), if `D_{t+1} ≤ D_t` then on
a measurable event of probability `≥ 1 − 2a`,
`P_{t+1} ∈ 𝓑^{𝒫(K)}(P̂_t, F_t + B_c √(log(1/a)/n) + B_c √(log(1/a)/(2n)))`. -/
def drift_forecast : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n : ℕ) (ε B a : ℝ) (c : K → K → ℝ) (P₀ P₁ P₂ : Measure K)
    [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂],
    0 < n → 0 < ε → 0 < B → StatFormal.Wave7b.CostSetting c B → 0 < a → a < 1 →
      Integrable (fun x : Fin n → K => (OTdisc ε (fun _ => (n : ℝ)⁻¹) (fun i => c (x i)) P₁).toReal)
          (Measure.pi fun _ : Fin n => P₀) ∧
        Integrable (fun y : Fin n → K => (OTdisc ε (fun _ => (n : ℝ)⁻¹) (fun i => c (y i)) P₂).toReal)
          (Measure.pi fun _ : Fin n => P₁) ∧
        ((∫ y, (OTdisc ε (fun _ => (n : ℝ)⁻¹) (fun i => c (y i)) P₂).toReal ∂(Measure.pi fun _ : Fin n => P₁)) ≤
            ∫ x, (OTdisc ε (fun _ => (n : ℝ)⁻¹) (fun i => c (x i)) P₁).toReal ∂(Measure.pi fun _ : Fin n => P₀) →
          ∃ E : Set ((Fin n → K) × (Fin n → K)), MeasurableSet E ∧
            ENNReal.ofReal (1 - 2 * a) ≤
              ((Measure.pi fun _ : Fin n => P₀).prod (Measure.pi fun _ : Fin n => P₁)) E ∧
            ∀ p ∈ E, P₂ ∈ StatFormal.RobustEquality.Tax.ballN {ν | IsProbabilityMeasure ν} ε (fun _ => (n : ℝ)⁻¹)
              (fun i => c (p.2 i))
              (OTdisc ε (fun _ => (n : ℝ)⁻¹) (fun i => c (p.1 i))
                  (StatFormal.RobustEquality.Coverage.empMeasure p.2) +
                ((B * √(Real.log (1 / a) / n) + B * √(Real.log (1 / a) / (2 * n)) : ℝ) : EReal)))


/-! #### JASA `prop:cs-tight` -/

/-- `prop:cs-tight`, construction (populations in `𝒫(ℝ^d)`): moving mass of group `s` along `w` so that the prediction
law becomes the law of `q_0 + σ_0 d/‖d‖` (group 0), `q_1 − σ_1 d/‖d‖` (group 1), `σ_s = |w|√β_s`, `d = q_0 − q_1`,
`‖d‖_{L²} = Δ_θ > 0`, is feasible (`W₂²(P_s, Q_s) ≤ β_s`); if both moved quantile functions are nondecreasing it attains
`W₂(h#Q_0, h#Q_1) = Δ_θ + σ_0 + σ_1`. The centres are any laws with finite second moments (the paper: `T_θ#P̂_s`). -/
def cs_tight : Prop :=
  ∀ (d : ℕ) (w : EuclideanSpace ℝ (Fin d)) (b β₀ β₁ : ℝ) (P₀ P₁ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁],
    w ≠ 0 → 0 ≤ β₀ → 0 ≤ β₁ → Integrable (fun x => ‖x‖ ^ 2) P₀ → Integrable (fun x => ‖x‖ ^ 2) P₁ →
    0 < deltaW w b P₀ P₁ →
      ∃ Q₀ Q₁ : Measure (EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure Q₀ ∧ IsProbabilityMeasure Q₁ ∧
        wassersteinEDist 2 P₀ Q₀ ^ 2 ≤ ENNReal.ofReal β₀ ∧ wassersteinEDist 2 P₁ Q₁ ^ 2 ≤ ENNReal.ofReal β₁ ∧
        Q₀.map (linRule w b) =
          unifIoo.map (movedQ (predQ w b P₀) (predQ w b P₀) (predQ w b P₁) (‖w‖ * √β₀ / deltaW w b P₀ P₁)) ∧
        Q₁.map (linRule w b) =
          unifIoo.map (movedQ (predQ w b P₁) (predQ w b P₀) (predQ w b P₁) (-(‖w‖ * √β₁) / deltaW w b P₀ P₁)) ∧
        (MonotoneOn (movedQ (predQ w b P₀) (predQ w b P₀) (predQ w b P₁) (‖w‖ * √β₀ / deltaW w b P₀ P₁)) (Ioo 0 1) →
          MonotoneOn (movedQ (predQ w b P₁) (predQ w b P₀) (predQ w b P₁) (-(‖w‖ * √β₁) / deltaW w b P₀ P₁))
            (Ioo 0 1) →
          wassersteinEDist 2 (Q₀.map (linRule w b)) (Q₁.map (linRule w b)) =
            ENNReal.ofReal (deltaW w b P₀ P₁ + ‖w‖ * √β₀ + ‖w‖ * √β₁))

/-- `prop:cs-tight`, exactness of `eq:cs-w2` at a fixed `θ` (populations in `𝒫(ℝ^d)`): under the monotonicity proviso the
supremum of `W₂²(h#Q_0, h#Q_1)` over `W₂²(P_s, Q_s) ≤ β_s` is attained and equals `(Δ_θ + σ_0 + σ_1)²`. -/
def cs_tight_exact : Prop :=
  ∀ (d : ℕ) (w : EuclideanSpace ℝ (Fin d)) (b β₀ β₁ : ℝ) (P₀ P₁ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁],
    w ≠ 0 → 0 ≤ β₀ → 0 ≤ β₁ → Integrable (fun x => ‖x‖ ^ 2) P₀ → Integrable (fun x => ‖x‖ ^ 2) P₁ →
    0 < deltaW w b P₀ P₁ →
    MonotoneOn (movedQ (predQ w b P₀) (predQ w b P₀) (predQ w b P₁) (‖w‖ * √β₀ / deltaW w b P₀ P₁)) (Ioo 0 1) →
    MonotoneOn (movedQ (predQ w b P₁) (predQ w b P₀) (predQ w b P₁) (-(‖w‖ * √β₁) / deltaW w b P₀ P₁)) (Ioo 0 1) →
      IsGreatest {v | ∃ Q₀ Q₁ : Measure (EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure Q₀ ∧
          IsProbabilityMeasure Q₁ ∧
          wassersteinEDist 2 P₀ Q₀ ^ 2 ≤ ENNReal.ofReal β₀ ∧ wassersteinEDist 2 P₁ Q₁ ^ 2 ≤ ENNReal.ofReal β₁ ∧
          v = wassersteinEDist 2 (Q₀.map (linRule w b)) (Q₁.map (linRule w b)) ^ 2}
        (ENNReal.ofReal ((deltaW w b P₀ P₁ + ‖w‖ * √β₀ + ‖w‖ * √β₁) ^ 2))

/-- Refutation of the `𝒫(K)` reading (`CsTightOnK`): `d = 1`, `w = e`, `b = 0`, `K` the closed ball of radius `½`
about `½e`, `P_0 = δ_e`, `P_1 = δ_0`, `β_0 = β_1 = ¼` (`Δ = 1`, `σ_s = ½`, both moved quantile functions constant):
every admissible pair has `W₂² ≤ 1 < 4 = (Δ + σ_0 + σ_1)²`. -/
def cs_tight_K_false : Prop := ¬ CsTightOnK


/-! #### otfd A `prop:lift-dual` -/

/-- (i), first step of the proof: the conjugate of a direct sum `φ_K ⊕ φ_⊥` on `ℝ^K ⊕ ℝ^{T−K}` is the direct sum
of the conjugates (`EReal`, `+∞` allowed). -/
def lift_dual_conj_split : Prop :=
  ∀ (α β : Type) [Fintype α] [Fintype β] (φ₁ : (α → ℝ) → ℝ) (φ₂ : (β → ℝ) → ℝ) (u : α ⊕ β → ℝ),
    conjE (fun x : α ⊕ β → ℝ => φ₁ (x ∘ Sum.inl) + φ₂ (x ∘ Sum.inr)) u =
      conjE φ₁ (u ∘ Sum.inl) + conjE φ₂ (u ∘ Sum.inr)

/-- (i): for a separable tail `φ_⊥ = Σ_k φ_k` the conjugate is `Σ_k φ_k*`. -/
def lift_dual_conj_sep : Prop :=
  ∀ (ι : Type) [Fintype ι] (φ : ι → ℝ → ℝ) (u : ι → ℝ),
    conjE (fun x : ι → ℝ => ∑ i, φ i (x i)) u = ∑ i, conj1 (φ i) (u i)

/-- (i): `J(φ_K ⊕ φ_⊥) = [E φ_K(X_K) + E φ_K*(U_K)] + [E φ_⊥(X_⊥) + E φ_⊥*(U_⊥)]`, whenever the four terms are
integrable and the two conjugates finite `μ`-a.e.; then `(φ_K ⊕ φ_⊥)*` is finite `μ`-a.e. too. -/
def lift_dual_J_split : Prop :=
  ∀ (α β : Type) [Fintype α] [Fintype β] (φ₁ : (α → ℝ) → ℝ) (φ₂ : (β → ℝ) → ℝ) (P μ : Measure (α ⊕ β → ℝ))
    [IsProbabilityMeasure P] [IsProbabilityMeasure μ],
    Integrable (fun x : α ⊕ β → ℝ => φ₁ (x ∘ Sum.inl)) P → Integrable (fun x : α ⊕ β → ℝ => φ₂ (x ∘ Sum.inr)) P →
    (∀ᵐ u ∂μ, conjE φ₁ (u ∘ Sum.inl) ≠ ⊤) → (∀ᵐ u ∂μ, conjE φ₂ (u ∘ Sum.inr) ≠ ⊤) →
    Integrable (fun u : α ⊕ β → ℝ => (conjE φ₁ (u ∘ Sum.inl)).toReal) μ →
    Integrable (fun u : α ⊕ β → ℝ => (conjE φ₂ (u ∘ Sum.inr)).toReal) μ →
      (∀ᵐ u ∂μ, conjE (fun x : α ⊕ β → ℝ => φ₁ (x ∘ Sum.inl) + φ₂ (x ∘ Sum.inr)) u ≠ ⊤) ∧
      (∫ x, (φ₁ (x ∘ Sum.inl) + φ₂ (x ∘ Sum.inr)) ∂P +
          ∫ u, (conjE (fun x : α ⊕ β → ℝ => φ₁ (x ∘ Sum.inl) + φ₂ (x ∘ Sum.inr)) u).toReal ∂μ =
        (∫ x, φ₁ (x ∘ Sum.inl) ∂P + ∫ u, (conjE φ₁ (u ∘ Sum.inl)).toReal ∂μ) +
          (∫ x, φ₂ (x ∘ Sum.inr) ∂P + ∫ u, (conjE φ₂ (u ∘ Sum.inr)).toReal ∂μ))

/-- (i), last sentence: with atomless tail marginals of `P_T`, the monotone rearrangements
`t_k = G_{U_k}^{-1} ∘ G_{X_k}` push each tail marginal of `P_T` onto the corresponding marginal of `μ_T` (the frozen
`IsSepTail` of `prop:lift-consistency`). -/
def lift_dual_push : Prop :=
  ∀ (T K : ℕ) (P μ : Measure (Fin T → ℝ)) [IsProbabilityMeasure P] [IsProbabilityMeasure μ],
    (∀ k : Fin T, K ≤ (k : ℕ) → ∀ y, (P.map fun x => x k) {y} = 0) →
      StatFormal.Wave16a.IsSepTail P μ K (rearrTail P μ)

/-- (ii), diagonal quadratic tails, one coordinate: `φ*(u) = m u + u²/(2λ)` for `φ = ½λ(· − m)²`, and with a centred
reference (`E U_k = 0`, the standing assumption of `sec:lift`), `E U_k² > 0`, `Var X_k > 0` and second moments, the
semi-dual over `λ > 0`, `m ∈ ℝ` has the unique minimiser `m = E X_k`, `λ = (E U_k² / Var X_k)^{1/2}`. -/
def lift_dual_ii : Prop :=
  ∀ (ν ρ : Measure ℝ) [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ],
    Integrable (fun x => x ^ 2) ν → Integrable (fun u => u ^ 2) ρ →
    0 < ∫ x, (x - ∫ y, y ∂ν) ^ 2 ∂ν → ∫ u, u ∂ρ = 0 → 0 < ∫ u, u ^ 2 ∂ρ →
      (∀ lam m u : ℝ, 0 < lam → conj1 (quadPot lam m) u = ((m * u + u ^ 2 / (2 * lam) : ℝ) : EReal)) ∧
      ∀ lam m : ℝ, 0 < lam →
        semiDual1 (quadPot (√((∫ u, u ^ 2 ∂ρ) / ∫ x, (x - ∫ y, y ∂ν) ^ 2 ∂ν)) (∫ y, y ∂ν)) ν ρ ≤
            semiDual1 (quadPot lam m) ν ρ ∧
          (semiDual1 (quadPot lam m) ν ρ =
              semiDual1 (quadPot (√((∫ u, u ^ 2 ∂ρ) / ∫ x, (x - ∫ y, y ∂ν) ^ 2 ∂ν)) (∫ y, y ∂ν)) ν ρ →
            lam = √((∫ u, u ^ 2 ∂ρ) / ∫ x, (x - ∫ y, y ∂ν) ^ 2 ∂ν) ∧ m = ∫ y, y ∂ν)

/-- (iii), full quadratic tails, reduced objective: for `Σ_X ≻ 0` (the hypothesis the corrected text adds) and
`Σ_U ≻ 0`, the Gelbrich matrix `Λ*` is positive definite, solves `Λ* Σ_X Λ* = Σ_U`, and is the unique minimiser of
`½ tr(Λ Σ_X) + ½ tr(Λ⁻¹ Σ_U)` over positive definite `Λ`. -/
def lift_dual_iii : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (A B : Matrix n n ℝ), A.PosDef → B.PosDef →
    (gelbrich A B).PosDef ∧ gelbrich A B * A * gelbrich A B = B ∧
      ∀ L : Matrix n n ℝ, L.PosDef → gaussObj A B (gelbrich A B) ≤ gaussObj A B L ∧
        (gaussObj A B L = gaussObj A B (gelbrich A B) → L = gelbrich A B)

/-- (iii), the diagonal case: if `Σ_X` and `Σ_U` are diagonal (FPCA basis, reference built along it), `Λ*` is the
diagonal matrix of (ii), `(σ²_{U,k}/σ²_{X,k})^{1/2}`. -/
def lift_dual_iii_diag : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (a b : n → ℝ), (∀ i, 0 < a i) → (∀ i, 0 < b i) →
    gelbrich (Matrix.diagonal a) (Matrix.diagonal b) = Matrix.diagonal fun i => √(b i / a i)

end Claims
end StatFormal.Wave20b
