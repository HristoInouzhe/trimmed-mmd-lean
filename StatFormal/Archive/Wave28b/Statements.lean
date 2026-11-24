import StatFormal.Archive.Wave23a.Statements
import StatFormal.Archive.Wave24c.Statements
import StatFormal.Archive.Wave24e.Statements
import StatFormal.Archive.Wave11b.Statements
import Mathlib.Probability.CentralLimitTheorem

/-!
# FROZEN STATEMENTS — wave 28b: ICL `thm:score` — the almost-sure uniform law and consistency on the concrete
# objective (discharge of the frozen Wave 23a `score_argmin` premises) and asymptotic normality (`p = 1`)

Sources:
* ICL `thm:score` (`context-distribution-ICL/paper/v3/sections/06_estimation.tex:137-148`), with the objective of
  `subsec:score-guarantees` (`:127-135`).
* Supplement `supp/proofs_score.tex`: Assumptions `as:compact`–`as:interior` (`:14-50`), the objectives `J`,
  `J^iid_{n,m}` (`:51-66`), `lem:e-ulln` (`:157-178`), the consistency proof (`:180-202`), the normality proof
  Steps 1–4 (`:204-294`, `eq:e-linear` `:216-220`), `prop:swor-score` (`:348-356`).
Imports the frozen `Wave23a` (`score_argmin`, the deterministic core being discharged), `Wave24c` (`ctxLawT`,
`coverRho`, `klPop`), `Wave24e` (`wPop`) and `Wave11b` (`jSwor`, `jIid`, `wScore`) statements, not copied; Mathlib's
`TendstoInDistribution`, `TendstoInMeasure`, `gaussianReal`, `HasLaw`, `variance` otherwise.

Covered:
* `thm:score`, first sentence: `score_argmin_discharged` (nested i.i.d. `P₀` pool `X` and validation `Y` sequences,
  `n → ∞`, `m = m(n) → ∞`, convergent penalty weights: almost surely `J` attains its minimum, `J_{n,m}` attains its
  minimum for every `n ≥ M`, `sup_Θ |J_{n,m} − J| → 0`, `inf J_{n,m} → min J`, and every limit point of
  `ε_n`-minimisers `θ̂_n` minimises `J`). DISCHARGE of the frozen Wave 23a `score_argmin` (mechanical diff: its premises
  `Continuous J` and `TendstoUniformly J_n J atTop` are removed; `J_n := J_{n,m(n)}(ω)` with conditional Poisson
  contexts — the paper's estimator — and `J` the population target are the concrete objects; the premise
  `Continuous (J_n n)` of the attainment clause becomes `M ≤ n`; the uniform convergence is added to the conclusion,
  which holds almost surely; new ⇒ old pathwise). `score_argmin_unique`: if `J` has a unique minimiser `θ⋆`, almost
  surely `θ̂_n → θ⋆` (the remark after `as:interior`, without relabelling).
* `thm:score`, asymptotic normality, for a one-dimensional parameter: `score_asymp_normal` — the exact minimisers of
  the without-replacement objective `J_{n,m}` satisfy `√n(θ̂_n − θ⋆) ⇝ N(0, (Σ_pool + κ⁻¹Σ_val)/V²)` — CONDITIONAL on
  Step 2 (`eq:e-linear` for the i.i.d.-context gradient), on Step 1 (convergence of its second derivative near
  `θ⋆`) and on consistency in probability; `score_asymp_normal_cons` — the same on `Θ = [a, b]` with consistency
  DISCHARGED through `score_argmin_unique` (identifiable `θ⋆`), so CONDITIONAL only on Steps 1 and 2. Proved: the
  without-replacement transfer of the first two derivatives (certified WaveP1d `swor_derivs`, the transfer clause of
  `prop:swor-score`), the first-order condition at an interior minimiser, the two-sample central limit theorem
  (Step 3), the mean-value expansion and Slutsky (Step 4), via the new library `Foundations/CLT` (`clt_two_sample`,
  `zest_asymp_normal`) on Mathlib's i.i.d. central limit theorem, Lévy continuity and Slutsky lemmas.

Not covered:
* `thm:score` normality: Step 2 (the Hoeffding decomposition of the two-sample V-statistic, the coverage and
  relative-entropy delta methods, `√n(λ_{·,n} − λ_·) → 0`) and Step 1 (the uniform law for `∇²J^iid_{n,m}`) are
  hypotheses; parameters in `ℝ^p`, `p ≥ 2` (Cramér–Wold, matrix `V`), and the relabelling representative.
* `cor:inference` (not attempted).

Encodings (to be checked by the critic):
* `J_{n,m}(θ) = jScore s L K x y n m λ_cov λ_KL θ` is the frozen Wave 11b `jSwor` (mean risk under the conditional
  Poisson law `Π_{w(θ)}`, coverage at its one-slot marginal `π/M`, `KL(w | u_n)`) at the frozen score weights
  `wScore`, on the pool `x_0, …, x_{n−1}` and the validation points `y_0, …, y_{m−1}` of the sample paths;
  `jScoreIid` is the frozen `jIid` (i.i.d. contexts from `w(θ)`, `supp:score-transfer`).
* `J(θ) = jPop P₀ s L K λ_cov λ_KL θ = ∫ L̄ dμ_θ^{⊗M} − λ_cov P₀ log ρ_{μ_θ} + λ_KL KL(μ_θ | P₀)` with
  `L̄(t) = ∫ L(z; t) dP₀(z)` (`lossBar`), the first term in the frozen density form `wPop`
  (`∫ ∏_k g_θ(t_k) L̄(t) dP₀^{⊗M}(t)`), the frozen `coverRho`, `ctxLawT` and the closed-form `klPop` — the limit of
  the frozen Wave 24c `e_ulln` and the supplement's display of `J`. It is the i.i.d.-context population objective;
  it equals the without-replacement one when `P₀` has no atoms (the paper's standing assumption), which is not
  needed here since `J_{n,m} → J` regardless.
* Sampling (`as:compact`): `X, Y : ℕ → Ω → 𝒵` each i.i.d. `P₀` (`iIndepFun`, `P.map (X j) = P₀`), nested; for the
  consistency part no independence between `X` and `Y` is needed; for normality the two families are independent
  (`IndepFun` of the two path maps). `m : ℕ → ℕ` with `m(n) → ∞` (paper: `n, m → ∞`), and `m(n)/n → κ ∈ (0,∞)` for
  normality. The joint limit is read along an arbitrary sequence `m(n)`, quantified outside the almost-sure event
  (the usual sequential reading; the paper's double limit on one null set is not stated).
* `as:score`, `as:kernel`, `as:loss` as in Wave 24c `e_ulln` and Wave 11b `swor_value`; `λ_{cov,n} ≥ 0`.
* `θ̂_n` are `ε_n`-minimisers (`ε_n → 0` almost surely, possibly random; paper: exact minimisers, `ε_n = 0`); limit
  points are `MapClusterPt`. Attainment for `n ≥ M` (the conditional Poisson law needs `M` pool points).
* Normality (`p = 1`): `Θ ⊆ ℝ` is any set `T ⊇ B(θ⋆, δ)` (`[a, b]` in `score_asymp_normal_cons`); `s` is given on all
  of `ℝ × 𝒵` with `s₋ ≤ s ≤ s₊` (extend outside `Θ`), with two `t`-derivatives on the ball bounded by `b₁`, `b₂`
  (`as:smooth`); `θ̂_n` is a measurable exact minimiser of `J_{n,m}` over `T`; `g`, `h` are the first two derivatives
  of the i.i.d. objective on the ball. Step 2 is `√n g_n(θ⋆) − (n^{−1/2} Σ_{i<n} ψ_pool(X_i) + √n m^{−1} Σ_{i<m}
  ψ_val(Y_i)) → 0` in probability (`eq:e-linear` times `√n`), with `ψ`'s measurable, centred and square integrable
  under `P₀` (paper: bounded), `Σ_pool = Var ψ_pool`, `Σ_val = Var ψ_val`. Step 1 is
  `P*(∃ t ∈ B(θ⋆,δ), |h_n(t) − H(t)| ≥ η) → 0` for every `η > 0` (outer probability), with `H` continuous at `θ⋆` and
  `V = H(θ⋆) > 0` (`as:interior`, `H = J''`; `H` is not required to be the second derivative of `jPop` — on the ball
  it is the probability limit of `h_n`, hence unique, and equals `J''` under the printed Step 1); the paper's almost-sure `sup_U |∇²J^iid_{n,m} − ∇²J| → 0` implies it
  whenever that supremum is measurable (e.g. `h_n` continuous in `t`, measurable in `ω`). The limit is any `G` with
  `HasLaw G (gaussianReal 0 ((Σ_pool + Σ_val/κ)/V²))`, convergence is Mathlib's `TendstoInDistribution` (weak
  convergence of the laws as `ProbabilityMeasure`s).
* Junk values: `jScore` at `n < M` (`e_M(w) = 0`, so `cps = x/0 = 0`) and at `m(n) = 0` (`1/0 = 0`) occurs for finitely
  many `n` only and enters no conclusion (attainment is for `n ≥ M`); `normC ≥ s₋ > 0`, coverages `≥ K_min > 0`;
  `√n/m(n)` at `m(n) = 0` multiplies an empty sum; the Gaussian variance is `≥ 0` before `toNNReal`.

Drafter notes:
* All 4 claims are proved in `Wave28b/Route{Consistency,Normal}.lean`, collected in `Wave28b/Proofs.lean` (kernel
  dependencies: propext, Classical.choice, Quot.sound). `Proofs.lean` also checks the discharge direction: pathwise,
  the new conclusion implies the frozen `score_argmin` conclusion at `J := jPop`, `J_n := J_{n,m(n)}(ω)`. Routes reuse the certified Wave 23a `score_argmin`, Wave 24e `e_vstat`, Wave 24c `e_ulln` (with
  `compactGC_of_iid`, i.e. Wave 20b `uniform_slln`), Wave 11b `swor_value`, WaveP1d `swor_derivs`, ICL `cps_incl`,
  `cps_wellPosed`. The risk term follows the supplement's `lem:e-ulln` proof: Glivenko–Cantelli with index `t ∈ 𝒵^M`
  for `(P_m − P₀)L(·; t)` plus `e_vstat` with `H_θ = L̄`. `J` is continuous as the uniform limit of the continuous
  `J_{n,m}`.
* Library `StatFormal/Foundations/CLT/`: `TwoSample.lean` (`clt_centered`, `tendstoInDistribution_add_gaussian`,
  `tendstoInDistribution_mul_of_tendsto`, `clt_two_sample`), `ZEstimator.lean` (`tight_of_tendstoInDistribution`,
  `zest_asymp_normal`). Mathlib already has the i.i.d. real CLT (`tendstoInDistribution_inv_sqrt_mul_sum_sub`),
  Lévy continuity (`TendstoInDistribution.of_tendsto_charFun`), Cramér–Wold and Slutsky.

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal NNReal Real

namespace StatFormal.Wave28b

section Objects
variable {Θ Z : Type*} {M : ℕ}

/-- The paper's `J_{n,m}(θ) = J_m(w(θ))` on the pool `x_0, …, x_{n−1}` and the validation points `y_0, …, y_{m−1}`:
the frozen Wave 11b `jSwor` (conditional Poisson contexts) at the score weights `w_j(θ) = s_θ(x_j)/Σ_l s_θ(x_l)`. -/
def jScore (s : Θ → Z → ℝ) (L : Z → (Fin M → Z) → ℝ) (K : Z → Z → ℝ) (x y : ℕ → Z) (n m : ℕ) (lcov lKL : ℝ)
    (θ : Θ) : ℝ :=
  StatFormal.Wave11b.jSwor L K (fun i : Fin n => x i) (fun i : Fin m => y i) lcov lKL
    (StatFormal.Wave11b.wScore s (fun i : Fin n => x i) θ)

/-- `J^iid_{n,m}(θ)`: the same objective with i.i.d. contexts from `w(θ)` (frozen Wave 11b `jIid`). -/
def jScoreIid (s : Θ → Z → ℝ) (L : Z → (Fin M → Z) → ℝ) (K : Z → Z → ℝ) (x y : ℕ → Z) (n m : ℕ) (lcov lKL : ℝ)
    (θ : Θ) : ℝ :=
  StatFormal.Wave11b.jIid L K (fun i : Fin n => x i) (fun i : Fin m => y i) lcov lKL
    (StatFormal.Wave11b.wScore s (fun i : Fin n => x i) θ)

variable [MeasurableSpace Z]

/-- `L̄(t) = ∫ L(z; t) dP₀(z)`. -/
def lossBar (P0 : Measure Z) (L : Z → (Fin M → Z) → ℝ) (t : Fin M → Z) : ℝ := ∫ z, L z t ∂P0

/-- The population target `J(θ) = ∫ L̄ dμ_θ^{⊗M} − λ_cov P₀ log ρ_{μ_θ} + λ_KL KL(μ_θ | P₀)`, `μ_θ = g_θ P₀`
(the first term in the frozen Wave 24e density form `wPop`). -/
def jPop (P0 : Measure Z) (s : Θ → Z → ℝ) (L : Z → (Fin M → Z) → ℝ) (K : Z → Z → ℝ) (lcov lKL : ℝ) (θ : Θ) : ℝ :=
  StatFormal.Wave24e.wPop P0 (fun q : Θ × Z => s q.1 q.2) (fun q : Θ × (Fin M → Z) => lossBar P0 L q.2) θ -
      lcov * ∫ z, Real.log (StatFormal.Wave24c.coverRho K (StatFormal.Wave24c.ctxLawT P0 s θ) z) ∂P0 +
    lKL * StatFormal.Wave24c.klPop P0 s θ

end Objects

namespace Claims

/-- ICL `thm:score`, consistency, on the concrete objective: for nested i.i.d. `P₀` pool and validation sequences,
`m(n) → ∞` and convergent penalty weights, almost surely `J` attains its minimum, every `J_{n,m}` with `n ≥ M`
attains its minimum, `sup_Θ |J_{n,m} − J| → 0`, `inf J_{n,m} → min J`, and every limit point of `ε_n`-minimisers
`θ̂_n` of `J_{n,m}` (`ε_n → 0`) minimises `J`. (Frozen Wave 23a `score_argmin` with its premises discharged.) -/
def score_argmin_discharged : Prop :=
  ∀ (Θ Z Ω : Type) [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MetricSpace Z] [CompactSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [MeasurableSpace Ω] (P : Measure Ω) (P0 : Measure Z) (M : ℕ)
    (X Y : ℕ → Ω → Z) (m : ℕ → ℕ) (s : Θ → Z → ℝ) (L : Z → (Fin M → Z) → ℝ) (K : Z → Z → ℝ)
    (sm sp BL Kmin Kmax lc lK : ℝ) (lcn lKn : ℕ → ℝ) (θn : ℕ → Ω → Θ) (εn : ℕ → Ω → ℝ),
    IsProbabilityMeasure P → IsProbabilityMeasure P0 → 1 ≤ M →
    Continuous (Function.uncurry s) → 0 < sm → (∀ θ z, sm ≤ s θ z ∧ s θ z ≤ sp) →
    Continuous (Function.uncurry K) → 0 < Kmin → (∀ z z', Kmin ≤ K z z' ∧ K z z' ≤ Kmax) →
    Continuous (Function.uncurry L) → (∀ z t, 0 ≤ L z t ∧ L z t ≤ BL) →
    (∀ z t (σ : Equiv.Perm (Fin M)), L z (t ∘ σ) = L z t) →
    (∀ j, Measurable (X j)) → iIndepFun X P → (∀ j, P.map (X j) = P0) →
    (∀ j, Measurable (Y j)) → iIndepFun Y P → (∀ j, P.map (Y j) = P0) →
    Tendsto m atTop atTop → (∀ n, 0 ≤ lcn n) → Tendsto lcn atTop (𝓝 lc) → Tendsto lKn atTop (𝓝 lK) →
    (∀ᵐ ω ∂P, Tendsto (fun n => εn n ω) atTop (𝓝 0)) →
    (∀ᵐ ω ∂P, ∀ n θ, jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n) (θn n ω) ≤
      jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n) θ + εn n ω) →
      ∀ᵐ ω ∂P, (∃ θ, ∀ θ', jPop P0 s L K lc lK θ ≤ jPop P0 s L K lc lK θ') ∧
        (∀ n, M ≤ n → ∃ θ, ∀ θ', jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n) θ ≤
          jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n) θ') ∧
        TendstoUniformly (fun n => jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n))
          (jPop P0 s L K lc lK) atTop ∧
        Tendsto (fun n => ⨅ θ, jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n) θ) atTop
          (𝓝 (⨅ θ, jPop P0 s L K lc lK θ)) ∧
        ∀ θ, MapClusterPt θ atTop (fun n => θn n ω) → ∀ θ', jPop P0 s L K lc lK θ ≤ jPop P0 s L K lc lK θ'

/-- ICL `thm:score`, consistency of the estimator (the remark after `as:interior`): under the hypotheses of
`score_argmin_discharged`, if `θ⋆` is the unique minimiser of `J`, then almost surely `θ̂_n → θ⋆`. -/
def score_argmin_unique : Prop :=
  ∀ (Θ Z Ω : Type) [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MetricSpace Z] [CompactSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [MeasurableSpace Ω] (P : Measure Ω) (P0 : Measure Z) (M : ℕ)
    (X Y : ℕ → Ω → Z) (m : ℕ → ℕ) (s : Θ → Z → ℝ) (L : Z → (Fin M → Z) → ℝ) (K : Z → Z → ℝ)
    (sm sp BL Kmin Kmax lc lK : ℝ) (lcn lKn : ℕ → ℝ) (θn : ℕ → Ω → Θ) (εn : ℕ → Ω → ℝ) (θs : Θ),
    IsProbabilityMeasure P → IsProbabilityMeasure P0 → 1 ≤ M →
    Continuous (Function.uncurry s) → 0 < sm → (∀ θ z, sm ≤ s θ z ∧ s θ z ≤ sp) →
    Continuous (Function.uncurry K) → 0 < Kmin → (∀ z z', Kmin ≤ K z z' ∧ K z z' ≤ Kmax) →
    Continuous (Function.uncurry L) → (∀ z t, 0 ≤ L z t ∧ L z t ≤ BL) →
    (∀ z t (σ : Equiv.Perm (Fin M)), L z (t ∘ σ) = L z t) →
    (∀ j, Measurable (X j)) → iIndepFun X P → (∀ j, P.map (X j) = P0) →
    (∀ j, Measurable (Y j)) → iIndepFun Y P → (∀ j, P.map (Y j) = P0) →
    Tendsto m atTop atTop → (∀ n, 0 ≤ lcn n) → Tendsto lcn atTop (𝓝 lc) → Tendsto lKn atTop (𝓝 lK) →
    (∀ᵐ ω ∂P, Tendsto (fun n => εn n ω) atTop (𝓝 0)) →
    (∀ᵐ ω ∂P, ∀ n θ, jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n) (θn n ω) ≤
      jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n) θ + εn n ω) →
    (∀ θ, (∀ θ', jPop P0 s L K lc lK θ ≤ jPop P0 s L K lc lK θ') → θ = θs) →
      ∀ᵐ ω ∂P, Tendsto (fun n => θn n ω) atTop (𝓝 θs)

/-- ICL `thm:score`, asymptotic normality, one-dimensional parameter, CONDITIONAL on the asymptotic linearity of the
i.i.d.-context gradient at `θ⋆` (pool and validation influence functions `ψ_pool`, `ψ_val`), the uniform convergence
in outer probability of its second derivative near `θ⋆` to `H` with `V = H(θ⋆) > 0`, and consistency: if `m/n → κ > 0`,
the exact minimisers `θ̂_n` of the without-replacement objective `J_{n,m}` satisfy
`√n(θ̂_n − θ⋆) ⇝ N(0, (Σ_pool + κ⁻¹Σ_val)/V²)`. -/
def score_asymp_normal : Prop :=
  ∀ (M : ℕ) (sm sp b1 b2 BL Kmin Kmax Λ κ : ℝ) (Z Ω Ω' : Type) [MeasurableSpace Z] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    (P0 : Measure Z) (X Y : ℕ → Ω → Z) (m : ℕ → ℕ) (s s1 s2 : ℝ → Z → ℝ) (L : Z → (Fin M → Z) → ℝ)
    (K : Z → Z → ℝ) (lcn lKn : ℕ → ℝ) (T : Set ℝ) (θh : ℕ → Ω → ℝ) (θs δ : ℝ) (g h : ℕ → Ω → ℝ → ℝ)
    (H : ℝ → ℝ) (ψp ψv : Z → ℝ) (σp σv : ℝ≥0) (G : Ω' → ℝ),
    1 ≤ M → 0 < sm → (∀ t x, sm ≤ s t x ∧ s t x ≤ sp) →
    (∀ x, ∀ t ∈ Metric.ball θs δ, HasDerivAt (fun t => s t x) (s1 t x) t ∧
      HasDerivAt (fun t => s1 t x) (s2 t x) t) →
    (∀ x, ∀ t ∈ Metric.ball θs δ, |s1 t x| ≤ b1 ∧ |s2 t x| ≤ b2) →
    (∀ x t, 0 ≤ L x t ∧ L x t ≤ BL) → (∀ x t (σ : Equiv.Perm (Fin M)), L x (t ∘ σ) = L x t) →
    0 < Kmin → (∀ x y, Kmin ≤ K x y ∧ K x y ≤ Kmax) → (∀ n, 0 ≤ lcn n ∧ lcn n ≤ Λ) →
    0 < κ → Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ) → 0 < δ → Metric.ball θs δ ⊆ T →
    (∀ n ω, ∀ t ∈ Metric.ball θs δ,
      HasDerivAt (jScoreIid s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n)) (g n ω t) t ∧
      HasDerivAt (g n ω) (h n ω t) t) →
    TendstoInMeasure P (fun (n : ℕ) ω => √(n : ℝ) * g n ω θs -
      ((√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, ψp (X i ω) +
        √(n : ℝ) / m n * ∑ i ∈ Finset.range (m n), ψv (Y i ω))) atTop 0 →
    ContinuousAt H θs → 0 < H θs →
    (∀ η > 0, Tendsto (fun n => P {ω | ∃ t ∈ Metric.ball θs δ, η ≤ |h n ω t - H t|}) atTop (𝓝 0)) →
    (∀ n, Measurable (θh n)) →
    (∀ n ω, θh n ω ∈ T ∧ ∀ t ∈ T, jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n)
      (θh n ω) ≤ jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n) t) →
    TendstoInMeasure P θh atTop (fun _ => θs) →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X P → iIndepFun Y P →
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) P → (∀ i, P.map (X i) = P0) → (∀ i, P.map (Y i) = P0) →
    Measurable ψp → Measurable ψv → MemLp ψp 2 P0 → MemLp ψv 2 P0 → ∫ z, ψp z ∂P0 = 0 →
    ∫ z, ψv z ∂P0 = 0 → Var[ψp; P0] = σp → Var[ψv; P0] = σv →
    HasLaw G (gaussianReal 0 ((((σp : ℝ) + σv / κ) / H θs ^ 2).toNNReal)) P' →
      TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) * (θh n ω - θs)) atTop G (fun _ => P) P'

/-- ICL `thm:score`, asymptotic normality with consistency DISCHARGED: on a compact interval `Θ = [a, b] ∋ θ⋆` with
`J` uniquely minimised at `θ⋆` (`as:interior`, no relabelling), under the hypotheses of `score_argmin_discharged`
and those of `score_asymp_normal` other than consistency, `√n(θ̂_n − θ⋆) ⇝ N(0, (Σ_pool + κ⁻¹Σ_val)/V²)`.
CONDITIONAL only on the asymptotic linearity of the i.i.d.-context gradient and the convergence of its second
derivative. -/
def score_asymp_normal_cons : Prop :=
  ∀ (M : ℕ) (sm sp b1 b2 BL Kmin Kmax Λ κ lc lK a b : ℝ) (Z Ω Ω' : Type) [MetricSpace Z] [CompactSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω)
    [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P'] (P0 : Measure Z) (X Y : ℕ → Ω → Z)
    (m : ℕ → ℕ) (s s1 s2 : ℝ → Z → ℝ) (L : Z → (Fin M → Z) → ℝ) (K : Z → Z → ℝ) (lcn lKn : ℕ → ℝ)
    (θh : ℕ → Ω → ℝ) (θs δ : ℝ) (g h : ℕ → Ω → ℝ → ℝ) (H : ℝ → ℝ) (ψp ψv : Z → ℝ) (σp σv : ℝ≥0) (G : Ω' → ℝ),
    1 ≤ M → 0 < sm → (∀ t x, sm ≤ s t x ∧ s t x ≤ sp) → ContinuousOn (Function.uncurry s) (Icc a b ×ˢ univ) →
    (∀ x, ∀ t ∈ Metric.ball θs δ, HasDerivAt (fun t => s t x) (s1 t x) t ∧
      HasDerivAt (fun t => s1 t x) (s2 t x) t) →
    (∀ x, ∀ t ∈ Metric.ball θs δ, |s1 t x| ≤ b1 ∧ |s2 t x| ≤ b2) →
    Continuous (Function.uncurry L) → (∀ x t, 0 ≤ L x t ∧ L x t ≤ BL) →
    (∀ x t (σ : Equiv.Perm (Fin M)), L x (t ∘ σ) = L x t) →
    Continuous (Function.uncurry K) → 0 < Kmin → (∀ x y, Kmin ≤ K x y ∧ K x y ≤ Kmax) →
    (∀ n, 0 ≤ lcn n ∧ lcn n ≤ Λ) → Tendsto lcn atTop (𝓝 lc) → Tendsto lKn atTop (𝓝 lK) →
    0 < κ → Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ) → 0 < δ → Metric.ball θs δ ⊆ Icc a b →
    (∀ θ ∈ Icc a b, (∀ θ' ∈ Icc a b, jPop P0 s L K lc lK θ ≤ jPop P0 s L K lc lK θ') → θ = θs) →
    (∀ n ω, ∀ t ∈ Metric.ball θs δ,
      HasDerivAt (jScoreIid s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n)) (g n ω t) t ∧
      HasDerivAt (g n ω) (h n ω t) t) →
    TendstoInMeasure P (fun (n : ℕ) ω => √(n : ℝ) * g n ω θs -
      ((√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, ψp (X i ω) +
        √(n : ℝ) / m n * ∑ i ∈ Finset.range (m n), ψv (Y i ω))) atTop 0 →
    ContinuousAt H θs → 0 < H θs →
    (∀ η > 0, Tendsto (fun n => P {ω | ∃ t ∈ Metric.ball θs δ, η ≤ |h n ω t - H t|}) atTop (𝓝 0)) →
    (∀ n, Measurable (θh n)) →
    (∀ n ω, θh n ω ∈ Icc a b ∧ ∀ t ∈ Icc a b, jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n)
      (lKn n) (θh n ω) ≤ jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n) t) →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X P → iIndepFun Y P →
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) P → (∀ i, P.map (X i) = P0) → (∀ i, P.map (Y i) = P0) →
    Measurable ψp → Measurable ψv → MemLp ψp 2 P0 → MemLp ψv 2 P0 → ∫ z, ψp z ∂P0 = 0 →
    ∫ z, ψv z ∂P0 = 0 → Var[ψp; P0] = σp → Var[ψv; P0] = σv →
    HasLaw G (gaussianReal 0 ((((σp : ℝ) + σv / κ) / H θs ^ 2).toNNReal)) P' →
      TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) * (θh n ω - θs)) atTop G (fun _ => P) P'

end Claims

end StatFormal.Wave28b
