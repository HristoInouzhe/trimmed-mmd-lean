import StatFormal.Archive.Wave28b.Statements

/-!
# FROZEN STATEMENTS — wave 28f: ICL `thm:score`, asymptotic normality UNCONDITIONAL for a one-dimensional parameter
# (discharge of the proof's Step 1 — the Hessian uniform law — and Step 2 — the linearisation `eq:e-linear`)

Sources:
* ICL `thm:score` (`context-distribution-ICL/paper/v3/sections/06_estimation.tex:137-148`).
* Supplement `supp/proofs_score.tex`: Assumptions `as:compact`–`as:interior` (`:14-50`), the objectives `J`,
  `J^iid_{n,m}` (`:51-66`), the normality proof Steps 1–4 (`:204-294`; Step 1 `:206-212`, Step 2 and
  `eq:e-linear` `:214-279`), `prop:swor-score` (`:348-356`).
Imports the frozen Wave 28b statements (`jScore`, `jScoreIid`, `jPop`, `lossBar`; themselves built on the frozen
Wave 11b `jSwor`, `jIid`, `wScore`, Wave 24c `coverRho`, `ctxLawT`, `klPop` and Wave 24e `wPop`), not copied.
Mathlib's `TendstoInDistribution`, `TendstoInMeasure`, `TendstoUniformlyOn`, `deriv`, `gaussianReal`, `HasLaw`,
`variance` otherwise.

Covered:
* Step 1 (`score_hessian_ulln`): under `as:compact`–`as:smooth` (one-dimensional `θ`), `J ∈ C²(U)` on the ball
  `U = B(θ⋆, δ)`: `J` and `J'` are differentiable on `U` with `J''` continuous on `U`; every `J^iid_{n,m}` is twice
  differentiable on `U`; and almost surely `sup_{B̄(θ⋆, r)} |(J^iid_{n,m})'' − J''| → 0` for all `r < δ`
  ("after shrinking `U` to a compact neighbourhood").
* Step 2 (`score_linearization`): `eq:e-linear` as printed, multiplied by `√n`: there are bounded measurable
  `P₀`-centred `ψ_pool`, `ψ_val` with `√n (J^iid_{n,m})'(θ⋆) − (n^{−1/2} Σ_{i<n} ψ_pool(Z_i) + √n m^{−1}
  Σ_{i<m} ψ_val(Z̃_i)) → 0` in probability, for `θ⋆` a local minimiser of `J`, `m/n → κ ∈ (0, ∞)` and
  `√n(λ_{·,n} − λ_·) → 0` (the theorem's hypotheses).
* `thm:score`, asymptotic normality, `p = 1`, UNCONDITIONAL (`score_asymp_normal_uncond`): on `Θ = [a, b]` with
  `J` uniquely minimised at the interior `θ⋆` and `V = J''(θ⋆) > 0`, the exact minimisers `θ̂_n` of the
  without-replacement objective `J_{n,m}` satisfy `√n(θ̂_n − θ⋆) ⇝ N(0, (Σ_pool + κ⁻¹ Σ_val)/V²)`, where `ψ_pool`,
  `ψ_val` are influence functions of `J'_{n,m}(θ⋆)` (the linearisation holds for the without-replacement gradient)
  and `Σ_· = Var_{P₀} ψ_·`.

Not covered:
* Parameters in `ℝ^p`, `p ≥ 2` (Cramér–Wold, the matrix `V`, multivariate derivatives of the objective): GAP.
* The relabelling representative of `as:interior` (`J` is assumed uniquely minimised, as in Wave 28b).
* Closed forms of `ψ_pool`, `ψ_val` (the theorem only names them "the influence functions"; they are determined
  `P₀`-a.e. by the linearisation, and the limit law is stated in terms of them).

Encodings (to be checked by the critic):
* Objects: the frozen Wave 28b `jScore` (`J_{n,m}`, conditional Poisson contexts), `jScoreIid` (`J^iid_{n,m}`) and
  `jPop` (`J`), on the pool `x_0, …, x_{n−1}` and validation points `y_0, …, y_{m(n)−1}` of the sample paths, with
  penalty weights `λ_{cov,n}`, `λ_{KL,n}`. Derivatives are Mathlib's `deriv`; every conclusion that uses
  `deriv` also asserts (or is preceded by a hypothesis giving) the corresponding `HasDerivAt`, so no junk value of
  `deriv` enters.
* `as:smooth` (`p = 1`): `s : ℝ → 𝒵 → ℝ` with `s₋ ≤ s ≤ s₊` everywhere, `s` jointly continuous on `U × 𝒵`,
  `∂_θ s = s1`, `∂_θ s1 = s2` on `U` (pointwise in `z`), `s1`, `s2` jointly continuous on `U × 𝒵`. The printed
  Lipschitz conditions (on `K`, `L`, `z ↦ s_θ(z)` and its derivatives) and "`𝒵 ⊂` Euclidean space" are NOT assumed
  (they serve the Donsker step of the printed proof; the routes use second-moment bounds instead). Boundedness of
  `s1`, `s2` follows from continuity on compact sub-balls.
* `as:kernel`, `as:loss`: `K`, `L` continuous, `0 < K_min ≤ K ≤ K_max`; Steps 1–2 need no bound, sign or symmetry of
  `L` (compactness); the normality claim keeps `0 ≤ L ≤ B_L` and symmetry (the without-replacement transfer).
* Sampling (`as:compact`): `X, Y` each i.i.d. `P₀`; independence of the two path maps for Step 2 and normality;
  `m(n) → ∞` (Step 1), `m(n)/n → κ > 0` (Step 2, normality); penalties `λ_{·,n} → λ_·` (Step 1) and
  `√n(λ_{·,n} − λ_·) → 0` (Step 2, normality; printed in `thm:score`); `λ_{cov,n} ≥ 0` (normality).
* Step 1's almost-sure uniform convergence holds on one null set for all radii `r < δ` simultaneously (`∀ᵐ ω, ∀ r < δ`;
  the printed "after shrinking `U` to a compact neighbourhood").
* Step 2's conclusion also asserts that every `J^iid_{n,m}` is differentiable at `θ⋆` (so the `deriv` in the
  linearisation is the true gradient, not a junk value).
* Step 2's `θ⋆` is any local minimiser of `J` (`J(θ⋆) ≤ J(t)` on `U`), which gives `J'(θ⋆) = 0` (`∇J(θ⋆) = 0`
  in the printed proof).
* Normality: `θ̂_n` are measurable exact minimisers of `J_{n,m}` over `[a, b]` (as in Wave 28b);
  `V = deriv (deriv J) θ⋆ > 0` (`as:interior`); the limit is any `G` with law
  `N(0, ((Var ψ_pool + Var ψ_val/κ)/V²))` on any probability space; Mathlib's `TendstoInDistribution`.
* Junk values: `√n/m(n)` at `m(n) = 0` multiplies an empty sum; `J_{n,m}` is differentiable at `θ⋆` for all large
  `n` (asserted in the conclusion), so `deriv` takes its junk value only for finitely many `n`; the Gaussian variance is `≥ 0` before `toNNReal`;
  `jScoreIid` at `n = 0` is the constant `0` (all sums empty, `log 0 = 0`), differentiable. In the normality claim
  `V = deriv (deriv J) θ⋆` is the true second derivative: its hypotheses contain those of `score_hessian_ulln`,
  which proves `J ∈ C²(U)` (and a junk `deriv (deriv J) θ⋆ = 0` would contradict `0 < V`).

Drafter notes:
* All 3 claims are proved in `Wave28f/Route{Derivs,Step1,Step1b,Hessian,Linear,Meas,Normal}.lean`, collected in
  `Wave28f/Proofs.lean` (kernel dependencies: propext, Classical.choice, Quot.sound).
  New library: `Foundations/CLT/Hoeffding.lean` (Hoeffding decomposition of one-sample V-statistics,
  `E[(V_n f − θ − Σ_r P_n f_r)²] ≤ 4M⁴((2M+2)B)²/n²`), `Foundations/CLT/AsympLinear.lean` (convergence in probability
  toolkit; asymptotic linearity `IsAL` and its closure under sums, products, inverses — the delta method),
  `Foundations/CLT/PlugIn.lean` (conditional Chebyshev for two independent samples; the two-sample plug-in theorem;
  the two-sample V-statistic of degree `(1, M)` and the coverage ratio are `IsAL`), `Foundations/CLT/HessianULLN.lean`
  (uniform convergence of smooth functions of uniformly convergent pieces). Routes reuse the certified Wave 24c
  `compactGC_of_iid`, `e_ulln`, Wave 24e `vstat_ae`, `e_vstat`, Wave 28b `score_asymp_normal_cons`,
  `score_argmin_discharged` routes (with `jScoreIid_eq`, `risk_eq`) and WaveP1d `swor_derivs`.

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal NNReal Real

namespace StatFormal.Wave28f

open StatFormal.Wave28b

namespace Claims

/-- ICL `thm:score`, normality proof, Step 1, one-dimensional parameter: `J ∈ C²(U)`, `J^iid_{n,m}` is twice
differentiable on `U`, and almost surely (one null set for all radii) `(J^iid_{n,m})'' → J''` uniformly on every
closed ball `B̄(θ⋆, r)`, `r < δ`. -/
def score_hessian_ulln : Prop :=
  ∀ (M : ℕ) (sm sp Kmin Kmax lc lK θs δ : ℝ) (Z Ω : Type) [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (P0 : Measure Z)
    (X Y : ℕ → Ω → Z) (m : ℕ → ℕ) (s s1 s2 : ℝ → Z → ℝ) (L : Z → (Fin M → Z) → ℝ) (K : Z → Z → ℝ)
    (lcn lKn : ℕ → ℝ),
    1 ≤ M → 0 < sm → (∀ t x, sm ≤ s t x ∧ s t x ≤ sp) → 0 < δ →
    ContinuousOn (Function.uncurry s) (Metric.ball θs δ ×ˢ univ) →
    ContinuousOn (Function.uncurry s1) (Metric.ball θs δ ×ˢ univ) →
    ContinuousOn (Function.uncurry s2) (Metric.ball θs δ ×ˢ univ) →
    (∀ x, ∀ t ∈ Metric.ball θs δ, HasDerivAt (fun t => s t x) (s1 t x) t ∧
      HasDerivAt (fun t => s1 t x) (s2 t x) t) →
    Continuous (Function.uncurry L) → Continuous (Function.uncurry K) → 0 < Kmin →
    (∀ x y, Kmin ≤ K x y ∧ K x y ≤ Kmax) →
    (∀ i, Measurable (X i)) → iIndepFun X P → (∀ i, P.map (X i) = P0) →
    (∀ i, Measurable (Y i)) → iIndepFun Y P → (∀ i, P.map (Y i) = P0) →
    Tendsto m atTop atTop → Tendsto lcn atTop (𝓝 lc) → Tendsto lKn atTop (𝓝 lK) →
      (∀ t ∈ Metric.ball θs δ, HasDerivAt (jPop P0 s L K lc lK) (deriv (jPop P0 s L K lc lK) t) t ∧
        HasDerivAt (deriv (jPop P0 s L K lc lK)) (deriv (deriv (jPop P0 s L K lc lK)) t) t) ∧
      ContinuousOn (deriv (deriv (jPop P0 s L K lc lK))) (Metric.ball θs δ) ∧
      (∀ n ω, ∀ t ∈ Metric.ball θs δ,
        HasDerivAt (jScoreIid s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n))
          (deriv (jScoreIid s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n)) t) t ∧
        HasDerivAt (deriv (jScoreIid s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n)))
          (deriv (deriv (jScoreIid s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n))) t) t) ∧
      ∀ᵐ ω ∂P, ∀ r, r < δ →
        TendstoUniformlyOn
          (fun n => deriv (deriv (jScoreIid s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n))))
          (deriv (deriv (jPop P0 s L K lc lK))) atTop (Metric.closedBall θs r)

/-- ICL `thm:score`, normality proof, Step 2 (`eq:e-linear` times `√n`), one-dimensional parameter: the i.i.d.-context
gradient at a local minimiser `θ⋆` of `J` is asymptotically linear in the pool and the validation sample, with
bounded measurable centred influence functions (every `J^iid_{n,m}` is differentiable at `θ⋆`). -/
def score_linearization : Prop :=
  ∀ (M : ℕ) (sm sp Kmin Kmax κ lc lK θs δ : ℝ) (Z Ω : Type) [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (P0 : Measure Z)
    (X Y : ℕ → Ω → Z) (m : ℕ → ℕ) (s s1 s2 : ℝ → Z → ℝ) (L : Z → (Fin M → Z) → ℝ) (K : Z → Z → ℝ)
    (lcn lKn : ℕ → ℝ),
    1 ≤ M → 0 < sm → (∀ t x, sm ≤ s t x ∧ s t x ≤ sp) → 0 < δ →
    ContinuousOn (Function.uncurry s) (Metric.ball θs δ ×ˢ univ) →
    ContinuousOn (Function.uncurry s1) (Metric.ball θs δ ×ˢ univ) →
    ContinuousOn (Function.uncurry s2) (Metric.ball θs δ ×ˢ univ) →
    (∀ x, ∀ t ∈ Metric.ball θs δ, HasDerivAt (fun t => s t x) (s1 t x) t ∧
      HasDerivAt (fun t => s1 t x) (s2 t x) t) →
    Continuous (Function.uncurry L) → Continuous (Function.uncurry K) → 0 < Kmin →
    (∀ x y, Kmin ≤ K x y ∧ K x y ≤ Kmax) →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X P → iIndepFun Y P →
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) P → (∀ i, P.map (X i) = P0) → (∀ i, P.map (Y i) = P0) →
    0 < κ → Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ) →
    Tendsto lcn atTop (𝓝 lc) → Tendsto lKn atTop (𝓝 lK) →
    Tendsto (fun n : ℕ => √(n : ℝ) * (lcn n - lc)) atTop (𝓝 0) →
    Tendsto (fun n : ℕ => √(n : ℝ) * (lKn n - lK)) atTop (𝓝 0) →
    (∀ t ∈ Metric.ball θs δ, jPop P0 s L K lc lK θs ≤ jPop P0 s L K lc lK t) →
      (∀ n ω, HasDerivAt (jScoreIid s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n))
        (deriv (jScoreIid s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n)) θs) θs) ∧
      ∃ ψp ψv : Z → ℝ, Measurable ψp ∧ Measurable ψv ∧ (∃ C, ∀ z, |ψp z| ≤ C ∧ |ψv z| ≤ C) ∧
        ∫ z, ψp z ∂P0 = 0 ∧ ∫ z, ψv z ∂P0 = 0 ∧
        TendstoInMeasure P (fun (n : ℕ) ω =>
          √(n : ℝ) * deriv (jScoreIid s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n)) θs -
            ((√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, ψp (X i ω) +
              √(n : ℝ) / m n * ∑ i ∈ Finset.range (m n), ψv (Y i ω))) atTop 0

/-- ICL `thm:score`, asymptotic normality, one-dimensional parameter, UNCONDITIONAL: on `Θ = [a, b]` with `J` uniquely
minimised at the interior `θ⋆` and `V = J''(θ⋆) > 0`, there are bounded measurable centred influence functions
`ψ_pool`, `ψ_val` of the without-replacement gradient `J'_{n,m}(θ⋆)`, and the exact minimisers `θ̂_n` of `J_{n,m}`
satisfy `√n(θ̂_n − θ⋆) ⇝ N(0, (Var ψ_pool + κ⁻¹ Var ψ_val)/V²)`. -/
def score_asymp_normal_uncond : Prop :=
  ∀ (M : ℕ) (sm sp BL Kmin Kmax κ lc lK a b θs δ : ℝ) (Z Ω : Type) [MetricSpace Z] [CompactSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (P0 : Measure Z) (X Y : ℕ → Ω → Z) (m : ℕ → ℕ) (s s1 s2 : ℝ → Z → ℝ) (L : Z → (Fin M → Z) → ℝ)
    (K : Z → Z → ℝ) (lcn lKn : ℕ → ℝ) (θh : ℕ → Ω → ℝ),
    1 ≤ M → 0 < sm → (∀ t x, sm ≤ s t x ∧ s t x ≤ sp) → ContinuousOn (Function.uncurry s) (Icc a b ×ˢ univ) →
    0 < δ → Metric.ball θs δ ⊆ Icc a b →
    ContinuousOn (Function.uncurry s1) (Metric.ball θs δ ×ˢ univ) →
    ContinuousOn (Function.uncurry s2) (Metric.ball θs δ ×ˢ univ) →
    (∀ x, ∀ t ∈ Metric.ball θs δ, HasDerivAt (fun t => s t x) (s1 t x) t ∧
      HasDerivAt (fun t => s1 t x) (s2 t x) t) →
    Continuous (Function.uncurry L) → (∀ x t, 0 ≤ L x t ∧ L x t ≤ BL) →
    (∀ x t (σ : Equiv.Perm (Fin M)), L x (t ∘ σ) = L x t) →
    Continuous (Function.uncurry K) → 0 < Kmin → (∀ x y, Kmin ≤ K x y ∧ K x y ≤ Kmax) →
    (∀ n, 0 ≤ lcn n) → Tendsto lcn atTop (𝓝 lc) → Tendsto lKn atTop (𝓝 lK) →
    Tendsto (fun n : ℕ => √(n : ℝ) * (lcn n - lc)) atTop (𝓝 0) →
    Tendsto (fun n : ℕ => √(n : ℝ) * (lKn n - lK)) atTop (𝓝 0) →
    0 < κ → Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ) →
    (∀ θ ∈ Icc a b, (∀ θ' ∈ Icc a b, jPop P0 s L K lc lK θ ≤ jPop P0 s L K lc lK θ') → θ = θs) →
    0 < deriv (deriv (jPop P0 s L K lc lK)) θs →
    (∀ n, Measurable (θh n)) →
    (∀ n ω, θh n ω ∈ Icc a b ∧ ∀ t ∈ Icc a b, jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n)
      (lKn n) (θh n ω) ≤ jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n) t) →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X P → iIndepFun Y P →
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) P → (∀ i, P.map (X i) = P0) → (∀ i, P.map (Y i) = P0) →
      (∀ᶠ n in atTop, ∀ ω, HasDerivAt (jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n))
        (deriv (jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n)) θs) θs) ∧
      ∃ ψp ψv : Z → ℝ, Measurable ψp ∧ Measurable ψv ∧ (∃ C, ∀ z, |ψp z| ≤ C ∧ |ψv z| ≤ C) ∧
        ∫ z, ψp z ∂P0 = 0 ∧ ∫ z, ψv z ∂P0 = 0 ∧
        TendstoInMeasure P (fun (n : ℕ) ω =>
          √(n : ℝ) * deriv (jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n)) θs -
            ((√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, ψp (X i ω) +
              √(n : ℝ) / m n * ∑ i ∈ Finset.range (m n), ψv (Y i ω))) atTop 0 ∧
        ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P'] (G : Ω' → ℝ),
          HasLaw G (gaussianReal 0 (((Var[ψp; P0] + Var[ψv; P0] / κ) /
            deriv (deriv (jPop P0 s L K lc lK)) θs ^ 2).toNNReal)) P' →
          TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) * (θh n ω - θs)) atTop G (fun _ => P) P'

end Claims

end StatFormal.Wave28f
