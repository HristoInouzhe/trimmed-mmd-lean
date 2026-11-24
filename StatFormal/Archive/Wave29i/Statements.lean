import StatFormal.Archive.Wave28f.Statements
import StatFormal.Archive.Wave24c.Statements
import StatFormal.Archive.WaveP1d.Statements
import StatFormal.Archive.ICL.Statements
import StatFormal.Archive.Wave22c.Statements
import StatFormal.Archive.TrimmedMMD.BangBang.Statements
import StatFormal.Archive.TrimmedMMD.Concentration.Statements
import StatFormal.Archive.Wave17a.Statements
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Algebra.Order.Floor.Semiring
import StatFormal.Archive.Wave24d.Statements
import StatFormal.Archive.Wave26b.Statements
import StatFormal.Archive.Wave11b.Statements
import StatFormal.Archive.ICL.JointFull.Statements

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 29i: discharges of conditional/partial ICL and trimmed-MMD results —
# ICL `lem:e-ulln` (risk-term premise), `prop:swor-score` (transfer to `thm:score`), `cor:consistency` (pool
# reduction and approximation; `R⋆ ≤ R^{iid⋆}`), `prop:cps-gradient` (Frank–Wolfe gap with coverage);
# trimmed MMD `thm:split` (asymptotic normality, coverage and asymptotic level)

Sources (current texts, read 2026-10-20):
* ICL (`context-distribution-ICL/paper/v3/`): `lem:e-ulln` (`supp/proofs_score.tex:157-178`) with `J`, `J^iid_{n,m}`
  (`:51-66`); `prop:swor-score` (`supp/proofs_score.tex:350-356`, the "Transfer" paragraph `:397-413`); Step 1 and
  Step 2 of the normality proof (`:204-279`); `prop:cps-gradient` (`sections/06_estimation.tex:12-31`, the
  Frank–Wolfe paragraph `:57-63`) and the fixed-prompt paragraph `supp/proofs_main.tex:82-88` ("With coverage, the
  term `λ_cov M(c̄_P − c_ℓ)` is added inside the maximum … With `λ_KL > 0` the gap is infinite at every `w` with a
  zero coordinate"); `cor:consistency` and its proof (see the ICL `cor:consistency` bullets below).
* Trimmed MMD (`trimmed-mmd/paper.tex`): `thm:split` and its inputs (see the `thm:split` bullets below).
Imports the frozen `Wave28f` (through it `Wave28b` `jScore`, `jScoreIid`, `jPop`, `score_argmin_discharged`; `Wave11b`
`jSwor`, `jIid`, `lossSub`, `swor_value`; `Wave24c`, `Wave24e`), `Wave24c` (`e_ulln`, `empAvg`, `coverRho`,
`empCtxLaw`, `klEmp`, `ctxLawT`, `klPop`), `WaveP1d` (`swor_derivs`, `cps_fixed_prompt`), `ICL` (`esym`, `incl`,
`Grisk`, `Vrisk`, `InDeltaM`, `cps_gradient`), `Wave24d` (`devBound`, `icl_consistency`), `Wave26b` (`poolLaw`,
`riskIid`), `ICL/JointFull` (`devFull`), `Wave22c` (`split_level`), `TrimmedMMD/BangBang` (`capped`),
`TrimmedMMD/Concentration` (`region`), `Wave17a` (`sepVal`) statements, not copied; Mathlib otherwise.

Covered — ICL `lem:e-ulln`:
* `eulln_discharged`: `lem:e-ulln` UNCONDITIONAL: the frozen `e_ulln` conclusion at the concrete risk term (mechanical
  diff: `R`, `R_n` and the premise `∀ᵐ ω, R_n → R` removed, `as:loss` added; new ⇒ old: the first conjunct is the
  old conclusion with `R_n = J^iid_{n,m}|_{λ=0}`, `R = J|_{λ=0}`) and the lemma's display `sup_Θ |J^iid_{n,m} − J| → 0`
  on the frozen `jScoreIid`, `jPop`. The risk-term premise itself (route `eullnRisk`, the `λ = 0` instance of the
  second conjunct) follows from the frozen Wave 28b `score_argmin_discharged` (at `λ_cov = λ_KL = 0`, kernel `K ≡ 1`,
  `1/(n+1)`-minimisers) and the frozen Wave 11b `swor_value`. Close to a corollary of those two frozen claims (for
  `λ_{cov,n} ≥ 0`); it is stated because `lem:e-ulln` is a separately labelled lemma about `J^iid_{n,m}`, and it
  needs no sign on `λ_{cov,n}`.
Covered — ICL `prop:swor-score`, transfer (properties (b), (c) of the "Transfer" paragraph for `J_{n,m}`):
* `swor_hessian` ((b), Step 1 for `J_{n,m}`): eventually every `J_{n,m}` is twice differentiable on `U = B(θ⋆, δ)` and
  a.s. `sup_{B̄(θ⋆,r)} |J''_{n,m} − J''| → 0` for all `r < δ` (route: frozen Wave 28f `score_hessian_ulln` + frozen
  WaveP1d `swor_derivs`; not contained in any frozen claim, which state Step 1 for `J^iid_{n,m}` only).
* `swor_linear` ((c), Step 2 for `J_{n,m}`): the SAME bounded centred influence functions linearise
  `√n (J^iid_{n,m})'(θ⋆)` and `√n J'_{n,m}(θ⋆)` (route: frozen `score_linearization` + `swor_derivs`). Overlap: the
  `J'_{n,m}` linearisation is also a conjunct of the frozen Wave 28f `score_asymp_normal_uncond`, there under the extra
  hypotheses `Θ = [a, b]`, unique minimiser, `V > 0` and measurable exact minimisers; `swor_linear` drops them (only
  a local minimiser on `U`) and asserts that the SAME `ψ`'s serve both gradients. Property (a) is the frozen Wave 28b `score_argmin_discharged`, (d) and the normality conclusion for
  the minimiser of `J_{n,m}` the frozen Wave 28f `score_asymp_normal_uncond` (`p = 1`).
Covered — ICL `prop:cps-gradient`:
* `cps_cov_fixed_prompt`: at `w` uniform on a prompt `P`, `J_m = G + λ_cov Φ_m(π/M)` (frozen `jSwor`, `λ_KL = 0`):
  `c_k = ∂Φ_m/∂w̄_k` at `w̄ = π/M` (proved as a derivative), the partial derivatives `g_ℓ = 0` on `P`,
  `g_ℓ = M²(V_ℓ − G) + λ_cov M(c_ℓ − c̄_P)` off `P`, and the Frank–Wolfe gap
  `⟨w, g⟩ − min_ℓ g_ℓ = max_{ℓ ∉ P}(M²(G − V_ℓ) + λ_cov M(c̄_P − c_ℓ))_+`.
* `cps_kl_gap_infinite`: with `λ_KL > 0`, at `w ∈ Δ^(M)` with `w_ℓ = 0`, the right difference quotients of `J_m` in
  `w_ℓ` tend to `−∞`, and `J_m` has no partial derivative in `w_ℓ` there.
Covered — ICL `cor:consistency` and trimmed MMD `thm:split`: see the two blocks below.

Not covered (declared), ICL: `prop:swor-score` for `p ≥ 2` (the frozen derivative bounds are along lines; the
multivariate `thm:score` is Wave 29h) and the transfer to `cor:inference` (not formalised anywhere); `prop:cps-gradient`
the sampling/algorithm paragraphs and "fixed prompts are rest points" (a reading of the frozen `cps_fixed_prompt`).

Encodings (to be checked by the critic), ICL items 1, 2, 4:
* `eulln_*`: the frozen Wave 24c `e_ulln` setting; `as:loss` is `L` continuous on `𝒵 × 𝒵^M`, `0 ≤ L ≤ B_L`,
  symmetric, `M ≥ 1` (symmetry and `M ≥ 1` are used only by the swor route; the i.i.d. risk term does not need
  them). The risk term (`J^iid` at `λ = 0`) does not depend on `K`.
* `swor_*`: the frozen Wave 28f encodings (`p = 1`, `U = B(θ⋆, δ)`, `deriv` with `HasDerivAt` asserted) plus
  `as:loss` and `λ_{cov,n} ≥ 0` (needed by `swor_derivs`); the bounds `b₁`, `b₂` of `swor_derivs` come from
  continuity of `s'`, `s''` on compact sub-balls. `J''` is the genuine second derivative by the frozen
  `score_hessian_ulln` (`J ∈ C²(U)`).
* `cps_*`: weights on `Fin n`, partial derivatives as `HasDerivAt` of `t ↦ J_m(update w ℓ t)` (the rational function
  on `ℝⁿ`, as in the frozen `cps_gradient`); the mean risk is `G(w; L̄)`, `L̄(S) = m⁻¹ Σ_i L(z̃_i; z_S)`; `cpsPhiM`
  is the coverage term of `jSwor` as a function of the one-slot marginal; the gap is an `IsGreatest` of
  `{0} ∪ {…: ℓ ∉ P}` (finite maximum, `n ≥ M ≥ 1`); `K > 0` (paper: `K ≥ K_min > 0`).
* Junk values (items 1, 2, 4): `jScore` at `n < M` and `1/0` at `m = 0` only for finitely many `n`; coverages are
  `> 0`, so every `log` is genuine; `⨅` over a finite nonempty `Fin n`; `log (n t)` at `t > 0`; no `sInf`.

Drafter notes: all 15 claims are proved, in `Wave29i/Route{Eulln,Swor,Cps}.lean` (items 1, 2, 4),
`Route{Consist,ConsistBasic,ConsistPool,ConsistReduction,ConsistApprox,ConsistCompare}.lean` (`cor:consistency`) and
`RouteSplit.lean` (`thm:split`), collected in `Wave29i/Proofs.lean`; kernel dependencies `propext`,
`Classical.choice`, `Quot.sound`. New libraries `Foundations/SworLaw` and `Foundations/TrimmedMean`.
Manuscript notes (item 4): the printed "the term `λ_cov M(c̄_P − c_ℓ)` is added inside the maximum" of
`M² max_{ℓ∉P}(G − V_ℓ)_+` is ambiguous: read literally (inside the bracket multiplied by `M²`) it is off by `M²`;
the correct gap is `max_{ℓ∉P}(M²(G − V_ℓ) + λ_cov M(c̄_P − c_ℓ))_+` (Lean `cps_cov_fixed_prompt`), i.e.
`M² max_{ℓ∉P}(G − V_ℓ + λ_cov (c̄_P − c_ℓ)/M)_+`; suggest printing the formula.

## ICL `cor:consistency` (pool reduction and approximation discharged)
Sources (`context-distribution-ICL/paper/v3/`, read 2026-10-20):
* `cor:consistency` (`sections/06_estimation.tex:107-113`), with `R(μ) = 𝒜(μ) + λ_cov Φ(μ)`, `R⋆`, `R^{iid⋆}`
  (`:101-105`), `thm:joint` (`:76-88`), `cor:oracle` (`:96-100`); proof `supp/proofs_main.tex:127-160`
  (Reduction, Approximation: quantiser `q_n`, collisions, risk, coverage; Comparison).
* `Π_μ = μ^{⊗M}(· | D_M)`, `G_μ`, symmetric `L` (`sections/03_framework.tex:14-28`), mean risk (`:34`),
  `μ_w`, `Δ^(M)`, the conditional Poisson law `Π_w`, `J_m`, `J_pool` (`:56-75`); coverage `ρ_μ` at the one-slot
  marginal `Π̄_μ` of `Π_μ`, `Φ` (`sections/04_selector.tex:1-14`); the i.i.d. objective (`supp/iid.tex:9-20`).
Imports the frozen `Wave24d` (`devBound`, `icl_consistency`), `Wave26b` (`poolLaw`, `riskIid`), `Wave11b`
(`distinctSet`, `ctxLaw`, `Admissible`, `jSwor`; through it `ICL` `InDeltaM`, `ICL/Diag` `klUnif`), `Wave20a`
(`PhiC`, through `Wave26b`) and `ICL/JointFull` (`devFull`) statements.

Covered:
* `cor:consistency`, first claim: `consist_risk` (in full, no conditional premise): `R⋆` is a genuine infimum
  (`IsGLB`, the class is nonempty and bounded below), and for almost every nested pool sequence, any
  `ε_opt`-minimiser `ŵ` of `J_m` over `Δ^(M)` has `R(μ_ŵ) → R⋆` in probability.
* The two premises of the frozen conditional `Wave24d.icl_consistency`, discharged: `consist_reduction` (on the
  almost-sure pool event: every `μ_w`, `w ∈ Δ^(M)`, is admissible; `J_m(w) − (R(μ_w) + λ_KL KL(w|u_n))` is the
  `thm:joint` deviation of the ordered conditional Poisson law `Π°_w` on `[n]^M`, i.e. `J_pool(w) = R(μ_w) +
  λ_KL KL(w|u_n)`; `0 ≤ KL ≤ log n`; the oracle event of probability `≥ 1 − 1/m`), `consist_approx`
  (`limsup_n inf_{Δ^(M)} R(μ_w) ≤ R⋆` almost surely); the route `consist_check`
  (`icl_consistency → consist_reduction → consist_approx → consist_risk`, not a target) assembles them.
* `cor:consistency`, second claim: `consist_compare` (`R⋆ ≤ R^{iid⋆}` for `L` continuous on `𝒵 × 𝒵^M`).

Not covered (declared):
* `𝒜 = CVaR_α` and weighted risks (the corollary assumes the mean risk). The sentence after the corollary ("can be
  strictly better", the diagonal-jump discussion; informal, referring to `supp:iid`).

Encodings:
* `𝒵` compact metric with its Borel σ-algebra; `P₀` without atoms: `∀ x, P₀ {x} = 0`. `L : 𝒵 → 𝒵^M → [0, B_L]`
  (`𝒵^M = Fin M → 𝒵`), continuous on `𝒵 × D_M` (`ContinuousOn` on `univ ×ˢ distinctSet M`; no measurability of
  `L` off `D_M` is assumed: `Π_μ` and the pool contexts never see it), symmetric in the slots (the standing
  `03_framework.tex:14`; needed for `J_m` on `M`-subsets, the frozen `jSwor` lists `z_S` in index order). `K`
  continuous, `K_min ≤ K ≤ K_max`, `0 < K_min`; `λ_cov ≥ 0`; `M ≥ 1` (fixed).
* `Π_μ` = frozen `ctxLaw` (Mathlib `cond`); its one-slot marginal `Π̄_μ = M⁻¹ Σ_s (Π_μ)∘ev_s⁻¹` (`consistMarg`,
  `ev_s` measurable, so no junk `map`; it is the slot-average, as the frozen `JointFull.oneSlot`, and equals each
  slot marginal by exchangeability); `G_μ(z) = ∫ L(z; t) dΠ_μ(t)` (`consistG`); `R(μ) = ∫ G_μ dP₀ + λ_cov Φ(Π̄_μ)`
  with `Φ` = frozen `PhiC` (`consistRisk`). The class of `R⋆` is the frozen `Admissible` (`μ ∈ 𝒫(supp P₀)`,
  `μ^{⊗M}(D_M) > 0`) (`consistClass`).
* The pool is the first `n_j` points of an i.i.d. `P₀` sequence on `(Ω₀, Q)` (nested pools); `μ_w` the frozen
  `poolLaw`; `J_m` the frozen `jSwor` (free simplex, mean risk, coverage at `π/M`, `λ_KL KL(w|u_n)`); `ŵ_j(ω)` any
  `ε_opt,j`-minimiser over `Δ^(M)` (`InDeltaM`), stated as `J_m(ŵ) ≤ J_m(w) + ε_opt` for all `w ∈ Δ^(M)` (no
  infimum). All per-`j` hypotheses on `ŵ`, `λ_KL`, `ε_opt` are required only for all large `j` (an asymptotic
  claim; Wave 26b required them for every `j`). The validation probability space, sample, schedules and `ŵ` are
  quantified after the pool (conditionally on the pool), as in Wave 26b; "in probability" is `TendstoInMeasure`
  (outer probability; no measurability of `ŵ` needed).
* `consist_reduction`: `Π°_w(t) = Π_s w_{t_s} 1{t injective}/(1 − p(w))` (`consistOrdLaw`, `p` the frozen
  `collision`), the deployed objective `J_pool(w) := J_m(w) − devFull(Π°_w)` (the frozen `thm:joint` deviation:
  `devFull` = `J_m − J_pool` for the law `Π°_w`, with `L_t = L(·; z∘t)`, `k_j = K(·, z_j)`); the oracle event in
  the form "`R(μ_ŵ) ≤ R(μ_w) + λ_KL log n + ε_opt + 2 dev_{m,n,1/m}` for all `w ∈ Δ^(M)`" (no `sInf`), for every
  `n ≥ 2`, `m ≥ 2`. `consist_approx`: "`∀ε>0`, all large `n` have `w ∈ Δ^(M)` with `R(μ_w) ≤ R⋆ + ε`".
* `consist_compare`: `R^{iid⋆}` any `IsGLB` of the frozen Wave 26b class `{R^iid(μ) : μ ∈ 𝒫(supp P₀)}` (Wave 26b
  proves it is attained; `IsGLB` is the weaker hypothesis).

Junk-value audit:
* `ctxLaw μ` is the zero measure when `μ^{⊗M}(D_M) = 0` (`cond`); `R` is only ever used on `Admissible` laws (in
  `consistClass`) or on `μ_ŵ`, `ŵ ∈ Δ^(M)`, which are admissible on the pool event (`consist_reduction`).
* `R⋆` is `IsGLB`, never `sInf`; the class is nonempty (`P₀`) and bounded below (`−λ_cov log K_max`), proved in
  `consist_risk`. No `sInf` in any claim (the frozen premise's `A_j = inf_w R(μ_w)` is instantiated in the route
  with a nonempty, bounded-below set).
* `map` only along measurable evaluations; `ρ_μ ∈ [K_min, K_max]`, so `log ρ` is genuine; `ℕ` subtraction none;
  `1/m`, `log n/m` with `m → ∞` stated; `devBound` at `δ = 1/m` used only for `m ≥ 2`.
* Integrals: `G_μ`, `ρ_μ` are continuous bounded functions of the query for admissible `μ` (proved), so the
  `P₀`-integrals are genuine.

Drafter notes:
* All 4 claims proved (no conditional premise): `consist_reduction` in `Wave29i/RouteConsistReduction.lean`,
  `consist_approx` in `RouteConsistApprox.lean`, the route `consist_check` and `consist_risk` (= `consist_check` applied to the
  frozen `Wave24d.icl_consistency` and the two discharges) in `RouteConsist.lean`, `consist_compare` in
  `RouteConsistCompare.lean` (with `RouteConsist{Basic,Pool}.lean`); axioms `propext`, `Classical.choice`,
  `Quot.sound`. Reused certified results: `ICL/JointFull` `joint_full` (`thm:joint`, `δ = 1/m`), `ICL/Diag` `oracle`
  (`cor:oracle`), `Wave11b` `swor_cps` (`Π_w` = conditioned i.i.d. index law up to order; `π/M` its one-slot
  marginal), `Wave24d` `icl_consistency`, `Wave20a` `phi_continuous` (through the Wave 26b route), and the Wave 26b
  route lemmas (pool event, cells, `R^iid` weak continuity).
* New library `Foundations/SworLaw` (`Basic`: atomless laws do not charge the diagonal, i.i.d. atomless sequences are
  injective a.s., finite Dirac sums under `cond` and `Measure.pi`, continuity in the query of `∫ L(x, ·) dΠ` for `Π`
  carried by the open `D_M`; `Quantise`: stability of `μ^{⊗M}(· | D_M)` under collision-preserving quantisers).
* Manuscript remarks (none changes the statement): (1) the reduction needs `L` symmetric (standing,
  `03_framework.tex:14`) to identify `J_m` on `M`-subsets with the ordered law `Π°_w` on `[n]^M`, and, since `L` is
  only continuous on `𝒵 × D_M`, `thm:joint` must be applied to a loss that is measurable on all of `[n]^M`: the
  route uses `L(·; z∘t)` on injective `t` and `0` elsewhere (`Π°_w` does not charge the latter); the printed
  `thm:joint` assumes `0 ≤ L ≤ B_L` measurable for every index tuple, a presentation gap. (2) The pointwise
  convergence in the "Risk" step holds for tuples in `(supp P₀)^M` only (where `d(q_n z, z) ≤ ε_n`), i.e.
  `μ^{⊗M}`-a.e.; the "Coverage" step needs `ρ_{μ_n} ∈ [K_min, K_max]`, true only once `μ_n^{⊗M}(D_M) > 0` (for
  large `n`), so bounded convergence is applied eventually. (3) `thm:joint` at `δ = 1/m` needs `n, m ≥ 2`, so
  premise (1) holds only for large `j` (as noted at Wave 24d). (4) The quantiser of the route uses the cells
  `B(z_i, δ) \ ⋃_{j<i} B(z_j, δ)` instead of nearest-point cells; the paper's argument goes through verbatim.

## Trimmed MMD `thm:split` (asymptotic level)
Sources (`trimmed-mmd/paper.tex`, current text): `eq:witness` (`:1131-1137`), `eq:splitstat` (`:1140-1151`),
`ass:split` (`:1153-1160`), `thm:split` (`:1162-1176`); `ass:regularity` (`:545-560`); `lem:trimmedmean`
(`:1100-1120`, frozen `BangBang.trimmedmean_value`); proof `supplement.tex` §`supp:split` (from `:361`, proof of `thm:split` after `lem:trimmedmean`).
Imports the frozen `Wave22c` (`split_level`), `TrimmedMMD/BangBang` (`capped`, `cap`), `TrimmedMMD/Concentration`
(`region`), `Wave17a` (`sepVal`) statements and `Distances` (`tvDist`, through Wave22c), not copied; Mathlib otherwise.

Covered:
* `split_pop_trimmed`: the population terms of `sep(f; 𝒞_α(P), 𝒞_α(Q))` are trimmed means (Rockafellar–Uryasev):
  for any `β`-quantile `q` of `h = ⟨f, φ⟩` under `P` and any `α`-quantile `q'` under `Q` (`β = 1 − α`),
  `inf_{𝒞_α(P)} ⟨f,·⟩ = q − β⁻¹ P(q − h)_+`, `sup_{𝒞_α(Q)} ⟨f,·⟩ = q' + β⁻¹ Q(h − q')_+`, so `sep` is the real
  `T₀ = L(P) − U(Q)`. All `α ∈ [0,1)`.
* `split_ass_unique`: the density form of `ass:split` (one side, level `p`) implies that the quantile is unique
  (`splitUQ`) and, for `p < 1`, `Var_P((q − h)_+) > 0`.
* `split_asymp_normal`: `√n (T̂_n − T₀) ⇝ N(0, σ²)`, `σ² = [Var_P (q − h)_+ + Var_Q (h − q')_+ / κ]/β²`, under
  quantile UNIQUENESS only (generalisation of `ass:split`: Stigler's condition, atoms allowed).
* `split_coverage`: with the plug-in standard error `ŝe_n` (`splitSE`: influence-function variances at the
  empirical quantiles) and `σ² > 0`: `P(T̂_n − z ŝe_n ≤ sep) → Φ(z)` for every real `z`.
* `split_level_boot`: for ANY measurable standard error `ŝe'_n` with `ŝe'_n / se_n → 1` in probability
  (`se_n = σ/√n`), under `ass:regularity`, `ass:split` (density form, both sides), `0 < α < 1`: coverage
  `liminf P(T̂_δ ≤ sep) ≥ 1 − δ`, asymptotic level `δ` of "reject if `T̂_δ > 0`" under `H_{0,α}`, and rejection on
  the coverage event certifies `TV(P,Q) > α`; `T̂_δ = T̂_n − z ŝe'_n`, `Φ(Ioi z) = δ`. CONDITIONAL only on the
  consistency of `ŝe'` (what the bootstrap must deliver).
* `split_level_discharged`: the same, UNCONDITIONAL, for the concrete plug-in `ŝe_n = splitSE`.
  Route `split_check` (not a target): frozen `Wave22c.split_level` + `split_coverage` ⇒ `split_level_discharged`.

Not covered (declared):
* Bootstrap consistency (the printed variance estimator / percentile bootstrap); only the conditional
  `split_level_boot` and the plug-in replacement are stated.
* `α = 0` (plain means): the density form of `ass:split` is unsatisfiable there (no positive density above the
  `1`-quantile), and `splitUQ` at level `1` (and at level `0`, the `Q` side) is unsatisfiable, so
  `split_asymp_normal` and `split_coverage`, although stated for `0 ≤ α`, say nothing at `α = 0`; the `α = 0` CLT
  (sample means) is not stated. `split_pop_trimmed` holds at `α = 0`.
* Only the ratio regime `m(n)/n → κ ∈ (0,∞)` (specialisation of "`n₂, m₂ → ∞`").
* The first fold / `eq:witness`: `f̂ = f` is a fixed element of `H` (the theorem conditions on the first fold);
  `‖f‖ ≤ 1` is not needed. `cor:lower` is not stated.

Encodings:
* `ℋ` real Hilbert space, `φ` strongly measurable with `‖φ x‖ ≤ κ'` (`ass:regularity` (A1); (A2), (A3) unused);
  `h x = ⟪f, φ x⟫`. Samples: `X, Y : ℕ → Ω → 𝒳` on one probability space, each measurable, `iIndepFun`, laws
  `μ.map (X i) = P` (maps guarded by measurability), the two families independent (`IndepFun` of the sequences);
  second-fold sizes `n` and `m n`.
* `T̂_n = splitStat` = `splitTrimLo n α (h(X_0..X_{n−1})) − splitTrimUp (m n) α (h(Y_0..))`, where
  `splitTrimLo/Up = inf/sup_{w ∈ capped n α} Σ w_i v_i` (`eq:splitstat` via `lem:trimmedmean`).
* `splitOrdStat k v = min_{|S|=k} max_{i∈S} v_i` (the `k`-th order statistic), `splitQuantLo = v_{(⌈nβ⌉)}`;
  `splitVarLo = P_n g_ĉ² − (P_n g_ĉ)²`, `g_c(y) = (c − y)_+`; the upper side uses `−v`;
  `splitSE n m α vx vy = √(V̂_X/n + V̂_Y/m)/β`.
* `splitUQ P h p q`: `P(h<q) ≤ p ≤ P(h≤q)`, `P(h < q−d) < p < P(h ≤ q+d)` for all `d > 0`.
  `splitAss P h p q` (`ass:split`, one side): `q` a `p`-quantile and a measurable `ρ > 0` on `(q−ε, q+ε)` with
  `P(h ∈ (a,b]) = ∫⁻_{(a,b]} ofReal ρ` there (lintegral: no integrability junk). Used as `splitAss P h (1−α) q`
  (the `(1−α)`-quantile under `P`) and `splitAss Q h α q'` (the `α`-quantile under `Q`), as printed.
* `⇝` is Mathlib `TendstoInDistribution` to `id` under `gaussianReal 0 σ²`; `Φ(z) = (gaussianReal 0 1).real (Iic z)`;
  `ŝe'/se → 1` is `TendstoInMeasure` to the constant `1`; level as in frozen `split_level`.

Junk-value audit: `sInf/sSup` over `capped n α` are genuine (nonempty compact) for `n ≥ 1`; at `n = 0` they are
`0` (only finitely many `n`, asymptotic claims). `splitOrdStat` with `1 ≤ k ≤ n` is a genuine finite min-max
(`⌈nβ⌉ ∈ [1, n]` for `n ≥ 1`, `α ∈ [0,1)`). Divisions by `n`, `m n`, `1 − α`, `κ`, `√n` are nonzero eventually
(or by hypothesis); `√` of the plug-in is of a nonnegative quantity only asymptotically — the claims are
asymptotic and `√` of a negative is `0`, harmless (proved consistent regardless). `sepVal` is identified as a real
(no `EReal` `⊤ − ⊤`). `Var` of bounded measurable functions is genuine. `toNNReal` of `σ² ≥ 0` is faithful.

Drafter notes: the asymptotic-linearity step avoids empirical-process theory: a deterministic inequality
`0 ≤ β(L_n − L) + (P_n − P)g_q ≤ d·(|F_n(q) − F(q)| + |F_n(q−) − F(q−)|)` on `{F_n(q+d) ≥ β ≥ F_n((q−d)−)}` plus
Chebyshev, letting `d ↓ 0` after `n → ∞`.

Critic notes (wave 29i fidelity pass):
* The drafted `*_check` claims (`eulln_risk_check`, `eulln_check`, `swor_hessian_check`, `swor_linear_check`,
  `consist_check`, `split_check`, all "frozen + discharge ⇒ new") were removed from `Claims`: each new conclusion is
  itself certified unconditionally, so each implication is provable by discarding its hypotheses and certifies
  nothing. They remain route theorems (`eulln_discharged_of`, `swor_hessian_of`, `swor_linear_of`, `consist_check`,
  `split_check`), and `Proofs.lean` checks them against the frozen claims, not as targets. `eulln_risk` was moved to the
  route (`eullnRisk`) too: it is the `λ ≡ 0`, `K ≡ 1` instance of the second conjunct of `eulln_discharged`.
* `splitAss` is satisfiable: `RouteSplit.splitAss_uniform` proves it for the uniform law on `[0, 1]`, `h = id`,
  `p = q = 1/2`. The hypotheses of `split_level_boot` are then met with `P = Q` that law (through a clamped `φ`),
  `0 < α < 1`, and the oracle `se_n = σ/√n`.

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

noncomputable section

namespace StatFormal.Wave29i

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal NNReal Real


open StatFormal.Wave28b

/-! ### ICL `prop:cps-gradient`: objects -/

section CPS
variable {Z : Type*} {n m : ℕ}

/-- The empirical coverage functional at a one-slot marginal `w̄`:
`Φ_m(w̄) = −m⁻¹ Σ_i log Σ_l w̄_l K(z̃_i, z_l)` (the coverage term of the frozen Wave 11b `jSwor` is
`λ_cov Φ_m(π/M)`). -/
def cpsPhiM (K : Z → Z → ℝ) (z : Fin n → Z) (zt : Fin m → Z) (wbar : Fin n → ℝ) : ℝ :=
  -(1 / (m : ℝ)) * ∑ i, Real.log (∑ l, wbar l * K (zt i) (z l))

end CPS

namespace Claims

/-! ### ICL `lem:e-ulln` -/

/-- ICL `lem:e-ulln`, with the risk-term premise of the frozen Wave 24c `e_ulln` DISCHARGED: under
`as:compact`–`as:loss`, `n, m → ∞` and `λ_{·,n} → λ_·`, almost surely the frozen `e_ulln` conclusion holds for the
concrete risk term (`R_n = J^iid_{n,m}` at `λ = 0`, `R = J` at `λ = 0`), and `sup_Θ |J^iid_{n,m} − J| → 0` (the
lemma's display, on the frozen Wave 28b `jScoreIid`, `jPop`). -/
def eulln_discharged : Prop :=
  ∀ (Θ Z Ω : Type) [MetricSpace Θ] [CompactSpace Θ] [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] [MeasurableSpace Ω] (P : Measure Ω) (P0 : Measure Z) (M : ℕ) (X Y : ℕ → Ω → Z) (m : ℕ → ℕ)
    (s : Θ → Z → ℝ) (L : Z → (Fin M → Z) → ℝ) (K : Z → Z → ℝ) (sm sp BL Kmin Kmax : ℝ)
    (lc lK : ℝ) (lcn lKn : ℕ → ℝ),
    IsProbabilityMeasure P0 → Continuous (Function.uncurry s) → 0 < sm → (∀ θ z, sm ≤ s θ z ∧ s θ z ≤ sp) →
    Continuous (Function.uncurry K) → 0 < Kmin → (∀ z z', Kmin ≤ K z z' ∧ K z z' ≤ Kmax) →
    1 ≤ M → Continuous (Function.uncurry L) → (∀ z t, 0 ≤ L z t ∧ L z t ≤ BL) →
    (∀ z t (σ : Equiv.Perm (Fin M)), L z (t ∘ σ) = L z t) →
    Tendsto m atTop atTop → IsProbabilityMeasure P →
    (∀ j, Measurable (X j)) → iIndepFun X P → (∀ j, P.map (X j) = P0) →
    (∀ j, Measurable (Y j)) → iIndepFun Y P → (∀ j, P.map (Y j) = P0) →
    Tendsto lcn atTop (𝓝 lc) → Tendsto lKn atTop (𝓝 lK) →
      ∀ᵐ ω ∂P,
        TendstoUniformly
          (fun n θ => jScoreIid s L K (fun i => X i ω) (fun i => Y i ω) n (m n) 0 0 θ -
              lcn n * StatFormal.Wave24c.empAvg (fun i => Y i ω) (m n)
                (fun z => Real.log (StatFormal.Wave24c.coverRho K
                  (StatFormal.Wave24c.empCtxLaw s (fun i => X i ω) n θ) z)) +
            lKn n * StatFormal.Wave24c.klEmp s (fun i => X i ω) n θ)
          (fun θ => jPop P0 s L K 0 0 θ -
              lc * ∫ z, Real.log (StatFormal.Wave24c.coverRho K (StatFormal.Wave24c.ctxLawT P0 s θ) z) ∂P0 +
            lK * StatFormal.Wave24c.klPop P0 s θ) atTop ∧
        TendstoUniformly (fun n => jScoreIid s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n))
          (jPop P0 s L K lc lK) atTop

/-! ### ICL `prop:swor-score`, the transfer to `thm:score` -/

/-- `prop:swor-score`, transfer (b) (Step 1 for the without-replacement objective), one-dimensional parameter:
under the hypotheses of the frozen Wave 28f `score_hessian_ulln` and `as:loss` (`0 ≤ L ≤ B_L`, symmetric),
`λ_{cov,n} ≥ 0`: for all large `n`, every `J_{n,m}` is twice differentiable on `U = B(θ⋆, δ)`, and almost surely
`sup_{B̄(θ⋆, r)} |J''_{n,m} − J''| → 0` for every `r < δ`. -/
def swor_hessian : Prop :=
  ∀ (M : ℕ) (sm sp BL Kmin Kmax lc lK θs δ : ℝ) (Z Ω : Type) [MetricSpace Z] [CompactSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (P0 : Measure Z) (X Y : ℕ → Ω → Z) (m : ℕ → ℕ) (s s1 s2 : ℝ → Z → ℝ) (L : Z → (Fin M → Z) → ℝ)
    (K : Z → Z → ℝ) (lcn lKn : ℕ → ℝ),
    1 ≤ M → 0 < sm → (∀ t x, sm ≤ s t x ∧ s t x ≤ sp) → 0 < δ →
    ContinuousOn (Function.uncurry s) (Metric.ball θs δ ×ˢ univ) →
    ContinuousOn (Function.uncurry s1) (Metric.ball θs δ ×ˢ univ) →
    ContinuousOn (Function.uncurry s2) (Metric.ball θs δ ×ˢ univ) →
    (∀ x, ∀ t ∈ Metric.ball θs δ, HasDerivAt (fun t => s t x) (s1 t x) t ∧
      HasDerivAt (fun t => s1 t x) (s2 t x) t) →
    Continuous (Function.uncurry L) → (∀ x t, 0 ≤ L x t ∧ L x t ≤ BL) →
    (∀ x t (σ : Equiv.Perm (Fin M)), L x (t ∘ σ) = L x t) →
    Continuous (Function.uncurry K) → 0 < Kmin → (∀ x y, Kmin ≤ K x y ∧ K x y ≤ Kmax) →
    (∀ i, Measurable (X i)) → iIndepFun X P → (∀ i, P.map (X i) = P0) →
    (∀ i, Measurable (Y i)) → iIndepFun Y P → (∀ i, P.map (Y i) = P0) →
    Tendsto m atTop atTop → (∀ n, 0 ≤ lcn n) → Tendsto lcn atTop (𝓝 lc) → Tendsto lKn atTop (𝓝 lK) →
      (∀ᶠ n in atTop, ∀ ω, ∀ t ∈ Metric.ball θs δ,
        HasDerivAt (jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n))
          (deriv (jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n)) t) t ∧
        HasDerivAt (deriv (jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n)))
          (deriv (deriv (jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n))) t) t) ∧
      ∀ᵐ ω ∂P, ∀ r, r < δ →
        TendstoUniformlyOn
          (fun n => deriv (deriv (jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n))))
          (deriv (deriv (jPop P0 s L K lc lK))) atTop (Metric.closedBall θs r)

/-- `prop:swor-score`, transfer (c) (Step 2 for the without-replacement objective), one-dimensional parameter: under
the hypotheses of the frozen Wave 28f `score_linearization` and `as:loss`, `λ_{cov,n} ≥ 0`, there are bounded
measurable `P₀`-centred `ψ_pool`, `ψ_val` that are influence functions of BOTH gradients at the local minimiser
`θ⋆`: `√n (J^iid_{n,m})'(θ⋆)` and `√n J'_{n,m}(θ⋆)` are each the linear statistic plus `o_P(1)`; every `J_{n,m}` with
`n` large is differentiable at `θ⋆`. -/
def swor_linear : Prop :=
  ∀ (M : ℕ) (sm sp BL Kmin Kmax κ lc lK θs δ : ℝ) (Z Ω : Type) [MetricSpace Z] [CompactSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (P0 : Measure Z) (X Y : ℕ → Ω → Z) (m : ℕ → ℕ) (s s1 s2 : ℝ → Z → ℝ) (L : Z → (Fin M → Z) → ℝ)
    (K : Z → Z → ℝ) (lcn lKn : ℕ → ℝ),
    1 ≤ M → 0 < sm → (∀ t x, sm ≤ s t x ∧ s t x ≤ sp) → 0 < δ →
    ContinuousOn (Function.uncurry s) (Metric.ball θs δ ×ˢ univ) →
    ContinuousOn (Function.uncurry s1) (Metric.ball θs δ ×ˢ univ) →
    ContinuousOn (Function.uncurry s2) (Metric.ball θs δ ×ˢ univ) →
    (∀ x, ∀ t ∈ Metric.ball θs δ, HasDerivAt (fun t => s t x) (s1 t x) t ∧
      HasDerivAt (fun t => s1 t x) (s2 t x) t) →
    Continuous (Function.uncurry L) → (∀ x t, 0 ≤ L x t ∧ L x t ≤ BL) →
    (∀ x t (σ : Equiv.Perm (Fin M)), L x (t ∘ σ) = L x t) →
    Continuous (Function.uncurry K) → 0 < Kmin → (∀ x y, Kmin ≤ K x y ∧ K x y ≤ Kmax) →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X P → iIndepFun Y P →
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) P → (∀ i, P.map (X i) = P0) → (∀ i, P.map (Y i) = P0) →
    0 < κ → Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ) →
    (∀ n, 0 ≤ lcn n) → Tendsto lcn atTop (𝓝 lc) → Tendsto lKn atTop (𝓝 lK) →
    Tendsto (fun n : ℕ => √(n : ℝ) * (lcn n - lc)) atTop (𝓝 0) →
    Tendsto (fun n : ℕ => √(n : ℝ) * (lKn n - lK)) atTop (𝓝 0) →
    (∀ t ∈ Metric.ball θs δ, jPop P0 s L K lc lK θs ≤ jPop P0 s L K lc lK t) →
      (∀ᶠ n in atTop, ∀ ω, HasDerivAt (jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n))
        (deriv (jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n)) θs) θs) ∧
      ∃ ψp ψv : Z → ℝ, Measurable ψp ∧ Measurable ψv ∧ (∃ C, ∀ z, |ψp z| ≤ C ∧ |ψv z| ≤ C) ∧
        ∫ z, ψp z ∂P0 = 0 ∧ ∫ z, ψv z ∂P0 = 0 ∧
        TendstoInMeasure P (fun (n : ℕ) ω =>
          √(n : ℝ) * deriv (jScoreIid s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n)) θs -
            ((√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, ψp (X i ω) +
              √(n : ℝ) / m n * ∑ i ∈ Finset.range (m n), ψv (Y i ω))) atTop 0 ∧
        TendstoInMeasure P (fun (n : ℕ) ω =>
          √(n : ℝ) * deriv (jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n)) θs -
            ((√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, ψp (X i ω) +
              √(n : ℝ) / m n * ∑ i ∈ Finset.range (m n), ψv (Y i ω))) atTop 0

/-! ### ICL `prop:cps-gradient`, the Frank–Wolfe gap with coverage -/

/-- `prop:cps-gradient`, the fixed-prompt Frank–Wolfe gap WITH COVERAGE (`supp/proofs_main.tex`, paragraph after
the proof): let `w` be uniform on a prompt `P` (`|P| = M`), `J_m = G + λ_cov Φ_m(π/M)` (frozen Wave 11b `jSwor`,
mean risk `G` over the `m` validation queries, `λ_KL = 0`), `w̄ = π/M` the one-slot marginal,
`c_k = ∂Φ_m/∂w̄_k` at `w̄` and `c̄_P = M⁻¹ Σ_{k ∈ P} c_k`. Then the partial derivatives of `J_m` at `w` are `g_ℓ = 0` on
`P` and `g_ℓ = M²(V_ℓ − G) + λ_cov M (c_ℓ − c̄_P)` off `P`, and the gap `⟨w, g⟩ − min_ℓ g_ℓ` equals
`max_{ℓ ∉ P} (M²(G − V_ℓ) + λ_cov M (c̄_P − c_ℓ))_+`. -/
def cps_cov_fixed_prompt : Prop :=
  ∀ (Z : Type) (n M m : ℕ) (P : Finset (Fin n)) (z : Fin n → Z) (zt : Fin m → Z) (L : Z → (Fin M → Z) → ℝ)
    (K : Z → Z → ℝ) (lcov : ℝ), 1 ≤ M → P.card = M → (∀ x y, 0 < K x y) →
    let w : Fin n → ℝ := fun j => if j ∈ P then 1 / (M : ℝ) else 0
    let Lb : Finset (Fin n) → ℝ := fun S => (1 / (m : ℝ)) * ∑ i, StatFormal.Wave11b.lossSub L (zt i) z S
    let wbar : Fin n → ℝ := fun l => StatFormal.ICL.incl w M l / M
    let c : Fin n → ℝ := fun k => -(1 / (m : ℝ)) * ∑ i, K (zt i) (z k) / ∑ l, wbar l * K (zt i) (z l)
    let cP : ℝ := (1 / (M : ℝ)) * ∑ k ∈ P, c k
    let g : Fin n → ℝ := fun ℓ => if ℓ ∈ P then 0 else
      (M : ℝ) ^ 2 * (StatFormal.ICL.Vrisk w M Lb ℓ - StatFormal.ICL.Grisk w M Lb) + lcov * M * (c ℓ - cP)
    (∀ k, HasDerivAt (fun t => cpsPhiM K z zt (Function.update wbar k t)) (c k) (wbar k)) ∧
    (∀ ℓ, HasDerivAt (fun t => StatFormal.Wave11b.jSwor L K z zt lcov 0 (Function.update w ℓ t)) (g ℓ) (w ℓ)) ∧
    IsGreatest (insert 0 ((fun ℓ => (M : ℝ) ^ 2 * (StatFormal.ICL.Grisk w M Lb - StatFormal.ICL.Vrisk w M Lb ℓ) +
        lcov * M * (cP - c ℓ)) '' {ℓ | ℓ ∉ P}))
      ((∑ ℓ, w ℓ * g ℓ) - ⨅ ℓ, g ℓ)

/-- `prop:cps-gradient`, "with `λ_KL > 0` the gap is infinite at every `w` with a zero coordinate": at `w ∈ Δ^(M)`
with `w_ℓ = 0`, the right difference quotients of `J_m` (frozen `jSwor`, `λ_KL > 0`) in the coordinate `ℓ` tend to
`−∞`; in particular `J_m` has no partial derivative in `w_ℓ` there (`g_ℓ = −∞`, so `⟨w, g⟩ − min_ℓ g_ℓ = +∞`). -/
def cps_kl_gap_infinite : Prop :=
  ∀ (Z : Type) (n M m : ℕ) (w : Fin n → ℝ) (z : Fin n → Z) (zt : Fin m → Z) (L : Z → (Fin M → Z) → ℝ)
    (K : Z → Z → ℝ) (lcov lKL : ℝ) (ℓ : Fin n), 1 ≤ M → StatFormal.ICL.InDeltaM w M → (∀ x y, 0 < K x y) →
    0 < lKL → w ℓ = 0 →
      Tendsto (fun t => (StatFormal.Wave11b.jSwor L K z zt lcov lKL (Function.update w ℓ t) -
          StatFormal.Wave11b.jSwor L K z zt lcov lKL w) / t) (𝓝[>] 0) atBot ∧
        ∀ d : ℝ, ¬ HasDerivAt (fun t => StatFormal.Wave11b.jSwor L K z zt lcov lKL (Function.update w ℓ t)) d (w ℓ)

end Claims

end StatFormal.Wave29i

namespace StatFormal.Wave29i

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal


open StatFormal.Wave11b (distinctSet ctxLaw Admissible jSwor collision)
open StatFormal.Wave26b (poolLaw riskIid)
open StatFormal.Wave20a (PhiC)
open StatFormal.ICL (InDeltaM)
open StatFormal.ICL.Diag (klUnif)
open StatFormal.ICL.Cond (iidLaw)

section Consist
variable {Z : Type*} [MeasurableSpace Z]

/-- The one-slot marginal `Π̄_μ = M⁻¹ Σ_s (Π_μ) ∘ ev_s⁻¹` of `Π_μ = μ^{⊗M}(· | D_M)`. -/
def consistMarg (μ : Measure Z) (M : ℕ) : Measure Z :=
  (M : ℝ≥0∞)⁻¹ • ∑ s : Fin M, (ctxLaw μ M).map (fun t => t s)

/-- The per-query risk `G_μ(z) = ∫ L(z; t) dΠ_μ(t)`. -/
def consistG {M : ℕ} (L : Z → (Fin M → Z) → ℝ) (μ : Measure Z) (z : Z) : ℝ :=
  ∫ t, L z t ∂(ctxLaw μ M)

/-- The population objective `R(μ) = ∫ G_μ dP₀ + λ_cov Φ(Π̄_μ)` (mean risk, coverage at the one-slot marginal). -/
def consistRisk {M : ℕ} (L : Z → (Fin M → Z) → ℝ) (Kk : Z → Z → ℝ) (lcov : ℝ) (P₀ μ : Measure Z) : ℝ :=
  ∫ z, consistG L μ z ∂P₀ + lcov * PhiC Kk P₀ (consistMarg μ M)

/-- The values `{R(μ) : μ ∈ 𝒫(supp P₀), μ^{⊗M}(D_M) > 0}` whose infimum is `R⋆`. -/
def consistClass [TopologicalSpace Z] {M : ℕ} (L : Z → (Fin M → Z) → ℝ) (Kk : Z → Z → ℝ) (lcov : ℝ)
    (P₀ : Measure Z) : Set ℝ :=
  {r | ∃ μ : Measure Z, Admissible P₀ M μ ∧ r = consistRisk L Kk lcov P₀ μ}

/-- The ordered conditional Poisson law `Π°_w(t) = Π_s w_{t_s} 1{t injective} / (1 − p(w))` on `[n]^M`
(the law of `M` i.i.d. indices from `w` conditioned on distinctness). -/
def consistOrdLaw {n : ℕ} (M : ℕ) (w : Fin n → ℝ) (t : Fin M → Fin n) : ℝ :=
  iidLaw w M t * (if Function.Injective t then 1 else 0) / (1 - collision w M)

end Consist

namespace Claims

/-- ICL `cor:consistency`, first claim: `𝒵` compact, `P₀` atomless, `L` bounded, symmetric and continuous on
`𝒵 × D_M`, `K` continuous with values in `[K_min, K_max]`, `K_min > 0`, mean risk, `M` fixed, nested i.i.d. pools.
`R⋆` exists as a genuine infimum, and for almost every pool sequence: if `ŵ` minimises `J_m` over `Δ^(M)` up to
`ε_opt → 0`, `n, m → ∞`, `log n/m → 0` and `λ_{KL,n} log n → 0`, then `R(μ_ŵ) → R⋆` in probability. -/
def consist_risk : Prop :=
  ∀ (Z Ω₀ : Type) [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z] [MeasurableSpace Ω₀]
    (P₀ : Measure Z) [IsProbabilityMeasure P₀] (Q : Measure Ω₀) [IsProbabilityMeasure Q] (Zs : ℕ → Ω₀ → Z)
    (M : ℕ) (L : Z → (Fin M → Z) → ℝ) (Kk : Z → Z → ℝ) (BL Kmin Kmax lcov : ℝ),
    1 ≤ M → (∀ x, P₀ {x} = 0) →
    ContinuousOn (fun p : Z × (Fin M → Z) => L p.1 p.2) (univ ×ˢ distinctSet M) →
    (∀ z t, 0 ≤ L z t ∧ L z t ≤ BL) → (∀ z t (σ : Equiv.Perm (Fin M)), L z (t ∘ σ) = L z t) →
    Continuous (Function.uncurry Kk) → 0 < Kmin → (∀ z z', Kmin ≤ Kk z z' ∧ Kk z z' ≤ Kmax) → 0 ≤ lcov →
    (∀ i, Measurable (Zs i)) → iIndepFun Zs Q → (∀ i, Q.map (Zs i) = P₀) →
    ∃ Rstar : ℝ, IsGLB (consistClass L Kk lcov P₀) Rstar ∧
      ∀ᵐ ω₀ ∂Q, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (n m : ℕ → ℕ)
        (X : (j : ℕ) → Fin (m j) → Ω → Z) (wh : (j : ℕ) → Ω → Fin (n j) → ℝ) (lamKL eps : ℕ → ℝ),
        (∀ j i, Measurable (X j i)) → (∀ j, iIndepFun (X j) P) → (∀ j i, P.map (X j i) = P₀) →
        (∀ᶠ j in atTop, 0 ≤ lamKL j ∧ ∀ ω, InDeltaM (wh j ω) M ∧ ∀ w : Fin (n j) → ℝ, InDeltaM w M →
          jSwor L Kk (fun i : Fin (n j) => Zs i ω₀) (fun i => X j i ω) lcov (lamKL j) (wh j ω) ≤
            jSwor L Kk (fun i : Fin (n j) => Zs i ω₀) (fun i => X j i ω) lcov (lamKL j) w + eps j) →
        Tendsto (fun j => (n j : ℝ)) atTop atTop → Tendsto (fun j => (m j : ℝ)) atTop atTop →
        Tendsto (fun j => Real.log (n j) / m j) atTop (𝓝 0) →
        Tendsto (fun j => lamKL j * Real.log (n j)) atTop (𝓝 0) → Tendsto eps atTop (𝓝 0) →
          TendstoInMeasure P
            (fun j ω => consistRisk L Kk lcov P₀ (poolLaw (fun i : Fin (n j) => Zs i ω₀) (wh j ω))) atTop
            (fun _ => Rstar)

/-- The reduction step of `cor:consistency` (premise (1) of the frozen `icl_consistency`), on the almost-sure pool
event: every `μ_w` with `w ∈ Δ^(M)` is admissible; `J_m(w) − devFull(Π°_w) = R(μ_w) + λ_KL KL(w|u_n)` (the deployed
objective of the conditional Poisson law, `thm:joint`'s `J_pool`) with `0 ≤ KL(w|u_n) ≤ log n`; and for `n, m ≥ 2`,
by `thm:joint` (`δ = 1/m`) and `cor:oracle`, with probability `≥ 1 − 1/m`,
`R(μ_ŵ) ≤ R(μ_w) + λ_KL log n + ε_opt + 2 dev_{m,n,1/m}` for every `w ∈ Δ^(M)`. -/
def consist_reduction : Prop :=
  ∀ (Z Ω₀ : Type) [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z] [MeasurableSpace Ω₀]
    (P₀ : Measure Z) [IsProbabilityMeasure P₀] (Q : Measure Ω₀) [IsProbabilityMeasure Q] (Zs : ℕ → Ω₀ → Z)
    (M : ℕ) (L : Z → (Fin M → Z) → ℝ) (Kk : Z → Z → ℝ) (BL Kmin Kmax lcov : ℝ),
    1 ≤ M → (∀ x, P₀ {x} = 0) →
    ContinuousOn (fun p : Z × (Fin M → Z) => L p.1 p.2) (univ ×ˢ distinctSet M) →
    (∀ z t, 0 ≤ L z t ∧ L z t ≤ BL) → (∀ z t (σ : Equiv.Perm (Fin M)), L z (t ∘ σ) = L z t) →
    Continuous (Function.uncurry Kk) → 0 < Kmin → (∀ z z', Kmin ≤ Kk z z' ∧ Kk z z' ≤ Kmax) → 0 ≤ lcov →
    (∀ i, Measurable (Zs i)) → iIndepFun Zs Q → (∀ i, Q.map (Zs i) = P₀) →
    ∀ᵐ ω₀ ∂Q, ∀ n : ℕ,
      (∀ w : Fin n → ℝ, InDeltaM w M →
        Admissible P₀ M (poolLaw (fun i : Fin n => Zs i ω₀) w) ∧
        (∀ (m : ℕ) (xs : Fin m → Z) (lKL : ℝ),
          jSwor L Kk (fun i : Fin n => Zs i ω₀) xs lcov lKL w -
              StatFormal.ICL.JointFull.devFull P₀ (fun t x => L x ((fun i : Fin n => Zs i ω₀) ∘ t))
                (fun j x => Kk x (Zs j ω₀)) lcov (consistOrdLaw M w) xs =
            consistRisk L Kk lcov P₀ (poolLaw (fun i : Fin n => Zs i ω₀) w) + lKL * klUnif n w) ∧
        0 ≤ klUnif n w ∧ klUnif n w ≤ Real.log n) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (m : ℕ) (X : Fin m → Ω → Z)
        (wh : Ω → Fin n → ℝ) (lKL eps : ℝ),
        2 ≤ n → 2 ≤ m → 0 ≤ lKL → (∀ i, Measurable (X i)) → iIndepFun X P → (∀ i, P.map (X i) = P₀) →
        (∀ ω, InDeltaM (wh ω) M) →
        (∀ ω (w : Fin n → ℝ), InDeltaM w M →
          jSwor L Kk (fun i : Fin n => Zs i ω₀) (fun i => X i ω) lcov lKL (wh ω) ≤
            jSwor L Kk (fun i : Fin n => Zs i ω₀) (fun i => X i ω) lcov lKL w + eps) →
        ∃ S : Set Ω, MeasurableSet S ∧ ENNReal.ofReal (1 - 1 / m) ≤ P S ∧ ∀ ω ∈ S, ∀ w : Fin n → ℝ,
          InDeltaM w M →
            consistRisk L Kk lcov P₀ (poolLaw (fun i : Fin n => Zs i ω₀) (wh ω)) ≤
              consistRisk L Kk lcov P₀ (poolLaw (fun i : Fin n => Zs i ω₀) w) + lKL * Real.log n + eps +
                2 * StatFormal.Wave24d.devBound BL lcov Kmin Kmax M n m (1 / m)

/-- The approximation step of `cor:consistency` (premise (2) of the frozen `icl_consistency`): for almost every
nested pool sequence, `limsup_n inf_{w ∈ Δ^(M)} R(μ_w) ≤ R⋆`, i.e. for every `ε > 0` all large pools carry a
`w ∈ Δ^(M)` with `R(μ_w) ≤ R⋆ + ε`. -/
def consist_approx : Prop :=
  ∀ (Z Ω₀ : Type) [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z] [MeasurableSpace Ω₀]
    (P₀ : Measure Z) [IsProbabilityMeasure P₀] (Q : Measure Ω₀) [IsProbabilityMeasure Q] (Zs : ℕ → Ω₀ → Z)
    (M : ℕ) (L : Z → (Fin M → Z) → ℝ) (Kk : Z → Z → ℝ) (BL Kmin Kmax lcov Rstar : ℝ),
    1 ≤ M → (∀ x, P₀ {x} = 0) →
    ContinuousOn (fun p : Z × (Fin M → Z) => L p.1 p.2) (univ ×ˢ distinctSet M) →
    (∀ z t, 0 ≤ L z t ∧ L z t ≤ BL) → (∀ z t (σ : Equiv.Perm (Fin M)), L z (t ∘ σ) = L z t) →
    Continuous (Function.uncurry Kk) → 0 < Kmin → (∀ z z', Kmin ≤ Kk z z' ∧ Kk z z' ≤ Kmax) → 0 ≤ lcov →
    (∀ i, Measurable (Zs i)) → iIndepFun Zs Q → (∀ i, Q.map (Zs i) = P₀) →
    IsGLB (consistClass L Kk lcov P₀) Rstar →
    ∀ᵐ ω₀ ∂Q, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∃ w : Fin n → ℝ, InDeltaM w M ∧
      consistRisk L Kk lcov P₀ (poolLaw (fun i : Fin n => Zs i ω₀) w) ≤ Rstar + ε

/-- ICL `cor:consistency`, second claim: for `L` continuous and bounded on `𝒵 × 𝒵^M` (and `P₀` atomless),
`R⋆ ≤ R^{iid⋆}`, `R^{iid⋆}` the infimum of the i.i.d. objective over `𝒫(supp P₀)`. -/
def consist_compare : Prop :=
  ∀ (Z : Type) [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (P₀ : Measure Z) [IsProbabilityMeasure P₀] (M : ℕ) (L : Z → (Fin M → Z) → ℝ) (Kk : Z → Z → ℝ)
    (BL Kmin Kmax lcov Rstar Riid : ℝ),
    1 ≤ M → (∀ x, P₀ {x} = 0) → Continuous (fun p : Z × (Fin M → Z) => L p.1 p.2) →
    (∀ z t, 0 ≤ L z t ∧ L z t ≤ BL) →
    Continuous (Function.uncurry Kk) → 0 < Kmin → (∀ z z', Kmin ≤ Kk z z' ∧ Kk z z' ≤ Kmax) →
    IsGLB (consistClass L Kk lcov P₀) Rstar →
    IsGLB {r | ∃ μ : Measure Z, IsProbabilityMeasure μ ∧ μ P₀.supportᶜ = 0 ∧ r = riskIid L Kk lcov P₀ μ} Riid →
      Rstar ≤ Riid

end Claims

end StatFormal.Wave29i

namespace StatFormal.Wave29i

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal NNReal RealInnerProductSpace


open StatFormal.TrimmedMMD.BangBang (capped)

/-- Empirical lower extreme trimmed mean `min_{w ∈ Δ_α(n)} Σ w_i v_i`. -/
def splitTrimLo (n : ℕ) (α : ℝ) (v : Fin n → ℝ) : ℝ := sInf ((fun w => ∑ i, w i * v i) '' capped n α)

/-- Empirical upper extreme trimmed mean `max_{w ∈ Δ_α(n)} Σ w_i v_i`. -/
def splitTrimUp (n : ℕ) (α : ℝ) (v : Fin n → ℝ) : ℝ := sSup ((fun w => ∑ i, w i * v i) '' capped n α)

/-- The `k`-th order statistic `min_{|S| = k} max_{i ∈ S} v_i`. -/
def splitOrdStat {n : ℕ} (k : ℕ) (v : Fin n → ℝ) : ℝ :=
  ⨅ S : {S : Finset (Fin n) // S.card = k}, ⨆ i : S.1, v i

/-- The empirical `(1−α)`-quantile `v_{(⌈n(1−α)⌉)}`. -/
def splitQuantLo (n : ℕ) (α : ℝ) (v : Fin n → ℝ) : ℝ := splitOrdStat ⌈(n : ℝ) * (1 - α)⌉₊ v

/-- Plug-in variance of the lower trimmed mean's influence function: `P_n g_ĉ² − (P_n g_ĉ)²`, `g_c = (c − ·)_+`. -/
def splitVarLo (n : ℕ) (α : ℝ) (v : Fin n → ℝ) : ℝ :=
  (∑ i, max (splitQuantLo n α v - v i) 0 ^ 2) / n - ((∑ i, max (splitQuantLo n α v - v i) 0) / n) ^ 2

/-- Plug-in standard error of `T̂ = L_n − U_m`: `√(V̂_X/n + V̂_Y/m)/(1 − α)`. -/
def splitSE (n m : ℕ) (α : ℝ) (vx : Fin n → ℝ) (vy : Fin m → ℝ) : ℝ :=
  √(splitVarLo n α vx / n + splitVarLo m α (fun j => -vy j) / m) / (1 - α)

/-- The split statistic `T̂_n` of `eq:splitstat` for the fixed witness `f`. -/
def splitStat {Ω 𝒳 H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (φ : 𝒳 → H) (f : H)
    (X Y : ℕ → Ω → 𝒳) (m : ℕ → ℕ) (α : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  splitTrimLo n α (fun i => ⟪f, φ (X i ω)⟫) - splitTrimUp (m n) α (fun j => ⟪f, φ (Y j ω)⟫)

/-- The plug-in standard error of `T̂_n`. -/
def splitSEn {Ω 𝒳 H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (φ : 𝒳 → H) (f : H)
    (X Y : ℕ → Ω → 𝒳) (m : ℕ → ℕ) (α : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  splitSE n (m n) α (fun i => ⟪f, φ (X i ω)⟫) (fun j => ⟪f, φ (Y j ω)⟫)

/-- `q` is the unique `p`-quantile of `h` under `P`. -/
def splitUQ {𝒳 : Type*} [MeasurableSpace 𝒳] (P : Measure 𝒳) (h : 𝒳 → ℝ) (p q : ℝ) : Prop :=
  P.real {x | h x < q} ≤ p ∧ p ≤ P.real {x | h x ≤ q} ∧ (∀ d > 0, P.real {x | h x < q - d} < p) ∧
    (∀ d > 0, p < P.real {x | h x ≤ q + d})

/-- `ass:split` (one side): `q` is a `p`-quantile of the law of `h` under `P`, which has a positive Lebesgue
density on a neighbourhood of `q`. -/
def splitAss {𝒳 : Type*} [MeasurableSpace 𝒳] (P : Measure 𝒳) (h : 𝒳 → ℝ) (p q : ℝ) : Prop :=
  P.real {x | h x < q} ≤ p ∧ p ≤ P.real {x | h x ≤ q} ∧
    ∃ ε > 0, ∃ ρ : ℝ → ℝ, Measurable ρ ∧ (∀ t ∈ Ioo (q - ε) (q + ε), 0 < ρ t) ∧
      ∀ a b, q - ε < a → b < q + ε → P {x | h x ∈ Ioc a b} = ∫⁻ t in Ioc a b, ENNReal.ofReal (ρ t)

/-- `σ² = [Var_P (q − h)_+ + Var_Q (h − q')_+ / κ]/(1 − α)²`. -/
def splitSigma2 {𝒳 : Type*} [MeasurableSpace 𝒳] (P Q : Measure 𝒳) (h : 𝒳 → ℝ) (α q q' κ : ℝ) : ℝ :=
  (Var[fun x => max (q - h x) 0; P] + Var[fun x => max (h x - q') 0; Q] / κ) / (1 - α) ^ 2

namespace Claims

open StatFormal.Wave17a (sepVal)
open StatFormal.TrimmedMMD.Concentration (region)

/-- Population identification: the two support functions of `sep(f; 𝒞_α(P), 𝒞_α(Q))` are the population lower
and upper trimmed means (at any `(1−α)`-quantile `q` under `P`, any `α`-quantile `q'` under `Q`). -/
def split_pop_trimmed : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ α q q' : ℝ) (f : H),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 →
    P.real {x | ⟪f, φ x⟫ < q} ≤ 1 - α → 1 - α ≤ P.real {x | ⟪f, φ x⟫ ≤ q} →
    Q.real {x | ⟪f, φ x⟫ < q'} ≤ α → α ≤ Q.real {x | ⟪f, φ x⟫ ≤ q'} →
      (⨅ a ∈ region φ α P, ((⟪f, a⟫ : ℝ) : EReal)) = ((q - (1 - α)⁻¹ * ∫ x, max (q - ⟪f, φ x⟫) 0 ∂P : ℝ) : EReal) ∧
      (⨆ b ∈ region φ α Q, ((⟪f, b⟫ : ℝ) : EReal)) = ((q' + (1 - α)⁻¹ * ∫ x, max (⟪f, φ x⟫ - q') 0 ∂Q : ℝ) : EReal) ∧
      sepVal f (region φ α P) (region φ α Q) =
        (((q - (1 - α)⁻¹ * ∫ x, max (q - ⟪f, φ x⟫) 0 ∂P) - (q' + (1 - α)⁻¹ * ∫ x, max (⟪f, φ x⟫ - q') 0 ∂Q) : ℝ) :
          EReal)

/-- `ass:split` (density form) gives a unique quantile and, below level `1`, a non-degenerate influence
variance. -/
def split_ass_unique : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P : Measure 𝒳) [IsProbabilityMeasure P] (h : 𝒳 → ℝ) (B p q : ℝ),
    Measurable h → (∀ x, |h x| ≤ B) → splitAss P h p q →
      splitUQ P h p q ∧ (p < 1 → 0 < Var[fun x => max (q - h x) 0; P])

/-- Asymptotic normality of `T̂_n` under quantile uniqueness (generalising `ass:split`), `m(n)/n → κ > 0`.
(At `α = 0` the uniqueness hypotheses are unsatisfiable, so the claim is informative only for `0 < α < 1`.) -/
def split_asymp_normal : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ' α q q' κ : ℝ) (f : H)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → 𝒳) (m : ℕ → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ') → 0 ≤ α → α < 1 →
    splitUQ P (fun x => ⟪f, φ x⟫) (1 - α) q → splitUQ Q (fun x => ⟪f, φ x⟫) α q' →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X μ → iIndepFun Y μ →
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ → (∀ i, μ.map (X i) = P) → (∀ i, μ.map (Y i) = Q) →
    0 < κ → Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ) →
      ∃ T₀ : ℝ, sepVal f (region φ α P) (region φ α Q) = (T₀ : EReal) ∧
        TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) * (splitStat φ f X Y m α n ω - T₀)) atTop id
          (fun _ => μ) (gaussianReal 0 (splitSigma2 P Q (fun x => ⟪f, φ x⟫) α q q' κ).toNNReal)

/-- Coverage of the plug-in normal lower limit: `P(T̂_n − z ŝe_n ≤ sep) → Φ(z)` for every `z`. (Informative only
for `0 < α < 1`, as `split_asymp_normal`.) -/
def split_coverage : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ' α q q' κ : ℝ) (f : H)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → 𝒳) (m : ℕ → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ') → 0 ≤ α → α < 1 →
    splitUQ P (fun x => ⟪f, φ x⟫) (1 - α) q → splitUQ Q (fun x => ⟪f, φ x⟫) α q' →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X μ → iIndepFun Y μ →
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ → (∀ i, μ.map (X i) = P) → (∀ i, μ.map (Y i) = Q) →
    0 < κ → Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ) →
    0 < splitSigma2 P Q (fun x => ⟪f, φ x⟫) α q q' κ →
      ∀ z : ℝ, Tendsto (fun n => μ.real {ω | ((splitStat φ f X Y m α n ω - z * splitSEn φ f X Y m α n ω : ℝ) : EReal) ≤
          sepVal f (region φ α P) (region φ α Q)}) atTop (𝓝 ((gaussianReal 0 1).real (Iic z)))

/-- `thm:split` with ANY consistent standard error (CONDITIONAL on `ŝe'_n/se_n → 1`, e.g. the bootstrap):
coverage, asymptotic level `δ`, and certification, under `ass:regularity` and `ass:split`. -/
def split_level_boot : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ' α q q' κ δ z : ℝ) (f : H)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → 𝒳) (m : ℕ → ℕ)
    (se : ℕ → Ω → ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ') → 0 < α → α < 1 →
    splitAss P (fun x => ⟪f, φ x⟫) (1 - α) q → splitAss Q (fun x => ⟪f, φ x⟫) α q' →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X μ → iIndepFun Y μ →
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ → (∀ i, μ.map (X i) = P) → (∀ i, μ.map (Y i) = Q) →
    0 < κ → Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ) →
    (∀ n, Measurable (se n)) →
    TendstoInMeasure μ (fun n ω => se n ω / (√(splitSigma2 P Q (fun x => ⟪f, φ x⟫) α q q' κ) / √(n : ℝ))) atTop
      (fun _ => 1) →
    (gaussianReal 0 1).real (Ioi z) = δ →
      (∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, 1 - δ - η ≤ μ.real {ω | ((splitStat φ f X Y m α n ω - z * se n ω : ℝ) : EReal) ≤
          sepVal f (region φ α P) (region φ α Q)}) ∧
      (StatFormal.Distances.tvDist P Q ≤ α →
          ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, μ {ω | 0 < splitStat φ f X Y m α n ω - z * se n ω} ≤ ENNReal.ofReal (δ + η)) ∧
      (∀ n, ∀ ω, ((splitStat φ f X Y m α n ω - z * se n ω : ℝ) : EReal) ≤ sepVal f (region φ α P) (region φ α Q) →
          0 < splitStat φ f X Y m α n ω - z * se n ω → α < StatFormal.Distances.tvDist P Q)

/-- `thm:split`, UNCONDITIONAL, with the plug-in standard error `ŝe_n = splitSEn`. -/
def split_level_discharged : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ' α q q' κ δ z : ℝ) (f : H)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → 𝒳) (m : ℕ → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ') → 0 < α → α < 1 →
    splitAss P (fun x => ⟪f, φ x⟫) (1 - α) q → splitAss Q (fun x => ⟪f, φ x⟫) α q' →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X μ → iIndepFun Y μ →
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ → (∀ i, μ.map (X i) = P) → (∀ i, μ.map (Y i) = Q) →
    0 < κ → Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ) →
    (gaussianReal 0 1).real (Ioi z) = δ →
      (∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, 1 - δ - η ≤ μ.real {ω |
          ((splitStat φ f X Y m α n ω - z * splitSEn φ f X Y m α n ω : ℝ) : EReal) ≤
            sepVal f (region φ α P) (region φ α Q)}) ∧
      (StatFormal.Distances.tvDist P Q ≤ α →
          ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
            μ {ω | 0 < splitStat φ f X Y m α n ω - z * splitSEn φ f X Y m α n ω} ≤ ENNReal.ofReal (δ + η)) ∧
      (∀ n, ∀ ω, ((splitStat φ f X Y m α n ω - z * splitSEn φ f X Y m α n ω : ℝ) : EReal) ≤
          sepVal f (region φ α P) (region φ α Q) →
          0 < splitStat φ f X Y m α n ω - z * splitSEn φ f X Y m α n ω → α < StatFormal.Distances.tvDist P Q)

end Claims

end StatFormal.Wave29i
