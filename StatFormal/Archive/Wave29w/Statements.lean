import StatFormal.Archive.Wave29f.Statements
import StatFormal.Archive.Wave29b.Statements
import StatFormal.Archive.Wave29i.Statements
import StatFormal.Archive.OTFD.Wave19a.Statements

/-!
# FROZEN STATEMENTS — wave 29w: a sweep of small gaps — otfd R `thm:student` (ii) (the region of content EXACTLY `p`);
# otfd T `thm:coverage-error` (the "consequently" clause: asymptotic content); otfd B `thm:consistency` for a general
# symmetric positive definite `M_K` under the PRINTED homeomorphism hypothesis; trimmed MMD `thm:split` at `α = 0`
# (plain sample means: CLT, plug-in coverage, asymptotic level, certification)

Sources (current text, read 2026-10-20, `research-lines/`):
* otfd R `thm:student` (`otfd/papers/R_robustness/sections/s6_references.tex:71-88`, proof `:90-98`), (ii): "the
  robustness of the region of content `p` is exactly `β*_K(p)`"; the content formula `F_{K,ν}(r²/K)`.
* otfd T `thm:coverage-error` (`otfd/papers/T_tangent/supp_moved.tex:955-969`, proof `:970-977`), the sentence
  "Consequently integrated quantile consistency gives asymptotic content at least `p` for every fixed positive expansion
  of a content-`p` fitted tube" (`:967-969`), with `thm:empirical` (`sec_tangent_theory.tex:308-320`, `eq:empQ`).
* otfd B `thm:consistency` (`otfd/papers/B_bands/supplement.tex:6145-6187`, proof `:6189-6218`): "`P_K` absolutely
  continuous with support `𝒴_K` and the `M_K`-optimal quantile map `Q_{±,K}` a homeomorphism from `int 𝒰_K` onto
  `int 𝒴_K`"; "almost surely, for every compact `𝒦 ⊂ int 𝒴_K`".
* trimmed MMD `thm:split` (`trimmed-mmd/paper.tex:1165-1178`), `ass:split` (`:1153-1163`: "If `α = 0` both terms are
  sample means and no condition is imposed"; DEFECTS #110), `eq:splitstat` (`:1140-1151`), proof
  `supplement.tex:400-414`.
Imports the frozen `Wave29f` statements (`coverr_rank`, `coverr_model` setting; through it Wave 23d `studentLaw`,
`fCDF`, `fQuant`, OTFD Wave 8c `IsRankPair`, `IsGradMap`, Wave 22b `LengthBound`, `Lb`, WaveL1 `LipNull`, `Euc`),
`Wave29b` (`cons_general_M` setting; Wave 8c `mvec`, Wave 22a `IsSubgrad`, Tau Ceti `empiricalMeasure`), `Wave29i`
(`splitTrimLo`, `splitTrimUp`, `splitVarLo`, `splitSE`, `splitStat`, `splitSEn`; through it Wave 17a `sepVal`,
`TrimmedMMD/Concentration` `region`, `Distances` `tvDist`) and OTFD `Wave19a` (`IsMGradMap`); not copied. No new
definitions.

Covered:
* R `thm:student` (ii), the region of content EXACTLY `p` (the gap left by the frozen Wave 23d `student_region`, which
  proves content `≥ p`): `student_region_exact` (`F_{K,ν}(F_{K,ν}^{-1}(p)) = p`; the ellipsoid of radius
  `√(K F_{K,ν}^{-1}(p))` has content `= p`; it is the smallest ellipsoid of content `≥ p`). With the frozen
  `student_region` (robustness `β*_K(p)`, optimality) this is the printed sentence.
* T `thm:coverage-error`, the "consequently" clause: `coverr_asymp` (in the frozen `coverr_rank` setting: content-`p`
  tubes along a training sequence with `∫ ‖Q̂_n − Q‖² dμ → 0` have asymptotic content `≥ p` at every fixed `δ > 0`),
  `coverr_asymp_model` (the same under `ass:model`, with the McCann maps `F_ν`, `Q_ν` of the frozen `coverr_model`).
* B `thm:consistency`, general SPD `M_K`, under the PRINTED homeomorphism hypothesis (the Wave 29p gap):
  `consB_homeo` (no differentiability hypothesis; `F = G := Q⁻¹` `P_K`-a.e., `ψ` differentiable on `int 𝒴_K` with
  gradient `M_K G`, the geometric depth bound, and a.s. `ε_n(𝒦) → 0` and uniform convergence of both depths for a
  fixed compact `𝒦`), `consB_homeo_allK` (one almost-sure event for EVERY compact `𝒦 ⊂ int 𝒴_K`, the printed
  quantifier order, when the estimator selection is defined on all of `int 𝒴_K`).
* trimmed MMD `thm:split` at `α = 0` (the DEFECTS #110 gap: the frozen Wave 29i/29l claims say nothing at `α = 0`):
  `split_zero_means` ("both terms are sample means"; the frozen plug-in variance at `α = 0` is the sample variance and
  `ŝe = √(s²_X/n + s²_Y/m)`), `split_zero_asymp_normal` (`sep = P h − Q h` and `√n (T̂_n − sep) ⇝ N(0, σ₀²)`,
  `σ₀² = Var_P h + Var_Q h/κ`, no condition), `split_zero_coverage` (`σ₀² > 0`: `P(T̂_n − z ŝe_n ≤ sep) → Φ(z)`),
  `split_zero_level` (UNCONDITIONAL, also for `σ₀² = 0`: coverage `≥ 1 − δ` asymptotically, asymptotic level `δ`
  under `H_{0,0}: TV(P,Q) ≤ 0`, and certification `TV(P,Q) > 0` on the coverage event).

Not covered (declared):
* R: nothing further in (ii) (the depth formula, `β*` and optimality are frozen Wave 23d; the rate is frozen Wave 25d).
* T: the training randomness is not modelled: "integrated quantile consistency" is a deterministic sequence of fitted
  maps (conditionally on the training sample; `thm:empirical`'s almost-sure `e_n → 0` gives the conclusion for almost
  every training sample by applying the claim pointwise). `thm:empirical` itself is the frozen Wave 25b
  `empirical_quantile` and is not re-instantiated; `LengthBound`, `L_b < ∞`, `eq:Hembed` are hypotheses as in the
  frozen claims.
* B: the proof's `L = M_K^{1/2}` reduction is not formalised (not needed: the `u ↦ M_K u` change of variables on the
  reference side suffices, as in the frozen Wave 29b `cons_general_M`); compactness and nonempty interior of `𝒰_K`
  are not used; the `ϖ_K` and rate clauses are frozen Wave 29p (`consB_varpi*`, `consB_rate`).
* trimmed MMD at `α = 0`: the BOOTSTRAP standard error and the percentile limit (frozen Wave 29l is for `α > 0`) — only
  the plug-in standard error `splitSEn` is covered; only the ratio regime `m(n)/n → κ ∈ (0, ∞)`; the first fold is
  fixed (`f̂ = f`), as in the frozen claims.

Encodings (to be checked by the critic):
* `student_region_exact`: objects of the frozen Wave 23d `student_region` verbatim (`ℝ^K`, `A` invertible,
  `studentLaw`, `fCDF`, `fQuant` = `sInf{x : p ≤ F(x)}`, `0 < p < 1`, `ν > 0`, `K ≥ 1`); "smallest ellipsoid of content
  `≥ p`" is the iff over radii `r ≥ 0`.
* `coverr_asymp*`: the hypotheses of the frozen `coverr_rank` / `coverr_model` at every `n`, with `Q̂ = Q̂_n`,
  `𝒯 = 𝒯_n`, `A = A_n`, `p̲ = p` fixed, and the tangent bound `b` FIXED along `n` (needed: `L_b` depends on `b`);
  "integrated quantile consistency" is `∫⁻ ‖Q̂_n − Q‖ₑ² dμ → 0` (the frozen lintegral form of `e_n²`); "asymptotic
  content at least `p`" is: for every `η > 0`, eventually a measurable event of probability `≥ p − η` (truncated
  subtraction in `[0, ∞]`) carries `X(t) ∈ 𝒯_n^δ(t)` for every `t` (i.e. `liminf` of the inner probability `≥ p`).
* `consB_homeo*`: the objects of the frozen Wave 29b `cons_general_M` verbatim, minus its hypothesis
  `∀ x ∈ 𝒦, HasGradientAt ψ (M_K F x) x`; the reference support `𝒰_K` is a convex set `S` carrying `μ_K ≪ Leb`; the
  `M_K`-optimal quantile map is the frozen OTFD Wave 19a `IsMGradMap M_K μ_K P_K Q` (Borel, `Q#μ_K = P_K`,
  `M_K Q(u) ∈ ∂φ(u)` `μ_K`-a.e. for an `EReal`-valued `φ`, finite at those points — Tau Ceti's subdifferential is
  empty where `φ` is infinite; equivalently, by Rockafellar, `c`-cyclical monotonicity for `‖z − u‖²_{M_K}`); the
  homeomorphism is as in the frozen Wave 29p `consA_homeo` (`ContinuousOn` both ways, `MapsTo` both ways, mutually
  inverse on the interiors, `𝒴_K = supp P_K`). The conclusions are stated for the continuous version `G = Q⁻¹` of the
  rank map (as `consA_homeo`; see Wave 29p Paper notes (3)). `g_K(G) ≤ 1` on `𝒦` (resp. `int 𝒴_K`) is the frozen
  `cons_general_M` hypothesis `g_K(F) ≤ 1` transported to `G`.
* `split_zero_*`: the frozen Wave 29i objects at `α = 0` literally (`splitStat … 0`, `splitSEn … 0`, `region φ 0`),
  the hypotheses of the frozen `split_level_discharged` minus `0 < α` and `ass:split`; `σ₀²` is
  `Var_P h + Var_Q h/κ` (the frozen `splitSigma2` at `α = 0` would need quantiles `q`, `q'`, which at `α = 0` are
  only one-sided; the claim states the sample-mean variance directly); `H_{0,0}` is `tvDist P Q ≤ 0`.

Junk-value audit: no new definition. `fQuant` is an `sInf` of a nonempty set bounded below (frozen). In
`split_zero_means`, `n, m ≥ 1` (no `/0`), `√` of a sum of squares. `splitTrimLo/Up` at `n = 0` (`sInf ∅ = 0`) occur only
for finitely many `n` (asymptotic claims; `m(n) → ∞`). The `σ₀² = 0` case of `split_zero_level` is genuine (the lower
limit is a.s. `sep` eventually, `ŝe = 0`), not a `√0 = 0` artefact: `split_zero_coverage` assumes `σ₀² > 0`, and the
degenerate case is proved separately (`h(X_i) = P h` a.s. when `Var_P h = 0`). `toNNReal` of `σ₀² ≥ 0` is faithful.
`ofReal p − η` is truncated subtraction (a lower bound, harmless). Every `Measure.map` is of a measurable map (inherited).
At `α = 0` the frozen `splitQuantLo n 0 v = splitOrdStat n v` is the sample MAXIMUM for `n ≥ 1` (the only `n`-subset is
`univ`; the empty `⨆ = 0` occurs only at `n = 0`), so `(max − v_i)_+ = max − v_i` and the frozen `splitVarLo n 0` is the
genuine sample variance; the frozen `splitSigma2` (one-sided quantiles `q`, `q'` at `α = 0`) is NOT referenced by any
claim — `σ₀²` is written as `Var_P h + Var_Q h/κ` (finite: `h = ⟨f, φ⟩` bounded, so `variance = evariance.toReal` is
not the `⊤ ↦ 0` junk). `region φ 0 P = {∫ φ dP}` (density `g ≤ 1`, `∫ g = 1` forces `g = 1` a.e.; `φ` bounded strongly
measurable, so the Bochner integral is of an integrable map).

Proof notes (author of the draft, 2026-10-20; `#print axioms`: propext, Classical.choice, Quot.sound for all 9 claims;
no `sorry`): routes `Wave29w/Route{Student,Coverage,ConsB,SplitZero}.lean`, new library
`Foundations/TrimmedMean/AlphaZero.lean`.
* `student_region_exact`: `F(q) ≥ p` (right-continuity, Wave 23d `fQuant_spec`); `F(q) = fLaw(Iic q) = fLaw(Iio q)`
  (atomless `fLaw`, the Wave 29f route lemma `fLaw_noAtoms`) `= lim F(q − 1/(n+1)) ≤ p`; content by Wave 23d
  `student_content_aux`, minimality by Wave 23d `content_lt`, `content_rp`.
* `coverr_asymp*`: the certified Wave 29f `coverr_rank` / `coverr_model` at each `n`, and `c·e_n² → 0` for the finite
  `c = L_b²Λ²/δ²`.
* `consB_homeo`: the Wave 29p `consA_homeo` argument through `u ↦ M_K u`: `IsMGradMap` gives a cyclically monotone
  `{(u, M_K Q u)}` (telescoping of finite subgradient inequalities); swap (WaveL3 `cycMon_swap`) and the image under
  `(a, b) ↦ (M_K⁻¹a, M_K b)` (symmetric `M_K`) give `{(Q u, M_K u)}`, which contains the graph of `M_K G'`
  (`G' = 1_{int 𝒴} G`); `M_K F` is cyclically monotone from `M_K F ∈ ∂ψ`; both push `P_K` to `M_K#μ_K ⊆ B̄(0, L')`, so
  the certified WaveL7 `brenierUniq_of_bdd_target` gives `M_K F = M_K G'` a.e.; then the Wave 29p route lemmas
  `subgrad_of_ae`, `hasGradientAt_of_subgrad` (closure, differentiability) and the certified Wave 29b
  `cons_general_M` with the rank map `G'`. `consB_homeo_allK`: a compact exhaustion of `int 𝒴_K` (Mathlib
  `CompactExhaustion` on the open subtype) and countably many null sets.
* `split_zero_*`: `capped n 0 = {(1/n, …, 1/n)}`; the plug-in variance centred at the maximum equals the sample
  variance (shift invariance); `sep` by `Foundations/TrimmedMean/Population.sepVal_eq` at `q = ‖f‖κ'`, `q' = −q`;
  the two-sample CLT `Foundations/CLT/TwoSample.clt_two_sample`; Chebyshev (`tip0_avg`) for `s²`; Slutsky + portmanteau
  `coverage_lim`; the certified frozen Wave 22c `split_level` for level and certification.

Paper notes:
(1) R `thm:student` (ii): correct as printed; "the region of content `p`" has content exactly `p` because
  `F_{K,ν}` is continuous (`χ²_K/K` has no atom); the proof could say so in one clause.
(2) T `thm:coverage-error`: the "consequently" clause holds as printed provided the tangent bound `b` is uniform along
  the sequence (it is, for a fixed `b` as in the theorem's hypotheses); "asymptotic content at least `p`" is a
  `liminf` statement.
(3) B `thm:consistency`: correct as printed for every SPD `M_K`; the `L = M_K^{1/2}` reduction in the proof is valid
  but more than is needed (`u ↦ M_K u` on the reference side suffices, with McCann uniqueness from the absolutely
  continuous `P_K` and the bounded target `M_K#μ_K`). As for A (Wave 29p note (3)), the conclusion concerns the
  continuous version `Q_{±,K}^{-1}` of the rank map on `int 𝒴_K`.
(4) trimmed MMD `thm:split` at `α = 0`: correct as printed after DEFECTS #110 (no condition at `α = 0`), including
  the degenerate case `Var_P f̂ = Var_Q f̂ = 0`; the plug-in variance at `α = 0` is the ordinary sample variance.
(5) (critic, expository, any `α`) trimmed MMD: `paper.tex:1141-1143` sets `f̂` to "an arbitrary fixed unit vector" when
  the first-fold optimum is zero, while the proof of `thm:split` (`supplement.tex:415-417`) says "When `f̂ = 0` … the
  statistic is identically zero and the rule does not reject". Both conventions are valid (the claims here hold for
  every `f ∈ H`, `f = 0` included: then `T̂ = ŝe = 0`, `σ₀² = 0`, and `split_zero_level` gives no rejection) but the
  two sentences describe different conventions; one should be dropped or the supplement sentence prefixed "Under the
  alternative convention `f̂ = 0`".

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave29w

open StatFormal.OTFD.WaveL1 (Euc LipNull)

namespace Claims

/-! ### otfd R `thm:student` (ii): the region of content `p` -/

open StatFormal.Wave23d (studentLaw fCDF fQuant) in
/-- R `thm:student` (ii), "the region of content `p`", with content EXACTLY `p`: `F_{K,ν}` is continuous at its
`p`-quantile, `F_{K,ν}(F_{K,ν}^{-1}(p)) = p`; the ellipsoid `E_p = {u : ‖Σ_K^{-1/2}u‖ ≤ √(K F_{K,ν}^{-1}(p))}` has
`μ_K`-content exactly `p`; and it is the smallest ellipsoid of content at least `p`: the ellipsoid of radius `r ≥ 0`
has content `≥ p` iff `r ≥ √(K F_{K,ν}^{-1}(p))`. (Its robustness `β*_K(p)` and optimality are the frozen Wave 23d
`student_region`.) -/
def student_region_exact : Prop :=
  ∀ (K : ℕ) (ν : ℝ) (A : EuclideanSpace ℝ (Fin K) ≃L[ℝ] EuclideanSpace ℝ (Fin K)) (p : ℝ), 0 < K → 0 < ν →
    0 < p → p < 1 →
      fCDF K ν (fQuant K ν p) = p ∧
      studentLaw K ν A {u | ‖A.symm u‖ ≤ √(K * fQuant K ν p)} = ENNReal.ofReal p ∧
      ∀ r : ℝ, 0 ≤ r →
        (ENNReal.ofReal p ≤ studentLaw K ν A {u | ‖A.symm u‖ ≤ r} ↔ √(K * fQuant K ν p) ≤ r)

/-! ### otfd T `thm:coverage-error`: the "consequently" clause -/

open StatFormal.OTFD.Wave8c (IsRankPair) in
open StatFormal.OTFD.Wave22b (LengthBound Lb) in
/-- T `thm:coverage-error`, "consequently integrated quantile consistency gives asymptotic content at least `p` for
every fixed positive expansion of a content-`p` fitted tube": in the setting of the frozen Wave 29f `coverr_rank`
(trajectory `X` in the chart image, `(F, Q)` a rank pair between `μ` and `ν = L_m#P_X`, tangent norms of `Q` at most `b`
`μ`-a.e.), take, along the training sequence `n`, fitted maps `Q̂_n` (tangent norms `≤ b`), fitted tubes `𝒯_n`
containing `E_m Q̂_n(A_n)` with `μ(A_n) ≥ p` (content-`p` tubes), and integrated quantile consistency
`∫ ‖Q̂_n − Q‖² dμ → 0`. Then for every fixed expansion `δ > 0` the content of `𝒯_n^δ` under the data law is
asymptotically at least `p`: for every `η > 0`, eventually a measurable event of probability `≥ p − η` carries
`X(t) ∈ 𝒯_n^δ(t)` for every `t`. -/
def coverr_asymp : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [SecondCountableTopology H] [MeasurableSpace H]
    [BorelSpace H] (Tm V W M C Ω : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
    [NormedSpace ℝ W] [PseudoEMetricSpace M] [MeasurableSpace C] [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → C)
    (curve : C → Tm → M) (μ : Measure H) (Ex : Tm → V → M) (D : Tm → V → V →L[ℝ] W) (ι : H →ₗ[ℝ] (Tm → V))
    (Em : H → C) (Lm : C → H) (Dr : Set H) (F Q : H → H) (Qhat : ℕ → H → H) (tube : ℕ → Tm → Set M)
    (A : ℕ → Set H) (b Λ p : ℝ),
    IsProbabilityMeasure P → IsProbabilityMeasure μ → Measurable X → (∀ v t, curve (Em v) t = Ex t (ι v t)) →
    Measurable Em → Measurable Lm → MeasurableSet Dr → (∀ v ∈ Dr, Lm (Em v) = v) →
    (∀ᵐ x ∂(P.map X), Lm x ∈ Dr ∧ Em (Lm x) = x) → IsRankPair μ ((P.map X).map Lm) F Q →
    (∀ n, Measurable (Qhat n)) → (∀ n, MeasurableSet (A n)) → 0 ≤ Λ → LengthBound Ex D → Lb D b ≠ ⊤ →
    (∀ x t, ‖ι x t‖ ≤ Λ * ‖x‖) → (∀ᵐ u ∂μ, ∀ t, ‖ι (Q u) t‖ ≤ b) → (∀ n u t, ‖ι (Qhat n u) t‖ ≤ b) →
    (∀ n, ∀ u ∈ A n, ∀ t, Ex t (ι (Qhat n u) t) ∈ tube n t) → (∀ n, ENNReal.ofReal p ≤ μ (A n)) →
    Tendsto (fun n => ∫⁻ u, ‖Qhat n u - Q u‖ₑ ^ 2 ∂μ) atTop (𝓝 0) →
      ∀ δ : ℝ, 0 < δ → ∀ η : ℝ≥0∞, 0 < η → ∀ᶠ n in atTop, ∃ Ev : Set Ω, MeasurableSet Ev ∧
        (∀ ω ∈ Ev, ∀ t, ∃ y ∈ tube n t, edist (curve (X ω) t) y ≤ ENNReal.ofReal δ) ∧
        ENNReal.ofReal p - η ≤ P Ev

open StatFormal.OTFD.Wave8c (IsRankPair IsGradMap) in
open StatFormal.OTFD.Wave22b (LengthBound Lb) in
/-- T `thm:coverage-error`, the "consequently" clause under `ass:model` (as the frozen Wave 29f `coverr_model`): the
McCann rank and quantile maps `F_ν`, `Q_ν` exist, and for them every sequence of content-`p` fitted tubes with
integrated quantile consistency `∫ ‖Q̂_n − Q_ν‖² dμ → 0` (tangent norms `≤ b`) has asymptotic content at least `p` at
every fixed expansion `δ > 0`. -/
def coverr_asymp_model : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (Tm V W M C Ω : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [PseudoEMetricSpace M] [MeasurableSpace C] [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → C) (curve : C → Tm → M) (μ : Measure H) (Ex : Tm → V → M) (D : Tm → V → V →L[ℝ] W)
    (ι : H →ₗ[ℝ] (Tm → V)) (Em : H → C) (Lm : C → H) (Dr : Set H) (B Bμ Λ : ℝ),
    IsProbabilityMeasure P → IsProbabilityMeasure μ → Measurable X → (∀ v t, curve (Em v) t = Ex t (ι v t)) →
    Measurable Em → Measurable Lm → MeasurableSet Dr → (∀ v ∈ Dr, Lm (Em v) = v) →
    (∀ᵐ x ∂(P.map X), Lm x ∈ Dr ∧ Em (Lm x) = x) →
    LipNull ((P.map X).map Lm) → LipNull μ → (∀ᵐ v ∂((P.map X).map Lm), ‖v‖ ≤ B) → (∀ᵐ u ∂μ, ‖u‖ ≤ Bμ) →
    0 ≤ Λ → (∀ x t, ‖ι x t‖ ≤ Λ * ‖x‖) → LengthBound Ex D →
      ∃ F Q : H → H, IsRankPair μ ((P.map X).map Lm) F Q ∧ IsGradMap ((P.map X).map Lm) μ F ∧
        IsGradMap μ ((P.map X).map Lm) Q ∧
        ∀ (Qhat : ℕ → H → H) (tube : ℕ → Tm → Set M) (A : ℕ → Set H) (b p : ℝ),
          (∀ n, Measurable (Qhat n)) → (∀ n, MeasurableSet (A n)) → Lb D b ≠ ⊤ →
          (∀ᵐ u ∂μ, ∀ t, ‖ι (Q u) t‖ ≤ b) → (∀ n u t, ‖ι (Qhat n u) t‖ ≤ b) →
          (∀ n, ∀ u ∈ A n, ∀ t, Ex t (ι (Qhat n u) t) ∈ tube n t) → (∀ n, ENNReal.ofReal p ≤ μ (A n)) →
          Tendsto (fun n => ∫⁻ u, ‖Qhat n u - Q u‖ₑ ^ 2 ∂μ) atTop (𝓝 0) →
            ∀ δ : ℝ, 0 < δ → ∀ η : ℝ≥0∞, 0 < η → ∀ᶠ n in atTop, ∃ Ev : Set Ω, MeasurableSet Ev ∧
              (∀ ω ∈ Ev, ∀ t, ∃ y ∈ tube n t, edist (curve (X ω) t) y ≤ ENNReal.ofReal δ) ∧
              ENNReal.ofReal p - η ≤ P Ev

/-! ### otfd B `thm:consistency`: general `M_K` under the printed homeomorphism hypothesis -/

open StatFormal.OTFD.Wave8c (mvec) in
open StatFormal.OTFD.Wave22a (IsSubgrad) in
open StatFormal.OTFD.Wave19a (IsMGradMap) in
open TauCeti.Probability (empiricalMeasure) in
/-- B `thm:consistency` for a general symmetric positive definite `M_K` under the PRINTED hypothesis: the reference
`μ_K ≪ Leb` is carried by a convex set `𝒰_K = S` (and by `B̄(0, R)`), `P_K ≪ Leb` with support `𝒴_K`, and the
`M_K`-optimal quantile map `Q_{±,K}` (the frozen Wave 19a `IsMGradMap M_K μ_K P_K Q`: Borel, `Q#μ_K = P_K`,
`M_K Q(u) ∈ ∂φ(u)` `μ_K`-a.e. for one `φ : ℝ^K → EReal`, finite at those points, with the global subgradient
inequality — equivalently `{(u, M_K Q u)}` is cyclically monotone, i.e. `c`-cyclical monotonicity for
`‖z − u‖²_{M_K}`) is a homeomorphism `int S → int 𝒴_K` with inverse `G`. The population
rank map `F` and the semi-discrete estimator are those of the frozen Wave 29b `cons_general_M` (`M_K F ∈ ∂ψ`
`P_K`-a.e., `F#P_K = μ_K`; `γ_n` carried by `{(z, u) : M_K u ∈ ∂ψ̂_n(z)}`, `F̂_n(x)` any `u` with `M_K u ∈ ∂ψ̂_n(x)`),
but WITHOUT its differentiability hypothesis "`∇ψ = M_K F` on `𝒦`". Then `F = G` `P_K`-a.e. (`G` is the continuous
version of the rank map), `ψ` is differentiable at every point of `int 𝒴_K` with gradient `M_K G`, the deterministic
geometric depth bound holds, and almost surely `ε_n(𝒦) = sup_𝒦 ‖F̂_n − G‖ → 0` and both depths
`1 − g_K(F̂_n(Π_K x))`, `1 − c_K(g_K(F̂_n(Π_K x)))` converge uniformly over `{x : Π_K x ∈ 𝒦}`. -/
def consB_homeo : Prop :=
  ∀ (K : ℕ) (Ω H : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (Z : ℕ → Ω → Euc K)
    (P μ : ProbabilityMeasure (Euc K)) (MK : Matrix (Fin K) (Fin K) ℝ) (ψ : Euc K → ℝ) (F : Euc K → Euc K)
    (R L L' : ℝ) (ψh : ℕ → Ω → Euc K → ℝ) (γ : ℕ → Ω → ProbabilityMeasure (Euc K × Euc K))
    (Fh : ℕ → Ω → Euc K → Euc K) (𝒦 : Set (Euc K)) (PiK : H → Euc K) (g : Euc K → ℝ) (cK : ℝ → ℝ) (c' : ℝ)
    (S : Set (Euc K)) (Q G : Euc K → Euc K),
    MK.PosDef →
    iIndepFun Z Pr → (∀ i, HasLaw (Z i) (P : Measure (Euc K)) Pr) → (P : Measure (Euc K)) ≪ volume →
    (μ : Measure (Euc K)) (Metric.closedBall 0 R)ᶜ = 0 → (∀ u ∈ Metric.closedBall (0 : Euc K) R, ‖mvec MK u‖ ≤ L') →
    (μ : Measure (Euc K)) ≪ volume → Convex ℝ S → (μ : Measure (Euc K)) Sᶜ = 0 →
    ConvexOn ℝ univ ψ → (∀ x x', |ψ x - ψ x'| ≤ L * ‖x - x'‖) →
    Measurable F → (P : Measure (Euc K)).map F = μ → (∀ᵐ x ∂(P : Measure (Euc K)), IsSubgrad ψ x (mvec MK (F x))) →
    IsMGradMap MK (μ : Measure (Euc K)) (P : Measure (Euc K)) Q →
    ContinuousOn Q (interior S) → ContinuousOn G (interior (P : Measure (Euc K)).support) →
    MapsTo Q (interior S) (interior (P : Measure (Euc K)).support) →
    MapsTo G (interior (P : Measure (Euc K)).support) (interior S) →
    (∀ u ∈ interior S, G (Q u) = u) → (∀ y ∈ interior (P : Measure (Euc K)).support, Q (G y) = y) →
    IsCompact 𝒦 → 𝒦 ⊆ interior (P : Measure (Euc K)).support →
    (∀ n ω, (γ n ω : Measure (Euc K × Euc K)).fst = (empiricalMeasure (fun i => Z i ω) n : Measure (Euc K))) →
    (∀ n ω, (γ n ω : Measure (Euc K × Euc K)).snd = μ) →
    (∀ n ω, (γ n ω : Measure (Euc K × Euc K)).support ⊆ {p | IsSubgrad (ψh n ω) p.1 (mvec MK p.2)}) →
    (∀ n ω x x', |ψh n ω x - ψh n ω x'| ≤ L' * ‖x - x'‖) →
    (∀ n ω, ∀ x ∈ 𝒦, IsSubgrad (ψh n ω) x (mvec MK (Fh n ω x))) →
    (∀ a b, g (a + b) ≤ g a + g b) → (∀ a, g (-a) = g a) → (∀ a, g a ≤ c' * ‖a‖) → Continuous cK →
    (∀ z ∈ 𝒦, g (G z) ≤ 1) →
      (∀ᵐ y ∂(P : Measure (Euc K)), F y = G y) ∧
      (∀ y ∈ interior (P : Measure (Euc K)).support, HasGradientAt ψ (mvec MK (G y)) y) ∧
      (∀ n ω x, |(1 - g (Fh n ω (PiK x))) - (1 - g (G (PiK x)))| ≤ c' * ‖Fh n ω (PiK x) - G (PiK x)‖) ∧
      ∀ᵐ ω ∂Pr, TendstoUniformlyOn (fun n => Fh n ω) G atTop 𝒦 ∧
        TendstoUniformlyOn (fun n x => 1 - g (Fh n ω (PiK x))) (fun x => 1 - g (G (PiK x))) atTop
          {x | PiK x ∈ 𝒦} ∧
        TendstoUniformlyOn (fun n x => 1 - cK (g (Fh n ω (PiK x)))) (fun x => 1 - cK (g (G (PiK x)))) atTop
          {x | PiK x ∈ 𝒦}

open StatFormal.OTFD.Wave8c (mvec) in
open StatFormal.OTFD.Wave22a (IsSubgrad) in
open StatFormal.OTFD.Wave19a (IsMGradMap) in
open TauCeti.Probability (empiricalMeasure) in
/-- B `thm:consistency`, general `M_K`, printed homeomorphism hypothesis, with the printed quantifier order "almost
surely, for every compact `𝒦 ⊂ int 𝒴_K`": the setting of `consB_homeo` with the estimator `F̂_n(x)` a selection
(`M_K F̂_n(x) ∈ ∂ψ̂_n(x)`) at every query point `x ∈ int 𝒴_K` and `g_K(G) ≤ 1` on `int 𝒴_K`; then ONE almost-sure
event carries, for EVERY compact `𝒦 ⊆ int 𝒴_K`, `ε_n(𝒦) → 0` and the uniform convergence of both depths over
`{x : Π_K x ∈ 𝒦}`. -/
def consB_homeo_allK : Prop :=
  ∀ (K : ℕ) (Ω H : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (Z : ℕ → Ω → Euc K)
    (P μ : ProbabilityMeasure (Euc K)) (MK : Matrix (Fin K) (Fin K) ℝ) (ψ : Euc K → ℝ) (F : Euc K → Euc K)
    (R L L' : ℝ) (ψh : ℕ → Ω → Euc K → ℝ) (γ : ℕ → Ω → ProbabilityMeasure (Euc K × Euc K))
    (Fh : ℕ → Ω → Euc K → Euc K) (PiK : H → Euc K) (g : Euc K → ℝ) (cK : ℝ → ℝ) (c' : ℝ)
    (S : Set (Euc K)) (Q G : Euc K → Euc K),
    MK.PosDef →
    iIndepFun Z Pr → (∀ i, HasLaw (Z i) (P : Measure (Euc K)) Pr) → (P : Measure (Euc K)) ≪ volume →
    (μ : Measure (Euc K)) (Metric.closedBall 0 R)ᶜ = 0 → (∀ u ∈ Metric.closedBall (0 : Euc K) R, ‖mvec MK u‖ ≤ L') →
    (μ : Measure (Euc K)) ≪ volume → Convex ℝ S → (μ : Measure (Euc K)) Sᶜ = 0 →
    ConvexOn ℝ univ ψ → (∀ x x', |ψ x - ψ x'| ≤ L * ‖x - x'‖) →
    Measurable F → (P : Measure (Euc K)).map F = μ → (∀ᵐ x ∂(P : Measure (Euc K)), IsSubgrad ψ x (mvec MK (F x))) →
    IsMGradMap MK (μ : Measure (Euc K)) (P : Measure (Euc K)) Q →
    ContinuousOn Q (interior S) → ContinuousOn G (interior (P : Measure (Euc K)).support) →
    MapsTo Q (interior S) (interior (P : Measure (Euc K)).support) →
    MapsTo G (interior (P : Measure (Euc K)).support) (interior S) →
    (∀ u ∈ interior S, G (Q u) = u) → (∀ y ∈ interior (P : Measure (Euc K)).support, Q (G y) = y) →
    (∀ n ω, (γ n ω : Measure (Euc K × Euc K)).fst = (empiricalMeasure (fun i => Z i ω) n : Measure (Euc K))) →
    (∀ n ω, (γ n ω : Measure (Euc K × Euc K)).snd = μ) →
    (∀ n ω, (γ n ω : Measure (Euc K × Euc K)).support ⊆ {p | IsSubgrad (ψh n ω) p.1 (mvec MK p.2)}) →
    (∀ n ω x x', |ψh n ω x - ψh n ω x'| ≤ L' * ‖x - x'‖) →
    (∀ n ω, ∀ x ∈ interior (P : Measure (Euc K)).support, IsSubgrad (ψh n ω) x (mvec MK (Fh n ω x))) →
    (∀ a b, g (a + b) ≤ g a + g b) → (∀ a, g (-a) = g a) → (∀ a, g a ≤ c' * ‖a‖) → Continuous cK →
    (∀ z ∈ interior (P : Measure (Euc K)).support, g (G z) ≤ 1) →
      ∀ᵐ ω ∂Pr, ∀ 𝒦 : Set (Euc K), IsCompact 𝒦 → 𝒦 ⊆ interior (P : Measure (Euc K)).support →
        TendstoUniformlyOn (fun n => Fh n ω) G atTop 𝒦 ∧
        TendstoUniformlyOn (fun n x => 1 - g (Fh n ω (PiK x))) (fun x => 1 - g (G (PiK x))) atTop
          {x | PiK x ∈ 𝒦} ∧
        TendstoUniformlyOn (fun n x => 1 - cK (g (Fh n ω (PiK x)))) (fun x => 1 - cK (g (G (PiK x)))) atTop
          {x | PiK x ∈ 𝒦}

/-! ### trimmed MMD `thm:split` at `α = 0`: plain sample means -/

open StatFormal.Wave29i (splitTrimLo splitTrimUp splitVarLo splitSE) in
/-- `ass:split`, "if `α = 0` both terms are sample means": for `n ≥ 1`, the two extreme trimmed means of
`eq:splitstat` at `α = 0` are the sample mean `v̄ = n⁻¹ Σ v_i`, and the frozen plug-in variance `splitVarLo` at
`α = 0` is the (`1/n`) sample variance `n⁻¹ Σ (v_i − v̄)²`; hence the frozen plug-in standard error at `α = 0` is
`ŝe = √(s²_X/n + s²_Y/m)`. -/
def split_zero_means : Prop :=
  ∀ (n m : ℕ) (v : Fin n → ℝ) (vx : Fin n → ℝ) (vy : Fin m → ℝ), 0 < n → 0 < m →
    splitTrimLo n 0 v = (∑ i, v i) / n ∧ splitTrimUp n 0 v = (∑ i, v i) / n ∧
    splitVarLo n 0 v = (∑ i, (v i - (∑ j, v j) / n) ^ 2) / n ∧
    splitSE n m 0 vx vy = √((∑ i, (vx i - (∑ j, vx j) / n) ^ 2) / n / n +
      (∑ j, (vy j - (∑ k, vy k) / m) ^ 2) / m / m)

open StatFormal.Wave29i (splitStat) in
open StatFormal.Wave17a (sepVal) in
open StatFormal.TrimmedMMD.Concentration (region) in
/-- `thm:split` at `α = 0`, asymptotic normality, NO regularity condition (as printed in `ass:split`): the population
separation at `α = 0` is the real `T₀ = E_P h − E_Q h` (`h = ⟨f, φ⟩`), and `√n (T̂_n − T₀) ⇝ N(0, σ₀²)`,
`σ₀² = Var_P h + Var_Q h/κ`, for `m(n)/n → κ > 0`. -/
def split_zero_asymp_normal : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ' κ : ℝ) (f : H)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → 𝒳) (m : ℕ → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ') →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X μ → iIndepFun Y μ →
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ → (∀ i, μ.map (X i) = P) → (∀ i, μ.map (Y i) = Q) →
    0 < κ → Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ) →
      sepVal f (region φ 0 P) (region φ 0 Q) = ((∫ x, ⟪f, φ x⟫ ∂P - ∫ x, ⟪f, φ x⟫ ∂Q : ℝ) : EReal) ∧
        TendstoInDistribution
          (fun (n : ℕ) ω => √(n : ℝ) * (splitStat φ f X Y m 0 n ω - (∫ x, ⟪f, φ x⟫ ∂P - ∫ x, ⟪f, φ x⟫ ∂Q)))
          atTop id (fun _ => μ)
          (gaussianReal 0 (Var[fun x => ⟪f, φ x⟫; P] + Var[fun x => ⟪f, φ x⟫; Q] / κ).toNNReal)

open StatFormal.Wave29i (splitStat splitSEn) in
open StatFormal.Wave17a (sepVal) in
open StatFormal.TrimmedMMD.Concentration (region) in
/-- `thm:split` at `α = 0`, coverage of the plug-in normal lower limit: if `σ₀² > 0`,
`P(T̂_n − z ŝe_n ≤ sep) → Φ(z)` for every `z`, with the frozen plug-in `ŝe_n = splitSEn` at `α = 0`. -/
def split_zero_coverage : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ' κ : ℝ) (f : H)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → 𝒳) (m : ℕ → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ') →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X μ → iIndepFun Y μ →
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ → (∀ i, μ.map (X i) = P) → (∀ i, μ.map (Y i) = Q) →
    0 < κ → Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ) →
    0 < Var[fun x => ⟪f, φ x⟫; P] + Var[fun x => ⟪f, φ x⟫; Q] / κ →
      ∀ z : ℝ, Tendsto (fun n => μ.real {ω | ((splitStat φ f X Y m 0 n ω - z * splitSEn φ f X Y m 0 n ω : ℝ) : EReal) ≤
          sepVal f (region φ 0 P) (region φ 0 Q)}) atTop (𝓝 ((gaussianReal 0 1).real (Iic z)))

open StatFormal.Wave29i (splitStat splitSEn) in
open StatFormal.Wave17a (sepVal) in
open StatFormal.TrimmedMMD.Concentration (region) in
/-- `thm:split` at `α = 0`, UNCONDITIONAL (no regularity condition, no non-degeneracy `σ₀² > 0`): with the plug-in
lower limit `T̂_δ = T̂_n − z ŝe_n` (`Φ(Ioi z) = δ`), coverage `liminf P(T̂_δ ≤ sep) ≥ 1 − δ`, asymptotic level `δ` of
"reject `H_{0,0}` if `T̂_δ > 0`" (under `TV(P,Q) ≤ 0`), and rejection on the coverage event certifies `TV(P,Q) > 0`;
the triple of the frozen Wave 29i `split_level_discharged` at `α = 0`. -/
def split_zero_level : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ' κ δ z : ℝ) (f : H)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → 𝒳) (m : ℕ → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ') →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X μ → iIndepFun Y μ →
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ → (∀ i, μ.map (X i) = P) → (∀ i, μ.map (Y i) = Q) →
    0 < κ → Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ) →
    (gaussianReal 0 1).real (Ioi z) = δ →
      (∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, 1 - δ - η ≤ μ.real {ω |
          ((splitStat φ f X Y m 0 n ω - z * splitSEn φ f X Y m 0 n ω : ℝ) : EReal) ≤
            sepVal f (region φ 0 P) (region φ 0 Q)}) ∧
      (StatFormal.Distances.tvDist P Q ≤ 0 →
          ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
            μ {ω | 0 < splitStat φ f X Y m 0 n ω - z * splitSEn φ f X Y m 0 n ω} ≤ ENNReal.ofReal (δ + η)) ∧
      (∀ n, ∀ ω, ((splitStat φ f X Y m 0 n ω - z * splitSEn φ f X Y m 0 n ω : ℝ) : EReal) ≤
          sepVal f (region φ 0 P) (region φ 0 Q) →
          0 < splitStat φ f X Y m 0 n ω - z * splitSEn φ f X Y m 0 n ω → 0 < StatFormal.Distances.tvDist P Q)

end Claims

end StatFormal.Wave29w
