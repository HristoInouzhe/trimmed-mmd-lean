import StatFormal.Archive.OTFD.Bands2.Statements
import StatFormal.Archive.TrimmedMMD.Lower.Statements
import StatFormal.Archive.TrimmedMMD.Unconditional.Statements
import StatFormal.Archive.Wave29i.Statements
import StatFormal.Archive.Wave29l.Statements
import StatFormal.Archive.WaveP2d.Statements
import StatFormal.Archive.Wave12c.Statements
import StatFormal.Archive.WaveP3b.Statements
import StatFormal.Archive.Defects2.Statements
import StatFormal.Archive.Wave11b.Statements
import StatFormal.Archive.Wave23a.Statements
import StatFormal.Archive.Wave4b.Statements
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# FROZEN STATEMENTS — wave 30at: coverage-note gaps (otfd B `lem:ext-solver-error` band edges; trimmed MMD
# `cor:lower` with `thm:split` discharged, `thm:rate` polynomial margin and `O(·)` reading, `thm:rffjoint` `O(·)`
# readings, `thm:trimconsist` rates and the lower-density limit; SB journal `cor:smoothing` `C^∞`, `prop:debiased`
# Gaussian minimiser, `prop:embed` optimality)

Sources (current text, read 2026-10-21):
* otfd B `lem:ext-solver-error` (`otfd/papers/B_bands/supplement.tex:1777-1795`, HEAD 72343d7e), the sentence
  "Consequently, with `c_j(t) = ⟨e(t), Z_j⟩` and `T_{f,f'}(t) = tanh(osc(f−f')/(4ε))(max_j c_j(t) − min_j c_j(t))`, the
  upper band edges built from `f` and from `f'` differ by at most `T_{f,f'}(t)` at every `t`, and so do the lower band
  edges and the inner edges … evaluated on a common finite set `F_{K,p}`" (`:1786-1794`); proof Step 4 (`:1854-1859`).
* trimmed MMD (`trimmed-mmd/paper.tex`, HEAD 58caecc): `thm:rate` (`:922-944`, the display "For `ω(ε) = c₀ε^γ` this
  reads …" `:932-943`); `thm:split` (`:1064-1076`: bootstrap variance, `T̂_δ` the one-sided `1 − δ` lower limit, reject
  iff `T̂_δ > 0`, asymptotic level `δ`); `cor:lower` (`:1091-1105`); `thm:trimconsist` (`:1555-1590`, the sentences
  "Since `Λ_n = O((n∧m)^{−1/4})`, both … are `O_P((n∧m)^{−1/4})`" and "If (Q) is weakened to a lower density bound
  alone, … both quantities tend to `0` in probability, but without a rate"); `thm:rffjoint` (`:1672-1691`, "which is
  `O(min(n,m)^{−1/2}) + O(r^{−1/4})`" and "which is `O(r^{−1/2})` whenever the discrepancy is bounded away from zero").
* SB journal (`data-fairness-repair-journal/journal/supp/`, read-only copy, HEAD 2ae7a22): `cor:smoothing`
  (`s_setting.tex:197-210`, with `eq:convolution` `:180-184`); `prop:debiased` (`s_univariate.tex:95-112`) with
  `eq:sinkbary` (`:18-27`), `prop:sbbary` (`:43-60`) and `eq:ceps`; `prop:embed` (`s_univariate.tex:160-170`) with
  `eq:wbary`, `def:repair` (`s_setting.tex:148-158`: `C_ε(R_s, ν) < ∞`) and the remark after `ass:ac` (`:91-95`:
  `C_ε = +∞` as soon as one marginal has an atom).
Frozen objects reused (imported, not copied): OTFD `Bands` (`Qent`), `Bands2` (`edgeUp`, `edgeLo`, `osc`, `solverT`);
TrimmedMMD (`tau`, `rn`, `alphaHat`), `TrimmedMMD/Unconditional` (`Dpop`, `Demp`), `TrimmedMMD/Lower` (`alphaLo`),
`TrimmedMMD/Concentration` (`region`), `BangBang` (`capped`, `qp`), `Projection` (`IsMinNorm`); Wave 29i (`splitStat`,
`splitSEn`, `splitAss`), Wave 29l (`splitBootSEn`, `splitBootPercn`); Wave P2d (`rffFeat`, `rffEps`, `rffH`), Wave 24e
(`unifCircle`, `bochnerKernel`); Wave 12c (`etaTC`, `zetaTC`, `lamTC`, `witFn`, `quantileAt`, `QDensity`,
`QDensityLower`, `plugDensity`, `tHat`), Wave 4b (`witness`, `endpointMixture`, `endpointMixture1`); Wave P3b
(`sqCost`), Defects2 (`DebiasedEq`), Wave 11b (`condLaw`), Wave 9b (`flowMap`), Wave 23a (`IsBarycenter`); Tau Ceti
(`entropicTransportCost`, `Measure.quantile`). New definitions: `sinkDivR` (`S_ε` as a real number), `debObj`.

Covered:
* otfd B `lem:ext-solver-error`, band-edge consequence: `ext_solver_edges` (upper and lower edges over ANY set `S` of
  reference points — the region `A_{K,p}` or a common finite `F_{K,p}` — differ by at most `T_{f,f'}(t)`, both
  directions, every `t`, edges in `EReal`). With the certified `ext_solver_error`, `ext_solver_sharp` the lemma is
  fully covered.
* trimmed MMD `cor:lower`: `cor_lower_boot` (the test of `thm:split` as printed: bootstrap variance), `cor_lower_split`
  (plug-in variance), `cor_lower_perc` (percentile bootstrap, the implementation): `limsup P(α̂_lo > TV) ≤ δ` with each
  level tested by the certified `thm:split` (its own hypotheses `ass:split` at `α_j > 0`, i.i.d. folds, `m/n → κ`);
  the frozen `cor_lower` had per-level validity as a hypothesis.
* trimmed MMD `thm:rate`, polynomial margin: `rate_poly` (unconditional, `|α̂ − α*| ≤ (2τ/c₀)^{1/γ}` on a measurable
  event of probability `≥ 1 − δ`; the `O(·)` with the explicit absolute constant `24`; the `min(n,m)^{−1/(2γ)}` form).
* trimmed MMD `thm:rffjoint`: `rffjoint_rates` (explicit `C_s min(n,m)^{−1/2} + C_r r^{−1/4}`; `O(r^{−1/2})` both when
  `D̂^{(r)} + D̂ ≥ c` and when the population `D ≥ c` and the first bound is `≤ c/2`).
* trimmed MMD `thm:trimconsist`: `trimconsist_lam_rate` (`Λ_n ≤ C (n∧m)^{−1/4}`), `trimconsist_OP` (`O_P((n∧m)^{−1/4})`
  for both quantities, every empirical optimum, every tie weight), `trimconsist_lower_prob` (lower density alone: both
  quantities `→ 0` in probability, uniformly over optima and tie weights).
* SB `cor:smoothing`: `smoothing_smooth` (`ℝ^d`: `C^∞`, every derivative bounded, positivity, the sup bound);
  `smoothing_smooth_one` (`d = 1`: the same, `F' = ρ`, `F` `C^∞`, the quantile `F^{-1}` is `C^∞` on `(0,1)` and is the
  two-sided inverse). With the certified Wave 4b `smoothing_density`, `smoothing_cdf` the corollary is fully covered.
* SB `prop:debiased`: `debiased_gauss_min` (a Gaussian target `N(b, τ²)` minimises `eq:sinkbary` over Gaussian targets
  iff `b = a⋆` and `τ` is the root; a minimiser exists). With Defects2 (uniqueness, bracket) and Wave 23a (limits) the
  proposition is fully covered.
* SB `prop:embed`: `embed_optimal` (the corner repair `F_{ν^W}^{-1} ∘ F_{R_s} ∘ h` is `σ(X,S)`-measurable, in `L²`,
  demographically fair, and minimises `E(Y − g)²` over all fair `σ(X,S)`-measurable `g ∈ L²`: the Chzhen et al. /
  Le Gouic et al. characterisation, proved); `embed_atomless_needed` (the atomless hypothesis cannot be dropped: for
  `R_0 = δ_0`, `R_1 = U[0,1]` no barycenter makes the corner repair fair). With Wave 24c `embed_corner`,
  `embed_identity` the proposition is fully covered; the citation itself is an attribution.

Not covered (declared):
* `prop:embed`: uniqueness of the optimal fair predictor (not printed); `S` binary (`Fin 2`), as in the paper.
* `thm:split` bootstrap at `B` replicates (the frozen Wave 29l objects are the ideal bootstrap), inherited.

Encodings (to be checked by the critic):
* Band edges: frozen Bands2 `edgeUp`/`edgeLo` (`m(t) + h_S(±e(t))` in `EReal`); `T_{f,f'}(t) = solverT ε (osc (f − f'))
  Z (e t)`; `S` arbitrary (empty `S` gives `⊥`/`⊤` edges, for which the inequalities hold trivially).
* `cor:lower`: the rejection events `{T̂_δ > 0}` at each grid level, grid strictly increasing in `[0,1)`, fixed in
  advance; probabilities are `μ` applied to the event (outer measure: measurability of the bootstrap events is not
  needed, and an outer-measure upper bound is the stronger form), as in the frozen Wave 29i/29l level clauses; `δ =
  P(N(0,1) > z) ∈ (0,1)`.
* `thm:rate`: `ω(ε) = c₀ε^γ`, `c₀, γ > 0`, `ass:margin` as the hypothesis `c₀e^γ ≤ D(α* − e)` on `[0, α*]`, the proviso
  `2τ ≤ ω(α*)`; `α*` any zero of `D` in `[0,1)` (as in the frozen `Unconditional.rate`); "`O(·)`" is an explicit
  inequality with the absolute constant `24` (`log 4 < 2`).
* `thm:rffjoint`: the frozen `rffjoint_uncond` setting; `C_s = 2κ(4 + √(2 log(6/δ)))/(1−α)`,
  `h_r = h + 2√(2 log(3/δ))`, `C_r = 2κ√h_r`; `(·)^{−1/2}`, `(·)^{−1/4}` are real powers of `min(n,m) ≥ 1`, `r ≥ 1`.
* `thm:trimconsist`: the frozen Wave 12c setting; "fix `α < α*`" is `D = ‖d*‖ > 0` (equivalent by the certified
  `eq:zeroeq`); `O_P`: for every `δ` there are `M` and `N₀` with the bounds `≤ M(n∧m)^{−1/4}` on one measurable event of
  probability `≥ 1 − δ` for all `n, m ≥ N₀`; "in probability": for every `δ, η > 0`, eventually, on one measurable event
  of probability `≥ 1 − δ`, both quantities `≤ η`.
* `cor:smoothing`: `ρ_t` the push-forward of an arbitrary probability plan (marginals, `𝒫₂` and optimality unused, as
  the paper stresses); `N(0, v I_d)` is its Lebesgue density (frozen Wave 4b `gaussianIso`), `d = 1` Mathlib's
  `gaussianReal`; "`C^∞`" is `ContDiff ℝ ∞`; "all derivatives bounded" is `∀ k, sup_y ‖D^kρ(y)‖ < ∞` (`iteratedFDeriv`;
  `iteratedDeriv` for `d = 1`, same norms); `F^{-1}` is Tau Ceti's quantile `inf{x : u ≤ F(x)}`.
* `prop:debiased`: Gaussian targets are `N(b, τ²)`, `b ∈ ℝ`, `τ > 0`; `S_ε` with Tau Ceti's `C_ε` (cost `½(x−y)²`,
  `ε KL(π ‖ μ ⊗ ν)`) as a real number (finite at Gaussians, certified `gaussplan_eot`); the paper's `−εH(π)`
  normalisation differs by `−ε(H(μ) + H(ν))`, which cancels in `S_ε`.
* `prop:embed`: `(Ω, P)`, a sub-σ-algebra `m` (the information `σ(X, S)`), `S`, `U = h(X,S)` `m`-measurable, `Y ∈ L²`,
  `U = E[Y | m]` a.s. ("`h` the regression function"); `R_s = 𝓛(U | S = s)` atomless (implied in the paper by
  `def:repair`: `C_ε(R_s, ν) < ∞` forces atomless `R_s`, remark after `ass:ac`); `ν` any `W₂` barycenter with weights
  `P(S = s)` (the frozen Wave 23a `IsBarycenter`, Tau Ceti `W₂`); fairness of a predictor `g` is
  `𝓛(g | S = 0) = 𝓛(g | S = 1)`; the repair is the frozen `flowMap` (Tau Ceti quantile ∘ cdf).

Critic notes (wave 30at critic, 2026-10-21): all 14 claims build, axioms `[propext, Classical.choice, Quot.sound]`;
compositions go through the frozen claims (`Unconditional.rate`, `WaveP2d.rffjoint_uncond`, `Wave12c.trimconsist`,
Wave 29i/29l/29w/30d `thm:split` level clauses, Defects2 `debiased_root_unique`, WaveP3b `gaussplan_cepsval`, Wave 11b
`flow_push`/`flow_cost`/`flow_minimal`, Wave 23a `qgrowth_one_dim`, Wave 4b `smoothing_cdf`); no hypothesis restates a
conclusion. Witnesses `~/.cache/w30at-critic/{NonVac,Embed}.lean` (`cor:lower` bundles on constant data at grid `![0]`;
`embed_optimal` on `unif(Fin 2) ⊗ U[0,1]` with `ν = U[0,1]`; `debiased_gauss_min` shows the shifted mean is not a
minimiser; the `∞` of `cor:smoothing` is `(⊤ : ℕ∞)`, i.e. `C^∞`, not `ω`). `rate_poly`, `trimconsist_OP`,
`trimconsist_lower_prob`, `rffjoint_rates`: hypothesis bundles are the frozen ones (non-vacuity inherited), `rate_poly`'s
polynomial margin has the analytic witness `P = ½(δ_0 + δ_1)`, `Q = δ_0`, `φ = id`, `κ = 1`: `D_α = (1 − 2α)/(2(1 − α))`,
`α* = ½`, `c₀ = γ = 1`. Bochner integrals in `trimconsist_*` and `embed_optimal` are of bounded measurable resp. `L¹`
integrands (no junk). `embed_atomless_needed` is a hypothesis-necessity record, not a defect (docstring corrected).
`prop:debiased`: `τ > 0` is the paper's setting (a point-mass target has `C_ε = +∞` in the `−εH(π)` normalisation).
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Matrix
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace Pointwise

namespace StatFormal.Wave30at

/-! ### SB `prop:debiased`: the debiased Sinkhorn objective over Gaussian targets -/

open TauCeti in
/-- The debiased Sinkhorn divergence `S_ε(μ, ν) = C_ε(μ, ν) − ½C_ε(μ, μ) − ½C_ε(ν, ν)` (`eq:sinkbary`), cost
`½(x − y)²`, with `C_ε = inf_π ∫ c dπ + ε KL(π ‖ μ ⊗ ν)` (Tau Ceti `entropicTransportCost`), as real numbers. For
`C^{paper}_ε = C_ε − ε(H(μ) + H(ν))` (the paper's `−εH(π)` normalisation, `eq:static`) the entropy constants cancel
exactly in `S_ε`, so this IS the paper's `S_ε`; at Gaussian marginals every value is finite (certified `gaussplan_eot`),
so `toReal` is not a junk value there. -/
def sinkDivR (ε : ℝ) (μ ν : Measure ℝ) : ℝ :=
  (entropicTransportCost StatFormal.WaveP3b.sqCost ε.toNNReal μ ν).toReal -
    (entropicTransportCost StatFormal.WaveP3b.sqCost ε.toNNReal μ μ).toReal / 2 -
    (entropicTransportCost StatFormal.WaveP3b.sqCost ε.toNNReal ν ν).toReal / 2

/-- The objective of `eq:sinkbary` at the Gaussian target `N(b, τ²)`, groups `R_s = N(a_s, σ_s²)`:
`Σ_s p_s S_ε(R_s, N(b, τ²))`. -/
def debObj {S : ℕ} (ε : ℝ) (p a σ : Fin S → ℝ) (b τ : ℝ) : ℝ :=
  ∑ s, p s * sinkDivR ε (gaussianReal (a s) ((σ s) ^ 2).toNNReal) (gaussianReal b (τ ^ 2).toNNReal)

namespace Claims

open StatFormal.OTFD.Bands (Qent)
open StatFormal.OTFD.Bands2 (edgeUp edgeLo osc solverT)

/-! ### otfd B `lem:ext-solver-error`, the band-edge consequence -/

/-- `lem:ext-solver-error`, "Consequently": with `c_j(t) = ⟨e(t), Z_j⟩` and
`T_{f,f'}(t) = tanh(osc(f − f')/(4ε)) (max_j c_j(t) − min_j c_j(t))`, the upper band edges built from `f` and from
`f'` over any set `S` of reference points (the region `A_{K,p}`, or a common finite set `F_{K,p}` for the inner edges)
differ by at most `T_{f,f'}(t)` at every `t`, and so do the lower band edges. -/
def ext_solver_edges : Prop :=
  ∀ (n K : ℕ) (𝒯 : Type) (ε : ℝ) (M : Matrix (Fin K) (Fin K) ℝ) (Z : Fin n → Fin K → ℝ) (f f' : Fin n → ℝ)
    (S : Set (Fin K → ℝ)) (mo : 𝒯 → ℝ) (e : 𝒯 → Fin K → ℝ),
    0 < n → 0 < ε → M.PosDef → ∀ t : 𝒯,
      edgeUp (Qent ε M Z f) S (mo t) (e t) ≤
          edgeUp (Qent ε M Z f') S (mo t) (e t) + (solverT ε (osc (f - f')) Z (e t) : EReal) ∧
      edgeUp (Qent ε M Z f') S (mo t) (e t) ≤
          edgeUp (Qent ε M Z f) S (mo t) (e t) + (solverT ε (osc (f - f')) Z (e t) : EReal) ∧
      edgeLo (Qent ε M Z f) S (mo t) (e t) ≤
          edgeLo (Qent ε M Z f') S (mo t) (e t) + (solverT ε (osc (f - f')) Z (e t) : EReal) ∧
      edgeLo (Qent ε M Z f') S (mo t) (e t) ≤
          edgeLo (Qent ε M Z f) S (mo t) (e t) + (solverT ε (osc (f - f')) Z (e t) : EReal)

/-! ### trimmed MMD `cor:lower` with each grid level tested by `thm:split` -/

open StatFormal.Wave29i (splitStat splitSEn splitAss) in
open StatFormal.TrimmedMMD.Lower (alphaLo) in
/-- `cor:lower` UNCONDITIONAL: each `H_{0,α_j}` (grid `0 ≤ α_1 < ⋯ < α_J < 1` fixed in advance) is tested by
`thm:split` with the plug-in standard error (`T̂_n − z ŝe_n > 0`, witness direction `f_j` fixed, `ass:split` at
every `α_j > 0`; at `α_j = 0` no assumption), and the grid is read upward (`eq:downclosed`). Then
`P(α̂_lo > TV(P,Q))` is asymptotically at most `δ = P(N(0,1) > z)`, with no multiplicity correction. -/
def cor_lower_split : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ' κ δ z : ℝ)
    (J : ℕ) (α : Fin J → ℝ) (f : Fin J → H) (q q' : Fin J → ℝ)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → 𝒳) (m : ℕ → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ') → StrictMono α → (∀ j, α j ∈ Ico (0 : ℝ) 1) →
    (∀ j, 0 < α j → splitAss P (fun x => ⟪f j, φ x⟫) (1 - α j) (q j) ∧
      splitAss Q (fun x => ⟪f j, φ x⟫) (α j) (q' j)) →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X μ → iIndepFun Y μ →
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ → (∀ i, μ.map (X i) = P) → (∀ i, μ.map (Y i) = Q) →
    0 < κ → Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ) →
    (gaussianReal 0 1).real (Ioi z) = δ →
      limsup (fun n => μ {ω | StatFormal.Distances.tvDist P Q < alphaLo α
          (fun j => 0 < splitStat φ (f j) X Y m (α j) n ω - z * splitSEn φ (f j) X Y m (α j) n ω)}) atTop
        ≤ ENNReal.ofReal δ

open StatFormal.Wave29i (splitStat splitAss) in
open StatFormal.Wave29l (splitBootSEn) in
open StatFormal.TrimmedMMD.Lower (alphaLo) in
/-- `cor:lower` UNCONDITIONAL with the test of `thm:split` as printed: the variance of `T̂` estimated by the
nonparametric bootstrap on the second-fold scalars, `T̂_δ = T̂ − z ŝe*_n` the one-sided `1 − δ` lower limit, reject
`H_{0,α_j}` iff `T̂_δ > 0`; otherwise as `cor_lower_split`. -/
def cor_lower_boot : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ' κ δ z : ℝ)
    (J : ℕ) (α : Fin J → ℝ) (f : Fin J → H) (q q' : Fin J → ℝ)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → 𝒳) (m : ℕ → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ') → StrictMono α → (∀ j, α j ∈ Ico (0 : ℝ) 1) →
    (∀ j, 0 < α j → splitAss P (fun x => ⟪f j, φ x⟫) (1 - α j) (q j) ∧
      splitAss Q (fun x => ⟪f j, φ x⟫) (α j) (q' j)) →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X μ → iIndepFun Y μ →
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ → (∀ i, μ.map (X i) = P) → (∀ i, μ.map (Y i) = Q) →
    0 < κ → Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ) →
    (gaussianReal 0 1).real (Ioi z) = δ →
      limsup (fun n => μ {ω | StatFormal.Distances.tvDist P Q < alphaLo α
          (fun j => 0 < splitStat φ (f j) X Y m (α j) n ω - z * splitBootSEn φ (f j) X Y m (α j) n ω)}) atTop
        ≤ ENNReal.ofReal δ

open StatFormal.Wave29i (splitAss) in
open StatFormal.Wave29l (splitBootPercn) in
open StatFormal.TrimmedMMD.Lower (alphaLo) in
/-- `cor:lower` UNCONDITIONAL with the percentile-bootstrap lower limit of the implementation
(`T̂_δ` = the bootstrap `δ`-quantile of `T̂*`, reject iff `T̂_δ > 0`); otherwise as `cor_lower_split`. -/
def cor_lower_perc : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ' κ δ z : ℝ)
    (J : ℕ) (α : Fin J → ℝ) (f : Fin J → H) (q q' : Fin J → ℝ)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → 𝒳) (m : ℕ → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ') → StrictMono α → (∀ j, α j ∈ Ico (0 : ℝ) 1) →
    (∀ j, 0 < α j → splitAss P (fun x => ⟪f j, φ x⟫) (1 - α j) (q j) ∧
      splitAss Q (fun x => ⟪f j, φ x⟫) (α j) (q' j)) →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X μ → iIndepFun Y μ →
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ → (∀ i, μ.map (X i) = P) → (∀ i, μ.map (Y i) = Q) →
    0 < κ → Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ) →
    (gaussianReal 0 1).real (Ioi z) = δ →
      limsup (fun n => μ {ω | StatFormal.Distances.tvDist P Q < alphaLo α
          (fun j => 0 < splitBootPercn φ (f j) X Y m (α j) δ n ω)}) atTop
        ≤ ENNReal.ofReal δ

/-! ### trimmed MMD `thm:rate`, the polynomial margin `ω(ε) = c₀ε^γ` -/

open StatFormal.TrimmedMMD (tau alphaHat) in
open StatFormal.TrimmedMMD.Unconditional (Dpop Demp) in
/-- `thm:rate`, "For `ω(ε) = c₀ε^γ` this reads": unconditionally (concentration events constructed), on a
measurable event of probability `≥ 1 − δ`, `|α̂ − α*| ≤ (2τ_{n,m}(α*,δ)/c₀)^{1/γ}`; the `O(·)` with the explicit
absolute constant `24`, `(2τ/c₀)^{1/γ} ≤ (24 κ/(c₀(1−α*)) √((1 + log(1/δ))/min(n,m)))^{1/γ}`, and the latter is
`C^{1/γ} min(n,m)^{−1/(2γ)}` (the `min(n,m)^{−1/(2γ)}` rate). -/
def rate_poly : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ δ αs c0 γ : ℝ) (n m : ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < κ → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
    αs ∈ Ico (0 : ℝ) 1 → Dpop φ P Q αs = 0 → 0 < c0 → 0 < γ →
    (∀ e ∈ Icc (0 : ℝ) αs, c0 * e ^ γ ≤ Dpop φ P Q (αs - e)) →
    2 * tau κ αs δ n m ≤ c0 * αs ^ γ →
      (∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤ ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | |alphaHat (Demp φ z.1 z.2) (fun α => tau κ α δ n m) - αs| ≤
          (2 * tau κ αs δ n m / c0) ^ (1 / γ)}) ∧
      (2 * tau κ αs δ n m / c0) ^ (1 / γ) ≤
        (24 * κ / (c0 * (1 - αs)) * √((1 + Real.log (1 / δ)) / (min n m : ℕ))) ^ (1 / γ) ∧
      (24 * κ / (c0 * (1 - αs)) * √((1 + Real.log (1 / δ)) / (min n m : ℕ))) ^ (1 / γ) =
        (24 * κ * √(1 + Real.log (1 / δ)) / (c0 * (1 - αs))) ^ (1 / γ) * ((min n m : ℕ) : ℝ) ^ (-(1 / (2 * γ)))

/-! ### trimmed MMD `thm:rffjoint`, the `O(·)` readings -/

open StatFormal.WaveP2d (rffFeat rffEps rffH) in
open StatFormal.TrimmedMMD.Unconditional (Dpop Demp) in
/-- `thm:rffjoint`, "which is `O(min(n,m)^{−1/2}) + O(r^{−1/4})`" and "which is `O(r^{−1/2})` whenever the discrepancy
is bounded away from zero", with explicit constants: on the certified event (`WaveP2d` `rffjoint_uncond`),
`|D̂^{(r)} − D| ≤ C_s min(n,m)^{−1/2} + C_r r^{−1/4}` with `C_s = 2κ(4 + √(2 log(6/δ)))/(1−α)` and
`C_r = 2κ √(h + 2√(2 log(3/δ)))` (`h = 4 + 12 diam(𝒳) σ_Λ`); if `D̂^{(r)} + D̂ ≥ c > 0` then
`|D̂^{(r)} − D̂| ≤ (4/c) κ²(h + 2√(2 log(3/δ))) r^{−1/2}`; and if the population discrepancy is bounded away from zero,
`D ≥ c > 0`, then as soon as `C_s min(n,m)^{−1/2} + C_r r^{−1/4} ≤ c/2`,
`|D̂^{(r)} − D̂| ≤ (8/c) κ²(h + 2√(2 log(3/δ))) r^{−1/2}`. -/
def rffjoint_rates : Prop :=
  ∀ (d r : ℕ) (𝒳 : Set (EuclideanSpace ℝ (Fin d))) (H Ω : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H] [MeasurableSpace Ω] (Pr : Measure Ω)
    [IsProbabilityMeasure Pr] (Λ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure Λ] (β : Measure ℝ)
    [IsProbabilityMeasure β] (W : Fin r → Ω → EuclideanSpace ℝ (Fin d)) (B : Fin r → Ω → ℝ)
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ α δ : ℝ) (n m : ℕ),
    β = StatFormal.Wave24e.unifCircle → 0 < r → IsCompact 𝒳 → Integrable (fun ω => ‖ω‖ ^ 2) Λ →
    (∀ j, Measurable (W j)) → (∀ j, Measurable (B j)) →
    iIndepFun (fun j ω => (W j ω, B j ω)) Pr → (∀ j, Pr.map (fun ω => (W j ω, B j ω)) = Λ.prod β) →
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < κ →
    (∀ x y : 𝒳, ⟪φ x, φ y⟫ = StatFormal.Wave24e.bochnerKernel κ Λ x y) →
    0 ≤ α → α < 1 → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳) × Ω), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤ ((Measure.pi fun _ : Fin n => P).prod
          ((Measure.pi fun _ : Fin m => Q).prod Pr)) E ∧
        ∀ s ∈ E,
          let Dr := Demp (fun x : 𝒳 => rffFeat κ (fun j => W j s.2.2) (fun j => B j s.2.2) x) s.1 s.2.1 α
          let Dh := Demp φ s.1 s.2.1 α
          let hr := rffH (Metric.diam 𝒳) √(∫ ω, ‖ω‖ ^ 2 ∂Λ) + 2 * √(2 * Real.log (1 / (δ / 3)))
          let Cs := 2 * κ * (4 + √(2 * Real.log (6 / δ))) / (1 - α)
          let Cr := 2 * κ * √hr
          |Dr - Dpop φ P Q α| ≤ Cs * ((min n m : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) + Cr * (r : ℝ) ^ (-(1 / 4 : ℝ)) ∧
          (∀ c : ℝ, 0 < c → c ≤ Dr + Dh → |Dr - Dh| ≤ 4 * κ ^ 2 * hr / c * (r : ℝ) ^ (-(1 / 2 : ℝ))) ∧
          (∀ c : ℝ, 0 < c → c ≤ Dpop φ P Q α →
            Cs * ((min n m : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) + Cr * (r : ℝ) ^ (-(1 / 4 : ℝ)) ≤ c / 2 →
            |Dr - Dh| ≤ 8 * κ ^ 2 * hr / c * (r : ℝ) ^ (-(1 / 2 : ℝ)))

/-! ### trimmed MMD `thm:trimconsist`, rates and the lower-density limit -/

open StatFormal.Wave12c (etaTC zetaTC lamTC) in
/-- `thm:trimconsist`, "`Λ_n = O((n ∧ m)^{−1/4})`": for fixed `κ, α, δ, c_f, D` there is a constant `C` with
`Λ_n ≤ C (n ∧ m)^{−1/4}` for all `n, m ≥ 1`. -/
def trimconsist_lam_rate : Prop :=
  ∀ (κ α δ cf D : ℝ), 0 ≤ κ → 0 ≤ α → α < 1 → 0 < δ → δ < 1 → 0 < cf → 0 ≤ D →
    ∃ C : ℝ, ∀ n m : ℕ, 1 ≤ n → 1 ≤ m →
      lamTC κ (zetaTC (etaTC κ α δ n m) D) cf δ n ≤ C * ((min n m : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))

open StatFormal.Wave12c (witFn quantileAt QDensity plugDensity tHat) in
open StatFormal.TrimmedMMD.Concentration (region) in
open StatFormal.TrimmedMMD.BangBang (capped qp) in
open StatFormal.TrimmedMMD.Projection (IsMinNorm) in
/-- `thm:trimconsist`, "both `P(Â_n △ A*)` and `∫|ĝ_n − g*| dP` are `O_P((n ∧ m)^{−1/4})`": under `(Q)` and
`α < α*` (encoded `D = ‖d*‖ > 0`), for every `δ ∈ (0,1)` there are `M` and `N₀` such that for all `n, m ≥ N₀` one
measurable event of probability `≥ 1 − δ` carries, for every empirical optimum and all tie weights, both bounds
`≤ M (n ∧ m)^{−1/4}`. -/
def trimconsist_OP : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H)
    (κ α ρ cf Cf : ℝ) (dstar : H),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 →
    IsMinNorm (region φ α P - region φ α Q) dstar → 0 < ‖dstar‖ →
    0 < ρ → 0 < cf →
    QDensity P (witFn dstar φ) (quantileAt P (witFn dstar φ) (1 - α)) ρ cf Cf →
    ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ Mc : ℝ, ∃ N₀ : ℕ, ∀ n m : ℕ, N₀ ≤ n → N₀ ≤ m →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤
          ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | ∀ (pr : (Fin n → ℝ) × (Fin m → ℝ)) (γ γh : ℝ),
          pr ∈ capped n α ×ˢ capped m α →
          IsMinOn (qp (fun i => φ (z.1 i)) (fun j => φ (z.2 j))) (capped n α ×ˢ capped m α) pr →
          0 ≤ γ → γ ≤ 1 / (1 - α) → 0 ≤ γh → γh ≤ 1 / (1 - α) →
          let dh := StatFormal.Wave4b.witness φ z.1 z.2 pr
          let tα := quantileAt P (witFn dstar φ) (1 - α)
          let th := tHat φ dh α z.1
          P (symmDiff {x | witFn dh φ x < th} {x | witFn dstar φ x < tα}) ≤
              ENNReal.ofReal (Mc * ((min n m : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))) ∧
          ∫ x, |plugDensity α γh (witFn dh φ) th x - plugDensity α γ (witFn dstar φ) tα x| ∂P ≤
            Mc * ((min n m : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))}

open StatFormal.Wave12c (witFn quantileAt QDensityLower plugDensity tHat) in
open StatFormal.TrimmedMMD.Concentration (region) in
open StatFormal.TrimmedMMD.BangBang (capped qp) in
open StatFormal.TrimmedMMD.Projection (IsMinNorm) in
/-- `thm:trimconsist`, last sentence: "If `(Q)` is weakened to a lower density bound alone, … both quantities tend
to `0` in probability, but without a rate": for every `δ ∈ (0,1)` and `η > 0` there is `N₀` such that for all
`n, m ≥ N₀` one measurable event of probability `≥ 1 − δ` carries, for every empirical optimum and all tie weights,
`P(Â_n △ A*) ≤ η` and `∫|ĝ_n − g*| dP ≤ η`. -/
def trimconsist_lower_prob : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H)
    (κ α ρ cf : ℝ) (dstar : H),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 →
    IsMinNorm (region φ α P - region φ α Q) dstar → 0 < ‖dstar‖ →
    0 < ρ → 0 < cf →
    QDensityLower P (witFn dstar φ) (quantileAt P (witFn dstar φ) (1 - α)) ρ cf →
    ∀ δ η : ℝ, 0 < δ → δ < 1 → 0 < η → ∃ N₀ : ℕ, ∀ n m : ℕ, N₀ ≤ n → N₀ ≤ m →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳)), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤
          ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) E ∧
        E ⊆ {z | ∀ (pr : (Fin n → ℝ) × (Fin m → ℝ)) (γ γh : ℝ),
          pr ∈ capped n α ×ˢ capped m α →
          IsMinOn (qp (fun i => φ (z.1 i)) (fun j => φ (z.2 j))) (capped n α ×ˢ capped m α) pr →
          0 ≤ γ → γ ≤ 1 / (1 - α) → 0 ≤ γh → γh ≤ 1 / (1 - α) →
          let dh := StatFormal.Wave4b.witness φ z.1 z.2 pr
          let tα := quantileAt P (witFn dstar φ) (1 - α)
          let th := tHat φ dh α z.1
          P (symmDiff {x | witFn dh φ x < th} {x | witFn dstar φ x < tα}) ≤ ENNReal.ofReal η ∧
          ∫ x, |plugDensity α γh (witFn dh φ) th x - plugDensity α γ (witFn dstar φ) tα x| ∂P ≤ η}

/-! ### SB `prop:debiased`, the minimiser over Gaussian targets -/

open StatFormal.Defects2 (DebiasedEq) in
/-- `prop:debiased`, first sentence: in the setting of `prop:sbbary` (`R_s = N(a_s, σ_s²)`, `σ_s > 0`, `ε > 0`, any
number of groups), a Gaussian target `N(b, τ²)`, `τ > 0`, minimises `eq:sinkbary` over all Gaussian targets iff
`b = a⋆ = Σ_s p_s a_s` and `τ` solves `τ²/c_ε(τ,τ) = Σ_s p_s σ_s²/c_ε(σ_s, τ)` (whose positive root is unique,
certified Defects2 `debiased_root_unique`, so this is `τ^S_ε`); and such a minimiser exists. -/
def debiased_gauss_min : Prop :=
  ∀ (S : ℕ) (ε : ℝ) (p a σ : Fin S → ℝ), 0 < ε → (∀ s, 0 < p s) → ∑ s, p s = 1 → (∀ s, 0 < σ s) →
    (∀ b τ : ℝ, 0 < τ →
      ((∀ b' τ' : ℝ, 0 < τ' → debObj ε p a σ b τ ≤ debObj ε p a σ b' τ') ↔
        (b = ∑ s, p s * a s ∧ DebiasedEq ε p σ τ))) ∧
    ∃ τ : ℝ, 0 < τ ∧ ∀ b' τ' : ℝ, 0 < τ' → debObj ε p a σ (∑ s, p s * a s) τ ≤ debObj ε p a σ b' τ'

/-! ### SB `prop:embed`, optimality of the corner `(t, ε) = (1, 0)` -/

open StatFormal.Wave11b (condLaw) in
open StatFormal.Wave23a (IsBarycenter) in
/-- `prop:embed`, "which is the optimal demographic-parity-constrained predictor under squared loss" (the
characterisation of Chzhen et al. 2020 and Le Gouic et al. 2020, proved here, two groups): `(Ω, P)` a probability
space, `m ≤ 𝓕` the information `σ(X, S)`, `S` and the prediction `U = h(X, S)` `m`-measurable, `U = E[Y | m]` with
`Y ∈ L²` (`h` the regression function), the group laws `R_s = 𝓛(U | S = s)` atomless with `P(S = s) > 0`, and `ν` any
`W₂` barycenter `ν^W` of `(R_0, R_1)` with weights `p_s = P(S = s)` (`eq:wbary`). Then the repair
`g*(ω) = F_ν^{-1}(F_{R_{S(ω)}}(U(ω)))` is `m`-measurable, in `L²`, satisfies demographic parity (`𝓛(g* | S = s) = ν`
for both `s`), and has the smallest risk `E(Y − g)²` among all `m`-measurable `g ∈ L²` with
`𝓛(g | S = 0) = 𝓛(g | S = 1)`. -/
def embed_optimal : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : Ω → Fin 2) (U Y : Ω → ℝ) (ν : Measure ℝ),
    m ≤ mΩ → Measurable[m] S → Measurable[m] U → (∀ s, P (S ⁻¹' {s}) ≠ 0) →
    (∀ s, NullSingletonClass (condLaw P S s U)) →
    MemLp Y 2 P → U =ᵐ[P] condExp m P Y →
    IsBarycenter (fun s => (P (S ⁻¹' {s})).toNNReal) (fun s => condLaw P S s U) ν →
      Measurable[m] (fun ω => StatFormal.Wave9b.flowMap (condLaw P S (S ω) U) ν (U ω)) ∧
      MemLp (fun ω => StatFormal.Wave9b.flowMap (condLaw P S (S ω) U) ν (U ω)) 2 P ∧
      (∀ s, condLaw P S s (fun ω => StatFormal.Wave9b.flowMap (condLaw P S (S ω) U) ν (U ω)) = ν) ∧
      ∀ V : Ω → ℝ, Measurable[m] V → MemLp V 2 P → condLaw P S 0 V = condLaw P S 1 V →
        ∫ ω, (Y ω - StatFormal.Wave9b.flowMap (condLaw P S (S ω) U) ν (U ω)) ^ 2 ∂P ≤ ∫ ω, (Y ω - V ω) ^ 2 ∂P

open StatFormal.Wave23a (IsBarycenter) in
/-- NECESSITY of the atomless hypothesis of `embed_optimal` (NOT a defect of `prop:embed`: the population repair is
defined only when `C_ε(R_s, ν) < ∞` (`def:repair`), which forces atomless `R_s` — the remark after `thm:flow`, "holds
automatically for the population repair"; this claim records that the encoding's atomless hypothesis is not
superfluous): for the group laws `R_0 = δ_0` (`h ≡ 0` on group 0, an atom) and `R_1 = U[0,1]` with weights `(½, ½)`,
a `W₂` barycenter exists, and for EVERY barycenter `ν` the corner formula `F_ν^{-1} ∘ F_{R_s}` is not demographically
fair: the two group laws `(F_ν^{-1} ∘ F_{R_s})_# R_s` differ (group 0 gets a point mass, group 1 gets `ν`, and no
point mass is a barycenter). -/
def embed_atomless_needed : Prop :=
  (∃ ν, IsBarycenter ![(1 / 2 : ℝ≥0), 1 / 2] ![Measure.dirac (0 : ℝ), volume.restrict (Icc (0 : ℝ) 1)] ν) ∧
  ∀ ν, IsBarycenter ![(1 / 2 : ℝ≥0), 1 / 2] ![Measure.dirac (0 : ℝ), volume.restrict (Icc (0 : ℝ) 1)] ν →
    (Measure.dirac (0 : ℝ)).map (StatFormal.Wave9b.flowMap (Measure.dirac 0) ν) ≠
      (volume.restrict (Icc (0 : ℝ) 1)).map (StatFormal.Wave9b.flowMap (volume.restrict (Icc (0 : ℝ) 1)) ν)

/-! ### SB `cor:smoothing`: `C^∞` with bounded derivatives; smoothness of `F_{μ_t}` and `F_{μ_t}^{-1}` -/

open scoped ContDiff in
open StatFormal.Wave4b (endpointMixture) in
/-- `cor:smoothing`, `ℝ^d`: for any probability plan, `μ_t = ρ_t ∗ N(0, εt(1−t) I_d)` has a density `ρ` that is
strictly positive, of class `C^∞`, with all derivatives bounded (`sup_y ‖D^kρ(y)‖ < ∞` for every `k`), and
`ρ ≤ (2πεt(1−t))^{-d/2}`. -/
def smoothing_smooth : Prop :=
  ∀ (d : ℕ) (ε t : ℝ) (plan : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure plan], 0 < ε → 0 < t → t < 1 →
      ∃ ρ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ ρ ∧
        (∀ k : ℕ, ∃ C : ℝ, ∀ y, ‖iteratedFDeriv ℝ k ρ y‖ ≤ C) ∧
        endpointMixture d ε t plan = volume.withDensity (fun y => ENNReal.ofReal (ρ y)) ∧
        ∀ y, 0 < ρ y ∧ ρ y ≤ (2 * Real.pi * (ε * t * (1 - t))) ^ (-(d : ℝ) / 2)

open scoped ContDiff in
open StatFormal.Wave4b (endpointMixture1) in
/-- `cor:smoothing`, `d = 1` (Mathlib's Gaussian): the density `ρ` of `μ_t` is strictly positive, `C^∞` with all
derivatives bounded, `ρ ≤ (2πεt(1−t))^{-1/2}`, and `ρ = F'_{μ_t}`; hence `F_{μ_t}` is `C^∞`, and its inverse on `(0,1)`
— the quantile function `F^{-1}_{μ_t}(u) = inf{x : u ≤ F_{μ_t}(x)}` (Tau Ceti), which satisfies `F(F^{-1}(u)) = u`
on `(0,1)` and `F^{-1}(F(x)) = x` on `ℝ` — is `C^∞` on `(0,1)`. (That `F_{μ_t}` is a strictly increasing bijection
`ℝ → (0,1)` is the certified Wave 4b `smoothing_cdf`.) -/
def smoothing_smooth_one : Prop :=
  ∀ (ε t : ℝ) (plan : Measure (ℝ × ℝ)) [IsProbabilityMeasure plan], 0 < ε → 0 < t → t < 1 →
    (∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧ (∀ k : ℕ, ∃ C : ℝ, ∀ y, ‖iteratedDeriv k ρ y‖ ≤ C) ∧
      endpointMixture1 ε t plan = volume.withDensity (fun y => ENNReal.ofReal (ρ y)) ∧
      (∀ y, 0 < ρ y ∧ ρ y ≤ (2 * Real.pi * (ε * t * (1 - t))) ^ (-(1 : ℝ) / 2)) ∧
      ∀ x, HasDerivAt (cdf (endpointMixture1 ε t plan)) (ρ x) x) ∧
    ContDiff ℝ ∞ (cdf (endpointMixture1 ε t plan)) ∧
    ContDiffOn ℝ ∞ (endpointMixture1 ε t plan).quantile (Ioo 0 1) ∧
    (∀ u ∈ Ioo (0 : ℝ) 1, cdf (endpointMixture1 ε t plan) ((endpointMixture1 ε t plan).quantile u) = u) ∧
    ∀ x, (endpointMixture1 ε t plan).quantile (cdf (endpointMixture1 ε t plan) x) = x

end Claims

end StatFormal.Wave30at
