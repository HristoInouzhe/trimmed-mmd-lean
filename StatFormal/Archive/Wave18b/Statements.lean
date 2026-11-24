import StatFormal.Archive.Wave11a.Statements
import StatFormal.Archive.Wave9b.Statements
import StatFormal.Archive.RobustEquality.CoverageRandom.Statements
import StatFormal.Archive.SBFairness.Statements
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Group.Convolution

/-!
# FROZEN STATEMENTS — wave 18b (QUEUE rows 189–196): robust equality JASA `lem:projection`, `prop:paired`,
# `thm:classcoverage`; SB `prop:randpenalty`, `prop:noisefree`, `prop:excess`; TM `lem:continuity`, `cor:consistency`

Sources (verbatim in `lean-formalisation/inventory/extracted/robust-equality-jasa.md`, `data-fairness-repair.md`,
`trimmed-mmd.md`; current text after the 2026-10-13/14/15 corrections):
* JASA `lem:projection` (`robust-equality-outcomes-under-distribution-shift/jasa/supp_proofs.tex:142-153`, proof
  `:155-161`), with `W^ν_ε`, `𝓑^𝒩(r)` (`jasa/main.tex:225-241`) and `thm:certificate` (`main.tex:356-362`).
* JASA `prop:paired` (`supp_proofs.tex:608-619`, proof `:621-626`), with `lem:tax` (`main.tex:243-253`) and
  `thm:coverage-general` (`supp_proofs.tex:524-531`).
* JASA `thm:classcoverage` (`supp_proofs.tex:663-671`, proof `:673-678`), with `H_J` (`:628-632`), `prop:tax`(c)
  (`:633-643`), `prop:uniform` (`main.tex:454-458`) and `eq:T`, `F̄^𝒩` (`main.tex:349-362`).
* SB `prop:randpenalty` (`data-fairness-repair/schrodinger_bridge_fairness_repair.tex:587-604`, proof
  `:2739-2751`), with `prop:mixture`/`eq:mixture` (`:456-470`).
* SB `prop:noisefree` (`schrodinger_bridge_fairness_repair.tex:1560-1573`, proof `:3101-3119`), with
  `thm:gaussian`/`eq:gaussmarg` (`:2474-2490`).
* SB `prop:excess` (`schrodinger_bridge_fairness_repair.tex:2337-2353`, proof `:2753-2761`), with `thm:flow`
  (`:538-568`).
* TM `lem:continuity` (`trimmed-mmd/paper.tex:885-893`, proof `supplement.tex:268-283`).
* TM `cor:consistency` (`trimmed-mmd/paper.tex:988-999`), with `eq:alphaest` (`:902-909`), `thm:consistency`
  (`:966-980`) and `ass:regularity` (`:547-560`).
Imports the frozen `Wave11a` (`worstPair`; through it `RobustEquality/Tax` `Wdisc`, `tax`, `ballN`, `Wave4b`
`RefClass`, `InBall`, `Fbar`, `Findep`, `TrimmedMMD/Unconditional` `Dpop`, `Demp`, `ZeroSet` `Characteristic` and
`TrimmedMMD` `tau`, `alphaHat`), `Wave9b` (`stoPlan`, `qcost`, `flowMap`), `RobustEquality/CoverageRandom`
(`rhoHat`) and `SBFairness` (`kappa`, `v`, `geo`) statements, not copied; Mathlib and Tau Ceti otherwise. No
`Foundations` file is imported directly (the frozen `ZeroSet` statements import `Foundations/Distances/TV`).

Covered:
* `lem:projection`: `projection_disc` (`W^{ν^X}_ε(P̂^X,Q^X) ≤ W^ν_{ε,𝒵}(P̂,Q)`); `projection_ball` (`Q ∈ 𝓑^{𝒩_𝒵}_𝒵(r) ⇒
  Q^X ∈ 𝓑^{(π_X)_#𝒩_𝒵}(r)`); `projection_worst` (worst case over data-space sets `≤` worst case over the projected
  sets, any measurable covariate rule); `projection_certificate` ("hence at most the certificate of
  `thm:certificate` with the class `(π_X)_#𝒩_𝒵`").
* `prop:paired`: `paired_tax_zero` (`τ_𝒩(P) = 0`, attained); `paired_radius`, `paired_radius_prob` (every bound /
  upper confidence bound for `OT_ε(P̂,P)` is a valid radius for `𝓑^𝒩`); `paired_coverage` (in particular the
  random-fold radius of `thm:coverage-general`); `paired_gauss_tax` (Gaussian error `X = X° + b'ξ`, `b' ≥ b`:
  `τ_{𝒩'_b}(P) ≤ log(1/p_K)`, with an explicit member); `paired_gauss_radius` (UCB `+ ε log(1/p_K)` is valid for
  `𝓑^{𝒩'_b}`).
* `thm:classcoverage`: `classcoverage` (one measurable event of probability `≥ 1 − Σ_s(a_s + a'_s)`, all rules and
  multipliers at once).
* `prop:randpenalty`: `randpenalty_decomp` (the risk identity and non-negativity of the penalty);
  `randpenalty_bridge_var` (`Var(Ũ_t | X₀ = u) = t² Var(X₁ | X₀ = u) + εt(1−t)`, and the conditional mean);
  `randpenalty_pos` (penalty `≥ εt(1−t) > 0` for `t ∈ (0,1)`, `ε > 0`); `randpenalty_pos_one` (`> 0` at `t = 1`
  when no conditional law of `X₁` is a Dirac mass); `randpenalty_zero` (`= 0` at `t = 0`: why `(0,1]`).
* `prop:noisefree`: `noisefree_bridge_exact`, `noisefree_additive_exact` (the two exact `W₂` formulas of the
  proof); `noisefree_bridge_theta` (`Θ(σ⁴)`), `noisefree_additive_theta` (`Θ(σ²)`); `noisefree_limits` (the
  limiting constants `1/(8σ_sτ g t(1−t))`, `1/(2g)`, and ratio `→ 0`); `noisefree_constants` (`25/104 ≈ 0.2404`,
  `5/13 ≈ 0.3846` at `t = 1/2`, `σ_s = 1`, `τ = 1.6`).
* `prop:excess`: `excess_minkowski` (both one-sided bounds and the squared consequence); `excess_flow_cost`
  (`C^flow = Σ_s p_s W₂²(R_s, μ_{s,t})`); `excess_sto_cost` (`E(X_t − X_0)² = t² E_π(X₁ − X₀)² + εt(1−t)`);
  `excess_flow_le_sto` (`C^flow ≤ C^sto`).
* `lem:continuity`: `continuity_lip` (`4κ/η²`), `continuity_lip_sharp` (`4κ/η`, the review note),
  `continuity_cont` (continuity on `[0,1)`).
* `cor:consistency`: `cor_consistency` (`α̂ → TV(P,Q)` in probability along any admissible schedule).

Not covered (declared):
* `lem:projection`: unbounded data-space costs `c_𝒵` (the `Y`-part of `c_𝒵` is taken bounded: `Setting`, see
  Encodings); `𝒴` Polish is not used.
* `prop:paired`: the density-bound and rounding-box examples (the latter is `prop:tax`, not part of this
  proposition); the negative remark "the population on `K` … is not itself a member of a class of restricted
  Gaussian mixtures".
* `thm:classcoverage`: the step "under `H_J` the jittered held-out points are i.i.d. `P_s` given the fold, so
  `thm:coverage-general` applies" and `prop:tax`(c) itself enter as the event hypotheses `A_s`, `T_s` (the radius
  `r̂^OT_s` may be any statistic with a measurable coverage event; `thm:coverage-general` is certified for i.i.d.
  samples, `coverage_random_folds`); weak compactness of the classes is replaced by the attainment hypothesis it
  is used for.
* `prop:randpenalty`: that kernel repair has the conditional-independence structure (definitional:
  `Ũ ∼ K(U,S)`); that entropic plans of a non-Dirac target have non-Dirac conditional laws (`lem:sharp`, certified
  separately in `Wave8a`; here a hypothesis of `randpenalty_pos_one`); the remark after the proof.
* `prop:noisefree`: **conditional on `eq:gaussmarg`** — `μ^ε_{s,t}` is the closed form `N((1−t)a_s + ta⋆, v_s(t))`
  (`muSB`), not derived from the Schrödinger bridge (only `thm:gaussian`(b),(c) are certified); the numerical
  sweep over `ε ∈ [0.025, 0.4]` (only the limiting constants are stated); the remark after the proposition.
* `prop:excess`: "for the two realisations" identifies `C^sto` per group with `qcost (stoPlan ε t π_s)` (the
  certified `Wave9b.pareto` shows `stoPlan` is the stochastic realisation); the sentence after the proof.
* `cor:consistency`: the remark "the rate condition cannot be dropped" (`τ_{n,m}` bounded away from `0` for
  `δ = e^{−min(n,m)}`; not part of the corollary).

Encodings (to be checked by the critic):
* `lem:projection`: data-space centre `P̂ = Σ_i a_i δ_{z_i}` as labelled atoms (`muDisc a` on `Fin k`, frozen
  `Wdisc`), its covariate marginal the same weights at `π(z_i)`; the costs are rows `c_𝒵(z_i, ·)` and
  `c(π(z_i), ·)`; `π : 𝒵 → X` any measurable map (`π_X = Prod.fst` on `K × 𝒴`: generalisation) and the domination
  `c_𝒵 ≥ ‖x − x'‖²` is `c(π z_i, π z) ≤ c_𝒵(z_i, z)` (any cost on `X`: generalisation); both costs satisfy the
  frozen `Setting` (bounded measurable rows, `ε > 0`, `a_i > 0`, `Σ a_i = 1`), so the Bochner costs are genuine
  (`sInf` in `EReal`, `⊤` for empty sets); references are finite measures, `KL` is the paper's `klRef`
  (sub-probability convention); `(π_X)_#𝒩_𝒵 = pushClass` (`Measure.map` of a measurable map: genuine); the
  disparity of a covariate rule over a data-space law is `W₂²((h∘π)_#Q₀, (h∘π)_#Q₁)` (`worstData`), the projected
  worst case the frozen `worstPair`; the certificate is the frozen `Fbar` (`Δ(h) + √T₀ + √T₁)²`, `√T^𝒩 = sup_ν √T^ν`)
  at uniform centres `π ∘ z_s` with `c ≥ 0` bounded jointly measurable, `h` bounded measurable, `RefClass` classes.
* `prop:paired`: `H` is `P ∈ 𝒩_H ⊆ 𝒩` with `RefClass 𝒩` (`0 < ν(K) ≤ 1`, needed: `KL(P‖ν) < 0` is possible if
  `ν(K) > 1`); "valid radius" is membership `P ∈ ballN` (deterministically, or on a measurable event of the same
  probability); the coverage radius is the frozen `rhoHat` sum. Gaussian error on a finite-dimensional real inner
  product space `E` (Borel): `G_σ = isoN E σ = (stdGaussian E).map (σ • ·)` (identical to the frozen
  `Wave17a.isoGauss`, not imported to keep the import light), the law of `X = X° + b'ξ` is `m₀ ∗ G_{b'}` (`X° ∼ m₀`
  independent of `ξ`), the population on `K` is `(m₀ ∗ G_{b'})[|K]` (`cond`; `p_K > 0`, so genuine), `𝒩'_b =
  gaussMixClass` (mixing laws all probability measures on `E`), `K` any measurable set (compactness not used);
  references and laws live on `E` and are carried by `K`; the transport cost is any `Setting` cost on `E` (the
  paper's `‖x − x'‖²` restricted to `K`).
* `thm:classcoverage`: probability space `(Ω, μ)`; centres `x_s(ω)` uniform on `n_s ≥ 1` labelled atoms; the four
  events `A_s` (transport bound `OT_ε(P̂_s,P_s) ≤ r̂^OT_s`, level `a_s`) and `T_s` (`τ_𝒩(P_s) ≤ τ̂_s`, level
  `a'_s`) measurable, inner-measure form; radii `r̂_s = r̂^OT_s + ε τ̂_s`; conclusion with the frozen `Fbar`.
* `prop:randpenalty`: `ρ` is the law of `((U,S), Y)` on `α × ℝ`, `K : Kernel α ℝ` Markov the law of `Ũ` given
  `(U,S)`; the joint law is `ρ ⊗ₘ (K ∘ fst)` — `Ũ` given `(U,S,Y)` depends on `(U,S)` only, i.e. conditional
  independence; `m̄ = meanK ∘ K`, `Var(Ũ | U,S) = varK ∘ K` (Bochner, genuine under the `L²` hypotheses
  `E Y² < ∞`, `E Ũ² < ∞`); `R(h̃^sto) = E(Ũ − Y)²`. Bridge: `bridgeLaw ε t u μ = (μ.map ((1−t)u + t·)) ∗ N(0,εt(1−t))`
  for any conditional law `μ` of `X₁` given `X₀ = u` with finite second moment (generalisation from the entropic
  plan); `w = (u,s) ∈ ℝ × G`, `π w` that conditional law in group `s`.
* `prop:noisefree`: `μ^ε_{s,t} = muSB ε σ_s τ a_s a⋆ t` (`eq:gaussmarg` with the frozen `SBFairness.v`, `kappa`),
  `μ^0_{s,t} = muSB 0 …` (`ε = 0` in `eq:gaussmarg`, the `W₂` geodesic), `σ² = εt(1−t)`, `N(0,σ²) = gaussianReal 0
  σ²`; `σ_s, τ > 0`, `t ∈ (0,1)` fixed; `W₂` is Tau Ceti's `wassersteinEDist 2` (`ℝ≥0∞`); `Θ(f)` is two-sided
  `c₁ f ≤ W₂ ≤ c₂ f` eventually as `ε ↓ 0` (`𝓝[>] 0`); limits use `.toReal` of `W₂`, which is finite (it equals
  `ofReal` of the exact formula).
* `prop:excess`: all costs and risks are `∫⁻ edist(·,·)^2` in `[0,∞]` (no finiteness needed, no junk); `p_s =
  P(S = s)`, `R_s = (P[·|S = s]).map U` (as in frozen `Wave11b.condLaw`), atomless (`NullSingletonClass`; implied by
  `C_ε(R_s,ν) < ∞` in `def:repair`); the flow repair is `ω ↦ flowMap R_{S ω} μ_{S ω} (U ω)` with `μ_s` any
  probability law (generalisation of `μ^ε_{s,t}`); the stochastic realisation is the frozen `stoPlan ε t π_s`, `π_s`
  any coupling (generalisation of `π*_ε(R_s,ν)`), `μ_{s,t}` its second marginal.
* `lem:continuity`: frozen `Dpop` (`setDist` of the frozen regions); `φ` strongly measurable with `‖φ‖ ≤ κ` into a
  complete real inner product space (separability and characteristicness not needed); `α, α' ∈ [0, 1−η]`,
  `η ∈ (0,1)`.
* `cor:consistency`: the schedule is any filter `l` on an index type `ι` with sample sizes `n, m : ι → ℕ` (`≥ 1`)
  and levels `δ : ι → ℝ` (`> 0`) — `ι = ℕ × ℕ`, `l = atTop ×ˢ atTop` is the paper's double limit; `min(n,m)` is cast
  from `ℕ` (`≥ 1`, no division by `0`); `α* = TV(P,Q)` (frozen `tvDist`), `< 1`; `ass:regularity` is `φ` strongly
  measurable, `‖φ‖ ≤ κ`, `κ > 0`, `ℋ` complete separable, `Characteristic φ`; convergence in probability is: for
  every `e > 0` there are measurable `E_i ⊆ {|α̂_i − α*| ≤ e}` with `P^{n_i} ⊗ Q^{m_i}(E_i) → 1` (inner form,
  stronger than the outer-measure reading).

Critic notes:
* All 30 claims are proved in `Wave18b/Route{Projection,Paired,ClassCoverage,RandPenalty,NoiseFree,Excess,
  Continuity,Consistency}.lean` (axioms: propext, Classical.choice, Quot.sound). Routes reuse the certified
  `Tax.tax_identity`, `Wave11a.kernel_iff`, `Wave4b.certificate_independent`, `CoverageRandom.coverage_random_folds`,
  `Wave11b.flow_cost`, `Wave9b.pareto_weak`, `Unconditional.events`, `ZeroSet.zeroeq`/`zero_of_tv_le`, and the
  untrusted libraries `Foundations/Tax/Tax` (`klRef_eq_klDiv`), `Foundations/Strong/Single` (`klRef_tilted`) — routes
  only.
* Nothing was certified before for these eight labels (the certified SB `lem:excess`, `thm:flow`, `prop:pareto` and
  TM `thm:consistency` are different results, used here); no statement was found false.
* `prop:randpenalty` (repaired 2026-10-13: "`t ∈ (0,1]`"): correct as repaired; at `t = 1` positivity needs the
  conditional laws of `X₁` not to be Dirac masses, which the proof derives from `ν` non-Dirac (`lem:sharp`); at
  `t = 0` the penalty is `0` (`randpenalty_zero`).
* `lem:continuity`: the constant `4κ/η` suffices (review note confirmed): `g = (1−θ)g' + θ` is within
  `E|g' − g| ≤ 2(α'−α)/(1−α)` of any `g' ∈ 𝒢_{α'}`; `4κ/η²` follows.
* `prop:noisefree`: the paper's "`W₂^add/σ²` settles at `0.384`" is the finite-`ε` value; the limit is
  `5/13 = 0.3846…` (`0.2404` is the bridge limit `25/104` to four places). Paper S4 (DEFECTS #62): the ratios do not "settle" over
  `ε ∈ [0.025, 0.4]` — they range over `0.2392–0.2404` and `0.3791–0.3843`; `0.384` is the `ε = 0.025` value truncated,
  the limit `5/13` rounds to `0.385`.
* `prop:paired`: `τ_𝒩(P) = 0` needs `ν(K) ≤ 1` for every `ν ∈ 𝒩` (the paper's convention for references).
* `lem:projection`: the data-processing step uses the paper's `KL` (`klRef`), which differs from Mathlib's `klDiv`
  by `ν(𝒵) − 1`; `π_#` preserves the mass, so the sub-probability convention is harmless (QUEUE note).
* Critic (2026-10-15): ACCEPT / ACCEPT-WITH-NOTE, all 30 TRUE. projection: bounded costs lose nothing (truncate
  `c_𝒵` to `min(c_𝒵, B)`; `W` is monotone in the cost). paired: `ν(K) ≤ 1` is the paper's convention (`def:family`,
  main.tex:233-235); `paired_gauss_radius` is deterministic (the probability form follows by event inclusion).
  classcoverage keeps the union-bound content; the `H_J` jitter step and `prop:tax`(c) enter as event hypotheses.
  randpenalty at `t = 1`: "no conditional law is Dirac" is stronger than needed (`E Var > 0` suffices) but holds for
  entropic plans. noisefree is CONDITIONAL on `eq:gaussmarg` (proved in the paper, supplement.tex:2907-2916; not certified).
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TauCeti
open scoped ENNReal NNReal

namespace StatFormal.Wave18b

open StatFormal.RobustEquality StatFormal.RobustEquality.Tax StatFormal.RobustEquality.SemidualStrong
  StatFormal.RobustEquality.Certificate StatFormal.Wave4b

/-! ### robust equality `lem:projection` -/

section Projection

variable {Z X : Type} [MeasurableSpace Z] [MeasurableSpace X]

/-- The projected class `(π_X)_# 𝒩_𝒵 = {π_# ν : ν ∈ 𝒩_𝒵}`. -/
def pushClass (π : Z → X) (𝒩 : Set (Measure Z)) : Set (Measure X) := (fun ν => ν.map π) '' 𝒩

/-- The worst-case disparity over the data-space sets `𝓑^{𝒩_s}_𝒵(r_s)` of a rule `h` of the covariates,
`sup W₂²((h∘π)#Q₀, (h∘π)#Q₁)`. -/
def worstData {k₀ k₁ : ℕ} (π : Z → X) (𝒩₀ 𝒩₁ : Set (Measure Z)) (ε : ℝ) (a₀ : Fin k₀ → ℝ)
    (c₀ : Fin k₀ → Z → ℝ) (r₀ : EReal) (a₁ : Fin k₁ → ℝ) (c₁ : Fin k₁ → Z → ℝ) (r₁ : EReal) (h : X → ℝ) :
    ℝ≥0∞ :=
  ⨆ (Q₀ : Measure Z) (_ : Q₀ ∈ ballN 𝒩₀ ε a₀ c₀ r₀) (Q₁ : Measure Z) (_ : Q₁ ∈ ballN 𝒩₁ ε a₁ c₁ r₁),
    wassersteinEDist 2 (Q₀.map (h ∘ π)) (Q₁.map (h ∘ π)) ^ 2

end Projection

/-! ### robust equality `prop:paired` (Gaussian measurement error) -/

section Paired

variable (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]

/-- `N(0, σ² I)` on a finite-dimensional real inner product space (`σ • Z`, `Z` standard Gaussian). -/
def isoN (σ : ℝ) : Measure E := (stdGaussian E).map fun x => σ • x

/-- The class `𝒩'_b = {(G_b ∗ m)|_K : m ∈ 𝒫(ℝ^d)}` of bandwidth-`b` mixtures restricted to `K`. -/
def gaussMixClass (b : ℝ) (K : Set E) : Set (Measure E) :=
  {ν | ∃ m : Measure E, IsProbabilityMeasure m ∧ ν = (isoN E b ∗ m).restrict K}

end Paired

/-! ### SB `prop:randpenalty`, `prop:noisefree` -/

section SB

/-- The mean `∫ u dμ` of a law on `ℝ`. -/
def meanK (μ : Measure ℝ) : ℝ := ∫ u, u ∂μ

/-- The variance `∫ (u − ∫ u dμ)² dμ` of a law on `ℝ` (genuine for finite second moment). -/
def varK (μ : Measure ℝ) : ℝ := ∫ u, (u - meanK μ) ^ 2 ∂μ

/-- The bridge kernel at `X₀ = u` (`eq:mixture`): the law of `(1−t)u + tX₁ + √(εt(1−t)) Z` with `X₁ ∼ μ`
(the conditional law of `X₁` given `X₀ = u`) and `Z ∼ N(0,1)` independent. -/
def bridgeLaw (ε t u : ℝ) (μ : Measure ℝ) : Measure ℝ :=
  (μ.map fun x => (1 - t) * u + t * x) ∗ gaussianReal 0 (ε * t * (1 - t)).toNNReal

/-- The Gaussian repaired marginal of `eq:gaussmarg`, `μ^ε_{s,t} = N((1−t)a_s + ta⋆, v_s(t))`. -/
def muSB (ε σ τ a astar t : ℝ) : Measure ℝ :=
  gaussianReal ((1 - t) * a + t * astar) (StatFormal.SBFairness.v ε σ τ t).toNNReal

end SB

namespace Claims

open StatFormal.Wave9b StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Unconditional
  StatFormal.TrimmedMMD.ZeroSet StatFormal.TrimmedMMD.Concentration

/-! #### robust equality `lem:projection` -/

/-- `W^{ν^X}_ε(P̂^X, Q^X) ≤ W^ν_{ε,𝒵}(P̂, Q)` for a measurable projection `π` and a dominating cost. -/
def projection_disc : Prop :=
  ∀ (Z X : Type) [MeasurableSpace Z] [MeasurableSpace X] (k : ℕ) (ε : ℝ) (a : Fin k → ℝ)
    (cZ : Fin k → Z → ℝ) (cX : Fin k → X → ℝ) (π : Z → X) (ν Q : Measure Z) [IsFiniteMeasure ν]
    [IsProbabilityMeasure Q],
    Setting ε a cZ → Setting ε a cX → Measurable π → (∀ i z, cX i (π z) ≤ cZ i z) →
      Wdisc ε a cX (ν.map π) (Q.map π) ≤ Wdisc ε a cZ ν Q

/-- `Q ∈ 𝓑^{𝒩_𝒵}_𝒵(r) ⇒ Q^X ∈ 𝓑^{(π_X)_#𝒩_𝒵}(r)`. -/
def projection_ball : Prop :=
  ∀ (Z X : Type) [MeasurableSpace Z] [MeasurableSpace X] (k : ℕ) (ε : ℝ) (a : Fin k → ℝ)
    (cZ : Fin k → Z → ℝ) (cX : Fin k → X → ℝ) (π : Z → X) (𝒩 : Set (Measure Z)) (r : EReal)
    (Q : Measure Z),
    Setting ε a cZ → Setting ε a cX → Measurable π → (∀ i z, cX i (π z) ≤ cZ i z) →
    (∀ ν ∈ 𝒩, IsFiniteMeasure ν) →
      Q ∈ ballN 𝒩 ε a cZ r → Q.map π ∈ ballN (pushClass π 𝒩) ε a cX r

/-- The worst case over the data-space sets is at most the worst case over the projected covariate-space
sets, for every measurable rule of the covariates. -/
def projection_worst : Prop :=
  ∀ (Z X : Type) [MeasurableSpace Z] [MeasurableSpace X] (k₀ k₁ : ℕ) (ε : ℝ) (a₀ : Fin k₀ → ℝ)
    (cZ₀ : Fin k₀ → Z → ℝ) (cX₀ : Fin k₀ → X → ℝ) (a₁ : Fin k₁ → ℝ) (cZ₁ : Fin k₁ → Z → ℝ)
    (cX₁ : Fin k₁ → X → ℝ) (π : Z → X) (𝒩₀ 𝒩₁ : Set (Measure Z)) (r₀ r₁ : EReal) (h : X → ℝ),
    Setting ε a₀ cZ₀ → Setting ε a₀ cX₀ → Setting ε a₁ cZ₁ → Setting ε a₁ cX₁ → Measurable π →
    Measurable h → (∀ i z, cX₀ i (π z) ≤ cZ₀ i z) → (∀ i z, cX₁ i (π z) ≤ cZ₁ i z) →
    (∀ ν ∈ 𝒩₀, IsFiniteMeasure ν) → (∀ ν ∈ 𝒩₁, IsFiniteMeasure ν) →
      worstData π 𝒩₀ 𝒩₁ ε a₀ cZ₀ r₀ a₁ cZ₁ r₁ h ≤
        StatFormal.Wave11a.worstPair (pushClass π 𝒩₀) (pushClass π 𝒩₁) ε a₀ cX₀ r₀ a₁ cX₁ r₁ h

/-- "hence at most the certificate of `thm:certificate` with the class `(π_X)_#𝒩_𝒵`": uniform data-space
centres `z_s`, covariate centres `π ∘ z_s`. -/
def projection_certificate : Prop :=
  ∀ (Z X : Type) [MeasurableSpace Z] [MeasurableSpace X] (n₀ n₁ : ℕ) (z₀ : Fin n₀ → Z) (z₁ : Fin n₁ → Z)
    (cZ : Z → Z → ℝ) (c : X → X → ℝ) (π : Z → X) (ε r₀ r₁ lam₀ lam₁ : ℝ) (h : X → ℝ)
    (𝒩₀ 𝒩₁ : Set (Measure Z)),
    0 < n₀ → 0 < n₁ → 0 < ε → 0 < lam₀ → 0 < lam₁ →
    Measurable (Function.uncurry c) → (∀ a b, 0 ≤ c a b) → (∃ B, ∀ a b, c a b ≤ B) →
    (∀ z, Measurable (cZ z)) → (∃ B, ∀ a b, |cZ a b| ≤ B) → (∀ z z', c (π z) (π z') ≤ cZ z z') →
    Measurable π → Measurable h → (∃ H, ∀ x, |h x| ≤ H) → RefClass 𝒩₀ → RefClass 𝒩₁ →
      worstData π 𝒩₀ 𝒩₁ ε (fun _ => (1 : ℝ) / n₀) (fun i => cZ (z₀ i)) (r₀ : EReal)
          (fun _ => (1 : ℝ) / n₁) (fun i => cZ (z₁ i)) (r₁ : EReal) h ≤
        Fbar (π ∘ z₀) (π ∘ z₁) c ε r₀ r₁ (pushClass π 𝒩₀) (pushClass π 𝒩₁) h lam₀ lam₁

/-! #### robust equality `prop:paired` -/

/-- `P ∈ 𝒩_H ⊆ 𝒩` gives `τ_𝒩(P) = 0`, attained at `ν = P`. -/
def paired_tax_zero : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (𝒩H 𝒩 : Set (Measure K)) (P : Measure K) [IsProbabilityMeasure P],
    RefClass 𝒩 → P ∈ 𝒩H → 𝒩H ⊆ 𝒩 → tax 𝒩 P = 0 ∧ klRef P P = tax 𝒩 P

/-- Under `H`, `OT_ε(P̂,P) ≤ r` is membership `P ∈ 𝓑^𝒩(r)`. -/
def paired_radius : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k : ℕ) (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (𝒩H 𝒩 : Set (Measure K)) (P : Measure K) [IsProbabilityMeasure P] (r : EReal),
    Setting ε a c → RefClass 𝒩 → P ∈ 𝒩H → 𝒩H ⊆ 𝒩 → OTdisc ε a c P ≤ r → P ∈ ballN 𝒩 ε a c r

/-- Under `H`, every upper confidence bound for `OT_ε(P̂,P)` is a valid radius for `𝓑^𝒩`. -/
def paired_radius_prob : Prop :=
  ∀ (K Ω : Type) [MeasurableSpace K] [MeasurableSpace Ω] (μΩ : Measure Ω) (k : ℕ) (ε : ℝ)
    (a : Fin k → ℝ) (c : Ω → Fin k → K → ℝ) (𝒩H 𝒩 : Set (Measure K)) (P : Measure K)
    [IsProbabilityMeasure P] (r : Ω → EReal) (α : ℝ),
    (∀ ω, Setting ε a (c ω)) → RefClass 𝒩 → P ∈ 𝒩H → 𝒩H ⊆ 𝒩 →
    (∃ E, MeasurableSet E ∧ ENNReal.ofReal (1 - α) ≤ μΩ E ∧ E ⊆ {ω | OTdisc ε a (c ω) P ≤ r ω}) →
      ∃ E, MeasurableSet E ∧ ENNReal.ofReal (1 - α) ≤ μΩ E ∧ E ⊆ {ω | P ∈ ballN 𝒩 ε a (c ω) (r ω)}

/-- "in particular the radius of `thm:coverage-general`" (random folds, Hoeffding term) is valid for `𝓑^𝒩`. -/
def paired_coverage : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (P : Measure K) [IsProbabilityMeasure P] (N V : ℕ)
    (fold : Fin N → Fin V) (n : Fin V → ℕ) (e : ∀ v, Fin (n v) ≃ {i // fold i = v})
    (c : K → K → ℝ) (B Bc ε a : ℝ) (𝒩H 𝒩 : Set (Measure K)),
    Function.Surjective fold → (∀ v, ∃ i, ¬ fold i = v) → Measurable (Function.uncurry c) →
    (∀ x y, |c x y| ≤ B) → 0 < ε → 0 < Bc → (∀ x y y', c x y - c x y' ≤ Bc) → 0 < a → a < 1 → 0 < N →
    RefClass 𝒩 → P ∈ 𝒩H → 𝒩H ⊆ 𝒩 →
      ∃ E : Set (Fin N → K), MeasurableSet E ∧ ENNReal.ofReal (1 - a) ≤ Measure.pi (fun _ : Fin N => P) E ∧
        E ⊆ {X | P ∈ ballN 𝒩 ε (fun _ : Fin N => (1 : ℝ) / N) (fun i => c (X i))
          ((∑ v, ((n v : ℝ) / N) * CoverageRandom.rhoHat ε c e Bc a v X : ℝ) : EReal)}

/-- Gaussian measurement error `X = X° + b'ξ`, `b' ≥ b`: the population on `K` (the law of `X` given
`X ∈ K`) has `KL(P ‖ ν) ≤ log(1/p_K)` for a member `ν` of `𝒩'_b`, so `τ_{𝒩'_b}(P) ≤ log(1/p_K)`. -/
def paired_gauss_tax : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (K : Set E) (m0 : Measure E) [IsProbabilityMeasure m0] (b b' pK : ℝ),
    MeasurableSet K → 0 ≤ b → b ≤ b' → 0 < pK → ENNReal.ofReal pK ≤ (m0 ∗ isoN E b') K →
      (∃ ν ∈ gaussMixClass E b K, klRef ((m0 ∗ isoN E b')[|K]) ν ≤ ((Real.log (1 / pK) : ℝ) : EReal)) ∧
        tax (gaussMixClass E b K) ((m0 ∗ isoN E b')[|K]) ≤ ((Real.log (1 / pK) : ℝ) : EReal)

/-- Under the measurement-error hypothesis, an upper bound `r` for `OT_ε(P̂,P)` gives `P ∈ 𝓑^{𝒩'_b}(r + ε log(1/p_K))`. -/
def paired_gauss_radius : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (K : Set E) (m0 : Measure E) [IsProbabilityMeasure m0] (b b' pK : ℝ) (k : ℕ) (ε : ℝ)
    (a : Fin k → ℝ) (c : Fin k → E → ℝ) (r : ℝ),
    MeasurableSet K → 0 ≤ b → b ≤ b' → 0 < pK → ENNReal.ofReal pK ≤ (m0 ∗ isoN E b') K → Setting ε a c →
    OTdisc ε a c ((m0 ∗ isoN E b')[|K]) ≤ (r : EReal) →
      (m0 ∗ isoN E b')[|K] ∈ ballN (gaussMixClass E b K) ε a c ((r + ε * Real.log (1 / pK) : ℝ) : EReal)

/-! #### robust equality `thm:classcoverage` -/

/-- On the intersection of the transport events (`thm:coverage-general` applied to the jittered held-out
points) and the tax events (`prop:tax`(c), or `τ̂ = dϰ(β)` with `T_s = Ω` for the resolution class), with
probability `≥ 1 − Σ_s(a_s + a'_s)`, simultaneously for all rules and multipliers,
`W₂²(h#P₀, h#P₁) ≤ F̄^𝒩(h;λ)` at radii `r̂_s = r̂^OT_s + ε τ̂_s`. -/
def classcoverage : Prop :=
  ∀ (K Ω : Type) [MeasurableSpace K] [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n₀ n₁ : ℕ) (x₀ : Ω → Fin n₀ → K) (x₁ : Ω → Fin n₁ → K) (c : K → K → ℝ) (ε : ℝ)
    (𝒩₀ 𝒩₁ : Set (Measure K)) (P₀ P₁ : Measure K) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    (rOT₀ rOT₁ τ₀ τ₁ : Ω → ℝ) (a₀ a₁ a₀' a₁' : ℝ) (A₀ A₁ T₀ T₁ : Set Ω),
    0 < n₀ → 0 < n₁ → 0 < ε →
    Measurable (Function.uncurry c) → (∀ a b, 0 ≤ c a b) → (∃ B, ∀ a b, c a b ≤ B) →
    RefClass 𝒩₀ → RefClass 𝒩₁ →
    (∃ ν ∈ 𝒩₀, klRef P₀ ν = tax 𝒩₀ P₀) → (∃ ν ∈ 𝒩₁, klRef P₁ ν = tax 𝒩₁ P₁) →
    MeasurableSet A₀ → MeasurableSet A₁ → MeasurableSet T₀ → MeasurableSet T₁ →
    ENNReal.ofReal (1 - a₀) ≤ μ A₀ → ENNReal.ofReal (1 - a₁) ≤ μ A₁ →
    ENNReal.ofReal (1 - a₀') ≤ μ T₀ → ENNReal.ofReal (1 - a₁') ≤ μ T₁ →
    (∀ ω ∈ A₀, OTdisc ε (fun _ => (1 : ℝ) / n₀) (fun i => c (x₀ ω i)) P₀ ≤ (rOT₀ ω : EReal)) →
    (∀ ω ∈ A₁, OTdisc ε (fun _ => (1 : ℝ) / n₁) (fun i => c (x₁ ω i)) P₁ ≤ (rOT₁ ω : EReal)) →
    (∀ ω ∈ T₀, tax 𝒩₀ P₀ ≤ (τ₀ ω : EReal)) → (∀ ω ∈ T₁, tax 𝒩₁ P₁ ≤ (τ₁ ω : EReal)) →
      ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - (a₀ + a₀' + a₁ + a₁')) ≤ μ E ∧
        E ⊆ {ω | ∀ (h : K → ℝ) (lam₀ lam₁ : ℝ), Measurable h → (∃ H, ∀ z, |h z| ≤ H) → 0 < lam₀ → 0 < lam₁ →
          wassersteinEDist 2 (P₀.map h) (P₁.map h) ^ 2 ≤
            Fbar (x₀ ω) (x₁ ω) c ε (rOT₀ ω + ε * τ₀ ω) (rOT₁ ω + ε * τ₁ ω) 𝒩₀ 𝒩₁ h lam₀ lam₁}

/-! #### SB `prop:randpenalty` -/

/-- `E[(Ũ − Y)²] = E[(m̄(U,S) − Y)²] + E[Var(Ũ | U,S)]` when `Ũ` given `(U,S,Y)` has law `K(U,S)` (conditional
independence of `Ũ` and `Y` given `(U,S)`), and the penalty is non-negative. `ρ` is the law of `((U,S), Y)`. -/
def randpenalty_decomp : Prop :=
  ∀ (α : Type) [MeasurableSpace α] (ρ : Measure (α × ℝ)) [IsProbabilityMeasure ρ] (K : Kernel α ℝ)
    [IsMarkovKernel K],
    Integrable (fun p : α × ℝ => p.2 ^ 2) ρ →
    Integrable (fun z : (α × ℝ) × ℝ => z.2 ^ 2) (ρ ⊗ₘ K.comap Prod.fst measurable_fst) →
      ∫ z, (z.2 - z.1.2) ^ 2 ∂(ρ ⊗ₘ K.comap Prod.fst measurable_fst) =
          ∫ p, (meanK (K p.1) - p.2) ^ 2 ∂ρ + ∫ p, varK (K p.1) ∂ρ ∧
        0 ≤ ∫ p, varK (K p.1) ∂ρ

/-- Under the bridge: `E[Ũ_t | X₀ = u] = (1−t)u + tE[X₁ | X₀ = u]` and
`Var(Ũ_t | X₀ = u) = t² Var(X₁ | X₀ = u) + εt(1−t)`. -/
def randpenalty_bridge_var : Prop :=
  ∀ (ε t u : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ], 0 ≤ ε → t ∈ Icc (0 : ℝ) 1 →
    Integrable (fun x => x ^ 2) μ →
      meanK (bridgeLaw ε t u μ) = (1 - t) * u + t * meanK μ ∧
        varK (bridgeLaw ε t u μ) = t ^ 2 * varK μ + ε * t * (1 - t)

/-- "strictly positive for `t ∈ (0,1)` when `ε > 0`": the mean conditional variance of the bridge kernel is
`≥ εt(1−t) > 0`. `π w` is the conditional law of `X₁` given `(X₀, S) = w`. -/
def randpenalty_pos : Prop :=
  ∀ (G : Type) [MeasurableSpace G] (ρ : Measure ((ℝ × G) × ℝ)) [IsProbabilityMeasure ρ]
    (K : Kernel (ℝ × G) ℝ) [IsMarkovKernel K] (π : ℝ × G → Measure ℝ) (ε t : ℝ),
    0 < ε → t ∈ Ioo (0 : ℝ) 1 → (∀ w, IsProbabilityMeasure (π w)) → (∀ w, Integrable (fun x => x ^ 2) (π w)) →
    (∀ w, K w = bridgeLaw ε t w.1 (π w)) →
    Integrable (fun z : ((ℝ × G) × ℝ) × ℝ => z.2 ^ 2) (ρ ⊗ₘ K.comap Prod.fst measurable_fst) →
      ε * t * (1 - t) ≤ ∫ p, varK (K p.1) ∂ρ ∧ 0 < ∫ p, varK (K p.1) ∂ρ

/-- "strictly positive for `t = 1`": `E[Var(X₁ | X₀)] > 0` when no conditional law of `X₁` is a Dirac mass (as for
the entropic plan of a non-Dirac target, `lem:sharp`). -/
def randpenalty_pos_one : Prop :=
  ∀ (G : Type) [MeasurableSpace G] (ρ : Measure ((ℝ × G) × ℝ)) [IsProbabilityMeasure ρ]
    (K : Kernel (ℝ × G) ℝ) [IsMarkovKernel K] (π : ℝ × G → Measure ℝ) (ε : ℝ),
    0 ≤ ε → (∀ w, IsProbabilityMeasure (π w)) → (∀ w, Integrable (fun x => x ^ 2) (π w)) →
    (∀ w y, π w ≠ Measure.dirac y) → (∀ w, K w = bridgeLaw ε 1 w.1 (π w)) →
    Integrable (fun z : ((ℝ × G) × ℝ) × ℝ => z.2 ^ 2) (ρ ⊗ₘ K.comap Prod.fst measurable_fst) →
      0 < ∫ p, varK (K p.1) ∂ρ

/-- At `t = 0` the bridge kernel is `δ_u` and the penalty vanishes (why `t ∈ (0,1]` is needed). -/
def randpenalty_zero : Prop :=
  ∀ (ε u : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ],
    bridgeLaw ε 0 u μ = Measure.dirac u ∧ varK (bridgeLaw ε 0 u μ) = 0

/-! #### SB `prop:noisefree` -/

/-- Exact bridge distortion `W₂(μ^ε_{s,t}, μ^0_{s,t}) = t(1−t)(κ_{ε,s} − 2σ_sτ)/(√v_s(t) + √v^0_s(t))`, with
`κ_{ε,s} − 2σ_sτ = ε²/(κ_{ε,s} + 2σ_sτ)`. -/
def noisefree_bridge_exact : Prop :=
  ∀ ε σ τ a astar t : ℝ, 0 < ε → 0 < σ → 0 < τ → t ∈ Ioo (0 : ℝ) 1 →
    wassersteinEDist 2 (muSB ε σ τ a astar t) (muSB 0 σ τ a astar t) =
        ENNReal.ofReal (t * (1 - t) * (StatFormal.SBFairness.kappa ε σ τ - 2 * σ * τ) /
          (√(StatFormal.SBFairness.v ε σ τ t) + √(StatFormal.SBFairness.v 0 σ τ t))) ∧
      StatFormal.SBFairness.kappa ε σ τ - 2 * σ * τ = ε ^ 2 / (StatFormal.SBFairness.kappa ε σ τ + 2 * σ * τ)

/-- Exact additive distortion `W₂(μ^0_{s,t} ∗ N(0,σ²), μ^0_{s,t}) = √(v^0_s(t) + σ²) − √v^0_s(t)`,
`σ² = εt(1−t)`. -/
def noisefree_additive_exact : Prop :=
  ∀ ε σ τ a astar t : ℝ, 0 < ε → 0 < σ → 0 < τ → t ∈ Ioo (0 : ℝ) 1 →
    wassersteinEDist 2 (muSB 0 σ τ a astar t ∗ gaussianReal 0 (ε * t * (1 - t)).toNNReal)
        (muSB 0 σ τ a astar t) =
      ENNReal.ofReal (√(StatFormal.SBFairness.v 0 σ τ t + ε * t * (1 - t)) - √(StatFormal.SBFairness.v 0 σ τ t))

/-- `W₂(μ^ε_{s,t}, μ^0_{s,t}) = Θ(σ⁴)` as `ε ↓ 0`, `σ² = εt(1−t)`. -/
def noisefree_bridge_theta : Prop :=
  ∀ σ τ a astar t : ℝ, 0 < σ → 0 < τ → t ∈ Ioo (0 : ℝ) 1 →
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ ε in 𝓝[>] 0,
      ENNReal.ofReal (c₁ * (ε * t * (1 - t)) ^ 2) ≤ wassersteinEDist 2 (muSB ε σ τ a astar t) (muSB 0 σ τ a astar t) ∧
        wassersteinEDist 2 (muSB ε σ τ a astar t) (muSB 0 σ τ a astar t) ≤ ENNReal.ofReal (c₂ * (ε * t * (1 - t)) ^ 2)

/-- `W₂(μ^0_{s,t} ∗ N(0,σ²), μ^0_{s,t}) = Θ(σ²)` as `ε ↓ 0`, `σ² = εt(1−t)`. -/
def noisefree_additive_theta : Prop :=
  ∀ σ τ a astar t : ℝ, 0 < σ → 0 < τ → t ∈ Ioo (0 : ℝ) 1 →
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ ε in 𝓝[>] 0,
      ENNReal.ofReal (c₁ * (ε * t * (1 - t))) ≤
          wassersteinEDist 2 (muSB 0 σ τ a astar t ∗ gaussianReal 0 (ε * t * (1 - t)).toNNReal) (muSB 0 σ τ a astar t) ∧
        wassersteinEDist 2 (muSB 0 σ τ a astar t ∗ gaussianReal 0 (ε * t * (1 - t)).toNNReal) (muSB 0 σ τ a astar t) ≤
          ENNReal.ofReal (c₂ * (ε * t * (1 - t)))

/-- The limits behind the `Θ`'s and the ratio: `W₂^bridge/σ⁴ → 1/(8σ_sτ g t(1−t))`, `W₂^add/σ² → 1/(2g)`
(`g = (1−t)σ_s + tτ`), and `W₂^bridge/W₂^add → 0`. -/
def noisefree_limits : Prop :=
  ∀ σ τ a astar t : ℝ, 0 < σ → 0 < τ → t ∈ Ioo (0 : ℝ) 1 →
    Tendsto (fun ε => (wassersteinEDist 2 (muSB ε σ τ a astar t) (muSB 0 σ τ a astar t)).toReal /
        (ε * t * (1 - t)) ^ 2) (𝓝[>] 0)
      (𝓝 (1 / (8 * σ * τ * StatFormal.SBFairness.geo σ τ t * (t * (1 - t))))) ∧
    Tendsto (fun ε => (wassersteinEDist 2 (muSB 0 σ τ a astar t ∗ gaussianReal 0 (ε * t * (1 - t)).toNNReal)
        (muSB 0 σ τ a astar t)).toReal / (ε * t * (1 - t))) (𝓝[>] 0)
      (𝓝 (1 / (2 * StatFormal.SBFairness.geo σ τ t))) ∧
    Tendsto (fun ε => (wassersteinEDist 2 (muSB ε σ τ a astar t) (muSB 0 σ τ a astar t)).toReal /
        (wassersteinEDist 2 (muSB 0 σ τ a astar t ∗ gaussianReal 0 (ε * t * (1 - t)).toNNReal)
          (muSB 0 σ τ a astar t)).toReal) (𝓝[>] 0) (𝓝 0)

/-- The two limiting constants at `t = 1/2`, `σ_s = 1`, `τ = 1.6` (the paper's "0.2404" and "0.384"). -/
def noisefree_constants : Prop :=
  1 / (8 * 1 * (8 / 5) * StatFormal.SBFairness.geo 1 (8 / 5) (1 / 2) * ((1 / 2) * (1 - 1 / 2))) = (25 / 104 : ℝ) ∧
    1 / (2 * StatFormal.SBFairness.geo 1 (8 / 5) (1 / 2)) = (5 / 13 : ℝ)

/-! #### SB `prop:excess` -/

/-- Minkowski: `|R(h̃)^{1/2} − R(h)^{1/2}| ≤ C^{1/2}` and `R(h̃) ≤ (R(h)^{1/2} + C^{1/2})²`, for every realisation
`Ũ = h̃(X,S)`, with `U = h(X)`, in `[0,∞]`. -/
def excess_minkowski : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (U Ut Y : Ω → ℝ),
    AEMeasurable U P → AEMeasurable Ut P → AEMeasurable Y P →
      (∫⁻ ω, edist (Ut ω) (Y ω) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) ≤
          (∫⁻ ω, edist (U ω) (Y ω) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) + (∫⁻ ω, edist (Ut ω) (U ω) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) ∧
        (∫⁻ ω, edist (U ω) (Y ω) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) ≤
          (∫⁻ ω, edist (Ut ω) (Y ω) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) + (∫⁻ ω, edist (Ut ω) (U ω) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) ∧
        ∫⁻ ω, edist (Ut ω) (Y ω) ^ (2 : ℝ) ∂P ≤
          ((∫⁻ ω, edist (U ω) (Y ω) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) +
            (∫⁻ ω, edist (Ut ω) (U ω) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ)) ^ (2 : ℝ)

/-- `C^flow = Σ_s p_s W₂²(R_s, μ_{s,t})` for the flow repair `h̃(x,s) = Ψ_s(h(x))`, `Ψ_s = F⁻¹_{μ_s} ∘ F_{R_s}`,
`R_s = 𝓛(U | S = s)` atomless, `p_s = P(S = s)`. -/
def excess_flow_cost : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (S : Ω → Fin 2) (U : Ω → ℝ)
    (μ : Fin 2 → Measure ℝ),
    Measurable S → Measurable U → (∀ s, P (S ⁻¹' {s}) ≠ 0) → (∀ s, IsProbabilityMeasure (μ s)) →
    (∀ s, NullSingletonClass ((P[|S ⁻¹' {s}]).map U)) →
      ∫⁻ ω, edist (flowMap ((P[|S ⁻¹' {S ω}]).map U) (μ (S ω)) (U ω)) (U ω) ^ (2 : ℝ) ∂P =
        ∑ s, P (S ⁻¹' {s}) * wassersteinEDist 2 ((P[|S ⁻¹' {s}]).map U) (μ s) ^ (2 : ℝ)

/-- `E[(X_t − X_0)²] = t² E_π[(X₁ − X₀)²] + εt(1−t)` for the stochastic realisation under any endpoint plan `π`
(in `[0,∞]`; no moment assumption); summed against `p_s` this is `C^sto`. -/
def excess_sto_cost : Prop :=
  ∀ (ε t : ℝ) (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π], 0 ≤ ε → t ∈ Icc (0 : ℝ) 1 →
    qcost (stoPlan ε t π) = ENNReal.ofReal (t ^ 2) * qcost π + ENNReal.ofReal (ε * t * (1 - t))

/-- `C^flow ≤ C^sto` (`thm:flow`(iii)): `Σ_s p_s W₂²(R_s, μ_{s,t}) ≤ Σ_s p_s E[(X_t − X_0)² | S = s]`, `μ_{s,t}` the
law of the stochastic realisation. -/
def excess_flow_le_sto : Prop :=
  ∀ (ε t : ℝ) (p : Fin 2 → ℝ) (R : Fin 2 → Measure ℝ) (ν : Measure ℝ) (π : Fin 2 → Measure (ℝ × ℝ)),
    0 ≤ ε → t ∈ Icc (0 : ℝ) 1 → (∀ s, IsProbabilityMeasure (π s)) → (∀ s, IsCoupling (π s) (R s) ν) →
      ∑ s, ENNReal.ofReal (p s) * wassersteinEDist 2 (R s) (stoPlan ε t (π s)).snd ^ (2 : ℝ) ≤
        ∑ s, ENNReal.ofReal (p s) * qcost (stoPlan ε t (π s))

/-! #### TM `lem:continuity` -/

/-- `|D_α − D_{α'}| ≤ (4κ/η²)|α − α'|` on `[0, 1−η]`. -/
def continuity_lip : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ η α α' : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < η → η < 1 → α ∈ Icc 0 (1 - η) → α' ∈ Icc 0 (1 - η) →
      |Dpop φ P Q α - Dpop φ P Q α'| ≤ 4 * κ / η ^ 2 * |α - α'|

/-- The sharper constant of the review note: `|D_α − D_{α'}| ≤ (4κ/η)|α − α'|` on `[0, 1−η]`. -/
def continuity_lip_sharp : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ η α α' : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < η → η < 1 → α ∈ Icc 0 (1 - η) → α' ∈ Icc 0 (1 - η) →
      |Dpop φ P Q α - Dpop φ P Q α'| ≤ 4 * κ / η * |α - α'|

/-- "In particular `α ↦ D_{α,k}(P,Q)` is continuous on `[0,1)`." -/
def continuity_cont : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → ContinuousOn (Dpop φ P Q) (Ico 0 1)

/-! #### TM `cor:consistency` -/

/-- Along any filter on sample-size/level schedules with `δ → 0` and `log(1/δ)/min(n,m) → 0`,
`α̂_{n,m} → α* = TV(P,Q)` in probability (measurable inner events of probability `→ 1`). -/
def cor_consistency : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : 𝒳 → H) (κ : ℝ) (ι : Type) (l : Filter ι) (n m : ι → ℕ) (δ : ι → ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < κ → Characteristic φ →
    StatFormal.Distances.tvDist P Q < 1 →
    (∀ i, 1 ≤ n i) → (∀ i, 1 ≤ m i) → (∀ i, 0 < δ i) → Tendsto δ l (𝓝 0) →
    Tendsto (fun i => Real.log (1 / δ i) / (min (n i) (m i) : ℕ)) l (𝓝 0) →
      ∀ e : ℝ, 0 < e → ∃ E : ∀ i, Set ((Fin (n i) → 𝒳) × (Fin (m i) → 𝒳)), (∀ i, MeasurableSet (E i)) ∧
        (∀ i, E i ⊆ {z | |alphaHat (Demp φ z.1 z.2) (fun α => tau κ α (δ i) (n i) (m i)) -
          StatFormal.Distances.tvDist P Q| ≤ e}) ∧
        Tendsto (fun i => ((Measure.pi fun _ : Fin (n i) => P).prod (Measure.pi fun _ : Fin (m i) => Q)) (E i))
          l (𝓝 1)

end Claims
end StatFormal.Wave18b
