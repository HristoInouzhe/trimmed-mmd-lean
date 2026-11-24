import StatFormal.Archive.RobustEquality.Paper2.Seminorm.Statements
import StatFormal.Archive.Wave4b.Statements
import StatFormal.Archive.Wave8a.Statements
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
import TauCeti.MeasureTheory.OptimalTransport.Entropic.Basic
import TauCeti.Probability.Quantile
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# FROZEN STATEMENTS — wave 9b (QUEUE rows 83–86): robust equality paper 2 `thm:price`; SB fairness
# repair `thm:field`, `prop:pareto`; trimmed MMD `prop:sinkexist`

Sources (verbatim in `lean-formalisation/inventory/extracted/robust-equality-paper2.md`,
`data-fairness-repair.md`, `trimmed-mmd.md`; current text after the 2026-10-13/14 corrections):
* paper 2 `thm:price` (`robust-equality-outcomes-under-distribution-shift/paper2/main.tex:582-593`, proof
  `paper2/app_proofs.tex:217-223`), with `Δ(w) = W₂(w#P̂₀, w#P̂₁)` (`main.tex:218`, coupling form `lem:delta-inf`
  `:296-303`), `G = Δ + N₀ + N₁` (`thm:seminorm`(iii), `:337`), `N_s` seminorms (`thm:seminorm`(ii), `:336`),
  Wasserstein balls `N_s(w) = √r_s |w|` (`thm:seminorm`(iv)(a), `:339`) and `prop:structured` (`:361`, the
  Lipschitz step of the proof).
* SB `thm:field` (`data-fairness-repair/schrodinger_bridge_fairness_repair.tex:957-972`, proof `:974-995`), with
  `def:standardisable` (`:932-947`; (iii) now asks `Ŝ_ν⁻¹` to be `L`-Lipschitz on all of `ℝ^d` with probability
  tending to one — the DEFECTS #11 repair).
* SB `prop:pareto` (`schrodinger_bridge_fairness_repair.tex:568-583`, proof `:2711-2722`), with `thm:flow`
  (`:537-566`, `Ψ = F⁻¹_{μ_t} ∘ F_{R_s}`), `def:repair` (`:435-447`, `C_ε(R_s, ν) < ∞`), `eq:static` and
  `ass:ac` (`:385-402`: `Ent` is differential entropy, so `C_ε = +∞` as soon as a marginal has an atom) and
  `prop:mixture` (`:449-460`: `X_t = (1−t)X₀ + tX₁ + √(εt(1−t)) Z`).
* trimmed MMD `prop:sinkexist` (`trimmed-mmd/entropic.tex:157-166`, proof `:167-174`), with `eq:trimset`
  (`:60-66`), `eq:trimSink` (`:123-128`) and the standing setting (`:134-137`: `𝒳` compact, `c` continuous,
  `OT_ε(μ,ν) = min_π ∫c dπ + ε KL(π‖μ⊗ν)`).
Reuses the frozen `RobustEquality/Paper2/Seminorm` (`Deltafin`), `Wave4b` (`endpointMixture1`) and `Wave8a`
(`trimSet`) statements, and Tau Ceti's `wassersteinEDist`, `IsCoupling`, `HasFiniteMoment`,
`entropicTransportCost`, `Measure.quantile`, imported, not copied.

Covered:
* `thm:price`: `price_lipschitz` (the proof's step `|G(w) − G(w')| ≤ |v|_{Σ₀} + |v|_{Σ₁} + N₀(v) + N₁(v)`,
  `v = w − w'`), `price_attained` (`Π(δ)` is a genuine minimum in finite dimension, and so is the trust-region
  value of (iii)), `price_upper` ((i)), `price_lower` ((ii), any `L ≥ L_G`), `price_LG_wass` ((ii), the
  Wasserstein-ball bound on `L_G`), `price_trust` ((iii)).
* `thm:field`: `field_exact` (`(T_s)_#R_s = ν` exactly), `field_bound` (the deterministic two-line triangle
  inequality of the proof, global Lipschitz `Ŝ_ν⁻¹`), `field_rate` (the parity gap is `O_P(r_n)`).
* `prop:pareto`: `pareto_atomless` (why atomless `R_s` is the standing setting: a coupling with a Lebesgue
  density has an atomless first marginal), `pareto_flow` (`Ψ_#R = μ` and `∫(Ψ − id)² dR = W₂²(R, μ)`,
  `thm:flow`(i)–(ii)), `pareto_weak` (`W₂² ≤` cost of every coupling, `thm:flow`(iii)), `pareto_strict`
  (strict inequality when `K(u,·)` is non-degenerate on a set of positive measure), `pareto_bridge` (the
  stochastic bridge realisation: it is a coupling of `R` and `μ_t`, has finite cost, and is strictly worse for
  `ε > 0`, `t ∈ (0,1)`), `pareto` (the proposition for two groups: same marginals, hence every fairness
  functional agrees; the displayed equality and strict inequality).
* `prop:sinkexist`: `sink_ot_finite` (`OT_ε < ∞`, so its real value is no junk), `sink_trim_compact` (`R_α(P)`
  is weakly compact), `sink_attained` (under (C) the infimum of `eq:trimSink` is attained).

Not covered (declared):
* `thm:price`: the identity `𝓡(w) − 𝓡(b*) = |w − b*|²_Σ` ("so that", a standard least-squares fact): `Σ ≻ 0`
  and `b*` are arbitrary here, which only generalises; the remark after the theorem (one-dimensional search,
  looseness of (ii)).
* `thm:field`: "If `r_n = n^{-1/2}`, all three properties of Table `tab:trilemma` hold" (informal table); the
  part of `def:standardisable`(iii) about `S_ν⁻¹` on `supp γ` and the inverse/estimator errors for `ν`'s own
  forward map (not used by the current proof; dropping them only generalises).
* `prop:pareto`: "Combined with Proposition `prop:excess` … uniformly tighter excess-risk bound" (a pointer);
  the identification of the bridge kernel with `prop:mixture` (taken as the encoding, see below); the
  literal kernel non-degeneracy of the bridge (`pareto_bridge` proves the strict inequality it is used for).
* `prop:sinkexist`: convexity of `R_α(P)` (proof remark, not needed); the closing sentence of the proof.

Encodings (see card):
* `thm:price`: covariates in a real inner-product space `E` (finite-dimensional only for `price_attained`);
  centres `P̂_s = Σ_i a^s_i δ_{x^s_i}` with `a ≥ 0`, `Σ a = 1`; `Δ = Deltafin` (frozen; `= W₂(w#P̂₀, w#P̂₁)` by
  the certified `delta_inf_linear`); `N_s` any `Seminorm ℝ E` (the queue's "abstract seminorm"; `thm:seminorm`(ii)
  makes the paper's `N_s` one); `Σ ≻ 0` a continuous linear map with `⟪Σv, v⟫ > 0` for `v ≠ 0`,
  `|v|_Σ = √⟪Σv, v⟫` (`sigNorm`); `|v|_{Σ_s} = √(Σ_i a^s_i ⟪v, x^s_i − c⟫²)` for one common point `c`
  (`smNorm`); `Π(δ)` is any `IsLeast` value of `{|w − b*|²_Σ : G(w) ≤ √δ}`, `0 ≤ δ`; (i) assumes
  `G(b*) > 0` (the printed bound divides by it; for `G(b*) = 0` `Π = 0`); `L_G := sup_{v≠0} ratio(v)` enters as
  any `L > 0` with `ratio ≤ L` for every `v` (`L_G` is the least such `L`, so the bound with `L_G` is an instance);
  `λ_max(Σ^{-1/2} M Σ^{-1/2}) = sup_v vᵀMv / vᵀΣv` likewise enters as any `Λ` with `vᵀMv ≤ Λ vᵀΣv` for all `v`;
  (iii) assumes `c_s ≥ 0`, `c₀ + c₁ > 0` (with `c₀ = c₁ = 0` the printed ball `|w| ≤ √δ/0` is junk).
* `thm:field`: `ℝ^d = EuclideanSpace ℝ (Fin d)`; groups `s : Fin 2`; `def:standardisable`(i) for `μ` is
  `Standardises μ γ S Sinv` (measurable `S`, `Sinv`, `S_#μ = γ`, `Sinv ∘ S = id` `μ`-a.e., `S ∘ Sinv = id`
  `γ`-a.e.); `W₂` is Tau Ceti's `wassersteinEDist 2` and `L²` norms are `eLpNorm · 2` (both `ℝ≥0∞`, no
  moment hypotheses, no junk); the rate is `r_n ≥ 0`; the estimators are arbitrary maps indexed by `(n, ω)`, measurable in the space
  variable for each `(n, ω)` ("from `n` i.i.d. observations" is not used); `O_P(r_n)` is `BigOP`
  (measurable-event convention: for every `η > 0` there are `M`, `N` and, for `n ≥ N`, a measurable event of
  probability `≥ 1 − η` on which the quantity is `≤ M r_n`); "with probability tending to one" is
  `LipschitzWhp` (measurable events `A_n`, `P(A_n) → 1`, `Ŝ_ν⁻¹` `L`-Lipschitz on `ℝ^d` on `A_n`).
* `prop:pareto`: dimension one; `Ψ = flowMap R μ = μ.quantile ∘ cdf R` (Tau Ceti's generalised inverse
  `inf{x : t ≤ F(x)}`, Mathlib `cdf`); costs are `qcost σ = ∫⁻ |x − y|²` (`ℝ≥0∞`) and the displayed `L²`
  norms are compared through their squares (`√` is monotone); `‖h̃ − h‖²_{L²} = Σ_s p_s E[(h̃ − U)² | S = s]`
  is encoded as the `p_s`-weighted sum of the group costs. Atomless `R_s` (needed: with `R_s = δ₀` every
  coupling is optimal) is hypothesised; it is the standing setting because `def:repair` requires
  `C_ε(R_s, ν) < ∞`, which forces the optimal plan to have a Lebesgue density (`Ent = −∞` otherwise,
  `:400-402`), whence `pareto_atomless`. A stochastic realisation is a Markov kernel `K` with
  `(R ⊗ K).snd = μ`; "non-degenerate on a set of positive measure" is a measurable `A`, `R(A) > 0`, with
  `K(u,·)` not a Dirac mass for `u ∈ A`. The bridge (`prop:mixture`): for **any** coupling `π` of `R` and `ν`
  (a generalisation of the entropic plan), the joint law of `(X₀, X_t)` is `stoPlan ε t π`, the law of
  `(X₀, (1−t)X₀ + tX₁ + Z)`, `Z ~ N(0, εt(1−t))` independent, whose second marginal is the frozen
  `endpointMixture1 ε t π = μ^ε_{s,t}`; `R_s, ν ∈ 𝒫₂` (`ass:main`) are `HasFiniteMoment 2`.
* `prop:sinkexist`: `𝒳` a compact metric space with its Borel σ-algebra; `c : 𝒳 × 𝒳 → ℝ≥0` continuous (a real
  continuous cost is bounded below on compact `𝒳`, and `S_ε` is invariant under adding a constant to `c`);
  `OT_ε(μ,ν)` is the real value of Tau Ceti's `entropicTransportCost` (finite by `sink_ot_finite`);
  `S_ε = OT_ε(P,Q) − ½OT_ε(P,P) − ½OT_ε(Q,Q)`; the weak topology is Mathlib's on `ProbabilityMeasure 𝒳`, and
  (C) is continuity of `(μ,ν) ↦ OT_ε(μ,ν)` on `ProbabilityMeasure 𝒳 × ProbabilityMeasure 𝒳`; `R_α(P)` is the
  frozen `trimSet P α`; "attained" is `IsLeast` of the set of values at a point of `R_α(P) × R_α(Q)`.
Critic notes:
* `thm:price` holds as printed (all three parts, with the factor 3, under the junk guards above).
* `thm:field` holds in the current text (DEFECTS #11 repaired: global Lipschitz `Ŝ_ν⁻¹`); the hypothesis on
  `S_ν⁻¹` on `supp γ` is no longer used.
* `prop:pareto` holds in the standing setting. The queue note "false as written" (QUEUE row 85, `R_s = δ₀`)
  is stale: DEFECTS #10 resolved it as *not a defect of the statement*, since `def:repair` makes admissible
  `R_s` atomless; the proof (`:2717`) only lacks that one-line justification. No refutation is given (it would
  leave the standing setting).
* `prop:sinkexist` holds as printed: (C) is a hypothesis; compactness of `R_α(P)` is proved here
  (Prokhorov on compact `𝒳`, closedness by the portmanteau theorem on open sets plus outer regularity).
* Critic (2026-10-14): ACCEPT-WITH-NOTE. `thm:price`: the paper's `L_G`, `λ_max` are instances of "any bounding
  constant" (finite and positive in the paper's setting); `c_s ≥ 0` is necessary (`c₀ = −5`, `c₁ = 6` breaks it).
  `prop:pareto`: atomless `R_s` is entailed by `def:repair` (`C_ε < ∞`, `sb:2732`; `pareto_atomless`). The text's
  argument at `sb:400-401` ("`Ent(π) = −∞` for any atomic `π`") is loose: `δ₀ ⊗ N(0,1)` is atomless but singular; the
  conclusion holds with "`π` without a Lebesgue density" (S4, DEFECTS #42). `prop:sinkexist`: a real continuous cost
  on a compact space is bounded below and `S_ε` is invariant under `c ↦ c + κ`, so the ℝ≥0 cost covers the paper's case
  via `c − min c`; "compact metric" specialises "compact".
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti Set Filter
open scoped ENNReal NNReal InnerProductSpace Topology

namespace StatFormal.Wave9b

/-! ### paper 2 `thm:price` -/

section Price

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `|v|_Σ = √⟪Σv, v⟫`. -/
def sigNorm (Sg : E →L[ℝ] E) (v : E) : ℝ := √⟪Sg v, v⟫_ℝ

/-- `|v|_{Σ_s} = √(Σ_i a_i ⟪v, x_i − c⟫²)`: the second-moment seminorm of `Σ_i a_i δ_{x_i}` about `c`. -/
def smNorm {n : ℕ} (a : Fin n → ℝ) (x : Fin n → E) (c : E) (v : E) : ℝ :=
  √(∑ i, a i * ⟪v, x i - c⟫_ℝ ^ 2)

/-- `G(w) = Δ(w) + N₀(w) + N₁(w)`. -/
def Gfun {n₀ n₁ : ℕ} (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E)
    (N₀ N₁ : Seminorm ℝ E) (w : E) : ℝ :=
  StatFormal.RobustEquality.Paper2.Seminorm.Deltafin a₀ x₀ a₁ x₁ w + N₀ w + N₁ w

/-- The feasible values `{|w − b*|²_Σ : G(w) ≤ √δ}` whose minimum is `Π(δ)`. -/
def priceSet {n₀ n₁ : ℕ} (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E)
    (N₀ N₁ : Seminorm ℝ E) (Sg : E →L[ℝ] E) (b : E) (δ : ℝ) : Set ℝ :=
  {q | ∃ w, Gfun a₀ x₀ a₁ x₁ N₀ N₁ w ≤ √δ ∧ q = sigNorm Sg (w - b) ^ 2}

/-- The trust-region values `{|w − b*|²_Σ : |w| ≤ ρ}` of (iii). -/
def trustSet (Sg : E →L[ℝ] E) (b : E) (ρ : ℝ) : Set ℝ :=
  {q | ∃ w, ‖w‖ ≤ ρ ∧ q = sigNorm Sg (w - b) ^ 2}

/-- `Σ ≻ 0`. -/
def PosDefOp (Sg : E →L[ℝ] E) : Prop := ∀ v, v ≠ 0 → 0 < ⟪Sg v, v⟫_ℝ

/-- Finitely supported probability weights. -/
def ProbWeights {n : ℕ} (a : Fin n → ℝ) : Prop := (∀ i, 0 ≤ a i) ∧ ∑ i, a i = 1

end Price

/-! ### SB `thm:field` -/

section Field

/-- `def:standardisable`(i) for one law: `S_#μ = γ` and `S` is invertible a.e. with measurable inverse `Sinv`
(`Sinv ∘ S = id` `μ`-a.e., `S ∘ Sinv = id` `γ`-a.e.). -/
def Standardises {d : ℕ} (μ γ : Measure (EuclideanSpace ℝ (Fin d)))
    (S Sinv : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop :=
  Measurable S ∧ Measurable Sinv ∧ μ.map S = γ ∧ (∀ᵐ x ∂μ, Sinv (S x) = x) ∧ ∀ᵐ z ∂γ, S (Sinv z) = z

/-- `X_n = O_P(r_n)`, measurable-event form: for every `η > 0` there are `M` and `N` such that for every
`n ≥ N` some measurable event of probability `≥ 1 − η` carries `X_n ≤ M r_n`. -/
def BigOP {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (r : ℕ → ℝ) (X : ℕ → Ω → ℝ≥0∞) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ M : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∃ A : Set Ω, MeasurableSet A ∧
    ENNReal.ofReal (1 - η) ≤ P A ∧ ∀ ω ∈ A, X n ω ≤ ENNReal.ofReal (M * r n)

/-- `f_n` is `L`-Lipschitz on all of `ℝ^d` with probability tending to one (measurable events). -/
def LipschitzWhp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ} (L : ℝ≥0)
    (f : ℕ → Ω → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∃ A : ℕ → Set Ω, (∀ n, MeasurableSet (A n)) ∧ Tendsto (fun n => P (A n)) atTop (𝓝 1) ∧
    ∀ n, ∀ ω ∈ A n, LipschitzWith L (f n ω)

end Field

/-! ### SB `prop:pareto` -/

section Pareto

/-- `Ψ = F⁻¹_μ ∘ F_R` (`eq:flowmap`). -/
def flowMap (R μ : Measure ℝ) (u : ℝ) : ℝ := μ.quantile (cdf R u)

/-- Quadratic intervention cost `∫ |x − y|² dσ` of a plan (`ℝ≥0∞`). -/
def qcost (σ : Measure (ℝ × ℝ)) : ℝ≥0∞ := ∫⁻ z, edist z.1 z.2 ^ (2 : ℝ) ∂σ

/-- The stochastic (bridge-kernel) realisation, `prop:mixture`: the joint law of
`(X₀, X_t) = (X₀, (1−t)X₀ + tX₁ + Z)`, `(X₀, X₁) ~ π`, `Z ~ N(0, εt(1−t))` independent. -/
def stoPlan (ε t : ℝ) (π : Measure (ℝ × ℝ)) : Measure (ℝ × ℝ) :=
  (π.prod (gaussianReal 0 (ε * t * (1 - t)).toNNReal)).map
    fun q => (q.1.1, (1 - t) * q.1.1 + t * q.1.2 + q.2)

end Pareto

/-! ### trimmed MMD `prop:sinkexist` -/

section Sink

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- `OT_ε(μ,ν)`, the real value of `inf_π ∫ c dπ + ε KL(π ‖ μ ⊗ ν)`. -/
def OTe (c : 𝒳 × 𝒳 → ℝ≥0) (ε : ℝ≥0) (μ ν : Measure 𝒳) : ℝ :=
  (entropicTransportCost (fun z => (c z : ℝ≥0∞)) ε μ ν).toReal

/-- The Sinkhorn divergence `S_ε(P,Q) = OT_ε(P,Q) − ½OT_ε(P,P) − ½OT_ε(Q,Q)`. -/
def sinkDiv (c : 𝒳 × 𝒳 → ℝ≥0) (ε : ℝ≥0) (P Q : Measure 𝒳) : ℝ :=
  OTe c ε P Q - OTe c ε P P / 2 - OTe c ε Q Q / 2

/-- Hypothesis (C): `(μ,ν) ↦ OT_ε(μ,ν)` is jointly continuous for the weak topology. -/
def JointCont (c : 𝒳 × 𝒳 → ℝ≥0) (ε : ℝ≥0) [TopologicalSpace 𝒳] [OpensMeasurableSpace 𝒳] : Prop :=
  Continuous fun p : ProbabilityMeasure 𝒳 × ProbabilityMeasure 𝒳 =>
    OTe c ε (p.1 : Measure 𝒳) (p.2 : Measure 𝒳)

end Sink

namespace Claims

open StatFormal.Wave8a (trimSet)

/-! #### paper 2 `thm:price` -/

/-- The Lipschitz step of the proof of `thm:price`(ii) (`prop:structured`): for any common point `c`,
`|G(w) − G(w')| ≤ |v|_{Σ₀} + |v|_{Σ₁} + N₀(v) + N₁(v)`, `v = w − w'`. -/
def price_lipschitz : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n₀ n₁ : ℕ)
    (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (N₀ N₁ : Seminorm ℝ E)
    (c w w' : E),
    ProbWeights a₀ → ProbWeights a₁ →
      |Gfun a₀ x₀ a₁ x₁ N₀ N₁ w - Gfun a₀ x₀ a₁ x₁ N₀ N₁ w'| ≤
        smNorm a₀ x₀ c (w - w') + smNorm a₁ x₁ c (w - w') + N₀ (w - w') + N₁ (w - w')

/-- `Π(δ)` is a genuine minimum (finite dimension, `Σ ≻ 0`, `δ ≥ 0`), and so is the trust-region value
`min{|w − b*|²_Σ : |w| ≤ ρ}` for `ρ ≥ 0`. -/
def price_attained : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (n₀ n₁ : ℕ)
    (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (N₀ N₁ : Seminorm ℝ E)
    (Sg : E →L[ℝ] E) (b : E) (δ ρ : ℝ),
    ProbWeights a₀ → ProbWeights a₁ → PosDefOp Sg → 0 ≤ δ → 0 ≤ ρ →
      (∃ Pv, IsLeast (priceSet a₀ x₀ a₁ x₁ N₀ N₁ Sg b δ) Pv) ∧ ∃ m, IsLeast (trustSet Sg b ρ) m

/-- `thm:price`(i): `Π(δ) ≤ (1 − √δ/G(b*))₊² |b*|²_Σ`. -/
def price_upper : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n₀ n₁ : ℕ)
    (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (N₀ N₁ : Seminorm ℝ E)
    (Sg : E →L[ℝ] E) (b : E) (δ Pv : ℝ),
    ProbWeights a₀ → ProbWeights a₁ → 0 ≤ δ → 0 < Gfun a₀ x₀ a₁ x₁ N₀ N₁ b →
    IsLeast (priceSet a₀ x₀ a₁ x₁ N₀ N₁ Sg b δ) Pv →
      Pv ≤ max (1 - √δ / Gfun a₀ x₀ a₁ x₁ N₀ N₁ b) 0 ^ 2 * sigNorm Sg b ^ 2

/-- `thm:price`(ii): `Π(δ) ≥ (G(b*) − √δ)₊² / L²` for every `L > 0` bounding
`{|v|_{Σ₀} + |v|_{Σ₁} + N₀(v) + N₁(v)} / |v|_Σ` (in particular `L = L_G`), `Σ_s` about a common point `c`. -/
def price_lower : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n₀ n₁ : ℕ)
    (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (N₀ N₁ : Seminorm ℝ E)
    (Sg : E →L[ℝ] E) (b c : E) (δ L Pv : ℝ),
    ProbWeights a₀ → ProbWeights a₁ → 0 ≤ δ → 0 < L →
    (∀ v, smNorm a₀ x₀ c v + smNorm a₁ x₁ c v + N₀ v + N₁ v ≤ L * sigNorm Sg v) →
    IsLeast (priceSet a₀ x₀ a₁ x₁ N₀ N₁ Sg b δ) Pv →
      max (Gfun a₀ x₀ a₁ x₁ N₀ N₁ b - √δ) 0 ^ 2 / L ^ 2 ≤ Pv

/-- `thm:price`(ii), Wasserstein balls (`N_s = √r_s |·|`, `S = √r₀ + √r₁`): if
`vᵀ(Σ₀ + Σ₁ + S²I)v ≤ Λ vᵀΣv` for all `v` (`Λ ≥ λ_max(Σ^{-1/2}(Σ₀+Σ₁+S²I)Σ^{-1/2})`), then
`L = √(3Λ)` bounds the ratio, i.e. `L_G ≤ {3 λ_max(…)}^{1/2}`. -/
def price_LG_wass : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n₀ n₁ : ℕ)
    (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (N₀ N₁ : Seminorm ℝ E)
    (Sg : E →L[ℝ] E) (c : E) (r₀ r₁ Λ : ℝ),
    ProbWeights a₀ → ProbWeights a₁ → 0 ≤ r₀ → 0 ≤ r₁ →
    (∀ v, N₀ v = √r₀ * ‖v‖) → (∀ v, N₁ v = √r₁ * ‖v‖) →
    (∀ v, smNorm a₀ x₀ c v ^ 2 + smNorm a₁ x₁ c v ^ 2 + (√r₀ + √r₁) ^ 2 * ‖v‖ ^ 2 ≤
      Λ * sigNorm Sg v ^ 2) →
      ∀ v, smNorm a₀ x₀ c v + smNorm a₁ x₁ c v + N₀ v + N₁ v ≤ √(3 * Λ) * sigNorm Sg v

/-- `thm:price`(iii): if `N_s(w) ≥ c_s|w|`, then `Π(δ) ≥ min{|w − b*|²_Σ : |w| ≤ √δ/(c₀ + c₁)}`. -/
def price_trust : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n₀ n₁ : ℕ)
    (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (N₀ N₁ : Seminorm ℝ E)
    (Sg : E →L[ℝ] E) (b : E) (δ c₀ c₁ Pv m : ℝ),
    ProbWeights a₀ → ProbWeights a₁ → 0 ≤ δ → 0 ≤ c₀ → 0 ≤ c₁ → 0 < c₀ + c₁ →
    (∀ w, c₀ * ‖w‖ ≤ N₀ w) → (∀ w, c₁ * ‖w‖ ≤ N₁ w) →
    IsLeast (priceSet a₀ x₀ a₁ x₁ N₀ N₁ Sg b δ) Pv → IsLeast (trustSet Sg b (√δ / (c₀ + c₁))) m →
      m ≤ Pv

/-! #### SB `thm:field` -/

/-- `thm:field`, exactness: `(T_s)_#R_s = (S_ν⁻¹ ∘ S_{R_s})_#R_s = ν` for each group. -/
def field_exact : Prop :=
  ∀ (d : ℕ) (R : Fin 2 → Measure (EuclideanSpace ℝ (Fin d))) (ν γ : Measure (EuclideanSpace ℝ (Fin d)))
    (S Sinv : Fin 2 → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (Sν Sνinv : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
    (∀ s, Standardises (R s) γ (S s) (Sinv s)) → Standardises ν γ Sν Sνinv →
      ∀ s, (R s).map (Sνinv ∘ S s) = ν

/-- `thm:field`, the deterministic bound of the proof: for a globally `L`-Lipschitz `Ŝ_ν⁻¹`,
`W₂((T̂_s)_#R_s, ν) ≤ L‖Ŝ_{R_s} − S_{R_s}‖_{L²(R_s)} + ‖Ŝ_ν⁻¹ − S_ν⁻¹‖_{L²(γ)}`, and the parity gap
`W₂((T̂₀)_#R₀, (T̂₁)_#R₁)` is at most the sum over the two groups. -/
def field_bound : Prop :=
  ∀ (d : ℕ) (R : Fin 2 → Measure (EuclideanSpace ℝ (Fin d))) (ν γ : Measure (EuclideanSpace ℝ (Fin d)))
    (S Sinv Shat : Fin 2 → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (Sν Sνinv Sνinvhat : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L : ℝ≥0),
    (∀ s, IsProbabilityMeasure (R s)) → IsProbabilityMeasure ν → IsProbabilityMeasure γ →
    (∀ s, Standardises (R s) γ (S s) (Sinv s)) → Standardises ν γ Sν Sνinv →
    (∀ s, Measurable (Shat s)) → Measurable Sνinvhat → LipschitzWith L Sνinvhat →
      (∀ s, wassersteinEDist 2 ((R s).map (Sνinvhat ∘ Shat s)) ν ≤
          L * eLpNorm (fun x => Shat s x - S s x) 2 (R s) +
            eLpNorm (fun z => Sνinvhat z - Sνinv z) 2 γ) ∧
        wassersteinEDist 2 ((R 0).map (Sνinvhat ∘ Shat 0)) ((R 1).map (Sνinvhat ∘ Shat 1)) ≤
          ∑ s, (L * eLpNorm (fun x => Shat s x - S s x) 2 (R s) +
            eLpNorm (fun z => Sνinvhat z - Sνinv z) 2 γ)

/-- `thm:field`, rate: if the forward errors `‖Ŝ_{R_s} − S_{R_s}‖_{L²(R_s)}` and the inverse error
`‖Ŝ_ν⁻¹ − S_ν⁻¹‖_{L²(γ)}` are `O_P(r_n)` and `Ŝ_ν⁻¹` is `L`-Lipschitz on `ℝ^d` with probability tending to one,
then `W₂((T̂₀)_#R₀, (T̂₁)_#R₁) = O_P(r_n)`. -/
def field_rate : Prop :=
  ∀ (d : ℕ) (R : Fin 2 → Measure (EuclideanSpace ℝ (Fin d))) (ν γ : Measure (EuclideanSpace ℝ (Fin d)))
    (S Sinv : Fin 2 → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (Sν Sνinv : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (Shat : ℕ → Ω → Fin 2 → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (Sνinvhat : ℕ → Ω → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (r : ℕ → ℝ) (L : ℝ≥0),
    IsProbabilityMeasure P → (∀ n, 0 ≤ r n) →
    (∀ s, IsProbabilityMeasure (R s)) → IsProbabilityMeasure ν → IsProbabilityMeasure γ →
    (∀ s, Standardises (R s) γ (S s) (Sinv s)) → Standardises ν γ Sν Sνinv →
    (∀ n ω s, Measurable (Shat n ω s)) → (∀ n ω, Measurable (Sνinvhat n ω)) →
    (∀ s, BigOP P r fun n ω => eLpNorm (fun x => Shat n ω s x - S s x) 2 (R s)) →
    BigOP P r (fun n ω => eLpNorm (fun z => Sνinvhat n ω z - Sνinv z) 2 γ) →
    LipschitzWhp P L Sνinvhat →
      BigOP P r fun n ω => wassersteinEDist 2 ((R 0).map (Sνinvhat n ω ∘ Shat n ω 0))
        ((R 1).map (Sνinvhat n ω ∘ Shat n ω 1))

/-! #### SB `prop:pareto` -/

/-- Why atomless `R_s` is the standing setting: if some coupling of `R` and `ν` has a density with respect to
Lebesgue measure on `ℝ²` (as the optimal plan must when `C_ε(R, ν) < ∞`, differential entropy), `R` has no
atoms. -/
def pareto_atomless : Prop :=
  ∀ (R ν : Measure ℝ) (π : Measure (ℝ × ℝ)), IsCoupling π R ν → π ≪ volume → NullSingletonClass R

/-- `thm:flow`(i)–(ii) as used by `prop:pareto`: for atomless `R`, `Ψ_#R = μ` and
`∫ (Ψ(u) − u)² dR = W₂²(R, μ)`. -/
def pareto_flow : Prop :=
  ∀ (R μ : Measure ℝ), IsProbabilityMeasure R → IsProbabilityMeasure μ → NullSingletonClass R →
    R.map (flowMap R μ) = μ ∧
      ∫⁻ u, edist u (flowMap R μ u) ^ (2 : ℝ) ∂R = wassersteinEDist 2 R μ ^ (2 : ℝ)

/-- `thm:flow`(iii): every realisation `V` with the right law (every coupling of `R` and `μ`) costs at least
`W₂²(R, μ)`. -/
def pareto_weak : Prop :=
  ∀ (R μ : Measure ℝ) (σ : Measure (ℝ × ℝ)), IsCoupling σ R μ → wassersteinEDist 2 R μ ^ (2 : ℝ) ≤ qcost σ

/-- `prop:pareto`, strictness: for atomless `R ∈ 𝒫₂`, `μ ∈ 𝒫₂` and a stochastic realisation given by a Markov
kernel `K` with `(R ⊗ K).snd = μ` that is non-degenerate (not a Dirac mass) on a set of positive measure,
`W₂²(R, μ) < E(V − U)²`. -/
def pareto_strict : Prop :=
  ∀ (R μ : Measure ℝ) (K : Kernel ℝ ℝ), IsProbabilityMeasure R → IsProbabilityMeasure μ →
    IsMarkovKernel K → NullSingletonClass R → HasFiniteMoment 2 R → HasFiniteMoment 2 μ → (R ⊗ₘ K).snd = μ →
    (∃ A, MeasurableSet A ∧ 0 < R A ∧ ∀ u ∈ A, ∀ y, K u ≠ Measure.dirac y) →
      wassersteinEDist 2 R μ ^ (2 : ℝ) < qcost (R ⊗ₘ K)

/-- `prop:pareto` for the bridge kernel (`ε > 0`, `t ∈ (0,1)`), any coupling `π` of `R` and `ν`: the
stochastic realisation couples `R` with `μ_t = endpointMixture1 ε t π`, has finite cost, and costs strictly
more than `W₂²(R, μ_t)`. -/
def pareto_bridge : Prop :=
  ∀ (ε t : ℝ) (R ν : Measure ℝ) (π : Measure (ℝ × ℝ)), 0 < ε → t ∈ Ioo (0 : ℝ) 1 →
    IsProbabilityMeasure R → IsCoupling π R ν → NullSingletonClass R → HasFiniteMoment 2 R → HasFiniteMoment 2 ν →
      IsCoupling (stoPlan ε t π) R (StatFormal.Wave4b.endpointMixture1 ε t π) ∧
        qcost (stoPlan ε t π) < ∞ ∧
        wassersteinEDist 2 R (StatFormal.Wave4b.endpointMixture1 ε t π) ^ (2 : ℝ) <
          qcost (stoPlan ε t π)

/-- `prop:pareto`, two groups with weights `p_s`: both realisations induce the same repaired marginals
`μ_{s,t}`, hence the same value of every functional of the two marginals; and
`‖h̃^flow − h‖² = Σ_s p_s W₂²(R_s, μ_{s,t}) < ‖h̃^sto − h‖²`. -/
def pareto : Prop :=
  ∀ (ε t : ℝ) (p : Fin 2 → ℝ) (R : Fin 2 → Measure ℝ) (ν : Measure ℝ) (π : Fin 2 → Measure (ℝ × ℝ)),
    0 < ε → t ∈ Ioo (0 : ℝ) 1 → (∀ s, 0 ≤ p s) → ∑ s, p s = 1 →
    (∀ s, IsProbabilityMeasure (R s)) → (∀ s, IsCoupling (π s) (R s) ν) → (∀ s, NullSingletonClass (R s)) →
    (∀ s, HasFiniteMoment 2 (R s)) → HasFiniteMoment 2 ν →
      (∀ s, (R s).map (flowMap (R s) (StatFormal.Wave4b.endpointMixture1 ε t (π s))) =
          StatFormal.Wave4b.endpointMixture1 ε t (π s) ∧
        (stoPlan ε t (π s)).snd = StatFormal.Wave4b.endpointMixture1 ε t (π s)) ∧
      (∀ (α : Type) (Φ : Measure ℝ → Measure ℝ → α),
        Φ ((R 0).map (flowMap (R 0) (StatFormal.Wave4b.endpointMixture1 ε t (π 0))))
            ((R 1).map (flowMap (R 1) (StatFormal.Wave4b.endpointMixture1 ε t (π 1)))) =
          Φ (stoPlan ε t (π 0)).snd (stoPlan ε t (π 1)).snd) ∧
      ∑ s, ENNReal.ofReal (p s) * ∫⁻ u, edist u (flowMap (R s)
          (StatFormal.Wave4b.endpointMixture1 ε t (π s)) u) ^ (2 : ℝ) ∂(R s) =
        ∑ s, ENNReal.ofReal (p s) *
          wassersteinEDist 2 (R s) (StatFormal.Wave4b.endpointMixture1 ε t (π s)) ^ (2 : ℝ) ∧
      ∑ s, ENNReal.ofReal (p s) *
          wassersteinEDist 2 (R s) (StatFormal.Wave4b.endpointMixture1 ε t (π s)) ^ (2 : ℝ) <
        ∑ s, ENNReal.ofReal (p s) * qcost (stoPlan ε t (π s))

/-! #### trimmed MMD `prop:sinkexist` -/

/-- `OT_ε(μ,ν) < ∞` for probability measures and a bounded cost (so `OTe` is no `toReal ⊤` junk). -/
def sink_ot_finite : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (c : 𝒳 × 𝒳 → ℝ≥0) (ε : ℝ≥0) (μ ν : Measure 𝒳),
    IsProbabilityMeasure μ → IsProbabilityMeasure ν → (∃ M, ∀ z, c z ≤ M) →
      entropicTransportCost (fun z => (c z : ℝ≥0∞)) ε μ ν < ∞

/-- `R_α(P)` is compact for the weak topology (`𝒳` compact metric, `α ∈ [0,1)`). -/
def sink_trim_compact : Prop :=
  ∀ (𝒳 : Type) [MetricSpace 𝒳] [CompactSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳]
    (P : Measure 𝒳) (α : ℝ), IsProbabilityMeasure P → 0 ≤ α → α < 1 →
      IsCompact {P' : ProbabilityMeasure 𝒳 | (P' : Measure 𝒳) ∈ trimSet P α}

/-- `prop:sinkexist`: under (C), for every `α ∈ [0,1)` the infimum in `eq:trimSink` is attained. -/
def sink_attained : Prop :=
  ∀ (𝒳 : Type) [MetricSpace 𝒳] [CompactSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳]
    (c : 𝒳 × 𝒳 → ℝ≥0) (ε : ℝ≥0) (P Q : Measure 𝒳) (α : ℝ),
    Continuous c → IsProbabilityMeasure P → IsProbabilityMeasure Q → 0 ≤ α → α < 1 → JointCont c ε →
      ∃ P' ∈ trimSet P α, ∃ Q' ∈ trimSet Q α,
        IsLeast {v | ∃ P'' ∈ trimSet P α, ∃ Q'' ∈ trimSet Q α, v = sinkDiv c ε P'' Q''}
          (sinkDiv c ε P' Q')

end Claims
end StatFormal.Wave9b
