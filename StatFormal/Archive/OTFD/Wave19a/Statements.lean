import StatFormal.Archive.OTFD.Wave8c.Statements
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Hull

/-!
# FROZEN STATEMENTS — otfd wave 19a (QUEUE rows 197–203): A `lem:app-graph-barycenter`, A `lem:app-graph-empirical`,
# B `prop:rk-transfer`, B `prop:ext-whitening`, B `lem:app-subgradient-convergence`, G `lem:evaluation`, T `eq:graphprob`

Sources (verbatim in `lean-formalisation/inventory/extracted/otfd-{A_sieves,B_bands,G_geodesic,T_tangent}.md`; current
text after the 2026-10-13/14/15 corrections; paths under `otfd/papers/`):
* A `lem:app-graph-barycenter` (`A_sieves/supplement.tex:3477-3492`, proof `:3494-3523`).
* A `lem:app-graph-empirical` (`A_sieves/supplement.tex:3965-3979`, proof `:3981-4005`).
* T `lem:graph` with `eq:graphprob` (`T_tangent/supp_moved.tex:856-868`, proof `T_tangent/app_proofs.tex:89-98`).
* B `prop:rk-transfer` (`B_bands/main.tex:1224-1245`, proof `B_bands/supplement.tex:5258-5276`), with
  `def:rk-transfer` (`main.tex:1204-1210`) and `M_K`-monotone maps `½M_K⁻¹∇χ` (`main.tex:431-435`).
* B `prop:ext-whitening` (`B_bands/supplement.tex:1280-1319`, proof `:1322-1383`), with the out-of-sample maps and
  scores of `lem:oos-potential` (`main.tex:596-605`, `:664-695`) and the band setup (`main.tex:633-660`).
* B `lem:app-subgradient-convergence` (`B_bands/supplement.tex:1940-1950`, proof `:1952-1965`).
* G `lem:evaluation` (`G_geodesic/appendix.tex:57-62`, proof `:64-78`), with `𝒳`, `D` (`G_geodesic/main.tex:160-166`,
  `:232-240`).
Imports the frozen `OTFD/Wave8c/Statements.lean` (`mvec`, `mnorm`, `IsRankPair`, `IsGradMap`, `quadCost`), not copied;
Mathlib and Tau Ceti (`TauCeti.IsCoupling`, `TauCeti.subdifferential`, `TauCeti.wassersteinEDist`,
`TauCeti.IsKantorovichOptimalTransportMap`) otherwise. No `StatFormal/Foundations` file is imported.

Covered:
* A barycenter: `app_graph_barycenter` (`∫‖u − F(x)‖²dγ_q → 0`, the proof's `eq:app-jensen-graph` right side, and
  `∫‖B_q − F‖²dP₀ → 0`); `app_graph_barycenter_family` (the last sentence, any countably generated filter `t → t₀`).
* A empirical: `app_graph_empirical` (a.s. and in expectation); `app_graph_empirical_barycenter` (the "Consequently").
* T `lem:graph`: `graphprob` (`eq:graphprob`, measurable event); `graph_ui` (uniform integrability ⇒ integrals → 0);
  `graph_bounded` (bounded `y` and `Q(u)` ⇒ uniform integrability and integrals → 0); `graph_barycenter`.
* B `prop:rk-transfer`: (i)–(ii) are **already certified** as `Wave8c.Claims.transfer_push_rank`, `transfer_unique`
  (identical statements for any reference, via `IsRankPair`; not duplicated). New: `rk_transfer_rank_functions` ((i),
  "hence depth and sign": every function of the rank); `rk_transfer_scalar_affine` ((iii)); `rk_transfer_affine` ((iv)
  closed forms of `Q_A`, `F_A`, `T_{A→B}`); `rk_transfer_affine_optimal_iff` ((iv) last sentence, strengthened to iff).
* B `prop:ext-whitening`: (a) `whiten_cost`, `whiten_wasserstein`, `whiten_scores`, `whiten_oos`; (b) `whiten_calib`,
  `whiten_support`, `whiten_ac`, `whiten_geom`; (c) `whiten_band`, `whiten_gaps`; (d) `whiten_population`,
  `whiten_essrange`, `whiten_subdiff`.
* B subgradients: `subgrad_conv_point` ((a)), `subgrad_conv_unif` ((b)).
* G `lem:evaluation`: general complete separable metric `M`: `evaluation_exists_metric`, `evaluation_unique_metric`
  (both sentences of uniqueness); flat case `𝒳 = L²(λ; E)` kept as `evaluation_exists`, `evaluation_unique`.

Not covered (declared):
* A/T: nothing beyond the encodings below (Lusin/Tietze are proof devices; the proofs use density of `C_b` in `L¹`).
* B `prop:rk-transfer`: the existence of the population maps (`thm:prob-content`(c), A paper) enters as hypotheses
  (`IsRankPair`, `IsMGradMap`); the closing `\ext{}` remark (cocycle: certified Wave 17a; fitted transfers).
* B `prop:ext-whitening`: the Karp/Moreau–Yosida map in (a) (Laguerre potential not encoded); in (c) the certified and
  inner edges of `prop:band-certificate`, `prop:band-inner-certificate` and the caps `κ_j` (built from the quantities
  shown to coincide; not encoded); in (d) "continuous on `O` iff on `LO`" (conjugation by a homeomorphism; only the
  subdifferential identity is stated); "hence so do the optimal couplings, dual vectors and semi-dual values" (functions
  of the identical cost matrix, `whiten_cost`); `τ_{K,p}` unchanged (same function `c_K`, `whiten_calib`); the
  "Consequently … verbatim" clause (meta-transfer of L3 results).
* G `lem:evaluation`: no Riemannian content is used (as the queue row notes); `λ` is a probability as printed
  (`T = [0,1]` generalised to any countably generated `T`).

Encodings:
* A/T: `ℝ^K = EuclideanSpace ℝ (Fin K)`; `H` a separable real Hilbert space, Borel. Weak convergence `WeakTo l` is
  convergence of `∫ f` for every bounded continuous `f` on the product (`(Id,F)#P₀ = graphLaw P₀ F`, `F` measurable, so
  the push-forward is genuine). A disintegration `γ = P₀(dx)γ^x(du)` is any Markov kernel `κ` with `γ = P₀ ⊗ₘ κ`
  (version-free), `B(x) = ∫ u κ(x, du)` (`bary`; integrable for `P₀`-a.e. `x` under the hypotheses, so the Bochner
  junk value `0` is irrelevant). All integrals of squares are `ℝ≥0∞` lintegrals (`sqDisc F z = ‖z.2 − F z.1‖ₑ²`), so
  no non-integrable junk. `Q_q(C) = 1` is `(γ_q.map snd)(C) = 1`; `C` compact (used only through boundedness).
* A empirical: `X_i` measurable, **pairwise** independent, each with law `P₀` (generalises iid); `P̂_n = n⁻¹Σ_{i<n}δ_{X_i}`
  (`empHat`; hypotheses only for `n ≥ 1`); the random couplings are a measurable kernel `Ω → 𝒫(ℝ^K × ℝ^K)` (needed for
  "in expectation"); the disintegrations of the "Consequently" are arbitrary per `ω` (expectation of an `ℝ≥0∞` function,
  meaningful without measurability).
* T: `Γ_n ∈ Π(μ, ν_n)` is `TauCeti.IsCoupling`; uniform integrability `SqUI`: for every `ε > 0` a finite `M` with
  `sup_n ∫_{‖y−Q(u)‖²>M} ‖y−Q(u)‖² dΓ_n ≤ ε`; "uniform boundedness" is `‖y‖ ≤ B` `Γ_n`-a.e. for all `n` and `‖Q(u)‖ ≤ B`
  `μ`-a.e.
* B transfer: `M_K`-monotone `= ½M⁻¹∇χ` is `IsMGradMap M α β T` (`M T(x) ∈ ∂φ(x)` `α`-a.e., `φ = χ/2`; `M = 1` is the frozen
  `IsGradMap`). (iii)/(iv) assume `μ ≪ Leb`, finite second moments of `μ` (and of `P_{A,K}` in (iii)), as Tau Ceti's
  Brenier uniqueness needs (declared conditionalisation; B's references are a.c. and boundedly supported). `M`-optimal
  is `TauCeti.IsKantorovichOptimalTransportMap (mCost M)`, `mCost = ‖x − y‖²_M/2` (same maps as `‖x − y‖²_M`); the
  optimality claim assumes the standing convexity of `supp μ_K` (an open set inside `supp P_{A,K}`). `P_{•,K} =
  μ.map (m_• + S_•·)`; "`M S` symmetric PD" is `(M * S).PosDef`.
* B whitening: `L` any matrix with `LᵀL = M`, `M` `PosDef` (so `L` invertible); `W_{2,M}` (`w2M`) is Tau Ceti's
  coupling infimum with ground cost `‖x − y‖_M`; scores `s_j(u) = f_j − ‖Z_j‖²_M + ⟨2MZ_j, u⟩` (`oosScore`); the entropic /
  quadratic map `Σ_j G((f − ‖u − Z‖²_M)/λ)_j Z_j` for an **arbitrary** weight rule `G` (`oosMap`; softmax, simplex
  projection: generalisation); whitened objects use `M = 1` and data `LZ_j`. Regions `{u ∈ supp μ : g(u) ≤ τ}` with gauge
  `g ∘ L⁻¹` in the whitened instance. Band/edge/support-function identities are stated as equalities of the **sets of
  values** (so every `sup`/`inf`, i.e. every edge or `h(v)`, coincides, with no `sSup` junk). Essential ranges are
  `supp(Q#(μ|A))`; `𝒮 = closure(conv ℛ)`.
* B subgradients: `g_n, g : ℝ^K → ℝ` convex on the open convex `C`; `∂g_n(u)` is Tau Ceti's subdifferential of `g_n`
  extended by `+∞` off `C` (`extTop`; equal to the local subdifferential at points of `C`); "uniformly on compact
  subsets" is `TendstoUniformlyOn` on every compact `S ⊆ C`; `∇g(u) = gradient g u` with `DifferentiableAt` (no junk);
  `ξ_n ∈ ∂g_n(u_n)` eventually (generalisation); the supremum in (b) is "eventually `≤ ε` for every `ε > 0`" (no
  `sSup` junk).
* G (general): `M` a complete, second-countable metric space, Borel (covers `S^q`, `SO(3)`, Hadamard spaces);
  `𝒳 = XSpace λ m = {x : T →ₘ[λ] M // D(x, m) < ∞}` for an arbitrary base class `m`, with
  `D(x,y) = (∫⁻ edist(x t, y t)² dλ)^{1/2}` (`dEv`, on `λ`-classes, `ℝ≥0∞`-valued, no junk) and the σ-algebra
  generated by the open `D`-balls (`XSpace.instMeasurableSpace`; `(𝒳, D)` is separable, proved in the route, so this
  is its Borel σ-algebra); representatives are the coercions `⇑x`.
* G (flat): `T` any countably generated measurable space with σ-finite `λ` (`[0,1]` with a probability: generalisation), `E`
  any separable Banach space, Borel (`ℝ^q`: specialisation of `M`); `𝒳 = Lp E 2 λ` with an arbitrary Borel
  `MeasurableSpace` instance; `ev(x, ·)` a representative of `x` is `(t ↦ ev(x,t)) =ᵐ[λ] ⇑x`; `𝓑(𝒳) ⊗ 𝓑(T)` is the
  product σ-algebra; laws `Q.map (ev(·, t))` (measurable sections, so genuine push-forwards).
* All claims quantify spaces over `Type` (universe 0), as elsewhere in the repo.

Critic notes:
* All 31 claims are proved in `Wave19a/Route{Graph,Subgrad,Eval,EvalMetric,Whiten,Transfer}.lean` (only propext, choice,
  Quot.sound only). No statement was found false.
* A/T: the proofs replace Lusin + Tietze by `C_b`-density in `L¹(μ)` after truncating `Q`; the barycentre step is the
  pointwise `ℝ≥0∞` conditional Jensen (valid even where `y` is not integrable).
* A empirical: the expectation clause presupposes measurability in `ω` of the random couplings (silent in the paper);
  encoded by a kernel. Only pairwise independence is used (SLLN for countably many bounded functions of `X_i`).
* B rk-transfer (iv): proved as an **iff** (`M S_B S_A⁻¹` symmetric ⇒ `M`-optimal as well), under the standing
  convex support of `μ_K`; `M S_A`, `M S_B` symmetric PD as printed. (iii)–(iv) are conditional on `μ ≪ Leb` and finite
  second moments (Brenier uniqueness).
* B whitening (d): "`Q_{±,K} = L⁻¹ ∘ Q' ∘ L`" holds `μ`-a.e. for **every** Brenier map `Q'` of the whitened pair, under
  `μ ≪ Leb` and second moments; the converse direction (the whitened `M`-monotone map is a Brenier map) needs nothing.
* G: general `M` proved (`RouteEvalMetric.lean`): separability of `(𝒳, D)` via the Kuratowski embedding into the
  separable Banach space `closure(span ι(M)) ⊆ ℓ^∞` and `L²(λ; ·)`; `ev` as in the paper's proof (dyadic nearest
  points of a dense sequence; `Σ_k D(z^{j_k(x)}, x) < ∞` gives a.e. convergence directly).
* B whitening (a), hard (Laguerre) map: covered by `whiten_oos` with `G` = one-hot of the argmax of the score vector
  under any tie-break that depends only on that vector (e.g. least index), `λ = 1`: the vector passed to `G` is
  `s(u) − ‖u‖²_M` and is identical in the whitened instance. A tie-break depending on `u` otherwise is not covered.
* A `app_graph_empirical_barycenter`: `κ n ω` at each atom of `P̂_n` is fixed by `γ n ω` (critic's observation),
  so the integrand is a function of `γ n ω` and the `ℝ≥0∞` expectation is a genuine one; the encoding does not
  need (and the route does not prove) this measurability.
* Paper (critic S3): A `lem:app-graph-empirical` claims convergence "in expectation" without requiring the random
  couplings to be measurable in `ω`; with non-measurable couplings the outer expectation can stay above some
  `c > 0`. The draft assumes a measurable kernel.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Matrix
open scoped ENNReal InnerProductSpace RealInnerProductSpace BoundedContinuousFunction

namespace StatFormal.OTFD.Wave19a

open StatFormal.OTFD.Wave8c (mvec mnorm IsRankPair IsGradMap quadCost)

/-! ### Graph convergence (A `lem:app-graph-barycenter`, `lem:app-graph-empirical`; T `lem:graph`) -/

section Graph
variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- Weak convergence along a filter: `∫ f dμ_i → ∫ f dμ` for every bounded continuous `f`. -/
def WeakTo {ι : Type*} (l : Filter ι) (μs : ι → Measure X) (μ : Measure X) : Prop :=
  ∀ f : X →ᵇ ℝ, Tendsto (fun i => ∫ x, f x ∂(μs i)) l (𝓝 (∫ x, f x ∂μ))

/-- The graph law `(Id, F)#μ`. -/
def graphLaw {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (F : X → Y) :
    Measure (X × Y) :=
  μ.map fun x => (x, F x)

/-- The squared discrepancy `‖y − F(x)‖²` of a point `(x, y)` from the graph of `F`. -/
def sqDisc {E : Type*} [NormedAddCommGroup E] (F : X → E) (z : X × E) : ℝ≥0∞ :=
  ‖z.2 - F z.1‖ₑ ^ 2

/-- The conditional barycentre `x ↦ ∫ y κ(x, dy)` of a disintegration kernel. -/
def bary {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    (κ : ProbabilityTheory.Kernel X E) (x : X) : E :=
  ∫ y, y ∂(κ x)

/-- The empirical measure `P̂_n = n⁻¹ Σ_{i<n} δ_{X_i}`. -/
def empHat {Ω E : Type*} [MeasurableSpace E] (Xs : ℕ → Ω → E) (n : ℕ) (ω : Ω) : Measure E :=
  (n : ℝ≥0∞)⁻¹ • ∑ i ∈ Finset.range n, Measure.dirac (Xs i ω)

/-- Uniform integrability of the squared discrepancies under `Γ_n`. -/
def SqUI {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] (Γ : ℕ → Measure (X × E)) (F : X → E) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ n, ∫⁻ z in {z | M < sqDisc F z}, sqDisc F z ∂(Γ n) ≤ ε

end Graph

/-! ### Euclidean geometry with a metric `M` (B `prop:rk-transfer`, `prop:ext-whitening`) -/

section Metric
variable {K : ℕ}

/-- `T` is `M`-monotone from `α` to `β`: measurable, `T#α = β`, and `M T(x) ∈ ∂φ(x)` `α`-a.e. for one
`φ : ℝ^K → (−∞, ∞]`, i.e. `T = ½M⁻¹∇χ` (`χ = 2φ` convex) as a subgradient selection. `M = 1` is `IsGradMap`. -/
def IsMGradMap (M : Matrix (Fin K) (Fin K) ℝ) (α β : Measure (EuclideanSpace ℝ (Fin K)))
    (T : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) : Prop :=
  Measurable T ∧ α.map T = β ∧
    ∃ φ : EuclideanSpace ℝ (Fin K) → EReal,
      ∀ᵐ x ∂α, mvec M (T x) ∈ TauCeti.subdifferential (innerₗ (EuclideanSpace ℝ (Fin K))) φ x

/-- The `M`-quadratic cost `‖x − y‖²_M / 2`. -/
def mCost (M : Matrix (Fin K) (Fin K) ℝ) (z : EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K)) : ℝ≥0∞ :=
  ENNReal.ofReal (mnorm M (z.1 - z.2) ^ 2 / 2)

/-- `W_{2,M}(α, β)`: the `2`-Wasserstein distance for the ground metric `‖x − y‖_M`. -/
def w2M (M : Matrix (Fin K) (Fin K) ℝ) (α β : Measure (EuclideanSpace ℝ (Fin K))) : ℝ≥0∞ :=
  ⨅ (π : Measure (EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K))) (_ : TauCeti.IsCoupling π α β),
    eLpNorm (fun z => ENNReal.ofReal (mnorm M (z.1 - z.2))) 2 π

/-- The affine scores `s_j(u) = a_j + ⟨b_j, u⟩`, `a_j = f_j − ‖Z_j‖²_M`, `b_j = 2MZ_j` (`lem:oos-potential`). -/
def oosScore {n : ℕ} (M : Matrix (Fin K) (Fin K) ℝ) (f : Fin n → ℝ) (Z : Fin n → EuclideanSpace ℝ (Fin K))
    (u : EuclideanSpace ℝ (Fin K)) (j : Fin n) : ℝ :=
  f j - mnorm M (Z j) ^ 2 + ⟪(2 : ℝ) • mvec M (Z j), u⟫

/-- The out-of-sample map `Q̂(u) = Σ_j G((f − ‖u − Z‖²_M)/λ)_j Z_j` for a weight rule `G` (softmax: entropic;
Euclidean projection onto the simplex: quadratic). -/
def oosMap {n : ℕ} (G : (Fin n → ℝ) → Fin n → ℝ) (lam : ℝ) (M : Matrix (Fin K) (Fin K) ℝ) (f : Fin n → ℝ)
    (Z : Fin n → EuclideanSpace ℝ (Fin K)) (u : EuclideanSpace ℝ (Fin K)) : EuclideanSpace ℝ (Fin K) :=
  ∑ j, G (fun i => (f i - mnorm M (u - Z i) ^ 2) / lam) j • Z j

/-- A real function on the open set `C`, extended by `+∞` off `C`. -/
def extTop {K : ℕ} (C : Set (EuclideanSpace ℝ (Fin K))) (g : EuclideanSpace ℝ (Fin K) → ℝ)
    (x : EuclideanSpace ℝ (Fin K)) : EReal :=
  by classical exact if x ∈ C then ((g x : ℝ) : EReal) else ⊤

end Metric

/-! ### Curves in a metric space (G `lem:evaluation`) -/

section Curves
variable {T M : Type*} [MeasurableSpace T] [MetricSpace M] (lam : Measure T)

/-- `D(x, y) = (∫ d_M(x(t), y(t))² dλ)^{1/2}` on `λ`-classes of measurable curves (`ℝ≥0∞`-valued). -/
def dEv (x y : T →ₘ[lam] M) : ℝ≥0∞ := (∫⁻ t, edist (x t) (y t) ^ 2 ∂lam) ^ (1 / 2 : ℝ)

/-- `𝒳 = {x : T → M measurable : D(x, m) < ∞}/∼_λ`. -/
def XSpace (m : T →ₘ[lam] M) : Type _ := {x : T →ₘ[lam] M // dEv lam x m < ⊤}

/-- The σ-algebra of `𝒳` generated by the open `D`-balls (the Borel σ-algebra of the separable space `(𝒳, D)`). -/
instance XSpace.instMeasurableSpace (m : T →ₘ[lam] M) : MeasurableSpace (XSpace lam m) :=
  MeasurableSpace.generateFrom {S | ∃ (x : XSpace lam m) (r : ℝ≥0∞), S = {y | dEv lam x.1 y.1 < r}}

end Curves

namespace Claims

/-! #### A `lem:app-graph-barycenter` -/

/-- `lem:app-graph-barycenter`: if `γ_q = P₀ ⊗ γ_q^x ⇀ (Id,F)#P₀` with second marginals on the compact `C`, then
`∫‖u − F(x)‖² dγ_q → 0` and the barycentres satisfy `∫‖B_q − F‖² dP₀ → 0`. -/
def app_graph_barycenter : Prop :=
  ∀ (K : ℕ) (P0 : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure P0]
    (C : Set (EuclideanSpace ℝ (Fin K)))
    (γ : ℕ → Measure (EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K)))
    (Qq : ℕ → Measure (EuclideanSpace ℝ (Fin K)))
    (κ : ℕ → Kernel (EuclideanSpace ℝ (Fin K)) (EuclideanSpace ℝ (Fin K))) [∀ q, IsMarkovKernel (κ q)]
    (F : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)),
    IsCompact C → Measurable F → (∀ x, F x ∈ C) →
    (∀ q, γ q = P0 ⊗ₘ κ q) → (∀ q, (γ q).map Prod.snd = Qq q) → (∀ q, Qq q C = 1) →
    WeakTo atTop γ (graphLaw P0 F) →
      Tendsto (fun q => ∫⁻ z, sqDisc F z ∂(γ q)) atTop (𝓝 0) ∧
        Tendsto (fun q => ∫⁻ x, ‖bary (κ q) x - F x‖ₑ ^ 2 ∂P0) atTop (𝓝 0)

/-- The last sentence: a family `γ_t`, `t → t₀` (any countably generated filter), every sequence of which has the
weak limit `(Id,F)#P₀`. -/
def app_graph_barycenter_family : Prop :=
  ∀ (K : ℕ) {ι : Type} (l : Filter ι) [l.IsCountablyGenerated]
    (P0 : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure P0] (C : Set (EuclideanSpace ℝ (Fin K)))
    (γ : ι → Measure (EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K)))
    (Qt : ι → Measure (EuclideanSpace ℝ (Fin K)))
    (κ : ι → Kernel (EuclideanSpace ℝ (Fin K)) (EuclideanSpace ℝ (Fin K))) [∀ t, IsMarkovKernel (κ t)]
    (F : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)),
    IsCompact C → Measurable F → (∀ x, F x ∈ C) →
    (∀ t, γ t = P0 ⊗ₘ κ t) → (∀ t, (γ t).map Prod.snd = Qt t) → (∀ t, Qt t C = 1) →
    (∀ s : ℕ → ι, Tendsto s atTop l → WeakTo atTop (γ ∘ s) (graphLaw P0 F)) →
      Tendsto (fun t => ∫⁻ z, sqDisc F z ∂(γ t)) l (𝓝 0) ∧
        Tendsto (fun t => ∫⁻ x, ‖bary (κ t) x - F x‖ₑ ^ 2 ∂P0) l (𝓝 0)

/-! #### A `lem:app-graph-empirical` -/

/-- `lem:app-graph-empirical`: iid `X_i ~ P₀`, random couplings `γ_n ∈ Π(P̂_n, Q_n)` (a measurable kernel in
`ω`) with `Q_n(C) = 1` and `γ_n ⇀ (Id,F)#P₀` a.s.; then `∫‖u − F(x)‖² dγ_n → 0` a.s. and in expectation. -/
def app_graph_empirical : Prop :=
  ∀ (K : ℕ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (P0 : Measure (EuclideanSpace ℝ (Fin K))) (C : Set (EuclideanSpace ℝ (Fin K)))
    (F : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (Xs : ℕ → Ω → EuclideanSpace ℝ (Fin K))
    (γ : ℕ → Kernel Ω (EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K))),
    IsCompact C → Measurable F → (∀ x, F x ∈ C) →
    (∀ i, Measurable (Xs i)) → Pairwise (fun i j => IndepFun (Xs i) (Xs j) P) → (∀ i, P.map (Xs i) = P0) →
    (∀ n, 1 ≤ n → ∀ ω, (γ n ω).map Prod.fst = empHat Xs n ω ∧ ((γ n ω).map Prod.snd) C = 1) →
    (∀ᵐ ω ∂P, WeakTo atTop (fun n => γ n ω) (graphLaw P0 F)) →
      (∀ᵐ ω ∂P, Tendsto (fun n => ∫⁻ z, sqDisc F z ∂(γ n ω)) atTop (𝓝 0)) ∧
        Tendsto (fun n => ∫⁻ ω, ∫⁻ z, sqDisc F z ∂(γ n ω) ∂P) atTop (𝓝 0)

/-- The barycentric consequence: for any disintegrations `γ_n = P̂_n ⊗ γ_n^x` (chosen per `ω`, no measurability
in `ω`), `∫‖B_n − F‖² dP̂_n → 0` a.s. and in expectation. -/
def app_graph_empirical_barycenter : Prop :=
  ∀ (K : ℕ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (P0 : Measure (EuclideanSpace ℝ (Fin K))) (C : Set (EuclideanSpace ℝ (Fin K)))
    (F : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (Xs : ℕ → Ω → EuclideanSpace ℝ (Fin K))
    (γ : ℕ → Kernel Ω (EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K)))
    (κ : ℕ → Ω → Kernel (EuclideanSpace ℝ (Fin K)) (EuclideanSpace ℝ (Fin K))) [∀ n ω, IsMarkovKernel (κ n ω)],
    IsCompact C → Measurable F → (∀ x, F x ∈ C) →
    (∀ i, Measurable (Xs i)) → Pairwise (fun i j => IndepFun (Xs i) (Xs j) P) → (∀ i, P.map (Xs i) = P0) →
    (∀ n, 1 ≤ n → ∀ ω, (γ n ω).map Prod.fst = empHat Xs n ω ∧ ((γ n ω).map Prod.snd) C = 1) →
    (∀ n, 1 ≤ n → ∀ ω, γ n ω = empHat Xs n ω ⊗ₘ κ n ω) →
    (∀ᵐ ω ∂P, WeakTo atTop (fun n => γ n ω) (graphLaw P0 F)) →
      (∀ᵐ ω ∂P, Tendsto (fun n => ∫⁻ x, ‖bary (κ n ω) x - F x‖ₑ ^ 2 ∂(empHat Xs n ω)) atTop (𝓝 0)) ∧
        Tendsto (fun n => ∫⁻ ω, ∫⁻ x, ‖bary (κ n ω) x - F x‖ₑ ^ 2 ∂(empHat Xs n ω) ∂P) atTop (𝓝 0)

/-! #### T `lem:graph` (`eq:graphprob`) -/

/-- `eq:graphprob`: `Γ_n ∈ Π(μ, ν_n)`, `Γ_n ⇀ (Id,Q)#μ` on `H × H`, `Q` Borel ⇒ `Γ_n{‖y − Q(u)‖ > γ} → 0`
(a measurable event) for every `γ > 0`. -/
def graphprob : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [IsProbabilityMeasure μ] (ν : ℕ → Measure H)
    (Γ : ℕ → Measure (H × H)) (Q : H → H),
    Measurable Q → (∀ n, TauCeti.IsCoupling (Γ n) μ (ν n)) → WeakTo atTop Γ (graphLaw μ Q) →
      ∀ γ : ℝ, 0 < γ → MeasurableSet {z : H × H | γ < ‖z.2 - Q z.1‖} ∧
        Tendsto (fun n => Γ n {z | γ < ‖z.2 - Q z.1‖}) atTop (𝓝 0)

/-- Uniformly integrable squared discrepancies have vanishing integrals. -/
def graph_ui : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [IsProbabilityMeasure μ] (ν : ℕ → Measure H)
    (Γ : ℕ → Measure (H × H)) (Q : H → H),
    Measurable Q → (∀ n, TauCeti.IsCoupling (Γ n) μ (ν n)) → WeakTo atTop Γ (graphLaw μ Q) → SqUI Γ Q →
      Tendsto (fun n => ∫⁻ z, sqDisc Q z ∂(Γ n)) atTop (𝓝 0)

/-- Uniform boundedness of `y` (under every `Γ_n`) and of `Q(u)` (under `μ`) suffices: it gives uniform
integrability, hence vanishing integrals. -/
def graph_bounded : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [IsProbabilityMeasure μ] (ν : ℕ → Measure H)
    (Γ : ℕ → Measure (H × H)) (Q : H → H) (B : ℝ),
    Measurable Q → (∀ n, TauCeti.IsCoupling (Γ n) μ (ν n)) → WeakTo atTop Γ (graphLaw μ Q) →
    (∀ n, ∀ᵐ z ∂(Γ n), ‖z.2‖ ≤ B) → (∀ᵐ u ∂μ, ‖Q u‖ ≤ B) →
      SqUI Γ Q ∧ Tendsto (fun n => ∫⁻ z, sqDisc Q z ∂(Γ n)) atTop (𝓝 0)

/-- The barycentre `Q̄_n(u) = ∫ y Γ_n(dy | u)` of any disintegration satisfies `∫‖Q̄_n − Q‖² dμ → 0` under
uniform integrability. -/
def graph_barycenter : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [IsProbabilityMeasure μ] (ν : ℕ → Measure H)
    (Γ : ℕ → Measure (H × H)) (Q : H → H) (κ : ℕ → Kernel H H) [∀ n, IsMarkovKernel (κ n)],
    Measurable Q → (∀ n, TauCeti.IsCoupling (Γ n) μ (ν n)) → (∀ n, Γ n = μ ⊗ₘ κ n) →
    WeakTo atTop Γ (graphLaw μ Q) → SqUI Γ Q →
      Tendsto (fun n => ∫⁻ u, ‖bary (κ n) u - Q u‖ₑ ^ 2 ∂μ) atTop (𝓝 0)

/-! #### B `prop:rk-transfer` -/

/-- (i), second sentence: every function of the rank (depth, sign) of `T_{A→B}(z)` in `B` equals that of `z` in
`A`, `P_{A,K}`-a.e. -/
def rk_transfer_rank_functions : Prop :=
  ∀ (K : ℕ) (μ PA PB : Measure (EuclideanSpace ℝ (Fin K)))
    (FA QA FB QB : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (α : Type) (φ : EuclideanSpace ℝ (Fin K) → α),
    IsRankPair μ PA FA QA → IsRankPair μ PB FB QB → ∀ᵐ z ∂PA, φ (FB (QB (FA z))) = φ (FA z)

/-- (iii) Scalar-affine equivariance: `P_{B,K} = φ#P_{A,K}`, `φ(z) = b + cz`, `c > 0` ⇒ `T_{A→B} = φ`, `P_{A,K}`-a.e. -/
def rk_transfer_scalar_affine : Prop :=
  ∀ (K : ℕ) (M : Matrix (Fin K) (Fin K) ℝ) (μ PA : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure μ]
    (FA QA QB : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (b : EuclideanSpace ℝ (Fin K)) (c : ℝ),
    M.PosDef → μ ≪ volume → MemLp id 2 μ → MemLp id 2 PA → 0 < c →
    IsRankPair μ PA FA QA → IsMGradMap M μ PA QA → IsMGradMap M μ (PA.map fun z => b + c • z) QB →
      (fun z => QB (FA z)) =ᵐ[PA] fun z => b + c • z

/-- (iv) Affine-reference laws: `Q_A = m_A + S_A·`, `F_A = S_A⁻¹(· − m_A)`, `T_{A→B} = m_B + S_BS_A⁻¹(· − m_A)`. -/
def rk_transfer_affine : Prop :=
  ∀ (K : ℕ) (M SA SB : Matrix (Fin K) (Fin K) ℝ) (mA mB : EuclideanSpace ℝ (Fin K))
    (μ : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure μ]
    (FA QA QB : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)),
    M.PosDef → (M * SA).PosDef → (M * SB).PosDef → μ ≪ volume → MemLp id 2 μ →
    IsRankPair μ (μ.map fun u => mA + mvec SA u) FA QA → IsMGradMap M μ (μ.map fun u => mA + mvec SA u) QA →
    IsMGradMap M μ (μ.map fun u => mB + mvec SB u) QB →
      (QA =ᵐ[μ] fun u => mA + mvec SA u) ∧
        (FA =ᵐ[μ.map fun u => mA + mvec SA u] fun z => mvec SA⁻¹ (z - mA)) ∧
          ((fun z => QB (FA z)) =ᵐ[μ.map fun u => mA + mvec SA u] fun z => mB + mvec (SB * SA⁻¹) (z - mA))

/-- (iv), last sentence (as an equivalence): `T_{A→B}` is the `M`-optimal transport map from `P_{A,K}` to `P_{B,K}`
iff `M S_B S_A⁻¹` is symmetric. -/
def rk_transfer_affine_optimal_iff : Prop :=
  ∀ (K : ℕ) (M SA SB : Matrix (Fin K) (Fin K) ℝ) (mA mB : EuclideanSpace ℝ (Fin K))
    (μ : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure μ]
    (FA QA QB : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)),
    M.PosDef → (M * SA).PosDef → (M * SB).PosDef → μ ≪ volume → MemLp id 2 μ → Convex ℝ μ.support →
    IsRankPair μ (μ.map fun u => mA + mvec SA u) FA QA → IsMGradMap M μ (μ.map fun u => mA + mvec SA u) QA →
    IsMGradMap M μ (μ.map fun u => mB + mvec SB u) QB →
      (TauCeti.IsKantorovichOptimalTransportMap (mCost M) (μ.map fun u => mA + mvec SA u)
          (μ.map fun u => mB + mvec SB u) (fun z => QB (FA z)) ↔
        (M * SB * SA⁻¹)ᵀ = M * SB * SA⁻¹)

/-! #### B `prop:ext-whitening` -/

/-- (a) The costs coincide: `‖z − u‖²_M = ‖Lz − Lu‖²`. -/
def whiten_cost : Prop :=
  ∀ (K : ℕ) (M L : Matrix (Fin K) (Fin K) ℝ), Lᵀ * L = M →
    ∀ z u : EuclideanSpace ℝ (Fin K), mnorm M (z - u) ^ 2 = ‖mvec L z - mvec L u‖ ^ 2

/-- (a) `W_{2,M}(α, β) = W₂(L#α, L#β)`. -/
def whiten_wasserstein : Prop :=
  ∀ (K : ℕ) (M L : Matrix (Fin K) (Fin K) ℝ), M.PosDef → Lᵀ * L = M →
    ∀ α β : Measure (EuclideanSpace ℝ (Fin K)),
      w2M M α β = TauCeti.wassersteinEDist 2 (α.map (mvec L)) (β.map (mvec L))

/-- (a) The scores satisfy `s_j(u) = s'_j(Lu)` (whitened data `LZ_j`, Euclidean metric). -/
def whiten_scores : Prop :=
  ∀ (K n : ℕ) (M L : Matrix (Fin K) (Fin K) ℝ), Lᵀ * L = M →
    ∀ (f : Fin n → ℝ) (Z : Fin n → EuclideanSpace ℝ (Fin K)) (u : EuclideanSpace ℝ (Fin K)) (j : Fin n),
      oosScore M f Z u j = oosScore 1 f (fun i => mvec L (Z i)) (mvec L u) j

/-- (a) `Q̂_n = L⁻¹ ∘ Q̂'_n ∘ L` for every weight rule (entropic, quadratic). -/
def whiten_oos : Prop :=
  ∀ (K n : ℕ) (M L : Matrix (Fin K) (Fin K) ℝ), M.PosDef → Lᵀ * L = M →
    ∀ (G : (Fin n → ℝ) → Fin n → ℝ) (lam : ℝ) (f : Fin n → ℝ) (Z : Fin n → EuclideanSpace ℝ (Fin K))
      (u : EuclideanSpace ℝ (Fin K)),
      oosMap G lam M f Z u = mvec L⁻¹ (oosMap G lam 1 f (fun i => mvec L (Z i)) (mvec L u))

/-- (b) `c_K` is unchanged: `(L#μ)(g ∘ L⁻¹ ≤ τ) = μ(g ≤ τ)` for every `τ`. -/
def whiten_calib : Prop :=
  ∀ (K : ℕ) (M L : Matrix (Fin K) (Fin K) ℝ), M.PosDef → Lᵀ * L = M →
    ∀ (μ : Measure (EuclideanSpace ℝ (Fin K))) (g : EuclideanSpace ℝ (Fin K) → ℝ), Measurable g → ∀ τ : ℝ,
      (μ.map (mvec L)) {w | g (mvec L⁻¹ w) ≤ τ} = μ {u | g u ≤ τ}

/-- (b) `supp(L#μ) = L𝒰_K` and `A'_{K,p} = L A_{K,p}` (regions `{u ∈ supp : g(u) ≤ τ}`). -/
def whiten_support : Prop :=
  ∀ (K : ℕ) (M L : Matrix (Fin K) (Fin K) ℝ), M.PosDef → Lᵀ * L = M →
    ∀ (μ : Measure (EuclideanSpace ℝ (Fin K))) (g : EuclideanSpace ℝ (Fin K) → ℝ) (τ : ℝ),
      (μ.map (mvec L)).support = mvec L '' μ.support ∧
        {w | w ∈ (μ.map (mvec L)).support ∧ g (mvec L⁻¹ w) ≤ τ} = mvec L '' {u | u ∈ μ.support ∧ g u ≤ τ}

/-- (b) Absolute continuity holds for one instance iff for the other. -/
def whiten_ac : Prop :=
  ∀ (K : ℕ) (M L : Matrix (Fin K) (Fin K) ℝ), M.PosDef → Lᵀ * L = M →
    ∀ μ : Measure (EuclideanSpace ℝ (Fin K)), μ.map (mvec L) ≪ volume ↔ μ ≪ volume

/-- (b) Convexity and compactness hold for one instance iff for the other; `L` maps interiors to interiors (so the
interior-level condition `A ⊆ int 𝒰` transfers). -/
def whiten_geom : Prop :=
  ∀ (K : ℕ) (M L : Matrix (Fin K) (Fin K) ℝ), M.PosDef → Lᵀ * L = M →
    ∀ A : Set (EuclideanSpace ℝ (Fin K)),
      (Convex ℝ (mvec L '' A) ↔ Convex ℝ A) ∧ (IsCompact (mvec L '' A) ↔ IsCompact A) ∧
        interior (mvec L '' A) = mvec L '' interior A

/-- (c) Bands: with `Q = L⁻¹ ∘ Q' ∘ L`, the band objective takes the same values over `A` and `LA` against
`e' = L⁻ᵀe` (so every supremum/infimum, i.e. every edge, coincides), and curve values coincide:
`𝔪 + ⟨e, Q(u)⟩ = 𝔪 + ⟨e', Q'(Lu)⟩`, `⟨e, Z_j⟩ = ⟨e', LZ_j⟩`. -/
def whiten_band : Prop :=
  ∀ (K : ℕ) (M L : Matrix (Fin K) (Fin K) ℝ), M.PosDef → Lᵀ * L = M →
    ∀ (Q Q' : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)), (∀ u, Q u = mvec L⁻¹ (Q' (mvec L u))) →
      (∀ (A : Set (EuclideanSpace ℝ (Fin K))) (v : EuclideanSpace ℝ (Fin K)),
        (fun u => ⟪v, Q u⟫) '' A = (fun w => ⟪mvec L⁻¹ᵀ v, Q' w⟫) '' (mvec L '' A)) ∧
      (∀ (c0 : ℝ) (e u : EuclideanSpace ℝ (Fin K)), c0 + ⟪e, Q u⟫ = c0 + ⟪mvec L⁻¹ᵀ e, Q' (mvec L u)⟫) ∧
      ∀ e z : EuclideanSpace ℝ (Fin K), ⟪e, z⟫ = ⟪mvec L⁻¹ᵀ e, mvec L z⟫

/-- (c) The gaps `δ_j(p) = min_{u∈A}[max_k s_k(u) − s_j(u)]` coincide: the gap objective has the same values over
`A` and over `LA` (whitened scores). -/
def whiten_gaps : Prop :=
  ∀ (K n : ℕ) (M L : Matrix (Fin K) (Fin K) ℝ), M.PosDef → Lᵀ * L = M →
    ∀ (f : Fin n → ℝ) (Z : Fin n → EuclideanSpace ℝ (Fin K)) (A : Set (EuclideanSpace ℝ (Fin K))) (j : Fin n),
      (fun u => (⨆ k, oosScore M f Z u k) - oosScore M f Z u j) '' A =
        (fun w => (⨆ k, oosScore 1 f (fun i => mvec L (Z i)) w k) - oosScore 1 f (fun i => mvec L (Z i)) w j) ''
          (mvec L '' A)

/-- (d) Population: an `M`-monotone `Q` pushing `μ` to `P` whitens to a Brenier map `LQL⁻¹` pushing `L#μ` to `L#P`,
and `Q = L⁻¹ ∘ Q' ∘ L` `μ`-a.e. for every Brenier map `Q'` of the whitened pair. -/
def whiten_population : Prop :=
  ∀ (K : ℕ) (M L : Matrix (Fin K) (Fin K) ℝ), M.PosDef → Lᵀ * L = M →
    ∀ (μ P : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure μ]
      (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)), IsMGradMap M μ P Q →
      IsGradMap (μ.map (mvec L)) (P.map (mvec L)) (fun w => mvec L (Q (mvec L⁻¹ w))) ∧
        (μ ≪ volume → MemLp id 2 μ → MemLp id 2 P →
          ∀ Q' : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K),
            IsGradMap (μ.map (mvec L)) (P.map (mvec L)) Q' → Q =ᵐ[μ] fun u => mvec L⁻¹ (Q' (mvec L u)))

/-- (d) Essential ranges: if `Q = L⁻¹ ∘ Q' ∘ L` `μ`-a.e., then `ℛ' = Lℛ` (supports of `Q#(μ|A)` and
`Q'#((L#μ)|LA)`), `𝒮' = L𝒮` (closed convex hulls), and the support-function values coincide,
`{⟨v,y⟩ : y ∈ ℛ} = {⟨L⁻ᵀv, y'⟩ : y' ∈ ℛ'}` (so `h^pop(v) = h'^pop(L⁻ᵀv)`). -/
def whiten_essrange : Prop :=
  ∀ (K : ℕ) (M L : Matrix (Fin K) (Fin K) ℝ), M.PosDef → Lᵀ * L = M →
    ∀ (μ : Measure (EuclideanSpace ℝ (Fin K))) (Q Q' : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
      (A : Set (EuclideanSpace ℝ (Fin K))), Measurable Q → Measurable Q' → MeasurableSet A →
      (Q =ᵐ[μ] fun u => mvec L⁻¹ (Q' (mvec L u))) →
      (((μ.map (mvec L)).restrict (mvec L '' A)).map Q').support = mvec L '' ((μ.restrict A).map Q).support ∧
        closure (convexHull ℝ (((μ.map (mvec L)).restrict (mvec L '' A)).map Q').support) =
          mvec L '' closure (convexHull ℝ ((μ.restrict A).map Q).support) ∧
        ∀ v : EuclideanSpace ℝ (Fin K), (fun y => ⟪v, y⟫) '' ((μ.restrict A).map Q).support =
          (fun y => ⟪mvec L⁻¹ᵀ v, y⟫) '' (((μ.map (mvec L)).restrict (mvec L '' A)).map Q').support

/-- (d) Subdifferentials: `{y : My ∈ ∂φ(u)} = L⁻¹ ∂(φ ∘ L⁻¹)(Lu)`, so `½M⁻¹∂χ` is single-valued at `u` iff the
whitened subdifferential is at `Lu`. -/
def whiten_subdiff : Prop :=
  ∀ (K : ℕ) (M L : Matrix (Fin K) (Fin K) ℝ), M.PosDef → Lᵀ * L = M →
    ∀ (φ : EuclideanSpace ℝ (Fin K) → EReal) (u : EuclideanSpace ℝ (Fin K)),
      {y | mvec M y ∈ TauCeti.subdifferential (innerₗ (EuclideanSpace ℝ (Fin K))) φ u} =
        mvec L⁻¹ '' TauCeti.subdifferential (innerₗ (EuclideanSpace ℝ (Fin K))) (fun w => φ (mvec L⁻¹ w)) (mvec L u)

/-! #### B `lem:app-subgradient-convergence` -/



/-- (a) `g_n → g` uniformly on compacts of `C`, `g` differentiable at `u`, `u_n → u`, `ξ_n ∈ ∂g_n(u_n)` (eventually)
⇒ `ξ_n → ∇g(u)`. -/
def subgrad_conv_point : Prop :=
  ∀ (K : ℕ) (C : Set (EuclideanSpace ℝ (Fin K))) (g : ℕ → EuclideanSpace ℝ (Fin K) → ℝ)
    (g0 : EuclideanSpace ℝ (Fin K) → ℝ) (u : EuclideanSpace ℝ (Fin K)) (us ξ : ℕ → EuclideanSpace ℝ (Fin K)),
    IsOpen C → Convex ℝ C → (∀ n, ConvexOn ℝ C (g n)) → ConvexOn ℝ C g0 →
    (∀ S ⊆ C, IsCompact S → TendstoUniformlyOn g g0 atTop S) →
    u ∈ C → DifferentiableAt ℝ g0 u → Tendsto us atTop (𝓝 u) →
    (∀ᶠ n in atTop, ξ n ∈ TauCeti.subdifferential (innerₗ (EuclideanSpace ℝ (Fin K))) (extTop C (g n)) (us n)) →
      Tendsto ξ atTop (𝓝 (gradient g0 u))

/-- (b) `g` differentiable on an open `O ⊆ C`, `S ⊆ O` compact ⇒
`sup{‖ξ − ∇g(w)‖ : w ∈ S, ξ ∈ ∂g_n(w)} → 0` (as: eventually `≤ ε`, for every `ε > 0`). -/
def subgrad_conv_unif : Prop :=
  ∀ (K : ℕ) (C : Set (EuclideanSpace ℝ (Fin K))) (g : ℕ → EuclideanSpace ℝ (Fin K) → ℝ)
    (g0 : EuclideanSpace ℝ (Fin K) → ℝ) (O S : Set (EuclideanSpace ℝ (Fin K))),
    IsOpen C → Convex ℝ C → (∀ n, ConvexOn ℝ C (g n)) → ConvexOn ℝ C g0 →
    (∀ S' ⊆ C, IsCompact S' → TendstoUniformlyOn g g0 atTop S') →
    IsOpen O → O ⊆ C → (∀ w ∈ O, DifferentiableAt ℝ g0 w) → S ⊆ O → IsCompact S →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ w ∈ S,
        ∀ ξ ∈ TauCeti.subdifferential (innerₗ (EuclideanSpace ℝ (Fin K))) (extTop C (g n)) w, ‖ξ - gradient g0 w‖ ≤ ε

/-! #### G `lem:evaluation` (flat case `M = E`, `𝒳 = L²(λ; E)`) -/

/-- Existence: a `𝓑(𝒳) ⊗ 𝓑(T)`-measurable `ev : 𝒳 × T → E` with `ev(x, ·)` a representative of `x` for every `x`. -/
def evaluation_exists : Prop :=
  ∀ (T : Type) [MeasurableSpace T] [MeasurableSpace.CountablyGenerated T] (lam : Measure T) [SigmaFinite lam]
    (E : Type) [NormedAddCommGroup E] [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E]
    [BorelSpace E] [MeasurableSpace (Lp E 2 lam)] [BorelSpace (Lp E 2 lam)],
    ∃ ev : Lp E 2 lam × T → E, Measurable ev ∧ ∀ x : Lp E 2 lam, (fun t => ev (x, t)) =ᵐ[lam] ⇑x

/-- Uniqueness: two such maps agree `Q ⊗ λ`-a.e. for every law `Q` on `𝒳`, and for `λ`-a.e. `t` the law of
`X(t) = ev(X, t)`, `X ~ Q`, does not depend on the choice. -/
def evaluation_unique : Prop :=
  ∀ (T : Type) [MeasurableSpace T] [MeasurableSpace.CountablyGenerated T] (lam : Measure T) [SigmaFinite lam]
    (E : Type) [NormedAddCommGroup E] [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E]
    [BorelSpace E] [MeasurableSpace (Lp E 2 lam)] [BorelSpace (Lp E 2 lam)]
    (ev ev' : Lp E 2 lam × T → E) (Q : Measure (Lp E 2 lam)) [IsProbabilityMeasure Q],
    Measurable ev → Measurable ev' → (∀ x : Lp E 2 lam, (fun t => ev (x, t)) =ᵐ[lam] ⇑x) →
    (∀ x : Lp E 2 lam, (fun t => ev' (x, t)) =ᵐ[lam] ⇑x) →
      ev =ᵐ[Q.prod lam] ev' ∧ ∀ᵐ t ∂lam, Q.map (fun x => ev (x, t)) = Q.map (fun x => ev' (x, t))

/-! #### G `lem:evaluation` (general complete separable metric `M`) -/

/-- Existence, for any complete separable metric space `M`, base curve `m` and `𝒳 = {D(·, m) < ∞}`: a jointly
measurable `ev : 𝒳 × T → M` with `ev(x, ·)` a representative of `x` for every `x`. -/
def evaluation_exists_metric : Prop :=
  ∀ (T : Type) [MeasurableSpace T] [MeasurableSpace.CountablyGenerated T] (lam : Measure T) [IsProbabilityMeasure lam]
    (M : Type) [MetricSpace M] [CompleteSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    (m : T →ₘ[lam] M),
    ∃ ev : XSpace lam m × T → M, Measurable ev ∧ ∀ x : XSpace lam m, (fun t => ev (x, t)) =ᵐ[lam] ⇑x.1

/-- Uniqueness, general `M`: two such maps agree `Q ⊗ λ`-a.e. for every law `Q` on `𝒳`, and for `λ`-a.e. `t` the
law of `X(t) = ev(X, t)`, `X ~ Q`, does not depend on the choice. -/
def evaluation_unique_metric : Prop :=
  ∀ (T : Type) [MeasurableSpace T] [MeasurableSpace.CountablyGenerated T] (lam : Measure T) [IsProbabilityMeasure lam]
    (M : Type) [MetricSpace M] [CompleteSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    (m : T →ₘ[lam] M) (ev ev' : XSpace lam m × T → M) (Q : Measure (XSpace lam m)) [IsProbabilityMeasure Q],
    Measurable ev → Measurable ev' → (∀ x : XSpace lam m, (fun t => ev (x, t)) =ᵐ[lam] ⇑x.1) →
    (∀ x : XSpace lam m, (fun t => ev' (x, t)) =ᵐ[lam] ⇑x.1) →
      ev =ᵐ[Q.prod lam] ev' ∧ ∀ᵐ t ∂lam, Q.map (fun x => ev (x, t)) = Q.map (fun x => ev' (x, t))

end Claims

end StatFormal.OTFD.Wave19a
