import StatFormal.Archive.OTFD.Bands.Statements
import StatFormal.Archive.OTFD.Bands2.Statements
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# FROZEN STATEMENTS — otfd wave 2: T `eq:dual` (prop:caps), T `eq:radial` (prop:directions),
# C `prop:conditional-perturbation`, B `cor:certified-band-rate` (with `prop:certified-band-weighted`),
# B `prop:vector-direction-net`, B `prop:rk-monotone-functionals`

Sources (verbatim in `lean-formalisation/inventory/extracted/otfd-T_tangent.md`, `otfd-C_conditional.md`,
`otfd-B_bands.md`; paths below are under `otfd/papers/`):
* T `prop:caps` (`T_tangent/sec_tangent_theory.tex:471-500`, label `eq:dual`), with the affine scores
  `eq:affine` (`:393-398`) and the gaps `eq:gaps` (`:464-467`).
* T `prop:directions` (`T_tangent/supp_moved.tex:917-942`, label `eq:radial`).
* C `prop:conditional-perturbation` (`C_conditional/main.tex:609-619`), with `eq:conditional-map`
  (`main.tex:393-397`), `δ_i(p|x)` and `L_i(ω,x)` of `prop:conditional-certificate` (`main.tex:538-547`);
  proof `C_conditional/supplement.tex:894-908`.
* B `prop:certified-band-weighted` (`B_bands/supplement.tex:1170-1180`) and `cor:certified-band-rate`
  (`supplement.tex:1191-1225`, proof `:1215-1225`).
* B `prop:vector-direction-net` (`B_bands/supplement.tex:3054-3100`).
* B `prop:rk-monotone-functionals` (`B_bands/supplement.tex:5429-5490`), using the event of
  `prop:rk-scenario-set` (`supplement.tex:5377-5393`, `def:rk-scenario-score` `:5356`).
Builds on the frozen kits `StatFormal/OTFD/Bands/Statements.lean` (`simplex`, `softmax`, `score`, `gap`,
`IsSimplexProj`, `mnormSq`) and `StatFormal/OTFD/Bands2/Statements.lean` (`satCapEnt`, `edgeUp`, `edgeLo`,
`curve`), imported, not copied.

Covered:
* T: `tangent_dual` (eq:dual); `tangent_caps_entropic`, `tangent_caps_quadratic` (eq:caps: every fitted `q(u)`,
  `u ∈ A`, lies in `𝒫_κ`, so `Σ q_j v_j ∈ S_A(t)`); `tangent_lead_caps` (eq:leadcaps, and `min(κ, κ')`);
  `tangent_knapsack` (the support of `S_A(t)` is attained by the greedy "fill in decreasing order" weights,
  reversing the order gives the minimum) and `tangent_knapsack_exists`.
* T: `radial_enclosure` (eq:radial), `radial_box` (eq:boxradius), `radial_min` (the smaller radius),
  `radial_circle` (`d = 2`, `N ≥ 3` equally spaced directions cover within `θ = π/N`).
* C: `cond_gap_shift`, `cond_witness_shift` (the two `2D_f` bounds), `cond_map_ent` (`R_I D_f/ε`),
  `cond_map_quad` (`|I| R_I D_f/(γ/m)`), `cond_edge_shift` (edges move by at most `E_K ×` the map bound).
* B: `weighted_slack` (prop:certified-band-weighted, both claims); `cBeta_summable` (`c_β < ∞`);
  `band_rate` (the displayed bound of cor:certified-band-rate, every `t`); `band_rate_schedule`
  (`ε_n ≲ 1/n`, `L_n = o(n^β)`, `R_n` subexponential ⇒ the bound → 0, and `ε_n log n → 0`).
* B: `direction_net` (`P_t` compact, `C_t ⊆ P_t`, eq:vector-net-radius, eq:vector-net-hausdorff, `β > 0`).
* B: `monotone_chain` (a); `max_type_bracket`, `min_type_bracket`, `window_peak_width` (b);
  `calibrated_envelope` (c, the event eq:rk-monotone-envelope) and `envelope_functionals` (c)(i),(ii) and (d)
  on that event; `mixed_sup` (d, first display).

Not covered (declared):
* T: that `q(u)` is `softmax(s/ε)` resp. the simplex projection of `s/λ` (`eq:affine`; the claims are about these
  weights); `prop:boundary`; the role of `θ` being the covering angle "of the tangent unit sphere" at every `t`
  (claims are pointwise in `t`); continuity of the center field `c` (unused); the remarks after `prop:caps`.
* C: the convex-potential / band-validity parts of `prop:conditional-certificate`; that the retained set `I_x` is
  produced by stage two (it is the index type `Fin n`, common to both queries).
* B weighted/rate: `prop:certified-band-limit` (the identity `H^∂ = max_{J_0}⟨v, Z_j⟩` and `x^{↑,∂} − 𝔪 = M_0` are
  taken as the definition of the comparison point `M_0`); the uniform-convergence sentences of
  `prop:certified-band-limit`; the `β = 1`, `ε_n = {log(en)}^{-2}` sentence ("grows like `n/log⁴n`", a description of
  the bound, not a claim about the slack) and the sentence about `ass:fixedK-oos`.
* B direction net: the computable choices `ξ_t = max g_p`, `R_t = max_j ‖E(t)Z_j‖` (they depend on
  `eq:vector-certified-support`).
* B monotone: `prop:rk-scenario-set` itself (its event enters as a hypothesis, measurable-event form); the
  "computed from caps and a sort" remark; the window-range example of (d); in (b), the last step
  `sup_W[x̄↑ − x̲↑] ≤ sup_W gap(t)` (immediate from `x̲↓ ≥ lb`, cf. Bands2 `inner_gap`).

Encodings (see card):
* `ℝ^K = Fin K → ℝ`, `⟨·,·⟩ = dotProduct`, Euclidean norm `eucl x = √(x ⬝ᵥ x)`; tangent spaces are any real
  vector space (`tangent_*`) or real inner-product space (`radial_enclosure`), `EuclideanSpace ℝ (Fin d)` where the
  paper uses coordinates (`radial_box`, `radial_circle`, `direction_net`).
* Gap lower bounds and support bounds enter as "any `δ ≤ δ_j(A)`", "any `σ ≥ sup_A`", "any `H(a) ≥ sup_S ⟨a,·⟩`"
  (covers the exact values and the paper's "any verified/upper bound"); `δ_j(A)` is the kit's `gap` (`sInf` of a
  set bounded below by `0`, no junk on nonempty `A`). `λ` is any positive real (T), `λ = γ/m` (C).
* Greedy fill = threshold form: `q ∈ 𝒫_κ` and some `τ` with `c_j > τ ⇒ q_j = κ_j`, `c_j < τ ⇒ q_j = 0`
  (sorting-free description of "fill capacities in decreasing order of the values until the total weight is one").
* Lead caps: `A ⊆ {‖u‖ ≤ ρ}` (covers the centered ball), `κ'_j = satCapEnt ε (γ_{j·}) j` (frozen Bands2 cap).
* Radial: covering within `θ` = `∀ x, ‖x‖ = 1 → ∃ a ∈ 𝒜, cos θ ≤ ⟨a, x⟩`; directions need not be unit (a
  generalisation); `𝒜` nonempty finite, the max is `⨆` over the finset; `0 ≤ θ < π/2`.
* C: `D_f = ⨅_c ⨆_i |f_i − f'_i − c|` (bounded below by `0`); `R_I` any bound `≥ ‖Z_i‖`; `L_i(ω,x)` uses the exact
  support function as `sSup` (the `σ` term cancels in `cond_witness_shift`, so its value is irrelevant there);
  `δ_i` needs `A` nonempty only.
* B weighted/rate: `c_j = c_j(t) = ⟨e(t), Z_j⟩`, the certified edge minus `𝔪(t)` is `Σ q_j c_j` for **every**
  `q ∈ 𝒫_κ` (stronger than the knapsack maximum), `κ_j = e^{−δ_j/ε}`, `J_0 = {δ_j = 0}`, `M_0(t)` with
  `IsGreatest`. `c_β = 1 + Σ_{k≥0} 2^{(k+1)(β+1)} e^{−2^k}` (paper's `k ≥ 1`, reindexed) with `cBeta_summable`.
  `R_n` any bound `≥ max_j c_j(t) − min_j c_j(t)`. Schedule: `ε_n ≤ a/n` eventually, `L_n/n^β → 0`,
  subexponential = `R_n e^{−bn} → 0` for every `b > 0`.
* B direction net: `C_t` nonempty compact convex (as in the proof), `h_C = sSup` (no junk: nonempty bounded),
  `d_H = Metric.hausdorffDist` (finite: both sets nonempty bounded).
* B monotone: edges are real functions equal (in `EReal`) to the frozen `edgeUp/edgeLo`; outer edges are any real
  functions beyond the exact edges (covers the certified ones); functionals `L : (T → ℝ) → β` into any preorder,
  "nondecreasing" = `Monotone` for the pointwise order; max/min-type functionals are `EReal`-valued `⨆/⨅` over `W`
  (no junk); `sup/inf_u L(x_u)` are `EReal` `⨆/⨅` resp. pointwise chains; "`Λ`-Lipschitz for the sup-norm" =
  `(∀ t, |x t − y t| ≤ r) → |L x − L y| ≤ Λ r`; `‖w‖_M = √(wᵀMw)`, `κ(t) = ‖M⁻¹e(t)‖_M`, `C_K` any bound on `κ`;
  "`min_{u∈A} ‖ΠX − Q̂u‖_M ≤ η̂_e`" is `∃ u ∈ A`; on `{ŝ ≥ 1}` the edges are `±∞` and the envelope is void, so the
  conclusion is stated on `{ŝ < 1}`; `Q̂`, `M` deterministic (conditionally on `𝓘₁`).
Critic notes: `calibrated_envelope` reuses the scenario event itself (the content is the event inclusion);
`tangent_dual` coincides with the certified Bands `band_dual_cert` (T restatement); `weighted_slack` bounds every
feasible `q`, hence the knapsack maximum (`tangent_knapsack`).
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
Critic notes: `tangent_dual` coincides with the certified `band_dual_cert`; in `cond_witness_shift` `σ` is an `sSup` (junk 0 if `A`
is unbounded; it cancels in the difference — do not reuse `condWitness` as a bound for unbounded `A`); `weighted_slack` takes
`M₀` as the definition of `x↑∂ − 𝔪` (the identity `H^∂ = max_{J₀}` is not proved here); `direction_net` assumes `C_t` compact and
convex (convexity is definitional in the paper, compactness asserted in its proof); `calibrated_envelope` gives a measurable
subset of probability ≥ 1−α (the envelope event's own measurability and the unconditional half are not covered).
-/

noncomputable section
open Finset Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace StatFormal.OTFD.Wave2

open StatFormal.OTFD.Bands StatFormal.OTFD.Bands2

variable {n K : ℕ}

/-! ### Shared -/

/-- Euclidean norm of a coefficient vector, `‖x‖ = √(x ⬝ᵥ x)`. -/
def eucl (x : Fin K → ℝ) : ℝ := Real.sqrt (x ⬝ᵥ x)

/-- The capped simplex `𝒫_κ = {q ∈ Δ_n : q_j ≤ κ_j}`. -/
def cappedSimplex (κ : Fin n → ℝ) : Set (Fin n → ℝ) := {q | q ∈ simplex n ∧ ∀ j, q j ≤ κ j}

/-! ### T `prop:caps` -/

/-- Entropic weights `q(u) = softmax(s(u)/ε)`. -/
def entWeights (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ) (ε : ℝ) (u : Fin K → ℝ) : Fin n → ℝ :=
  fun j => softmax (fun k => score a b k u / ε) j

/-- The relaxed tangent region `S_A(t) = {Σ_j q_j v_j(t) : q ∈ 𝒫_κ}`. -/
def tangentRegion {E : Type*} [AddCommGroup E] [Module ℝ E] (κ : Fin n → ℝ) (v : Fin n → E) : Set E :=
  (fun q => ∑ j, q j • v j) '' cappedSimplex κ

/-- Greedy (fractional-knapsack) fill: `q ∈ 𝒫_κ` and a threshold `τ` such that values above `τ` are filled to
capacity and values below `τ` get no weight. -/
def IsGreedyFill (κ c q : Fin n → ℝ) : Prop :=
  q ∈ cappedSimplex κ ∧ ∃ τ : ℝ, ∀ j, (τ < c j → q j = κ j) ∧ (c j < τ → q j = 0)

/-- `γ_{jl} = a_j − a_l + ρ ‖b_j − b_l‖`. -/
def leadGap (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ) (ρ : ℝ) (j l : Fin n) : ℝ :=
  a j - a l + ρ * eucl (b j - b l)

/-- Lead cap `κ'_j = (1 + Σ_{l≠j} e^{−γ_{jl}/ε})⁻¹`. -/
def leadCap (ε : ℝ) (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ) (ρ : ℝ) (j : Fin n) : ℝ :=
  satCapEnt ε (leadGap a b ρ j) j

/-! ### T `prop:directions` -/

/-- `R_A^c = (cos θ)⁻¹ max_{a∈𝒜} [H(a) − ⟨a, c⟩]` (`H = h_{S_A(t)}` or any upper bound). -/
def radialRadius {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (θ : ℝ) (𝒜 : Finset E)
    (H : E → ℝ) (c : E) : ℝ :=
  (Real.cos θ)⁻¹ * ⨆ a : 𝒜, (H a - ⟪(a : E), c⟫_ℝ)

/-- `R_box^c = [Σ_a max{|ℓ_a − c_a|, |r_a − c_a|}²]^{1/2}`. -/
def boxRadius {d : ℕ} (ℓ r : Fin d → ℝ) (c : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Real.sqrt (∑ a, (max |ℓ a - c a| |r a - c a|) ^ 2)

/-- The `N` equally spaced unit directions `(cos 2πk/N, sin 2πk/N)`, `k < N`. -/
def circleDirs (N : ℕ) : Finset (EuclideanSpace ℝ (Fin 2)) :=
  (Finset.range N).image fun k : ℕ =>
    !₂[Real.cos (2 * Real.pi * k / N), Real.sin (2 * Real.pi * k / N)]

/-! ### C `prop:conditional-perturbation` -/

/-- Intercepts `a_i(x) = f_i(x) − ‖Z_i‖²`. -/
def condA (f : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) : Fin n → ℝ := fun i => f i - Z i ⬝ᵥ Z i

/-- Slopes `2 Z_i` (query-free). -/
def condB (Z : Fin n → Fin K → ℝ) : Fin n → Fin K → ℝ := fun i => (2 : ℝ) • Z i

/-- `δ_i(p | x) = min_{u∈A} max_k [s_k(u|x) − s_i(u|x)]`. -/
def condGap (f : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) (A : Set (Fin K → ℝ)) (i : Fin n) : ℝ :=
  gap (condA f Z) (condB Z) A i

/-- `L_i(ω, x) = Σ_k ω_k a_k(x) − a_i(x) − σ_A(2Z_i − 2Σ_k ω_k Z_k)`. -/
def condWitness (f : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) (A : Set (Fin K → ℝ)) (ω : Fin n → ℝ)
    (i : Fin n) : ℝ :=
  ∑ k, ω k * condA f Z k - condA f Z i -
    sSup ((fun u => (condB Z i - ∑ k, ω k • condB Z k) ⬝ᵥ u) '' A)

/-- `D_f = inf_c ‖f − f' − c 1‖_∞`. -/
def potOsc (f f' : Fin n → ℝ) : ℝ := ⨅ c : ℝ, ⨆ i, |f i - f' i - c|

/-- Entropic conditional map `T_x(u) = Σ_i softmax_i(s(u|x)/ε) Z_i`. -/
def condMapEnt (ε : ℝ) (f : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) (u : Fin K → ℝ) : Fin K → ℝ :=
  ∑ i, entWeights (condA f Z) (condB Z) ε u i • Z i

/-! ### B `cor:certified-band-rate` -/

/-- `c_β = 1 + Σ_{k≥1} 2^{k(β+1)} e^{−2^{k−1}}`, written with `k ↦ k + 1`. -/
def cBeta (β : ℝ) : ℝ :=
  1 + ∑' k : ℕ, (2 : ℝ) ^ (((k : ℝ) + 1) * (β + 1)) * Real.exp (-(2 : ℝ) ^ k)

/-! ### B `prop:vector-direction-net` -/

/-- Support function `h_C(v) = sup_{z∈C} ⟨v, z⟩`. -/
def supportFn {d : ℕ} (C : Set (EuclideanSpace ℝ (Fin d))) (v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  sSup ((fun z => ⟪v, z⟫_ℝ) '' C)

/-- `P_t = ⋂_{v∈V} {z : ⟨v, z⟩ ≤ h̃(v)}`. -/
def netPolytope {d : ℕ} (V : Finset (EuclideanSpace ℝ (Fin d))) (h : EuclideanSpace ℝ (Fin d) → ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {z | ∀ v ∈ V, ⟪v, z⟫_ℝ ≤ h v}

/-! ### B `prop:rk-monotone-functionals` -/

/-- Max-type functional `L(x) = sup_{t∈W} φ_t(x(t))` (in `EReal`). -/
def maxFun {T : Type} (W : Set T) (φ : T → ℝ → ℝ) (x : T → ℝ) : EReal :=
  ⨆ t ∈ W, ((φ t (x t) : ℝ) : EReal)

/-- Min-type functional `inf_{t∈W} φ_t(x(t))` (in `EReal`). -/
def minFun {T : Type} (W : Set T) (φ : T → ℝ → ℝ) (x : T → ℝ) : EReal :=
  ⨅ t ∈ W, ((φ t (x t) : ℝ) : EReal)

/-- `‖w‖_M = √(wᵀ M w)`. -/
def mnorm (M : Matrix (Fin K) (Fin K) ℝ) (w : Fin K → ℝ) : ℝ := Real.sqrt (mnormSq M w)

/-- `κ(t) = ‖M⁻¹ e(t)‖_M`. -/
def kappaM (M : Matrix (Fin K) (Fin K) ℝ) (v : Fin K → ℝ) : ℝ := mnorm M (M⁻¹ *ᵥ v)

namespace Claims

/-! ### T `prop:caps` (`eq:dual`, `eq:caps`, `eq:polytope`, `eq:leadcaps`, knapsack) -/

/-- `eq:dual`: for every `w ∈ Δ_n`, `δ_j(A) ≥ Σ_l w_l a_l − a_j − σ_A(b_j − Σ_l w_l b_l)` (any `σ ≥ sup_A`). -/
def tangent_dual : Prop :=
  ∀ (n K : ℕ) (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ) (A : Set (Fin K → ℝ)) (j : Fin n)
    (w : Fin n → ℝ) (σA : ℝ),
    A.Nonempty → w ∈ simplex n →
    (∀ u ∈ A, (b j - ∑ l, w l • b l) ⬝ᵥ u ≤ σA) →
      ∑ l, w l * a l - a j - σA ≤ gap a b A j

/-- Entropic caps `κ_j = e^{−δ̲_j/ε}`: for `u ∈ A` and verified `δ̲_j ≤ δ_j(A)`, `q(u) ∈ 𝒫_κ` and
`Σ_j q_j(u) v_j ∈ S_A(t)`. -/
def tangent_caps_entropic : Prop :=
  ∀ (n K : ℕ) (E : Type) [AddCommGroup E] [Module ℝ E] (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ)
    (A : Set (Fin K → ℝ)) (ε : ℝ) (δlow : Fin n → ℝ) (v : Fin n → E) (u : Fin K → ℝ),
    0 < n → 0 < ε → u ∈ A → (∀ j, δlow j ≤ gap a b A j) →
      entWeights a b ε u ∈ cappedSimplex (fun j => Real.exp (-δlow j / ε)) ∧
      ∑ j, entWeights a b ε u j • v j ∈ tangentRegion (fun j => Real.exp (-δlow j / ε)) v

/-- Quadratic caps `κ_j = (1 − δ̲_j/λ)_+`, `q(u)` the simplex projection of `s(u)/λ`. -/
def tangent_caps_quadratic : Prop :=
  ∀ (n K : ℕ) (E : Type) [AddCommGroup E] [Module ℝ E] (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ)
    (A : Set (Fin K → ℝ)) (lam : ℝ) (δlow : Fin n → ℝ) (v : Fin n → E) (u : Fin K → ℝ)
    (q : Fin n → ℝ),
    0 < lam → u ∈ A → (∀ j, δlow j ≤ gap a b A j) →
    IsSimplexProj (fun k => score a b k u / lam) q →
      q ∈ cappedSimplex (fun j => max 0 (1 - δlow j / lam)) ∧
      ∑ j, q j • v j ∈ tangentRegion (fun j => max 0 (1 - δlow j / lam)) v

/-- `eq:leadcaps`: on `A ⊆ {‖u‖ ≤ ρ}`, the lead caps are valid and `min(κ_j, κ'_j)` may be used. -/
def tangent_lead_caps : Prop :=
  ∀ (n K : ℕ) (E : Type) [AddCommGroup E] [Module ℝ E] (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ)
    (A : Set (Fin K → ℝ)) (ε ρ : ℝ) (δlow : Fin n → ℝ) (v : Fin n → E) (u : Fin K → ℝ),
    0 < n → 0 < ε → (∀ u' ∈ A, eucl u' ≤ ρ) → u ∈ A → (∀ j, δlow j ≤ gap a b A j) →
      (∀ j, entWeights a b ε u j ≤ leadCap ε a b ρ j) ∧
      entWeights a b ε u ∈
        cappedSimplex (fun j => min (Real.exp (-δlow j / ε)) (leadCap ε a b ρ j)) ∧
      ∑ j, entWeights a b ε u j • v j ∈
        tangentRegion (fun j => min (Real.exp (-δlow j / ε)) (leadCap ε a b ρ j)) v

/-- Knapsack: a greedy fill attains `h_{S_A(t)}(a) = max_{q∈𝒫_κ} Σ_j q_j c_j` (`c_j = ⟨a, v_j(t)⟩`); the
reversed order attains the minimum (lower edges). -/
def tangent_knapsack : Prop :=
  ∀ (n : ℕ) (κ c q : Fin n → ℝ),
    (IsGreedyFill κ c q →
      IsGreatest ((fun q' => ∑ j, q' j * c j) '' cappedSimplex κ) (∑ j, q j * c j)) ∧
    (IsGreedyFill κ (-c) q →
      IsLeast ((fun q' => ∑ j, q' j * c j) '' cappedSimplex κ) (∑ j, q j * c j))

/-- A greedy fill exists whenever `𝒫_κ` is nonempty (e.g. it contains the actual weights). -/
def tangent_knapsack_exists : Prop :=
  ∀ (n : ℕ) (κ c : Fin n → ℝ), (cappedSimplex κ).Nonempty → ∃ q, IsGreedyFill κ c q

/-! ### T `prop:directions` (`eq:radial`, `eq:boxradius`) -/

/-- `eq:radial`: every `v ∈ S` satisfies `‖v − c‖ ≤ R_A^c`. -/
def radial_enclosure : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (S : Set E) (𝒜 : Finset E) (θ : ℝ)
    (H : E → ℝ) (c : E),
    𝒜.Nonempty → 0 ≤ θ → θ < Real.pi / 2 →
    (∀ x : E, ‖x‖ = 1 → ∃ a ∈ 𝒜, Real.cos θ ≤ ⟪a, x⟫_ℝ) →
    (∀ a ∈ 𝒜, ∀ v ∈ S, ⟪a, v⟫_ℝ ≤ H a) →
      ∀ v ∈ S, ‖v - c‖ ≤ radialRadius θ 𝒜 H c

/-- `eq:boxradius`: with component edges `ℓ_a ≤ v_a ≤ r_a` on `S`, `‖v − c‖ ≤ R_box^c`. -/
def radial_box : Prop :=
  ∀ (d : ℕ) (S : Set (EuclideanSpace ℝ (Fin d))) (ℓ r : Fin d → ℝ) (c : EuclideanSpace ℝ (Fin d)),
    (∀ v ∈ S, ∀ a, ℓ a ≤ v a ∧ v a ≤ r a) → ∀ v ∈ S, ‖v - c‖ ≤ boxRadius ℓ r c

/-- The smaller of the two radii can be retained. -/
def radial_min : Prop :=
  ∀ (d : ℕ) (S : Set (EuclideanSpace ℝ (Fin d))) (𝒜 : Finset (EuclideanSpace ℝ (Fin d))) (θ : ℝ)
    (H : EuclideanSpace ℝ (Fin d) → ℝ) (ℓ r : Fin d → ℝ) (c : EuclideanSpace ℝ (Fin d)),
    𝒜.Nonempty → 0 ≤ θ → θ < Real.pi / 2 →
    (∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ = 1 → ∃ a ∈ 𝒜, Real.cos θ ≤ ⟪a, x⟫_ℝ) →
    (∀ a ∈ 𝒜, ∀ v ∈ S, ⟪a, v⟫_ℝ ≤ H a) → (∀ v ∈ S, ∀ a, ℓ a ≤ v a ∧ v a ≤ r a) →
      ∀ v ∈ S, ‖v - c‖ ≤ min (radialRadius θ 𝒜 H c) (boxRadius ℓ r c)

/-- `d = 2`: `N ≥ 3` equally spaced unit directions cover the circle within `θ = π/N`, and `0 ≤ π/N < π/2`. -/
def radial_circle : Prop :=
  ∀ N : ℕ, 3 ≤ N →
    0 ≤ Real.pi / N ∧ Real.pi / N < Real.pi / 2 ∧ (circleDirs N).Nonempty ∧
    (∀ a ∈ circleDirs N, ‖a‖ = 1) ∧
    ∀ x : EuclideanSpace ℝ (Fin 2), ‖x‖ = 1 → ∃ a ∈ circleDirs N, Real.cos (Real.pi / N) ≤ ⟪a, x⟫_ℝ

/-! ### C `prop:conditional-perturbation` -/

/-- `|δ_i(p|x) − δ_i(p|x')| ≤ 2 D_f` (same retained set `Fin n`, any nonempty region). -/
def cond_gap_shift : Prop :=
  ∀ (n K : ℕ) (f f' : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) (A : Set (Fin K → ℝ)) (i : Fin n),
    A.Nonempty → |condGap f Z A i - condGap f' Z A i| ≤ 2 * potOsc f f'

/-- `|L_i(ω,x) − L_i(ω,x')| ≤ 2 D_f` for every `ω ∈ Δ`. -/
def cond_witness_shift : Prop :=
  ∀ (n K : ℕ) (f f' : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) (A : Set (Fin K → ℝ)) (ω : Fin n → ℝ)
    (i : Fin n),
    ω ∈ simplex n → |condWitness f Z A ω i - condWitness f' Z A ω i| ≤ 2 * potOsc f f'

/-- Entropic: uniformly in `u`, `‖T_x(u) − T_{x'}(u)‖ ≤ R_I D_f / ε`. -/
def cond_map_ent : Prop :=
  ∀ (n K : ℕ) (ε R : ℝ) (f f' : Fin n → ℝ) (Z : Fin n → Fin K → ℝ),
    0 < ε → (∀ i, eucl (Z i) ≤ R) →
      ∀ u, eucl (condMapEnt ε f Z u - condMapEnt ε f' Z u) ≤ R * potOsc f f' / ε

/-- Quadratic: with `q, q'` the simplex projections of `s(u|x)/λ`, `s(u|x')/λ`, `λ = γ/m`,
`‖Σ_i q_i Z_i − Σ_i q'_i Z_i‖ ≤ |I| R_I D_f / λ`. -/
def cond_map_quad : Prop :=
  ∀ (n K m : ℕ) (γ R : ℝ) (f f' : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) (u : Fin K → ℝ)
    (q q' : Fin n → ℝ),
    0 < γ → 0 < m → (∀ i, eucl (Z i) ≤ R) →
    IsSimplexProj (fun k => score (condA f Z) (condB Z) k u / (γ / m)) q →
    IsSimplexProj (fun k => score (condA f' Z) (condB Z) k u / (γ / m)) q' →
      eucl (∑ i, q i • Z i - ∑ i, q' i • Z i) ≤ n * R * potOsc f f' / (γ / m)

/-- Band edges move by at most `E_K` times a uniform map bound. -/
def cond_edge_shift : Prop :=
  ∀ (K : ℕ) (T T' : (Fin K → ℝ) → Fin K → ℝ) (A : Set (Fin K → ℝ)) (mo B E : ℝ) (v : Fin K → ℝ),
    (∀ u, eucl (T u - T' u) ≤ B) → eucl v ≤ E →
      edgeUp T A mo v ≤ edgeUp T' A mo v + ((E * B : ℝ) : EReal) ∧
      edgeUp T' A mo v ≤ edgeUp T A mo v + ((E * B : ℝ) : EReal) ∧
      edgeLo T A mo v ≤ edgeLo T' A mo v + ((E * B : ℝ) : EReal) ∧
      edgeLo T' A mo v ≤ edgeLo T A mo v + ((E * B : ℝ) : EReal)

/-! ### B `prop:certified-band-weighted`, `cor:certified-band-rate` -/

/-- `prop:certified-band-weighted`: for every `q` in the capped simplex (`κ_j = e^{−δ_j/ε}`),
`Σ q_j c_j − M_0 ≤ min{Σ_{j∉J_0} κ_j Δ_j, max_j c_j − M_0}`, and this never exceeds
`min{1, Σ_{j∉J_0} κ_j} (max_j c_j − M_0)`. -/
def weighted_slack : Prop :=
  ∀ (n : ℕ) (c δ : Fin n → ℝ) (ε M0 : ℝ),
    0 < ε → (∀ j, 0 ≤ δ j) → IsGreatest (c '' {j | δ j = 0}) M0 →
      (∀ q ∈ cappedSimplex (fun j => Real.exp (-δ j / ε)),
        ∑ j, q j * c j - M0 ≤
          min (∑ j ∈ univ.filter (fun j => δ j ≠ 0), Real.exp (-δ j / ε) * max 0 (c j - M0))
            ((⨆ j, c j) - M0)) ∧
      min (∑ j ∈ univ.filter (fun j => δ j ≠ 0), Real.exp (-δ j / ε) * max 0 (c j - M0))
          ((⨆ j, c j) - M0) ≤
        min 1 (∑ j ∈ univ.filter (fun j => δ j ≠ 0), Real.exp (-δ j / ε)) * ((⨆ j, c j) - M0)

/-- `c_β < ∞`. -/
def cBeta_summable : Prop :=
  ∀ β : ℝ, Summable fun k : ℕ => (2 : ℝ) ^ (((k : ℝ) + 1) * (β + 1)) * Real.exp (-(2 : ℝ) ^ k)

/-- `cor:certified-band-rate`: under (M1), (M2), for every `t` the slack is at most
`c_β C L n ε^{β+1} + n R e^{−x_0/ε}`. -/
def band_rate : Prop :=
  ∀ (n : ℕ) (T : Type) (c : T → Fin n → ℝ) (δ : Fin n → ℝ) (M0 : T → ℝ) (ε L C x0 β R : ℝ),
    0 < ε → 0 < L → 0 < C → 0 < x0 → 0 < β → (∀ j, 0 ≤ δ j) →
    (∀ t, IsGreatest (c t '' {j | δ j = 0}) (M0 t)) →
    (∀ t, (⨆ j, c t j) - (⨅ j, c t j) ≤ R) →
    (∀ t j, 0 < δ j → δ j ≤ x0 → max 0 (c t j - M0 t) ≤ L * δ j) →
    (∀ x : ℝ, 0 < x → x ≤ x0 →
      ((univ.filter (fun j => 0 < δ j ∧ δ j ≤ x)).card : ℝ) ≤ C * n * x ^ β) →
      ∀ t, ∀ q ∈ cappedSimplex (fun j => Real.exp (-δ j / ε)),
        ∑ j, q j * c t j - M0 t ≤
          cBeta β * C * L * n * ε ^ (β + 1) + n * R * Real.exp (-x0 / ε)

/-- Schedule: `ε_n ≤ a/n` eventually, `L_n = o(n^β)`, `R_n` subexponential ⇒ the bound of `band_rate`
tends to `0`; and `ε_n log n → 0`. -/
def band_rate_schedule : Prop :=
  ∀ (β C x0 a : ℝ) (ε L R : ℕ → ℝ),
    0 < β → 0 < x0 → 0 < a → (∀ k, 0 < ε k) → (∀ᶠ k in atTop, ε k ≤ a / k) →
    Tendsto (fun k => L k / (k : ℝ) ^ β) atTop (𝓝 0) →
    (∀ b : ℝ, 0 < b → Tendsto (fun k => R k * Real.exp (-b * k)) atTop (𝓝 0)) →
      Tendsto (fun k => cBeta β * C * L k * k * ε k ^ (β + 1) + k * R k * Real.exp (-x0 / ε k))
        atTop (𝓝 0) ∧
      Tendsto (fun k => ε k * Real.log k) atTop (𝓝 0)

/-! ### B `prop:vector-direction-net` -/

/-- `P_t` is compact, contains `C_t`, lies in `B̄(0, (R+ξ)/β)`, and `d_H(P_t, C_t) ≤ ξ + η(R + (R+ξ)/β)`,
`β = 1 − η²/2 > 0`. -/
def direction_net : Prop :=
  ∀ (d : ℕ) (C : Set (EuclideanSpace ℝ (Fin d))) (V : Finset (EuclideanSpace ℝ (Fin d)))
    (R η ξ : ℝ) (ht : EuclideanSpace ℝ (Fin d) → ℝ),
    C.Nonempty → IsCompact C → Convex ℝ C → (∀ z ∈ C, ‖z‖ ≤ R) →
    (∀ v ∈ V, ‖v‖ = 1) → (∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ = 1 → ∃ v ∈ V, ‖x - v‖ ≤ η) →
    0 ≤ η → η < Real.sqrt 2 → 0 ≤ ξ →
    (∀ v ∈ V, supportFn C v ≤ ht v ∧ ht v ≤ supportFn C v + ξ) →
      0 < 1 - η ^ 2 / 2 ∧ IsCompact (netPolytope V ht) ∧ C ⊆ netPolytope V ht ∧
      netPolytope V ht ⊆ Metric.closedBall 0 ((R + ξ) / (1 - η ^ 2 / 2)) ∧
      Metric.hausdorffDist (netPolytope V ht) C ≤ ξ + η * (R + (R + ξ) / (1 - η ^ 2 / 2))

/-! ### B `prop:rk-monotone-functionals` -/

/-- (a) Deterministic chain at every level: `x̄↓ ≤ x̂↓ ≤ x_u ≤ x̂↑ ≤ x̄↑` and its image under every
nondecreasing `L`. -/
def monotone_chain : Prop :=
  ∀ (K : ℕ) (T : Type) (Q : (Fin K → ℝ) → Fin K → ℝ) (A : Set (Fin K → ℝ)) (mo : T → ℝ)
    (e : T → Fin K → ℝ) (uhat lhat ubar lbar : T → ℝ),
    (∀ t, (uhat t : EReal) = edgeUp Q A (mo t) (e t)) →
    (∀ t, (lhat t : EReal) = edgeLo Q A (mo t) (e t)) → uhat ≤ ubar → lbar ≤ lhat →
      ∀ u ∈ A,
        (lbar ≤ lhat ∧ lhat ≤ curve mo e (Q u) ∧ curve mo e (Q u) ≤ uhat ∧ uhat ≤ ubar) ∧
        ∀ (β : Type) [Preorder β] (L : (T → ℝ) → β), Monotone L →
          L lbar ≤ L lhat ∧ L lhat ≤ L (curve mo e (Q u)) ∧ L (curve mo e (Q u)) ≤ L uhat ∧
          L uhat ≤ L ubar

/-- (b) Max-type functionals: `sup_{u∈A} L(x_u) = L(x̂↑)`, bracketed by the inner edge (`F ⊆ A`) and the
outer edge. -/
def max_type_bracket : Prop :=
  ∀ (K : ℕ) (T : Type) (Q : (Fin K → ℝ) → Fin K → ℝ) (A F : Set (Fin K → ℝ)) (mo : T → ℝ)
    (e : T → Fin K → ℝ) (uhat uin ubar : T → ℝ) (W : Set T) (φ : T → ℝ → ℝ),
    IsCompact A → Continuous Q → F ⊆ A → W.Nonempty → (∀ t, Monotone (φ t)) →
    (∀ t, (uhat t : EReal) = edgeUp Q A (mo t) (e t)) →
    (∀ t, (uin t : EReal) = edgeUp Q F (mo t) (e t)) → uhat ≤ ubar →
      (⨆ u ∈ A, maxFun W φ (curve mo e (Q u))) = maxFun W φ uhat ∧
      maxFun W φ uin ≤ (⨆ u ∈ A, maxFun W φ (curve mo e (Q u))) ∧
      (⨆ u ∈ A, maxFun W φ (curve mo e (Q u))) ≤ maxFun W φ ubar

/-- (b) symmetric: `inf_u inf_{t∈W} φ_t(x_u(t)) = inf_{t∈W} φ_t(x̂↓(t))`, bracketed by the certified and
the inner lower edges. -/
def min_type_bracket : Prop :=
  ∀ (K : ℕ) (T : Type) (Q : (Fin K → ℝ) → Fin K → ℝ) (A F : Set (Fin K → ℝ)) (mo : T → ℝ)
    (e : T → Fin K → ℝ) (lhat lin lbar : T → ℝ) (W : Set T) (φ : T → ℝ → ℝ),
    IsCompact A → Continuous Q → F ⊆ A → W.Nonempty → (∀ t, Monotone (φ t)) →
    (∀ t, (lhat t : EReal) = edgeLo Q A (mo t) (e t)) →
    (∀ t, (lin t : EReal) = edgeLo Q F (mo t) (e t)) → lbar ≤ lhat →
      (⨅ u ∈ A, minFun W φ (curve mo e (Q u))) = minFun W φ lhat ∧
      minFun W φ lbar ≤ (⨅ u ∈ A, minFun W φ (curve mo e (Q u))) ∧
      (⨅ u ∈ A, minFun W φ (curve mo e (Q u))) ≤ minFun W φ lin

/-- (b) window peak: the bracket width is at most `sup_{t∈W}[x̄↑(t) − x̲↑(t)]` (any `G` bounding it). -/
def window_peak_width : Prop :=
  ∀ (T : Type) (W : Set T) (ubar uin : T → ℝ) (G : ℝ),
    (∀ t ∈ W, ubar t - uin t ≤ G) →
      maxFun W (fun _ => id) ubar ≤ maxFun W (fun _ => id) uin + (G : EReal)

/-- (c) Calibrated envelope: on the scenario-set event (probability `≥ 1 − α`, measurable),
`x̄↓ − η̂_r − κ η̂_e ≤ X_{n+1} ≤ x̄↑ + η̂_r + κ η̂_e` on `𝒯` (stated on `{ŝ < 1}`; void otherwise). -/
def calibrated_envelope : Prop :=
  ∀ (K : ℕ) (T Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (Q : (Fin K → ℝ) → Fin K → ℝ)
    (M : Matrix (Fin K) (Fin K) ℝ) (mo : T → ℝ) (e : T → Fin K → ℝ) (X : Ω → T → ℝ)
    (PiX : Ω → Fin K → ℝ) (A : Ω → Set (Fin K → ℝ)) (shat ηe ηr : Ω → ℝ) (ubar lbar : Ω → T → ℝ)
    (α : ℝ),
    M.PosDef →
    (∀ ω, shat ω < 1 → ∀ t, edgeUp Q (A ω) (mo t) (e t) ≤ (ubar ω t : EReal) ∧
      (lbar ω t : EReal) ≤ edgeLo Q (A ω) (mo t) (e t)) →
    (∃ S : Set Ω, MeasurableSet S ∧ ENNReal.ofReal (1 - α) ≤ P S ∧
      S ⊆ {ω | shat ω < 1 → (∃ u ∈ A ω, mnorm M (PiX ω - Q u) ≤ ηe ω) ∧
        ∀ t, |X ω t - curve mo e (PiX ω) t| ≤ ηr ω}) →
    ∃ S : Set Ω, MeasurableSet S ∧ ENNReal.ofReal (1 - α) ≤ P S ∧
      S ⊆ {ω | shat ω < 1 → ∀ t,
        lbar ω t - ηr ω - kappaM M (e t) * ηe ω ≤ X ω t ∧
        X ω t ≤ ubar ω t + ηr ω + kappaM M (e t) * ηe ω}

/-- (c)(i), (c)(ii) and (d) on the envelope event: monotone, antitone, Lipschitz-monotone and mixed
functionals. -/
def envelope_functionals : Prop :=
  ∀ (T : Type) (X lbar ubar κ : T → ℝ) (ηr ηe CK : ℝ),
    0 ≤ ηr → 0 ≤ ηe → (∀ t, 0 ≤ κ t ∧ κ t ≤ CK) →
    (∀ t, lbar t - ηr - κ t * ηe ≤ X t ∧ X t ≤ ubar t + ηr + κ t * ηe) →
      (∀ (β : Type) [Preorder β] (L : (T → ℝ) → β), Monotone L →
        L (fun t => lbar t - ηr - κ t * ηe) ≤ L X ∧ L X ≤ L (fun t => ubar t + ηr + κ t * ηe)) ∧
      (∀ (β : Type) [Preorder β] (L : (T → ℝ) → β), Antitone L →
        L (fun t => ubar t + ηr + κ t * ηe) ≤ L X ∧ L X ≤ L (fun t => lbar t - ηr - κ t * ηe)) ∧
      (∀ (L : (T → ℝ) → ℝ) (Λ : ℝ), Monotone L →
        (∀ x y : T → ℝ, ∀ r : ℝ, (∀ t, |x t - y t| ≤ r) → |L x - L y| ≤ Λ * r) →
          L lbar - Λ * (ηr + CK * ηe) ≤ L X ∧ L X ≤ L ubar + Λ * (ηr + CK * ηe)) ∧
      (∀ (β : Type) [Preorder β] (Ψ : (T → ℝ) → (T → ℝ) → β),
        (∀ y, Monotone fun x => Ψ x y) → (∀ x, Antitone (Ψ x)) →
          Ψ (fun t => lbar t - ηr - κ t * ηe) (fun t => ubar t + ηr + κ t * ηe) ≤ Ψ X X ∧
          Ψ X X ≤ Ψ (fun t => ubar t + ηr + κ t * ηe) (fun t => lbar t - ηr - κ t * ηe))

/-- (d) first display: `sup_{u∈A} Ψ(x_u, x_u) ≤ Ψ(x̄↑, x̄↓)`. -/
def mixed_sup : Prop :=
  ∀ (K : ℕ) (T : Type) (Q : (Fin K → ℝ) → Fin K → ℝ) (A : Set (Fin K → ℝ)) (mo : T → ℝ)
    (e : T → Fin K → ℝ) (ubar lbar : T → ℝ) (β : Type) [Preorder β]
    (Ψ : (T → ℝ) → (T → ℝ) → β),
    (∀ t, edgeUp Q A (mo t) (e t) ≤ (ubar t : EReal)) →
    (∀ t, (lbar t : EReal) ≤ edgeLo Q A (mo t) (e t)) →
    (∀ y, Monotone fun x => Ψ x y) → (∀ x, Antitone (Ψ x)) →
      ∀ u ∈ A, Ψ (curve mo e (Q u)) (curve mo e (Q u)) ≤ Ψ ubar lbar

end Claims
end StatFormal.OTFD.Wave2
