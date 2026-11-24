import StatFormal.Archive.OTFD.Wave7a.Statements
import StatFormal.Archive.OTFD.Wave8b.Statements
import StatFormal.Archive.OTFD.Ranks.Statements
import StatFormal.Archive.Wave4b.Statements
import StatFormal.Archive.Wave11a.Statements
import TauCeti.MeasureTheory.OptimalTransport.Coupling
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic

/-!
# FROZEN STATEMENTS — wave 16b (QUEUE rows 159–166): otfd C `lem:supp-small-cells`, C `cor:net-inner-band-neural`,
# T `eq:dualmap` (`lem:mapcost`); robust equality paper2 `prop:band`; A `thm:sample-split`, A `prop:rate-decomp`,
# A `prop:emp-bijective`, A `prop:app-entropic`

Sources (verbatim in `lean-formalisation/inventory/extracted/otfd-{C_conditional,T_tangent,A_sieves}.md`,
`robust-equality-paper2.md`; current text after the 2026-10-13/14 corrections; paths under `research-lines/`):
* C `lem:supp-small-cells` (`otfd/papers/C_conditional/supplement.tex:1911-1916`, proof `:1918-1926`).
* C `cor:net-inner-band-neural` (`otfd/papers/C_conditional/supplement.tex:1605-1621`, proof `:1657-1669`), with
  `prop:net-inner-band` (`:1581-1603`, proof `:1630-1655`; not certified elsewhere, so its deterministic part is stated
  here) and the setting of `thm:neural-band-consistency` (frozen Wave 7a).
* T `lem:mapcost` / `eq:dualmap` (`otfd/papers/T_tangent/supp_moved.tex:107-118`, proof `T_tangent/app_proofs.tex:347-352`;
  the hidden hypotheses as spelled out in `lem:mapcost-mult`, `supp_moved.tex:121-140`, proof `app_proofs.tex:356-370`).
* paper2 `prop:band` (`robust-equality-outcomes-under-distribution-shift/paper2/main.tex:557-563`, proof
  `paper2/app_proofs.tex:201-207`), with `eq:BN`, `eq:T` (`main.tex:222-250`) and the companion paper's
  `prop:cs-compose` (frozen Wave 11a).
* A `thm:sample-split` (`otfd/papers/A_sieves/supplement.tex:286-293`, proof `:699-703`), with `thm:fixedK-df`.
* A `prop:rate-decomp` (`A_sieves/supplement.tex:2352-2404`, proof `:2787-2860`).
* A `prop:emp-bijective` (`A_sieves/supplement.tex:2992-3002`, proof `:3041-3102`), with `ass:app-conditioning`
  (`:2966-2990`).
* A `prop:app-entropic` (`A_sieves/supplement.tex:3299-3321`, proof `:3323-3391`), with `eq:app-entropic-program`,
  `eq:app-entropic-barycenter` (`:3282-3297`).
Reuses, imported, not copied: frozen `OTFD/Wave7a/Statements.lean` (`NeuralSetting`, `nnSup`, `popSup`, `edgeUpE`,
`edgeLoE`, `EClose`, `risk`, `MonoOn`), `OTFD/Wave8b/Statements.lean` (`bregD`, `IsOptAssign`, `IsEntPlan`, `entBary`),
`OTFD/Wave6b/Statements.lean` (`empMeasure`), `OTFD/Ranks/Statements.lean` (`IsMin`, `UniqueMin`),
`Wave4b/Statements.lean` (`InBall`, `sqrtT`, `nominal`, `RefClass`), `Wave11a/Statements.lean` (`freeClass`); Tau Ceti's
`IsCoupling` and `wassersteinEDist`. No `StatFormal/Foundations` file is imported by this draft (the route
`RouteBand.lean` imports `Foundations/Tax/Tax.lean`).

Covered:
* `lem:supp-small-cells`: `small_cells` (some level `ℓ` has every cube of measure `≤ η`), `dyadic_partition` (the cubes
  are a countable Borel partition).
* `cor:net-inner-band-neural`: `net_inner_deficit` (`prop:net-inner-band`(i)–(ii) and its deficit sentence:
  the net band lies inside the band of `T`, deficit `≤ E_K(w + η)` with `w ≥ ω_S(h)`, `η ≥ sup_S‖T − Q‖`),
  `net_inner_two_sided` ((iv) and the two-sided display under the support condition); `net_band_neural_ae`,
  `net_band_neural_prob` (the deficit tends to `0` a.s., resp. in probability, uniformly in `t` and `0 < p ≤ 1 − δ`),
  `net_band_neural_two_sided_ae`, `net_band_neural_two_sided_prob` (two-sided convergence under the support condition),
  `net_band_neural_rate` (the displayed rate `E_K{Lh + C_{K,ρ}L^{K/(K+2)}𝓡^{1/(K+2)}}`, every `h ≥ 0`).
* `eq:dualmap`: `dualmap` (`2δ/β`), `dualmap_one_sided` (`δ/β`), each with `π₁`-integrability of `‖v − Q₀u‖²`.
* `prop:band`: `band` (the two-sided band on `E`, every bounded measurable rule, all multipliers), `band_selected`
  ("hence": a rule and multipliers selected on the same data, measurable-event convention), `band_deploy` (free end with a
  declared `W₂` budget, via `prop:cs-compose`).
* `thm:sample-split`: `sample_split` (`P(W ∈ B, σ̂ = π) = P(W ∈ B)/n!`), `sample_split_ranks` (the rank vector has, given
  `𝓘₀`, the law of `u_W ∘ π` with `π` uniform).
* `prop:rate-decomp`: `rate_decomp` (`eq:app-rate-decomp`), `rate_decomp_local` (`eq:app-rate-decomp-local`).
* `prop:emp-bijective`: `bijective_two_sided_core` (Steps 1–2 for one realisation), `emp_bijective_sq` (the Step 2
  display), `emp_bijective` (the displayed bound on `Δ^{emp,(n)}_n`). Extends the certified Wave 8b
  `emp_bijective_weak`.
* `prop:app-entropic`: `entropic_two_sided_core`, `app_entropic` (`eq:app-entropic-projected-bound`),
  `app_entropic_hilbert` (`eq:app-entropic-hilbert-bound`). Extends the certified Wave 8b `app_entropic_weak`.

Not covered (declared):
* `cor:net-inner-band-neural`: "the coverage conclusions of `cor:conditional-test-coverage` hold for it" (a pointer: that
  proof uses only a vanishing deficit, which is what is proved); the parenthetical "by `lem:convex-continuous-gradient`
  this follows from …" (that lemma is not formalised: `Q = ∇χ_{K,x}` with `χ` convex and differentiable on `O` enters only
  through monotonicity of `Q` on `O`, `MonoOn Q O`); "No Lipschitz bound … is needed only to certify an outer band"
  (interpretive). `prop:net-inner-band`(iii), the upper half of (i) (`sup_A⟨v,T⟩ ≤ M_p + ‖v‖η`) and the `M_p` halves of (ii) are NOT
  stated (declared; not covered).
* `eq:dualmap`: `π₀ = (Id, Q₀)#μ` is generalised to any `c₀`-optimal coupling `π₀` (the graph form is never used); the
  remarks after the lemma.
* `prop:band`: `ε = 0` (Wasserstein balls; the frozen kernel-witness encoding needs `ε > 0`); structured sets.
* `thm:sample-split`: iid is generalised to exchangeability of the rank sample (what the proof uses).
* `prop:rate-decomp`: the sentences "`prop:integrated-sieve-strong` gives `Δ^{sieve,L²}_n → 0`" and "the stronger
  local-uniform conclusion … yields" (pointers to other results).
* `prop:emp-bijective`, `prop:app-entropic`: the Brenier layer (Step 0, `x_i = ∇φ*(r_i)`), as in Wave 8b; "the last term
  vanishes by `prop:integrated-sieve-strong`" (a pointer).

Encodings:
* `lem:supp-small-cells`: `ℝ^q = Fin q → ℝ` (product = Borel `σ`-algebra), `μ` finite with `μ{x} = 0` for every `x`;
  cubes `∏_i [k_i2^{-ℓ}, (k_i+1)2^{-ℓ})`, `k ∈ ℤ^q` (`dyadicCube`); `η ∈ (0, ∞]` in `ℝ≥0∞`.
* `cor:net-inner-band-neural`: the frozen Wave 7a setting (`NeuralSetting`, `ℝ^K = EuclideanSpace`, `S = A(1−δ)`, query
  suppressed, `risk = ∫⁻_O‖T − Q‖²dμ_K`, edges in `EReal`, support condition as the open-set form `hsupp`); `0 < K`
  (for `K = 0` the region `ℝ⁰` has empty frontier and an empty net). Nets `𝒩_{n,p}` are `Finset`s with `NetCovers`
  (`𝒩 ⊆ A_{K,p}`, every point of `∂A_{K,p} = frontier` within `h`); `b^{±,net} = 𝔪 ± max_{𝒩}⟨±e, T⟩` is `nnSup T 𝒩`
  (an `EReal` sup over a finite set, `⊥` only for an empty net). The modulus `ω_S(h)` enters as any `w` with
  `‖Qx − Qy‖ ≤ w` for `x, y ∈ S`, `‖x − y‖ ≤ h` (the least such `w` is `ω_S(h)`), `η` as any bound of `sup_S‖T − Q‖`.
  Deficit (`NetDeficit`): `b^{+,pop} ≤ b^{+,net} + ε` and `b^{-,net} ≤ b^{-,pop} + ε`. Modes as in Wave 7a (a.s.:
  `∀ᵐ ω`; in probability: measurable-event convention on both sides); `h_n → 0` deterministic. Rate: `C_{K,ρ}` is
  chosen before the data (as in the frozen `neural_band_rate`), `L > 0`, "small risk" is `∃ R₀ > 0`; no smallness of
  `h` is needed.
* `eq:dualmap`: `U`, `V` measurable spaces, `V` normed; marginals `μ` (probability) and `ν`; couplings are Tau Ceti's
  `IsCoupling`; "optimal for `c`" (`IsOptimalFor`) is: a coupling with `c` integrable whose cost is `≤` that of every
  coupling under which `c` is integrable; "integrable optimal dual potentials" is `f ∈ L¹(μ)`, `g ∈ L¹(ν)` and
  `∫f dμ + ∫g dν = ∫c₀ dπ₀` (zero duality gap); "on the marginal supports" is on `S_u × S_v` for any measurable
  `S_u, S_v` of full `μ`-, `ν`-measure (the supports in second-countable spaces are one instance); the cost and the map
  error `‖v − Q₀(u)‖` are measurable. The conclusion asserts integrability, so the Bochner integral is not junk.
* `prop:band`: the frozen kernel-witness encoding (`InBall`, `RefClass`, `sqrtT = ⨆_ν √T^{{ν}}` in `ℝ≥0∞`, `nominal` =
  `Δ(h)`, `W₂` = Tau Ceti `wassersteinEDist 2`); `|a − b| ≤ c` is `a ≤ b + c ∧ b ≤ a + c` in `ℝ≥0∞`. `band_selected`:
  data `ω ↦ (x₀, x₁, r₀, r₁)`, selected rule `ĥ(ω)` and multipliers arbitrary functions of `ω`; `E ⊇ G` measurable with
  `P(G) ≥ 1 − α`. `band_deploy`: `K` compact metric (Borel), `c = dist²`, the free class `𝒫(K)`, `W₂²(P_s,Q_s) ≤ β_s`.
* `thm:sample-split`: `𝓘₀` is any random element `W` (the basis sample, or the estimates computed from it); rank-sample
  curves `X : Ω → Fin n → H` (`H` any measurable space); the estimated projection is a jointly measurable
  `proj : 𝒲 → H → E` and the reference grid `u : 𝒲 → Fin n → E` (`E` a real inner-product space; an estimated metric
  `M_w = L_wᵀL_w` is absorbed by `z ↦ L_w z` in `proj` and `u`); `σ̂ = sel_W(Z)` a jointly Borel selection of minimisers of
  the frozen `IsMin` cost; independence `IndepFun W X`, exchangeability of `X`; "conditionally a.s. unique" is a.s.
  uniqueness. "Uniform conditionally on `𝓘₀`" is the product formula over `{W ∈ B}` for measurable `B`.
* `prop:rate-decomp`: `rmsE P g = (∫⁻ n⁻¹Σ_i g_i² dP)^{1/2}` in `ℝ≥0∞` (`N(Z)` of the proof, no integrability junk);
  `ι_K` any linear isometry `ℝ^K → H`; in `rate_decomp` the four rank vectors are arbitrary random vectors (`F̂(x_i)`,
  `F_{+,K,m}(x_i)`, `F_{+,K}(x_i)` in `ℝ^K`, `𝔽_P(X_i)` in `H`) with measurable error norms (generalisation). Local form:
  `X_i ∼ P_X` (no independence), `F_{+,K} ∘ Π_K` and `𝔽_P` maps with `‖ι_KF_{+,K}(Π_Kx)‖ ≤ M`, `‖𝔽_P(x)‖ ≤ M`;
  `Δ^{sieve}(𝒦₀)` is any `D ≥ 0` bounding the sieve error at `y = F_{+,K}(Π_Kx)` for `P_X`-a.e. `x ∈ 𝒦₀`; `𝒦₀` measurable
  (compactness unused); `P(H∖𝒦₀)^{1/2}` is `rpow` in `ℝ≥0∞`.
* `prop:emp-bijective`, `prop:app-entropic`: the Wave 8b encoding (`x_i` the projected data, `r_i = F(x_i)`, grid `u`,
  `φ*` a real function `f` used only at grid points and ranks, `D = bregD`); `ass:app-conditioning` enters at the pairs
  used, a.s.: `TwoSidedAt α L` (`(α/2)‖u_j − r_i‖² ≤ D(u_j, r_i) ≤ (L/2)‖u_j − r_i‖²`), `0 < α ≤ L`, `κ = L/α`; the
  finite-grid population map `F_{+,K,n}` is any Borel `Fg`; the hard selection `σ̂(ω)` has measurable ranks `u_{σ̂(i)}`
  (needed for Minkowski only); `μ_K` a probability measure; `E` are lower integrals, the bounds in `ℝ≥0∞`
  (`ENNReal.ofReal` of nonnegative reals), `{·}^{1/2}` is `rpow (1/2)`.
* All claims quantify types in `Type` (universe 0), as elsewhere in the repo.

Critic notes:
* All 24 claims are proved by the routes (`Wave16b/Route{SmallCells,Net,Dualmap,Band,SampleSplit,Rates}.lean`), axioms
  `propext, Classical.choice, Quot.sound` only. No defect found in the eight items; the printed constants are exact.
* `lem:supp-small-cells`: the route replaces Bolzano–Weierstrass by a Lebesgue number of a cover by small-mass balls
  (same content).
* `cor:net-inner-band-neural`: the displayed rate inherits the `L > 0` caveat already flagged for `eq:neural-band-rate`
  (S3, Wave 7a): with `L = 0` the bound is `0`, false (`K = 1`, `μ = Unif[−1,1]`, `Q ≡ 0`, `T ≡ c`, monotone, risk
  `→ 0`, error `|c||e(t)| > 0`). `K ≥ 1` is implicit (for `K = 0` the frontier is empty). Convexity of `A_{K,p}` is not
  needed, as printed; closedness of `A_{K,p}` is not needed either (the route works on its closure).
* `eq:dualmap` holds as printed once its hidden hypotheses are explicit: `μ`, `ν` probability (the `δ`-steps integrate
  constants), zero duality gap `∫f + ∫g = OT₀`, integrability of `c₁` (automatic from that of `c₀` and `|c₁ − c₀| ≤ δ`).
* `prop:band` holds as printed (for `ε > 0`); the deployment clause needs `ε > 0`, compact `K` and `c = ‖·‖²`, the
  setting of `prop:cs-compose`.
* `thm:sample-split`, `prop:rate-decomp`, `prop:emp-bijective`, `prop:app-entropic` hold as printed.
* Critic (2026-10-15): ACCEPT / ACCEPT-WITH-NOTE, all 24 TRUE. `MonoOn Q O` + `ContinuousOn Q O` for `Q = ∇χ` is a
  genuine generalisation (Step 1 uses only monotonicity); `0 < K` is needed (empty frontier). The corollary inherits
  `L > 0` from `thm:neural-band-consistency` (fixed 2026-10-14, DEFECTS #38); `net_band_neural_rate` carries `0 < L`.
  The nets are deterministic (could depend on `ω` at no cost). `dualmap`'s explicit assumptions (probability laws,
  `∫f + ∫g = OT₀`, full-measure supports) are the paper's setting (`lem:mapcost-mult`). paper2 `prop:band` is certified
  for `ε > 0` only: the `ε = 0` Wasserstein/anisotropic sets (used by `cor:oracle`) are NOT covered (declared; weak
  duality for `ε = 0` would be an easy follow-up).
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped InnerProductSpace ENNReal

namespace StatFormal.OTFD.Wave16b

open StatFormal.OTFD.Wave7a (NeuralSetting nnSup popSup edgeUpE edgeLoE EClose risk MonoOn)
open StatFormal.OTFD.Wave8b (bregD IsOptAssign IsEntPlan entBary)
open StatFormal.OTFD.Wave6b (empMeasure)
open StatFormal.OTFD.Ranks (IsMin UniqueMin)
open StatFormal.RobustEquality.Certificate (KernelWitness)
open StatFormal.Wave4b (InBall sqrtT nominal RefClass)
open StatFormal.Wave11a (freeClass)
open TauCeti (wassersteinEDist IsCoupling)

/-! ### C `lem:supp-small-cells` -/

/-- The half-open dyadic cube `∏_i [k_i 2^{-ℓ}, (k_i + 1) 2^{-ℓ})` of side `2^{-ℓ}`, indexed by `k ∈ ℤ^q`. -/
def dyadicCube (q ℓ : ℕ) (k : Fin q → ℤ) : Set (Fin q → ℝ) :=
  Set.pi Set.univ fun i => Set.Ico ((k i : ℝ) / 2 ^ ℓ) (((k i : ℝ) + 1) / 2 ^ ℓ)

/-! ### C `cor:net-inner-band-neural` -/

section Net
variable {K : ℕ}

/-- `𝒩 ⊆ A` is finite and every point of `∂A` lies within `h` of `𝒩`. -/
def NetCovers (A : Set (EuclideanSpace ℝ (Fin K))) (N : Finset (EuclideanSpace ℝ (Fin K))) (h : ℝ) : Prop :=
  (↑N : Set (EuclideanSpace ℝ (Fin K))) ⊆ A ∧ ∀ z ∈ frontier A, ∃ u ∈ N, ‖z - u‖ ≤ h

/-- Edge deficit of the attained net band `b^{±,net}_p = 𝔪 ± max_{u∈𝒩_p}⟨±e, T(u)⟩` against the population band is at
most `ε`: `b^{+,pop} ≤ b^{+,net} + ε` and `b^{-,net} ≤ b^{-,pop} + ε`, at every `t` and every `0 < p ≤ 1 − δ`. -/
def NetDeficit {𝒯 : Type} (μ : Measure (EuclideanSpace ℝ (Fin K)))
    (T Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (A : ℝ → Set (EuclideanSpace ℝ (Fin K)))
    (δ : ℝ) (mo : 𝒯 → ℝ) (e : 𝒯 → EuclideanSpace ℝ (Fin K)) (N : ℝ → Finset (EuclideanSpace ℝ (Fin K)))
    (ε : ℝ) : Prop :=
  ∀ p, 0 < p → p ≤ 1 - δ → ∀ t,
    edgeUpE (popSup μ Q (A p)) (mo t) (e t) ≤ edgeUpE (nnSup T ↑(N p)) (mo t) (e t) + (ε : EReal) ∧
    edgeLoE (nnSup T ↑(N p)) (mo t) (e t) ≤ edgeLoE (popSup μ Q (A p)) (mo t) (e t) + (ε : EReal)

/-- Both attained net edges are within `ε` of the population edges, at every `t` and every `0 < p ≤ 1 − δ`. -/
def NetClose {𝒯 : Type} (μ : Measure (EuclideanSpace ℝ (Fin K)))
    (T Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (A : ℝ → Set (EuclideanSpace ℝ (Fin K)))
    (δ : ℝ) (mo : 𝒯 → ℝ) (e : 𝒯 → EuclideanSpace ℝ (Fin K)) (N : ℝ → Finset (EuclideanSpace ℝ (Fin K)))
    (ε : ℝ) : Prop :=
  ∀ p, 0 < p → p ≤ 1 - δ → ∀ t,
    EClose (edgeUpE (nnSup T ↑(N p)) (mo t) (e t)) (edgeUpE (popSup μ Q (A p)) (mo t) (e t)) ε ∧
    EClose (edgeLoE (nnSup T ↑(N p)) (mo t) (e t)) (edgeLoE (popSup μ Q (A p)) (mo t) (e t)) ε

end Net

/-! ### T `eq:dualmap` -/

section Dualmap
variable {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]

/-- `π` is an optimal coupling of `μ, ν` for the cost `c`: a coupling under which `c` is integrable and whose cost is
at most that of every coupling under which `c` is integrable. -/
def IsOptimalFor (c : U × V → ℝ) (μ : Measure U) (ν : Measure V) (π : Measure (U × V)) : Prop :=
  IsCoupling π μ ν ∧ Integrable c π ∧
    ∀ γ : Measure (U × V), IsCoupling γ μ ν → Integrable c γ → ∫ z, c z ∂π ≤ ∫ z, c z ∂γ

end Dualmap

/-! ### A `prop:rate-decomp`, `prop:emp-bijective`, `prop:app-entropic` -/

section Rates

/-- `(E[n⁻¹ Σ_i g_i²])^{1/2}` for nonnegative errors `g_i` (lower integral, `ℝ≥0∞`). -/
def rmsE {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ} (g : Ω → Fin n → ℝ) : ℝ≥0∞ :=
  (∫⁻ ω, ENNReal.ofReal ((1 / n : ℝ) * ∑ i, g ω i ^ 2) ∂P) ^ (1 / 2 : ℝ)

variable {K n m : ℕ}

/-- `ass:app-conditioning` at the pairs `(u_j, r_i)` used by the proofs (`x_i` in the role of `∇φ*(r_i)`):
`(α/2)‖u_j − r_i‖² ≤ D(u_j, r_i) ≤ (L/2)‖u_j − r_i‖²`. -/
def TwoSidedAt (α L : ℝ) (f : EuclideanSpace ℝ (Fin K) → ℝ) (u : Fin m → EuclideanSpace ℝ (Fin K))
    (x r : Fin n → EuclideanSpace ℝ (Fin K)) : Prop :=
  ∀ i j, α / 2 * ‖u j - r i‖ ^ 2 ≤ bregD f (x i) (r i) (u j) ∧
    bregD f (x i) (r i) (u j) ≤ L / 2 * ‖u j - r i‖ ^ 2

end Rates

namespace Claims

/-! ### C `lem:supp-small-cells` -/

/-- `lem:supp-small-cells`: for a finite atomless Borel measure on `ℝ^q` and `η > 0`, some dyadic level `ℓ` has every
half-open dyadic cube of side `2^{-ℓ}` of measure at most `η`. -/
def small_cells : Prop :=
  ∀ (q : ℕ) (μ : Measure (Fin q → ℝ)) [IsFiniteMeasure μ], (∀ x, μ {x} = 0) →
    ∀ η : ℝ≥0∞, 0 < η → ∃ ℓ : ℕ, ∀ k : Fin q → ℤ, μ (dyadicCube q ℓ k) ≤ η

/-- The half-open dyadic cubes of side `2^{-ℓ}` form a countable Borel partition of `ℝ^q`. -/
def dyadic_partition : Prop :=
  ∀ q ℓ : ℕ, Countable (Fin q → ℤ) ∧ (∀ k, MeasurableSet (dyadicCube q ℓ k)) ∧
    Pairwise (fun k k' => Disjoint (dyadicCube q ℓ k) (dyadicCube q ℓ k')) ∧
    (⋃ k, dyadicCube q ℓ k) = univ

/-! ### C `cor:net-inner-band-neural` (and the deterministic part of `prop:net-inner-band`) -/

/-- `prop:net-inner-band` (i)–(ii) and the deficit sentence, deterministically: if `sup_S‖T − Q‖ ≤ η`, `Q` moves by at
most `w` over distances `≤ h` on `S = A_{K,1−δ}`, and the nets have covering radius `h`, then the net band lies inside the
band of `T` and its edge deficit is at most `E_K(w + η)`. -/
def net_inner_deficit : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ : Measure (EuclideanSpace ℝ (Fin K))) (O : Set (EuclideanSpace ℝ (Fin K)))
    (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (A : ℝ → Set (EuclideanSpace ℝ (Fin K)))
    (δ : ℝ) (mo : 𝒯 → ℝ) (e : 𝒯 → EuclideanSpace ℝ (Fin K)) (E : ℝ)
    (T : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (N : ℝ → Finset (EuclideanSpace ℝ (Fin K)))
    (h η w : ℝ),
    0 < K → NeuralSetting μ O Q A δ e E → MonoOn Q O →
    0 ≤ η → (∀ u ∈ A (1 - δ), ‖T u - Q u‖ ≤ η) →
    (∀ x ∈ A (1 - δ), ∀ y ∈ A (1 - δ), ‖x - y‖ ≤ h → ‖Q x - Q y‖ ≤ w) →
    (∀ p, 0 < p → p ≤ 1 - δ → NetCovers (A p) (N p) h) →
      (∀ p, 0 < p → p ≤ 1 - δ → ∀ t,
        edgeUpE (nnSup T ↑(N p)) (mo t) (e t) ≤ edgeUpE (nnSup T (A p)) (mo t) (e t) ∧
        edgeLoE (nnSup T (A p)) (mo t) (e t) ≤ edgeLoE (nnSup T ↑(N p)) (mo t) (e t)) ∧
      NetDeficit μ T Q A δ mo e N (E * (w + η))

/-- `prop:net-inner-band` (iv) and the two-sided display, deterministically: under the support condition the net
edges are within `E_K(w + η)` of the population edges. -/
def net_inner_two_sided : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ : Measure (EuclideanSpace ℝ (Fin K))) (O : Set (EuclideanSpace ℝ (Fin K)))
    (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (A : ℝ → Set (EuclideanSpace ℝ (Fin K)))
    (δ : ℝ) (mo : 𝒯 → ℝ) (e : 𝒯 → EuclideanSpace ℝ (Fin K)) (E : ℝ)
    (T : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (N : ℝ → Finset (EuclideanSpace ℝ (Fin K)))
    (h η w : ℝ),
    0 < K → NeuralSetting μ O Q A δ e E → MonoOn Q O →
    (∀ p, 0 < p → p ≤ 1 - δ → ∀ N', IsOpen N' → (N' ∩ A p).Nonempty → 0 < μ (A p ∩ N')) →
    0 ≤ η → (∀ u ∈ A (1 - δ), ‖T u - Q u‖ ≤ η) →
    (∀ x ∈ A (1 - δ), ∀ y ∈ A (1 - δ), ‖x - y‖ ≤ h → ‖Q x - Q y‖ ≤ w) →
    (∀ p, 0 < p → p ≤ 1 - δ → NetCovers (A p) (N p) h) →
      NetClose μ T Q A δ mo e N (E * (w + η))

/-- `cor:net-inner-band-neural`, almost-sure mode: `𝓡_{n,x} → 0` a.s. and `h_n → 0` give an edge deficit of the attained
net band tending to `0` a.s., uniformly in `t` and `0 < p ≤ 1 − δ`. -/
def net_band_neural_ae : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ : Measure (EuclideanSpace ℝ (Fin K))) (O : Set (EuclideanSpace ℝ (Fin K)))
    (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (A : ℝ → Set (EuclideanSpace ℝ (Fin K)))
    (δ : ℝ) (mo : 𝒯 → ℝ) (e : 𝒯 → EuclideanSpace ℝ (Fin K)) (E : ℝ)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (T : ℕ → Ω → EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (N : ℕ → ℝ → Finset (EuclideanSpace ℝ (Fin K))) (h : ℕ → ℝ),
    0 < K → NeuralSetting μ O Q A δ e E → MonoOn Q O → (∀ n ω, MonoOn (T n ω) O) →
    Tendsto h atTop (𝓝 0) → (∀ n p, 0 < p → p ≤ 1 - δ → NetCovers (A p) (N n p) (h n)) →
    (∀ᵐ ω ∂P, Tendsto (fun n => risk μ O (T n ω) Q) atTop (𝓝 0)) →
      ∀ᵐ ω ∂P, ∀ ε, 0 < ε → ∀ᶠ n in atTop, NetDeficit μ (T n ω) Q A δ mo e (N n) ε

/-- `cor:net-inner-band-neural`, in-probability mode (measurable-event convention on both sides). -/
def net_band_neural_prob : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ : Measure (EuclideanSpace ℝ (Fin K))) (O : Set (EuclideanSpace ℝ (Fin K)))
    (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (A : ℝ → Set (EuclideanSpace ℝ (Fin K)))
    (δ : ℝ) (mo : 𝒯 → ℝ) (e : 𝒯 → EuclideanSpace ℝ (Fin K)) (E : ℝ)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (T : ℕ → Ω → EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (N : ℕ → ℝ → Finset (EuclideanSpace ℝ (Fin K))) (h : ℕ → ℝ),
    0 < K → NeuralSetting μ O Q A δ e E → MonoOn Q O → (∀ n ω, MonoOn (T n ω) O) →
    Tendsto h atTop (𝓝 0) → (∀ n p, 0 < p → p ≤ 1 - δ → NetCovers (A p) (N n p) (h n)) →
    (∀ η, 0 < η → ∀ δ', 0 < δ' → ∀ᶠ n in atTop, ∃ G : Set Ω, MeasurableSet G ∧
        G ⊆ {ω | risk μ O (T n ω) Q ≤ ENNReal.ofReal η} ∧ ENNReal.ofReal (1 - δ') ≤ P G) →
      ∀ ε, 0 < ε → ∀ δ', 0 < δ' → ∀ᶠ n in atTop, ∃ G : Set Ω, MeasurableSet G ∧
        G ⊆ {ω | NetDeficit μ (T n ω) Q A δ mo e (N n) ε} ∧ ENNReal.ofReal (1 - δ') ≤ P G

/-- `cor:net-inner-band-neural`, two-sided convergence under the support condition of `prop:net-inner-band`(iv),
almost-sure mode. -/
def net_band_neural_two_sided_ae : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ : Measure (EuclideanSpace ℝ (Fin K))) (O : Set (EuclideanSpace ℝ (Fin K)))
    (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (A : ℝ → Set (EuclideanSpace ℝ (Fin K)))
    (δ : ℝ) (mo : 𝒯 → ℝ) (e : 𝒯 → EuclideanSpace ℝ (Fin K)) (E : ℝ)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (T : ℕ → Ω → EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (N : ℕ → ℝ → Finset (EuclideanSpace ℝ (Fin K))) (h : ℕ → ℝ),
    0 < K → NeuralSetting μ O Q A δ e E → MonoOn Q O → (∀ n ω, MonoOn (T n ω) O) →
    (∀ p, 0 < p → p ≤ 1 - δ → ∀ N', IsOpen N' → (N' ∩ A p).Nonempty → 0 < μ (A p ∩ N')) →
    Tendsto h atTop (𝓝 0) → (∀ n p, 0 < p → p ≤ 1 - δ → NetCovers (A p) (N n p) (h n)) →
    (∀ᵐ ω ∂P, Tendsto (fun n => risk μ O (T n ω) Q) atTop (𝓝 0)) →
      ∀ᵐ ω ∂P, ∀ ε, 0 < ε → ∀ᶠ n in atTop, NetClose μ (T n ω) Q A δ mo e (N n) ε

/-- `cor:net-inner-band-neural`, two-sided convergence under the support condition, in-probability mode. -/
def net_band_neural_two_sided_prob : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ : Measure (EuclideanSpace ℝ (Fin K))) (O : Set (EuclideanSpace ℝ (Fin K)))
    (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (A : ℝ → Set (EuclideanSpace ℝ (Fin K)))
    (δ : ℝ) (mo : 𝒯 → ℝ) (e : 𝒯 → EuclideanSpace ℝ (Fin K)) (E : ℝ)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (T : ℕ → Ω → EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (N : ℕ → ℝ → Finset (EuclideanSpace ℝ (Fin K))) (h : ℕ → ℝ),
    0 < K → NeuralSetting μ O Q A δ e E → MonoOn Q O → (∀ n ω, MonoOn (T n ω) O) →
    (∀ p, 0 < p → p ≤ 1 - δ → ∀ N', IsOpen N' → (N' ∩ A p).Nonempty → 0 < μ (A p ∩ N')) →
    Tendsto h atTop (𝓝 0) → (∀ n p, 0 < p → p ≤ 1 - δ → NetCovers (A p) (N n p) (h n)) →
    (∀ η, 0 < η → ∀ δ', 0 < δ' → ∀ᶠ n in atTop, ∃ G : Set Ω, MeasurableSet G ∧
        G ⊆ {ω | risk μ O (T n ω) Q ≤ ENNReal.ofReal η} ∧ ENNReal.ofReal (1 - δ') ≤ P G) →
      ∀ ε, 0 < ε → ∀ δ', 0 < δ' → ∀ᶠ n in atTop, ∃ G : Set Ω, MeasurableSet G ∧
        G ⊆ {ω | NetClose μ (T n ω) Q A δ mo e (N n) ε} ∧ ENNReal.ofReal (1 - δ') ≤ P G

/-- The displayed rate of `cor:net-inner-band-neural`: with `Q` `L`-Lipschitz and density `≥ ρ` near `S`, for small
risk the net edges are within `E_K{L h + C_{K,ρ} L^{K/(K+2)} 𝓡^{1/(K+2)}}` of the population edges, for every covering
radius `h ≥ 0`. -/
def net_band_neural_rate : Prop :=
  ∀ (K : ℕ) (ρ : ℝ), 0 < K → 0 < ρ → ∃ Cst : ℝ, 0 < Cst ∧
    ∀ (𝒯 : Type) (μ : Measure (EuclideanSpace ℝ (Fin K))) (O O' : Set (EuclideanSpace ℝ (Fin K)))
      (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (A : ℝ → Set (EuclideanSpace ℝ (Fin K)))
      (δ : ℝ) (mo : 𝒯 → ℝ) (e : 𝒯 → EuclideanSpace ℝ (Fin K)) (E L : ℝ),
      NeuralSetting μ O Q A δ e E → MonoOn Q O →
      (∀ p, 0 < p → p ≤ 1 - δ → ∀ N', IsOpen N' → (N' ∩ A p).Nonempty → 0 < μ (A p ∩ N')) →
      IsOpen O' → A (1 - δ) ⊆ O' → O' ⊆ O →
      (∀ B, MeasurableSet B → B ⊆ O' → ENNReal.ofReal ρ * volume B ≤ μ B) →
      0 < L → (∀ x ∈ O', ∀ y ∈ O', ‖Q x - Q y‖ ≤ L * ‖x - y‖) →
        ∃ R₀, 0 < R₀ ∧ ∀ R, 0 < R → R ≤ R₀ →
          ∀ T : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K),
            MonoOn T O → risk μ O T Q ≤ ENNReal.ofReal R →
              ∀ (N : ℝ → Finset (EuclideanSpace ℝ (Fin K))) (h : ℝ), 0 ≤ h →
                (∀ p, 0 < p → p ≤ 1 - δ → NetCovers (A p) (N p) h) →
                  NetClose μ T Q A δ mo e N
                    (E * (L * h + Cst * L ^ ((K : ℝ) / (K + 2)) * R ^ ((1 : ℝ) / (K + 2))))

/-! ### T `eq:dualmap` (`lem:mapcost`) -/

/-- `eq:dualmap`: `|c₁ − c₀| ≤ δ` on the marginal supports and a `β`-quadratic dual gap give
`∫‖v − Q₀(u)‖² dπ₁ ≤ 2δ/β` (the integrand is `π₁`-integrable). -/
def dualmap : Prop :=
  ∀ (U V : Type) [MeasurableSpace U] [MeasurableSpace V] [NormedAddCommGroup V]
    (μ : Measure U) (ν : Measure V) [IsProbabilityMeasure μ] (c₀ c₁ : U × V → ℝ) (f : U → ℝ) (g : V → ℝ)
    (Q₀ : U → V) (π₀ π₁ : Measure (U × V)) (Su : Set U) (Sv : Set V) (β δ : ℝ),
    Measurable c₀ → Measurable c₁ → Measurable f → Measurable g →
    Measurable (fun z : U × V => ‖z.2 - Q₀ z.1‖) →
    MeasurableSet Su → MeasurableSet Sv → μ Suᶜ = 0 → ν Svᶜ = 0 →
    IsOptimalFor c₀ μ ν π₀ → Integrable f μ → Integrable g ν →
    ∫ u, f u ∂μ + ∫ v, g v ∂ν = ∫ z, c₀ z ∂π₀ →
    0 < β → (∀ u ∈ Su, ∀ v ∈ Sv, β * ‖v - Q₀ u‖ ^ 2 ≤ c₀ (u, v) - f u - g v) →
    (∀ u ∈ Su, ∀ v ∈ Sv, |c₁ (u, v) - c₀ (u, v)| ≤ δ) →
    IsOptimalFor c₁ μ ν π₁ →
      Integrable (fun z : U × V => ‖z.2 - Q₀ z.1‖ ^ 2) π₁ ∧
        ∫ z, ‖z.2 - Q₀ z.1‖ ^ 2 ∂π₁ ≤ 2 * δ / β

/-- `eq:dualmap`, one-sided perturbation `0 ≤ c₀ − c₁ ≤ δ`: the bound improves to `δ/β`. -/
def dualmap_one_sided : Prop :=
  ∀ (U V : Type) [MeasurableSpace U] [MeasurableSpace V] [NormedAddCommGroup V]
    (μ : Measure U) (ν : Measure V) [IsProbabilityMeasure μ] (c₀ c₁ : U × V → ℝ) (f : U → ℝ) (g : V → ℝ)
    (Q₀ : U → V) (π₀ π₁ : Measure (U × V)) (Su : Set U) (Sv : Set V) (β δ : ℝ),
    Measurable c₀ → Measurable c₁ → Measurable f → Measurable g →
    Measurable (fun z : U × V => ‖z.2 - Q₀ z.1‖) →
    MeasurableSet Su → MeasurableSet Sv → μ Suᶜ = 0 → ν Svᶜ = 0 →
    IsOptimalFor c₀ μ ν π₀ → Integrable f μ → Integrable g ν →
    ∫ u, f u ∂μ + ∫ v, g v ∂ν = ∫ z, c₀ z ∂π₀ →
    0 < β → (∀ u ∈ Su, ∀ v ∈ Sv, β * ‖v - Q₀ u‖ ^ 2 ≤ c₀ (u, v) - f u - g v) →
    (∀ u ∈ Su, ∀ v ∈ Sv, 0 ≤ c₀ (u, v) - c₁ (u, v) ∧ c₀ (u, v) - c₁ (u, v) ≤ δ) →
    IsOptimalFor c₁ μ ν π₁ →
      Integrable (fun z : U × V => ‖z.2 - Q₀ z.1‖ ^ 2) π₁ ∧
        ∫ z, ‖z.2 - Q₀ z.1‖ ^ 2 ∂π₁ ≤ δ / β

/-! ### paper2 `prop:band` -/

/-- `prop:band`: on `E = {P_s ∈ 𝓑_s, s = 0,1}`, for every bounded measurable rule `h` and all multipliers,
`|W₂(h#P₀, h#P₁) − Δ(h)| ≤ √T₀(h,λ₀) + √T₁(h,λ₁)` (two `ℝ≥0∞` inequalities). -/
def band : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n₀ n₁ : ℕ) (x₀ : Fin n₀ → K) (x₁ : Fin n₁ → K)
    (c : K → K → ℝ) (ε r₀ r₁ : ℝ) (N₀ N₁ : Set (Measure K)) (P₀ P₁ : Measure K),
    0 < n₀ → 0 < n₁ → 0 < ε →
    Measurable (Function.uncurry c) → (∀ a b, 0 ≤ c a b) → (∃ B, ∀ a b, c a b ≤ B) →
    RefClass N₀ → RefClass N₁ → InBall x₀ c ε r₀ N₀ P₀ → InBall x₁ c ε r₁ N₁ P₁ →
      ∀ (h : K → ℝ) (lam₀ lam₁ : ℝ), Measurable h → (∃ H, ∀ z, |h z| ≤ H) → 0 < lam₀ → 0 < lam₁ →
        wassersteinEDist 2 (P₀.map h) (P₁.map h) ≤
            nominal x₀ x₁ h + sqrtT x₀ c h ε r₀ lam₀ N₀ + sqrtT x₁ c h ε r₁ lam₁ N₁ ∧
          nominal x₀ x₁ h ≤
            wassersteinEDist 2 (P₀.map h) (P₁.map h) + sqrtT x₀ c h ε r₀ lam₀ N₀ + sqrtT x₁ c h ε r₁ lam₁ N₁

/-- `prop:band`, "hence": the certificate of a rule `ĥ` selected on the same data (any data-dependent choice of rule and
multipliers) bounds its population disparity on `E`; with `P(E) ≥ 1 − α` (measurable-event convention) the bound holds
on a measurable event of probability `≥ 1 − α`. -/
def band_selected : Prop :=
  ∀ (K Ω : Type) [MeasurableSpace K] [MeasurableSpace Ω] (P : Measure Ω) (n₀ n₁ : ℕ)
    (x₀ : Ω → Fin n₀ → K) (x₁ : Ω → Fin n₁ → K) (c : K → K → ℝ) (ε α : ℝ) (r₀ r₁ : Ω → ℝ)
    (N₀ N₁ : Set (Measure K)) (P₀ P₁ : Measure K) (hsel : Ω → K → ℝ) (lam₀ lam₁ : Ω → ℝ) (G : Set Ω),
    0 < n₀ → 0 < n₁ → 0 < ε →
    Measurable (Function.uncurry c) → (∀ a b, 0 ≤ c a b) → (∃ B, ∀ a b, c a b ≤ B) →
    RefClass N₀ → RefClass N₁ →
    (∀ ω, Measurable (hsel ω) ∧ (∃ H, ∀ z, |hsel ω z| ≤ H) ∧ 0 < lam₀ ω ∧ 0 < lam₁ ω) →
    MeasurableSet G → ENNReal.ofReal (1 - α) ≤ P G →
    (∀ ω ∈ G, InBall (x₀ ω) c ε (r₀ ω) N₀ P₀ ∧ InBall (x₁ ω) c ε (r₁ ω) N₁ P₁) →
      ∃ G' : Set Ω, MeasurableSet G' ∧ ENNReal.ofReal (1 - α) ≤ P G' ∧
        G' ⊆ {ω | wassersteinEDist 2 (P₀.map (hsel ω)) (P₁.map (hsel ω)) ≤
          nominal (x₀ ω) (x₁ ω) (hsel ω) + sqrtT (x₀ ω) c (hsel ω) ε (r₀ ω) (lam₀ ω) N₀ +
            sqrtT (x₁ ω) c (hsel ω) ε (r₁ ω) (lam₁ ω) N₁}

/-- `prop:band`, free end with a declared Wasserstein budget: if `P_s` lies in the free-end ball of radius `r_s` and the
deployment `Q_s` has `W₂²(P_s, Q_s) ≤ β_s`, composition (`prop:cs-compose`) places `Q_s` in the free-end ball of radius
`(√r_s + √β_s)²`, and the certificate at these radii bounds the deployment disparity of every rule. -/
def band_deploy : Prop :=
  ∀ (K : Type) [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (n₀ n₁ : ℕ)
    (x₀ : Fin n₀ → K) (x₁ : Fin n₁ → K) (ε r₀ r₁ β₀ β₁ : ℝ) (P₀ P₁ Q₀ Q₁ : Measure K)
    [IsProbabilityMeasure Q₀] [IsProbabilityMeasure Q₁],
    0 < n₀ → 0 < n₁ → 0 < ε → 0 ≤ r₀ → 0 ≤ r₁ → 0 ≤ β₀ → 0 ≤ β₁ →
    InBall x₀ (fun a b => dist a b ^ 2) ε r₀ freeClass P₀ →
    InBall x₁ (fun a b => dist a b ^ 2) ε r₁ freeClass P₁ →
    wassersteinEDist 2 P₀ Q₀ ^ 2 ≤ ENNReal.ofReal β₀ → wassersteinEDist 2 P₁ Q₁ ^ 2 ≤ ENNReal.ofReal β₁ →
      ∀ (h : K → ℝ) (lam₀ lam₁ : ℝ), Measurable h → (∃ H, ∀ z, |h z| ≤ H) → 0 < lam₀ → 0 < lam₁ →
        wassersteinEDist 2 (Q₀.map h) (Q₁.map h) ≤
          nominal x₀ x₁ h +
            sqrtT x₀ (fun a b => dist a b ^ 2) h ε ((√r₀ + √β₀) ^ 2) lam₀ freeClass +
            sqrtT x₁ (fun a b => dist a b ^ 2) h ε ((√r₁ + √β₁) ^ 2) lam₁ freeClass

/-! ### A `thm:sample-split` -/

/-- `thm:sample-split`: with the basis/metric/reference estimated from `𝓘₀` (`W`), rank-sample curves `X` exchangeable
and independent of `W`, and a conditionally a.s. unique assignment, the hard rank permutation is uniform on `S_n`
conditionally on `𝓘₀`: `P(W ∈ B, σ̂ = π) = P(W ∈ B)/n!`. -/
def sample_split : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (H 𝒲 Ω : Type) [MeasurableSpace H] [MeasurableSpace 𝒲] [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ) (W : Ω → 𝒲) (X : Ω → Fin n → H) (proj : 𝒲 → H → E)
    (u : 𝒲 → Fin n → E) (sel : 𝒲 → (Fin n → E) → Equiv.Perm (Fin n)),
    Measurable W → Measurable X → Measurable (Function.uncurry proj) →
    (∀ w z, IsMin (u w) z (sel w z)) →
    (∀ π, MeasurableSet {p : 𝒲 × (Fin n → E) | sel p.1 p.2 = π}) →
    IndepFun W X P → (∀ τ : Equiv.Perm (Fin n), P.map (fun ω => X ω ∘ τ) = P.map X) →
    (∀ᵐ ω ∂P, UniqueMin (u (W ω)) (fun i => proj (W ω) (X ω i))) →
      ∀ B : Set 𝒲, MeasurableSet B → ∀ π : Equiv.Perm (Fin n),
        P ({ω | W ω ∈ B} ∩ {ω | sel (W ω) (fun i => proj (W ω) (X ω i)) = π}) =
          P {ω | W ω ∈ B} * (Nat.factorial n : ℝ≥0∞)⁻¹

open scoped Classical in
/-- `thm:sample-split`, rank form: the ranks `R_i = u_{σ̂(i)}` are distributed, conditionally on `𝓘₀`, as
`(u_{π(i)})_i` with `π` uniform: `P(W ∈ B, R ∈ S) = ∫_{W ∈ B} #{π : u_W ∘ π ∈ S}/n! dP`. -/
def sample_split_ranks : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (H 𝒲 Ω : Type) [MeasurableSpace H] [MeasurableSpace 𝒲] [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ) (W : Ω → 𝒲) (X : Ω → Fin n → H) (proj : 𝒲 → H → E)
    (u : 𝒲 → Fin n → E) (sel : 𝒲 → (Fin n → E) → Equiv.Perm (Fin n)),
    Measurable W → Measurable X → Measurable (Function.uncurry proj) → Measurable u →
    (∀ w z, IsMin (u w) z (sel w z)) →
    (∀ π, MeasurableSet {p : 𝒲 × (Fin n → E) | sel p.1 p.2 = π}) →
    IndepFun W X P → (∀ τ : Equiv.Perm (Fin n), P.map (fun ω => X ω ∘ τ) = P.map X) →
    (∀ᵐ ω ∂P, UniqueMin (u (W ω)) (fun i => proj (W ω) (X ω i))) →
      ∀ B : Set 𝒲, MeasurableSet B → ∀ S : Set (Fin n → E), MeasurableSet S →
        P ({ω | W ω ∈ B} ∩
            {ω | (fun i => u (W ω) (sel (W ω) (fun i => proj (W ω) (X ω i)) i)) ∈ S}) =
          ∫⁻ ω in {ω | W ω ∈ B},
            ((Finset.univ.filter (fun π : Equiv.Perm (Fin n) => u (W ω) ∘ π ∈ S)).card : ℝ≥0∞) *
              (Nat.factorial n : ℝ≥0∞)⁻¹ ∂P

/-! ### A `prop:rate-decomp` -/

/-- `eq:app-rate-decomp` (Minkowski): with `ι_K` an isometry,
`rms(ι_K F̂ − 𝔽_P) ≤ Δ^{emp,(m)} + Δ^{grid} + Δ^{sieve,L²}`. -/
def rate_decomp : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (K n : ℕ) (Ω : Type) [MeasurableSpace Ω]
    (P : Measure Ω) (ι : EuclideanSpace ℝ (Fin K) →ₗᵢ[ℝ] H)
    (Fhat Fm FK : Ω → Fin n → EuclideanSpace ℝ (Fin K)) (FP : Ω → Fin n → H),
    (∀ i, Measurable fun ω => ‖Fhat ω i - Fm ω i‖) → (∀ i, Measurable fun ω => ‖Fm ω i - FK ω i‖) →
    (∀ i, Measurable fun ω => ‖ι (FK ω i) - FP ω i‖) →
      rmsE P (fun ω i => ‖ι (Fhat ω i) - FP ω i‖) ≤
        rmsE P (fun ω i => ‖Fhat ω i - Fm ω i‖) + rmsE P (fun ω i => ‖Fm ω i - FK ω i‖) +
          rmsE P (fun ω i => ‖ι (FK ω i) - FP ω i‖)

/-- `eq:app-rate-decomp-local`: if the sieve error is at most `D` on `𝒦₀` and all rank maps take values in `B_H(0,M)`,
then `rms(ι_K F̂ − 𝔽_P) ≤ Δ^{emp,(m)} + Δ^{grid} + D + 2M√P(H∖𝒦₀)`. -/
def rate_decomp_local : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] (K n : ℕ) (Ω : Type)
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (ι : EuclideanSpace ℝ (Fin K) →ₗᵢ[ℝ] H)
    (X : Ω → Fin n → H) (PX : Measure H) (Pi : H → EuclideanSpace ℝ (Fin K))
    (FK : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (FP : H → H)
    (Fhat Fm : Ω → Fin n → EuclideanSpace ℝ (Fin K)) (K₀ : Set H) (D M : ℝ),
    (∀ i, Measurable fun ω => X ω i) → (∀ i, P.map (fun ω => X ω i) = PX) → MeasurableSet K₀ →
    (∀ i, Measurable fun ω => ‖Fhat ω i - Fm ω i‖) →
    (∀ i, Measurable fun ω => ‖Fm ω i - FK (Pi (X ω i))‖) →
    Measurable (fun x => ‖ι (FK (Pi x)) - FP x‖) →
    0 ≤ D → (∀ᵐ x ∂PX, x ∈ K₀ → ‖ι (FK (Pi x)) - FP x‖ ≤ D) →
    (∀ x, ‖ι (FK (Pi x))‖ ≤ M) → (∀ x, ‖FP x‖ ≤ M) →
      rmsE P (fun ω i => ‖ι (Fhat ω i) - FP (X ω i)‖) ≤
        rmsE P (fun ω i => ‖Fhat ω i - Fm ω i‖) + rmsE P (fun ω i => ‖Fm ω i - FK (Pi (X ω i))‖) +
          ENNReal.ofReal D + ENNReal.ofReal (2 * M) * PX K₀ᶜ ^ (1 / 2 : ℝ)

/-! ### A `prop:emp-bijective` -/

/-- Steps 1–2 of the proof for one realisation: `n⁻¹Σ‖u_{σ̂(i)} − r_i‖² ≤ κ W₂²(ν̂_n, μ_{K,n})`, `κ = L/α`. -/
def bijective_two_sided_core : Prop :=
  ∀ (K n : ℕ) (α L : ℝ) (f : EuclideanSpace ℝ (Fin K) → ℝ) (x r u : Fin n → EuclideanSpace ℝ (Fin K))
    (σ : Equiv.Perm (Fin n)),
    1 ≤ n → 0 < α → α ≤ L → TwoSidedAt α L f u x r → IsOptAssign x u σ →
      ENNReal.ofReal ((1 / n : ℝ) * ∑ i, ‖u (σ i) - r i‖ ^ 2) ≤
        ENNReal.ofReal (L / α) * wassersteinEDist 2 (empMeasure r) (empMeasure u) ^ 2

/-- The Step 2 display: `E[n⁻¹Σ‖F̂(x_i) − F(x_i)‖²] ≤ 2κ{E W₂²(ν̂_n, μ_K) + W₂²(μ_{K,n}, μ_K)}`. -/
def emp_bijective_sq : Prop :=
  ∀ (K n : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure μ]
    (x : Fin n → Ω → EuclideanSpace ℝ (Fin K))
    (F : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (u : Fin n → EuclideanSpace ℝ (Fin K))
    (f : EuclideanSpace ℝ (Fin K) → ℝ) (α L : ℝ) (σ : Ω → Equiv.Perm (Fin n)),
    1 ≤ n → 0 < α → α ≤ L →
    (∀ᵐ ω ∂P, TwoSidedAt α L f u (fun i => x i ω) (fun i => F (x i ω))) →
    (∀ ω, IsOptAssign (fun i => x i ω) u (σ ω)) →
      ∫⁻ ω, ENNReal.ofReal ((1 / n : ℝ) * ∑ i, ‖u (σ ω i) - F (x i ω)‖ ^ 2) ∂P ≤
        ENNReal.ofReal (2 * (L / α)) *
          (∫⁻ ω, wassersteinEDist 2 (empMeasure fun i => F (x i ω)) μ ^ 2 ∂P +
            wassersteinEDist 2 (empMeasure u) μ ^ 2)

/-- `prop:emp-bijective`: `Δ^{emp,(n)}_n ≤ [2κ{E W₂²(ν̂_n, μ_K) + W₂²(μ_{K,n}, μ_K)}]^{1/2} + Δ^{grid}_n`, with
`F_{+,K,n}` any finite-grid population map `Fg`. -/
def emp_bijective : Prop :=
  ∀ (K n : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure μ]
    (x : Fin n → Ω → EuclideanSpace ℝ (Fin K))
    (F Fg : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (u : Fin n → EuclideanSpace ℝ (Fin K))
    (f : EuclideanSpace ℝ (Fin K) → ℝ) (α L : ℝ) (σ : Ω → Equiv.Perm (Fin n)),
    1 ≤ n → 0 < α → α ≤ L → (∀ i, Measurable (x i)) → Measurable F → Measurable Fg →
    (∀ i, Measurable fun ω => u (σ ω i)) →
    (∀ᵐ ω ∂P, TwoSidedAt α L f u (fun i => x i ω) (fun i => F (x i ω))) →
    (∀ ω, IsOptAssign (fun i => x i ω) u (σ ω)) →
      rmsE P (fun ω i => ‖u (σ ω i) - Fg (x i ω)‖) ≤
        (ENNReal.ofReal (2 * (L / α)) *
          (∫⁻ ω, wassersteinEDist 2 (empMeasure fun i => F (x i ω)) μ ^ 2 ∂P +
            wassersteinEDist 2 (empMeasure u) μ ^ 2)) ^ (1 / 2 : ℝ) +
        rmsE P (fun ω i => ‖Fg (x i ω) - F (x i ω)‖)

/-! ### A `prop:app-entropic` -/

/-- The bound for one realisation: `n⁻¹Σ‖F̂^{bar}(x_i) − r_i‖² ≤ κ W₂²(ν̂_n, μ_{K,m}) + (ε/α) log min(n,m)`. -/
def entropic_two_sided_core : Prop :=
  ∀ (K n m : ℕ) (α L ε : ℝ) (f : EuclideanSpace ℝ (Fin K) → ℝ) (x r : Fin n → EuclideanSpace ℝ (Fin K))
    (u : Fin m → EuclideanSpace ℝ (Fin K)) (π : Matrix (Fin n) (Fin m) ℝ),
    1 ≤ n → 1 ≤ m → 0 < α → α ≤ L → 0 < ε → TwoSidedAt α L f u x r → IsEntPlan ε x u π →
      ENNReal.ofReal ((1 / n : ℝ) * ∑ i, ‖entBary π u i - r i‖ ^ 2) ≤
        ENNReal.ofReal (L / α) * wassersteinEDist 2 (empMeasure r) (empMeasure u) ^ 2 +
          ENNReal.ofReal (ε / α * Real.log (min n m))

/-- `eq:app-entropic-projected-bound`: `E[n⁻¹Σ‖F̂^{bar}(x_i) − F(x_i)‖²] ≤ 2κ{E W₂²(ν̂_n, μ_K) + W₂²(μ_{K,m}, μ_K)} +
(ε/α) log min(n,m)`, every `n, m ≥ 1`, `ε > 0`. -/
def app_entropic : Prop :=
  ∀ (K n m : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure μ]
    (x : Fin n → Ω → EuclideanSpace ℝ (Fin K))
    (F : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (u : Fin m → EuclideanSpace ℝ (Fin K))
    (f : EuclideanSpace ℝ (Fin K) → ℝ) (α L ε : ℝ) (π : Ω → Matrix (Fin n) (Fin m) ℝ),
    1 ≤ n → 1 ≤ m → 0 < α → α ≤ L → 0 < ε →
    (∀ᵐ ω ∂P, TwoSidedAt α L f u (fun i => x i ω) (fun i => F (x i ω))) →
    (∀ ω, IsEntPlan ε (fun i => x i ω) u (π ω)) →
      ∫⁻ ω, ENNReal.ofReal ((1 / n : ℝ) * ∑ i, ‖entBary (π ω) u i - F (x i ω)‖ ^ 2) ∂P ≤
        ENNReal.ofReal (2 * (L / α)) *
            (∫⁻ ω, wassersteinEDist 2 (empMeasure fun i => F (x i ω)) μ ^ 2 ∂P +
              wassersteinEDist 2 (empMeasure u) μ ^ 2) +
          ENNReal.ofReal (ε / α * Real.log (min n m))

/-- `eq:app-entropic-hilbert-bound`: `rms(ι_K F̂^{bar} − 𝔽_P) ≤ {RHS of eq:app-entropic-projected-bound}^{1/2} +
Δ^{sieve,L²}`. -/
def app_entropic_hilbert : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (K n m : ℕ) (Ω : Type) [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ι : EuclideanSpace ℝ (Fin K) →ₗᵢ[ℝ] H)
    (μ : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure μ]
    (x : Fin n → Ω → EuclideanSpace ℝ (Fin K))
    (F : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (u : Fin m → EuclideanSpace ℝ (Fin K))
    (f : EuclideanSpace ℝ (Fin K) → ℝ) (α L ε : ℝ) (π : Ω → Matrix (Fin n) (Fin m) ℝ)
    (FPX : Ω → Fin n → H),
    1 ≤ n → 1 ≤ m → 0 < α → α ≤ L → 0 < ε →
    (∀ i, Measurable fun ω => ‖entBary (π ω) u i - F (x i ω)‖) →
    (∀ i, Measurable fun ω => ‖ι (F (x i ω)) - FPX ω i‖) →
    (∀ᵐ ω ∂P, TwoSidedAt α L f u (fun i => x i ω) (fun i => F (x i ω))) →
    (∀ ω, IsEntPlan ε (fun i => x i ω) u (π ω)) →
      rmsE P (fun ω i => ‖ι (entBary (π ω) u i) - FPX ω i‖) ≤
        (ENNReal.ofReal (2 * (L / α)) *
            (∫⁻ ω, wassersteinEDist 2 (empMeasure fun i => F (x i ω)) μ ^ 2 ∂P +
              wassersteinEDist 2 (empMeasure u) μ ^ 2) +
          ENNReal.ofReal (ε / α * Real.log (min n m))) ^ (1 / 2 : ℝ) +
        rmsE P (fun ω i => ‖ι (F (x i ω)) - FPX ω i‖)

end Claims

end StatFormal.OTFD.Wave16b
