import StatFormal.Archive.OTFD.Wave13b.Statements
import StatFormal.Archive.OTFD.Wave7a.Statements
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Analysis.Convex.Topology

/-!
# FROZEN STATEMENTS — otfd wave 14c (QUEUE rows 128–134): R `lem:convex`, R `lem:boundary`,
# B `prop:vector-directional-reduction`, B `prop:band-nesting`, B `cor:rk-functionals`,
# B `prop:rk-linear-certificate` (B `prop:certified-band-weighted`: already certified, see below)

Sources (verbatim in `lean-formalisation/inventory/extracted/otfd-R_robustness.md` and `otfd-B_bands.md`; current
text of 2026-10-14, paths under `otfd/papers/`):
* R `lem:convex` (`R_robustness/sections/appendix_a.tex:8-16`), proof `:18-24` (as corrected 2026-10-14 for `α ≥ 1`,
  DEFECTS #49), with `eq:TDH` (`s2_setting.tex:8-10`) and `D_α` (`s3_infinite.tex:8`).
* R `lem:boundary` (`R_robustness/sections/s5_families.tex:6-9`), proof `:11-15`, with `β(A;ν) = inf_{u∈A} TD(u;ν)`
  (`s2_setting.tex:75`).
* B `prop:vector-directional-reduction` (`B_bands/supplement.tex:2764-2778`), proof `:2780-2785`, with the setup
  `eq:vector-band-reconstruction` and `H_p(t,v)` (`:2725-2762`).
* B `prop:band-nesting` (`B_bands/supplement.tex:4703-4713`), proof `:4715-4718`, with `prop:band-certificate`
  (i)–(iv) (`B_bands/main.tex:720-753`).
* B `cor:rk-functionals` (`B_bands/supplement.tex:5397-5408`), proof `:5589-5596`, using the event of
  `prop:rk-scenario-set` (`:5379-5392`).
* B `prop:rk-linear-certificate` (`B_bands/supplement.tex:5662-5674`), proof `:5676-5680`.
* B `prop:certified-band-weighted` (`B_bands/supplement.tex:1170-1180`): **no new claim** — both displayed claims are
  the frozen, certified `Wave2.Claims.weighted_slack` (target `cor:certified-band-rate (weighted_slack)`). The
  remaining input, `H^∂ = max_{J₀}⟨v,Z_j⟩`, belongs to `prop:certified-band-limit` (not in this wave).
Reuses, imported and not copied: `tdH`, `depthRegionH` (frozen Wave 13b); `tukeyDepth`, `regionDepth` (Wave 1);
`gap`, `score`, `Qent`, `simplex`, `IsSimplexProj`, `mnormSq` (Bands); `hsup`, `edgeUp`, `edgeLo`, `curve`, `band`
(Bands2); `cappedSimplex`, `mnorm`, `kappaM` (Wave 2); `dotCLM` (Wave 4); `oosA`, `oosB`, `rawScore`, `baryMap`,
`laguerre`, `IsProx`, `karpMap` (Wave 7a). This file **extends** Wave 13b: `compact_region` already gives `D_α`
compact and convex on complete separable `𝓗`; `convex_closed` drops completeness and separability, and the
halfspace representation with `q_v ∈ (−∞, +∞]` is new.

Covered:
* `lem:convex`: `convex_closed` (`D_α` closed and convex), `convex_halfline` (`{t : g_v(t) ≥ α} = [q_v, ∞)` as a
  set of reals, `q_v > −∞`, and `q_v < +∞` when `α < 1`; when the set is empty `q_v = +∞`), `convex_repr`
  (`D_α = ⋂_{v≠0} {u : ⟨v,u⟩ ≥ q_v}`, each halfspace closed and convex, empty when `q_v = +∞`).
* `lem:boundary`: `boundary_depth` (`TD(u;ν) = 0` at every boundary point `u` of `C`, the proof's conclusion) and
  `boundary_region` (`β(A;ν) = 0` when `A` meets `∂C`).
* `prop:vector-directional-reduction`: `vec_reduction_support` (`H_p(t,v)` is attained and equals
  `vᵀ𝔪(t) + max_{u∈A} ℓ(t,v)ᵀQ̂(u)`, the latter attained), `vec_reduction_boundary` (for `Q̂ = ½M⁻¹∇ψ`, `ψ`
  convex differentiable, the maximum of `ℓᵀQ̂` over `∂A` exists and equals the maximum over `A`),
  `vec_reduction_min` (the minimum is `−H_p(t,−v)`), `vec_reduction_extensions` ("consequently … for all three
  extensions": entropic, quadratic, Karp/Moreau–Yosida, `sup_A = sup_{∂A}` for every coefficient direction).
* `prop:band-nesting`: `nesting_gap` (`δ_j(p) ≥ δ_j(p')`), `nesting_knapsack` (the knapsack values are monotone in
  the caps), `nesting_band_ent`, `nesting_band_quad` (caps, both certified edges, and `B̄(p) ⊆ B̄(p')`, for the
  entropic resp. quadratic caps), `nesting_exact` (the same for `x̂↑, x̂↓` and their band, any map),
  `nesting_dual` (caps from one fixed family of dual candidates of `prop:band-certificate`(ii)).
* `cor:rk-functionals`: `rk_functionals` (on the scenario event, simultaneously for every Lipschitz functional,
  both bounds) and `rk_functionals_integral` (`L(x) = ∫ a x` is `‖a‖_{L¹}`-Lipschitz).
* `prop:rk-linear-certificate`: `rk_linear_identity` (`L(x_u) = L(𝔪) + ⟨b, Q̂(u)⟩`, `sup_u L(x_u) = L(𝔪) + h(b)`,
  and every feasible `u` is a lower bound), `rk_linear_ent`, `rk_linear_quad` (the knapsack bound with the
  `L`-independent caps), `rk_linear_boundary` (`sup_A = sup_{∂A}` for both maps).

Not covered (declared):
* `lem:convex`: nothing omitted. The Lean statement holds on every real inner-product space (no completeness or
  separability) — a generalisation.
* `lem:boundary`: nothing omitted. `ν` is a probability on `ℝ^K` with every affine hyperplane null.
* `prop:vector-directional-reduction`: the setup sentences (compactness of `𝒳_p` and `S_p(t)`, the sup-norm
  continuity of `u ↦ x_u`, measurability of `Q̂`); the remarks after the proposition (not concave, the boundary
  probe). Claims are pointwise in `t` (`𝔪(t)`, `E(t)` are an arbitrary vector and matrix), which is all the
  proposition uses. `vec_reduction_extensions` is in the `sup`-equality form of the frozen `band_boundary_sup`
  (attainment needs continuity of the map, entered only in `vec_reduction_boundary`).
* `prop:band-nesting`: that `A_{K,p} ⊆ A_{K,p'}` for `p ≤ p'` (the paper's "chosen nested in `p`"; entered as
  `A ⊆ A'`); the convex-program remark of (i).
* `cor:rk-functionals`: `prop:rk-scenario-set` itself (certified as Wave 3 `rk_scenario_set`; its event enters as a
  hypothesis in measurable-event form, as in the frozen `calibrated_envelope`). `rk_functionals_integral` is stated
  on the curves `x` with `a·x` integrable (on `C(𝒯)`, `𝒯` compact, every curve qualifies).
* `prop:rk-linear-certificate`: continuity of `L` (unused: any linear functional, a generalisation); "attained on
  `∂A`" is the `sup`-equality form (no attainment claim for the quadratic map, whose continuity is not proved here).

Encodings (see card):
* `lem:convex`: `g_v(t) = distFn μ v t = μ{z : ⟨v,z⟩ ≤ t} ∈ [0,1]`, `α : ℝ≥0∞`, `0 < α`;
  `q_v = qLevel μ α v = inf{t : g_v(t) ≥ α}` in `EReal` (the empty infimum is `⊤ = +∞`, the paper's convention, not
  a junk value); "`[q_v, ∞)`" is `{t : ℝ | q_v ≤ t}`, "`q_v ∈ ℝ` when `α < 1`" is `⊥ < q_v < ⊤`. Halfspaces are
  `{u : q_v ≤ ⟨v,u⟩}` with `⟨v,u⟩` cast to `EReal`. `μ` is a Borel probability on any real inner-product space.
* `lem:boundary`: `ℝ^K = EuclideanSpace ℝ (Fin K)`, `TD = tukeyDepth`, `β = regionDepth` (frozen Wave 1); "zero mass
  to every hyperplane" is `∀ w ≠ 0, ∀ c, ν{z : ⟨w,z⟩ = c} = 0`; `C = closedConvexHull ℝ (supp ν)` with Mathlib's
  `Measure.support`; "boundary" is `frontier`.
* Vector: `ℝ^D = Fin D → ℝ`, outputs `Fin d → ℝ`, `x_u(t) = 𝔪 + E Q̂(u)` (`vecCurve`), `ℓ(t,v) = Eᵀv`;
  `H_p(t,v) = vecH = sSup` of a set shown to have a greatest element (no junk). `Q̂ = ½M⁻¹∇ψ` with `ψ` convex
  differentiable is `ConvexOn ψ` and `HasFDerivAt ψ (dotCLM (2 • M Q̂(u))) u` for every `u` (the Wave 7a form).
  `A` nonempty compact (convexity unused), `Q̂` continuous on `A` (the setup), `D ≥ 1`. The three maps are those of
  the certified Wave 7a `oos_ent_potential`, `oos_quad_potential` (any selection of the projection), `karp_potential`.
* Nesting: caps `κ_j = e^{−δ_j/ε}` (`entCaps`), `(1 − mδ_j/γ)_+` (`quadCaps`), with `δ_j = gap a b A j` (frozen
  Bands; nonempty `A`); certified edges `x̄↑ = 𝔪 + max{Σ q_j c_j : q ∈ Δ_n, q_j ≤ κ_j}`, `x̄↓ = 𝔪 + min{…}`
  (`certUp`, `certLo`), `c_j(t) = ⟨e(t), Z_j⟩`, the max/min as `EReal` `⨆/⨅` over `cappedSimplex` (an empty capped
  simplex gives `⊥`/`⊤`: an empty band, not a junk real). `B̄(p)` is the Bands2 `band`. Dual caps: for a fixed nonempty
  family `w^{(1)},…,w^{(N)} ∈ Δ_n`, `δ̃_j(A) = max_i [Σ_k w^{(i)}_k a_k − a_j − σ_A(v_j^{w^{(i)}})]` (`dualGap`),
  `σ_A = sSup` over the nonempty bounded `A` (no junk).
* `cor:rk-functionals`: as in the frozen `calibrated_envelope`: `M.PosDef`, `κ(t) = kappaM M (e t)`, `C_K` any bound
  `≥ κ(t)`, curves `curve mo e c`, the event `{ŝ < 1 → (∃ u ∈ A, ‖ΠX − Q̂u‖_M ≤ η̂_e) ∧ ‖X − x_{[ΠX]}‖_∞ ≤ η̂_r}`
  with a measurable subset of probability `≥ 1 − α`. "`Λ`-Lipschitz for the sup-norm" is on any class `𝔉` of curves
  containing `X_{n+1}` and every `x_u`: `x, y ∈ 𝔉`, `|x(t) − y(t)| ≤ r ∀t ⇒ |L x − L y| ≤ Λr`. `sup/inf_u L(x_u)` are
  `EReal` `⨆/⨅` (no junk). `‖a‖_{L¹} = ∫|a|` for integrable `a`.
* `prop:rk-linear-certificate`: curves form any real vector space `F`, `L : F →ₗ[ℝ] ℝ`, `x_u = 𝔪 + Σ_k Q̂(u)_k e_k`
  (`recon`), `b = (L(e_k))_k` (`lfCoef`); `L(𝔪) + h_{K,p}(b)` is the Bands2 `edgeUp Q̂ A (L 𝔪) b`. Entropic map =
  frozen `Qent` with intercepts/slopes `oosA`, `oosB` (Wave 7a); quadratic map = `Σ_j q_j(u)Z_j` for a selection of
  the projection of `rawScore (γ/m)`; caps from the exact gaps `gap (oosA) (oosB) A`; `n ≥ 1` (for `n = 0` the
  capped simplex is empty).
* All types are in `Type` (universe 0), as elsewhere in the repo.

Critic notes:
* `lem:convex` as corrected is right: the `α ≥ 1` case gives `q_v = +∞` (Gaussian, `α = 1`) or a finite `q_v`
  (bounded support, `α = 1`). For `v = 0` the claims also hold, but are stated for `v ≠ 0` as printed.
* `lem:boundary` is right in every dimension; the empty-interior case of `C` cannot occur for `K ≥ 1` (`supp ν`
  would lie in a null hyperplane), and the route handles it by the hyperplane itself. For `K = 0`, `∂C = ∅`.
* `prop:band-nesting` "for caps computed from the dual bounds … since `σ_{A_p} ≤ σ_{A_{p'}}`" needs the exact support
  function (or monotone upper bounds); with arbitrary upper bounds per level it can fail. Encoded with the exact `σ`.
  Scope note (S4): for the cubic law (ii) uses a bisection *upper bound* on `σ_{A_p}`; the dual-cap nesting then
  needs that computed bound to be nondecreasing in `p` (true for the ball and box caps, not argued for the bisection).
* `rk_linear_ent`/`rk_linear_quad` use the exact-gap caps; caps from lower bounds on `δ_j` (also allowed by the paper)
  follow from the same proof but are not stated.
* `prop:rk-linear-certificate` needs `n ≥ 1` (implicit; `Δ_0 = ∅`).
* Critic (2026-10-14): ACCEPT / ACCEPT-WITH-NOTE, all TRUE. `lem:convex` matches the corrected proof (EReal `q_v`,
  `inf ∅ = ⊤` is the paper's convention); `vec_reduction_extensions` states `sup = sup_∂` but not attainment (all
  three maps are continuous, so it holds); band-nesting: the computed cubic-law bisection bound is monotone in `p`
  in exact arithmetic (bracket independent of `r`, monotone inside test; `package/src/otfd/bands/region.py`), so
  dual-cap nesting holds — the paper should say so in one clause (S4, DEFECTS #51); nesting of the reported caps
  `κ ∧ κ^sat` is not claimed. `prop:certified-band-weighted` is already certified as `Wave2.Claims.weighted_slack`
  (it still needs `x^{↑,∂} = 𝔪 + M₀` from `prop:certified-band-limit`).
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Finset Matrix
open scoped InnerProductSpace ENNReal

namespace StatFormal.OTFD.Wave14c

open StatFormal.OTFD.Wave1 (tukeyDepth regionDepth)
open StatFormal.OTFD.Wave13b (tdH depthRegionH)
open StatFormal.OTFD.Bands (simplex gap score Qent IsSimplexProj)
open StatFormal.OTFD.Bands2 (hsup edgeUp edgeLo curve band)
open StatFormal.OTFD.Wave2 (cappedSimplex mnorm kappaM)
open StatFormal.OTFD.Wave4 (dotCLM)
open StatFormal.OTFD.Wave7a (oosA oosB rawScore baryMap laguerre IsProx karpMap)

/-! ### R `lem:convex` -/

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]

/-- `g_v(t) = μ{z : ⟨v, z⟩ ≤ t}`. -/
def distFn (μ : Measure H) (v : H) (t : ℝ) : ℝ≥0∞ := μ {z | ⟪v, z⟫_ℝ ≤ t}

/-- `q_v = inf{t : g_v(t) ≥ α} ∈ [−∞, +∞]` (`inf ∅ = +∞`). -/
def qLevel (μ : Measure H) (α : ℝ≥0∞) (v : H) : EReal :=
  ⨅ (t : ℝ) (_ : α ≤ distFn μ v t), (t : EReal)

end Hilbert

/-! ### B `prop:vector-directional-reduction` -/

section Vector
variable {d D : ℕ}

/-- `x_u(t) = 𝔪(t) + E(t) Q̂(u)` at a fixed `t`, for a coefficient vector `c = Q̂(u)`. -/
def vecCurve (mo : Fin d → ℝ) (E : Matrix (Fin d) (Fin D) ℝ) (c : Fin D → ℝ) : Fin d → ℝ := mo + E *ᵥ c

/-- `H_p(t,v) = max_{u∈A} vᵀ x_u(t)`. -/
def vecH (Q : (Fin D → ℝ) → Fin D → ℝ) (A : Set (Fin D → ℝ)) (mo : Fin d → ℝ)
    (E : Matrix (Fin d) (Fin D) ℝ) (v : Fin d → ℝ) : ℝ :=
  sSup ((fun u => v ⬝ᵥ vecCurve mo E (Q u)) '' A)

end Vector

/-! ### B `prop:band-nesting` -/

section Knapsack
variable {n K : ℕ}

/-- `max{Σ_j q_j c_j : q ∈ Δ_n, q_j ≤ κ_j}` (in `EReal`; `⊥` if the capped simplex is empty). -/
def knapUp (κ c : Fin n → ℝ) : EReal := ⨆ q ∈ cappedSimplex κ, ((∑ j, q j * c j : ℝ) : EReal)

/-- `min{Σ_j q_j c_j : q ∈ Δ_n, q_j ≤ κ_j}` (in `EReal`; `⊤` if the capped simplex is empty). -/
def knapLo (κ c : Fin n → ℝ) : EReal := ⨅ q ∈ cappedSimplex κ, ((∑ j, q j * c j : ℝ) : EReal)

/-- Certified upper edge `x̄↑(t) = 𝔪(t) + max{Σ_j q_j ⟨e(t), Z_j⟩ : q ∈ 𝒫_κ}` at `mo = 𝔪(t)`, `v = e(t)`. -/
def certUp (κ : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) (mo : ℝ) (v : Fin K → ℝ) : EReal :=
  (mo : EReal) + knapUp κ (fun j => v ⬝ᵥ Z j)

/-- Certified lower edge `x̄↓(t) = 𝔪(t) + min{Σ_j q_j ⟨e(t), Z_j⟩ : q ∈ 𝒫_κ}`. -/
def certLo (κ : Fin n → ℝ) (Z : Fin n → Fin K → ℝ) (mo : ℝ) (v : Fin K → ℝ) : EReal :=
  (mo : EReal) + knapLo κ (fun j => v ⬝ᵥ Z j)

/-- Entropic caps `κ_j = e^{−δ_j/ε}`. -/
def entCaps (ε : ℝ) (δ : Fin n → ℝ) : Fin n → ℝ := fun j => Real.exp (-δ j / ε)

/-- Quadratic caps `κ_j = (1 − m δ_j/γ)_+`. -/
def quadCaps (m : ℕ) (γ : ℝ) (δ : Fin n → ℝ) : Fin n → ℝ := fun j => max 0 (1 - m * δ j / γ)

/-- Support function `σ_A(v) = sup_{u∈A} ⟨v, u⟩` (used on nonempty bounded `A`). -/
def suppFnR (A : Set (Fin K → ℝ)) (v : Fin K → ℝ) : ℝ := sSup ((fun u => v ⬝ᵥ u) '' A)

/-- Dual gap bound from a fixed family of candidates:
`δ̃_j(A) = max_i [Σ_k w^{(i)}_k a_k − a_j − σ_A(b_j − Σ_k w^{(i)}_k b_k)]`. -/
def dualGap {N : ℕ} (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ) (A : Set (Fin K → ℝ)) (W : Fin N → Fin n → ℝ)
    (j : Fin n) : ℝ :=
  ⨆ i, (∑ k, W i k * a k - a j - suppFnR A (b j - ∑ k, W i k • b k))

end Knapsack

/-! ### B `prop:rk-linear-certificate` -/

section Linear
variable {K : ℕ} {F : Type*} [AddCommGroup F] [Module ℝ F]

/-- `x_c = 𝔪 + Σ_k c_k e_k` in a vector space of curves. -/
def recon (mo : F) (e : Fin K → F) (c : Fin K → ℝ) : F := mo + ∑ k, c k • e k

/-- `b = (L(e_1), …, L(e_K))`. -/
def lfCoef (L : F →ₗ[ℝ] ℝ) (e : Fin K → F) : Fin K → ℝ := fun k => L (e k)

end Linear

namespace Claims

/-! ### R `lem:convex` -/

/-- `D_α(μ)` is closed and convex for every Borel probability `μ` and `α > 0`. -/
def convex_closed : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure H) [IsProbabilityMeasure μ] (α : ℝ≥0∞), 0 < α →
      IsClosed (depthRegionH μ α) ∧ Convex ℝ (depthRegionH μ α)

/-- `{t : g_v(t) ≥ α} = [q_v, ∞)` (empty iff `q_v = +∞`), with `q_v > −∞`, and `q_v ∈ ℝ` when `α < 1`. -/
def convex_halfline : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure H) [IsProbabilityMeasure μ] (α : ℝ≥0∞), 0 < α → ∀ v : H, v ≠ 0 →
      {t : ℝ | α ≤ distFn μ v t} = {t : ℝ | qLevel μ α v ≤ (t : EReal)} ∧
      ⊥ < qLevel μ α v ∧ (α < 1 → qLevel μ α v < ⊤)

/-- `D_α(μ) = ⋂_{v≠0} {u : ⟨v,u⟩ ≥ q_v}`, an intersection of closed (convex) halfspaces. -/
def convex_repr : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure H) [IsProbabilityMeasure μ] (α : ℝ≥0∞), 0 < α →
      depthRegionH μ α = (⋂ (v : H) (_ : v ≠ 0), {u : H | qLevel μ α v ≤ ((⟪v, u⟫_ℝ : ℝ) : EReal)}) ∧
      ∀ v : H, IsClosed {u : H | qLevel μ α v ≤ ((⟪v, u⟫_ℝ : ℝ) : EReal)} ∧
        Convex ℝ {u : H | qLevel μ α v ≤ ((⟪v, u⟫_ℝ : ℝ) : EReal)}

/-! ### R `lem:boundary` -/

/-- At a boundary point `u` of `C = cl conv supp ν`, `TD(u;ν) = 0`, when `ν` charges no hyperplane. -/
def boundary_depth : Prop :=
  ∀ (K : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν],
    (∀ (w : EuclideanSpace ℝ (Fin K)) (c : ℝ), w ≠ 0 → ν {z | ⟪w, z⟫_ℝ = c} = 0) →
      ∀ u ∈ frontier (closedConvexHull ℝ ν.support), tukeyDepth ν u = 0

/-- `lem:boundary`: a region containing a boundary point of `C` has `β(A;ν) = 0`. -/
def boundary_region : Prop :=
  ∀ (K : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν],
    (∀ (w : EuclideanSpace ℝ (Fin K)) (c : ℝ), w ≠ 0 → ν {z | ⟪w, z⟫_ℝ = c} = 0) →
      ∀ A : Set (EuclideanSpace ℝ (Fin K)), (A ∩ frontier (closedConvexHull ℝ ν.support)).Nonempty →
        regionDepth ν A = 0

/-! ### B `prop:vector-directional-reduction` -/

/-- `eq:vector-directional-support`: `H_p(t,v)` is attained and `H_p(t,v) − vᵀ𝔪(t) = max_{u∈A} ℓ(t,v)ᵀQ̂(u)`. -/
def vec_reduction_support : Prop :=
  ∀ (d D : ℕ) (Q : (Fin D → ℝ) → Fin D → ℝ) (A : Set (Fin D → ℝ)) (mo : Fin d → ℝ)
    (E : Matrix (Fin d) (Fin D) ℝ) (v : Fin d → ℝ),
    IsCompact A → A.Nonempty → ContinuousOn Q A →
      IsGreatest ((fun u => v ⬝ᵥ vecCurve mo E (Q u)) '' A) (vecH Q A mo E v) ∧
      IsGreatest ((fun u => (Eᵀ *ᵥ v) ⬝ᵥ Q u) '' A) (vecH Q A mo E v - v ⬝ᵥ mo)

/-- Boundary representation: for `Q̂ = ½M⁻¹∇ψ`, `ψ` convex and differentiable, the maximum of `ℓ(t,v)ᵀQ̂` over
`∂A` exists and equals the maximum over `A`. -/
def vec_reduction_boundary : Prop :=
  ∀ (d D : ℕ) (Q : (Fin D → ℝ) → Fin D → ℝ) (A : Set (Fin D → ℝ)) (mo : Fin d → ℝ)
    (E : Matrix (Fin d) (Fin D) ℝ) (v : Fin d → ℝ) (M : Matrix (Fin D) (Fin D) ℝ) (ψ : (Fin D → ℝ) → ℝ),
    0 < D → IsCompact A → A.Nonempty → ContinuousOn Q A → M.PosDef → ConvexOn ℝ Set.univ ψ →
    (∀ u, HasFDerivAt ψ (dotCLM ((2 : ℝ) • (M *ᵥ Q u))) u) →
      IsGreatest ((fun u => (Eᵀ *ᵥ v) ⬝ᵥ Q u) '' frontier A) (vecH Q A mo E v - v ⬝ᵥ mo)

/-- The minimum of `vᵀx_u(t)` over `A` is `−H_p(t,−v)`. -/
def vec_reduction_min : Prop :=
  ∀ (d D : ℕ) (Q : (Fin D → ℝ) → Fin D → ℝ) (A : Set (Fin D → ℝ)) (mo : Fin d → ℝ)
    (E : Matrix (Fin d) (Fin D) ℝ) (v : Fin d → ℝ),
    IsCompact A → A.Nonempty → ContinuousOn Q A →
      IsLeast ((fun u => v ⬝ᵥ vecCurve mo E (Q u)) '' A) (-vecH Q A mo E (-v))

/-- "Consequently" for the three extensions (entropic, quadratic, Karp/Moreau–Yosida), in dimension `D ≥ 1`:
`sup_{u∈A} ⟨ℓ, Q̂(u)⟩ = sup_{u∈∂A} ⟨ℓ, Q̂(u)⟩` for every compact `A` and every `ℓ`, without injectivity. -/
def vec_reduction_extensions : Prop :=
  ∀ (D n : ℕ) (A : Set (Fin D → ℝ)) (ℓ : Fin D → ℝ) (M : Matrix (Fin D) (Fin D) ℝ) (Z : Fin n → Fin D → ℝ)
    (f : Fin n → ℝ),
    0 < D → 0 < n → IsCompact A → M.PosDef →
      (∀ ε : ℝ, 0 < ε → hsup (Qent ε M Z f) A ℓ = hsup (Qent ε M Z f) (frontier A) ℓ) ∧
      (∀ (lam : ℝ) (q : (Fin D → ℝ) → Fin n → ℝ), 0 < lam →
        (∀ u, IsSimplexProj (rawScore lam M f Z u) (q u)) →
          hsup (fun u => baryMap (q u) Z) A ℓ = hsup (fun u => baryMap (q u) Z) (frontier A) ℓ) ∧
      (∀ (β : Fin n → Fin D → ℝ) (θ : Fin n → ℝ) (ε₀ σ : ℝ) (L : Matrix (Fin D) (Fin D) ℝ)
          (P : (Fin D → ℝ) → Fin D → ℝ),
        0 < ε₀ → 0 < σ → L.transpose * L = M → (∀ y, IsProx (laguerre β θ) ε₀ y (P y)) →
          hsup (karpMap σ ε₀ L P) A ℓ = hsup (karpMap σ ε₀ L P) (frontier A) ℓ)

/-! ### B `prop:band-nesting` -/

/-- `A_{K,p} ⊆ A_{K,p'}` gives `δ_j(p) ≥ δ_j(p')`. -/
def nesting_gap : Prop :=
  ∀ (n K : ℕ) (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ) (A A' : Set (Fin K → ℝ)) (j : Fin n),
    A.Nonempty → A ⊆ A' → gap a b A' j ≤ gap a b A j

/-- The knapsack values are monotone in the caps: larger caps give a larger max and a smaller min. -/
def nesting_knapsack : Prop :=
  ∀ (n : ℕ) (κ κ' c : Fin n → ℝ), (∀ j, κ j ≤ κ' j) →
    knapUp κ c ≤ knapUp κ' c ∧ knapLo κ' c ≤ knapLo κ c

/-- Entropic caps: `κ_j(p) ≤ κ_j(p')`, `x̄↑_p ≤ x̄↑_{p'}`, `x̄↓_p ≥ x̄↓_{p'}` pointwise, and `B̄(p) ⊆ B̄(p')`. -/
def nesting_band_ent : Prop :=
  ∀ (n K : ℕ) (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ) (Z : Fin n → Fin K → ℝ) (A A' : Set (Fin K → ℝ))
    (ε : ℝ) (T : Type) (mo : T → ℝ) (e : T → Fin K → ℝ),
    A.Nonempty → A ⊆ A' → 0 < ε →
      (∀ j, entCaps ε (gap a b A) j ≤ entCaps ε (gap a b A') j) ∧
      (∀ t, certUp (entCaps ε (gap a b A)) Z (mo t) (e t) ≤ certUp (entCaps ε (gap a b A')) Z (mo t) (e t)) ∧
      (∀ t, certLo (entCaps ε (gap a b A')) Z (mo t) (e t) ≤ certLo (entCaps ε (gap a b A)) Z (mo t) (e t)) ∧
      band (fun t => certLo (entCaps ε (gap a b A)) Z (mo t) (e t))
          (fun t => certUp (entCaps ε (gap a b A)) Z (mo t) (e t)) ⊆
        band (fun t => certLo (entCaps ε (gap a b A')) Z (mo t) (e t))
          (fun t => certUp (entCaps ε (gap a b A')) Z (mo t) (e t))

/-- Quadratic caps `(1 − mδ_j/γ)_+`: the same nesting. -/
def nesting_band_quad : Prop :=
  ∀ (n K m : ℕ) (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ) (Z : Fin n → Fin K → ℝ) (A A' : Set (Fin K → ℝ))
    (γ : ℝ) (T : Type) (mo : T → ℝ) (e : T → Fin K → ℝ),
    A.Nonempty → A ⊆ A' → 0 < γ → 0 < m →
      (∀ j, quadCaps m γ (gap a b A) j ≤ quadCaps m γ (gap a b A') j) ∧
      (∀ t, certUp (quadCaps m γ (gap a b A)) Z (mo t) (e t) ≤
        certUp (quadCaps m γ (gap a b A')) Z (mo t) (e t)) ∧
      (∀ t, certLo (quadCaps m γ (gap a b A')) Z (mo t) (e t) ≤
        certLo (quadCaps m γ (gap a b A)) Z (mo t) (e t)) ∧
      band (fun t => certLo (quadCaps m γ (gap a b A)) Z (mo t) (e t))
          (fun t => certUp (quadCaps m γ (gap a b A)) Z (mo t) (e t)) ⊆
        band (fun t => certLo (quadCaps m γ (gap a b A')) Z (mo t) (e t))
          (fun t => certUp (quadCaps m γ (gap a b A')) Z (mo t) (e t))

/-- The exact edges `x̂↑, x̂↓` (any map) are nested directly from `A ⊆ A'`, and so is their band. -/
def nesting_exact : Prop :=
  ∀ (K : ℕ) (T : Type) (Q : (Fin K → ℝ) → Fin K → ℝ) (A A' : Set (Fin K → ℝ)) (mo : T → ℝ)
    (e : T → Fin K → ℝ),
    A ⊆ A' →
      (∀ t, edgeUp Q A (mo t) (e t) ≤ edgeUp Q A' (mo t) (e t)) ∧
      (∀ t, edgeLo Q A' (mo t) (e t) ≤ edgeLo Q A (mo t) (e t)) ∧
      band (fun t => edgeLo Q A (mo t) (e t)) (fun t => edgeUp Q A (mo t) (e t)) ⊆
        band (fun t => edgeLo Q A' (mo t) (e t)) (fun t => edgeUp Q A' (mo t) (e t))

/-- Caps from one fixed family of dual candidates `w^{(i)} ∈ Δ_n` at every level: `δ̃_j(p) ≥ δ̃_j(p')`
(because `σ_{A_p} ≤ σ_{A_{p'}}`), and the certified edges (entropic and quadratic caps) are nested. -/
def nesting_dual : Prop :=
  ∀ (n K N m : ℕ) (a : Fin n → ℝ) (b : Fin n → Fin K → ℝ) (Z : Fin n → Fin K → ℝ) (A A' : Set (Fin K → ℝ))
    (W : Fin N → Fin n → ℝ) (ε γ : ℝ) (T : Type) (mo : T → ℝ) (e : T → Fin K → ℝ),
    A.Nonempty → A ⊆ A' → Bornology.IsBounded A' → 0 < N → (∀ i, W i ∈ simplex n) →
    0 < ε → 0 < γ → 0 < m →
      (∀ j, dualGap a b A' W j ≤ dualGap a b A W j) ∧
      (∀ t, certUp (entCaps ε (dualGap a b A W)) Z (mo t) (e t) ≤
        certUp (entCaps ε (dualGap a b A' W)) Z (mo t) (e t)) ∧
      (∀ t, certLo (entCaps ε (dualGap a b A' W)) Z (mo t) (e t) ≤
        certLo (entCaps ε (dualGap a b A W)) Z (mo t) (e t)) ∧
      (∀ t, certUp (quadCaps m γ (dualGap a b A W)) Z (mo t) (e t) ≤
        certUp (quadCaps m γ (dualGap a b A' W)) Z (mo t) (e t)) ∧
      (∀ t, certLo (quadCaps m γ (dualGap a b A' W)) Z (mo t) (e t) ≤
        certLo (quadCaps m γ (dualGap a b A W)) Z (mo t) (e t))

/-! ### B `cor:rk-functionals` -/

/-- On the scenario-set event (measurable, probability `≥ 1 − α`; stated on `{ŝ < 1}`), simultaneously for every
functional `L` that is `Λ`-Lipschitz for the sup-norm on a class `𝔉` containing `X_{n+1}` and the `x_u`:
`L(X_{n+1}) ≤ sup_{u∈A} L(x_u) + Λ(η̂_r + C_Kη̂_e)` and `inf_{u∈A} L(x_u) − Λ(η̂_r + C_Kη̂_e) ≤ L(X_{n+1})`. -/
def rk_functionals : Prop :=
  ∀ (K : ℕ) (T Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (Q : (Fin K → ℝ) → Fin K → ℝ)
    (M : Matrix (Fin K) (Fin K) ℝ) (mo : T → ℝ) (e : T → Fin K → ℝ) (X : Ω → T → ℝ)
    (PiX : Ω → Fin K → ℝ) (A : Ω → Set (Fin K → ℝ)) (shat ηe ηr : Ω → ℝ) (α CK : ℝ),
    M.PosDef → (∀ t, kappaM M (e t) ≤ CK) →
    (∃ S : Set Ω, MeasurableSet S ∧ ENNReal.ofReal (1 - α) ≤ P S ∧
      S ⊆ {ω | shat ω < 1 → (∃ u ∈ A ω, mnorm M (PiX ω - Q u) ≤ ηe ω) ∧
        ∀ t, |X ω t - curve mo e (PiX ω) t| ≤ ηr ω}) →
    ∃ S : Set Ω, MeasurableSet S ∧ ENNReal.ofReal (1 - α) ≤ P S ∧
      S ⊆ {ω | shat ω < 1 → ∀ (𝔉 : Set (T → ℝ)) (L : (T → ℝ) → ℝ) (Λ : ℝ),
        (∀ x ∈ 𝔉, ∀ y ∈ 𝔉, ∀ r : ℝ, (∀ t, |x t - y t| ≤ r) → |L x - L y| ≤ Λ * r) →
        X ω ∈ 𝔉 → (∀ u ∈ A ω, curve mo e (Q u) ∈ 𝔉) →
          ((L (X ω) : ℝ) : EReal) ≤
              (⨆ u ∈ A ω, ((L (curve mo e (Q u)) : ℝ) : EReal)) + ((Λ * (ηr ω + CK * ηe ω) : ℝ) : EReal) ∧
          (⨅ u ∈ A ω, ((L (curve mo e (Q u)) : ℝ) : EReal)) - ((Λ * (ηr ω + CK * ηe ω) : ℝ) : EReal) ≤
              ((L (X ω) : ℝ) : EReal)}

/-- `L(x) = ∫ a x` is `‖a‖_{L¹}`-Lipschitz for the sup-norm on the curves with `a x` integrable. -/
def rk_functionals_integral : Prop :=
  ∀ (T : Type) [MeasurableSpace T] (ρT : Measure T) (a : T → ℝ), Integrable a ρT →
    ∀ x y : T → ℝ, Integrable (fun t => a t * x t) ρT → Integrable (fun t => a t * y t) ρT →
      ∀ r : ℝ, (∀ t, |x t - y t| ≤ r) →
        |(∫ t, a t * x t ∂ρT) - ∫ t, a t * y t ∂ρT| ≤ (∫ t, |a t| ∂ρT) * r

/-! ### B `prop:rk-linear-certificate` -/

/-- `L(x_u) = L(𝔪) + ⟨b, Q̂(u)⟩`, `sup_{u∈A} L(x_u) = L(𝔪) + h_A(b)`, and every feasible `u` is a lower bound. -/
def rk_linear_identity : Prop :=
  ∀ (K : ℕ) (F : Type) [AddCommGroup F] [Module ℝ F] (L : F →ₗ[ℝ] ℝ) (mo : F) (e : Fin K → F)
    (Q : (Fin K → ℝ) → Fin K → ℝ) (A : Set (Fin K → ℝ)),
    (∀ u, L (recon mo e (Q u)) = L mo + lfCoef L e ⬝ᵥ Q u) ∧
    (⨆ u ∈ A, ((L (recon mo e (Q u)) : ℝ) : EReal)) = edgeUp Q A (L mo) (lfCoef L e) ∧
    ∀ u ∈ A, ((L (recon mo e (Q u)) : ℝ) : EReal) ≤ edgeUp Q A (L mo) (lfCoef L e)

/-- Entropic map: `sup_{u∈A} L(x_u) ≤ L(𝔪) + max{Σ_j q_j ℓ_j : q ∈ Δ_n, q_j ≤ κ_j}`, `ℓ_j = ⟨b, Z_j⟩`, with the
`L`-independent caps `κ_j = e^{−δ_j/ε}`. -/
def rk_linear_ent : Prop :=
  ∀ (n K : ℕ) (ε : ℝ) (M : Matrix (Fin K) (Fin K) ℝ) (Z : Fin n → Fin K → ℝ) (f : Fin n → ℝ)
    (A : Set (Fin K → ℝ)) (F : Type) [AddCommGroup F] [Module ℝ F] (L : F →ₗ[ℝ] ℝ) (mo : F) (e : Fin K → F),
    0 < n → 0 < ε → M.PosDef → A.Nonempty →
      edgeUp (Qent ε M Z f) A (L mo) (lfCoef L e) ≤
        certUp (entCaps ε (gap (oosA M f Z) (oosB M Z) A)) Z (L mo) (lfCoef L e)

/-- Quadratic map (`λ = γ/m`): the same bound with the caps `(1 − mδ_j/γ)_+`. -/
def rk_linear_quad : Prop :=
  ∀ (n K m : ℕ) (γ : ℝ) (M : Matrix (Fin K) (Fin K) ℝ) (Z : Fin n → Fin K → ℝ) (f : Fin n → ℝ)
    (q : (Fin K → ℝ) → Fin n → ℝ) (A : Set (Fin K → ℝ)) (F : Type) [AddCommGroup F] [Module ℝ F]
    (L : F →ₗ[ℝ] ℝ) (mo : F) (e : Fin K → F),
    0 < n → 0 < γ → 0 < m → M.PosDef → A.Nonempty → (∀ u, IsSimplexProj (rawScore (γ / m) M f Z u) (q u)) →
      edgeUp (fun u => baryMap (q u) Z) A (L mo) (lfCoef L e) ≤
        certUp (quadCaps m γ (gap (oosA M f Z) (oosB M Z) A)) Z (L mo) (lfCoef L e)

/-- The supremum of `L(x_u)` over a compact `A` equals that over `∂A`, for the entropic and quadratic maps. -/
def rk_linear_boundary : Prop :=
  ∀ (n K m : ℕ) (ε γ : ℝ) (M : Matrix (Fin K) (Fin K) ℝ) (Z : Fin n → Fin K → ℝ) (f : Fin n → ℝ)
    (q : (Fin K → ℝ) → Fin n → ℝ) (A : Set (Fin K → ℝ)) (F : Type) [AddCommGroup F] [Module ℝ F]
    (L : F →ₗ[ℝ] ℝ) (mo : F) (e : Fin K → F),
    0 < n → 0 < K → M.PosDef → IsCompact A →
      (0 < ε → (⨆ u ∈ A, ((L (recon mo e (Qent ε M Z f u)) : ℝ) : EReal)) =
        ⨆ u ∈ frontier A, ((L (recon mo e (Qent ε M Z f u)) : ℝ) : EReal)) ∧
      (0 < γ → 0 < m → (∀ u, IsSimplexProj (rawScore (γ / m) M f Z u) (q u)) →
        (⨆ u ∈ A, ((L (recon mo e (baryMap (q u) Z)) : ℝ) : EReal)) =
          ⨆ u ∈ frontier A, ((L (recon mo e (baryMap (q u) Z)) : ℝ) : EReal))

end Claims
end StatFormal.OTFD.Wave14c
