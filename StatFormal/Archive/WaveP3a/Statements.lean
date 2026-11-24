import StatFormal.Archive.WaveP2a.Statements
import StatFormal.Archive.Wave23b.Statements
import StatFormal.Archive.OTFD.Wave12a.Statements
import StatFormal.Archive.OTFD.Wave7a.Statements
import TauCeti.Probability.Quantile

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave P3a (partial-audit wave 3c, B/G/R clause gaps): otfd B `prop:cubic-band-infinite`,
# `prop:trimmed-band`, `prop:band-injectivity`; R `thm:trimmed`, `thm:region-breakdown` (band half), `thm:elliptical`;
# G `cor:discretisation` (c), `prop:cap` (b)–(c)

Sources (current text, read 2026-10-16; paths under `otfd/papers/`):
* B `prop:cubic-band-infinite` (`B_bands/supplement.tex:951-982`), with `lem:interior-levels` (`:940-948`),
  `cor:matched-gaussian-cubic` (A); frozen `OTFD/Wave8c` `cubicLaw`, `cK`, `tauKp`, `rhoBox`; Wave 23a `popSupp`,
  `fitSupp`; WaveP2a `FixedKOOSInexact`, `band_pointwise_lower`; wave L1 `IsCMMapAE`.
* B `prop:trimmed-band` (`supplement.tex:997-1054`), with `thm:band-containment`, `thm:band-consistency` (frozen
  WaveP2a `band_containment_discharged`, OTFD Wave 22b `band_consistency`, Wave 17a `hPop`, Wave 21b `supE`,
  Wave 19a `extTop`).
* B `prop:band-injectivity` (`supplement.tex:4486-4508`, proof `:4510-4535`), with frozen OTFD Wave 7a `rawScore`,
  `baryMap`, `laguerre`, `IsProx`, `karpMap`, Bands `IsSimplexProj`.
* R `thm:trimmed` (`R_robustness/sections/s8_unbalanced.tex:119-140`, `def:trimmed` `:102-112`, proof
  `appendix_b.tex:285-317`), with `thm:entropic` (`s4_regions.tex:42-64`, proof `appendix_b.tex:3-49`); frozen OTFDR
  `piCond`, `Qhat`, `TrimKKT`, Lift `Contam`, `BP`, Wave 6b `halfMass`, `dMinus`, `regionSup`, Wave 12a `dPlus`,
  Wave 1 `tukeyDepth`, `regionDepth`.
* R `thm:region-breakdown`, last sentence (`s4_regions.tex:75-83`) with the remark after `def:bp`
  (`s2_setting.tex:53-63`) and `(S4)` (`:31-33`); frozen Wave 6b `EntSetting`, `regionSup`, Wave 12a
  `region_bp_unconditional`.
* R `thm:elliptical` (i) (`s3_infinite.tex:56-72`), with `lem:cm-null`; frozen Wave 23c `EllSetting`, `cmNorm`,
  `ellLaw`, OTFD Wave 13a `tukeyDepthH`, Wave 24e `cm_null`.
* G `cor:discretisation` (c) (`G_geodesic/supp_moved.tex:202-234`, proof (c) `:278-287`); frozen OTFD Wave 6b `sphDist`,
  `sphExp`, Wave 5b `GibbsHyp`, `gibbsMean`.
* G `prop:cap` (b), (c) (`G_geodesic/main.tex:407-447`, `def:reference` `:323-345`); frozen Wave 23b `gridInner`,
  `gridNorm`, `gridSup`, `GridOrthonormal`, `bK`.
All frozen objects are imported, not copied.

Covered:
* B `prop:cubic-band-infinite`: (i) `cubic_quantile_map` (`Q(u) = (λ_kΦ^{-1}(u_k/λ_k + ½))_k` pushes `μ_K` to
  `⊗N(0, λ_k²)`, is `μ_K`-a.e. cyclically monotone — a McCann Brenier map — and is continuous on `int 𝒰_K`); (ii)
  `cubic_popSupp_top` (`h^pop(v) = +∞ ⇔ v_k ≠ 0` for some `k ∈ 𝒦_p`); (iii) `cubic_K_nonempty_iff` (`𝒦_p ≠ ∅ ⇔
  p ≥ p*_K`), `cubic_containment_fails` (the bounded-range hypothesis of `thm:band-containment` fails); (iv)
  `cubic_edges_diverge` (entropic edges `→ ±∞` a.s., simultaneously in `p`, `t`).
* B `prop:trimmed-band`: (ii) `trimmed_containment` (finite trimmed population support; a.s. one-sided containment,
  no regularity), `trimmed_cube_support` (the cube's certified support bound); (iii) `trimmed_band_consistency`
  (almost surely, two-sided convergence uniform in `p ∈ (0, p̄]` and `t`, under `ass:fixedK-oos` as printed and the
  printed differentiability of `χ_K` on `O ⊇ A^{δ'}_{p̄}`), `trimmed_matched_edges`
  (`|x^{pop,δ'} − 𝔪| ≤ Φ^{-1}(1 − δ'/2)Σλ_k|e_k|`).
* B `prop:band-injectivity`: (i) `band_injectivity_contour_supset` (`Q̂(∂A) ⊆ ∂Q̂(A)` under the printed continuity and
  injectivity), and for local diffeomorphisms both inclusions: `band_injectivity_contour`; (iii)
  `band_injectivity_quad_const`, `band_injectivity_karp_const` (constant where the active set is a singleton, hence not
  injective), `band_injectivity_quad_affine` (all weights active: affine with the printed linear part, invertible and
  injective when the `Z_j` affinely span).
* R `thm:trimmed`: (b) `trimmed_b`; (c) `trimmed_c`; the closing display `trimmed_bp_general`, `trimmed_bp` (point),
  `trimmed_region_bp_general`, `trimmed_region_bp` (region).
* R `thm:region-breakdown`, band half: `band_region_bp_eq` (band and region have the same breakdown point),
  `band_bp_unconditional`, `band_bp_general_unconditional`.
* R `thm:elliptical` (i): `elliptical_cm_space` (`‖x‖_CM < ∞ ⇔ x ∈ ran Σ^{1/2}`, `‖Σ^{1/2}y‖_CM = ‖y‖`),
  `elliptical_positive_space` (`{TD_H > 0} = ran Σ^{1/2}`, dense, infinite-dimensional when `H` is),
  `elliptical_positive_null` (`μ`-null, Karhunen–Loève setting).
* G `cor:discretisation` (c), unit sphere: `disc_base_transport` (pointwise geometric step), `disc_base_cost` (the cost
  bound), `disc_base_rank` (the rank bound).
* G `prop:cap`: (b) `cap_support` (`supp μ` = closed unit ball of `S`), `cap_esssup` (`b_K` is the `μ`-essential
  supremum); (c) scalar part `cap_scale`.

Not covered (declared):
* B `prop:cubic-band-infinite` (iv): the certified edges and the edges of selected hard maps (`lem:band-pointwise-lower`
  variants, not formalised). The identification `Q_{±,K} = Q` is through McCann uniqueness (the certified WaveP2a
  `potential_consistency` under `FixedKOOSInexact`; no standalone uniqueness claim here).
* B `prop:trimmed-band` (ii): the certified band `B̄^{δ'}` and the `η`-inflation / nesting coverage sentences; (iii):
  the explicit rate `E_K sup ‖Q̂_n − Q‖` (only the convergence is stated), the hard-map variant; "the hypothesis holds
  for every `δ'` in the matched model" (needs `χ_K` explicitly; `cubic_quantile_map` gives the continuity of `Q` on
  `int 𝒰_K`, not the differentiability of `χ_K`).
* B `prop:band-injectivity` (i): the inclusion `∂Q̂(A) ⊆ Q̂(∂A)` for maps that are only continuous and injective
  (Brouwer's invariance of domain, not in Mathlib); the entropic instance of `band_injectivity_contour` (strict
  differentiability of `entMap` with invertible derivative is not formalised).
* R `thm:trimmed`: the data-dependent temperature; existence of the trimmed potentials for every sample (a premise,
  `TrimSetting`: the facts it asks hold for the minimiser of `def:trimmed` once it exists, which it does for compactly
  supported `ν`; no certified existence result for the trimmed dual is available to discharge it).
* R `thm:elliptical` (i): the identity `Var⟨v, G⟩ = ‖Σ^{1/2}v‖²` from the Karhunen–Loève series (a premise in
  `elliptical_positive_null`, consistent with it).
* G `cor:discretisation` (c) on Hadamard manifolds (Jacobi-field `cosh` comparison): RIEM-blocked. That `sphTransport`
  is the Levi-Civita parallel transport along the minimal geodesic is the encoding (no Riemannian layer).
* G `prop:cap` (c): the Riemannian clauses (`d_M(m(t), Y(t)) = s|v(t)|` within `0.9 inj(M)`, distance to the cut
  locus, minimising geodesics): RIEM-blocked. (d): interpretive (`s`, `ε` are functions of the design split, the
  reference draws independent of them) — no mathematical content beyond `IndepFun.comp`; not formalised. The
  continuum halves of (a), (b) (ess sup over `t ∼ λ`): grid only, as in the frozen Wave 23b.

Encodings (to be checked by the critic):
* B: `ℝ^K = EuclideanSpace ℝ (Fin K)`; `μ_K = cubicLaw` carried by `toLp` (`cubicLawE`, a measurable equivalence: no
  `map` junk), `P_K = ⊗ N(0, (2a_k)²)` (`gaussProdE`), half-widths `a_k = λ_k/2`; `Φ^{-1}` = Tau Ceti
  `Measure.quantile` of `N(0,1)` (junk value `0` outside `(0, 1)`, never used on `int 𝒰_K`); `A_{K,p}` = frozen
  `rhoBox ≤ tauKp` inside the box; `𝒦_p ≠ ∅` written `∃ k, 2a_k ≤ 2τ_{K,p}D_∞`; `p*_K = c_K(min λ/(2D_∞))` with the
  frozen `cK`; edges in `EReal` (`+∞`/`−∞` as `⊤`/`⊥`). Trimmed regions `A ∩ (1 − δ')𝒰_K` (pointwise scaling), in the
  cube coordinatewise; `𝒰_K = supp μ_K` with `0` interior (paper: the reference is centred).
* R: the band estimator `bandSup` (sup-norm over `t` of `x↑ = sup_A⟨e(t), Q̂⟩`, `x↓ = −sup_A⟨−e(t), Q̂⟩`, real
  suprema, bounded since `Q̂` is a convex combination and `e` bounded: no junk); bounded spanning `e` (paper: values of
  `K` continuous linearly independent functions on compact `𝒯`). `M_ℓ = (ℓ/n − α)/(1 − α)` (`trimM`); `TrimSetting`
  asks the frozen `TrimKKT` facts and that the row masses are the `ν`-integrals of `piCond`; "absolutely continuous" is
  `ν ≪ volume`; "up to `1/n`" is the bracket `[β, β + 1/n]`. Elliptical: `S = Σ^{1/2}` any self-adjoint bounded `S`
  with `Var⟨v, G⟩ = ‖Sv‖²` (i.e. `⟨Σv, v⟩ = ‖Σ^{1/2}v‖²`); infinite-dimensional = `¬ FiniteDimensional`.
* G (c): unit sphere `S^d ⊂ ℝ^{d+1}`, curves `ℝ → S^d` measurable, `λ` a probability on `ℝ`, `D` the `L²(λ)` distance
  of the frozen `sphDist`; `Γ` the explicit rotation of `span{m(t), m̂(t)}` (`⟨m, m̂⟩ > −1`); reference fields a Hilbert
  space with an evaluation map tangent along `m` and `∫‖ev v‖² ≤ ‖v‖²`; `Γ^{-1}F_{m̂}` = the rank map of the plan for the
  cost `c_{s,m̂}(Γv, x)` (identification `H_{m̂} ≅ H_m` by `Γ`). `prop:cap` (b): grid fields, `G = Σ√λ_k ξ_k φ_k`,
  `V = τG/‖G‖` (`V = 0` on the null event `G = 0`), `τ ∼ Unif(0,1]` independent of `ξ`; support = every `ε`-ball
  around a point of the unit ball of `S` has positive probability (with the a.s. inclusion).

Critic notes:
* Proved in `WaveP3a/Route{Band,Disc,Ell,Inj,CubicIff,CubicMap,CubicSupp,Trim,TrimBP,Cap}.lean`; kernel axioms
  `propext`, `Classical.choice`, `Quot.sound` only (checked by `#print axioms` and `example : Claims.X := X` for all 32).
* Thin claims (kept, flagged): `trimmed_cube_support` is Cauchy–Schwarz plus the box bound; `cap_scale` is an arithmetic
  corollary of the frozen Wave 23b `cap_sup` (with `cap_support`, the unit ball of `S` is `supp μ`);
  `band_bp_unconditional`, `band_bp_general_unconditional` are `band_region_bp_eq` composed with the frozen Wave 12a
  `region_bp_unconditional`, `region_bp_general_unconditional`. (iii) of `prop:trimmed-band` discharges the
  potential-convergence premise of the frozen Wave 22b `band_consistency` by the certified WaveP2a
  `potential_consistency` (and the soft-potential gradient inequality of the fitted entropic maps).
* Observations: `disc_base_cost` has slack (the proof gives `(s + B + D/2)D`; the printed `(s + B + D)D` is valid, not
  sharp, and so is the rank bound built on it); in `thm:trimmed` (b) the condition
  `ℓ ≥ nα` is not needed, and (c) needs only `Σ_O m ≥ M_ℓ` (always true by the caps), not the capping argument;
  `prop:band-injectivity` (iii)'s Karp statement holds with "active set" = the maximisers of the Laguerre potential at
  the proximal point. No statement was found false.

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace Matrix Pointwise

namespace StatFormal.WaveP3a

open StatFormal.OTFDR (piCond Qhat)
open StatFormal.OTFDR.Lift (Contam BP)
open StatFormal.OTFD.Wave1 (regionDepth)
open StatFormal.OTFD.Wave6b (dMinus EntSetting regionSup)

/-! ### R `thm:region-breakdown`: the band half -/

section Band
variable {K : ℕ}

/-- The band estimator of `def:bp`: the sup-norm over `t ∈ 𝒯` of the band edges `x↑(t) = sup_{u∈A}⟨e(t), Q̂(u)⟩`
and `x↓(t) = −sup_{u∈A}⟨−e(t), Q̂(u)⟩` (`(S4)`, `s2_setting.tex:31-33`), `Q̂` the fitted map recomputed on the sample. -/
def bandSup (ε : ℝ) {n : ℕ} (fsel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ)
    (A : Set (EuclideanSpace ℝ (Fin K))) {𝒯 : Type*} (e : 𝒯 → EuclideanSpace ℝ (Fin K))
    (Z' : Fin n → EuclideanSpace ℝ (Fin K)) : ℝ :=
  ⨆ t, max |⨆ u : A, ⟪e t, Qhat Z' (fsel Z') ε u⟫_ℝ| |-⨆ u : A, ⟪-e t, Qhat Z' (fsel Z') ε u⟫_ℝ|

end Band

/-! ### G `cor:discretisation` (c) on the unit sphere -/

section Sphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Parallel transport on the unit sphere along the minimal geodesic from `p` to `q` (`⟨p, q⟩ > −1`): the rotation of
the plane `span{p, q}` taking `p` to `q`, the identity on its orthogonal complement,
`Γ w = w − (⟨p + q, w⟩/(1 + ⟨p, q⟩))(p + q) + 2⟨p, w⟩ q`. -/
def sphTransport (p q w : E) : E :=
  w - (⟪p + q, w⟫_ℝ / (1 + ⟪p, q⟫_ℝ)) • (p + q) + (2 * ⟪p, w⟫_ℝ) • q

/-- The curve distance `D(y, x) = (∫ d_{S}(y(t), x(t))² dλ(t))^{1/2}` (`d_S` the frozen round distance). -/
def sphD (lam : Measure ℝ) (y x : ℝ → E) : ℝ := Real.sqrt (∫ t, StatFormal.OTFD.Wave6b.sphDist (y t) (x t) ^ 2 ∂lam)

/-- The cost `½ D(y, x)² = ½ ∫ d_S(y(t), x(t))² dλ(t)` (`eq:cost`). -/
def sphCost (lam : Measure ℝ) (y x : ℝ → E) : ℝ := (∫ t, StatFormal.OTFD.Wave6b.sphDist (y t) (x t) ^ 2 ∂lam) / 2

/-- The reference curve `E_m(sv)(t) = Exp_{m(t)}(s v(t))` (frozen `sphExp`). -/
def refCurve (m v : ℝ → E) (s : ℝ) : ℝ → E := fun t => StatFormal.OTFD.Wave6b.sphExp (m t) (s • v t)

/-- The reference curve at the estimated base, `E_{m̂}(sΓv)(t) = Exp_{m̂(t)}(s Γ_t v(t))`. -/
def refCurveHat (m mh v : ℝ → E) (s : ℝ) : ℝ → E :=
  fun t => StatFormal.OTFD.Wave6b.sphExp (mh t) (s • sphTransport (m t) (mh t) (v t))

end Sphere

/-! ### B `prop:cubic-band-infinite` -/

section Cubic
variable {N : ℕ}

/-- The cubic law `μ_K = ⊗_k Unif[−a_k, a_k]` (frozen `cubicLaw`, half-widths `a_k = λ_k/2`) carried to
`ℝ^K = EuclideanSpace ℝ (Fin K)` by the measurable equivalence `toLp`. -/
def cubicLawE (a : Fin N → ℝ) : Measure (EuclideanSpace ℝ (Fin N)) :=
  (StatFormal.OTFD.Wave8c.cubicLaw a).map (MeasurableEquiv.toLp 2 (Fin N → ℝ))

/-- The matched Gaussian `P_K = ⊗_k N(0, λ_k²)`, `λ_k = 2a_k`, on `ℝ^K`. -/
def gaussProdE (a : Fin N → ℝ) : Measure (EuclideanSpace ℝ (Fin N)) :=
  (Measure.pi fun k => gaussianReal 0 ((2 * a k) ^ 2).toNNReal).map (MeasurableEquiv.toLp 2 (Fin N → ℝ))

/-- The product quantile map `Q(u) = (λ_k Φ^{-1}(u_k/λ_k + ½))_k`, `λ_k = 2a_k`, `Φ^{-1}` the quantile function of
`N(0,1)` (Tau Ceti `Measure.quantile`; on `int 𝒰_K` the levels lie in `(0, 1)`). -/
def cubicGaussQ (a : Fin N → ℝ) (u : EuclideanSpace ℝ (Fin N)) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 fun k => 2 * a k * (gaussianReal 0 1).quantile (u k / (2 * a k) + 1 / 2)

/-- The cubic region `A_{K,p} = {u ∈ 𝒰_K : ρ_box(u) ≤ τ_{K,p}}` (frozen `rhoBox`, `tauKp`). -/
def cubicRegion (a : Fin N → ℝ) (Dinf p : ℝ) : Set (EuclideanSpace ℝ (Fin N)) :=
  {u | (∀ k, |u k| ≤ a k) ∧ StatFormal.OTFD.Wave8c.rhoBox Dinf (fun k => u k) ≤ StatFormal.OTFD.Wave8c.tauKp a Dinf p}

end Cubic

/-! ### G `prop:cap` (b), (c) on a grid -/

section CapRef
variable {J q K : ℕ}

/-- The rank-`K` Gaussian field on the grid in Karhunen–Loève form, `G = Σ_k √λ_k x_k φ_k` (`x = ξ` the standard
normal coordinates). -/
def gridG (lam : Fin K → ℝ) (φ : Fin K → Fin J → EuclideanSpace ℝ (Fin q)) (x : Fin K → ℝ) :
    Fin J → EuclideanSpace ℝ (Fin q) :=
  ∑ k, (Real.sqrt (lam k) * x k) • φ k

/-- The reference field `V = τ G/‖G‖` (`def:reference`; `V = 0` on the null event `G = 0`). -/
def gridV (w : Fin J → ℝ) (lam : Fin K → ℝ) (φ : Fin K → Fin J → EuclideanSpace ℝ (Fin q)) (x : Fin K → ℝ)
    (t : ℝ) : Fin J → EuclideanSpace ℝ (Fin q) :=
  (t / StatFormal.Wave23b.gridNorm w (gridG lam φ x)) • gridG lam φ x

end CapRef

/-! ### R `thm:trimmed` -/

section Trim
variable {K : ℕ}

/-- The standing hypotheses of `thm:trimmed`: `ν` a probability carried by `{‖u‖ ≤ D_ν}`, fixed `ε > 0`, `α ∈ (0, 1)`,
and for every sample `Z'` trimmed potentials `fsel Z'` with row masses `msel Z'` satisfying the facts of `eq:trim-kkt`
(frozen `TrimKKT`: `f ≤ 0`, masses positive, summing to `1`, capped by `1/(n(1−α))`, at the cap where `f_i < 0`), the
row masses being the integrals `∫ π(i|u) ν(du)` of the conditional law `eq:oos` (frozen `piCond`). -/
structure TrimSetting (ν : Measure (EuclideanSpace ℝ (Fin K))) (Dν ε α : ℝ) {n : ℕ}
    (fsel msel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ) : Prop where
  supp : ν {u | Dν < ‖u‖} = 0
  eps_pos : 0 < ε
  alpha_pos : 0 < α
  alpha_lt : α < 1
  kkt : ∀ Z', StatFormal.OTFDR.TrimKKT (fsel Z') (msel Z') α
  mass : ∀ Z' i, ∫ u, piCond Z' (fsel Z') ε u i ∂ν = msel Z' i

/-- `M_ℓ = (ℓ/n − α)/(1 − α)`. -/
def trimM (n ℓ : ℕ) (α : ℝ) : ℝ := ((ℓ : ℝ) / n - α) / (1 - α)

end Trim

namespace Claims

/-! ### R `thm:region-breakdown`, band half -/

/-- The remark after `def:bp`: when the evaluation functionals `e(t)` are bounded and span `ℝ^K`, the band edges'
sup-norm and `sup_{u∈A} ‖Q̂(u)‖` explode for the same contaminations, so the band and the region have the same
breakdown point — for every sample, temperature and choice of potentials, every nonempty `A`. -/
def band_region_bp_eq : Prop :=
  ∀ (K n : ℕ) (𝒯 : Type) (ε : ℝ) (fsel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ)
    (Z : Fin n → EuclideanSpace ℝ (Fin K)) (A : Set (EuclideanSpace ℝ (Fin K))) (e : 𝒯 → EuclideanSpace ℝ (Fin K)),
    A.Nonempty → (∃ C : ℝ, ∀ t, ‖e t‖ ≤ C) → Submodule.span ℝ (Set.range e) = ⊤ →
      BP (bandSup ε fsel A e) Z = BP (regionSup ε fsel A) Z

/-- `thm:region-breakdown`, last sentence, band half: for absolutely continuous `ν`, compact nonempty `A` and bounded
spanning evaluation functionals, the breakdown point of the band is `β(A;ν)` up to `1/n`. -/
def band_bp_unconditional : Prop :=
  ∀ (K n : ℕ) (𝒯 : Type) (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν] (ε : ℝ)
    (fsel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ) (Z : Fin n → EuclideanSpace ℝ (Fin K))
    (A : Set (EuclideanSpace ℝ (Fin K))) (e : 𝒯 → EuclideanSpace ℝ (Fin K)),
    0 < K → 1 ≤ n → ν ≪ volume → EntSetting ν ε fsel → IsCompact A → A.Nonempty →
    (∃ C : ℝ, ∀ t, ‖e t‖ ≤ C) → Submodule.span ℝ (Set.range e) = ⊤ →
      (regionDepth ν A).toReal ≤ BP (bandSup ε fsel A e) Z ∧
        BP (bandSup ε fsel A e) Z ≤ (regionDepth ν A).toReal + 1 / n

/-- The band half for every reference (the frozen `region_bp_general_unconditional` for the band):
`β⁻ ≤ BP(band) ≤ β⁻ + 1/n`, `β⁻ = inf_{u∈A} d⁻(u;ν)`. -/
def band_bp_general_unconditional : Prop :=
  ∀ (K n : ℕ) (𝒯 : Type) (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν] (ε : ℝ)
    (fsel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ) (Z : Fin n → EuclideanSpace ℝ (Fin K))
    (A : Set (EuclideanSpace ℝ (Fin K))) (e : 𝒯 → EuclideanSpace ℝ (Fin K)),
    0 < K → 1 ≤ n → EntSetting ν ε fsel → IsCompact A → A.Nonempty →
    (∃ C : ℝ, ∀ t, ‖e t‖ ≤ C) → Submodule.span ℝ (Set.range e) = ⊤ →
      (⨅ u ∈ A, dMinus ν u).toReal ≤ BP (bandSup ε fsel A e) Z ∧
        BP (bandSup ε fsel A e) Z ≤ (⨅ u ∈ A, dMinus ν u).toReal + 1 / n

/-! ### G `cor:discretisation` (c), unit sphere -/

/-- (c), the geometric step on the unit sphere: for unit `p, q` with `⟨p, q⟩ > −1` and `w` tangent at `p`, the
transport `Γw` is tangent at `q` with `‖Γw‖ = ‖w‖`, and `d_S(Exp_q(Γw), Exp_p(w)) ≤ d_S(p, q)` (the printed
"`D(E_{m̂}(sΓv), E_m(sv)) ≤ D(m, m̂)`", pointwise). -/
def disc_base_transport : Prop :=
  ∀ (d : ℕ) (p q w : EuclideanSpace ℝ (Fin (d + 1))), ‖p‖ = 1 → ‖q‖ = 1 → -1 < ⟪p, q⟫_ℝ → ⟪p, w⟫_ℝ = 0 →
    ⟪q, sphTransport p q w⟫_ℝ = 0 ∧ ‖sphTransport p q w‖ = ‖w‖ ∧
      StatFormal.OTFD.Wave6b.sphDist (StatFormal.OTFD.Wave6b.sphExp q (sphTransport p q w))
          (StatFormal.OTFD.Wave6b.sphExp p w) ≤ StatFormal.OTFD.Wave6b.sphDist p q

/-- (c), the cost bound on the unit sphere: for a reference field `v` tangent along `m` with `‖v‖_{H_m} ≤ 1`,
`s ≥ 0`, and a data curve `x` with `D(m, x) ≤ B`,
`|c_{s,m̂}(Γv, x) − c_{s,m}(v, x)| ≤ (s + B + D(m, m̂)) D(m, m̂)`. -/
def disc_base_cost : Prop :=
  ∀ (d : ℕ) (lam : Measure ℝ) [IsProbabilityMeasure lam] (m mh v x : ℝ → EuclideanSpace ℝ (Fin (d + 1))) (s B : ℝ),
    Measurable m → Measurable mh → Measurable v → Measurable x →
    (∀ t, ‖m t‖ = 1) → (∀ t, ‖mh t‖ = 1) → (∀ t, ‖x t‖ = 1) → (∀ t, -1 < ⟪m t, mh t⟫_ℝ) →
    (∀ t, ⟪m t, v t⟫_ℝ = 0) → Integrable (fun t => ‖v t‖ ^ 2) lam → ∫ t, ‖v t‖ ^ 2 ∂lam ≤ 1 → 0 ≤ s →
    sphD lam m x ≤ B →
      |sphCost lam (refCurveHat m mh v s) x - sphCost lam (refCurve m v s) x| ≤
        (s + B + sphD lam m mh) * sphD lam m mh

/-- (c), the rank bound on the unit sphere: `∫ ‖Γ^{-1}F_{m̂} − F_m‖ dP ≤ (s + B + D(m, m̂)) D(m, m̂)/ε`. The reference
fields are a Hilbert space `H_m` (`Hs`) with evaluation `ev` (tangent along `m`, `∫‖ev v‖² dλ ≤ ‖v‖²`), `μ`-a.s.
`‖v‖ ≤ 1`; the data curves `X x` satisfy `D(m, X x) ≤ B` (`ass:bounded`). Identifying `H_{m̂}` with `H_m` by `Γ`,
`Γ^{-1}F_{m̂}` is the rank map (`gibbsMean`, `ψ = id`) of the entropic plan between `μ` and `P` for the cost
`c_{s,m̂}(Γv, x)`. -/
def disc_base_rank : Prop :=
  ∀ (d : ℕ) (Hs 𝒳 : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℝ Hs] [CompleteSpace Hs] [MeasurableSpace Hs]
    [BorelSpace Hs] [SecondCountableTopology Hs] [MeasurableSpace 𝒳]
    (μ : Measure Hs) (P : Measure 𝒳) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (lam : Measure ℝ) [IsProbabilityMeasure lam] (m mh : ℝ → EuclideanSpace ℝ (Fin (d + 1)))
    (ev : Hs → ℝ → EuclideanSpace ℝ (Fin (d + 1))) (X : 𝒳 → ℝ → EuclideanSpace ℝ (Fin (d + 1)))
    (s B ε : ℝ) (f f' : Hs → ℝ) (g g' : 𝒳 → ℝ),
    Measurable m → Measurable mh → (∀ t, ‖m t‖ = 1) → (∀ t, ‖mh t‖ = 1) → (∀ t, -1 < ⟪m t, mh t⟫_ℝ) →
    (∀ v, Measurable (ev v)) → (∀ v t, ⟪m t, ev v t⟫_ℝ = 0) →
    (∀ v, Integrable (fun t => ‖ev v t‖ ^ 2) lam ∧ ∫ t, ‖ev v t‖ ^ 2 ∂lam ≤ ‖v‖ ^ 2) →
    (∀ x, Measurable (X x)) → (∀ x t, ‖X x t‖ = 1) → (∀ x, sphD lam m (X x) ≤ B) →
    0 ≤ s → 0 < ε → (∀ᵐ v ∂μ, ‖v‖ ≤ 1) →
    Measurable (fun z : Hs × 𝒳 => sphCost lam (refCurve m (ev z.1) s) (X z.2)) →
    Measurable (fun z : Hs × 𝒳 => sphCost lam (refCurveHat m mh (ev z.1) s) (X z.2)) →
    StatFormal.OTFD.Wave5b.GibbsHyp μ P ε (fun z => sphCost lam (refCurve m (ev z.1) s) (X z.2)) f g →
    StatFormal.OTFD.Wave5b.GibbsHyp μ P ε (fun z => sphCost lam (refCurveHat m mh (ev z.1) s) (X z.2)) f' g' →
      ∫⁻ x, ‖StatFormal.OTFD.Wave5b.gibbsMean μ ε (fun z => sphCost lam (refCurveHat m mh (ev z.1) s) (X z.2)) f' g'
              id x -
          StatFormal.OTFD.Wave5b.gibbsMean μ ε (fun z => sphCost lam (refCurve m (ev z.1) s) (X z.2)) f g id x‖ₑ ∂P ≤
        ENNReal.ofReal ((s + B + sphD lam m mh) * sphD lam m mh / ε)

/-! ### R `thm:elliptical` (i): the Cameron–Martin space -/

/-- `thm:elliptical`, the Cameron–Martin norm on and off `ran Σ^{1/2}`: if `Var⟨v, G⟩ = ‖Sv‖²` for a self-adjoint
bounded `S` (`S = Σ^{1/2}`, so `⟨Σv, v⟩ = ‖Sv‖²`) on a Hilbert space, then `‖x‖_CM < ∞` iff `x ∈ ran S`, and
`‖Sy‖_CM = ‖y‖` (`= ‖Σ^{-1/2}(Sy)‖`; `+∞` off `ran S`). -/
def elliptical_cm_space : Prop :=
  ∀ (Ω H : Type) [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [Nontrivial H] (Pr : Measure Ω) (G : Ω → H) (W : Ω → ℝ) (S : H →L[ℝ] H),
    StatFormal.Wave23c.EllSetting Pr G W → (∀ v w, ⟪S v, w⟫_ℝ = ⟪v, S w⟫_ℝ) →
    (∀ v, Var[fun ω => ⟪v, G ω⟫_ℝ; Pr] = ‖S v‖ ^ 2) →
      (∀ x : H, StatFormal.Wave23c.cmNorm Pr G x < ⊤ ↔ x ∈ Set.range S) ∧
        ∀ y : H, StatFormal.Wave23c.cmNorm Pr G (S y) = ((‖y‖ : ℝ) : EReal)

/-- `thm:elliptical` (i), the rest: the positive-depth set `{x : TD_H(x; μ) > 0}` is the Cameron–Martin space
`ran Σ^{1/2}` (`S = Σ^{1/2}` as in `elliptical_cm_space`), a dense linear subspace, infinite-dimensional when `H` is. -/
def elliptical_positive_space : Prop :=
  ∀ (Ω H : Type) [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [Nontrivial H] (Pr : Measure Ω) (G : Ω → H) (W : Ω → ℝ) (S : H →L[ℝ] H),
    StatFormal.Wave23c.EllSetting Pr G W → (∀ v w, ⟪S v, w⟫_ℝ = ⟪v, S w⟫_ℝ) →
    (∀ v, Var[fun ω => ⟪v, G ω⟫_ℝ; Pr] = ‖S v‖ ^ 2) →
      {x : H | 0 < StatFormal.OTFD.Wave13a.tukeyDepthH (StatFormal.Wave23c.ellLaw Pr G W) x} = Set.range S ∧
        Dense (Set.range S) ∧ (¬ FiniteDimensional ℝ H → ¬ FiniteDimensional ℝ (LinearMap.range (S : H →ₗ[ℝ] H)))

/-- `thm:elliptical` (i), "`μ`-null": in the Karhunen–Loève setting of the frozen `lem:cm-null` (`Σ e_k = λ_k e_k`,
`λ_k > 0`, `Σ λ_k < ∞`, `⟨e_k, G⟩ = √λ_k ξ_k` with `ξ_k` iid `N(0,1)`, `S e_k = √λ_k e_k`), with `Var⟨v, G⟩ = ‖Sv‖²`,
the positive-depth set has `μ`-measure `0`. -/
def elliptical_positive_null : Prop :=
  ∀ (Ω H : Type) [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] [Nontrivial H] (Pr : Measure Ω)
    (e : HilbertBasis ℕ ℝ H) (lam : ℕ → ℝ) (S : H →L[ℝ] H) (ξ : ℕ → Ω → ℝ) (G : Ω → H) (W : Ω → ℝ),
    StatFormal.Wave23c.EllSetting Pr G W → (∀ v w, ⟪S v, w⟫_ℝ = ⟪v, S w⟫_ℝ) →
    (∀ v, Var[fun ω => ⟪v, G ω⟫_ℝ; Pr] = ‖S v‖ ^ 2) →
    (∀ k, 0 < lam k) → Summable lam → (∀ k, S (e k) = Real.sqrt (lam k) • e k) →
    (∀ k, Measurable (ξ k)) → iIndepFun ξ Pr → (∀ k, Pr.map (ξ k) = gaussianReal 0 1) →
    (∀ᵐ ω ∂Pr, ∀ k, ⟪e k, G ω⟫_ℝ = Real.sqrt (lam k) * ξ k ω) →
      StatFormal.Wave23c.ellLaw Pr G W
        {x : H | 0 < StatFormal.OTFD.Wave13a.tukeyDepthH (StatFormal.Wave23c.ellLaw Pr G W) x} = 0

/-! ### B `prop:band-injectivity` (i), (iii) -/

/-- `prop:band-injectivity` (i), both inclusions, for maps with an invertible strict derivative on `U` (local
diffeomorphisms; the printed (i) assumes only continuity and injectivity, whose `⊆` half is Brouwer's invariance of
domain): if `Q̂` has an invertible strict derivative at every point of an open `U ⊇ A`, is injective on `U`, and `A` is
compact, then `∂Q̂(A) = Q̂(∂A)`. Any real Banach space (here `ℝ^K` in either encoding). -/
def band_injectivity_contour : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (Qh : E → E) (U A : Set E)
    (D : E → E ≃L[ℝ] E),
    IsOpen U → A ⊆ U → IsCompact A → (∀ u ∈ U, HasStrictFDerivAt Qh (D u : E →L[ℝ] E) u) → InjOn Qh U →
      frontier (Qh '' A) = Qh '' frontier A

/-- `prop:band-injectivity` (i), the inclusion `Q̂(∂A) ⊆ ∂Q̂(A)` under the printed hypotheses (`Q̂` continuous and
injective on an open `U ⊇ A`, `A = A_{K,p}` compact; the proof's "Conversely" half, no invariance of domain). -/
def band_injectivity_contour_supset : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (Qh : E → E) (U A : Set E),
    IsOpen U → A ⊆ U → IsCompact A → ContinuousOn Qh U → InjOn Qh U →
      Qh '' frontier A ⊆ frontier (Qh '' A)

/-- `prop:band-injectivity` (iii), quadratic map: where the active set `{i : q_i(u) > 0}` of the simplex-projection
weights is the singleton `{j}`, the quadratic map `Σ_i q_i(u) Z_i` equals `Z_j`; so on a nonempty open such set `O`
(`K ≥ 1`) it is constant and not injective on any `U ⊇ O`. -/
def band_injectivity_quad_const : Prop :=
  ∀ (n K : ℕ) (lam : ℝ) (M : Matrix (Fin K) (Fin K) ℝ) (Z : Fin n → Fin K → ℝ) (f : Fin n → ℝ)
    (q : (Fin K → ℝ) → Fin n → ℝ) (O : Set (Fin K → ℝ)) (j : Fin n),
    (∀ u, StatFormal.OTFD.Bands.IsSimplexProj (StatFormal.OTFD.Wave7a.rawScore lam M f Z u) (q u)) →
    (∀ u ∈ O, ∀ i, 0 < q u i ↔ i = j) →
      (∀ u ∈ O, StatFormal.OTFD.Wave7a.baryMap (q u) Z = Z j) ∧
        (1 ≤ K → IsOpen O → O.Nonempty → ∀ U, O ⊆ U → ¬ InjOn (fun u => StatFormal.OTFD.Wave7a.baryMap (q u) Z) U)

/-- `prop:band-injectivity` (iii), Karp map: where the active set of the Laguerre potential at the proximal point
`P(L_K u)` is the singleton `{j}`, `Q̂_Karp(u) = σ⁻¹ L_K⁻¹ β_j`; so on a nonempty open such set `O` (`K ≥ 1`) the Karp
map is constant and not injective on any `U ⊇ O`. -/
def band_injectivity_karp_const : Prop :=
  ∀ (n K : ℕ) (β : Fin n → Fin K → ℝ) (θ : Fin n → ℝ) (ε₀ σ : ℝ) (L : Matrix (Fin K) (Fin K) ℝ)
    (P : (Fin K → ℝ) → Fin K → ℝ) (O : Set (Fin K → ℝ)) (j : Fin n),
    0 < ε₀ → (∀ y, StatFormal.OTFD.Wave7a.IsProx (StatFormal.OTFD.Wave7a.laguerre β θ) ε₀ y (P y)) →
    (∀ u ∈ O, ∀ i, i ≠ j → β i ⬝ᵥ P (L *ᵥ u) - θ i < β j ⬝ᵥ P (L *ᵥ u) - θ j) →
      (∀ u ∈ O, StatFormal.OTFD.Wave7a.karpMap σ ε₀ L P u = σ⁻¹ • (L⁻¹ *ᵥ β j)) ∧
        (1 ≤ K → IsOpen O → O.Nonempty → ∀ U, O ⊆ U → ¬ InjOn (StatFormal.OTFD.Wave7a.karpMap σ ε₀ L P) U)

/-- `prop:band-injectivity` (iii), quadratic map with every weight active on `U`: the map is affine on `U` with linear
part `(2/λ) 𝖹ᵀ(I_n − n⁻¹𝟏𝟏ᵀ)𝖹 M_K` (`𝖹` the `n × K` matrix with rows `Z_j`); when the `Z_j` affinely span `ℝ^K`
this linear part is invertible and the map is injective on `U`. -/
def band_injectivity_quad_affine : Prop :=
  ∀ (n K : ℕ) (lam : ℝ) (M : Matrix (Fin K) (Fin K) ℝ) (Z : Fin n → Fin K → ℝ) (f : Fin n → ℝ)
    (q : (Fin K → ℝ) → Fin n → ℝ) (U : Set (Fin K → ℝ)),
    0 < n → 0 < lam → M.PosDef →
    (∀ u, StatFormal.OTFD.Bands.IsSimplexProj (StatFormal.OTFD.Wave7a.rawScore lam M f Z u) (q u)) →
    (∀ u ∈ U, ∀ i, 0 < q u i) →
      (∃ c : Fin K → ℝ, ∀ u ∈ U, StatFormal.OTFD.Wave7a.baryMap (q u) Z =
          c + ((2 / lam) • ((Matrix.of Z)ᵀ * (1 - (n : ℝ)⁻¹ • Matrix.of (fun _ _ => (1 : ℝ))) * Matrix.of Z * M)) *ᵥ u) ∧
      (affineSpan ℝ (Set.range Z) = ⊤ →
        ((Matrix.of Z)ᵀ * (1 - (n : ℝ)⁻¹ • Matrix.of (fun _ _ => (1 : ℝ))) * Matrix.of Z * M).det ≠ 0 ∧
          InjOn (fun u => StatFormal.OTFD.Wave7a.baryMap (q u) Z) U)

/-! ### B `prop:cubic-band-infinite` (i), (ii), the iff of (iii), (iv) -/

/-- (iii), the equivalence: with `λ_k = 2a_k`, `r_p = τ_{K,p} D_∞` and `𝒦_p = {k : λ_k ≤ 2r_p}`, for `p ∈ (0, 1]`,
`𝒦_p ≠ ∅ ⇔ p ≥ p*_K = c_K(λ_(K)/(2D_∞))`. -/
def cubic_K_nonempty_iff : Prop :=
  ∀ (N : ℕ) (a : Fin N → ℝ) (Dinf p : ℝ), 0 < N → (∀ k, 0 < a k) → 0 < Dinf → 0 < p → p ≤ 1 →
    ((∃ k, 2 * a k ≤ 2 * (StatFormal.OTFD.Wave8c.tauKp a Dinf p * Dinf)) ↔
      StatFormal.OTFD.Wave8c.cK a Dinf ((⨅ k, 2 * a k) / (2 * Dinf)) ≤ p)

/-- (i): the product map `Q(u) = (λ_k Φ^{-1}(u_k/λ_k + ½))_k` pushes `μ_K` to `P_K = ⊗N(0, λ_k²)`, is `μ_K`-a.e.
cyclically monotone (a Brenier map in McCann's sense, so it is `Q_{±,K}`: the certified WaveP2a
`potential_consistency` identifies every such map with `∇χ_K` `μ_K`-a.e.), and is continuous on
`int 𝒰_K = {|u_k| < a_k}`. -/
def cubic_quantile_map : Prop :=
  ∀ (N : ℕ) (a : Fin N → ℝ), (∀ k, 0 < a k) →
    HasLaw (cubicGaussQ a) (gaussProdE a) (cubicLawE a) ∧ StatFormal.OTFD.WaveL1.IsCMMapAE (cubicLawE a) (cubicGaussQ a) ∧
      ContinuousOn (cubicGaussQ a) {u | ∀ k, |u k| < a k}

/-- (ii): for `p ∈ (0, 1]` and `v ∈ ℝ^K`, `h^pop_{K,p}(v) = +∞` iff `v_k ≠ 0` for some `k ∈ 𝒦_p`. -/
def cubic_popSupp_top : Prop :=
  ∀ (N : ℕ) (a : Fin N → ℝ) (Dinf p : ℝ) (v : EuclideanSpace ℝ (Fin N)), (∀ k, 0 < a k) → 0 < Dinf → 0 < p → p ≤ 1 →
    (StatFormal.Wave23a.popSupp (cubicLawE a) (cubicRegion a Dinf p) (cubicGaussQ a) v = ⊤ ↔
      ∃ k, 2 * a k ≤ 2 * (StatFormal.OTFD.Wave8c.tauKp a Dinf p * Dinf) ∧ v k ≠ 0)

/-- (iii), consequence: if `𝒦_p ≠ ∅` the bounded-range hypothesis of `thm:band-containment` fails on `A_{K,p}`. -/
def cubic_containment_fails : Prop :=
  ∀ (N : ℕ) (a : Fin N → ℝ) (Dinf p : ℝ), (∀ k, 0 < a k) → 0 < Dinf → 0 < p → p ≤ 1 →
    (∃ k, 2 * a k ≤ 2 * (StatFormal.OTFD.Wave8c.tauKp a Dinf p * Dinf)) →
      ¬ ∃ R : ℝ, ∀ᵐ u ∂(cubicLawE a).restrict (cubicRegion a Dinf p), ‖cubicGaussQ a u‖ ≤ R

/-- (iv): under `ass:fixedK-oos` as printed (the certified WaveP2a `FixedKOOSInexact`) with `μ_K` the cubic law and
`P_K` the matched Gaussian, almost surely, simultaneously for every `p ∈ (0, 1]` and every `t` with `e_k(t) ≠ 0` for
some `k ∈ 𝒦_p`, the computed edges `x̂↑_{n,p}(t) = 𝔪(t) + ĥ_n(e(t)) → +∞` and `x̂↓_{n,p}(t) = 𝔪(t) − ĥ_n(−e(t)) → −∞`
(`Q̂_n` the fitted entropic maps). -/
def cubic_edges_diverge : Prop :=
  ∀ (N : ℕ) (a : Fin N → ℝ) (Dinf : ℝ) (μ P : ProbabilityMeasure (EuclideanSpace ℝ (Fin N)))
    (μs : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin N))) (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω)
    [IsProbabilityMeasure Pr] (Z : ℕ → Ω → EuclideanSpace ℝ (Fin N)) (ε : ℕ → ℝ)
    (f : (n : ℕ) → Ω → Fin (n + 1) → ℝ) (r : ℕ → Ω → ℝ) (𝒯 : Type) (mfrak : 𝒯 → ℝ)
    (e : 𝒯 → EuclideanSpace ℝ (Fin N)),
    (∀ k, 0 < a k) → 0 < Dinf → (μ : Measure (EuclideanSpace ℝ (Fin N))) = cubicLawE a →
    (P : Measure (EuclideanSpace ℝ (Fin N))) = gaussProdE a →
    StatFormal.WaveP2a.FixedKOOSInexact μ P μs Pr Z ε f r →
      ∀ᵐ ω ∂Pr, ∀ p : ℝ, 0 < p → p ≤ 1 → ∀ t,
        (∃ k, 2 * a k ≤ 2 * (StatFormal.OTFD.Wave8c.tauKp a Dinf p * Dinf) ∧ e t k ≠ 0) →
        Tendsto (fun n => (mfrak t : EReal) + StatFormal.Wave23a.fitSupp (cubicRegion a Dinf p)
            (StatFormal.Wave23c.entMap (ε n) (fun i : Fin (n + 1) => Z i ω) (f n ω)) (e t)) atTop (𝓝 ⊤) ∧
          Tendsto (fun n => (mfrak t : EReal) - StatFormal.Wave23a.fitSupp (cubicRegion a Dinf p)
            (StatFormal.Wave23c.entMap (ε n) (fun i : Fin (n + 1) => Z i ω) (f n ω)) (-e t)) atTop (𝓝 ⊥)

/-! ### B `prop:trimmed-band` (ii), (iii) -/

/-- (ii) under `ass:fixedK-oos` as printed (WaveP2a `FixedKOOSInexact`), no regularity of `Q_{±,K}`: for any measurable
level region `A`, with `𝒰_K = supp μ_K ∋ 0` interior and `δ' ∈ (0, 1)`, the trimmed region `A^{δ'} = A ∩ (1 − δ')𝒰_K`
has finite population support function (`< +∞`, and `> −∞` when `μ_K(A^{δ'}) > 0`), and almost surely the
conclusions of `thm:band-containment` hold for the trimmed bands: for every `η > 0`, eventually, for all `t`,
`x↑pop,δ' ≤ x̂↑_n,δ' + η` and `x̂↓_n,δ' ≤ x↓pop,δ' + η` (`T` any McCann Brenier map, `Q̂_n` the fitted entropic maps). -/
def trimmed_containment : Prop :=
  ∀ (K : ℕ) (μ P : ProbabilityMeasure (EuclideanSpace ℝ (Fin K))) (μs : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin K)))
    (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (Z : ℕ → Ω → EuclideanSpace ℝ (Fin K))
    (ε : ℕ → ℝ) (f : (n : ℕ) → Ω → Fin (n + 1) → ℝ) (r : ℕ → Ω → ℝ)
    (T : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (𝒯 : Type) (A : Set (EuclideanSpace ℝ (Fin K)))
    (mfrak : 𝒯 → ℝ) (e : 𝒯 → EuclideanSpace ℝ (Fin K)) (δ : ℝ),
    StatFormal.WaveP2a.FixedKOOSInexact μ P μs Pr Z ε f r →
    HasLaw T (P : Measure (EuclideanSpace ℝ (Fin K))) (μ : Measure (EuclideanSpace ℝ (Fin K))) →
    StatFormal.OTFD.WaveL1.IsCMMapAE (μ : Measure (EuclideanSpace ℝ (Fin K))) T →
    MeasurableSet A → (0 : EuclideanSpace ℝ (Fin K)) ∈ interior (μ : Measure (EuclideanSpace ℝ (Fin K))).support →
    0 < δ → δ < 1 → (∃ C : ℝ, ∀ t, ‖e t‖ ≤ C) →
      (∀ v, StatFormal.Wave23a.popSupp (μ : Measure (EuclideanSpace ℝ (Fin K)))
          (A ∩ (1 - δ) • (μ : Measure (EuclideanSpace ℝ (Fin K))).support) T v ≠ ⊤) ∧
      ((μ : Measure (EuclideanSpace ℝ (Fin K))) (A ∩ (1 - δ) • (μ : Measure (EuclideanSpace ℝ (Fin K))).support) ≠ 0 →
        ∀ v, StatFormal.Wave23a.popSupp (μ : Measure (EuclideanSpace ℝ (Fin K)))
          (A ∩ (1 - δ) • (μ : Measure (EuclideanSpace ℝ (Fin K))).support) T v ≠ ⊥) ∧
      ∀ᵐ ω ∂Pr, ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t,
        (mfrak t : EReal) + StatFormal.Wave23a.popSupp (μ : Measure (EuclideanSpace ℝ (Fin K)))
            (A ∩ (1 - δ) • (μ : Measure (EuclideanSpace ℝ (Fin K))).support) T (e t) ≤
          (mfrak t : EReal) + StatFormal.Wave23a.fitSupp (A ∩ (1 - δ) • (μ : Measure (EuclideanSpace ℝ (Fin K))).support)
            (StatFormal.Wave23c.entMap (ε n) (fun i : Fin (n + 1) => Z i ω) (f n ω)) (e t) + (η : EReal) ∧
        (mfrak t : EReal) - StatFormal.Wave23a.fitSupp (A ∩ (1 - δ) • (μ : Measure (EuclideanSpace ℝ (Fin K))).support)
            (StatFormal.Wave23c.entMap (ε n) (fun i : Fin (n + 1) => Z i ω) (f n ω)) (-e t) ≤
          (mfrak t : EReal) - StatFormal.Wave23a.popSupp (μ : Measure (EuclideanSpace ℝ (Fin K)))
            (A ∩ (1 - δ) • (μ : Measure (EuclideanSpace ℝ (Fin K))).support) T (-e t) + (η : EReal)

/-- (ii), the cube's certified support bound: `σ_{A^{δ'}}(v) ≤ min{r_p‖v‖₂, (1 − δ')Σ_k λ_k|v_k|/2}` for the cubic
region `A_{K,p} = {u ∈ 𝒰_K : ‖u‖₂ ≤ r_p}` (`λ_k = 2a_k`), `A^{δ'} = A_{K,p} ∩ {|u_k| ≤ (1 − δ')a_k}`. -/
def trimmed_cube_support : Prop :=
  ∀ (N : ℕ) (a : Fin N → ℝ) (rp δ : ℝ) (v : EuclideanSpace ℝ (Fin N)), (∀ k, 0 < a k) → 0 < δ → δ < 1 →
    ∀ u ∈ {u : EuclideanSpace ℝ (Fin N) | ((∀ k, |u k| ≤ a k) ∧ ‖u‖ ≤ rp) ∧ ∀ k, |u k| ≤ (1 - δ) * a k},
      ⟪v, u⟫_ℝ ≤ min (rp * ‖v‖) ((1 - δ) * ∑ k, 2 * a k * |v k| / 2)

/-- (iii), two-sided and uniform in the level, under `ass:fixedK-oos` as printed (WaveP2a `FixedKOOSInexact`), with
`0 ∈ int 𝒰_K` (`𝒰_K = supp μ_K`) and level regions `A_p ⊆ 𝒰_K` convex compact with `0` interior, nested below
`A_{p̄}`: if the normalised Brenier potential `χ_K` (convex on `int 𝒰_K`, `inf χ_K = 0`, `∇χ_K = T` `μ_K`-a.e. for a
McCann Brenier map `T`; it exists and is unique by the certified WaveP2a `potential_consistency`) is differentiable on
an open `O` with `A^{δ'}_{p̄} ⊆ O ⊆ int 𝒰_K`, then almost surely, for every `η > 0`, eventually every trimmed band edge
of the fitted entropic maps is within `η` of the (finite) population trimmed edge, uniformly in `p ∈ (0, p̄]` and
`t`. -/
def trimmed_band_consistency : Prop :=
  ∀ (K : ℕ) (μ P : ProbabilityMeasure (EuclideanSpace ℝ (Fin K))) (μs : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin K)))
    (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (Z : ℕ → Ω → EuclideanSpace ℝ (Fin K))
    (ε : ℕ → ℝ) (f : (n : ℕ) → Ω → Fin (n + 1) → ℝ) (r : ℕ → Ω → ℝ)
    (T : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (𝒯 : Type) (A : ℝ → Set (EuclideanSpace ℝ (Fin K)))
    (O : Set (EuclideanSpace ℝ (Fin K))) (χ : EuclideanSpace ℝ (Fin K) → ℝ) (e : 𝒯 → EuclideanSpace ℝ (Fin K))
    (δ pbar EK : ℝ),
    StatFormal.WaveP2a.FixedKOOSInexact μ P μs Pr Z ε f r →
    HasLaw T (P : Measure (EuclideanSpace ℝ (Fin K))) (μ : Measure (EuclideanSpace ℝ (Fin K))) →
    StatFormal.OTFD.WaveL1.IsCMMapAE (μ : Measure (EuclideanSpace ℝ (Fin K))) T →
    (0 : EuclideanSpace ℝ (Fin K)) ∈ interior (μ : Measure (EuclideanSpace ℝ (Fin K))).support →
    0 < δ → δ < 1 → 0 < pbar →
    (∀ p, 0 < p → p ≤ pbar → A p ⊆ (μ : Measure (EuclideanSpace ℝ (Fin K))).support ∧ Convex ℝ (A p) ∧
      IsCompact (A p) ∧ (0 : EuclideanSpace ℝ (Fin K)) ∈ interior (A p) ∧ A p ⊆ A pbar) →
    ConvexOn ℝ (interior (μ : Measure (EuclideanSpace ℝ (Fin K))).support) χ →
    IsGLB (χ '' interior (μ : Measure (EuclideanSpace ℝ (Fin K))).support) 0 →
    (∀ᵐ u ∂(μ : Measure (EuclideanSpace ℝ (Fin K))), DifferentiableAt ℝ χ u ∧ gradient χ u = T u) →
    IsOpen O → A pbar ∩ (1 - δ) • (μ : Measure (EuclideanSpace ℝ (Fin K))).support ⊆ O →
    O ⊆ interior (μ : Measure (EuclideanSpace ℝ (Fin K))).support → (∀ u ∈ O, DifferentiableAt ℝ χ u) →
    (∀ t, ‖e t‖ ≤ EK) →
      ∀ᵐ ω ∂Pr, ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ p, 0 < p → p ≤ pbar → ∀ t,
        ∀ v ∈ ({e t, -e t} : Set (EuclideanSpace ℝ (Fin K))), ∃ r s : ℝ,
          StatFormal.Wave23a.popSupp (μ : Measure (EuclideanSpace ℝ (Fin K)))
              (A p ∩ (1 - δ) • (μ : Measure (EuclideanSpace ℝ (Fin K))).support) T v = r ∧
            StatFormal.Wave23a.fitSupp (A p ∩ (1 - δ) • (μ : Measure (EuclideanSpace ℝ (Fin K))).support)
              (StatFormal.Wave23c.entMap (ε n) (fun i : Fin (n + 1) => Z i ω) (f n ω)) v = s ∧ |s - r| ≤ η

/-- (iii), the matched Gaussian–cubic model: on the trimmed cube `{|u_k| ≤ (1 − δ')a_k}` the product quantile map
satisfies `|⟨v, Q(u)⟩| ≤ Φ^{-1}(1 − δ'/2) Σ_k λ_k |v_k|`, so for every region `A` the trimmed population support
`h^{pop,δ'}(v)` lies in `[−Φ^{-1}(1 − δ'/2) Σ λ_k|v_k|, Φ^{-1}(1 − δ'/2) Σ λ_k|v_k|]` (the lower bound when the trimmed
region has positive mass): `|x^{↑/↓,pop,δ'}(t) − 𝔪(t)| ≤ Φ^{-1}(1 − δ'/2) Σ_k λ_k|e_k(t)|`. -/
def trimmed_matched_edges : Prop :=
  ∀ (N : ℕ) (a : Fin N → ℝ) (δ : ℝ) (A : Set (EuclideanSpace ℝ (Fin N))) (v : EuclideanSpace ℝ (Fin N)),
    (∀ k, 0 < a k) → 0 < δ → δ < 1 →
      StatFormal.Wave23a.popSupp (cubicLawE a) (A ∩ {u | ∀ k, |u k| ≤ (1 - δ) * a k}) (cubicGaussQ a) v ≤
          (((gaussianReal 0 1).quantile (1 - δ / 2) * ∑ k, 2 * a k * |v k| : ℝ) : EReal) ∧
        (cubicLawE a (A ∩ {u | ∀ k, |u k| ≤ (1 - δ) * a k}) ≠ 0 →
          ((-((gaussianReal 0 1).quantile (1 - δ / 2) * ∑ k, 2 * a k * |v k|) : ℝ) : EReal) ≤
            StatFormal.Wave23a.popSupp (cubicLawE a) (A ∩ {u | ∀ k, |u k| ≤ (1 - δ) * a k}) (cubicGaussQ a) v)

/-! ### G `prop:cap` (b), (c) on a grid -/

/-- (b), the support: for the rank-`K` reference on a grid (`ξ_k` iid `N(0,1)`, `λ_k > 0`, `τ ∼ Unif(0,1]`
independent of `ξ`, `V = τG/‖G‖`), almost surely `V` lies in the closed unit ball of `S = span{φ_k}`, and every point of
that ball is in the support: `P(‖V − v‖ < ε) > 0` for every `v ∈ S` with `‖v‖ ≤ 1` and every `ε > 0`. -/
def cap_support : Prop :=
  ∀ (J q K : ℕ) (w : Fin J → ℝ) (φ : Fin K → Fin J → EuclideanSpace ℝ (Fin q)) (lam : Fin K → ℝ) (Ω : Type)
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (ξ : Fin K → Ω → ℝ) (τ : Ω → ℝ),
    1 ≤ J → 1 ≤ K → (∀ j, 0 < w j) → StatFormal.Wave23b.GridOrthonormal w φ → (∀ k, 0 < lam k) →
    (∀ k, Measurable (ξ k)) → iIndepFun ξ P → (∀ k, P.map (ξ k) = gaussianReal 0 1) →
    Measurable τ → P.map τ = volume.restrict (Ioc 0 1) → IndepFun τ (fun ω k => ξ k ω) P →
      (∀ᵐ ω ∂P, gridV w lam φ (fun k => ξ k ω) (τ ω) ∈ Submodule.span ℝ (Set.range φ) ∧
        StatFormal.Wave23b.gridNorm w (gridV w lam φ (fun k => ξ k ω) (τ ω)) ≤ 1) ∧
      ∀ v ∈ Submodule.span ℝ (Set.range φ), StatFormal.Wave23b.gridNorm w v ≤ 1 → ∀ ε : ℝ, 0 < ε →
        0 < P {ω | StatFormal.Wave23b.gridNorm w (gridV w lam φ (fun k => ξ k ω) (τ ω) - v) < ε}

/-- (b), the essential supremum: `b_K` is the `μ`-essential supremum of `v ↦ max_j |v(t_j)|`: it bounds the reference
field almost surely, and is exceeded by `b_K − δ` with positive probability for every `δ > 0`. -/
def cap_esssup : Prop :=
  ∀ (J q K : ℕ) (w : Fin J → ℝ) (φ : Fin K → Fin J → EuclideanSpace ℝ (Fin q)) (lam : Fin K → ℝ) (Ω : Type)
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (ξ : Fin K → Ω → ℝ) (τ : Ω → ℝ),
    1 ≤ J → 1 ≤ K → (∀ j, 0 < w j) → StatFormal.Wave23b.GridOrthonormal w φ → (∀ k, 0 < lam k) →
    (∀ k, Measurable (ξ k)) → iIndepFun ξ P → (∀ k, P.map (ξ k) = gaussianReal 0 1) →
    Measurable τ → P.map τ = volume.restrict (Ioc 0 1) → IndepFun τ (fun ω k => ξ k ω) P →
      (∀ᵐ ω ∂P, StatFormal.Wave23b.gridSup (gridV w lam φ (fun k => ξ k ω) (τ ω)) ≤ StatFormal.Wave23b.bK φ) ∧
      ∀ δ : ℝ, 0 < δ →
        0 < P {ω | StatFormal.Wave23b.bK φ - δ < StatFormal.Wave23b.gridSup (gridV w lam φ (fun k => ξ k ω) (τ ω))}

/-- (c), its scalar content (the geometric clauses — `d_M(m(t), Y(t)) = s|v(t)|` within the injectivity radius, the
distance to the cut locus, minimising geodesics — need the Riemannian layer): every field of the support satisfies
`s|v(t_j)| ≤ 0.9 ι` at every node iff `s ≤ 0.9 ι/b_K`; so no larger `s` works for every field of `supp μ`. -/
def cap_scale : Prop :=
  ∀ (J q K : ℕ) (w : Fin J → ℝ) (φ : Fin K → Fin J → EuclideanSpace ℝ (Fin q)) (ι s : ℝ),
    1 ≤ J → (∀ j, 0 < w j) → StatFormal.Wave23b.GridOrthonormal w φ → 0 < StatFormal.Wave23b.bK φ → 0 ≤ s →
      ((∀ v ∈ Submodule.span ℝ (Set.range φ), StatFormal.Wave23b.gridNorm w v ≤ 1 → ∀ j, s * ‖v j‖ ≤ 9 / 10 * ι) ↔
        s ≤ 9 / 10 * ι / StatFormal.Wave23b.bK φ)

/-! ### R `thm:trimmed` (b), (c) and the breakdown point -/

/-- (b), above the budget: if `M_ℓ < d⁺(u₀;ν)`, witnessed by `t > 0`, `D` with `M_ℓ < inf_{‖e‖=1} ν(H_{t,D}(e))`,
then `Q̂(u₀)` is bounded over `𝔠_ℓ(𝒵)` (the potentials recomputed on every contaminated sample). No `ℓ ≥ nα` is
needed (below the budget `M_ℓ ≤ 0` and (a) applies). -/
def trimmed_b : Prop :=
  ∀ (K n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν] (Dν ε α : ℝ)
    (fsel msel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ) (Z : Fin n → EuclideanSpace ℝ (Fin K)) (ℓ : ℕ)
    (u₀ : EuclideanSpace ℝ (Fin K)) (t D : ℝ),
    0 < K → 1 ≤ n → TrimSetting ν Dν ε α fsel msel → 0 < t →
    trimM n ℓ α < (StatFormal.OTFD.Wave6b.halfMass ν u₀ t D).toReal →
      ∃ M : ℝ, ∀ Z' ∈ Contam Z ℓ, ‖Qhat Z' (fsel Z') ε u₀‖ ≤ M

/-- (c), the converse: if `M_ℓ > d⁻(u₀;ν)`, there are contaminations with `‖Q̂(u₀)‖` arbitrarily large. -/
def trimmed_c : Prop :=
  ∀ (K n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν] (Dν ε α : ℝ)
    (fsel msel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ) (Z : Fin n → EuclideanSpace ℝ (Fin K)) (ℓ : ℕ)
    (u₀ : EuclideanSpace ℝ (Fin K)),
    0 < K → 1 ≤ n → TrimSetting ν Dν ε α fsel msel →
    (dMinus ν u₀).toReal < trimM n ℓ α →
      ∀ M : ℝ, ∃ Z' ∈ Contam Z ℓ, M < ‖Qhat Z' (fsel Z') ε u₀‖

/-- The closing display, point version, for every reference: `α + (1 − α)d⁺ ≤ BP(Q̂(u₀)) ≤ α + (1 − α)d⁻ + 1/n`. -/
def trimmed_bp_general : Prop :=
  ∀ (K n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν] (Dν ε α : ℝ)
    (fsel msel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ) (Z : Fin n → EuclideanSpace ℝ (Fin K))
    (u₀ : EuclideanSpace ℝ (Fin K)),
    0 < K → 1 ≤ n → TrimSetting ν Dν ε α fsel msel →
      α + (1 - α) * (StatFormal.OTFD.Wave12a.dPlus ν u₀).toReal ≤ BP (fun Z' => Qhat Z' (fsel Z') ε u₀) Z ∧
        BP (fun Z' => Qhat Z' (fsel Z') ε u₀) Z ≤ α + (1 - α) * (dMinus ν u₀).toReal + 1 / n

/-- The closing display, point version: for absolutely continuous `ν`, `BP(Q̂(u₀)) = α + (1 − α) TD(u₀;ν)` up to
`1/n`. -/
def trimmed_bp : Prop :=
  ∀ (K n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν] (Dν ε α : ℝ)
    (fsel msel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ) (Z : Fin n → EuclideanSpace ℝ (Fin K))
    (u₀ : EuclideanSpace ℝ (Fin K)),
    0 < K → 1 ≤ n → ν ≪ volume → TrimSetting ν Dν ε α fsel msel →
      α + (1 - α) * (StatFormal.OTFD.Wave1.tukeyDepth ν u₀).toReal ≤ BP (fun Z' => Qhat Z' (fsel Z') ε u₀) Z ∧
        BP (fun Z' => Qhat Z' (fsel Z') ε u₀) Z ≤ α + (1 - α) * (StatFormal.OTFD.Wave1.tukeyDepth ν u₀).toReal + 1 / n

/-- The closing display, region version, for every reference: with `β⁻(A) = inf_{u∈A} d⁻(u;ν)`,
`α + (1 − α)β⁻ ≤ BP(Q̂(A)) ≤ α + (1 − α)β⁻ + 1/n` (`A` compact, nonempty). -/
def trimmed_region_bp_general : Prop :=
  ∀ (K n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν] (Dν ε α : ℝ)
    (fsel msel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ) (Z : Fin n → EuclideanSpace ℝ (Fin K))
    (A : Set (EuclideanSpace ℝ (Fin K))),
    0 < K → 1 ≤ n → TrimSetting ν Dν ε α fsel msel → IsCompact A → A.Nonempty →
      α + (1 - α) * (⨅ u ∈ A, dMinus ν u).toReal ≤ BP (regionSup ε fsel A) Z ∧
        BP (regionSup ε fsel A) Z ≤ α + (1 - α) * (⨅ u ∈ A, dMinus ν u).toReal + 1 / n

/-- The closing display, region version: for absolutely continuous `ν`, `BP(Q̂(A)) = α + (1 − α)β(A;ν)` up to `1/n`. -/
def trimmed_region_bp : Prop :=
  ∀ (K n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν] (Dν ε α : ℝ)
    (fsel msel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ) (Z : Fin n → EuclideanSpace ℝ (Fin K))
    (A : Set (EuclideanSpace ℝ (Fin K))),
    0 < K → 1 ≤ n → ν ≪ volume → TrimSetting ν Dν ε α fsel msel → IsCompact A → A.Nonempty →
      α + (1 - α) * (regionDepth ν A).toReal ≤ BP (regionSup ε fsel A) Z ∧
        BP (regionSup ε fsel A) Z ≤ α + (1 - α) * (regionDepth ν A).toReal + 1 / n

end Claims

end StatFormal.WaveP3a
