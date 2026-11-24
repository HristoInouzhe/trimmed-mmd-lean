import StatFormal.Archive.WaveP3a.Statements
import StatFormal.Archive.WaveP3c.Statements
import StatFormal.Archive.WaveP1d.Statements
import StatFormal.Archive.OTFD.Wave19a.Statements

/-!
# FROZEN STATEMENTS — wave 29b: otfd B remaining partial coverage — `prop:hard-transfer` (construction),
# `cor:band-coverage-asymptotic` (iv), `thm:consistency` (general `M_K`), the certified/hard edge variants of
# `lem:band-pointwise-lower`, `prop:cubic-band-infinite` (iv), `prop:trimmed-band` (ii), and `prop:rk-paths`
# (curve-space form of (i))

Sources (current text of 2026-10-17, `otfd/papers/B_bands/`):
* `def:hard-transfer`, `prop:hard-transfer` and the paragraph after it (`supplement.tex:6665-6694`).
* `cor:band-coverage-asymptotic` (`supplement.tex:1086-1118`, `eq:normalized-nesting`), its proof, part (iv)
  (`supplement.tex:2337-2391`); `h^pop`, `𝒮_{K,p}` (`supplement.tex:795-804`); `E_K < ∞` (`supplement.tex:742`).
* `thm:consistency` (`supplement.tex:6137-6179`, proof `:6181-6200`).
* `lem:band-pointwise-lower` (`supplement.tex:849-860`), `prop:cubic-band-infinite` (iv) (`supplement.tex:951-985`),
  `prop:trimmed-band` (ii) (`supplement.tex:997-1040`), with `prop:band-certificate` (`main.tex:719-760`) and
  `ass:fixedK-oos` (`supplement.tex:751-790`).
* `def:rk-path` (`main.tex:1076-1090`), `prop:rk-paths` (`supplement.tex:6599-6631`).
Imports the frozen statements of WaveP3a (`cubicLawE`, `gaussProdE`, `cubicRegion`; through it WaveP2a
`FixedKOOSInexact`, Wave 23a `popSupp`, `fitSupp`, `cdfK`, `cdfKInv`, Wave 23c `lagPot`), WaveP3c (through it WaveL1
`Euc`, `IsCMMapAE`, Wave 22a `IsSubgrad`, Tau Ceti `empiricalMeasure`), WaveP1d (through it OTFD Bands `gap`, `Qent`,
Wave 7a `oosA`, `oosB`, Wave 14c `knapUp`, `certUp`, `certLo`, `entCaps`) and OTFD Wave 19a (`IsMGradMap`, `extTop`; through it
Wave 8c `mvec`, `mnorm`, `IsRankPair`), not copied; Mathlib and Tau Ceti otherwise. No `Foundations` file is imported by
the statements.

Covered:
* `prop:hard-transfer`: `hard_piecewise_const` ((iii) "piecewise constant": open, disjoint cells, constant on each, ties outside),
  `hard_discontinuous` ((iii) "hence discontinuous across cell boundaries": at every two-cell boundary point with
  distinct grid points and distinct assigned `B` heads), `hard_scale_target` (closing sentence: rescaling does not
  change the population target `Q_{B,K} ∘ F_{A,K}`). (i) is the certified OTFD `cell_eq_partner` (with
  `strict_margin_of_unique`, `unique_of_strict_margin` for the potentials); together these cover the construction.
* `cor:band-coverage-asymptotic` (iv): `bca_iv_closure` (`ς(p') > 0` iff `h_p > h_{p'}` on `𝒲`), `bca_iv_nesting`
  (uniform strict nesting implies it), `bca_iv_nesting_iff` (equivalent when `inf_t ‖e(t)‖ > 0`), `bca_iv_interior`
  (`𝒮_{K,p'} ⊂ int 𝒮_{K,p}` gives it for every basis). `NormNesting` is literally the premise of the certified
  frozen Wave 24d `band_coverage_asymptotic` (and WaveP2a `_discharged`), so (iv) feeds (i) directly.
* `thm:consistency`: `cons_general_M` (general symmetric positive definite `M_K`, Ghosal–Sen premise discharged as in
  the certified WaveP3c `consistency_B_gs`, plus `ε_n(𝒦) → 0`), `cons_cprime` (`c'_K = λ_max(M_K)^{1/2}` for the gauge
  `‖·‖_{M_K}` of the naive and ball laws, the smallest constant with `g_K ≤ c'_K‖·‖₂`).
* Certified/hard edges: `bpl_certified` (`lem:band-pointwise-lower`, certified support), `cbi_certified_diverge`,
  `cbi_hard_diverge` (`prop:cubic-band-infinite` (iv), certified edges and every selected hard map),
  `trim_certified_containment` (`prop:trimmed-band` (ii), the certified trimmed band).
* `prop:rk-paths`: `rkp_curve_mono`, `rkp_curve_strict` ((i) "equivalently, in curve space", with the strict
  entropic case).

Not covered (declared):
* `prop:hard-transfer` (iii) "costs `O(N)` per new curve, no refitting" (complexity; the map is a function of the
  stored `ψ`, `σ_B`, `zB` only, which is what "deterministic, no refitting" means); the transductive variant; the
  Bellman–Ford remark (an algorithm for the difference constraints, which are `HasMarginPotentials` re-indexed); the
  a.s. uniqueness for iid heads is the certified Wave 5a `fixedK_unique_of_atomless`; "consistency of the
  out-of-sample hard map is open" (open in the paper). (i) beyond the frozen `cell_eq_partner` and (ii) are
  definitional for `hardTransfer` (its value is `zB` of an index; the partner bijection is `σ_B⁻¹ ∘ σ_A`): a draft
  `hard_partner` was REJECTED by the critic (2026-10-17) as a re-packaging of `cell_eq_partner` plus an `rfl` conjunct.
* `prop:rk-paths` (iii), shell variant: the frozen Wave 24a `rk_paths_consistency` is generic in the compact region
  `A1` and the level sets `P w`, so the shell case is its instance at `A1 = Σ_{p₀,δ}`, `P w ∩ [p₀, 1 − δ]` (the region
  premise discharged by `g(τ_p w) = τ_p`); a draft `rkp_consistency_shell` was REJECTED by the critic as a restatement.
* `thm:consistency`: `c'_K = 1/D_∞` for the cubic law (the cubic gauge is not restated), the modulus bound
  `|D̂^prob − D^prob| ≤ ϖ_K(c'_K ε_n)` and the rate-transfer remark (only uniform convergence of both depths, as in the
  frozen claim); the paper's homeomorphism hypothesis is replaced by differentiability on `𝒦` with gradient `M_K F`, as
  in the frozen WaveP3c claim (weaker, see Encodings); the order "a.s., for every compact `𝒦`" (as frozen: per `𝒦`).
* Certified edges: the quadratic map's certified band (the fixed-`K` asymptotics concern the entropic map only); the
  hard-map variant of `prop:trimmed-band` (ii) (not printed there).
* `prop:hard-transfer` (iii) at tied `B` heads: `hard_discontinuous` assumes the two adjacent cells carry distinct `B`
  heads (the printed "hence discontinuous" needs it, see manuscript note (1)).

Encodings (to be checked by the critic):
* Hard transfer: generic real inner product space `E` (`ℝ^K` in the paper); the `A` pool rescaled by `s` (the paper's
  RMS ratio; any scalar is allowed); `σ_B k` the grid point of `B` curve `k` (no optimality of `σ_B` needed); "the cell
  containing `z`" is ANY selection of minimisers (`IsCellSelection`), so ties are covered by quantification.
  Population target: Wave 8c `IsRankPair`, Wave 19a `IsMGradMap`
  (any positive definite `M`, generalising `M_K = I`), rescaled laws `PA.map (a • ·)` (measurable map, no junk).
* Coverage (iv): `ς(p') > 0` is `NormNesting` (some `ς > 0` with `h_{p'}(σe) + ς‖e‖ ≤ h_p(σe)`, `t ∈ 𝒯_*`, `σ = ±1`;
  `inf ∅ = +∞` is the vacuous case); `𝒲` is the closure in `ℝ^K` of `normDirs e` (it lies in the closed unit sphere, so
  this is the closure in the sphere); uniform strict nesting `UnifNesting` on the `EReal` edges; `𝒮_{K,p}` is
  `popRegion = {y : ∀ v, ⟨v, y⟩ ≤ h^pop(v)}`, the closed convex set with support function `h^pop` (the paper's
  definition of `𝒮_{K,p}` through its support function). Hypotheses: the bounded-range hypothesis of
  `thm:band-containment` on BOTH regions (on `A_{K,p'} ⊆ A_{K,p}` it follows) and positive content of both (the
  paper's `μ_K(A_{K,p}) = p > 0`), which make the support functions finite; `E_K = sup ‖e‖ < ∞` is the setting.
* `thm:consistency`, general `M_K`: the estimator class for the cost `‖z − u‖²_{M_K}`: the `M_K`-`c`-subdifferential
  of the data-side potential is `{u : M_K u ∈ ∂ψ̂_n(z)}` for `ψ̂_n = (‖·‖²_{M_K} − φ)/2 = sup_u ⟨·, M_K u⟩ − …`
  (convex, `sup_{𝒮_K} ‖M_K u‖`-Lipschitz, hence `L'`-Lipschitz with `L' ≥ ‖M_K u‖` on `B(0, R) ⊇ 𝒮_K`); the class
  CONTAINS the `M_K`-Ghosal–Sen estimator (argued, not formalised, exactly as for the frozen `M_K = I` claim). The
  population map: `F#P_K = μ_K`, `M_K F ∈ ∂ψ` `P_K`-a.e. (`F = M_K⁻¹∇ψ`, the `M_K`-monotone rank map of `main.tex`), `ψ`
  convex Lipschitz, differentiable on `𝒦` with gradient `M_K F` (weaker than the homeomorphism hypothesis, as argued in
  the frozen WaveP3c card). `c'_K`: `λ_max = ⨆_i eigenvalues_i` of the Hermitian `M_K` (`K ≥ 1`, finite nonempty
  index: no junk `iSup`).
* Certified edges: `M_K = I` (the setting of `subsec:fixedK-band-limits`); the certified edge is the frozen Wave 14c
  `certUp`/`certLo` (`= 𝔪 + knapUp`, `𝔪 + knapLo`) of the `n`-th fit, data `Z_0, …, Z_n` read in `Fin K → ℝ`
  coordinates (`WithLp.ofLp`), region `WithLp.ofLp '' A`, caps `entCaps ε_n δ_n` from ANY lower bounds
  `δ_{n,j} ≤ δ_j` of the reachability gaps (frozen OTFD Bands `gap` of the affine scores `oosA 1`, `oosB 1`), chosen
  inside the a.s. event (data-dependent caps allowed; covers the dual certificate (ii) and "any valid upper bound on
  `σ_{A^{δ'}}`"). "Certified support at `v = e(t)`" is `knapUp(κ, ⟨v, Z_j⟩)` at every `v` (stronger).
* Curve space: `e_1, …, e_K : 𝒯 → ℝ` orthonormal in `L²(𝒯, λ)` (`IsOrthonormalFamily`: integrable products,
  `∫ e_k e_l = δ_{kl}`), `π_v(p)(t) = 𝔪(t) + Σ_k Q̂(τ_p v)_k e_k(t)`, `ι_K(Mv) = Σ_l (Mv)_l e_l`.

Junk audit: no division by a variable that can vanish (`‖e(t)‖⁻¹` only for `e(t) ≠ 0`; `b⁻¹` with `b > 0`); no
`sInf`/`sSup` in the new statements except through the frozen `gap` (an `sInf` of a set of nonnegative reals, bounded
below; the claims only use LOWER bounds `δ ≤ gap`, so a junk `0` would only weaken the caps' premise, and the frozen
`band_outer_ent` is certified for exactly this premise) and `cdfKInv` (frozen); `⨆_i eigenvalues_i` over a finite
nonempty index (`K ≥ 1`); `Measure.map` only of measurable maps (`a • ·`, `mvec`, `(z, u) ↦ (z, M_K u)`) or as frozen
(`P.map F` with `Measurable F`); `popSupp` is an `EReal` essential supremum (`⊥` only on null regions, excluded by
`μ A ≠ 0` where finiteness is used); `liminf` in the complete lattice `EReal`; `EReal` subtraction only of finite or as in
the frozen edges; Bochner integrals only of integrable integrands (`IsOrthonormalFamily`).

Proof notes (author of the draft, 2026-10-17): all 15 claims are proved in `Wave29b/Route{Hard,Coverage,ConsM,
Certified,Paths}.lean` (`#print axioms`: propext, Classical.choice, Quot.sound), on the new library
`Foundations/BandSupport` (`PopSupp`: finiteness, Lipschitz bound, homogeneity of `popSupp`, the essential range lies in
`popRegion`; `CertBridge`: `entMap ↔ Qent` under `WithLp.ofLp`, certified ≥ fitted support from the certified WaveP1d
`band_outer_ent`; `MatrixGauge`: Rayleigh bound via the eigenvector basis).
* Hard transfer: along `z + t(u_j − u_{j'})` the score
  difference is exactly `−2st‖u_j − u_{j'}‖²` (`lagScore_add_sub`), so the one-sided limits are the two `B` heads.
  Scale: frozen Wave 19a `rk_transfer_scalar_affine` gives `Q_{aA}∘F_A = a·`; the rank pair of `a#P_A` inverts it;
  McCann uniqueness (`Wave19a.mgrad_unique`) gives `Q_{bB} = bQ_B`.
* (iv): `ς(p') = inf_𝒟 (h_p − h_{p'})` by homogeneity, the minimum over the compact `𝒲` by continuity; interior:
  `𝒮_{K,p'}` compact, `cthickening r 𝒮' ⊆ 𝒮`, and `μ|_{A'}`-a.e. `Q ∈ 𝒮'` (countable dense set of directions).
* General `M_K`: change of variables `u ↦ M_K u` on the REFERENCE side (data untouched): `γ_n ↦ (id × M_K)#γ_n` is
  carried by the closed subgradient graph of `ψ̂_n`, `M_K#μ_K` by `B(0, L')`; the certified WaveP3c
  `ghosal_sen_uniform` and the uniformly continuous `M_K⁻¹` give `F̂_n → F`; the frozen Wave 24a `consistency_B` gives
  the depths. (The paper uses `L = M_K^{1/2}` on both sides; same conclusion.)
* Certified edges: `certUp ≥ 𝔪 + ĥ_n`, `certLo ≤ 𝔪 − ĥ_n(−·)` at every `n`, composed with the certified WaveP2a
  `band_pointwise_lower`, WaveP3a `cubic_edges_diverge`, `trimmed_containment`; the hard cubic divergence is the
  certified Wave 27e `band_pointwise_lower_hard` with WaveP3a `cubic_quantile_map`, `cubic_popSupp_top`.
* Curve space: `∫(Σ c_k e_k)(Σ d_l e_l) = Σ c_k d_k`, then the frozen `rk_paths_mono`, `rk_paths_strict`.
* Light claims (content mostly in frozen results): `hard_piecewise_const`, `bpl_certified`, `cbi_*`,
  `trim_certified_containment`, `rkp_*` (compositions of a certified claim with an elementary or certified bridge
  — `band_outer_ent` through `CertBridge`, the finite Parseval identity — each covering a printed clause that no frozen
  claim states). Critic review (2026-10-17): accepted with this note; `hard_partner`, `rkp_consistency_shell` rejected
  (see Not covered).
* No tautology: no conclusion is a hypothesis; the potentials, selections and caps are quantified, not assumed to have
  the concluded property.
* Manuscript notes: (1) `prop:hard-transfer` (iii) "hence discontinuous across cell boundaries" (`supplement.tex:6683`)
  holds where the two adjacent cells carry DIFFERENT `B` heads (distinct grid points); if two `B` curves have equal
  heads the map is continuous across their common boundary, so "hence" is a non-sequitur in that (null-probability)
  case — a minor wording defect. (2) The rescaling sentence
  holds for any positive scalars and any `M`, by McCann uniqueness, not only "since monotone maps are scale-equivariant"
  (equivariance gives the candidate, uniqueness identifies it). (3) (iv)'s "implied by uniform strict nesting" uses
  `E_K < ∞` (the section's standing assumption, `supplement.tex:742`; the proof's bound `ς ≥ ς₀/E_K`); the claim
  states it explicitly. (4) `thm:consistency`'s reduction can be done on the reference side only (`u ↦ M_K u`), which needs no
  square root and leaves `P_K`, `𝒦` and `int 𝒴_K` unchanged. No printed statement was found false.

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Matrix
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace Pointwise

namespace StatFormal.Wave29b

open StatFormal.Wave23a (popSupp fitSupp)
open StatFormal.OTFD.WaveL1 (IsCMMapAE Euc)
open StatFormal.OTFD.Wave22a (IsSubgrad)
open StatFormal.OTFD.Wave8c (mvec mnorm IsRankPair)
open StatFormal.OTFD.Wave19a (IsMGradMap)
open StatFormal.OTFD.Bands (gap)
open StatFormal.OTFD.Wave7a (oosA oosB)
open StatFormal.OTFD.Wave14c (knapUp certUp certLo entCaps)
open StatFormal.WaveP2a (FixedKOOSInexact)
open StatFormal.WaveP3a (cubicLawE gaussProdE cubicRegion)
open TauCeti.Probability (empiricalMeasure)

/-! ### B `def:hard-transfer` -/

section Hard
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {N : ℕ}

/-- The score of grid point `j` at a (rescaled) head `y`: `‖y − u_j‖² − ψ_j`; the cell of `y` is its set of
minimisers (`def:hard-transfer`). -/
def lagScore (u : Fin N → E) (ψ : Fin N → ℝ) (y : E) (j : Fin N) : ℝ := ‖y - u j‖ ^ 2 - ψ j

/-- `sel` selects a cell for every point: `sel y` minimises `j ↦ ‖y − u_j‖² − ψ_j` (any choice at ties). -/
def IsCellSelection (u : Fin N → E) (ψ : Fin N → ℝ) (sel : E → Fin N) : Prop :=
  ∀ y j, lagScore u ψ y (sel y) ≤ lagScore u ψ y j

/-- The open cell of grid point `j` in head coordinates (heads rescaled by `s`): the score is minimised at `j` only. -/
def openCell (u : Fin N → E) (ψ : Fin N → ℝ) (s : ℝ) (j : Fin N) : Set E :=
  {z | ∀ i, i ≠ j → lagScore u ψ (s • z) j < lagScore u ψ (s • z) i}

/-- `def:hard-transfer`: a head `z` (fitted or new), rescaled by `s`, is sent to the head `z^B_k` of the `B` curve
`k = σ_B⁻¹(j)` assigned to the grid point `j = sel(s z)` of its cell (`σ_B k` is the grid point of `B` curve `k`). -/
def hardTransfer (zB : Fin N → E) (σB : Equiv.Perm (Fin N)) (sel : E → Fin N) (s : ℝ) (z : E) : E :=
  zB (σB.symm (sel (s • z)))

end Hard

/-! ### B `cor:band-coverage-asymptotic` (iv) -/

section Coverage
variable {K : ℕ} {𝒯 : Type*}

/-- The normalised directions `{±e(t)/‖e(t)‖ : t ∈ 𝒯_*}`, `𝒯_* = {t : e(t) ≠ 0}`. -/
def normDirs (e : 𝒯 → Euc K) : Set (Euc K) :=
  {w | ∃ t, e t ≠ 0 ∧ ∃ σ ∈ ({1, -1} : Set ℝ), w = σ • (‖e t‖⁻¹ • e t)}

/-- `ς(p') > 0` (`eq:normalized-nesting`), written as in the premise of the frozen Wave 24d `band_coverage_asymptotic`:
some `ς > 0` with `h_{p'}(σe(t)) + ς‖e(t)‖ ≤ h_p(σe(t))` for `t ∈ 𝒯_*`, `σ = ±1` (`A = A_{K,p}`, `A' = A_{K,p'}`). -/
def NormNesting (μ : Measure (Euc K)) (A A' : Set (Euc K)) (Q : Euc K → Euc K) (e : 𝒯 → Euc K) : Prop :=
  ∃ ς : ℝ, 0 < ς ∧ ∀ t, e t ≠ 0 → ∀ σ ∈ ({1, -1} : Set ℝ),
    popSupp μ A' Q (σ • e t) + ((ς * ‖e t‖ : ℝ) : EReal) ≤ popSupp μ A Q (σ • e t)

/-- Uniform strict nesting of the population edges `x↑_p = 𝔪 + h_p(e)`, `x↓_p = 𝔪 − h_p(−e)`:
`inf_t [x↑_p − x↑_{p'}] > 0` and `inf_t [x↓_{p'} − x↓_p] > 0` (a common positive lower bound `c`). -/
def UnifNesting (μ : Measure (Euc K)) (A A' : Set (Euc K)) (Q : Euc K → Euc K) (mfrak : 𝒯 → ℝ)
    (e : 𝒯 → Euc K) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ t,
    (mfrak t : EReal) + popSupp μ A' Q (e t) + (c : EReal) ≤ (mfrak t : EReal) + popSupp μ A Q (e t) ∧
    (mfrak t : EReal) - popSupp μ A Q (-e t) + (c : EReal) ≤ (mfrak t : EReal) - popSupp μ A' Q (-e t)

/-- `𝒮_{K,p}`: the closed convex set whose support function is `h^pop_{K,p}` (`supplement.tex:802-803`: `h^pop` is
the support function of the closed convex hull `𝒮_{K,p}` of the essential range), `{y : ∀ v, ⟨v, y⟩ ≤ h^pop(v)}`. -/
def popRegion (μ : Measure (Euc K)) (A : Set (Euc K)) (Q : Euc K → Euc K) : Set (Euc K) :=
  {y | ∀ v, ((⟪v, y⟫ : ℝ) : EReal) ≤ popSupp μ A Q v}

end Coverage


/-! ### B `prop:rk-paths`: the curve-space functional -/

section Paths
variable {K : ℕ} {𝒯 : Type*} [MeasurableSpace 𝒯]

/-- `e_1, …, e_K` orthonormal in `L²(𝒯, λ)`: the products are integrable and `∫ e_k e_l dλ = δ_{kl}`. -/
def IsOrthonormalFamily (lam : Measure 𝒯) (e : Fin K → 𝒯 → ℝ) : Prop :=
  ∀ k l, Integrable (fun t => e k t * e l t) lam ∧ ∫ t, e k t * e l t ∂lam = if k = l then 1 else 0

/-- The curve-space functional of a scenario point: `∫_𝒯 (x_c − 𝔪) ι_K(Mv) dλ`, with `x_c(t) = 𝔪(t) + Σ_k c_k e_k(t)`
(the curve with coefficient vector `c = Q̂(τ_{K,p}v)`, i.e. `π_v(p)`) and `ι_K(Mv) = Σ_l (Mv)_l e_l`. -/
def curveFunctional (lam : Measure 𝒯) (e : Fin K → 𝒯 → ℝ) (mfrak : 𝒯 → ℝ) (M : Matrix (Fin K) (Fin K) ℝ)
    (v c : Fin K → ℝ) : ℝ :=
  ∫ t, ((mfrak t + ∑ k, c k * e k t) - mfrak t) * ∑ l, (M *ᵥ v) l * e l t ∂lam

end Paths

namespace Claims

/-! #### B `prop:hard-transfer` -/

/-- (iii), "piecewise constant": the open cells are open and pairwise disjoint, the map is constant (an observed `B`
head) on each, and every point outside all open cells is a tie point (two grid points share the minimal score), for
every cell selection. -/
def hard_piecewise_const : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (N : ℕ) (zB u : Fin N → E) (ψ : Fin N → ℝ)
    (s : ℝ) (σB : Equiv.Perm (Fin N)) (sel : E → Fin N),
    IsCellSelection u ψ sel →
      (∀ j, IsOpen (openCell u ψ s j) ∧ ∀ z ∈ openCell u ψ s j, hardTransfer zB σB sel s z = zB (σB.symm j)) ∧
      (∀ j j', j ≠ j' → Disjoint (openCell u ψ s j) (openCell u ψ s j')) ∧
      ∀ z, (∀ j, z ∉ openCell u ψ s j) →
        ∃ j j', j ≠ j' ∧ lagScore u ψ (s • z) j = lagScore u ψ (s • z) j' ∧ ∀ i, lagScore u ψ (s • z) j ≤ lagScore u ψ (s • z) i

/-- (iii), "hence discontinuous across cell boundaries": at a point where exactly two cells `j ≠ j'` meet (equal
minimal scores, all others strictly larger), with distinct grid points and distinct assigned `B` heads, the point is in
the closure of both open cells and the hard transfer is not continuous there (for every cell selection, `s > 0`). -/
def hard_discontinuous : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (N : ℕ) (zB u : Fin N → E) (ψ : Fin N → ℝ)
    (s : ℝ) (σB : Equiv.Perm (Fin N)) (sel : E → Fin N) (z : E) (j j' : Fin N),
    0 < s → IsCellSelection u ψ sel → j ≠ j' → u j ≠ u j' →
    lagScore u ψ (s • z) j = lagScore u ψ (s • z) j' →
    (∀ i, i ≠ j → i ≠ j' → lagScore u ψ (s • z) j < lagScore u ψ (s • z) i) →
    zB (σB.symm j) ≠ zB (σB.symm j') →
      z ∈ closure (openCell u ψ s j) ∧ z ∈ closure (openCell u ψ s j') ∧
        ¬ ContinuousAt (hardTransfer zB σB sel s) z

/-- The closing sentence, "the rescaling does not change the population target `Q_{B,K} ∘ F_{A,K}`": for scalings
`a, b > 0` of the two pools, the population transfer between the rescaled laws `a#P_A`, `b#P_B`, read back in the
original units, `z ↦ b⁻¹ Q_{bB}(F_{aA}(a z))`, equals `Q_B ∘ F_A` `P_A`-a.e. (`M`-monotone maps, any positive definite
`M`; the rank/quantile maps of the rescaled laws are ANY `M`-monotone rank pair, not the rescaled ones). -/
def hard_scale_target : Prop :=
  ∀ (K : ℕ) (M : Matrix (Fin K) (Fin K) ℝ) (μ PA PB : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure μ]
    (FA QA QB FA' QA' QB' : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (a b : ℝ),
    M.PosDef → μ ≪ volume → MemLp id 2 μ → MemLp id 2 PA → MemLp id 2 PB → 0 < a → 0 < b →
    IsRankPair μ PA FA QA → IsMGradMap M μ PA QA → IsMGradMap M μ PB QB →
    IsRankPair μ (PA.map fun z => a • z) FA' QA' → IsMGradMap M μ (PA.map fun z => a • z) QA' →
    IsMGradMap M μ (PB.map fun z => b • z) QB' →
      (fun z => b⁻¹ • QB' (FA' (a • z))) =ᵐ[PA] fun z => QB (FA z)

/-! #### B `cor:band-coverage-asymptotic` (iv) -/

/-- (iv), first sentence: under the bounded-range hypothesis of `thm:band-containment` on both regions (positive
content), `ς(p') > 0` iff `h_p > h_{p'}` on the closure `𝒲` of the normalised directions. -/
def bca_iv_closure : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ : Measure (Euc K)) (A A' : Set (Euc K)) (Q : Euc K → Euc K) (e : 𝒯 → Euc K),
    (∃ R : ℝ, ∀ᵐ u ∂μ.restrict A, ‖Q u‖ ≤ R) → (∃ R : ℝ, ∀ᵐ u ∂μ.restrict A', ‖Q u‖ ≤ R) → μ A ≠ 0 → μ A' ≠ 0 →
      (NormNesting μ A A' Q e ↔ ∀ w ∈ closure (normDirs e), popSupp μ A' Q w < popSupp μ A Q w)

/-- (iv), second sentence: with `E_K = sup_t ‖e(t)‖ < ∞` (the setting of the section), uniform strict nesting of the
population edges implies `ς(p') > 0`. -/
def bca_iv_nesting : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ : Measure (Euc K)) (A A' : Set (Euc K)) (Q : Euc K → Euc K) (mfrak : 𝒯 → ℝ)
    (e : 𝒯 → Euc K) (EK : ℝ),
    (∃ R : ℝ, ∀ᵐ u ∂μ.restrict A, ‖Q u‖ ≤ R) → (∃ R : ℝ, ∀ᵐ u ∂μ.restrict A', ‖Q u‖ ≤ R) → μ A ≠ 0 → μ A' ≠ 0 →
    (∀ t, ‖e t‖ ≤ EK) →
      UnifNesting μ A A' Q mfrak e → NormNesting μ A A' Q e

/-- (iv), "and is equivalent to it when `inf_t ‖e(t)‖ > 0`". -/
def bca_iv_nesting_iff : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ : Measure (Euc K)) (A A' : Set (Euc K)) (Q : Euc K → Euc K) (mfrak : 𝒯 → ℝ)
    (e : 𝒯 → Euc K) (EK : ℝ),
    (∃ R : ℝ, ∀ᵐ u ∂μ.restrict A, ‖Q u‖ ≤ R) → (∃ R : ℝ, ∀ᵐ u ∂μ.restrict A', ‖Q u‖ ≤ R) → μ A ≠ 0 → μ A' ≠ 0 →
    (∀ t, ‖e t‖ ≤ EK) → (∃ b : ℝ, 0 < b ∧ ∀ t, b ≤ ‖e t‖) →
      (NormNesting μ A A' Q e ↔ UnifNesting μ A A' Q mfrak e)

/-- (iv), last sentence: if `𝒮_{K,p'} ⊂ int 𝒮_{K,p}`, then `ς(p') > 0` for every basis (every index set `𝒯` and
evaluation map `e`). -/
def bca_iv_interior : Prop :=
  ∀ (K : ℕ) (μ : Measure (Euc K)) (A A' : Set (Euc K)) (Q : Euc K → Euc K),
    (∃ R : ℝ, ∀ᵐ u ∂μ.restrict A, ‖Q u‖ ≤ R) → (∃ R : ℝ, ∀ᵐ u ∂μ.restrict A', ‖Q u‖ ≤ R) → μ A ≠ 0 → μ A' ≠ 0 →
    popRegion μ A' Q ⊆ interior (popRegion μ A Q) →
      ∀ (𝒯 : Type) (e : 𝒯 → Euc K), NormNesting μ A A' Q e

/-! #### B `thm:consistency`, general symmetric positive definite `M_K` -/

/-- B `thm:consistency` for a general symmetric positive definite `M_K` (cost `‖z − u‖²_{M_K}`): the estimator class
of the frozen WaveP3c `ghosal_sen_uniform` for the `M_K`-cost — `ψ̂_n` convex and `L'`-Lipschitz (`L' ≥ ‖M_K u‖` on the
reference ball), a coupling `γ_n` of `P̂_n` and `μ_K` carried by `{(z, u) : M_K u ∈ ∂ψ̂_n(z)}`, `F̂_n(x)` ANY `u` with
`M_K u ∈ ∂ψ̂_n(x)` — and the `M_K`-monotone population rank map (`M_K F ∈ ∂ψ` `P_K`-a.e., `F#P_K = μ_K`, `ψ`
differentiable with gradient `M_K F` on `𝒦`). Then: the deterministic depth bound, and almost surely
`ε_n(𝒦) = sup_𝒦 ‖F̂_n − F‖ → 0` and both depths converge uniformly over `{x : Π_K x ∈ 𝒦}` (the conclusions of the frozen
`consistency_B_gs`, which is the case `M_K = I`, plus `ε_n(𝒦) → 0`). -/
def cons_general_M : Prop :=
  ∀ (K : ℕ) (Ω H : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (Z : ℕ → Ω → Euc K)
    (P μ : ProbabilityMeasure (Euc K)) (MK : Matrix (Fin K) (Fin K) ℝ) (ψ : Euc K → ℝ) (F : Euc K → Euc K)
    (R L L' : ℝ) (ψh : ℕ → Ω → Euc K → ℝ) (γ : ℕ → Ω → ProbabilityMeasure (Euc K × Euc K))
    (Fh : ℕ → Ω → Euc K → Euc K) (𝒦 : Set (Euc K)) (PiK : H → Euc K) (g : Euc K → ℝ) (cK : ℝ → ℝ) (c' : ℝ),
    MK.PosDef →
    iIndepFun Z Pr → (∀ i, HasLaw (Z i) (P : Measure (Euc K)) Pr) → (P : Measure (Euc K)) ≪ volume →
    (μ : Measure (Euc K)) (Metric.closedBall 0 R)ᶜ = 0 → (∀ u ∈ Metric.closedBall (0 : Euc K) R, ‖mvec MK u‖ ≤ L') →
    ConvexOn ℝ univ ψ → (∀ x x', |ψ x - ψ x'| ≤ L * ‖x - x'‖) →
    Measurable F → (P : Measure (Euc K)).map F = μ → (∀ᵐ x ∂(P : Measure (Euc K)), IsSubgrad ψ x (mvec MK (F x))) →
    IsCompact 𝒦 → 𝒦 ⊆ interior (P : Measure (Euc K)).support → (∀ x ∈ 𝒦, HasGradientAt ψ (mvec MK (F x)) x) →
    (∀ n ω, (γ n ω : Measure (Euc K × Euc K)).fst = (empiricalMeasure (fun i => Z i ω) n : Measure (Euc K))) →
    (∀ n ω, (γ n ω : Measure (Euc K × Euc K)).snd = μ) →
    (∀ n ω, (γ n ω : Measure (Euc K × Euc K)).support ⊆ {p | IsSubgrad (ψh n ω) p.1 (mvec MK p.2)}) →
    (∀ n ω x x', |ψh n ω x - ψh n ω x'| ≤ L' * ‖x - x'‖) →
    (∀ n ω, ∀ x ∈ 𝒦, IsSubgrad (ψh n ω) x (mvec MK (Fh n ω x))) →
    (∀ a b, g (a + b) ≤ g a + g b) → (∀ a, g (-a) = g a) → (∀ a, g a ≤ c' * ‖a‖) → Continuous cK →
    (∀ z ∈ 𝒦, g (F z) ≤ 1) →
      (∀ n ω x, |(1 - g (Fh n ω (PiK x))) - (1 - g (F (PiK x)))| ≤ c' * ‖Fh n ω (PiK x) - F (PiK x)‖) ∧
      ∀ᵐ ω ∂Pr, TendstoUniformlyOn (fun n => Fh n ω) F atTop 𝒦 ∧
        TendstoUniformlyOn (fun n x => 1 - g (Fh n ω (PiK x))) (fun x => 1 - g (F (PiK x))) atTop
          {x | PiK x ∈ 𝒦} ∧
        TendstoUniformlyOn (fun n x => 1 - cK (g (Fh n ω (PiK x)))) (fun x => 1 - cK (g (F (PiK x)))) atTop
          {x | PiK x ∈ 𝒦}


/-- B `thm:consistency`, "`c'_K := max_{‖u‖₂=1} g_K(u)`, which is `λ_max(M_K)^{1/2}` for the naive and ball laws, the
smallest constant with `g_K ≤ c'_K‖·‖₂`": for the gauge `g_K = ‖·‖_{M_K}` (`mnorm`, frozen Wave 8c), `λ_max(M_K)^{1/2}`
(`λ_max = max_i` of the eigenvalues) is the maximum of `g_K` on the Euclidean unit sphere, and `g_K ≤ c‖·‖₂` holds iff
`c ≥ λ_max(M_K)^{1/2}` (`K ≥ 1`). -/
def cons_cprime : Prop :=
  ∀ (K : ℕ) (M : Matrix (Fin K) (Fin K) ℝ) (hM : M.PosDef), 0 < K →
    IsGreatest {c | ∃ u : EuclideanSpace ℝ (Fin K), ‖u‖ = 1 ∧ c = mnorm M u}
        (Real.sqrt (⨆ i, hM.isHermitian.eigenvalues i)) ∧
      ∀ c : ℝ, (∀ u, mnorm M u ≤ c * ‖u‖) ↔ Real.sqrt (⨆ i, hM.isHermitian.eigenvalues i) ≤ c

/-! #### B certified edges: `lem:band-pointwise-lower`, `prop:cubic-band-infinite` (iv), `prop:trimmed-band` (ii) -/

/-- `lem:band-pointwise-lower`, "or by the certified support `x̄↑_{n,p}(t) − 𝔪(t)` at `v = e(t)`": in the setting of the
certified WaveP2a `band_pointwise_lower` (`ass:fixedK-oos` as printed, `T` a McCann Brenier map), almost surely,
simultaneously for every measurable region `A`, EVERY sequence of lower bounds `δ_{n,j} ≤ δ_j(A)` of the reachability
gaps of the `n`-th entropic fit (`prop:band-certificate`(ii)–(iii); scores `oosA`, `oosB` at `M_K = I`, region read in
`Fin K → ℝ` coordinates) and every `v`, `liminf_n knapUp(κ_n, ⟨v, Z_j⟩) ≥ h^pop(v)`, where `knapUp(κ_n, ⟨v, Z_j⟩)` with
the entropic caps `κ_{n,j} = e^{−δ_{n,j}/ε_n}` is the certified support (frozen Wave 14c: `certUp κ Z 𝔪 v = 𝔪 + knapUp`). -/
def bpl_certified : Prop :=
  ∀ (K : ℕ) (μ P : ProbabilityMeasure (Euc K)) (μs : ℕ → ProbabilityMeasure (Euc K)) (Ω : Type)
    [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (Z : ℕ → Ω → Euc K) (ε : ℕ → ℝ)
    (f : (n : ℕ) → Ω → Fin (n + 1) → ℝ) (r : ℕ → Ω → ℝ) (T : Euc K → Euc K),
    FixedKOOSInexact μ P μs Pr Z ε f r →
    HasLaw T (P : Measure (Euc K)) (μ : Measure (Euc K)) → IsCMMapAE (μ : Measure (Euc K)) T →
      ∀ᵐ ω ∂Pr, ∀ A : Set (Euc K), MeasurableSet A → ∀ δ : (n : ℕ) → Fin (n + 1) → ℝ,
        (∀ n j, δ n j ≤ gap (oosA 1 (f n ω) fun i : Fin (n + 1) => WithLp.ofLp (Z i ω))
          (oosB 1 fun i : Fin (n + 1) => WithLp.ofLp (Z i ω)) (WithLp.ofLp '' A) j) →
        ∀ v : Euc K, popSupp (μ : Measure (Euc K)) A T v ≤
          liminf (fun n => knapUp (entCaps (ε n) (δ n))
            (fun j : Fin (n + 1) => WithLp.ofLp v ⬝ᵥ WithLp.ofLp (Z j ω))) atTop

/-- `prop:cubic-band-infinite` (iv), "and so do the certified edges": in the setting of the certified WaveP3a
`cubic_edges_diverge` (cubic reference, matched Gaussian, `ass:fixedK-oos` as printed), almost surely, simultaneously
for every `p ∈ (0, 1]`, every sequence of lower bounds of the reachability gaps over `A_{K,p}` and every `t` with
`e_k(t) ≠ 0` for some `k ∈ 𝒦_p`, the certified edges `x̄↑_{n,p}(t) → +∞` and `x̄↓_{n,p}(t) → −∞`. -/
def cbi_certified_diverge : Prop :=
  ∀ (N : ℕ) (a : Fin N → ℝ) (Dinf : ℝ) (μ P : ProbabilityMeasure (EuclideanSpace ℝ (Fin N)))
    (μs : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin N))) (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω)
    [IsProbabilityMeasure Pr] (Z : ℕ → Ω → EuclideanSpace ℝ (Fin N)) (ε : ℕ → ℝ)
    (f : (n : ℕ) → Ω → Fin (n + 1) → ℝ) (r : ℕ → Ω → ℝ) (𝒯 : Type) (mfrak : 𝒯 → ℝ)
    (e : 𝒯 → EuclideanSpace ℝ (Fin N)),
    (∀ k, 0 < a k) → 0 < Dinf → (μ : Measure (EuclideanSpace ℝ (Fin N))) = cubicLawE a →
    (P : Measure (EuclideanSpace ℝ (Fin N))) = gaussProdE a →
    FixedKOOSInexact μ P μs Pr Z ε f r →
      ∀ᵐ ω ∂Pr, ∀ p : ℝ, 0 < p → p ≤ 1 → ∀ δ : (n : ℕ) → Fin (n + 1) → ℝ,
        (∀ n j, δ n j ≤ gap (oosA 1 (f n ω) fun i : Fin (n + 1) => WithLp.ofLp (Z i ω))
          (oosB 1 fun i : Fin (n + 1) => WithLp.ofLp (Z i ω)) (WithLp.ofLp '' cubicRegion a Dinf p) j) →
        ∀ t, (∃ k, 2 * a k ≤ 2 * (StatFormal.OTFD.Wave8c.tauKp a Dinf p * Dinf) ∧ e t k ≠ 0) →
          Tendsto (fun n => certUp (entCaps (ε n) (δ n)) (fun i : Fin (n + 1) => WithLp.ofLp (Z i ω)) (mfrak t)
            (WithLp.ofLp (e t))) atTop (𝓝 ⊤) ∧
          Tendsto (fun n => certLo (entCaps (ε n) (δ n)) (fun i : Fin (n + 1) => WithLp.ofLp (Z i ω)) (mfrak t)
            (WithLp.ofLp (e t))) atTop (𝓝 ⊥)

/-- `prop:cubic-band-infinite` (iv), "and the edges of every selected hard map": in the same setting, for ANY maps
`ξ_n(ω, ·)` with `ξ_n(ω, u) ∈ ∂χ_n(u)` for every `u` (`χ_n` the Laguerre potential of the fitted dual vector, frozen
Wave 23c `lagPot`), almost surely, for every `p ∈ (0, 1]` and every `t` with `e_k(t) ≠ 0` for some `k ∈ 𝒦_p`,
`𝔪(t) + sup_{A_{K,p}} ⟨e(t), ξ_n⟩ → +∞` and `𝔪(t) − sup_{A_{K,p}} ⟨−e(t), ξ_n⟩ → −∞`. -/
def cbi_hard_diverge : Prop :=
  ∀ (N : ℕ) (a : Fin N → ℝ) (Dinf : ℝ) (μ P : ProbabilityMeasure (EuclideanSpace ℝ (Fin N)))
    (μs : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin N))) (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω)
    [IsProbabilityMeasure Pr] (Z : ℕ → Ω → EuclideanSpace ℝ (Fin N)) (ε : ℕ → ℝ)
    (f : (n : ℕ) → Ω → Fin (n + 1) → ℝ) (r : ℕ → Ω → ℝ) (𝒯 : Type) (mfrak : 𝒯 → ℝ)
    (e : 𝒯 → EuclideanSpace ℝ (Fin N)) (ξ : ℕ → Ω → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)),
    (∀ k, 0 < a k) → 0 < Dinf → (μ : Measure (EuclideanSpace ℝ (Fin N))) = cubicLawE a →
    (P : Measure (EuclideanSpace ℝ (Fin N))) = gaussProdE a →
    FixedKOOSInexact μ P μs Pr Z ε f r →
    (∀ n ω u y, StatFormal.Wave23c.lagPot (fun i : Fin (n + 1) => Z i ω) (f n ω) u + ⟪ξ n ω u, y - u⟫_ℝ ≤
      StatFormal.Wave23c.lagPot (fun i : Fin (n + 1) => Z i ω) (f n ω) y) →
      ∀ᵐ ω ∂Pr, ∀ p : ℝ, 0 < p → p ≤ 1 → ∀ t,
        (∃ k, 2 * a k ≤ 2 * (StatFormal.OTFD.Wave8c.tauKp a Dinf p * Dinf) ∧ e t k ≠ 0) →
        Tendsto (fun n => (mfrak t : EReal) + fitSupp (cubicRegion a Dinf p) (ξ n ω) (e t)) atTop (𝓝 ⊤) ∧
          Tendsto (fun n => (mfrak t : EReal) - fitSupp (cubicRegion a Dinf p) (ξ n ω) (-e t)) atTop (𝓝 ⊥)

/-- `prop:trimmed-band` (ii), "the conclusions of `thm:band-containment` hold for the trimmed bands, the certified one
included": in the setting of the certified WaveP3a `trimmed_containment`, almost surely, for every sequence of lower
bounds of the reachability gaps over the trimmed region `A^{δ'} = A ∩ (1 − δ')𝒰_K` (any valid upper bound on
`σ_{A^{δ'}}` in `prop:band-certificate`(ii) gives one), for every `η > 0`, eventually, for all `t`,
`x↑pop,δ' ≤ x̄↑_n,δ' + η` and `x̄↓_n,δ' ≤ x↓pop,δ' + η`. -/
def trim_certified_containment : Prop :=
  ∀ (K : ℕ) (μ P : ProbabilityMeasure (EuclideanSpace ℝ (Fin K))) (μs : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin K)))
    (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (Z : ℕ → Ω → EuclideanSpace ℝ (Fin K))
    (ε : ℕ → ℝ) (f : (n : ℕ) → Ω → Fin (n + 1) → ℝ) (r : ℕ → Ω → ℝ)
    (T : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (𝒯 : Type) (A : Set (EuclideanSpace ℝ (Fin K)))
    (mfrak : 𝒯 → ℝ) (e : 𝒯 → EuclideanSpace ℝ (Fin K)) (δ : ℝ),
    FixedKOOSInexact μ P μs Pr Z ε f r →
    HasLaw T (P : Measure (EuclideanSpace ℝ (Fin K))) (μ : Measure (EuclideanSpace ℝ (Fin K))) →
    IsCMMapAE (μ : Measure (EuclideanSpace ℝ (Fin K))) T →
    MeasurableSet A → (0 : EuclideanSpace ℝ (Fin K)) ∈ interior (μ : Measure (EuclideanSpace ℝ (Fin K))).support →
    0 < δ → δ < 1 → (∃ C : ℝ, ∀ t, ‖e t‖ ≤ C) →
      ∀ᵐ ω ∂Pr, ∀ dl : (n : ℕ) → Fin (n + 1) → ℝ,
        (∀ n j, dl n j ≤ gap (oosA 1 (f n ω) fun i : Fin (n + 1) => WithLp.ofLp (Z i ω))
          (oosB 1 fun i : Fin (n + 1) => WithLp.ofLp (Z i ω))
          (WithLp.ofLp '' (A ∩ (1 - δ) • (μ : Measure (EuclideanSpace ℝ (Fin K))).support)) j) →
        ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t,
          (mfrak t : EReal) + popSupp (μ : Measure (EuclideanSpace ℝ (Fin K)))
              (A ∩ (1 - δ) • (μ : Measure (EuclideanSpace ℝ (Fin K))).support) T (e t) ≤
            certUp (entCaps (ε n) (dl n)) (fun i : Fin (n + 1) => WithLp.ofLp (Z i ω)) (mfrak t)
              (WithLp.ofLp (e t)) + (η : EReal) ∧
          certLo (entCaps (ε n) (dl n)) (fun i : Fin (n + 1) => WithLp.ofLp (Z i ω)) (mfrak t)
              (WithLp.ofLp (e t)) ≤
            (mfrak t : EReal) - popSupp (μ : Measure (EuclideanSpace ℝ (Fin K)))
              (A ∩ (1 - δ) • (μ : Measure (EuclideanSpace ℝ (Fin K))).support) T (-e t) + (η : EReal)

/-! #### B `prop:rk-paths` -/

/-- (i), "equivalently, in curve space": for an orthonormal basis `e_1, …, e_K` of `L²(𝒯, λ)` the curve-space functional
`∫_𝒯 (π_v(p) − 𝔪) ι_K(M_K v)` of the scenario path equals `⟨v, Q̂(τ_{K,p}v)⟩_{M_K}` at every level, so, for any
selection `T(u) ∈ ½M⁻¹∂ψ(u)` of a convex `ψ` (the frozen hypotheses of Wave 24a `rk_paths_mono`) and any nondecreasing
`p ↦ τ_p` on `𝒫_v`, it is nondecreasing on `𝒫_v`. -/
def rkp_curve_mono : Prop :=
  ∀ (K : ℕ) (M : Matrix (Fin K) (Fin K) ℝ) (ψ : (Fin K → ℝ) → ℝ) (T : (Fin K → ℝ) → Fin K → ℝ) (v : Fin K → ℝ)
    (τ : ℝ → ℝ) (Pv : Set ℝ) (𝒯 : Type) [MeasurableSpace 𝒯] (lam : Measure 𝒯) (e : Fin K → 𝒯 → ℝ) (mfrak : 𝒯 → ℝ),
    M.PosDef → ConvexOn ℝ Set.univ ψ → (∀ u y, ψ u + (2 • (M *ᵥ T u)) ⬝ᵥ (y - u) ≤ ψ y) → MonotoneOn τ Pv →
    IsOrthonormalFamily lam e →
      (∀ p, curveFunctional lam e mfrak M v (T (τ p • v)) = (M *ᵥ v) ⬝ᵥ T (τ p • v)) ∧
        MonotoneOn (fun p => curveFunctional lam e mfrak M v (T (τ p • v))) Pv

/-- (i), strictness in curve space: for the entropic map with affinely spanning `Z_j` (the hypotheses of the frozen
WaveP1d `rk_paths_strict`), the curve-space functional is strictly increasing on `[0, 1] ⊇ 𝒫_v`. -/
def rkp_curve_strict : Prop :=
  ∀ (K n : ℕ) (ε : ℝ) (M : Matrix (Fin K) (Fin K) ℝ) (Z : Fin n → Fin K → ℝ) (f : Fin n → ℝ)
    (μ : Measure (EuclideanSpace ℝ (Fin K))) (ρ : EuclideanSpace ℝ (Fin K) → ℝ) (v : Fin K → ℝ)
    (𝒯 : Type) [MeasurableSpace 𝒯] (lam : Measure 𝒯) (e : Fin K → 𝒯 → ℝ) (mfrak : 𝒯 → ℝ),
    0 < ε → M.PosDef → affineSpan ℝ (Set.range Z) = ⊤ → v ≠ 0 →
    ContinuousOn (StatFormal.Wave23a.cdfK μ ρ) (Icc 0 1) → StatFormal.Wave23a.cdfK μ ρ 0 = 0 →
    StatFormal.Wave23a.cdfK μ ρ 1 = 1 → IsOrthonormalFamily lam e →
      StrictMonoOn (fun p => curveFunctional lam e mfrak M v
        (StatFormal.OTFD.Bands.Qent ε M Z f (StatFormal.Wave23a.cdfKInv μ ρ p • v))) (Icc 0 1)

end Claims

end StatFormal.Wave29b
