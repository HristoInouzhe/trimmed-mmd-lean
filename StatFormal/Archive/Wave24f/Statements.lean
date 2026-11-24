import StatFormal.Archive.OTFD.WaveL3.Statements
import StatFormal.Archive.OTFD.Wave16b.Statements
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.SpecialFunctions.Arcosh
import StatFormal.Archive.Wave23a.Statements
import TauCeti.Probability.Quantile
import Mathlib.Probability.CDF
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.Fourier.LpSpace
import StatFormal.Lib.Distances.TV
import StatFormal.Archive.NNFibers.Statements
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Data.Fintype.Sigma

/-!
# FROZEN STATEMENTS — wave 24f (QUEUE rows 380–393): otfd C `lem:ref-potential-limit` (c); G `lem:reduction` (ii)–(iii),
# `lem:jacobicosh` (matrix core), `lem:polish` (flat); T `prop:hadamard-distortion`, `prop:chartsafe`; SB `thm:copbary`,
# `cor:field-npn` (exactness), `lem:equiv` (static identity); NN `lem:marked-block-transform` (exact part); A
# `lem:lift-cost`, `cor:app-sample-rate`; TM `thm:interp`

Sources (verbatim in `lean-formalisation/inventory/extracted/{otfd-C_conditional,otfd-G_geodesic,otfd-T_tangent,
data-fairness-repair,proliferation-nns,otfd-A_sieves,trimmed-mmd}.md`; current text checked 2026-10-16):
* C `lem:ref-potential-limit` (`otfd/papers/C_conditional/supplement.tex:279-290`, proof `:292-350`), with the conjugate
  Kantorovich pair and Brenier potential (`:269-277`).
* G `lem:reduction` (`otfd/papers/G_geodesic/appendix.tex:299-319`, proof `:321-368`); `lem:jacobicosh`
  (`appendix.tex:131-148`, proof `:150-201`); `lem:polish` (`main.tex:242-245`, proof `appendix.tex:3-56`).
* T `prop:hadamard-distortion` with `eq:hadamard-lower`, `eq:hadamard-two-sided` (`otfd/papers/T_tangent/supp_moved.tex:
  59-79`, proof `app_proofs.tex:332-345`); `prop:chartsafe` (`supp_moved.tex:894-905`) with `eq:Hembed`
  (`sec_tangent_theory.tex:62-66`).
* SB `thm:copbary` (`data-fairness-repair/schrodinger_bridge_fairness_repair.tex:1309-1323`, proof `:1325-1340`) with
  `eq:repaircost` (`:1203-1208`); `cor:field-npn` (`:1064-1086`); `lem:equiv` (`:414-423`, proof `:2662-2679`) with
  `eq:static` (`:385-390`).
* NN `lem:marked-block-transform` (`proliferation-and-geometry-in-nns/paper_revised.tex:1001-1019`, proof
  `tube_asymptotics_proof.tex:39-76`) with `eq:data` (`paper_revised.tex:521-525`), `prop:disjoint` (`:530-535`).
* A `lem:lift-cost` (`otfd/papers/A_sieves/main.tex:1137-1151`); `cor:app-sample-rate` (`supplement.tex:2934-2959`) with
  `prop:rate-decomp` (`:2353-2398`) and `ass:app-grid-stability` (`:2437-2465`).
* TM `thm:interp` (`trimmed-mmd/paper.tex:1314-1322`, proof `supplement.tex:506-519`) with `ass:smooth` (`paper.tex:
  1298-1303`).
Imports the frozen `OTFD/WaveL3` (`Mom1`; through it `WaveL1`: `Euc`, `LipNull`, `IsCMMapAE`; `Wave8b`: `embed`; `Wave1`:
`truncK`), `OTFD/Wave16b` (`rmsE`), `Wave23a` (`barF`, `IsBarycenter`) and `NNFibers` (`bell`) statements, not copied;
Mathlib, Tau Ceti (`wassersteinEDist`, `HasFiniteMoment`, `Measure.quantile`) and the locked import
`Foundations/Distances/TV` (`tvDist`, the supremum over measurable sets) otherwise.

Covered:
* C (c): `ref_potential_unique` (on `S = closure Ω`, `Ω ⊆ ℝ^q` bounded, open, connected, `supp ν_X = S`, `P_C` carried
  by a compact `D`: two normalised conjugate Kantorovich pairs agree on `S × D`; no density).
* G `lem:reduction`: `reduction_cond` ((ii), general reference `μ` on the unit ball of `S`: `Z(z) ∈ (0, ∞)`,
  `π(·|z)` a probability, `π(·|z) = π(·|Πz)`, invariance under `f ↦ f + a` a.e.), `reduction_tilt` ((iii): `ν` finite,
  `ν ~ μ`, `π(·|y) = ν_{βy/ε}`), `reduction_inject` ((iii), finite reference `μ_r`: `Φ_S` continuous and injective
  on `S` under the non-degeneracy hypothesis).
* G `lem:jacobicosh`: `jacobicosh_core` (`𝖠'' + 𝖱𝖠 = 0`, `𝖠(0) = I`, `𝖠'(0) = 0`, `−κ² ≤ 𝖱 ≤ 0`:
  `‖y‖ ≤ ‖𝖠(r)y‖ ≤ cosh(κr)‖y‖`).
* G `lem:polish`: `polish_flat` (`M = ℝ^q`).
* T: `hadamard_lower` (`eq:hadamard-lower`), `hadamard_two_sided` (`eq:hadamard-two-sided`), `hadamard_cost` (the
  cost and `OT` orderings) on the hyperbolic space of curvature `−k²`; `chartsafe_tube`, `chartsafe_embed`.
* SB `thm:copbary`: `copbary_bary` ((i)), `copbary_map` ((ii): pushforward and optimality), `copbary_cost` ((iii):
  parity and `𝒥(T) = 𝒥⋆`).
* SB `cor:field-npn`: `field_npn_std` (`𝕊_μ # μ = N(0, I)`), `field_npn_exact` (`(T_s)#R_s = ν`).
* SB `lem:equiv`: `equiv_static` (`ε KL(π ‖ R₀₁) = ½∫‖x − y‖²dπ − ε Ent(π) + ε Ent(μ) + (εd/2) log(2πε)`).
* NN: `marked_block_count`, `marked_block_transform` (`eq:exact-marked-pgf`).
* A: `lift_cost_identity`, `lift_cost_integral`, `lift_cost_entropic` (`lem:lift-cost`); `app_sample_rate`.
* TM: `interp_core`, `interp_bound` (`thm:interp`).

Not covered (declared):
* C (a), (b) (Arzelà–Ascoli on the Schrödinger potentials, uniform Laplace principle, weak limits of entropic plans).
* G `lem:reduction` (i) (Nutz's Gibbs-form uniqueness for general `μ`, `Q`; the fitted special case is the certified
  Wave 24b `blindspot_fit_factor`); in (ii), "a function of `Πz` determined by `(μ, Q_S, β, ε)`" (`f_S` unique
  `μ`-a.e. up to a constant, again Nutz; here `f` is any function satisfying `ReductionHyp`); the injectivity in
  (iii) for non-atomic `μ` (differentiation under the integral).
* G `lem:jacobicosh`: the Riemannian part (Jacobi fields, symmetry lemma, the tangential/normal splitting giving
  `|J|² ≤ a² + cosh²(…)(|σ'|² − a²)`, the constant-curvature equality, the parallel-transport corollary and its
  sharpness); only the normal-frame matrix ODE is formalised.
* G `lem:polish`: curved `M` (completeness and separability of `L²(λ; M)`, measurable selection of minimal geodesics).
* T: general Hadamard manifolds (Cartan–Hadamard, Rauch comparison), including variable curvature and the flat
  case `k = 0`; `Log_{m(t)}` globally defined; in
  `prop:chartsafe`, "logarithmic inversion remains valid" (injectivity radius).
* SB `thm:copbary`: uniqueness of the barycenter and of the Brenier map (these need the a.c. hypothesis); the rate
  `n^{-1/2}` in (iii) (quantile processes). `cor:field-npn`: the operator-norm rate and Winsorisation.
  `lem:equiv`: the dynamic part (path space, Brownian bridges, the KL chain rule), existence/uniqueness of `P⋆_ε`.
* NN: `eq:marked-pgf-asymptotic`, `eq:marked-pgf-power` (saddle point / Hayman); so no discharge of the Wave 24c
  hypothesis (`average_offset_penalty` assumes the asymptotic, not the exact identity).
* A `lem:lift-cost`: "the projected potentials solve the full problem only when this factor is constant" (informal;
  not even true as an iff in general). `cor:app-sample-rate`: the bijective-grid rate for `Δ^{emp}` (that is
  `cor:app-bijective-rate`).
* TM: the kernel comparison `‖·‖_{H^{−s}} ≤ A_k MMD_k` itself (it defines `A_k`; hypothesis).
* ICL `lem:cond-measurable` (row 390): NOT ATTEMPTED — (i)–(ii) need the identification of the Borel σ-algebra of the
  weak topology on `𝒫(𝒵)` with the Giry σ-algebra, absent from Mathlib, and (iii) the Donsker–Varadhan formula
  (absent); value 1, and the ranking marks it worthwhile only together with `prop:cond-target`(i).

Encodings (to be checked by the critic):
* C: `ℝ^q = Euc q`; `IsConjPair` (continuity on `S`, `D`; the two `min` formulas as "≤ for all, = for some"; the
  duality equality in `ℝ` with `W₂² = (wassersteinEDist 2)²`, finite since both laws have compact support, so
  `toReal` is not a junk value); `supp ν_X = S` as `ν_X(Sᶜ) = 0` plus positive mass of every ball centred in `S`;
  `D = supp P_C` weakened to `P_C(Dᶜ) = 0`, `D` compact (paper: compact); the normalisation `∫ φ dP_C = 0`.
* G reduction: `H` a real inner product space (complete for `reduction_inject`, so the Bochner integral of `v` is not
  junk); `c_β(v, z) = ½‖βv − z‖²` (`cBeta`); `Z`, `π(·|z)` (`gibbsZ`, `condLaw`) for any measurable `f`; the
  potential property is the hypothesis `ReductionHyp` (Schrödinger equation at one `y₀` with finite `g(y₀)`, which the
  paper derives from `g_S ∈ L¹(Q_S)`); `ν_θ` (`tiltLaw`); `μ_r = Σ_j b_j δ_{V_j}` (`atomLaw`); "`⟨v, h⟩` not
  `μ_r`-a.s. constant" as `∃ j l, ⟨V_j, h⟩ ≠ ⟨V_l, h⟩` (`b_j > 0`).
* G jacobicosh: operators `E →L[ℝ] E` on a finite-dimensional real inner product space (the normal frame);
  `A'` given with `HasDerivAt A A'`, `HasDerivAt A' (−R ∘ A)` on `ℝ`; `R(r)` symmetric for all `r`, the curvature
  bounds for `r ≥ 0` (the paper's `−κ²|w|² ≤ 𝖱` is this with `κ|w|`).
* G polish: `T = [0, 1]` (`Icc` subtype) with any probability `λ`; `𝒳 = Lp (Euc q) 2 λ`; separability as
  `SeparableSpace`; the geodesic with `x_0 = x`, `x_1 = x'`.
* T: SPECIALISATION — `prop:hadamard-distortion` is printed for every finite-dimensional Hadamard manifold; here
  `M` is the single model space of constant curvature `−k²`, `k > 0` (a faithful instance, not the general
  statement; generalised only in allowing `dim E = ∞`). The hyperboloid model `H_k = {B(x, x) = −1/k², x₀ > 0}`
  in `ℝ × E` (`minkB`, `OnHyp`), `T_pH_k = p^⊥_B`
  (`minkB p v = 0`), `|v| = √B(v, v)` (`tanNorm`; `B ≥ 0` on `p^⊥`, proved), `Exp_p` (`hypExp`; at `v = 0` Lean's
  `sinh 0/0 = 0` gives `Exp_p 0 = p`, the true value), `d = arcosh(−k²B)/k` (`hypDist`; argument `≥ 1` on `H_k`);
  curves `x ∈ X` given by their log fields `ℓ_x(t) ∈ T_{m(t)}H_k`; costs as lower integrals in `[0, ∞]`; `OT_c`
  (`otCost`) = inf over couplings. chartsafe: tangent spaces `Etan t` normed; `eq:Hembed` as
  `‖ev_t h‖ ≤ Λ‖h‖_H` for continuous linear evaluations, `Λ ≥ 0` (implicit in the paper).
* SB copbary: `ℝ^d = Euc d`; groups `Fin S` (paper: two), `Σ p_s = 1`; continuous marginals as `NullSingletonClass`;
  a copula is a law on `ℝ^d` with uniform `(0,1)` marginals (`IsCopula`); `R_s = copLaw C (F_{s,·}^{-1})` (Sklar's
  representation for continuous marginals), `ν = copLaw C (G^{-1})`, `G_i^{-1} = Σ_s p_s F_{s,i}^{-1}` (`baryQ`),
  `T_s = copMap` (Tau Ceti quantiles; the junk values at levels `0`, `1` are never reached a.e.); `R_s ∈ 𝒫₂`
  (`HasFiniteMoment 2`, `ass:main`) for (i); `𝒥⋆ = inf_ω F(ω)` over probability laws.
* SB field-npn: `Φ = cdf N(0,1)`, `Φ^{-1}` its Tau Ceti quantile; `Z_μ` (`zScore`) from the marginal cdfs; the class
  `𝔐` as `InNPN μ R` (`Z_μ # μ = N(0, R)`, Mathlib's `multivariateGaussian`); `R^{1/2} = CFC.sqrt R`,
  `R^{-1/2} = (R^{1/2})⁻¹` (`invSqrt`), `R_s ≻ 0` (needed for `R_s^{-1/2}`), `R_ν ⪰ 0`; `G_i` the marginals of `ν`,
  continuous.
* SB equiv: `π` with Lebesgue density `p` on `ℝ^d × ℝ^d`, first marginal density `m = ∫ p(·, y) dy` assumed `> 0`
  everywhere (specialisation: `R₀₁` then has a positive density); `R₀₁ = m(x) φ_ε(y − x) dx dy` (`refEndpoint`,
  `gaussDens`); KL is Mathlib's `klDiv` (proved finite); `Ent` the differential entropy `−∫ p log p`; the
  integrability hypotheses are those under which `Ent(π)`, `Ent(μ)`, `∫‖x − y‖² dπ` are finite.
* NN: `𝒟_{q,m}` as `Σ P : Finpartition [m], [q] ↪ blocks(P)` (`LabPart`), the uniform law as the normalised sum
  (`markedPGF`); `exp(e^x − 1)` as its coefficient series `Σ B_n xⁿ/n!` with `B_n` the frozen `NNFibers.bell`
  (number of set partitions; the classical identity of the two series is not formalised); `e^{zx} − 1 =
  rescale z (exp) − 1` (`expm1`); `q ≤ m` so that `𝒟_{q,m} ≠ ∅`; any real `z` (paper: `z_i > 0`).
* A lift-cost: `ℝ^T` as any real inner product space, the head span `S` with orthogonal projection `Π`
  (`x_K ↔ Πx`, `x_⊥ = x − Πx`, `tail`); the head marginal `π_K = (Π × Π)#π`; finite second moments of both
  marginals (the Setting's `P_T ∈ 𝒫₂(ℝ^T)`; for `μ_T` implicit, the coherent references being bounded); entropic
  plans as `withDensity` of the Gibbs densities (`gibbs`) on `P ⊗ μ` (the projected plan lifted to `ℝ^T`).
* A sample-rate: the frozen hypotheses of `OTFD/WaveL3.sieve_strong_limit_uncond` (A's forward-map hypotheses), `K_n →
  ∞`, coordinates `X_{n,i}` of law `P` (independence not needed), `ass:app-grid-stability` with `W₂` Tau Ceti's
  `wassersteinEDist 2` between the grid law and `μ_{K_n}`, the root mean squared errors `rmsE` (frozen) in `[0, ∞]`,
  `limsup` in `[0, ∞]`.
* TM: `ℝ^d = Euc d`; `H^σ` norms on the Fourier side with Mathlib's unitary `L²` Fourier transform (weight
  `(1 + ‖ξ‖²)^σ`; the paper's normalisation constants are absorbed in `A_k`, `L`), `sobNorm` in `[0, ∞]`;
  `‖p − q‖_{H^t} < ∞` explicit (else `toReal` would be a junk `0`); `X` measurable of finite volume (paper: bounded),
  `p = q` off `X`; `TV` the locked-import `tvDist`; `MMD_k(P, Q)` any `m ≥ 0` with `‖p − q‖_{H^{−s}} ≤ A_k m`.

Critic notes:
* All 25 claims are proved in `Wave24f/Route{Small,Lift,Rate,Hadamard,Reduction,Copbary,RefPot,Equiv,NPN,Jacobi,
  Interp,Marked}.lean`. Routes reuse the certified `OTFD/Wave16b.rate_decomp`, `OTFD/WaveL3.sieve_strong_limit_uncond`,
  Wave 24b `smax_mono_sharp`, NNFibers `sum_finpartition_eq`, `sum_PSall_card`, `embFixEquiv`, and Tau Ceti's
  one-dimensional barycenter and quantile coupling theory (`sum_mul_wassersteinEDist_sq_quantileBarycenter_le`,
  `wassersteinEDist_rpow_eq_lintegral_rpow_enorm_quantile_sub`, `cdf_quantile_ae`, `quantile_cdf_ae`,
  `cdf_map_eq_volume_restrict`) and `exists_isOptimalCoupling`.
* Manuscript error (confirmed by the critic, 2026-10-16): SB `lem:equiv` is stated in `ℝ^d` (`Ω = C([0,1]; ℝ^d)`,
  `μ, ν ∈ 𝒫₂(ℝ^d)`), but `eq:calib` (`:421`) prints `=\Ccal_\eps(\mu,\nu)+\eps\,\Ent(\mu)+\tfrac\eps2\log(2\pi\eps)`,
  and the proof (`:2668`, `:2673`) takes "`p_\eps` the `N(0,\eps)` density" and prints
  `\KL(\pi\Vert R_{01})=-\Ent(\pi)+\Ent(\mu)+\tfrac12\log(2\pi\eps)+\frac{1}{2\eps}\int|x-y|^2\,d\pi`. The heat
  kernel of `√ε B` on `ℝ^d` is `p_ε(z) = (2πε)^{−d/2} e^{−|z|²/(2ε)}`, so `−log p_ε(z) = (d/2) log(2πε) + |z|²/(2ε)`;
  fix: `\tfrac{\eps d}2\log(2\pi\eps)` in `eq:calib`, `\tfrac d2\log(2\pi\eps)` in the proof, "`N(0,\eps I_d)`
  density" (`equiv_static`; correct as printed only for `d = 1`). Low severity: the constant depends on neither `π`
  nor `ν`, so every use of `lem:equiv` (minimising over couplings or targets) is unaffected; `:488` already uses
  the correct `(2πε t(1 − t))^{−d/2}`.
* Observations: (1) `thm:copbary` (i) and the optimality in (ii) hold without the absolute-continuity hypothesis on
  `ν` (the proof here goes through the product lower bound `W₂² ≥ Σ_i W₂²(marginals)` and the one-dimensional
  quantile barycenter, with no Agueh–Carlier or Brenier); a.c. matters only for uniqueness. (2) `lem:reduction`
  (iii)'s identity `π(·|y) = ν_{βy/ε}` holds for every `y ∈ H`. (3) C (c) needs no Rademacher theorem: every
  `r ∈ S` (not just a.e.) has a common contact point, so the two Brenier potentials have a common subgradient
  everywhere on `S`, and a telescoping argument on segments replaces the a.e. gradient. (4) `cor:app-sample-rate`
  needs only identically distributed curves. (5) `lem:marked-block-transform`'s exact identity holds for every real
  `z`. (6) `prop:chartsafe` needs `Λ ≥ 0` and holds for any family of normed tangent spaces.
* Trivial or near-trivial claims: `lift_cost_identity` (Pythagoras), `chartsafe_tube`, `chartsafe_embed` (triangle
  inequality), `polish_flat` (Mathlib `Lp` instances plus the segment), `lift_cost_entropic` (exponent algebra).
  Critic verdict: kept — none restates a definition, a hypothesis or a frozen claim (no overlap in
  `certify/targets.toml`); each is the paper's own printed sentence (`lem:lift-cost`'s first display,
  `prop:chartsafe`'s two clauses, `lem:polish` for `M = ℝ^q`), at level L0–L1 as ranked in the QUEUE.

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

noncomputable section
open MeasureTheory Set Filter Topology Finset
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave24f

open StatFormal.OTFD.WaveL1 (Euc LipNull IsCMMapAE)
open StatFormal.OTFD.Wave8b (embed)
open StatFormal.OTFD.Wave1 (truncK)
open StatFormal.OTFD.WaveL3 (Mom1)
open StatFormal.OTFD.Wave16b (rmsE)

/-! ### A `lem:lift-cost`: head and tail of an orthogonal splitting -/

section Lift

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The tail `x_⊥ = x − Π x` of `x` for the head span `S`. -/
def tail (S : Submodule ℝ E) [S.HasOrthogonalProjection] (x : E) : E := x - S.starProjection x

/-- The Gibbs density `exp((f(x) + g(u) − c(x, u))/ε)`, in `[0, ∞)`. -/
def gibbs {X U : Type*} (ε : ℝ) (f : X → ℝ) (g : U → ℝ) (c : X → U → ℝ) (p : X × U) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp ((f p.1 + g p.2 - c p.1 p.2) / ε))

end Lift

/-! ### T `prop:hadamard-distortion`: the hyperboloid model of curvature `−k²` -/

section Hyp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Minkowski form on `ℝ × E`: `B(x, y) = −x₀ y₀ + ⟨x₁, y₁⟩`. -/
def minkB (x y : ℝ × E) : ℝ := -(x.1 * y.1) + ⟪x.2, y.2⟫

/-- `x` lies on the hyperboloid `H_k = {B(x, x) = −1/k², x₀ > 0}`, the hyperbolic space of curvature `−k²`. -/
def OnHyp (k : ℝ) (x : ℝ × E) : Prop := minkB x x = -1 / k ^ 2 ∧ 0 < x.1

/-- The norm `|v| = √B(v, v)` of a tangent vector (`B` is positive definite on `T_pH_k = p^⊥`). -/
def tanNorm (v : ℝ × E) : ℝ := √(minkB v v)

/-- `Exp_p v = cosh(k|v|) p + (sinh(k|v|)/(k|v|)) v` (at `v = 0` the second coefficient is `0` and `Exp_p 0 = p`). -/
def hypExp (k : ℝ) (p v : ℝ × E) : ℝ × E :=
  Real.cosh (k * tanNorm v) • p + (Real.sinh (k * tanNorm v) / (k * tanNorm v)) • v

/-- The geodesic distance of `H_k`: `d(x, y) = arcosh(−k² B(x, y))/k`. -/
def hypDist (k : ℝ) (x y : ℝ × E) : ℝ := Real.arcosh (-(k ^ 2) * minkB x y) / k

end Hyp

/-- The optimal transport cost `OT_c(P, P') = inf_π ∫ c dπ` over couplings `π` of `P` and `P'`, in `[0, ∞]`. -/
def otCost {X : Type*} [MeasurableSpace X] (c : X → X → ℝ≥0∞) (P P' : Measure X) : ℝ≥0∞ :=
  ⨅ (π : Measure (X × X)) (_ : π.map Prod.fst = P ∧ π.map Prod.snd = P'), ∫⁻ z, c z.1 z.2 ∂π

/-! ### G `lem:reduction`: Gibbs conditionals and exponential tilts -/

section Reduction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]

/-- The cost `c_β(v, z) = ½‖βv − z‖²`. -/
def cBeta (β : ℝ) (v z : H) : ℝ := ‖β • v - z‖ ^ 2 / 2

/-- The normaliser `Z(z) = ∫ e^{(f(v) − c_β(v, z))/ε} μ(dv)`, in `[0, ∞]`. -/
def gibbsZ (μ : Measure H) (f : H → ℝ) (β ε : ℝ) (z : H) : ℝ≥0∞ :=
  ∫⁻ v, ENNReal.ofReal (Real.exp ((f v - cBeta β v z) / ε)) ∂μ

/-- The conditional reference law `π(dv | z) = e^{(f(v) − c_β(v, z))/ε} μ(dv) / Z(z)`. -/
def condLaw (μ : Measure H) (f : H → ℝ) (β ε : ℝ) (z : H) : Measure H :=
  (gibbsZ μ f β ε z)⁻¹ • μ.withDensity fun v => ENNReal.ofReal (Real.exp ((f v - cBeta β v z) / ε))

/-- The exponential tilt `ν_θ(dv) = e^{⟨v, θ⟩} ν(dv) / ∫ e^{⟨u, θ⟩} ν(du)`. -/
def tiltLaw (ν : Measure H) (θ : H) : Measure H :=
  (∫⁻ u, ENNReal.ofReal (Real.exp ⟪u, θ⟫) ∂ν)⁻¹ • ν.withDensity fun v => ENNReal.ofReal (Real.exp ⟪v, θ⟫)

/-- The finite reference `μ_r = Σ_j b_j δ_{V_j}`. -/
def atomLaw {r : ℕ} (b : Fin r → ℝ) (V : Fin r → H) : Measure H :=
  ∑ j, ENNReal.ofReal (b j) • Measure.dirac (V j)

end Reduction

/-! ### SB `thm:copbary`: laws with a common copula -/

section Copula

/-- `C` is a copula on `[0, 1]^d`: a probability law on `ℝ^d` with uniform marginals on `(0, 1)`. -/
def IsCopula {d : ℕ} (C : Measure (Fin d → ℝ)) : Prop :=
  IsProbabilityMeasure C ∧ ∀ i, C.map (fun u => u i) = volume.restrict (Ioo (0 : ℝ) 1)

/-- The law of `(Q_1(U_1), …, Q_d(U_d))` for `U ∼ C`, on `ℝ^d` (`EuclideanSpace`); with `Q_i = F_i^{-1}` the
quantile functions of continuous marginals `F_i`, this is the law with copula `C` and marginals `F_i` (Sklar). -/
def copLaw {d : ℕ} (C : Measure (Fin d → ℝ)) (Q : Fin d → ℝ → ℝ) : Measure (Euc d) :=
  C.map fun u => WithLp.toLp 2 (fun i => Q i (u i))

/-- `G_i^{-1} = Σ_s p_s F_{s,i}^{-1}`. -/
def baryQ {S d : ℕ} (p : Fin S → ℝ≥0) (m : Fin S → Fin d → Measure ℝ) (i : Fin d) (u : ℝ) : ℝ :=
  ∑ s, (p s : ℝ) * (m s i).quantile u

/-- The coordinatewise quantile map `T_s(x) = (G_i^{-1}(F_{s,i}(x_i)))_{i ≤ d}`. -/
def copMap {S d : ℕ} (p : Fin S → ℝ≥0) (m : Fin S → Fin d → Measure ℝ) (s : Fin S) (x : Euc d) : Euc d :=
  WithLp.toLp 2 (fun i => baryQ p m i (ProbabilityTheory.cdf (m s i) (x i)))

end Copula

/-! ### SB `lem:equiv`: the static identity behind `eq:calib` -/

/-- The `N(0, εI_d)` density on `ℝ^d`: `(2πε)^{−d/2} e^{−‖z‖²/(2ε)}`. -/
def gaussDens (d : ℕ) (ε : ℝ) (z : Euc d) : ℝ :=
  (2 * Real.pi * ε) ^ (-(d : ℝ) / 2) * Real.exp (-‖z‖ ^ 2 / (2 * ε))

/-- The endpoint law `R₀₁(dx, dy) = μ(dx) p_ε(y − x) dy` of `𝕎^ε_μ`, for `μ` with Lebesgue density `m`. -/
def refEndpoint (d : ℕ) (ε : ℝ) (m : Euc d → ℝ) : Measure (Euc d × Euc d) :=
  volume.withDensity fun z => ENNReal.ofReal (m z.1 * gaussDens d ε (z.2 - z.1))

/-! ### SB `cor:field-npn`: the nonparanormal class -/

section NPN

open scoped MatrixOrder Matrix.Norms.L2Operator

/-- The `i`-th marginal law `μ ∘ x_i⁻¹` of a law on `ℝ^d`. -/
def marg {d : ℕ} (μ : Measure (Euc d)) (i : Fin d) : Measure ℝ := μ.map fun x : Euc d => x i

/-- `Φ = cdf N(0, 1)`. -/
def stdPhi (u : ℝ) : ℝ := ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) u

/-- `Φ^{-1}`, the quantile function of `N(0, 1)`. -/
def stdPhiInv (u : ℝ) : ℝ := (ProbabilityTheory.gaussianReal 0 1).quantile u

/-- The Gaussian scores `Z_μ(x) = (Φ^{-1}(F_{μ,i}(x_i)))_i`. -/
def zScore {d : ℕ} (μ : Measure (Euc d)) (x : Euc d) : Euc d :=
  WithLp.toLp 2 fun i => stdPhiInv (ProbabilityTheory.cdf (marg μ i) (x i))

/-- `μ` is in the nonparanormal (Gaussian-copula) class with correlation matrix `R`: `Z_μ # μ = N(0, R)`. -/
def InNPN {d : ℕ} (μ : Measure (Euc d)) (R : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  μ.map (zScore μ) = ProbabilityTheory.multivariateGaussian 0 R

/-- `R^{-1/2} = (R^{1/2})⁻¹` (positive square root, then matrix inverse). -/
def invSqrt {d : ℕ} (R : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ := (CFC.sqrt R)⁻¹

/-- The standardisation `𝕊_μ(x) = R_μ^{-1/2} Z_μ(x)`. -/
def npnStd {d : ℕ} (μ : Measure (Euc d)) (R : Matrix (Fin d) (Fin d) ℝ) (x : Euc d) : Euc d :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (invSqrt R) (zScore μ x)

/-- The nonparanormal repair `T_s(x) = (G_i^{-1}(Φ([R_ν^{1/2} R_s^{-1/2} Z_s(x)]_i)))_i`. -/
def npnMap {d : ℕ} (μs ν : Measure (Euc d)) (Rs Rν : Matrix (Fin d) (Fin d) ℝ) (x : Euc d) : Euc d :=
  WithLp.toLp 2 fun i => (marg ν i).quantile
    (stdPhi (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt Rν * invSqrt Rs) (zScore μs x) i))

end NPN

/-! ### TM `thm:interp`: Sobolev norms on the Fourier side -/

/-- `‖f‖_{H^σ} = (∫ (1 + ‖ξ‖²)^σ |𝓕f(ξ)|² dξ)^{1/2}` in `[0, ∞]`, with `𝓕` Mathlib's unitary (Plancherel) Fourier
transform on `L²(ℝ^d)`. -/
def sobNorm {d : ℕ} (σ : ℝ) (f : Lp ℂ 2 (volume : Measure (Euc d))) : ℝ≥0∞ :=
  (∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ σ) *
    ‖(FourierTransform.fourier f : Lp ℂ 2 (volume : Measure (Euc d))) ξ‖ₑ ^ 2) ^ (1 / 2 : ℝ)

/-! ### NN `lem:marked-block-transform`: labelled partitions -/

section Marked

/-- The labelled partitions `𝒟_{q,m}` (`eq:data`, in bijection with the canonical pieces `𝒞_{q,m}` by
`prop:disjoint`): a set partition `π` of `[m]` with an injective labelling `ι : [q] ↪ blocks(π)`. -/
abbrev LabPart (q m : ℕ) : Type := Σ P : Finpartition (univ : Finset (Fin m)), (Fin q ↪ P.parts)

/-- `∏_i z_i^{N_i}`, `N_i = |ι(i)|` the copy number of the `i`-th distinguished unit. -/
def markedWeight {q m : ℕ} (z : Fin q → ℝ) (x : LabPart q m) : ℝ :=
  ∏ i, z i ^ ((x.2 i : Finset (Fin m))).card

/-- `E_{U_{q,m}}[∏_i z_i^{N_i}]` under the uniform law `U_{q,m}` on `𝒟_{q,m}`. -/
def markedPGF (q m : ℕ) (z : Fin q → ℝ) : ℝ :=
  (∑ x : LabPart q m, markedWeight z x) / Fintype.card (LabPart q m)

/-- `exp(e^x − 1) = Σ_n B_n xⁿ/n!` (Bell numbers `B_n` = numbers of set partitions, frozen `NNFibers.bell`). -/
def bellEGF : PowerSeries ℝ := PowerSeries.mk fun n => (StatFormal.NNFibers.bell n : ℝ) / n.factorial

/-- `e^{zx} − 1`. -/
def expm1 (z : ℝ) : PowerSeries ℝ := PowerSeries.rescale z (PowerSeries.exp ℝ) - 1

end Marked

namespace Claims

/-! ### T `prop:chartsafe` -/

/-- T `prop:chartsafe` (tube clause): if every field satisfies `sup_t ‖v_j(t)‖ ≤ r₀`, then every convex combination
`v̂_u = Σ_j q_j(u) v_j` with one weight vector per curve satisfies `‖v̂_u(t)‖ ≤ r₀` for every `t` and `u`. -/
def chartsafe_tube : Prop :=
  ∀ (T ι U : Type) [Fintype ι] (Etan : T → Type) [∀ t, NormedAddCommGroup (Etan t)] [∀ t, NormedSpace ℝ (Etan t)]
    (v : ι → (t : T) → Etan t) (q : U → ι → ℝ) (r₀ : ℝ),
    (∀ u j, 0 ≤ q u j) → (∀ u, ∑ j, q u j = 1) → (∀ j t, ‖v j t‖ ≤ r₀) →
      ∀ u t, ‖∑ j, q u j • v j t‖ ≤ r₀

/-- T `prop:chartsafe` (sufficient condition under `eq:Hembed`): fields `v_j = ev(h_j)` of a normed space `H` with
`sup_t ‖ev_t h‖ ≤ Λ ‖h‖_H`; if `max_j ‖h_j‖_H ≤ B₀` and `Λ B₀ ≤ r₀`, the fields and every convex combination lie in
the closed tube of radius `r₀`. -/
def chartsafe_embed : Prop :=
  ∀ (T ι U H : Type) [Fintype ι] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (Etan : T → Type) [∀ t, NormedAddCommGroup (Etan t)] [∀ t, NormedSpace ℝ (Etan t)]
    (ev : (t : T) → H →L[ℝ] Etan t) (Λ B₀ r₀ : ℝ) (h : ι → H) (q : U → ι → ℝ),
    (∀ t x, ‖ev t x‖ ≤ Λ * ‖x‖) → (∀ j, ‖h j‖ ≤ B₀) → Λ * B₀ ≤ r₀ → 0 ≤ Λ →
    (∀ u j, 0 ≤ q u j) → (∀ u, ∑ j, q u j = 1) →
      (∀ j t, ‖ev t (h j)‖ ≤ r₀) ∧ ∀ u t, ‖∑ j, q u j • ev t (h j)‖ ≤ r₀

/-! ### A `lem:lift-cost` -/

/-- A `lem:lift-cost`, pointwise identity:
`‖x − u‖² = ‖x_K − u_K‖² + ‖x_⊥‖² + ‖u_⊥‖² − 2⟨x_⊥, u_⊥⟩`. -/
def lift_cost_identity : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (S : Submodule ℝ E) [S.HasOrthogonalProjection]
    (x u : E),
    ‖x - u‖ ^ 2 = ‖S.starProjection x - S.starProjection u‖ ^ 2 + ‖tail S x‖ ^ 2 + ‖tail S u‖ ^ 2
      - 2 * ⟪tail S x, tail S u⟫

/-- A `lem:lift-cost`, integrated form, for every coupling `π` of two laws with finite second moments (the paper's
`P_T, μ_T ∈ 𝒫₂`): all four integrands are `π`-integrable and
`∫‖x − u‖² dπ = ∫‖a − b‖² dπ_K + E‖X_⊥‖² + E‖U_⊥‖² − 2∫⟨x_⊥, u_⊥⟩ dπ`, `π_K = (Π × Π)#π` the head marginal. -/
def lift_cost_integral : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (S : Submodule ℝ E) [S.HasOrthogonalProjection]
    (P μ : Measure E) (π : Measure (E × E)),
    IsProbabilityMeasure π → π.map Prod.fst = P → π.map Prod.snd = μ →
    Integrable (fun x => ‖x‖ ^ 2) P → Integrable (fun x => ‖x‖ ^ 2) μ →
      Integrable (fun p : E × E => ‖p.1 - p.2‖ ^ 2) π ∧
      Integrable (fun p : E × E => ⟪tail S p.1, tail S p.2⟫) π ∧
      Integrable (fun p : E × E => ‖p.1 - p.2‖ ^ 2)
        (π.map fun p => (S.starProjection p.1, S.starProjection p.2)) ∧
      ∫ p, ‖p.1 - p.2‖ ^ 2 ∂π =
        ∫ p, ‖p.1 - p.2‖ ^ 2 ∂(π.map fun p => (S.starProjection p.1, S.starProjection p.2))
          + ∫ x, ‖tail S x‖ ^ 2 ∂P + ∫ u, ‖tail S u‖ ^ 2 ∂μ - 2 * ∫ p, ⟪tail S p.1, tail S p.2⟫ ∂π

/-- A `lem:lift-cost`, entropic clause (cost `‖x − u‖²`, temperature `ε > 0`): the plan on `P ⊗ μ` with the lifted
potentials `(f_K(x_K) + ‖x_⊥‖², g_K(u_K) + ‖u_⊥‖²)` equals the projected plan (density
`e^{(f_K(x_K) + g_K(u_K) − ‖x_K − u_K‖²)/ε}`) reweighted by `exp(2⟨x_⊥, u_⊥⟩/ε)`. -/
def lift_cost_entropic : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (S : Submodule ℝ E) [S.HasOrthogonalProjection]
    (P μ : Measure E) [SFinite μ] (ε : ℝ) (fK gK : E → ℝ),
    0 < ε → Measurable fK → Measurable gK →
      (P.prod μ).withDensity
          (gibbs ε (fun x => fK (S.starProjection x) + ‖tail S x‖ ^ 2)
            (fun u => gK (S.starProjection u) + ‖tail S u‖ ^ 2) (fun x u => ‖x - u‖ ^ 2)) =
        ((P.prod μ).withDensity
            (gibbs ε (fun x => fK (S.starProjection x)) (fun u => gK (S.starProjection u))
              (fun x u => ‖S.starProjection x - S.starProjection u‖ ^ 2))).withDensity
          (fun p => ENNReal.ofReal (Real.exp (2 * ⟪tail S p.1, tail S p.2⟫ / ε)))

/-! ### A `cor:app-sample-rate` -/

/-- A `cor:app-sample-rate`, from the certified `prop:rate-decomp` and `prop:integrated-sieve-strong`: under the
forward-map hypotheses of `prop:integrated-sieve-strong` (as frozen in `OTFD/WaveL3`, `sieve_strong_limit_uncond`), with
`K_n → ∞`, curves `X_1, …, X_n` of law `P`, and `ass:app-grid-stability` (`Δ^grid_n ≤ L_n W₂(μ_{K_n,m_n}, μ_{K_n})^α`
with `L_n W₂(…)^α → 0`), the root mean squared error of the embedded computed ranks satisfies
`limsup LHS ≤ limsup Δ^{emp,(m)}_n`, and `LHS → 0` whenever `Δ^{emp,(m)}_n → 0`. -/
def app_sample_rate : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (P μ : ProbabilityMeasure H) (F : H → H) (M : ℝ) (FK : (K : ℕ) → Euc K → Euc K)
    (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (Kn : ℕ → ℕ) (X : (n : ℕ) → Ω → Fin n → H) (Fhat Fm : (n : ℕ) → Ω → Fin n → Euc (Kn n))
    (μgrid : (n : ℕ) → Measure (Euc (Kn n))) (L : ℕ → ℝ≥0∞) (α : ℝ),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    LipNull (P : Measure H) → Mom1 (P : Measure H) ≠ ∞ → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
    Measurable F → (P : Measure H).map F = μ → IsCMMapAE (P : Measure H) F →
    (∀ K, Measurable (FK K)) →
    (∀ K, ((P : Measure H).map (truncK e K)).map (FK K) = (μ : Measure H).map (truncK e K)) →
    (∀ K, IsCMMapAE ((P : Measure H).map (truncK e K)) (FK K)) →
    Tendsto Kn atTop atTop →
    (∀ n i, Measurable fun ω => X n ω i) → (∀ n i, Pr.map (fun ω => X n ω i) = (P : Measure H)) →
    (∀ n i, Measurable fun ω => ‖Fhat n ω i - Fm n ω i‖) →
    (∀ n i, Measurable fun ω => ‖Fm n ω i - FK (Kn n) (truncK e (Kn n) (X n ω i))‖) →
    0 < α → α ≤ 1 →
    (∀ n, rmsE Pr (fun ω i => ‖Fm n ω i - FK (Kn n) (truncK e (Kn n) (X n ω i))‖) ≤
      L n * TauCeti.wassersteinEDist 2 (μgrid n) ((μ : Measure H).map (truncK e (Kn n))) ^ α) →
    Tendsto (fun n => L n * TauCeti.wassersteinEDist 2 (μgrid n) ((μ : Measure H).map (truncK e (Kn n))) ^ α)
      atTop (𝓝 0) →
      limsup (fun n => rmsE Pr (fun ω i => ‖embed e (Kn n) (Fhat n ω i) - F (X n ω i)‖)) atTop ≤
          limsup (fun n => rmsE Pr (fun ω i => ‖Fhat n ω i - Fm n ω i‖)) atTop ∧
        (Tendsto (fun n => rmsE Pr (fun ω i => ‖Fhat n ω i - Fm n ω i‖)) atTop (𝓝 0) →
          Tendsto (fun n => rmsE Pr (fun ω i => ‖embed e (Kn n) (Fhat n ω i) - F (X n ω i)‖)) atTop (𝓝 0))

/-! ### G `lem:polish`, flat target -/

/-- G `lem:polish` for `M = ℝ^q` (flat; an orthonormal frame identifies the fields with `ℝ^q`-valued maps): the curve
space `𝒳 = L²_λ([0,1]; ℝ^q)`, `λ` any probability measure on `T = [0,1]`, is a complete separable metric space, and
every two curves are joined by `θ ↦ x_θ` with `x_0 = x`, `x_1 = x'` and `D(x_θ, x_θ') = |θ − θ'| D(x, x')`. -/
def polish_flat : Prop :=
  ∀ (q : ℕ) (lam : Measure (Icc (0 : ℝ) 1)), IsProbabilityMeasure lam →
    CompleteSpace (Lp (Euc q) 2 lam) ∧ TopologicalSpace.SeparableSpace (Lp (Euc q) 2 lam) ∧
      ∀ x x' : Lp (Euc q) 2 lam, ∃ γ : ℝ → Lp (Euc q) 2 lam, γ 0 = x ∧ γ 1 = x' ∧
        ∀ θ θ', θ ∈ Icc (0 : ℝ) 1 → θ' ∈ Icc (0 : ℝ) 1 → dist (γ θ) (γ θ') = |θ - θ'| * dist x x'

/-! ### T `prop:hadamard-distortion` (`eq:hadamard-lower`, `eq:hadamard-two-sided`), constant curvature `−k²` -/

/-- T `eq:hadamard-lower` on the hyperbolic space `H_k` of curvature `−k²` (`k > 0`): for every base point `p` and
tangent vectors `v, w ∈ T_pH_k`, `d(Exp_p v, Exp_p w) ≥ |v − w|`, with no restriction on the radius. -/
def hadamard_lower : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (k : ℝ) (p v w : ℝ × E),
    0 < k → OnHyp k p → minkB p v = 0 → minkB p w = 0 →
      tanNorm (v - w) ≤ hypDist k (hypExp k p v) (hypExp k p w)

/-- T `eq:hadamard-two-sided` on `H_k` (sectional curvature `−k²`, so bounded below by `−k²`): if `|v|, |w| ≤ r`,
`r > 0`, then `|v − w| ≤ d(Exp_p v, Exp_p w) ≤ (sinh(kr)/(kr)) |v − w|`. -/
def hadamard_two_sided : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (k r : ℝ) (p v w : ℝ × E),
    0 < k → 0 < r → OnHyp k p → minkB p v = 0 → minkB p w = 0 → tanNorm v ≤ r → tanNorm w ≤ r →
      tanNorm (v - w) ≤ hypDist k (hypExp k p v) (hypExp k p w) ∧
        hypDist k (hypExp k p v) (hypExp k p w) ≤ Real.sinh (k * r) / (k * r) * tanNorm (v - w)

/-- T `prop:hadamard-distortion`, cost and transport form on `M = H_k`: curves `x ∈ X` given by their logarithmic
fields `ℓ_x(t) ∈ T_{m(t)}H_k` along a base curve `m` (`x(t) = Exp_{m(t)} ℓ_x(t)`), `c_geo(x, y) = ∫ d(x(t), y(t))² dλ`,
`c_m^{H₀}(x, y) = ∫ |ℓ_x(t) − ℓ_y(t)|² dλ` (in `[0, ∞]`). Then `c_geo ≥ c_m^{H₀}` and `OT_{c_geo}(P, P') ≥
OT_{c_m^{H₀}}(P, P')` for all laws `P, P'` of curves; if the fields are bounded by `r > 0`, then
`c_geo ≤ (sinh(kr)/(kr))² c_m^{H₀}`. -/
def hadamard_cost : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (T X : Type) [MeasurableSpace T]
    [MeasurableSpace X] (lam : Measure T) (k : ℝ) (m : T → ℝ × E) (ℓ : X → T → ℝ × E),
    0 < k → (∀ t, OnHyp k (m t)) → (∀ x t, minkB (m t) (ℓ x t) = 0) →
      let cgeo : X → X → ℝ≥0∞ := fun x y =>
        ∫⁻ t, ENNReal.ofReal (hypDist k (hypExp k (m t) (ℓ x t)) (hypExp k (m t) (ℓ y t)) ^ 2) ∂lam
      let cm : X → X → ℝ≥0∞ := fun x y => ∫⁻ t, ENNReal.ofReal (tanNorm (ℓ x t - ℓ y t) ^ 2) ∂lam
      (∀ x y, cm x y ≤ cgeo x y) ∧ (∀ P P' : Measure X, otCost cm P P' ≤ otCost cgeo P P') ∧
        ∀ r : ℝ, 0 < r → (∀ x t, tanNorm (ℓ x t) ≤ r) →
          ∀ x y, cgeo x y ≤ ENNReal.ofReal ((Real.sinh (k * r) / (k * r)) ^ 2) * cm x y

/-! ### G `lem:reduction` (ii), (iii) -/

/-- Standing hypotheses of G `lem:reduction` for a reference potential `f`: `β, ε > 0`, `μ` a probability measure
with `μ(S ∩ {‖v‖ ≤ 1}) = 1`, `f` measurable and satisfying the Schrödinger equation
`∫ e^{(f(v) + g(y₀) − c_β(v, y₀))/ε} μ(dv) = 1` at one point `y₀` with `g(y₀)` finite (the paper's input from
`g_S ∈ L¹(Q_S)`). -/
def ReductionHyp {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
    (S : Submodule ℝ H) (μ : Measure H) (f : H → ℝ) (β ε : ℝ) : Prop :=
  0 < β ∧ 0 < ε ∧ IsProbabilityMeasure μ ∧ μ ((S : Set H) ∩ Metric.closedBall 0 1)ᶜ = 0 ∧ Measurable f ∧
    ∃ (y₀ : H) (g₀ : ℝ), ∫⁻ v, ENNReal.ofReal (Real.exp ((f v + g₀ - cBeta β v y₀) / ε)) ∂μ = 1

/-- G `lem:reduction` (ii): for every `z ∈ H`, `Z(z) ∈ (0, ∞)`, `π(· | z)` is a probability measure,
`π(· | z) = π(· | Πz)`, and `π(· | z)` does not change if `f` is replaced by any measurable `f'` with `f' = f + a`
`μ`-a.e. -/
def reduction_cond : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (S : Submodule ℝ H) [S.HasOrthogonalProjection] (μ : Measure H) (f : H → ℝ) (β ε : ℝ),
    ReductionHyp S μ f β ε → ∀ z : H,
      (0 < gibbsZ μ f β ε z ∧ gibbsZ μ f β ε z < ∞) ∧ IsProbabilityMeasure (condLaw μ f β ε z) ∧
        condLaw μ f β ε z = condLaw μ f β ε (S.starProjection z) ∧
        ∀ (f' : H → ℝ) (a : ℝ), Measurable f' → (∀ᵐ v ∂μ, f' v = f v + a) →
          condLaw μ f' β ε z = condLaw μ f β ε z

/-- G `lem:reduction` (iii), first part: `ν(dv) = e^{(f(v) − β²‖v‖²/2)/ε} μ(dv)` is a finite measure equivalent to
`μ`, and `π(dv | y) = ν_{βy/ε}(dv)` (for every `y ∈ H`; the paper states it for `y ∈ S`). -/
def reduction_tilt : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (S : Submodule ℝ H) [S.HasOrthogonalProjection] (μ : Measure H) (f : H → ℝ) (β ε : ℝ),
    ReductionHyp S μ f β ε →
      let ν := μ.withDensity fun v => ENNReal.ofReal (Real.exp ((f v - β ^ 2 * ‖v‖ ^ 2 / 2) / ε))
      ν Set.univ < ∞ ∧ ν ≪ μ ∧ μ ≪ ν ∧ ∀ y : H, condLaw μ f β ε y = tiltLaw ν ((β / ε) • y)

/-- G `lem:reduction` (iii), injectivity, for a finite reference `μ_r = Σ_j b_j δ_{V_j}` (`b_j > 0`, `Σ b_j = 1`,
`V_j ∈ S`, `‖V_j‖ ≤ 1`) and any potential `f`: if `⟨v, h⟩` is not `μ_r`-a.s. constant for any `h ∈ S \ {0}`, then
`Φ_S(y) = ∫ v π(dv | y)` is continuous and injective on `S`. -/
def reduction_inject : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    [BorelSpace H] (S : Submodule ℝ H) (r : ℕ) (b : Fin r → ℝ) (V : Fin r → H) (f : H → ℝ) (β ε : ℝ),
    0 < β → 0 < ε → (∀ j, 0 < b j) → ∑ j, b j = 1 → (∀ j, V j ∈ S) → (∀ j, ‖V j‖ ≤ 1) →
    (∀ h ∈ S, h ≠ 0 → ∃ j l, ⟪V j, h⟫ ≠ ⟪V l, h⟫) →
      ContinuousOn (fun y => ∫ v, v ∂(condLaw (atomLaw b V) f β ε y)) S ∧
        Set.InjOn (fun y => ∫ v, v ∂(condLaw (atomLaw b V) f β ε y)) S

/-! ### SB `thm:copbary` -/

/-- Standing hypotheses of SB `thm:copbary`: weights `p_s` summing to one, probability marginals `F_{s,i}` without
atoms (continuous distribution functions), a copula `C`, and `R_s = copLaw C (F_{s,·}^{-1}) ∈ 𝒫₂(ℝ^d)`. -/
def CopHyp {S d : ℕ} (p : Fin S → ℝ≥0) (m : Fin S → Fin d → Measure ℝ) (C : Measure (Fin d → ℝ)) : Prop :=
  ∑ s, p s = 1 ∧ (∀ s i, IsProbabilityMeasure (m s i)) ∧ (∀ s i, NullSingletonClass (m s i)) ∧ IsCopula C ∧
    ∀ s, TauCeti.HasFiniteMoment 2 (copLaw C fun i => (m s i).quantile)

/-- SB `thm:copbary` (i): the law `ν` with copula `C` and marginals `G_i`, `G_i^{-1} = Σ_s p_s F_{s,i}^{-1}`, is a
Wasserstein barycenter of `(R_s, p_s)` (frozen `Wave23a.IsBarycenter`); it minimises `F(ω) = Σ_s p_s W₂²(R_s, ω)` even
over all probability laws `ω` on `ℝ^d`. -/
def copbary_bary : Prop :=
  ∀ (S d : ℕ) (p : Fin S → ℝ≥0) (m : Fin S → Fin d → Measure ℝ) (C : Measure (Fin d → ℝ)),
    CopHyp p m C →
      StatFormal.Wave23a.IsBarycenter p (fun s => copLaw C fun i => (m s i).quantile) (copLaw C (baryQ p m)) ∧
        ∀ ω : Measure (Euc d), IsProbabilityMeasure ω →
          StatFormal.Wave23a.barF p (fun s => copLaw C fun i => (m s i).quantile) (copLaw C (baryQ p m)) ≤
            StatFormal.Wave23a.barF p (fun s => copLaw C fun i => (m s i).quantile) ω

/-- SB `thm:copbary` (ii): the coordinatewise quantile map `T_s` pushes `R_s` to `ν` and is an optimal transport map:
`‖T_s − Id‖²_{L²(R_s)} = W₂²(R_s, ν)`. -/
def copbary_map : Prop :=
  ∀ (S d : ℕ) (p : Fin S → ℝ≥0) (m : Fin S → Fin d → Measure ℝ) (C : Measure (Fin d → ℝ)),
    CopHyp p m C → ∀ s : Fin S,
      (copLaw C fun i => (m s i).quantile).map (copMap p m s) = copLaw C (baryQ p m) ∧
        ∫⁻ x, ‖x - copMap p m s x‖ₑ ^ 2 ∂(copLaw C fun i => (m s i).quantile) =
          TauCeti.wassersteinEDist 2 (copLaw C fun i => (m s i).quantile) (copLaw C (baryQ p m)) ^ 2

/-- SB `thm:copbary` (iii): the repair `(T_s)_s` is parity-exact (`(T_s)#R_s = ν` for every `s`) and
intervention-optimal: `𝒥(T) = Σ_s p_s ‖T_s − Id‖²_{L²(R_s)} = 𝒥⋆ = min_ω F(ω)` (minimum over probability laws). -/
def copbary_cost : Prop :=
  ∀ (S d : ℕ) (p : Fin S → ℝ≥0) (m : Fin S → Fin d → Measure ℝ) (C : Measure (Fin d → ℝ)),
    CopHyp p m C →
      (∀ s t : Fin S, (copLaw C fun i => (m s i).quantile).map (copMap p m s) =
        (copLaw C fun i => (m t i).quantile).map (copMap p m t)) ∧
      ∑ s, (p s : ℝ≥0∞) * ∫⁻ x, ‖x - copMap p m s x‖ₑ ^ 2 ∂(copLaw C fun i => (m s i).quantile) =
        ⨅ (ω : Measure (Euc d)) (_ : IsProbabilityMeasure ω),
          StatFormal.Wave23a.barF p (fun s => copLaw C fun i => (m s i).quantile) ω

/-! ### C `lem:ref-potential-limit` (c) -/

/-- `(ψ, φ)` is a conjugate Kantorovich pair for `(ν_X, P_C)` with reference support `S` and covariate support `D`
(cost `‖r − c‖²`): continuous on `S` and `D`, `ψ(r) = min_{c ∈ D} {‖r − c‖² − φ(c)}` on `S`,
`φ(c) = min_{r ∈ S} {‖r − c‖² − ψ(r)}` on `D`, and `∫ ψ dν_X + ∫ φ dP_C = W₂²(ν_X, P_C)`. -/
def IsConjPair {q : ℕ} (ν P : Measure (Euc q)) (S D : Set (Euc q)) (ψ φ : Euc q → ℝ) : Prop :=
  ContinuousOn ψ S ∧ ContinuousOn φ D ∧
    (∀ r ∈ S, (∀ c ∈ D, ψ r ≤ ‖r - c‖ ^ 2 - φ c) ∧ ∃ c ∈ D, ψ r = ‖r - c‖ ^ 2 - φ c) ∧
    (∀ c ∈ D, (∀ r ∈ S, φ c ≤ ‖r - c‖ ^ 2 - ψ r) ∧ ∃ r ∈ S, φ c = ‖r - c‖ ^ 2 - ψ r) ∧
    ∫ r, ψ r ∂ν + ∫ c, φ c ∂P = (TauCeti.wassersteinEDist 2 ν P ^ 2).toReal

/-- C `lem:ref-potential-limit` (c): if `S = closure Ω` with `Ω ⊆ ℝ^q` bounded, open and connected, `ν_X` a probability
law with support `S` (`ν_X(Sᶜ) = 0` and every ball centred in `S` has positive mass), and `P_C` a probability law
carried by a compact set `D`, then the conjugate Kantorovich pair with `∫ φ dP_C = 0` is unique (on `S × D`). No
density is assumed. -/
def ref_potential_unique : Prop :=
  ∀ (q : ℕ) (Ω D : Set (Euc q)) (ν P : Measure (Euc q)) (ψ₁ φ₁ ψ₂ φ₂ : Euc q → ℝ),
    IsOpen Ω → IsConnected Ω → Bornology.IsBounded Ω → IsCompact D →
    IsProbabilityMeasure ν → IsProbabilityMeasure P → ν (closure Ω)ᶜ = 0 →
    (∀ r ∈ closure Ω, ∀ ε > 0, 0 < ν (Metric.ball r ε)) → P Dᶜ = 0 →
    IsConjPair ν P (closure Ω) D ψ₁ φ₁ → IsConjPair ν P (closure Ω) D ψ₂ φ₂ →
    ∫ c, φ₁ c ∂P = 0 → ∫ c, φ₂ c ∂P = 0 →
      (∀ r ∈ closure Ω, ψ₁ r = ψ₂ r) ∧ ∀ c ∈ D, φ₁ c = φ₂ c

/-! ### SB `lem:equiv` (static part) -/

/-- SB `lem:equiv`, the static identity of its proof (the dynamic part is the chain rule on path space, not
covered): for a coupling `π` with Lebesgue density `p` on `ℝ^d × ℝ^d` whose first marginal `μ` has density
`m = ∫ p(·, y) dy > 0`, with `p log p`, `m log m` and `‖x − y‖² p` integrable,
`ε KL(π ‖ R₀₁) = (½ ∫ ‖x − y‖² dπ − ε Ent(π)) + ε Ent(μ) + (εd/2) log(2πε)` (Mathlib's `klDiv`, finite), with
`Ent(π) = −∫ p log p`, `Ent(μ) = −∫ m log m`. Minimising over `π ∈ Π(μ, ν)` gives `eq:calib` with the constant
`(εd/2) log(2πε)`. -/
def equiv_static : Prop :=
  ∀ (d : ℕ) (ε : ℝ) (p : Euc d × Euc d → ℝ) (m : Euc d → ℝ),
    0 < ε → Measurable p → (∀ z, 0 ≤ p z) → Integrable p → ∫ z, p z = 1 →
    (∀ x, m x = ∫ y, p (x, y)) → (∀ x, 0 < m x) →
    Integrable (fun z => p z * Real.log (p z)) → Integrable (fun x => m x * Real.log (m x)) →
    Integrable (fun z => ‖z.1 - z.2‖ ^ 2 * p z) →
      let π := volume.withDensity fun z => ENNReal.ofReal (p z)
      InformationTheory.klDiv π (refEndpoint d ε m) ≠ ∞ ∧
        ε * (InformationTheory.klDiv π (refEndpoint d ε m)).toReal =
          (1 / 2 * (∫ z, ‖z.1 - z.2‖ ^ 2 * p z) - ε * -(∫ z, p z * Real.log (p z))) +
            ε * -(∫ x, m x * Real.log (m x)) + ε * d / 2 * Real.log (2 * Real.pi * ε)

/-! ### SB `cor:field-npn` (exactness) -/

/-- SB `cor:field-npn`, standardisation: if `μ` is nonparanormal with a positive-definite correlation matrix `R_μ`,
then `𝕊_μ = R_μ^{-1/2} Z_μ` pushes `μ` onto `N(0, I_d)`. -/
def field_npn_std : Prop :=
  ∀ (d : ℕ) (μ : Measure (Euc d)) (R : Matrix (Fin d) (Fin d) ℝ),
    IsProbabilityMeasure μ → R.PosDef → InNPN μ R →
      μ.map (npnStd μ R) = ProbabilityTheory.multivariateGaussian 0 1

/-- SB `cor:field-npn`, exactness: if the group law `R_s` and the target `ν` are nonparanormal (`R_s` with a
positive-definite correlation matrix, `ν` with a positive-semidefinite one) and `ν` has continuous marginals `G_i`,
then the repair `T_s` pushes `R_s` exactly onto `ν`. -/
def field_npn_exact : Prop :=
  ∀ (d : ℕ) (μs ν : Measure (Euc d)) (Rs Rν : Matrix (Fin d) (Fin d) ℝ),
    IsProbabilityMeasure μs → IsProbabilityMeasure ν → Rs.PosDef → Rν.PosSemidef →
    InNPN μs Rs → InNPN ν Rν → (∀ i, NullSingletonClass (marg ν i)) →
      μs.map (npnMap μs ν Rs Rν) = ν

/-! ### G `lem:jacobicosh`, matrix-ODE core -/

/-- G `lem:jacobicosh`, the matrix-ODE core (in a parallel orthonormal frame of `γ'^⊥`, `𝖠` is the fundamental
solution of the Jacobi equation for the normal component): if `𝖠'' + 𝖱𝖠 = 0`, `𝖠(0) = I`, `𝖠'(0) = 0`, `𝖱(r)`
symmetric with `−κ² I ≤ 𝖱(r) ≤ 0` for `r ≥ 0`, then for every `r ≥ 0` and `y`,
`‖y‖ ≤ ‖𝖠(r) y‖ ≤ cosh(κr) ‖y‖` (no focal points, and the bound behind `eq:jacobicosh`). Operators on a
finite-dimensional real inner product space; `A'` is the derivative of `A`. -/
def jacobicosh_core : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (A A' R : ℝ → E →L[ℝ] E) (κ : ℝ),
    0 ≤ κ → (∀ r, HasDerivAt A (A' r) r) → (∀ r, HasDerivAt A' (-((R r).comp (A r))) r) →
    A 0 = ContinuousLinearMap.id ℝ E → A' 0 = 0 →
    (∀ r x y, ⟪R r x, y⟫ = ⟪x, R r y⟫) →
    (∀ r, 0 ≤ r → ∀ x, -(κ ^ 2 * ‖x‖ ^ 2) ≤ ⟪R r x, x⟫ ∧ ⟪R r x, x⟫ ≤ 0) →
      ∀ r, 0 ≤ r → ∀ y, ‖y‖ ≤ ‖A r y‖ ∧ ‖A r y‖ ≤ Real.cosh (κ * r) * ‖y‖

/-! ### TM `thm:interp` -/

/-- Standing hypotheses of TM `thm:interp` (`ass:smooth`, densities part): `P = p·λ`, `Q = q·λ` probability laws on
`ℝ^d`, `p = q` off a measurable set `X` of finite volume (paper: `supp P ∪ supp Q ⊆ 𝒳` bounded), and `f ∈ L²(ℝ^d; ℂ)`
a representative of `p − q`. -/
def InterpHyp {d : ℕ} (p q : Euc d → ℝ) (X : Set (Euc d)) (f : Lp ℂ 2 (volume : Measure (Euc d))) : Prop :=
  Measurable p ∧ Measurable q ∧ (∀ x, 0 ≤ p x) ∧ (∀ x, 0 ≤ q x) ∧ Integrable p ∧ Integrable q ∧
    ∫ x, p x = 1 ∧ ∫ x, q x = 1 ∧ MeasurableSet X ∧ volume X < ∞ ∧ (∀ x ∉ X, p x = q x) ∧
    (f : Euc d → ℂ) =ᵐ[volume] fun x => ((p x - q x : ℝ) : ℂ)

/-- TM `thm:interp`, interpolation core: for `s, t > 0`, `θ = t/(s + t)` and `‖p − q‖_{H^t} < ∞`,
`TV(P, Q) ≤ ½ |X|^{1/2} ‖p − q‖_{H^{−s}}^θ ‖p − q‖_{H^t}^{1−θ}`. -/
def interp_core : Prop :=
  ∀ (d : ℕ) (p q : Euc d → ℝ) (X : Set (Euc d)) (f : Lp ℂ 2 (volume : Measure (Euc d))) (s t : ℝ),
    InterpHyp p q X f → 0 < s → 0 < t → sobNorm t f < ∞ →
      StatFormal.Distances.tvDist (volume.withDensity fun x => ENNReal.ofReal (p x))
          (volume.withDensity fun x => ENNReal.ofReal (q x)) ≤
        1 / 2 * √(volume X).toReal * (sobNorm (-s) f).toReal ^ (t / (s + t)) *
          (sobNorm t f).toReal ^ (1 - t / (s + t))

/-- TM `thm:interp` as printed: if `‖p − q‖_{H^{−s}} ≤ A_k MMD_k(P, Q)` and `‖p − q‖_{H^t} ≤ L`, then
`TV(P, Q) ≤ ½ |X|^{1/2} A_k^θ L^{1−θ} MMD_k(P, Q)^θ` (`MMD_k(P, Q)` enters only through the defining inequality of
`A_k`, so it is any `m ≥ 0` satisfying it). -/
def interp_bound : Prop :=
  ∀ (d : ℕ) (p q : Euc d → ℝ) (X : Set (Euc d)) (f : Lp ℂ 2 (volume : Measure (Euc d))) (s t A L m : ℝ),
    InterpHyp p q X f → 0 < s → 0 < t → 0 ≤ A → 0 ≤ L → 0 ≤ m →
    sobNorm (-s) f ≤ ENNReal.ofReal (A * m) → sobNorm t f ≤ ENNReal.ofReal L →
      StatFormal.Distances.tvDist (volume.withDensity fun x => ENNReal.ofReal (p x))
          (volume.withDensity fun x => ENNReal.ofReal (q x)) ≤
        1 / 2 * √(volume X).toReal * A ^ (t / (s + t)) * L ^ (1 - t / (s + t)) * m ^ (t / (s + t))

/-! ### NN `lem:marked-block-transform` (exact part) -/

/-- NN `lem:marked-block-transform`, the counting identity behind `eq:exact-marked-pgf`:
`Σ_{(π, ι) ∈ 𝒟_{q,m}} ∏_i z_i^{N_i} = m! [x^m] exp(e^x − 1) ∏_i (e^{z_i x} − 1)`, for every `z ∈ ℝ^q`. -/
def marked_block_count : Prop :=
  ∀ (q m : ℕ) (z : Fin q → ℝ),
    ∑ x : LabPart q m, markedWeight z x =
      (m.factorial : ℝ) * PowerSeries.coeff m (bellEGF * ∏ i, expm1 (z i))

/-- NN `lem:marked-block-transform`, `eq:exact-marked-pgf`: for `q ≤ m` (so that `𝒟_{q,m} ≠ ∅`),
`E_{U_{q,m}}[∏_i z_i^{N_i}] = [x^m] exp(e^x − 1) ∏_i (e^{z_i x} − 1) / [x^m] exp(e^x − 1)(e^x − 1)^q`. -/
def marked_block_transform : Prop :=
  ∀ (q m : ℕ) (z : Fin q → ℝ), q ≤ m →
    markedPGF q m z = PowerSeries.coeff m (bellEGF * ∏ i, expm1 (z i)) /
      PowerSeries.coeff m (bellEGF * expm1 1 ^ q)

end Claims

end StatFormal.Wave24f
