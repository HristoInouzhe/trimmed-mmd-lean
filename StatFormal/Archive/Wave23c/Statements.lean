import StatFormal.Archive.OTFD.Wave3.Statements
import StatFormal.Archive.Wave23a.Statements
import StatFormal.Archive.OTFD.Wave5b.Statements
import StatFormal.Archive.OTFD.Wave13a.Statements
import StatFormal.Archive.OTFD.Wave8c.Statements
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.CDF
import TauCeti.MeasureTheory.OptimalTransport.Brenier
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# FROZEN STATEMENTS — wave 23c (QUEUE rows 291–299, 308–309): otfd B `prop:app-potential-consistency` (with a
# DISCHARGE of Wave 23a `band_containment`), `prop:cubic-band-infinite`, `lem:convex-boundary-null`; G
# `thm:wellposed`, `thm:flatlimit`, `prop:onlyL2`; T `prop:randomised`; ICL `prop:cond-target`; A
# `cor:matched-gaussian-cubic`; R `thm:elliptical`; C `prop:cond-tail-free`

Sources (current text after the 2026-10-15 corrections; verbatim in `lean-formalisation/inventory/extracted/`):
* otfd B `prop:app-potential-consistency` (`otfd/papers/B_bands/supplement.tex:1851-1863`, proof `:1865-1934`), with
  `ass:fixedK-oos` (`:744-776`), Step 1 (`:1772-1818`: `ℓ_i`, `χ_n`, `χ̂_n`, `eq:app-soft-hard-sandwich`), the map
  `Q̂_{K,oos}` (`main.tex:587-600`), `lem:app-subgradient-convergence` (`supplement.tex:1938-1950`) and the frozen
  Wave 23a `band_containment` (`thm:band-containment`, `supplement.tex:805-824`).
* otfd B `prop:cubic-band-infinite` (`supplement.tex:939-970`), with the frozen `OTFD/Wave8c` `cubicLaw`, `cK`;
  `lem:convex-boundary-null` (`supplement.tex:465-468`).
* otfd G `thm:wellposed` (`G_geodesic/main.tex:469-500`), `ass:bounded` (`:276-278`); `thm:flatlimit`
  (`main.tex:668-690`, proof `:692-720`); `prop:onlyL2` (`supp_moved.tex:340-370`, proof `:372-430`), with the frozen
  `OTFD/Wave5b` `lem:stability` objects `GibbsHyp`, `gibbsPlan`, `gibbsMean` and `SBFairness.Stability.tv`.
* otfd T `prop:randomised` (`T_tangent/supp_moved.tex:728-760`, proof `:762-800`).
* ICL `prop:cond-target` (`context-distribution-ICL/paper/v3/sections/06b_cond_theory.tex:8-30`), `Π_μ`
  (`03_framework.tex:18-28`).
* otfd A `cor:matched-gaussian-cubic` (`A_sieves/supplement.tex:2645-2715`).
* otfd R `thm:elliptical` (`R_robustness/sections/s3_infinite.tex:56-75`), `lem:elliptical-proj`
  (`appendix_a.tex:74-92`), proof (`appendix_a.tex:238-262`), with the frozen `OTFD/Wave13a` `tukeyDepthH`.
* otfd C `prop:cond-tail-free` (`C_conditional/main.tex:786-791`, proof `supplement.tex:1707-1715`), with the frozen
  `OTFD/Wave3` `ExchVec`, `calQ`.
Imports the frozen `OTFD/Wave3`, `Wave23a`, `OTFD/Wave5b`, `OTFD/Wave13a`, `OTFD/Wave8c` statements, not copied;
Mathlib and Tau Ceti (`IsCoupling`, `IsKantorovichOptimalTransportMap`) otherwise.

Covered:
* `prop:app-potential-consistency` (specialised, see `FixedKOOS`): `potential_consistency` (a Brenier map exists; a
  convex `φ` on `int 𝒰_K`, `φ(x₀) = 0`, has `∇φ` = every Brenier map `μ_K`-a.e., is unique, and a.s.
  `χ_n − χ_n(x₀) → φ`, `χ̂_n − χ_n(x₀) → φ` uniformly on compacts of `int 𝒰_K`); `potential_consistency_maps` (a.s.
  `Q̂_n → Q` `μ_K`-a.e.). DISCHARGE of Wave 23a: `band_containment_discharged` (the frozen `band_containment`'s
  a.e.-convergence premise replaced by `FixedKOOS`, `Q` a Brenier map, `Q̂_n = entMap` of the data).
* `lem:convex-boundary-null`: `convex_boundary_null`.
* `prop:cubic-band-infinite` (iii), closed form: `cubic_pstar` (`c_K(r/D_∞) = ω_K r^K/Πλ_k` for `r ≤ min a_k`),
  `cubic_pstar_values` (`p*_2 = π/8`, `p*_4 = 12π²/4096`, `p*_8 = 8!π⁴/(24·16⁸)`).
* `thm:wellposed`: `wellposed_infinite` ((a), first clause), `wellposed_osc` ((c): cost in `[0, ½(s+B)²]`, the
  canonical soft potential real-valued with oscillation `≤ ½(s+B)²`).
* `thm:flatlimit`: `flatlimit` (`TV ≤ sΘ/(4η)`, `∫‖F^geo − F^tan‖ dP ≤ sΘ/(2η)`), `flatlimit_flat` (`Θ ≡ 0`: plans
  coincide), `flatlimit_coth` (`x coth x − 1 ≤ min{x, x²/3}`).
* `prop:onlyL2` (ii) (a)⇔(b): `onlyL2_gibbs`.
* `prop:randomised`: `rand_uniform` ((a): `D_rand ∼ Unif[0,1]`, mean `½`), `bar_ge_rad` ((b), Jensen branch,
  pointwise), `randomised_plan` ((b)/(c) example: `σ(2u/ε)` is the a.e.-unique minimiser and meets the constraint),
  `randomised_beta` (`β(ε) = E|U| tanh(|U|/ε) ∈ (0, ½)`, `D_rad ≡ ½`).
* `prop:cond-target` (iii), first sentence: `cond_target_iid`.
* `cor:matched-gaussian-cubic`: `matched_bound` (the `B_{n_r}` display), `matched_logK` (`K = o(log n/log log n)` ⇔
  `log K = o(log q)` along `n = q^K`), `matched_grid` (`q/K → ∞` suffices; the condition forces `q → ∞`),
  `matched_square` (`q = K²` allowed, `log n/log log n ∼ 2K`).
* `thm:elliptical`: `elliptical_F1`, `elliptical_proj` (`lem:elliptical-proj`), `elliptical_depth`
  (`TD_H = F₁(−‖x‖_CM)`), `elliptical_positive` ((i) first part), `elliptical_regions` ((ii) the formula),
  `elliptical_atomless` ((iii)), `elliptical_cm_range` (`‖Σy‖_CM = ⟨Σy,y⟩^{1/2}`).
* `prop:cond-tail-free`: `cond_tail_basis` (depends on `V_K`, `𝔪 + V_K` only), `cond_tail_calibrates` (marginal
  split-conformal calibration of the pooled residuals), `cond_tail_varies` (the conditional law may vary: example).

Not covered (declared):
* `prop:app-potential-consistency`: the general near-optimal fitted dual (`r_n > 0`, entropic duals; needs the
  conjugate-side Arzelà–Ascoli/Wijsman argument of the printed proof, or approximate-potential plan stability);
  `P_K` with a first moment only; the extended-value statements (`χ_K = +∞` off `𝒰_K`, closedness) and the paper's
  normalisation `inf χ_K = 0` with `X_n(0) = 0` (replaced by `φ(x₀) = 0` and `χ_n − χ_n(x₀)`; the printed convergence
  implies this one but the constants `inf_𝒰 χ_n` are not tracked — a weakening; maps and bands are invariant).
* `prop:cubic-band-infinite` (i) (the product quantile map is the Brenier map; `Φ^{-1}`), (ii) (`h^pop = ∞`
  criterion), the equivalence `𝒦_p ≠ ∅ ⇔ p ≥ p*_K` (continuity/strict monotonicity of `c_K`, `τ_{K,p}`), (iv).
* `thm:wellposed`: existence/uniqueness of the entropic plan and of potentials for a continuous Hilbert-space
  marginal (Nutz 2021; missing), (b), (c)'s boundedness of `g^c` on `supp P` beyond the soft-transform bound.
* `thm:flatlimit`: the Riemannian Taylor bound itself (hypothesis), `Θ(r) = 1 − r cot r` on the sphere and the
  Hessian comparison `Θ ≤ κr coth κr − 1`; the sup-norm-free sphere remark.
* `prop:onlyL2`: (i) for general schedules `ε_s/s → η`; (ii) for unbounded bilinear costs (Step 0, Nutz 4.2), (b)⇔(c);
  (iii).
* `prop:randomised`: (a)'s "in particular" (the randomized rank of a training curve has law `μ_{n_ref}`: the first
  marginal of the fitted plan); `D_rad ≤_cx D_rand`, `D_bar ≥_icv D_rand`, `E D_bar ≥ ½` (convex order, disintegration); the
  projected-ball counterexample (`ε*`, `≈ 0.31`, `≈ 0.435`; projected ball law); (c)'s content statement (immediate
  from `D_bar ≡ 1 − β`).
* `prop:cond-target` (i) (universal measurability, ε-optimal Borel policies), (ii), (iii) beyond the first sentence
  (existence, fixed point, uniqueness threshold).
* `cor:matched-gaussian-cubic`: `α_K = √(2π)` (needs `ass:app-weak-conditioning`), the midpoint bound for
  `(Φ^{-1})²`, `W₂(μ_{K,q^K}, μ_K) ≤ ‖λ‖/(q√12)`, `σ_K² ≤ ‖λ‖²`, `P ∈ 𝒫^ℓ(H)`, and the conclusion (sieve term, L4).
* `thm:elliptical`: `ran Σ^{1/2}` is dense, infinite-dimensional and `μ`-null (`lem:cm-null`); compactness of the
  ellipsoids; `‖x‖_CM = ∞` off `ran Σ^{1/2}` (the dual form is the encoding).
* `prop:cond-tail-free`: "not on the query, the weights, the retained set or the potentials" (definitional: `r_K`
  takes no such argument).

Encodings (to be checked by the critic):
* B: `E = ℝ^K` (`EuclideanSpace`), `M_K = I`; `μ_K`, `P_K`, grids as `ProbabilityMeasure`s; `μ_K ≪` every additive
  Haar measure (= Lebesgue a.c.); `𝒰_K = supp μ_K` convex compact; grids carried by `𝒰_K`, converging weakly (on
  compact `𝒰_K` equivalent to the paper's `W₁`); data `Z_0, Z_1, …` iid (`iIndepFun`, `HasLaw`), fit `n` uses
  `Z_0..Z_n` (`N = n+1`; `ε_n log(n+1) → 0`); `f^{(n)} : Ω → ℝ^{n+1}`, no measurability needed (a.s. statements);
  (iv) SPECIALISED to an exactly optimal HARD dual: `∃ π ∈ Π(μ_{K,m_n}, P̂_n)` with `∫‖u−z‖²dπ ≤ ∫ φ_n dμ_{K,m_n} +
  N⁻¹Σf_i` (= `W₂² ≤` hard semi-dual value; since `φ_n ≤ φ̂_n` this is (iv) with `r_n = 0`); P_K SECOND moment;
  Brenier map = Tau Ceti `IsKantorovichOptimalTransportMap` for `½‖u − z‖²` (same maps as `‖u−z‖²`);
  `lagPot`, `softPot`, `hardCT`, `entMap` as printed; normalisation at `x₀ ∈ int 𝒰_K`. Integrals in `dual` are
  genuine (bounded integrands on full-measure sets).
* G: `𝒳` a pseudometric curve space with `D = dist`, `Y v = E_m(sv)` with `D(m, Y v) ≤ s‖v‖`; `c_s = ½D(Y v,x)²`;
  in `flatlimit` the geodesic cost `cs`, `L = Log_m` (bounded by `ρ₀`), `d2 = D(m,·)²` are abstract measurable maps
  and the Taylor expansion with remainder `≤ (s/2)Θ‖v‖²` (`μ⊗P`-a.e.) is a hypothesis; entropic plans are Gibbs plans
  with bounded potentials and the right marginals (`GibbsHyp`, frozen), so existence/uniqueness are not used; `cs`
  bounded on `‖v‖ ≤ 1` only.
* T: `c_K = cdf` of the law of `‖U‖`; `D_bar`, `D_rad` at one `z` through the conditional law `κ`; the two-point
  example parametrises couplings by `p(u) = π({+1}|u)` with the proof's displayed integrand `φ_u` (`entObj`,
  `0 log 0 = 0`), `E_π[U | +1] = 2∫u p(u)dμ₁`, `μ₁ = unifSym 1` (frozen).
* ICL: `𝒵` any measurable space with measurable diagonal (paper: compact); `D_M` = injective tuples; `Π_μ` =
  Mathlib `cond`; `KL` = Mathlib `klDiv`; "no atoms" = `P₀{z} = 0`.
* A: `Λ = ‖λ‖²`, `n_r = q^K` as reals, the `o(·)` conditions as ratio limits.
* R: `H` any real inner product space; `G` centred Gaussian = `IsGaussian (P∘G⁻¹)` with mean-zero projections;
  injective covariance = `Var⟨v,G⟩ > 0` for `v ≠ 0`; `F₁(t) = E Φ(t/√W)`; `‖·‖_CM` in dual form (EReal, `+∞` allowed);
  `TD_H` = frozen `tukeyDepthH` (`ℝ≥0∞`); `Nontrivial H` for the depth claims (else `TD = ⊤`, `‖·‖_CM = ⊥`).
* C: curves in a real inner product space with evaluation functionals on a finite grid `𝒯₀`; `r_K ∈ [0,∞]`;
  calibration = frozen `calQ`, exchangeable pairs (`ExchVec`).

Critic notes:
* All 31 claims are proved in `Wave23c/Route{Tail,PotBasic,PotDual,Potential,PotClaims,CondTarget,Geodesic,Matched,
  EllPhi,EllDepth,Randomised,Cubic}.lean` (axioms: propext, Classical.choice, Quot.sound). Routes reuse the library
  (`Foundations/{Potentials,OTLimits,Empirical,Convex}`), Tau Ceti (Brenier, PIT), the certified `OTFD/Wave5b`
  `stab_tv_osc`, `stab_separable`, `stab_rank`, `OTFD/Wave3` `cal_coverage_lower`, `band_mem_iff`, Wave 23a
  `band_containment`.
* CONDITIONAL claims: `flatlimit`, `flatlimit_flat` take the Riemannian Taylor expansion of `c_s` (remainder
  `≤ (s/2)Θ‖v‖²`, `μ⊗P`-a.e.) as a hypothesis; the card lists them as conditional on it. The discharge
  `band_containment_discharged` is unconditional on the specialised `FixedKOOS`.
* Observations: (1) `prop:app-potential-consistency`'s proof only needs plans whose supports lie in `∂χ_n` when the
  hard dual is exact; the general `r_n` case is genuinely harder. (2) `thm:wellposed` (a) needs `s ≥ 0` (paper
  `s > 0`). (3) No statement was found false.
* Critic (2026-10-15): ACCEPT-WITH-NOTE, all 31 TRUE. Fixes: `matched_bound` now takes `σ_K² ≤ Λ` (printed
  `σ_K² = Σ_{j≤K}λ_j²`, was `σ_K² = Λ`); docstrings (`randomised_plan` is (c)'s reference, the normalisation weakening,
  `elliptical_cm_range` on `ran Σ` only); conditionality of `flatlimit`. Discharge: `band_containment_discharged` is the
  frozen `Wave23a.band_containment` at `μ := μ_K`, `Q := T`, `Q̂_n := entMap` of the data on a full-measure `ω`-set,
  conclusion verbatim (mechanical diff), its a.e.-convergence premise replaced by `FixedKOOS` and `T` Brenier. The
  Taylor hypothesis is implied by the printed pointwise bound (holds on `supp μ × supp P`), is satisfiable (`Θ = 0`
  with the flat identity) and does not by itself give the conclusion (needs `lem:stability`). Thin content
  (accepted as faithful): `convex_boundary_null` (Mathlib `Convex.addHaar_frontier`), `cond_tail_basis`,
  `cond_tail_varies` (an example), `matched_bound`, `cubic_pstar_values` (checked: `π/8 ≈ 0.393`,
  `12π²/4096 ≈ 0.0289`, `8!π⁴/(24·16⁸) ≈ 3.81·10⁻⁵`). Junk audit: `FixedKOOS.dual`'s integrals are genuine (bounded
  continuous integrands, compact `𝒰_K`, finite `P̂_n`), so `r_n = 0` is not trivialised; `projSd > 0` by `inj`; `cmNorm`
  is never `⊥` under `Nontrivial H`; `ellLaw`'s map is measurable (`ℝ` second countable); `ctxLaw`'s conditioning set
  has mass `1`; `klDiv ≠ ⊤` forces `μ ≪ P₀`; the `gibbsMean` and `entObj` integrands are bounded.

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace Gradient

namespace StatFormal.Wave23c

open StatFormal.OTFD.Wave3 (ExchVec calQ bandScore inflBand)
open StatFormal.Wave23a (popSupp fitSupp)
open StatFormal.OTFD.Wave5b (GibbsHyp gibbsPlan gibbsMean)
open StatFormal.SBFairness.Stability (tv)
open TauCeti (IsCoupling IsKantorovichOptimalTransportMap)

/-! ### C: the truncation channel -/

section Truncation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The reconstruction `𝖯_K Y = 𝔪 + Σ_{k<K} ⟨Y − 𝔪, e_k⟩ e_k` (affine projection onto `𝔪 + V_K`). -/
def recon {K : ℕ} (m : H) (e : Fin K → H) (Y : H) : H :=
  m + ∑ k, ⟪Y - m, e k⟫_ℝ • e k

/-- The residual curve `t ↦ (Y − 𝖯_K Y)(t)` on the grid `𝒯₀`, through evaluation functionals. -/
def residCurve {T₀ : Type*} {K : ℕ} (ev : T₀ → H →L[ℝ] ℝ) (m : H) (e : Fin K → H) (Y : H) : T₀ → ℝ :=
  fun t => ev t (Y - recon m e Y)

/-- The sup-norm residual `r_K(Y) = sup_{t ∈ 𝒯₀} |Y(t) − (𝖯_K Y)(t)|`, in `[0, ∞]`. -/
def residK {T₀ : Type*} {K : ℕ} (ev : T₀ → H →L[ℝ] ℝ) (m : H) (e : Fin K → H) (Y : H) : ℝ≥0∞ :=
  ⨆ t, ENNReal.ofReal |residCurve ev m e Y t|

end Truncation

/-! ### B: potentials and maps at fixed `K` -/

section FixedK

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The empirical law `P̂ = N⁻¹ Σ_{i<N} δ_{z_i}`. -/
def empLaw [MeasurableSpace E] {N : ℕ} (z : Fin N → E) : Measure E :=
  ∑ i, ((N : ℕ) : ℝ≥0∞)⁻¹ • Measure.dirac (z i)

/-- The affine pieces `ℓ_i(u) = ⟨u, Z_i⟩ − f̃_i`, `f̃_i = (‖Z_i‖² − f_i)/2`. -/
def lagPiece {N : ℕ} (z : Fin N → E) (f : Fin N → ℝ) (i : Fin N) (u : E) : ℝ :=
  ⟪u, z i⟫_ℝ - (‖z i‖ ^ 2 - f i) / 2

/-- The Laguerre potential `χ_n = max_i ℓ_i` (`N = n + 1` data points). -/
def lagPot {n : ℕ} (z : Fin (n + 1) → E) (f : Fin (n + 1) → ℝ) (u : E) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => lagPiece z f i u

/-- The soft potential `χ̂_n = (ε/2) log(N⁻¹ Σ_i e^{2ℓ_i/ε})`. -/
def softPot {n : ℕ} (ε : ℝ) (z : Fin (n + 1) → E) (f : Fin (n + 1) → ℝ) (u : E) : ℝ :=
  ε / 2 * Real.log ((∑ i, Real.exp (2 * lagPiece z f i u / ε)) / (n + 1))

/-- The hard `c`-transform `φ_n(u) = min_i (‖u − Z_i‖² − f_i)` (the `ε → 0` form of `φ̂_n`). -/
def hardCT {n : ℕ} (z : Fin (n + 1) → E) (f : Fin (n + 1) → ℝ) (u : E) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun i => ‖u - z i‖ ^ 2 - f i

/-- The entropic out-of-sample quantile map `Q̂_n(u) = Σ_i softmax_i((f_i − ‖u − Z_i‖²)/ε) Z_i`
(`subsec:oos-menu`, `M_K = I`). -/
def entMap {N : ℕ} (ε : ℝ) (z : Fin N → E) (f : Fin N → ℝ) (u : E) : E :=
  ∑ i, (Real.exp ((f i - ‖u - z i‖ ^ 2) / ε) / ∑ j, Real.exp ((f j - ‖u - z j‖ ^ 2) / ε)) • z i

variable [MeasurableSpace E] [BorelSpace E]

/-- `ass:fixedK-oos`, specialised: (i) `μ_K ≪ Leb` with convex compact support `𝒰_K`; (ii) `P_K` with a
finite SECOND moment (paper: first); (iii) grids `μ_{K,m_n}` carried by `𝒰_K`, converging weakly to `μ_K`;
data `Z_0, Z_1, …` iid `P_K`, the `n`-th fit using `Z_0, …, Z_n`; (iv) `ε_n > 0`, `ε_n log(n+1) → 0`, and the
fitted vector `f^{(n)}` is EXACTLY optimal for the unregularised semi-dual, almost surely:
`∫ φ_n dμ_{K,m_n} + N⁻¹ Σ_i f_i ≥ W₂²(μ_{K,m_n}, P̂_{K,n})`, written as the existence of a coupling whose cost
`∫ ‖u − z‖² dπ` is at most the hard semi-dual value (`φ_n ≤ φ̂_n`, so this is (iv) with `r_n = 0`). -/
structure FixedKOOS (μ P : ProbabilityMeasure E) (μs : ℕ → ProbabilityMeasure E) {Ω : Type*}
    [MeasurableSpace Ω] (Pr : Measure Ω) (Z : ℕ → Ω → E) (ε : ℕ → ℝ) (f : (n : ℕ) → Ω → Fin (n + 1) → ℝ) :
    Prop where
  ac : ∀ (ρ : Measure E), ρ.IsAddHaarMeasure → (μ : Measure E) ≪ ρ
  convex : Convex ℝ (μ : Measure E).support
  compact : IsCompact (μ : Measure E).support
  moment : ∫⁻ z, ‖z‖ₑ ^ 2 ∂(P : Measure E) ≠ ∞
  grid_supp : ∀ n, (μs n : Measure E) ((μ : Measure E).support)ᶜ = 0
  grid_lim : Tendsto μs atTop (𝓝 μ)
  indep : iIndepFun Z Pr
  law : ∀ i, HasLaw (Z i) (P : Measure E) Pr
  eps_pos : ∀ n, 0 < ε n
  eps_log : Tendsto (fun n : ℕ => ε n * Real.log (n + 1)) atTop (𝓝 0)
  dual : ∀ᵐ ω ∂Pr, ∀ n, ∃ π : Measure (E × E),
    IsCoupling π (μs n : Measure E) (empLaw fun i : Fin (n + 1) => Z i ω) ∧
      ∫ p, ‖p.1 - p.2‖ ^ 2 ∂π ≤
        ∫ u, hardCT (fun i : Fin (n + 1) => Z i ω) (f n ω) u ∂(μs n : Measure E) + (∑ i, f n ω i) / (n + 1)

end FixedK

/-! ### R: elliptical references -/

section Elliptical

variable {Ω H : Type*} [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]

/-- `σ_v = Var[⟨v, G⟩]^{1/2}` (`= ‖Σ^{1/2} v‖`). -/
def projSd (Pr : Measure Ω) (G : Ω → H) (v : H) : ℝ := Real.sqrt (Var[fun ω => ⟪v, G ω⟫_ℝ; Pr])

/-- `F₁(t) = E Φ(t/√W)`: the distribution function of `√W ξ`, `ξ ∼ N(0,1)` independent of `W`
(`Φ = cdf N(0,1)`). -/
def ellF1 (Pr : Measure Ω) (W : Ω → ℝ) (t : ℝ) : ℝ :=
  ∫ ω, cdf (gaussianReal 0 1) (t / Real.sqrt (W ω)) ∂Pr

/-- The Cameron–Martin norm in its dual form `‖x‖_CM = sup_{v ≠ 0} ⟨v, x⟩/σ_v ∈ (−∞, +∞]`
(Bogachev, *Gaussian Measures*, §2.4; `= ‖Σ^{-1/2}x‖` on `ran Σ^{1/2}`, `+∞` off it). -/
def cmNorm (Pr : Measure Ω) (G : Ω → H) (x : H) : EReal :=
  ⨆ v : {v : H // v ≠ 0}, ((⟪(v : H), x⟫_ℝ / projSd Pr G v : ℝ) : EReal)

/-- The elliptical law `μ = 𝓛(√W G)`. -/
def ellLaw (Pr : Measure Ω) (G : Ω → H) (W : Ω → ℝ) : Measure H :=
  Pr.map fun ω => Real.sqrt (W ω) • G ω

/-- The setting of `thm:elliptical`: `G` a centred Gaussian on `H` (every `⟨v, G⟩` Gaussian, mean `0`) with injective
covariance (`Var⟨v, G⟩ > 0` for `v ≠ 0`), `W > 0` a.s. independent of `G`, no integrability of `W`. -/
structure EllSetting (Pr : Measure Ω) (G : Ω → H) (W : Ω → ℝ) : Prop where
  prob : IsProbabilityMeasure Pr
  meas_G : Measurable G
  meas_W : Measurable W
  pos_W : ∀ᵐ ω ∂Pr, 0 < W ω
  indep : IndepFun W G Pr
  gauss : IsGaussian (Pr.map G)
  centred : ∀ v, ∫ ω, ⟪v, G ω⟫_ℝ ∂Pr = 0
  inj : ∀ v, v ≠ 0 → 0 < Var[fun ω => ⟪v, G ω⟫_ℝ; Pr]

end Elliptical

/-! ### T: randomized and barycentric entropic depths -/

/-- The logistic function `σ(x) = (1 + e^{−x})^{-1}`. -/
def logistic (x : ℝ) : ℝ := 1 / (1 + Real.exp (-x))

/-- The pointwise entropic objective of `prop:randomised` (b): for a coupling of `μ₁ = Unif[−1,1]` with
`½δ_{−1} + ½δ_{+1}` written as `p(u) = π({+1} | u)`, the integrand
`φ_u(t) = t c(u,1) + (1−t) c(u,−1) + ε[t log(2t) + (1−t) log(2(1−t))]`, `c(u,z) = ½(u − z)²`
(`0 log 0 = 0`). -/
def entObj (ε u t : ℝ) : ℝ :=
  t * ((u - 1) ^ 2 / 2) + (1 - t) * ((u + 1) ^ 2 / 2) +
    ε * (t * Real.log (2 * t) + (1 - t) * Real.log (2 * (1 - t)))

/-! ### ICL: contexts drawn without replacement -/

/-- `D_M = {z_{1:M} : z_k ≠ z_l for k ≠ l}`. -/
def distinctSet (𝒵 : Type*) (M : ℕ) : Set (Fin M → 𝒵) := {z | Function.Injective z}

/-- The without-replacement context law `Π_μ = μ^{⊗M}(· | D_M)`. -/
def ctxLaw {𝒵 : Type*} [MeasurableSpace 𝒵] (μ : Measure 𝒵) (M : ℕ) : Measure (Fin M → 𝒵) :=
  (Measure.pi fun _ : Fin M => μ)[|distinctSet 𝒵 M]

namespace Claims

/-! ### B `lem:convex-boundary-null` -/

/-- `lem:convex-boundary-null`: the boundary of every convex `C ⊆ ℝ^K` is Lebesgue-null. -/
def convex_boundary_null : Prop :=
  ∀ (K : ℕ) (C : Set (EuclideanSpace ℝ (Fin K))), Convex ℝ C → volume (frontier C) = 0

/-! ### C `prop:cond-tail-free` -/

/-- `r_K` depends on `V_K` (and on `𝔪 + V_K`) only: two orthonormal bases of the same `K`-dimensional
subspace and two base curves differing by an element of it give the same reconstruction, hence the same
residual curve and the same `r_K`, at every curve `Y`. -/
def cond_tail_basis : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (T₀ : Type) (ev : T₀ → H →L[ℝ] ℝ) (K : ℕ)
    (m m' : H) (e e' : Fin K → H),
    Orthonormal ℝ e → Orthonormal ℝ e' → Submodule.span ℝ (Set.range e) = Submodule.span ℝ (Set.range e') →
    m - m' ∈ Submodule.span ℝ (Set.range e) →
      ∀ Y : H, recon m e Y = recon m' e' Y ∧ residCurve ev m e Y = residCurve ev m' e' Y ∧
        residK ev m e Y = residK ev m' e' Y

/-- "Its pooled distribution calibrates the truncation channel marginally over queries": for exchangeable
pairs `(X_i, Y_i)`, `i = 0, …, n₂` (test pair `i = 0`; the covariates are arbitrary and unused), with
`r̂_α` the `⌈(n₂+1)(1−α)⌉`-th smallest pooled calibration residual `r_K(Y_i)`, `i ≥ 1` (`+∞` past `n₂`),
`P(r_K(Y_0) ≤ r̂_α) ≥ 1 − α`, the event being measurable. -/
def cond_tail_calibrates : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H] (𝒳 : Type) [MeasurableSpace 𝒳] (T₀ : Type)
    [Finite T₀] (ev : T₀ → H →L[ℝ] ℝ) (K : ℕ) (m : H) (e : Fin K → H) (n₂ : ℕ)
    (Z : Ω → Fin (n₂ + 1) → 𝒳 × H),
    Measurable Z → ExchVec P Z → ∀ α : ℝ, 0 < α → α < 1 →
      MeasurableSet {ω | residK ev m e (Z ω 0).2 ≤ calQ α fun i => residK ev m e (Z ω i).2} ∧
        ENNReal.ofReal (1 - α) ≤ P {ω | residK ev m e (Z ω 0).2 ≤ calQ α fun i => residK ev m e (Z ω i).2}

/-- "The conditional law of `r_K(Y)` given `X = x` may vary with `x`": there is a curve space, a basis, and a
joint law of a two-valued covariate `X` and a curve `Y` for which the laws of `r_K(Y)` given `X = 0` and given
`X = 1` differ. -/
def cond_tail_varies : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : MeasurableSpace H)
    (T₀ : Type) (ev : T₀ → H →L[ℝ] ℝ) (K : ℕ) (m : H) (e : Fin K → H) (P : Measure (Bool × H)),
    IsProbabilityMeasure P ∧ Orthonormal ℝ e ∧ Measurable (fun Y => residK ev m e Y) ∧
      0 < P {z | z.1 = false} ∧ 0 < P {z | z.1 = true} ∧
      (P[|{z | z.1 = false}]).map (fun z => residK ev m e z.2) ≠
        (P[|{z | z.1 = true}]).map (fun z => residK ev m e z.2)

/-! ### ICL `prop:cond-target` -/

/-- `prop:cond-target` (iii), first sentence: if `P₀` has no atoms, every `μ` with `KL(μ | P₀) < ∞` has
`μ^{⊗M}(D_M) = 1` (so `Π_μ` is defined) and `Π_μ = μ^{⊗M}`: contexts with and without replacement coincide. -/
def cond_target_iid : Prop :=
  ∀ (𝒵 : Type) [MeasurableSpace 𝒵] [MeasurableEq 𝒵] (P₀ μ : Measure 𝒵) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure μ], (∀ z, P₀ {z} = 0) → InformationTheory.klDiv μ P₀ ≠ ⊤ → ∀ M : ℕ,
      (Measure.pi fun _ : Fin M => μ) (distinctSet 𝒵 M) = 1 ∧ ctxLaw μ M = Measure.pi fun _ : Fin M => μ

/-! ### T `prop:randomised` (supplement:727) -/

open StatFormal.OTFD.Wave8c (unifSym)

/-- (a): for any coupling `π` of `μ_K` and `ν̂` with `U` the reference coordinate and a continuous radial
distribution function `c_K(ρ) = μ_K(‖u‖ ≤ ρ)`, the randomized depth `D_rand = 1 − c_K(‖U‖)` is exactly
`Unif[0,1]`, with mean `½`. -/
def rand_uniform : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] (μ ν : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (π : Measure (E × E)),
    IsCoupling π μ ν → Continuous (cdf (μ.map fun u => ‖u‖)) →
      π.map (fun p => 1 - cdf (μ.map fun u => ‖u‖) ‖p.1‖) = volume.restrict (Icc (0 : ℝ) 1) ∧
        ∫ p, (1 - cdf (μ.map fun u => ‖u‖) ‖p.1‖) ∂π = 1 / 2

/-- (b), Jensen branch, pointwise: for a conditional law `κ = π(· | z)` carried by the unit ball and `c_K`
convex and nondecreasing on `[0,1]` and continuous (a continuous distribution function), `D_bar(z) = 1 − c_K(‖E[U | z]‖) ≥ 1 − E[c_K(‖U‖) | z] = D_rad(z)`. -/
def bar_ge_rad : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (κ : Measure E) [IsProbabilityMeasure κ] (c : ℝ → ℝ),
    (∀ᵐ u ∂κ, ‖u‖ ≤ 1) → ConvexOn ℝ (Icc 0 1) c → MonotoneOn c (Icc 0 1) → Continuous c →
      1 - ∫ u, c ‖u‖ ∂κ ≤ 1 - c ‖∫ u, u ∂κ‖

/-- The explicit plan of the proof of (b), for (c)'s reference (`K = 1`, `μ₁ = Unif[−1,1]`; the printed (b) runs the
same computation for the projected ball law), `ν̂ = ½δ_{−1} + ½δ_{+1}`, cost `½|u − z|²`: `p(u) = σ(2u/ε)`
meets the marginal constraint `∫ p dμ₁ = ½` and minimises `∫ φ_u(p(u)) dμ₁` over all measurable `p : ℝ → [0,1]`,
uniquely `μ₁`-a.e. -/
def randomised_plan : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∫ u, logistic (2 * u / ε) ∂unifSym 1 = 1 / 2 ∧
      ∀ p : ℝ → ℝ, Measurable p → (∀ u, p u ∈ Icc (0 : ℝ) 1) →
        ∫ u, entObj ε u (logistic (2 * u / ε)) ∂unifSym 1 ≤ ∫ u, entObj ε u (p u) ∂unifSym 1 ∧
          (∫ u, entObj ε u (p u) ∂unifSym 1 = ∫ u, entObj ε u (logistic (2 * u / ε)) ∂unifSym 1 →
            p =ᵐ[unifSym 1] fun u => logistic (2 * u / ε))

/-- (b), (c): `E_π[U | +1] = β(ε) = 2E[Uσ(2U/ε)] = E[|U| tanh(|U|/ε)] ∈ (0, ½)`, and `D_rad(±1) = ½`
(`c₁(ρ) = ρ` on `[0,1]` for `Unif[−1,1]`): `1 − 2E[|U| σ(2U/ε)] = ½`. Hence `D_bar ≡ 1 − β ≠ ½`. -/
def randomised_beta : Prop :=
  ∀ ε : ℝ, 0 < ε →
    2 * ∫ u, u * logistic (2 * u / ε) ∂unifSym 1 = ∫ u, |u| * Real.tanh (|u| / ε) ∂unifSym 1 ∧
      0 < ∫ u, |u| * Real.tanh (|u| / ε) ∂unifSym 1 ∧ ∫ u, |u| * Real.tanh (|u| / ε) ∂unifSym 1 < 1 / 2 ∧
        1 - 2 * ∫ u, |u| * logistic (2 * u / ε) ∂unifSym 1 = 1 / 2

/-! ### R `thm:elliptical` -/

open StatFormal.OTFD.Wave13a (tukeyDepthH)

/-- `lem:elliptical-proj`, `F₁` part: `F₁` is continuous, strictly increasing, symmetric (`F₁(−t) = 1 − F₁(t)`),
with values in `(0,1)`, `F₁(−∞) = 0`, `F₁(+∞) = 1`. -/
def elliptical_F1 : Prop :=
  ∀ (Ω H : Type) [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
    [BorelSpace H] (Pr : Measure Ω) (G : Ω → H) (W : Ω → ℝ),
    EllSetting Pr G W →
      Continuous (ellF1 Pr W) ∧ StrictMono (ellF1 Pr W) ∧ (∀ t, ellF1 Pr W (-t) = 1 - ellF1 Pr W t) ∧
        (∀ t, 0 < ellF1 Pr W t ∧ ellF1 Pr W t < 1) ∧ Tendsto (ellF1 Pr W) atBot (𝓝 0) ∧
          Tendsto (ellF1 Pr W) atTop (𝓝 1)

/-- `lem:elliptical-proj`: for `v ≠ 0`, `μ{z : ⟨v, z − x⟩ ≤ 0} = F₁(⟨v, x⟩/σ_v)` for every `x`. -/
def elliptical_proj : Prop :=
  ∀ (Ω H : Type) [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
    [BorelSpace H] (Pr : Measure Ω) (G : Ω → H) (W : Ω → ℝ),
    EllSetting Pr G W → ∀ v : H, v ≠ 0 → ∀ x : H,
      ellLaw Pr G W {z | ⟪v, z - x⟫_ℝ ≤ 0} = ENNReal.ofReal (ellF1 Pr W (⟪v, x⟫_ℝ / projSd Pr G v))

/-- `thm:elliptical`, main display: `TD_H(x; μ) = F₁(−‖x‖_CM)`, with `F₁(−∞) := 0`. -/
def elliptical_depth : Prop :=
  ∀ (Ω H : Type) [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
    [BorelSpace H] [Nontrivial H] (Pr : Measure Ω) (G : Ω → H) (W : Ω → ℝ),
    EllSetting Pr G W → ∀ x : H,
      (cmNorm Pr G x = ⊤ → tukeyDepthH (ellLaw Pr G W) x = 0) ∧
        ∀ r : ℝ, cmNorm Pr G x = r → tukeyDepthH (ellLaw Pr G W) x = ENNReal.ofReal (ellF1 Pr W (-r))

/-- `thm:elliptical` (i), first part: the depth is positive exactly on the Cameron–Martin space
`{x : ‖x‖_CM < ∞}`. -/
def elliptical_positive : Prop :=
  ∀ (Ω H : Type) [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
    [BorelSpace H] [Nontrivial H] (Pr : Measure Ω) (G : Ω → H) (W : Ω → ℝ),
    EllSetting Pr G W → ∀ x : H, 0 < tukeyDepthH (ellLaw Pr G W) x ↔ cmNorm Pr G x < ⊤

/-- `thm:elliptical` (ii), the region formula: for `α ∈ (0, ½]`, `D_α = {x : ‖x‖_CM ≤ −F₁^{-1}(α)}`
(`r_α = −F₁^{-1}(α) ≥ 0`). -/
def elliptical_regions : Prop :=
  ∀ (Ω H : Type) [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
    [BorelSpace H] [Nontrivial H] (Pr : Measure Ω) (G : Ω → H) (W : Ω → ℝ),
    EllSetting Pr G W → ∀ α : ℝ, 0 < α → α ≤ 1 / 2 →
      ∃ r : ℝ, 0 ≤ r ∧ ellF1 Pr W (-r) = α ∧
        {x | ENNReal.ofReal α ≤ tukeyDepthH (ellLaw Pr G W) x} = {x | cmNorm Pr G x ≤ r}

/-- `thm:elliptical` (iii): every one-dimensional projection of `μ` is atomless (hence nondegenerate). -/
def elliptical_atomless : Prop :=
  ∀ (Ω H : Type) [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
    [BorelSpace H] (Pr : Measure Ω) (G : Ω → H) (W : Ω → ℝ),
    EllSetting Pr G W → ∀ v : H, v ≠ 0 → ∀ s : ℝ, ellLaw Pr G W {z | ⟪v, z⟫_ℝ = s} = 0

/-- Sanity check of the encoding: the dual Cameron–Martin norm is `‖Σ^{-1/2}x‖` on `ran Σ` (not all of
`ran Σ^{1/2}`): if `Var⟨v, G⟩ = ⟨Σv, v⟩` for a
symmetric `Σ` (`S`), then `‖Σy‖_CM = ⟨Σy, y⟩^{1/2}` (`= ‖Σ^{-1/2}(Σy)‖`). -/
def elliptical_cm_range : Prop :=
  ∀ (Ω H : Type) [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
    [BorelSpace H] [Nontrivial H] (Pr : Measure Ω) (G : Ω → H) (W : Ω → ℝ) (S : H →L[ℝ] H),
    EllSetting Pr G W → (∀ v w, ⟪S v, w⟫_ℝ = ⟪v, S w⟫_ℝ) →
    (∀ v, Var[fun ω => ⟪v, G ω⟫_ℝ; Pr] = ⟪S v, v⟫_ℝ) →
      ∀ y : H, cmNorm Pr G (S y) = ((Real.sqrt ⟪S y, y⟫_ℝ : ℝ) : EReal)

/-! ### B `prop:cubic-band-infinite` -/

open StatFormal.OTFD.Wave8c (cK)

/-- (iii), the closed form of `p*_K = c_K(λ_(K)/(2D_∞))`: for the cubic law with half-widths `a_k = λ_k/2` (frozen
`cubicLaw`, `cK`) and any radius `r ≤ min_k a_k` (the calibrated ball inside the box),
`c_K(r/D_∞) = ω_K r^K / Π_k λ_k`, `ω_K = π^{K/2}/Γ(K/2+1)`. -/
def cubic_pstar : Prop :=
  ∀ (N : ℕ) (a : Fin N → ℝ) (Dinf r : ℝ), 0 < N → (∀ k, 0 < a k) → 0 < Dinf → 0 ≤ r → (∀ k, r ≤ a k) →
    cK a Dinf (r / Dinf) = Real.sqrt Real.pi ^ N / Real.Gamma (N / 2 + 1) * r ^ N / ∏ k, (2 * a k)

/-- (iii), the numbers for `λ_k = 1/k`: `p*_2 = π/8`, `p*_4 = 12π²/4096`, `p*_8 = 8! π⁴/(24·16⁸)`. -/
def cubic_pstar_values : Prop :=
  ∀ Dinf : ℝ, 0 < Dinf →
    cK (fun k : Fin 2 => 1 / (2 * ((k : ℝ) + 1))) Dinf (1 / 4 / Dinf) = Real.pi / 8 ∧
      cK (fun k : Fin 4 => 1 / (2 * ((k : ℝ) + 1))) Dinf (1 / 8 / Dinf) = 12 * Real.pi ^ 2 / 4096 ∧
        cK (fun k : Fin 8 => 1 / (2 * ((k : ℝ) + 1))) Dinf (1 / 16 / Dinf) =
          (Nat.factorial 8 : ℝ) * Real.pi ^ 4 / (24 * 16 ^ 8)

/-! ### A `cor:matched-gaussian-cubic` -/

/-- The display bounding `B_{n_r}` along `n_r = q^K` (its arithmetic): with `α_K = √(2π)`, `β_K² ≤ Λ`,
`σ_K² ≤ Λ` (printed: `σ_K² = Σ_{j≤K} λ_j² ≤ Λ`), `M = √Λ/2` (`Λ = ‖λ‖²_{ℓ²}`) and `W₂²(μ_{K,q^K}, μ_K) ≤ Λ/(12q²)`,
`(4/α_K)(β_K² + σ_K²)^{1/2} {20M²(K+1) n_r^{−2/(K+4)} + W₂²}^{1/2} ≤ (4/√π) Λ {5(K+1) q^{−2K/(K+4)} + 1/(12q²)}^{1/2}`. -/
def matched_bound : Prop :=
  ∀ (K : ℕ) (q Λ β2 σ2 W2 : ℝ), 1 ≤ q → 0 ≤ Λ → 0 ≤ β2 → β2 ≤ Λ → 0 ≤ σ2 → σ2 ≤ Λ → 0 ≤ W2 →
    W2 ≤ Λ / (12 * q ^ 2) →
    4 / Real.sqrt (2 * Real.pi) * Real.sqrt (β2 + σ2) *
        Real.sqrt (20 * (Real.sqrt Λ / 2) ^ 2 * (K + 1) * (q ^ K) ^ (-2 / ((K : ℝ) + 4)) + W2) ≤
      4 / Real.sqrt Real.pi * Λ *
        Real.sqrt (5 * (K + 1) * q ^ (-2 * (K : ℝ) / (K + 4)) + 1 / (12 * q ^ 2))

/-- "Along `n = q^K` the condition `K = o(log n / log log n)` amounts to `log K = o(log q)`": for `q_r → ∞` and
`K_r ≥ 1`, `K_r log log n_r / log n_r → 0` iff `log K_r / log q_r → 0`, `n_r = q_r^{K_r}`. -/
def matched_logK : Prop :=
  ∀ (K q : ℕ → ℕ), Tendsto q atTop atTop → (∀ r, 1 ≤ K r) →
    (Tendsto (fun r => (K r : ℝ) * Real.log (Real.log ((q r : ℝ) ^ K r)) / Real.log ((q r : ℝ) ^ K r)) atTop
        (𝓝 0) ↔
      Tendsto (fun r => Real.log (K r) / Real.log (q r)) atTop (𝓝 0))

/-- The hard bijective route's grid condition: if `K_r → ∞` and `q_r / K_r → ∞` then
`(K_r + 1) q_r^{−2K_r/(K_r+4)} → 0`; conversely the condition forces `q_r → ∞` (for `q_r ≥ 1`). -/
def matched_grid : Prop :=
  ∀ (K q : ℕ → ℕ), (∀ r, 1 ≤ q r) →
    (Tendsto K atTop atTop → Tendsto (fun r => (q r : ℝ) / K r) atTop atTop →
      Tendsto (fun r => ((K r : ℝ) + 1) * (q r : ℝ) ^ (-2 * (K r : ℝ) / (K r + 4))) atTop (𝓝 0)) ∧
    (Tendsto (fun r => ((K r : ℝ) + 1) * (q r : ℝ) ^ (-2 * (K r : ℝ) / (K r + 4))) atTop (𝓝 0) →
      Tendsto q atTop atTop)

/-- "`q_r = K_r²` is allowed although then `log n_r / log log n_r ∼ 2K_r`": with `K_r → ∞` and `q_r = K_r²`, the
grid condition holds and `(log n_r / log log n_r) / K_r → 2`. -/
def matched_square : Prop :=
  ∀ K : ℕ → ℕ, Tendsto K atTop atTop →
    Tendsto (fun r => ((K r : ℝ) + 1) * ((K r : ℝ) ^ 2) ^ (-2 * (K r : ℝ) / (K r + 4))) atTop (𝓝 0) ∧
    Tendsto (fun r => Real.log (((K r : ℝ) ^ 2) ^ K r) / Real.log (Real.log (((K r : ℝ) ^ 2) ^ K r)) / K r)
      atTop (𝓝 2)

/-! ### G `thm:wellposed` -/

/-- `thm:wellposed` (a), first clause: if `E D(m,X)² = ∞` then every coupling has infinite cost `∫ c_s dπ`. The
Riemannian content enters only through `D(m, E_m(sv)) ≤ s‖v‖` (`Y v = E_m(sv)`), the reference through
`μ(‖v‖ ≤ 1) = 1`; `D` is the metric of the curve space `𝒳` and `c_s(v,x) = ½ D(E_m(sv), x)²`. -/
def wellposed_infinite : Prop :=
  ∀ (H 𝒳 : Type) [NormedAddCommGroup H] [MeasurableSpace H] [PseudoMetricSpace 𝒳] [MeasurableSpace 𝒳]
    [OpensMeasurableSpace 𝒳] (μ : Measure H) (P : Measure 𝒳) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (m : 𝒳) (s : ℝ) (Y : H → 𝒳),
    0 ≤ s → (∀ v, dist m (Y v) ≤ s * ‖v‖) → (∀ᵐ v ∂μ, ‖v‖ ≤ 1) → ∫⁻ x, ENNReal.ofReal (dist m x ^ 2) ∂P = ⊤ →
      ∀ π : Measure (H × 𝒳), IsCoupling π μ P → ∫⁻ z, ENNReal.ofReal (dist (Y z.1) z.2 ^ 2 / 2) ∂π = ⊤

/-- `thm:wellposed` (c), under `ass:bounded` (`D(m,X) ≤ B` a.s.): the cost lies in `[0, ½(s+B)²]` on
`{‖v‖ ≤ 1} × supp P`, and the canonical (soft `c`-transform) potential `f^c(v) = −ε log ∫ e^{(g(x) − c_s(v,x))/ε} dP`
built from any measurable `g` with `∫ e^{g/ε} dP < ∞` is real-valued with oscillation at most `½(s+B)²` over
`‖v‖ ≤ 1`. -/
def wellposed_osc : Prop :=
  ∀ (H 𝒳 : Type) [NormedAddCommGroup H] [PseudoMetricSpace 𝒳] [MeasurableSpace 𝒳] [OpensMeasurableSpace 𝒳]
    (P : Measure 𝒳) [IsProbabilityMeasure P] (m : 𝒳) (s B ε : ℝ) (Y : H → 𝒳) (g : 𝒳 → ℝ),
    0 ≤ s → 0 < ε → (∀ v, dist m (Y v) ≤ s * ‖v‖) → (∀ᵐ x ∂P, dist m x ≤ B) → Measurable g →
    Integrable (fun x => Real.exp (g x / ε)) P →
      (∀ v, ‖v‖ ≤ 1 → ∀ᵐ x ∂P, 0 ≤ dist (Y v) x ^ 2 / 2 ∧ dist (Y v) x ^ 2 / 2 ≤ (s + B) ^ 2 / 2) ∧
      (∀ v, ‖v‖ ≤ 1 → 0 < ∫ x, Real.exp ((g x - dist (Y v) x ^ 2 / 2) / ε) ∂P) ∧
      ∀ v v', ‖v‖ ≤ 1 → ‖v'‖ ≤ 1 →
        -ε * Real.log (∫ x, Real.exp ((g x - dist (Y v) x ^ 2 / 2) / ε) ∂P) -
          -ε * Real.log (∫ x, Real.exp ((g x - dist (Y v') x ^ 2 / 2) / ε) ∂P) ≤ (s + B) ^ 2 / 2

/-! ### G `thm:flatlimit` -/

/-- `thm:flatlimit`, the abstract chain. The Riemannian Taylor step is the hypothesis: `μ ⊗ P`-a.e.,
`c_s/s = D(m,x)²/(2s) + (s/2)‖v‖² − ⟨v, Log_m x⟩ + ω_s` with `|ω_s| ≤ (s/2) Θ ‖v‖²` (`Θ = Θ(ρ₀ + sb)`, a number);
`L = Log_m`, bounded by `ρ₀`; `d2 = D(m,·)²`; `μ(‖v‖ ≤ 1) = 1`. The geodesic plan is the Gibbs plan for `c_s` at
temperature `sη`, the tangent plan the Gibbs plan for `c^tan = ½‖v − Log_m x‖²` at temperature `η` (`GibbsHyp`).
Conclusion: `TV(π^geo_s, π^tan) ≤ sΘ/(4η)` and `∫ ‖F^geo_s − F^tan‖ dP ≤ sΘ/(2η)`. -/
def flatlimit : Prop :=
  ∀ (H 𝒳 : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    [BorelSpace H] [SecondCountableTopology H] [MeasurableSpace 𝒳] (μ : Measure H) (P : Measure 𝒳)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] (s η Θ ρ₀ : ℝ) (cs : H × 𝒳 → ℝ) (L : 𝒳 → H)
    (d2 : 𝒳 → ℝ) (f f' : H → ℝ) (g g' : 𝒳 → ℝ),
    0 < s → 0 < η → 0 ≤ Θ → Measurable cs → Measurable L → Measurable d2 → (∀ x, ‖L x‖ ≤ ρ₀) →
    (∃ C, ∀ x, |d2 x| ≤ C) → (∃ C, ∀ z : H × 𝒳, ‖z.1‖ ≤ 1 → |cs z| ≤ C) → (∀ᵐ v ∂μ, ‖v‖ ≤ 1) →
    (∀ᵐ z ∂(μ.prod P), |cs z / s - (d2 z.2 / (2 * s) + s / 2 * ‖z.1‖ ^ 2 - ⟪z.1, L z.2⟫_ℝ)| ≤
      s / 2 * Θ * ‖z.1‖ ^ 2) →
    GibbsHyp μ P (s * η) cs f g → GibbsHyp μ P η (fun z => ‖z.1 - L z.2‖ ^ 2 / 2) f' g' →
      tv (gibbsPlan μ P (s * η) cs f g) (gibbsPlan μ P η (fun z => ‖z.1 - L z.2‖ ^ 2 / 2) f' g') ≤
          s * Θ / (4 * η) ∧
        ∫⁻ x, ‖gibbsMean μ (s * η) cs f g id x -
          gibbsMean μ η (fun z => ‖z.1 - L z.2‖ ^ 2 / 2) f' g' id x‖ₑ ∂P ≤ ENNReal.ofReal (s * Θ / (2 * η))

/-- `thm:flatlimit`, flat case (`Θ ≡ 0`, e.g. `ℝ^q` or a flat torus within the injectivity radius): the geodesic
and tangent plans coincide. -/
def flatlimit_flat : Prop :=
  ∀ (H 𝒳 : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    [BorelSpace H] [SecondCountableTopology H] [MeasurableSpace 𝒳] (μ : Measure H) (P : Measure 𝒳)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] (s η ρ₀ : ℝ) (cs : H × 𝒳 → ℝ) (L : 𝒳 → H)
    (d2 : 𝒳 → ℝ) (f f' : H → ℝ) (g g' : 𝒳 → ℝ),
    0 < s → 0 < η → Measurable cs → Measurable L → Measurable d2 → (∀ x, ‖L x‖ ≤ ρ₀) →
    (∃ C, ∀ x, |d2 x| ≤ C) → (∃ C, ∀ z : H × 𝒳, ‖z.1‖ ≤ 1 → |cs z| ≤ C) → (∀ᵐ v ∂μ, ‖v‖ ≤ 1) →
    (∀ᵐ z ∂(μ.prod P), cs z / s = d2 z.2 / (2 * s) + s / 2 * ‖z.1‖ ^ 2 - ⟪z.1, L z.2⟫_ℝ) →
    GibbsHyp μ P (s * η) cs f g → GibbsHyp μ P η (fun z => ‖z.1 - L z.2‖ ^ 2 / 2) f' g' →
      gibbsPlan μ P (s * η) cs f g = gibbsPlan μ P η (fun z => ‖z.1 - L z.2‖ ^ 2 / 2) f' g'

/-- `thm:flatlimit`, last sentence: `x coth x − 1 ≤ min{x, x²/3}` for `x > 0` (the Hadamard bound
`κr coth(κr) − 1 ≤ min{κr, κ²r²/3}`). -/
def flatlimit_coth : Prop :=
  ∀ x : ℝ, 0 < x → x * (Real.cosh x / Real.sinh x) - 1 ≤ x ∧ x * (Real.cosh x / Real.sinh x) - 1 ≤ x ^ 2 / 3

/-! ### G `prop:onlyL2` -/

/-- `prop:onlyL2` (ii), (a) ⇔ (b), for bounded measurable costs in Gibbs form: two entropic plans in `Π(μ, P)` at the
same temperature coincide iff the cost difference is separable `μ ⊗ P`-a.e. (with integrable parts). -/
def onlyL2_gibbs : Prop :=
  ∀ (V 𝒳 : Type) [MeasurableSpace V] [MeasurableSpace 𝒳] (μ : Measure V) (P : Measure 𝒳)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] (ε : ℝ) (c c' : V × 𝒳 → ℝ) (f f' : V → ℝ)
    (g g' : 𝒳 → ℝ),
    0 < ε → Measurable c → Measurable c' → (∃ C, ∀ z, |c z| ≤ C) → (∃ C, ∀ z, |c' z| ≤ C) →
    GibbsHyp μ P ε c f g → GibbsHyp μ P ε c' f' g' →
      (gibbsPlan μ P ε c f g = gibbsPlan μ P ε c' f' g' ↔
        ∃ (u : V → ℝ) (w : 𝒳 → ℝ), Measurable u ∧ Measurable w ∧ Integrable u μ ∧ Integrable w P ∧
          ∀ᵐ z ∂(μ.prod P), c z - c' z = u z.1 + w z.2)

/-! ### B `prop:app-potential-consistency` -/

/-- `prop:app-potential-consistency` (specialised as in `FixedKOOS`; normalisation at a point `x₀ ∈ int 𝒰_K`
instead of `inf χ_K = 0`): there is a Brenier map from `μ_K` to `P_K`; there is a convex `φ` on `int 𝒰_K`
with `φ(x₀) = 0` whose gradient equals every Brenier map `μ_K`-a.e.; it is the unique such function on
`int 𝒰_K`; and almost surely `χ_n − χ_n(x₀) → φ` and `χ̂_n − χ_n(x₀) → φ` uniformly on compact subsets of
`int 𝒰_K`. -/
def potential_consistency : Prop :=
  ∀ (K : ℕ) (μ P : ProbabilityMeasure (EuclideanSpace ℝ (Fin K)))
    (μs : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin K))) (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω)
    [IsProbabilityMeasure Pr] (Z : ℕ → Ω → EuclideanSpace ℝ (Fin K)) (ε : ℕ → ℝ)
    (f : (n : ℕ) → Ω → Fin (n + 1) → ℝ) (x₀ : EuclideanSpace ℝ (Fin K)),
    FixedKOOS μ P μs Pr Z ε f → x₀ ∈ interior (μ : Measure (EuclideanSpace ℝ (Fin K))).support →
      (∃ T, IsKantorovichOptimalTransportMap (fun z => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) (μ : Measure (EuclideanSpace ℝ (Fin K)))
        (P : Measure (EuclideanSpace ℝ (Fin K))) T) ∧
      ∃ φ : EuclideanSpace ℝ (Fin K) → ℝ, ConvexOn ℝ (interior (μ : Measure (EuclideanSpace ℝ (Fin K))).support) φ ∧ φ x₀ = 0 ∧
        (∀ T, IsKantorovichOptimalTransportMap (fun z => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) (μ : Measure (EuclideanSpace ℝ (Fin K)))
          (P : Measure (EuclideanSpace ℝ (Fin K))) T → ∀ᵐ u ∂(μ : Measure (EuclideanSpace ℝ (Fin K))), DifferentiableAt ℝ φ u ∧ ∇ φ u = T u) ∧
        (∀ ψ : EuclideanSpace ℝ (Fin K) → ℝ, ConvexOn ℝ (interior (μ : Measure (EuclideanSpace ℝ (Fin K))).support) ψ → ψ x₀ = 0 →
          (∀ᵐ u ∂(μ : Measure (EuclideanSpace ℝ (Fin K))), DifferentiableAt ℝ ψ u ∧ ∇ ψ u = ∇ φ u) →
            EqOn ψ φ (interior (μ : Measure (EuclideanSpace ℝ (Fin K))).support)) ∧
        ∀ᵐ ω ∂Pr,
          TendstoLocallyUniformlyOn (fun n u => lagPot (fun i : Fin (n + 1) => Z i ω) (f n ω) u -
            lagPot (fun i : Fin (n + 1) => Z i ω) (f n ω) x₀) φ atTop (interior (μ : Measure (EuclideanSpace ℝ (Fin K))).support) ∧
          TendstoLocallyUniformlyOn (fun n u => softPot (ε n) (fun i : Fin (n + 1) => Z i ω) (f n ω) u -
            lagPot (fun i : Fin (n + 1) => Z i ω) (f n ω) x₀) φ atTop (interior (μ : Measure (EuclideanSpace ℝ (Fin K))).support)

/-- The map form (`prop:app-potential-consistency` with `lem:app-subgradient-convergence`(a)): for every Brenier
map `T`, almost surely `Q̂_n(u) → T(u)` for `μ_K`-a.e. `u`. -/
def potential_consistency_maps : Prop :=
  ∀ (K : ℕ) (μ P : ProbabilityMeasure (EuclideanSpace ℝ (Fin K)))
    (μs : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin K))) (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω)
    [IsProbabilityMeasure Pr] (Z : ℕ → Ω → EuclideanSpace ℝ (Fin K)) (ε : ℕ → ℝ)
    (f : (n : ℕ) → Ω → Fin (n + 1) → ℝ) (T : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)),
    FixedKOOS μ P μs Pr Z ε f →
    IsKantorovichOptimalTransportMap (fun z => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) (μ : Measure (EuclideanSpace ℝ (Fin K)))
      (P : Measure (EuclideanSpace ℝ (Fin K))) T →
      ∀ᵐ ω ∂Pr, ∀ᵐ u ∂(μ : Measure (EuclideanSpace ℝ (Fin K))),
        Tendsto (fun n => entMap (ε n) (fun i : Fin (n + 1) => Z i ω) (f n ω) u) atTop (𝓝 (T u))

/-- DISCHARGE of the premise of the frozen Wave 23a `band_containment` (`thm:band-containment`): with the
population map `Q_{±,K}` a Brenier map `T` from `μ_K` to `P_K` and `Q̂_n` the fitted entropic maps, under
`FixedKOOS` alone, almost surely, for every `η > 0`, eventually `x↑pop ≤ x̂↑_n + η` and `x̂↓_n ≤ x↓pop + η`,
uniformly in `t`. -/
def band_containment_discharged : Prop :=
  ∀ (K : ℕ) (μ P : ProbabilityMeasure (EuclideanSpace ℝ (Fin K)))
    (μs : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin K))) (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω)
    [IsProbabilityMeasure Pr] (Z : ℕ → Ω → EuclideanSpace ℝ (Fin K)) (ε : ℕ → ℝ)
    (f : (n : ℕ) → Ω → Fin (n + 1) → ℝ) (T : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (𝒯 : Type) (A : Set (EuclideanSpace ℝ (Fin K))) (mfrak : 𝒯 → ℝ) (e : 𝒯 → EuclideanSpace ℝ (Fin K)),
    FixedKOOS μ P μs Pr Z ε f →
    IsKantorovichOptimalTransportMap (fun z => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) (μ : Measure (EuclideanSpace ℝ (Fin K)))
      (P : Measure (EuclideanSpace ℝ (Fin K))) T →
    MeasurableSet A → (∃ R : ℝ, ∀ᵐ u ∂(μ : Measure (EuclideanSpace ℝ (Fin K))).restrict A, ‖T u‖ ≤ R) → (∃ C : ℝ, ∀ t, ‖e t‖ ≤ C) →
      ∀ᵐ ω ∂Pr, ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t,
        (mfrak t : EReal) + popSupp (μ : Measure (EuclideanSpace ℝ (Fin K))) A T (e t) ≤
            (mfrak t : EReal) + fitSupp A (entMap (ε n) (fun i : Fin (n + 1) => Z i ω) (f n ω)) (e t) +
              (η : EReal) ∧
          (mfrak t : EReal) - fitSupp A (entMap (ε n) (fun i : Fin (n + 1) => Z i ω) (f n ω)) (-e t) ≤
            (mfrak t : EReal) - popSupp (μ : Measure (EuclideanSpace ℝ (Fin K))) A T (-e t) + (η : EReal)

end Claims

end StatFormal.Wave23c
