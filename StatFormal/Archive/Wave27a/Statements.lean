import StatFormal.Archive.OTFD.Wave1.Statements
import StatFormal.Archive.WaveP3e.Statements
import StatFormal.Archive.Wave26a.Statements
import StatFormal.Archive.OTFD.WaveL6.Statements
import StatFormal.Archive.Wave25b.Statements
import Mathlib.MeasureTheory.Measure.Prod

/-!
# FROZEN STATEMENTS — wave 27a (last uncovered rows): otfd A `prop:estimated-basis` (ii), (iv) and
# `cor:estimated-basis-sample`; B `prop:band-two-stage`; G `prop:ratesgeneral` on CAT(0) targets; T `prop:Cb` on the
# model spaces `H_k`, `S^d`

Sources (current text of `otfd/papers/`, read 2026-10-17; verbatim in `lean-formalisation/inventory/extracted/`):
* A `prop:estimated-basis` (`A_sieves/main.tex:1031-1093`, proof `supplement.tex:1993-2121`, with `lem:app-reflection`
  `:1974-1991`); `cor:estimated-basis-sample` (`supplement.tex:5345-5363`, proof `:2131-2193`), with
  `thm:app-hard-diagonal` (Step 1) and `prop:integrated-sieve-strong`.
* B `prop:band-two-stage` (`B_bands/supplement.tex:1407-1421`, the paragraph *Closing the loop* `:1398-1406`, proof
  `:2412-2466`), with `thm:band-containment`, `lem:app-esssup-subgradients`, A `thm:sieve-convergence`.
* G `prop:ratesgeneral` (`G_geodesic/supp_moved.tex:523-539`, proof `appendix.tex:716-756`, `rem:ratesradius`
  `:757-`), with `thm:rates` (`main.tex:849-878`, proof `appendix.tex:626-715`, paragraph *Quantiles* `:695-715`).
* T `prop:Cb` (`T_tangent/supp_moved.tex:1017-1049`, proof `app_proofs.tex:205-305`), `prop:base`, `eq:basebridge`
  (`sec_tangent_theory.tex:641-660`), `eq:L` (`supp_moved.tex:834-838`).
Imports the frozen statement files of OTFD wave 1 (`PellClass`, `truncK`), P3e (`IsCAT0`, `IsGeodFrom`, `hypLog`,
`hypTransport`, `sphLog`; through it 24f `minkB`, `OnHyp`, `tanNorm`, `hypExp`, `hypDist`, 6b `sphDist`, `sphExp`,
P3a `sphTransport`, 24c `frechetSet`, 23a `popSupp`, 22a `IsSubgrad`, `supAff`, `reflE`, `signCoef`, 8b `embed`,
L1 `IsCMMapAE`, `Euc`), 26a (`schDens`, `BddCost`, `IsSchrodingerPot`; 24b `empLaw`), L6 and 25b (through it Ranks
`IsMin`), not copied. New definitions: `hypGeod`, `hypHoriz`, `CbAdmHyp`, `sphGeod`, `sphHoriz`, `CbAdmSph`,
`LbAdmHyp`, `condT`, `empT`, `targetErr`.

Covered (12 claims):
* A `prop:estimated-basis` (ii): `ebasis_pell` (for EVERY realisation of the held-out orthonormal `K`-frame and every
  offset, `P̂_K = law(Π̂_K(X − m̂)) ∈ 𝒫^ℓ(ℝ^K)`), `ebasis_uncond` (conditional-on-`𝓘₀` probability bounds, `≤ α` or
  `≥ β`, hold unconditionally under independence of the folds: the sentence "finite-sample ones therefore also hold
  unconditionally"). (iv): `ebasis_target` — the proof's deterministic statement in uniform form: `𝒯_K(f) ≤ δ` once the
  sign-aligned frame error `Σ_{k<K}‖η_k f_k − e_k‖²` is `≤ ε(δ)`, for ANY family of rank maps of the `Π_f#P`;
  `ebasis_target_prob` — `𝒯_K(n₀) → 0` in (outer) probability and in `L¹`, and almost surely for nested folds,
  CONDITIONAL on the frame error tending to `0` in probability (resp. a.s.).
* A `cor:estimated-basis-sample`: `ebasis_sample` — the staircase `(K_r, n_{0,r}, N_r)`, CONDITIONAL on the consistency
  of the estimated eigenfunctions (see Not covered); everything else (fixed-`K` hard assignment, reverse Fatou over the
  basis fold, `ebasis_target`, the integrated sieve limit) is proved.
* B `prop:band-two-stage`: `band_two_stage_pop` (the displayed `liminf_K inf_t [x^{↑,pop}_{K,p} − x^{↑,∞}_p] ≥ 0`, and
  the lower edge); `band_two_stage_schedule` (the schedule sentence, CONDITIONAL on `thm:band-containment` at every fixed
  `K`, in outer probability; implied by the certified almost-sure WaveP2a/Wave23c `band_containment_discharged` —
  instance `A = B̄(0, τ_K)`, `e_t = Π_K g_t`, `𝔪 = 0` — only when the failure events are measurable, so NOT discharged
  here).
* G `prop:ratesgeneral`, SPECIALISED to `Λ ≤ 0` on simply connected targets (`ρ_Λ = ∞`, `α_ρ = 1`; the paper's
  "Hadamard manifold" case) and there GENERALISED to CAT(0) metric spaces: `ratesgeneral_cat0` — `E ∫ d(Q̂(v)(t), Q_ε(v)(t))² dμ(v) ≤ K'_ε (1/n + 1/r)` for
  `λ`-a.e. `t`, and the curve-level `E ∫ D(Q̂(v), Q_ε(v))² dμ(v) ≤ K'_ε (1/n + 1/r)` under joint measurability, with
  `α_ρ = 1` and the explicit `K'_ε = 88ρ²e^{18c̄/ε}`, on CAT(0) targets with a first-variation logarithm
  (i.i.d. reference draws; any cost bound `c̄`, the paper's `c̄ = ½(s + ρ)²` being one).
  The paper's hypothesis "sectional curvature at most `Λ ∈ ℝ`" is NOT covered for `Λ > 0`, nor for non-simply-connected
  `Λ ≤ 0` targets (see Not covered).
* T `prop:Cb` (a) on `H_k` (constant curvature `−k²`: locally symmetric, also Hadamard, so (b) there): `cb_hyp`
  (`C = cosh(kb)` admissible, every admissible `C ≥ 1` for a nonconstant geodesic, `≥ cosh(kb)` when `T_pH_k` has a
  vector of norm `b` orthogonal to the geodesic: then `C_b = cosh(kb)`),
  `lb_hyp` (`max{1, sinh(kb)/(kb)}` admissible in `eq:L`, and the least admissible constant is `sinh(kb)/(kb)` when
  `dim T_pH_k ≥ 2`), `cb_hyp_least` (for `dim E ≥ 2` and `p ≠ q`: `C_b = cosh(kb)` and `L_b = sinh(kb)/(kb)` exactly,
  as `IsLeast`; (ii) is the case `k = 1/√2`, `E = ℝ²`); (i) on the unit sphere: `cb_sphere` (`C_b ≤ 1` for every `b`,
  `C_b ≥ 1` when nonconstant).

Not covered (declared):
* A `prop:estimated-basis`: (ii)'s "every fixed-`K` statement holds under its own hypotheses imposed on `P̂_K`" (a
  meta-statement: every frozen fixed-`K` claim is stated for an arbitrary law on `ℝ^K`, and `ebasis_pell` supplies
  `𝒫^ℓ`); (iii)'s rate (Bosq's perturbation bound and `E‖Γ̂₀ − Γ‖²_HS ≤ E‖X‖⁴/n₀`, operator perturbation theory,
  missing); (iv)'s probabilistic step `Σ_k ‖Δ_k‖² → 0` in probability / a.s. (WLLN/SLLN for `Γ̂` in Hilbert–Schmidt norm
  and Bosq: the premise of `ebasis_target_prob`), and its radial-rank / depth sentence; (v) (the frozen certified claims
  cover its sieve part only).
* A `cor:estimated-basis-sample`: the premise `Σ_{k<K}‖η_k ê_k − e_k‖² → 0` in probability (for every `K`), which the
  paper derives from `ϑ_1 > ϑ_2 > ⋯` as just said; `rem:estimated-basis-sample-entropic` (the entropic route).
* B `prop:band-two-stage`: the computed band `B̂_{K_n}(p)` itself (the schedule claim takes the fixed-`K` containment of
  the computed edges as a hypothesis, certified elsewhere almost surely for the frozen computed bands), the grid and
  smoothing schedules `(m_n, ε_n)` (absorbed in the computed edges `x̂_{K,n}`), "a fortiori `B̄_{K_n}(p)`"; the closing
  paragraph on the reverse inequality (a non-result).
* G `prop:ratesgeneral`: `Λ > 0` (`α_ρ = b_Λ(2ρ) = 2ρ√Λ cot(2ρ√Λ)`, spheres of any radius, `SO(3)`, `ℝP^q`) and
  non-simply-connected `Λ ≤ 0` targets (flat tori, compact hyperbolic manifolds: CAT(0) only within `½ inj(M)`) — they
  need the Hessian comparison `b_Λ` for `½d(·, y)²` (Afsari–Tron–Vidal (2.3), (2.5)) and smoothness of the Fréchet
  function within the injectivity radius, not formalised; the stratified/antithetic draws (`2/r`); the bridge
  "a Hadamard manifold with `Log_z = Exp_z^{-1}` in a global orthonormal frame satisfies the first-variation formula"
  (Riemannian first variation, textbook, not formalised).
* T `prop:Cb`: (a) for locally symmetric spaces other than `H_k`, `S^d`; (b) in variable curvature (Riccati comparison);
  "`L_b = 1` there" on spheres (frozen `prop:sphere`, not reproved); (i) for spheres of radius `≠ 1` and `SO(3)`; (ii)
  the isometry Fisher–Rao half-plane `≅ H_{1/√2}` (textbook); (iii) positive definite matrices.

Encodings (to be checked by the critic):
* `prop:estimated-basis`: the held-out basis is any orthonormal `K`-frame `ê` (`Orthonormal ℝ (fun k : Fin K => ê k)`);
  `P̂_K = P.map (fun x => Π̂_K(x − m̂))`, `Π̂_K = truncK ê K`; independence of the folds is the product law
  `P₀ ⊗ Q` and events are measurable sets of the product. `targetErr P K e f F G = ∫⁻ ‖ι_f G(Π_f x) − ι_K F(Π_K x)‖²
  dP` in `[0, ∞]`; rank maps are Borel maps pushing to `μ_K` and a.e. cyclically monotone (the frozen `IsCMMapAE`;
  McCann's uniqueness makes the choice immaterial); in `ebasis_target_prob` the `L¹` statement is a lower integral
  `∫⁻` (the basis folds are not assumed measurable there), the upper-integral version following from the
  outer-probability statement and `𝒯_K ≤ 4ū²`; `μ_K` is any law carried by `B̄(0, ū)` invariant under every
  `reflE η`, `η_k = ±1` (both named references, frozen `ebasis_reflect`); `η_k = signCoef ⟨f_k, e_k⟩` (`sign 0 = 1`).
* `cor:estimated-basis-sample`: basis folds `ê^{(n₀)} : Ω₀ → (ℕ → H)` measurable (product σ-algebra), orthonormal for
  every `ω₀`; fitting fold an i.i.d. sequence `X_i` on `(Ω, Pr)` (the size-`n` fold is `X_0, …, X_{n−1}`); the joint
  expectation is the iterated `∫⁻ ω₀ ∫⁻ ω` (equal to the `P₀ ⊗ Pr` expectation by Tonelli, the integrand being jointly
  measurable); grids and hard assignments exactly as in the frozen Wave 25b `app_hard_diagonal` (`u K n`, `sel K n`
  with `IsMin`, measurable fibres); "uniform laws on `n` distinct points of `supp μ_K` with `W₂ → 0`" is weakened to
  bounded grids with weakly convergent empirical laws (GENERALISATION); `μ` is any reference carried by a ball with
  reflection-invariant `μ_K` (both named references); the schedule is stated as: `StrictMono K_r, n_{0,r}, N_r` and for
  every `ε > 0`, eventually in `r`, the error is `≤ ε` for `N_r ≤ n < N_{r+1}`.
* `prop:band-two-stage`: "the ball law" is encoded by the properties used: carried by `B̄(0, 1)`, `μ(B̄(0, r)) = r`
  (`‖U‖ ∼ Unif(0, 1)`), `B̄(0, 1) ⊆ supp μ` (GENERALISATION); the quantile-map hypotheses of `thm:sieve-convergence` are
  those of the frozen WaveL6 `sieve_quant_norm_cpt` (Lipschitz potentials as `supAff` with slopes in a strongly
  compact `T`), plus `P(Tᶜ) = 0` (`supp P` strongly compact, `T = ch(supp P)`); "reverse fullness"
  `μ(int dom ∇χ̃) = 1` is weakened to `μ`-a.e. Gâteaux differentiability of `χ̃` with gradient `Q` (GENERALISATION);
  `A_p = B̄(0, p)`, `A_{K,p} = B̄(0, τ_K)` with `μ_K(A_{K,p}) ≥ p` (the calibrated `τ_{K,p}` is one; GENERALISATION);
  point evaluation is `[y](t) = ⟨g_t, y⟩`, `‖g_t‖ ≤ Λ` (the paper's `Λ = sup_t (Σ_k e_k(t)²)^{1/2}`, `e_k(t) =
  ⟨g_t, e_k⟩`, so `e_K(t) = Π_K g_t`; any bounded functionals, as the paper allows); edges are the frozen `popSupp`
  (`EReal` essential suprema), the lower edge `x^↓ = −popSupp(−·)`; "`liminf_K inf_t [a_K(t) − b(t)] ≥ 0`" is
  `∀ η > 0, ∀ᶠ K, ∀ t, b(t) ≤ a_K(t) + η` (no `EReal` subtraction). Schedule: the computed edges are arbitrary
  `x̂^{↑,↓}_{K,n} : Ω → T → EReal`; "with probability tending to one" is the outer probability of the failure event
  tending to `0` (no measurability needed, stronger than for any measurable version).
* `prop:ratesgeneral`: target `M` a metric space with the frozen `IsCAT0`; for every base point `z` a map
  `Log z : M → E` into one real Hilbert space `E` with `‖Log_z y‖ = d(z, y)` and, along geodesics `γ_{z,y}` from `z` to
  `y` (frozen `IsGeodFrom`), `(d(γ_{z,y}(s), x)² − d(z, x)²)/s → −2⟨Log_z x, Log_z y⟩` (`s ↓ 0`), jointly measurable
  (`uncurry Log`); curves are labels `x ∈ Y` with time-`t` evaluation `ev x t`, `o(t)` the base point `m(t)`;
  `π_ε(· | v)` at time `t` is `condT` (`p*(v, ·) P` pushed by `ev · t`, `ev · t` measurable, so no `map` junk), the
  fitted conditional `empT = Σ_i n⁻¹ p̂(v, X_i) δ_{X_i(t)}` (`p̂` the empirical Gibbs density at ANY canonically
  extended empirical potentials, frozen Wave 26a); `Q_ε(v)(t)`, `Q̂(v)(t)` any points of the frozen `frechetSet`s (the
  paper's unique minimisers); `Q_ε(·)(t)` measurable (a measurable version; the paper's `v ↦ Q_ε(v)(t)` is continuous);
  the cost is the frozen `BddCost` (`0 ≤ c ≤ c̄`, here `c̄ = ½(s + ρ)²` from the design); `D² = ∫ d² dλ`, `λ` a
  probability. The curve-level bound assumes joint measurability of `(ω, v, t) ↦ d(Q̂, Q_ε)` (Tonelli; the paper takes
  it for granted). `K'_ε = 88ρ²e^{18c̄/ε} = 22(2ρ)²e^{18c̄/ε}` is the frozen Rigollet–Stromme map constant with labels
  bounded by `2ρ`.
* `prop:Cb`: `H_k = {B(x, x) = −1/k², x₀ > 0}` (frozen); the connecting geodesic is `σ ↦ Exp_p(σ Log_p q)`, `P_σ` the
  frozen `hypTransport` from `p` to `γ(σ)` (the transport along the sub-geodesic), norms of tangent vectors `tanNorm`;
  `C` admissible ⇔ `|∂_σ Exp_{γ(σ)}(P_σ v)| ≤ C |γ'(σ)|` for `σ ∈ [0, 1]`, `|v| ≤ b`, for every derivative (`HasDerivAt`)
  — the paper's `C_b` is the least admissible constant (over the chosen family of connecting geodesics; here one
  geodesic, the constants being uniform in `p, q`); `L` admissible ⇔ `|d(Exp_p)_v w| ≤ L|w|` with `d(Exp_p)_v w` the
  derivative of `s ↦ Exp_p(v + s w)` at `0`, `|v| ≤ b` (`eq:L` at one base point; `L_b` the least). On the unit sphere
  `S ⊂ E` (`‖p‖ = 1`), `γ(σ) = Exp_p(σ Log_p q)` with the frozen P3e `sphLog`, `⟨p, q⟩ > −1` (unique minimal geodesic),
  `P_σ` the frozen `sphTransport`; differentiability is claimed for `σ ∈ [0, 1]` (the transport formula degenerates
  only at antipodes).
* No junk values: divisions only by quantities proved nonzero in the proofs or harmless (`sinh(kb)/(kb)` with `k, b >
  0`; in the routes `0/0 = 0` at `v = 0` matches the true limit); every `map` is of a measurable map; `sSup`/`iSup`
  occur only as the frozen `popSupp` (`EReal` `essSup`) and `⨆` over `EReal`/`ℝ≥0∞`; no `toReal`.

Proof notes (author of the draft, 2026-10-17): all 12 claims are proved in `Wave27a/Route*.lean` (`#print` dependencies: propext,
Classical.choice, Quot.sound): `RouteEBasis` (Lipschitz hypersurfaces are closed; their preimage under `x ↦ Π̂(x − m̂)`
lies in `A_W`, `W = Σ w_k ê_k`), `RouteEBasisTarget` (reflection conjugation `J F_f J`, frozen-route
`WaveL1.tendsto_of_cmConc` with `WaveL8.brenier_uniq_H`, bounded Lipschitz test functions to move the plans from
`(Ỹ, ·)` to `(Y, ·)`, the graph-`L²` lemma `OTLimits.tendsto_lintegral_enorm_sub_sq_of_tendsto_graphPlan`; the uniform
form by contradiction), `RouteEBasisSample` (`Wave25b.fixedK_hard_exp` at the estimated basis, `WaveP3c` McCann
existence with `Wave25b.bounded_version`, joint measurability by fibres of the assignment, `limsup_lintegral_le`,
`WaveL3.sieve_strong_limit_uncond`, a staircase), `RouteBandTwoStage` (the essential-supremum bound at interior
subgradients by monotonicity of the subdifferential on small balls of positive `μ_K`-mass — no `μ_K ≪ Leb`; `τ_K`
eventually exceeds `‖Π_K u‖` by continuity from above of `μ{‖Π_K u‖ ≤ s} ↓ μ{‖u‖ ≤ s}`; frozen-route
`WaveL6.sieve_quant_norm_cpt` at the finite net; `Wave25b.exists_diag` for the schedule), `RouteRatesCore` (the
geometric core `d(z, ẑ) ≤ ‖∫ Log_z dν̂ − ∫ Log_z dν‖` from dyadic CN convexity, the variance inequality and dominated
convergence of the first-variation quotients), `RouteRatesGeneral` (labels `Log_{Q_ε(v)(t)} x(t)`, clipped off the
ball, and frozen-route `Wave26a.map_rate`), `RouteCbHyp`, `RouteLbHyp`, `RouteCbSphere` (closed forms of the
geodesic, the transport and the horizontal curves; `|f'|² = d²(cosh²(kr) − sinh²(kr)a²/r²)` on `H_k`,
`d²(cos² r + (sin r/r)² a²)` on `S^d`, `B(e', e') = r'²(1 − φ²) + φ²|w|²` for `d Exp`).

Paper notes: (1) B proof of `prop:band-two-stage`: only `c_K(s) ↓ c_∞(s)` pointwise is needed (not Pólya's uniform
convergence, not `τ_{K,p} ↑ p`), and the step through `lem:app-esssup-subgradients` needs only that `μ_K` charges balls
in the open unit ball (that lemma, frozen in Wave 20a, assumes `ν ≪ Leb`). (2) G: the quantile display holds on any
complete CAT(0) target with a first-variation logarithm, with `α = 1`; the second term of the paper's split and the
first together are exactly the entropic barycentric map error for the label `Log_z x(t)`, so Rigollet–Stromme's map
rate gives the bound in one step. (3) T: on `H_k` the horizontal speed is explicit,
`|∂_σ Exp_{γ(σ)}(P_σ v)|² = |γ'|²(cosh²(k|v|) − sinh²(k|v|)⟨v, γ'(0)⟩²/(|v|²|γ'|²))`, so the bound `cosh(kb)` is
attained exactly at `v ⊥ γ'` and the constant is `1` along `γ'`. (4) A `prop:estimated-basis` (iv): the deterministic
statement needs neither the separation `ϑ_1 > ⋯ > ϑ_{K+1}` nor orthonormality of the estimated frame (it enters only
through the frame error); `prop:vector-transfer` (B) is an instance of frozen claims stated for an arbitrary separable `H`
and an arbitrary dimension `K`, read at `H := H_d` (with the `W`-inner product, i.e. after `J_W`) and `K := dK`, and gets
no claim: (a) WaveL6/WaveL8 `sieve_conv_weak`, `sieve_conv_norm`, `sieve_conv_norm_cube`, WaveL6 `sieve_quant_norm_cpt`,
WaveL3 `sieve_strong_limit_uncond`; (b) Wave24d `calib_ball_limit`, `calib_ball_cont`, `calib_cubic_*`; (c) OTFD Wave6b
`empirical_wass_rate20` at dimension `dK`, Wave8b `emp_bijective_weak`, `app_entropic_weak`, Wave24a
`app_entropic_rate`, Wave16b `emp_bijective`, `app_entropic`.

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace BoundedContinuousFunction

namespace StatFormal.Wave27a

open StatFormal.OTFD.Wave1 (PellClass truncK)
open StatFormal.Wave24f (minkB OnHyp tanNorm hypExp hypDist)
open StatFormal.WaveP3e (hypLog hypTransport sphLog)
open StatFormal.OTFD.Wave6b (sphDist sphExp)
open StatFormal.WaveP3a (sphTransport)

section ModelConstants

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The connecting geodesic `γ(σ) = Exp_p(σ Log_p q)` of `H_k` from `p` (`σ = 0`) to `q` (`σ = 1`). -/
def hypGeod (k : ℝ) (p q : ℝ × E) (σ : ℝ) : ℝ × E := hypExp k p (σ • hypLog k p q)

/-- The horizontal curve `σ ↦ Exp_{γ(σ)}(P_σ v)` of `prop:base` on `H_k`, `P_σ` the parallel transport along `γ`. -/
def hypHoriz (k : ℝ) (p q v : ℝ × E) (σ : ℝ) : ℝ × E :=
  hypExp k (hypGeod k p q σ) (hypTransport k p (hypGeod k p q σ) v)

/-- `C` is admissible in the definition of `C_b` of `prop:base` along the connecting geodesic from `p` to `q` of
`H_k`: `|∂_σ Exp_{γ(σ)}(P_σ v)| ≤ C |γ'(σ)|` for `σ ∈ [0, 1]` and tangent `v ∈ T_pH_k` with `|v| ≤ b` (`C_b` is the
smallest admissible constant). -/
def CbAdmHyp (k b : ℝ) (p q : ℝ × E) (C : ℝ) : Prop :=
  ∀ σ ∈ Icc (0 : ℝ) 1, ∀ v : ℝ × E, minkB p v = 0 → tanNorm v ≤ b → ∀ f' γ' : ℝ × E,
    HasDerivAt (hypHoriz k p q v) f' σ → HasDerivAt (hypGeod k p q) γ' σ → tanNorm f' ≤ C * tanNorm γ'

/-- The connecting (minimal) geodesic `γ(σ) = Exp_p(σ Log_p q)` of the unit sphere from `p` to `q`. -/
def sphGeod (p q : E) (σ : ℝ) : E := sphExp p (σ • sphLog p q)

/-- The horizontal curve `σ ↦ Exp_{γ(σ)}(P_σ v)` on the unit sphere (`P_σ` the frozen `sphTransport` along `γ`). -/
def sphHoriz (p q v : E) (σ : ℝ) : E := sphExp (sphGeod p q σ) (sphTransport p (sphGeod p q σ) v)

/-- `C` is admissible for `C_b` along the minimal geodesic from `p` to `q` of the unit sphere. -/
def CbAdmSph (b : ℝ) (p q : E) (C : ℝ) : Prop :=
  ∀ σ ∈ Icc (0 : ℝ) 1, ∀ v : E, ⟪p, v⟫_ℝ = 0 → ‖v‖ ≤ b → ∀ f' γ' : E,
    HasDerivAt (sphHoriz p q v) f' σ → HasDerivAt (sphGeod p q) γ' σ → ‖f'‖ ≤ C * ‖γ'‖

/-- `L` is admissible in `eq:L` at `p ∈ H_k` for `|v| ≤ b`: `|d(Exp_p)_v(w)| ≤ L |w|` for tangent `v, w`, with
`d(Exp_p)_v(w)` the derivative of `s ↦ Exp_p(v + s w)` at `0` (`L_b` is the smallest admissible constant). -/
def LbAdmHyp (k b : ℝ) (p : ℝ × E) (L : ℝ) : Prop :=
  ∀ v w : ℝ × E, minkB p v = 0 → minkB p w = 0 → tanNorm v ≤ b → ∀ e' : ℝ × E,
    HasDerivAt (fun s : ℝ => hypExp k p (v + s • w)) e' 0 → tanNorm e' ≤ L * tanNorm w

end ModelConstants

section Quantiles

variable {V Y M : Type*} [MeasurableSpace V] [MeasurableSpace Y] [MeasurableSpace M]

/-- The time-`t` law of the entropic conditional `π_ε(· | v)`: `(p*(v, ·) P)` pushed by the evaluation `x ↦ x(t)`
(`evt`), `p* = schDens ε c f g` the population Gibbs density (used with `evt` measurable). -/
def condT (ε : ℝ) (c : V → Y → ℝ) (f : V → ℝ) (g : Y → ℝ) (P : Measure Y) (evt : Y → M) (v : V) : Measure M :=
  (P.withDensity fun x => ENNReal.ofReal (StatFormal.Wave26a.schDens ε c f g v x)).map evt

/-- The fitted time-`t` conditional law `Σ_i n⁻¹ p̂(v, X_i) δ_{X_i(t)}` (`p̂` the empirical Gibbs density). -/
def empT {n : ℕ} (ε : ℝ) (c : V → Y → ℝ) (fh : V → ℝ) (gh : Y → ℝ) (X : Fin n → Y) (evt : Y → M) (v : V) :
    Measure M :=
  ∑ i, ENNReal.ofReal ((n : ℝ)⁻¹ * StatFormal.Wave26a.schDens ε c fh gh v (X i)) • Measure.dirac (evt (X i))

end Quantiles

/-- The target error `𝒯_K(f) = E‖ι_f F_f(Π_f X) − ι_K F_{+,K}(Π_K X)‖²` of an estimated orthonormal `K`-frame `f`
(`F_f` the rank map of `Π_f#P` against `μ_K`, `F` that of `P_K = Π_K#P`), in `[0, ∞]`. -/
def targetErr {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] (P : Measure H)
    (K : ℕ) (e f : ℕ → H) (F Ff : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) : ℝ≥0∞ :=
  ∫⁻ x, ‖StatFormal.OTFD.Wave8b.embed f K (Ff (truncK f K x)) -
    StatFormal.OTFD.Wave8b.embed e K (F (truncK e K x))‖ₑ ^ 2 ∂P

namespace Claims

/-! ### otfd A `prop:estimated-basis` (ii), (iv) -/

/-- A `prop:estimated-basis` (ii), first sentence: for EVERY realisation `ê` of the held-out basis (any orthonormal
`K`-frame) and every offset `m̂`, the coefficient law `P̂_K = law(Π̂_K(X − m̂))` of `X ∼ P ∈ 𝒫^ℓ(H)` lies in
`𝒫^ℓ(ℝ^K)`. -/
def ebasis_pell : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (P : Measure H) (K : ℕ) (eh : ℕ → H) (mh : H),
    PellClass P → Orthonormal ℝ (fun k : Fin K => eh k) →
      PellClass (P.map fun x => truncK eh K (x - mh))

/-- A `prop:estimated-basis` (ii), last sentence: a statement that holds with a given probability conditionally on the
basis fold `𝓘₀` holds with the same probability unconditionally. The basis fold `ω₀ ∼ P₀` is independent of the fitting
and calibration folds `ω ∼ Q` (product law); for a measurable event `A` whose section at every `ω₀` has `Q`-probability
at most `α` (resp. at least `β`), the joint probability is at most `α` (resp. at least `β`). -/
def ebasis_uncond : Prop :=
  ∀ (Ω₀ Ω : Type) [MeasurableSpace Ω₀] [MeasurableSpace Ω] (P₀ : Measure Ω₀) (Q : Measure Ω)
    [IsProbabilityMeasure P₀] [IsProbabilityMeasure Q] (A : Set (Ω₀ × Ω)) (α β : ℝ≥0∞),
    MeasurableSet A →
      ((∀ ω₀, Q {ω | (ω₀, ω) ∈ A} ≤ α) → (P₀.prod Q) A ≤ α) ∧
      ((∀ ω₀, β ≤ Q {ω | (ω₀, ω) ∈ A}) → β ≤ (P₀.prod Q) A)

/-- A `prop:estimated-basis` (iv), the deterministic statement of its proof, in uniform (`ε`–`δ`) form: for
`P ∈ 𝒫^ℓ(H)`, a reference `μ_K` carried by a ball and invariant under every coordinate reflection (both named
references, (i)), the rank map `F = F_{+,K}` of `P_K`, and ANY family of rank maps `F_f` of `Π_f#P` against `μ_K`
(Borel, pushing, `Π_f#P`-a.e. cyclically monotone), `𝒯_K(f) ≤ δ` as soon as the sign-aligned frame error
`Σ_{k<K} ‖η_k f_k − e_k‖²` (`η_k = sign⟨f_k, e_k⟩`, `sign 0 = 1`) is at most `ε(δ)`. No rate, no smoothness, no
fourth moment. -/
def ebasis_target : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (P : ProbabilityMeasure H) (K : ℕ) (μK : ProbabilityMeasure (EuclideanSpace ℝ (Fin K))) (ubar : ℝ)
    (e : ℕ → H) (F : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (Ff : (ℕ → H) → EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)),
    PellClass (P : Measure H) → Orthonormal ℝ (fun k : Fin K => e k) →
    (μK : Measure (EuclideanSpace ℝ (Fin K))) (Metric.closedBall 0 ubar)ᶜ = 0 →
    (∀ η : Fin K → ℝ, (∀ k, η k = 1 ∨ η k = -1) →
      (μK : Measure (EuclideanSpace ℝ (Fin K))).map (StatFormal.OTFD.Wave22a.reflE η) = μK) →
    Measurable F → ((P : Measure H).map (truncK e K)).map F = μK →
    StatFormal.OTFD.WaveL1.IsCMMapAE ((P : Measure H).map (truncK e K)) F →
    (∀ f : ℕ → H, Orthonormal ℝ (fun k : Fin K => f k) → Measurable (Ff f) ∧
      ((P : Measure H).map (truncK f K)).map (Ff f) = μK ∧
      StatFormal.OTFD.WaveL1.IsCMMapAE ((P : Measure H).map (truncK f K)) (Ff f)) →
    ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ f : ℕ → H, Orthonormal ℝ (fun k : Fin K => f k) →
      ∑ k : Fin K, ‖StatFormal.OTFD.Wave22a.signCoef ⟪f k, e k⟫_ℝ • f k - e k‖ ^ 2 ≤ ε →
        targetErr (P : Measure H) K e f F (Ff f) ≤ ENNReal.ofReal δ

/-- A `prop:estimated-basis` (iv), the convergence of the target, CONDITIONAL on the consistency of the estimated
eigenfunctions: basis folds `ê^{(n₀)}` (orthonormal `K`-frames) on `(Ω₀, P₀)` with `Σ_{k<K}‖η_k ê_k − e_k‖² → 0` in
probability give `𝒯_K(n₀) → 0` in (outer) probability and in `L¹(P₀)`; almost surely if the frame error tends to `0`
almost surely (nested folds). Rank maps as in `ebasis_target`, taken bounded by `ū` everywhere (bounded versions; the
target does not depend on the version). -/
def ebasis_target_prob : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (P : ProbabilityMeasure H) (K : ℕ) (μK : ProbabilityMeasure (EuclideanSpace ℝ (Fin K))) (ubar : ℝ)
    (e : ℕ → H) (F : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (Ff : (ℕ → H) → EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (Ω₀ : Type) [MeasurableSpace Ω₀] (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀] (eh : ℕ → Ω₀ → ℕ → H),
    PellClass (P : Measure H) → Orthonormal ℝ (fun k : Fin K => e k) →
    (μK : Measure (EuclideanSpace ℝ (Fin K))) (Metric.closedBall 0 ubar)ᶜ = 0 →
    (∀ η : Fin K → ℝ, (∀ k, η k = 1 ∨ η k = -1) →
      (μK : Measure (EuclideanSpace ℝ (Fin K))).map (StatFormal.OTFD.Wave22a.reflE η) = μK) →
    Measurable F → ((P : Measure H).map (truncK e K)).map F = μK →
    StatFormal.OTFD.WaveL1.IsCMMapAE ((P : Measure H).map (truncK e K)) F → (∀ z, ‖F z‖ ≤ ubar) →
    (∀ f : ℕ → H, Orthonormal ℝ (fun k : Fin K => f k) → Measurable (Ff f) ∧
      ((P : Measure H).map (truncK f K)).map (Ff f) = μK ∧
      StatFormal.OTFD.WaveL1.IsCMMapAE ((P : Measure H).map (truncK f K)) (Ff f) ∧ ∀ z, ‖Ff f z‖ ≤ ubar) →
    (∀ n₀ ω₀, Orthonormal ℝ (fun k : Fin K => eh n₀ ω₀ k)) →
      ((∀ ε : ℝ, 0 < ε → Tendsto (fun n₀ => P₀ {ω₀ | ε < ∑ k : Fin K,
          ‖StatFormal.OTFD.Wave22a.signCoef ⟪eh n₀ ω₀ k, e k⟫_ℝ • eh n₀ ω₀ k - e k‖ ^ 2}) atTop (𝓝 0)) →
        (∀ δ : ℝ, 0 < δ → Tendsto (fun n₀ => P₀ {ω₀ |
          ENNReal.ofReal δ < targetErr (P : Measure H) K e (eh n₀ ω₀) F (Ff (eh n₀ ω₀))}) atTop (𝓝 0)) ∧
        Tendsto (fun n₀ => ∫⁻ ω₀, targetErr (P : Measure H) K e (eh n₀ ω₀) F (Ff (eh n₀ ω₀)) ∂P₀) atTop (𝓝 0)) ∧
      ((∀ᵐ ω₀ ∂P₀, Tendsto (fun n₀ => ∑ k : Fin K,
          ‖StatFormal.OTFD.Wave22a.signCoef ⟪eh n₀ ω₀ k, e k⟫_ℝ • eh n₀ ω₀ k - e k‖ ^ 2) atTop (𝓝 0)) →
        ∀ᵐ ω₀ ∂P₀, Tendsto (fun n₀ => targetErr (P : Measure H) K e (eh n₀ ω₀) F (Ff (eh n₀ ω₀))) atTop (𝓝 0))

/-! ### otfd A `cor:estimated-basis-sample` -/

/-- A `cor:estimated-basis-sample`, CONDITIONAL on the consistency of the estimated eigenfunctions. Setting of
`prop:estimated-basis`: `P ∈ 𝒫^ℓ(H)`, `(e_k)` the population FPCA basis (complete orthonormal), `μ` a reference
carried by a ball whose coefficient laws `μ_K = Π_K#μ` are invariant under coordinate reflections (both named
references), `𝔽_P` its `μ`-distribution function (Borel, `𝔽_P#P = μ`, `P`-a.e. cyclically monotone). Basis folds:
for each size `n₀` a measurable estimated orthonormal basis `ê^{(n₀)}` on a probability space `(Ω₀, P₀)`, with
`Σ_{k<K} ‖η_k ê_k − e_k‖² → 0` in probability for every `K` (the premise; the paper derives it from the separation
`ϑ_1 > ϑ_2 > ⋯` through the law of large numbers for `Γ̂` and Bosq's perturbation bound, `prop:estimated-basis`
(iii)–(iv), not formalised). Fitting fold: `X_1, X_2, …` i.i.d. `P` on `(Ω, Pr)`, independent of the basis fold
(the joint expectation is the iterated integral over `P₀ ⊗ Pr`). Grids `u_{K,n}` bounded with empirical laws
converging weakly to `μ_K` (implied by `W₂(μ_{K,n}, μ_K) → 0` on `supp μ_K`), hard assignments `σ̂` optimal with a
measurable tie rule. Then there are strictly increasing `K_r`, `n_{0,r}`, `N_r` such that, with
`(K, n₀) = (K_r, n_{0,r})` for `N_r ≤ n < N_{r+1}`,
`E[n⁻¹ Σ_{i<n} ‖ι̂_K u_{σ̂(i)} − 𝔽_P(X_i)‖²] → 0`. -/
def ebasis_sample : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (P μ : ProbabilityMeasure H) (FP : H → H) (M : ℝ)
    (Ω₀ : Type) [MeasurableSpace Ω₀] (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀] (eh : ℕ → Ω₀ → ℕ → H)
    (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (X : ℕ → Ω → H)
    (u : (K n : ℕ) → Fin n → EuclideanSpace ℝ (Fin K))
    (sel : (K n : ℕ) → (Fin n → EuclideanSpace ℝ (Fin K)) → Equiv.Perm (Fin n)),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    PellClass (P : Measure H) → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
    (∀ (K : ℕ) (η : Fin K → ℝ), (∀ k, η k = 1 ∨ η k = -1) →
      ((μ : Measure H).map (truncK e K)).map (StatFormal.OTFD.Wave22a.reflE η) = (μ : Measure H).map (truncK e K)) →
    Measurable FP → (P : Measure H).map FP = μ → StatFormal.OTFD.WaveL1.IsCMMapAE (P : Measure H) FP →
    (∀ n₀ ω₀, Orthonormal ℝ (eh n₀ ω₀)) → (∀ n₀, Measurable (eh n₀)) →
    (∀ (K : ℕ) (ε : ℝ), 0 < ε → Tendsto (fun n₀ => P₀ {ω₀ | ε < ∑ k : Fin K,
      ‖StatFormal.OTFD.Wave22a.signCoef ⟪eh n₀ ω₀ k, e k⟫_ℝ • eh n₀ ω₀ k - e k‖ ^ 2}) atTop (𝓝 0)) →
    (∀ i, Measurable (X i)) → ProbabilityTheory.iIndepFun X Pr → (∀ i, Pr.map (X i) = P) →
    (∀ K, ∃ R : ℝ, ∀ n i, ‖u K n i‖ ≤ R) →
    (∀ K (f : EuclideanSpace ℝ (Fin K) →ᵇ ℝ), Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i, f (u K n i)) atTop
      (𝓝 (∫ z, f z ∂((μ : Measure H).map (truncK e K))))) →
    (∀ K n z, StatFormal.OTFD.Ranks.IsMin (u K n) z (sel K n z)) →
    (∀ K n h, MeasurableSet {z | sel K n z = h}) →
      ∃ Kr n₀r Nr : ℕ → ℕ, StrictMono Kr ∧ StrictMono n₀r ∧ StrictMono Nr ∧
        ∀ ε : ℝ, 0 < ε → ∃ R : ℕ, ∀ r, R ≤ r → ∀ n, Nr r ≤ n → n < Nr (r + 1) →
          ∫⁻ ω₀, ∫⁻ ω, (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n,
            ‖StatFormal.OTFD.Wave8b.embed (eh (n₀r r) ω₀) (Kr r)
                (u (Kr r) n (sel (Kr r) n (fun j => truncK (eh (n₀r r) ω₀) (Kr r) (X j ω)) i)) -
              FP (X i ω)‖ₑ ^ 2 ∂Pr ∂P₀ ≤ ENNReal.ofReal ε

/-! ### otfd B `prop:band-two-stage` -/

/-- B `prop:band-two-stage`, population inequality (both edges), with `𝔪 = 0`. `H` separable Hilbert with complete
orthonormal `(e_k)`; `μ` a law with the properties of the ball law used (`‖U‖ ∼ Unif(0, 1)`: `μ(B̄(0, r)) = r` for
`r ∈ [0, 1]`, carried by and with support containing the closed unit ball); the quantile-map hypotheses of A
`thm:sieve-convergence` in the form of the frozen `sieve_quant_norm_cpt` (Lipschitz potentials `χ̃ = supAff S b`,
`χ'_K = supAff S_K b_K`, slopes in a strongly compact `T` with `P(Tᶜ) = 0`: `supp P` strongly compact), `𝕼_P = Q`,
`Q_{+,K}`; reverse fullness in Gâteaux form (`μ`-a.e. `u` is a point of Gâteaux differentiability of `χ̃` with
gradient `Q u`); sieve regions `A_{K,p} = B̄(0, τ_K)` of `μ_K`-content at least `p` (the ball calibration
`τ_{K,p}` is one); point evaluation `[y](t) = ⟨g_t, y⟩` with `‖g_t‖ ≤ Λ` (so `e_K(t) = Π_K g_t`). Then the Hilbert
edge `x^{↑,∞}_p(t) = μ-ess sup_{u ∈ A_p} [Q(u)](t)`, `A_p = B̄(0, p)`, and the sieve edge
`x^{↑,pop}_{K,p}(t) = μ_K-ess sup_{z ∈ A_{K,p}} ⟨e_K(t), Q_{+,K}(z)⟩` satisfy
`liminf_K inf_t [x^{↑,pop}_{K,p}(t) − x^{↑,∞}_p(t)] ≥ 0` (for every `η > 0`, eventually in `K`, for all `t`,
`x^{↑,∞}_p(t) ≤ x^{↑,pop}_{K,p}(t) + η`), and symmetrically for the lower edges `x^↓ = −ess sup ⟨−·, ·⟩`. -/
def band_two_stage_pop : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (P μ : ProbabilityMeasure H) (T S : Set H) (b : H → ℝ) (x₀ : H) (Q : H → H)
    (SK : (K : ℕ) → Set (StatFormal.OTFD.WaveL1.Euc K)) (bK : (K : ℕ) → StatFormal.OTFD.WaveL1.Euc K → ℝ)
    (zK : (K : ℕ) → StatFormal.OTFD.WaveL1.Euc K)
    (QK : (K : ℕ) → StatFormal.OTFD.WaveL1.Euc K → StatFormal.OTFD.WaveL1.Euc K) (τ : ℕ → ℝ) (p Λ : ℝ)
    (Tt : Type) (gt : Tt → H),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    PellClass (P : Measure H) →
    (μ : Measure H) (Metric.closedBall 0 1)ᶜ = 0 →
    (∀ r ∈ Icc (0 : ℝ) 1, (μ : Measure H) (Metric.closedBall 0 r) = ENNReal.ofReal r) →
    Metric.closedBall 0 1 ⊆ (μ : Measure H).support →
    IsCompact T → (P : Measure H) Tᶜ = 0 → S.Nonempty → S ⊆ T →
    BddAbove (range fun y : S => ⟪x₀, (y : H)⟫ - b y) →
    Measurable Q → (μ : Measure H).map Q = P →
    (∀ᵐ u ∂(μ : Measure H), StatFormal.OTFD.Wave22a.IsSubgrad (StatFormal.OTFD.Wave22a.supAff S b) u (Q u)) →
    (∀ K, (SK K).Nonempty) → (∀ K, SK K ⊆ truncK e K '' T) →
    (∀ K, BddAbove (range fun z : SK K => ⟪zK K, (z : StatFormal.OTFD.WaveL1.Euc K)⟫ - bK K z)) →
    (∀ K, Measurable (QK K)) →
    (∀ K, ((μ : Measure H).map (truncK e K)).map (QK K) = (P : Measure H).map (truncK e K)) →
    (∀ K, ∀ᵐ z ∂((μ : Measure H).map (truncK e K)),
      StatFormal.OTFD.Wave22a.IsSubgrad (StatFormal.OTFD.Wave22a.supAff (SK K) (bK K)) z (QK K z)) →
    (∀ᵐ u ∂(μ : Measure H), ∀ v, HasLineDerivAt ℝ (StatFormal.OTFD.Wave22a.supAff S b) ⟪Q u, v⟫ u v) →
    0 < p → p < 1 →
    (∀ K, ENNReal.ofReal p ≤ ((μ : Measure H).map (truncK e K)) (Metric.closedBall 0 (τ K))) →
    (∀ t, ‖gt t‖ ≤ Λ) →
      (∀ η : ℝ, 0 < η → ∀ᶠ K in atTop, ∀ t,
        StatFormal.Wave23a.popSupp (μ : Measure H) (Metric.closedBall 0 p) Q (gt t) ≤
          StatFormal.Wave23a.popSupp ((μ : Measure H).map (truncK e K)) (Metric.closedBall 0 (τ K)) (QK K)
            (truncK e K (gt t)) + (η : EReal)) ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ K in atTop, ∀ t,
        -StatFormal.Wave23a.popSupp ((μ : Measure H).map (truncK e K)) (Metric.closedBall 0 (τ K)) (QK K)
            (-truncK e K (gt t)) ≤
          -StatFormal.Wave23a.popSupp (μ : Measure H) (Metric.closedBall 0 p) Q (-gt t) + (η : EReal))

/-- B `prop:band-two-stage`, the schedule sentence, CONDITIONAL on `thm:band-containment` at every fixed `K` in
probability (the certified WaveP2a/Wave23c `band_containment_discharged` gives the almost-sure form for the frozen
computed bands; it implies this premise when the failure events are measurable — continuity from above fails for outer
measures — so the premise is not discharged here):
the hypotheses of `band_two_stage_pop`, and computed upper/lower edges `x̂^↑_{K,n}`, `x̂^↓_{K,n}` (random, on
`(Ω, Pr)`, for every `K` already along admissible within-`K` grid and smoothing sequences) such that for every `K`
and `η > 0` the (outer) probability that the computed band fails to contain the sieve population band
`[x^{↓,pop}_{K,p} − η, x^{↑,pop}_{K,p} + η]` tends to `0`. Then there is a deterministic nondecreasing `K_n → ∞`
along which, for every `η > 0`, the computed band contains the `η`-deflation `[x^{↓,∞}_p + η, x^{↑,∞}_p − η]` of the
Hilbert band with probability tending to one (outer probability of failure `→ 0`). -/
def band_two_stage_schedule : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (P μ : ProbabilityMeasure H) (T S : Set H) (b : H → ℝ) (x₀ : H) (Q : H → H)
    (SK : (K : ℕ) → Set (StatFormal.OTFD.WaveL1.Euc K)) (bK : (K : ℕ) → StatFormal.OTFD.WaveL1.Euc K → ℝ)
    (zK : (K : ℕ) → StatFormal.OTFD.WaveL1.Euc K)
    (QK : (K : ℕ) → StatFormal.OTFD.WaveL1.Euc K → StatFormal.OTFD.WaveL1.Euc K) (τ : ℕ → ℝ) (p Λ : ℝ)
    (Tt : Type) (gt : Tt → H) (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (xhU xhL : ℕ → ℕ → Ω → Tt → EReal),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    PellClass (P : Measure H) →
    (μ : Measure H) (Metric.closedBall 0 1)ᶜ = 0 →
    (∀ r ∈ Icc (0 : ℝ) 1, (μ : Measure H) (Metric.closedBall 0 r) = ENNReal.ofReal r) →
    Metric.closedBall 0 1 ⊆ (μ : Measure H).support →
    IsCompact T → (P : Measure H) Tᶜ = 0 → S.Nonempty → S ⊆ T →
    BddAbove (range fun y : S => ⟪x₀, (y : H)⟫ - b y) →
    Measurable Q → (μ : Measure H).map Q = P →
    (∀ᵐ u ∂(μ : Measure H), StatFormal.OTFD.Wave22a.IsSubgrad (StatFormal.OTFD.Wave22a.supAff S b) u (Q u)) →
    (∀ K, (SK K).Nonempty) → (∀ K, SK K ⊆ truncK e K '' T) →
    (∀ K, BddAbove (range fun z : SK K => ⟪zK K, (z : StatFormal.OTFD.WaveL1.Euc K)⟫ - bK K z)) →
    (∀ K, Measurable (QK K)) →
    (∀ K, ((μ : Measure H).map (truncK e K)).map (QK K) = (P : Measure H).map (truncK e K)) →
    (∀ K, ∀ᵐ z ∂((μ : Measure H).map (truncK e K)),
      StatFormal.OTFD.Wave22a.IsSubgrad (StatFormal.OTFD.Wave22a.supAff (SK K) (bK K)) z (QK K z)) →
    (∀ᵐ u ∂(μ : Measure H), ∀ v, HasLineDerivAt ℝ (StatFormal.OTFD.Wave22a.supAff S b) ⟪Q u, v⟫ u v) →
    0 < p → p < 1 →
    (∀ K, ENNReal.ofReal p ≤ ((μ : Measure H).map (truncK e K)) (Metric.closedBall 0 (τ K))) →
    (∀ t, ‖gt t‖ ≤ Λ) →
    (∀ (K : ℕ) (η : ℝ), 0 < η → Tendsto (fun n => Pr {ω | ¬ ∀ t,
      StatFormal.Wave23a.popSupp ((μ : Measure H).map (truncK e K)) (Metric.closedBall 0 (τ K)) (QK K)
          (truncK e K (gt t)) ≤ xhU K n ω t + (η : EReal) ∧
      xhL K n ω t ≤ -StatFormal.Wave23a.popSupp ((μ : Measure H).map (truncK e K)) (Metric.closedBall 0 (τ K))
          (QK K) (-truncK e K (gt t)) + (η : EReal)}) atTop (𝓝 0)) →
      ∃ Kn : ℕ → ℕ, Monotone Kn ∧ Tendsto Kn atTop atTop ∧ ∀ η : ℝ, 0 < η →
        Tendsto (fun n => Pr {ω | ¬ ∀ t,
          StatFormal.Wave23a.popSupp (μ : Measure H) (Metric.closedBall 0 p) Q (gt t) ≤ xhU (Kn n) n ω t + (η : EReal) ∧
          xhL (Kn n) n ω t ≤ -StatFormal.Wave23a.popSupp (μ : Measure H) (Metric.closedBall 0 p) Q (-gt t) + (η : EReal)})
          atTop (𝓝 0)

/-! ### otfd G `prop:ratesgeneral` on CAT(0) targets -/

/-- G `prop:ratesgeneral`, SPECIALISED to `Λ ≤ 0` on simply connected targets (no `Λ > 0`, no tori or compact
hyperbolic manifolds) and there GENERALISED from Hadamard manifolds to CAT(0) spaces with a first-variation logarithm, with `α_ρ = 1` and the explicit constant `K'_ε = 88 ρ² e^{18c̄/ε}` (`= Cρ²α_ρ^{−2}`, `C` a function of
`c̄/ε` only). Target `M` CAT(0); at every base point `z` a logarithm `Log z : M → E` into one real Hilbert space `E`
with `‖Log_z y‖ = d(z, y)` and the first-variation formula `d/ds|₀₊ d(γ_{z,y}(s), x)² = −2⟨Log_z x, Log_z y⟩` along
the geodesics `γ_{z,y}` from `z` to `y` (on a Hadamard manifold: `Exp_z^{-1}` read in a global orthonormal frame,
`γ_{z,y}(s) = Exp_z(s Log_z y)`). Design fixed: reference law `μ` on `V`, bounded measurable cost `0 ≤ c ≤ c̄`,
reference draws `V_1..V_r ∼ μ` and curves `X_1..X_n ∼ P` independent; population and ANY empirical (canonically
extended) Schrödinger potentials; `Q_ε(v)(t)` any minimiser of the time-`t` Fréchet function of `π_ε(· | v)`
(measurable in `v`), `Q̂(v)(t)` any minimiser of the fitted one. If for `λ`-a.e. `t`, `d(o(t), X(t)) ≤ ρ` almost
surely, then for `λ`-a.e. `t`, `E ∫ d(Q̂(v)(t), Q_ε(v)(t))² dμ(v) ≤ K'_ε (1/n + 1/r)`, and, when the error is jointly
measurable, `E ∫ D(Q̂(v), Q_ε(v))² dμ(v) ≤ K'_ε (1/n + 1/r)` with `D² = ∫ d² dλ`. -/
def ratesgeneral_cat0 : Prop :=
  ∀ (V Y M T : Type) [MeasurableSpace V] [MeasurableSpace Y] [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    [MeasurableSpace T] (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Log : M → M → E) (γ : M → M → ℝ → M) (ev : Y → T → M) (o : T → M) (ρ : ℝ) (lam : Measure T)
    (μ : Measure V) (P : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure P] [IsProbabilityMeasure lam]
    (ε cbar : ℝ) (c : V → Y → ℝ) (r n : ℕ) (f : V → ℝ) (g : Y → ℝ)
    (fh : (Fin r → V) × (Fin n → Y) → V → ℝ) (gh : (Fin r → V) × (Fin n → Y) → Y → ℝ)
    (Qe : T → V → M) (Qh : (Fin r → V) × (Fin n → Y) → T → V → M),
    StatFormal.WaveP3e.IsCAT0 M → (∀ z y, StatFormal.WaveP3e.IsGeodFrom z y (γ z y)) →
    (∀ z y, ‖Log z y‖ = dist z y) →
    (∀ z x y, Tendsto (fun s : ℝ => (dist (γ z y s) x ^ 2 - dist z x ^ 2) / s) (𝓝[>] 0)
      (𝓝 (-2 * ⟪Log z x, Log z y⟫_ℝ))) →
    Measurable (Function.uncurry Log) →
    (∀ t, Measurable fun x => ev x t) → (∀ᵐ t ∂lam, P {x | ev x t ∉ Metric.closedBall (o t) ρ} = 0) →
    StatFormal.Wave26a.BddCost ε cbar c → 0 < r → 0 < n → StatFormal.Wave26a.IsSchrodingerPot ε c μ P f g →
    (∀ ω, StatFormal.Wave26a.IsSchrodingerPot ε c (StatFormal.Wave24b.empLaw ω.1) (StatFormal.Wave24b.empLaw ω.2)
      (fh ω) (gh ω)) →
    (∀ t, Measurable (Qe t)) →
    (∀ t v, Qe t v ∈ StatFormal.Wave24c.frechetSet (condT ε c f g P (fun x => ev x t) v)) →
    (∀ ω t v, Qh ω t v ∈ StatFormal.Wave24c.frechetSet (empT ε c (fh ω) (gh ω) ω.2 (fun x => ev x t) v)) →
      (∀ᵐ t ∂lam, ∫⁻ ω, ∫⁻ v, ENNReal.ofReal (dist (Qh ω t v) (Qe t v) ^ 2) ∂μ
          ∂((Measure.pi fun _ : Fin r => μ).prod (Measure.pi fun _ : Fin n => P)) ≤
        ENNReal.ofReal (88 * ρ ^ 2 * Real.exp (18 * cbar / ε) * (1 / n + 1 / r))) ∧
      (Measurable (fun q : ((Fin r → V) × (Fin n → Y)) × (V × T) => dist (Qh q.1 q.2.2 q.2.1) (Qe q.2.2 q.2.1)) →
        ∫⁻ ω, ∫⁻ v, ∫⁻ t, ENNReal.ofReal (dist (Qh ω t v) (Qe t v) ^ 2) ∂lam ∂μ
          ∂((Measure.pi fun _ : Fin r => μ).prod (Measure.pi fun _ : Fin n => P)) ≤
        ENNReal.ofReal (88 * ρ ^ 2 * Real.exp (18 * cbar / ε) * (1 / n + 1 / r)))

/-! ### otfd T `prop:Cb` on the model spaces -/

/-- T `prop:Cb` (a) and the sentence "if some connecting geodesic is nonconstant, `C_b ≥ 1`", on the hyperbolic
space `H_k` (constant curvature `−k²`, locally symmetric and Hadamard): along the connecting geodesic `γ` from `p` to
`q`, `γ` and every horizontal curve `σ ↦ Exp_{γ(σ)}(P_σ v)` are differentiable, `C = cosh(kb)` is admissible
(`C_b ≤ cosh(kb)`), every admissible `C` is `≥ 1` when `p ≠ q`, and `≥ cosh(kb)` as soon as `T_pH_k` contains a
vector of norm `b` orthogonal to `γ'(0) = Log_p q` (so then `C_b = cosh(kb)` exactly). -/
def cb_hyp : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (k b : ℝ) (p q : ℝ × E),
    0 < k → 0 < b → OnHyp k p → OnHyp k q →
      (∀ σ, DifferentiableAt ℝ (hypGeod k p q) σ) ∧
      (∀ v σ, minkB p v = 0 → DifferentiableAt ℝ (hypHoriz k p q v) σ) ∧
      CbAdmHyp k b p q (Real.cosh (k * b)) ∧
      (p ≠ q → ∀ C, CbAdmHyp k b p q C → 1 ≤ C) ∧
      (p ≠ q → ∀ w : ℝ × E, minkB p w = 0 → minkB (hypLog k p q) w = 0 → tanNorm w = b →
        ∀ C, CbAdmHyp k b p q C → Real.cosh (k * b) ≤ C)

/-- T `prop:Cb` (a), the vertical constant, on `H_k`: `Exp_p` is differentiable along every tangent line, and
`L = max{1, sinh(kb)/(kb)}` is admissible (`L_b ≤ max{1, sinh(kb)/(kb)}`); as soon as `T_pH_k` contains `v ⊥ w` with
`|v| = b`, `|w| = 1`, every admissible `L` is `≥ sinh(kb)/(kb)` (so `L_b = sinh(kb)/(kb)` exactly). -/
def lb_hyp : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (k b : ℝ) (p : ℝ × E),
    0 < k → 0 < b → OnHyp k p →
      (∀ v w : ℝ × E, minkB p v = 0 → minkB p w = 0 → DifferentiableAt ℝ (fun s : ℝ => hypExp k p (v + s • w)) 0) ∧
      LbAdmHyp k b p (max 1 (Real.sinh (k * b) / (k * b))) ∧
      ((∃ v w : ℝ × E, minkB p v = 0 ∧ minkB p w = 0 ∧ tanNorm v = b ∧ minkB v w = 0 ∧ tanNorm w = 1) →
        ∀ L, LbAdmHyp k b p L → Real.sinh (k * b) / (k * b) ≤ L)

/-- T `prop:Cb` (a) and (ii) without the orthogonality proviso: on `H_k ⊂ ℝ × E` with `dim E ≥ 2` (so `dim H_k ≥ 2`;
the Fisher–Rao half-plane of univariate Gaussians is `H_{1/√2}` with `E = ℝ²`), for `p ≠ q` the least admissible
`C` is exactly `cosh(kb)` ("with equality when some connecting geodesic is nonconstant") and the least admissible `L`
in `eq:L` is exactly `sinh(kb)/(kb)`. -/
def cb_hyp_least : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (k b : ℝ) (p q : ℝ × E),
    2 ≤ Module.finrank ℝ E → 0 < k → 0 < b → OnHyp k p → OnHyp k q → p ≠ q →
      IsLeast {C | CbAdmHyp k b p q C} (Real.cosh (k * b)) ∧
      IsLeast {L | LbAdmHyp k b p L} (Real.sinh (k * b) / (k * b))

/-- T `prop:Cb` (i) and "`C_b ≥ 1`", on the unit sphere `S ⊂ E` (round spheres of radius one; every `b > 0`): along the
minimal geodesic from `p` to `q` (`⟨p, q⟩ > −1`), `γ` is differentiable, the horizontal curves are differentiable at
every `σ ∈ [0, 1]`, `C = 1` is admissible (`C_b ≤ 1`), and every admissible `C` is `≥ 1` when `p ≠ q` (so `C_b = 1`). -/
def cb_sphere : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (b : ℝ) (p q : E),
    0 < b → ‖p‖ = 1 → ‖q‖ = 1 → -1 < ⟪p, q⟫_ℝ →
      (∀ σ, DifferentiableAt ℝ (sphGeod p q) σ) ∧
      (∀ v σ, σ ∈ Icc (0 : ℝ) 1 → ⟪p, v⟫_ℝ = 0 → DifferentiableAt ℝ (sphHoriz p q v) σ) ∧
      CbAdmSph b p q 1 ∧
      (p ≠ q → ∀ C, CbAdmSph b p q C → 1 ≤ C)

end Claims

end StatFormal.Wave27a
