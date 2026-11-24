import StatFormal.Archive.Wave21b.Statements
import StatFormal.Archive.Wave9b.Statements
import StatFormal.Archive.OTFD.WaveL3.Statements
import StatFormal.Archive.OTFD.Wave8c.Statements
import StatFormal.Archive.Wave16a.Statements
import StatFormal.Archive.Wave7b.Statements
import StatFormal.Archive.Wave23c.Statements
import StatFormal.Archive.OTFD.Wave22a.Statements
import StatFormal.Archive.Wave20a.Statements

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 24d (QUEUE rows 343–359): otfd A `prop:calibrations`, `lem:app-references-Pl`,
# `lem:app-reflection`, `thm:prob-content`; R `lem:elliptical-proj`; B `prop:calibrations`, `prop:trimmed-band`,
# `cor:band-coverage-asymptotic`, `prop:rk-transfer-consistency`; C `cor:coordinate-obstruction-empirical`,
# `thm:neural-score-learning`; G `lem:decoupling`; T `eq:explicitbridge-mult`; robust equality `prop:pays`;
# SB `cor:field-ell`, `cor:field-local`; ICL `cor:consistency`

Sources (current text, read 2026-10-15; verbatim in `lean-formalisation/inventory/extracted/`):
* otfd A (`otfd/papers/A_sieves/supplement.tex`): `prop:calibrations` (`:451-509`, proofs `:1904-1953`),
  `lem:app-references-Pl` (`:996-1015`, proof `:1017-1059`, with the frozen Wave 20a `lem:app-block-Pl` and
  `def:app-lipschitz-hypersurface`), `lem:app-reflection` (`:1965-1972`, proof `:1974-1982`), `thm:prob-content`
  (`:5056-5076`).
* otfd R `lem:elliptical-proj` (`R_robustness/sections/appendix_a.tex:74-84`, proof `:86-94`).
* otfd B: `prop:calibrations` (`B_bands/main.tex:518-540`, with `def:depth-family` `:502-516`); `prop:trimmed-band`
  (`supplement.tex:986-1042`); `cor:band-coverage-asymptotic` (`supplement.tex:1075-1105`, with the population band
  `:779-793`); `prop:rk-transfer-consistency` (`supplement.tex:5279-5304`, proof `:5306-5347`).
* otfd C (`C_conditional/supplement.tex`): `cor:coordinate-obstruction-empirical` (`:502-512`, proof `:514-527`);
  `thm:neural-score-learning` (`:2835-2844`, proof `:1312-1336`, `eq:energy-score` `:1276-1281`).
* otfd G `lem:decoupling` (`G_geodesic/appendix.tex:80-86`, proof `:88-118`).
* otfd T `cor:linearmodel-mult` (`eq:explicitbridge-mult`; `T_tangent/supp_moved.tex:206-229`), with the model of
  `prop:linearmodel` (`:181-201`).
* Robust equality JASA `prop:pays` (`robust-equality-outcomes-under-distribution-shift/jasa/supp_proofs.tex:680-694`,
  proof `:696-700`), with `T^𝒩_s` (`main.tex:349`) and `prop:envelope`(iii).
* SB `cor:field-ell` (`data-fairness-repair/schrodinger_bridge_fairness_repair.tex:1017-1023`), `cor:field-local`
  (`:1087-1096`), with `def:standardisable` (`:932-949`), `thm:field` (`:956-995`).
* ICL `cor:consistency` (`context-distribution-ICL/paper/v3/sections/06_estimation.tex:107-114`, proof
  `supp/proofs_main.tex:123-160`), with `thm:joint` (`06_estimation.tex:76-89`).
Imports the frozen `Wave21b` (`lamClass`, `probOn`, `gaussClass`, `phiLin`, `piB`, `avgLogMgf`), `Wave9b`
(`Standardises`), `OTFD/WaveL3` (through it `OTFD/WaveL1` `IsCMMapAE`, `Euc`, `OTFD/Wave1` `PellClass`, `IsLipHyp`,
`lipHyp`, `truncK`, `OTFD/Wave19a` `extTop`), `OTFD/Wave8c` (`naiveLaw`, `mnorm`, `mvec`, `unifRadius`, `cubicLaw`,
`rhoBox`), `Wave16a` (`IsOptPlan`), `Wave7b` (through it `OTFD/Wave6b` `sphDist`, `sphExp`), `Wave23c` (`EllSetting`,
`ellF1`, `ellLaw`, `projSd`; through it `Wave23a` `popSupp`, `fitSupp`), `OTFD/Wave22a` (`energyD`), `Wave20a`
statements, not copied; Mathlib and Tau Ceti otherwise.

Covered (43 claims):
* A/B `prop:calibrations`: (b) `calib_ball_limit` (`c_K(τ) → τ` on `[0,1]`), `calib_ball_cont` (`c_K` continuous, `c_K(0) = 0`, `c_K(1) = 1`); (c) `calib_cubic_range` (`ρ ∈ [0, D_K/D_∞]`
  a.s., `D_K/D_∞ < 1`, the corner characterisation), `calib_cubic_limit` (a.s. and `L²` convergence to `‖X‖/D_∞`, limit
  `< 1` a.s.), `calib_cubic_nondeg` (`Var > 0`), `calib_cubic_cdf` (`c_K → c_∞` at continuity points),
  `calib_cubic_cont` (`c_K` continuous, `c_K(0) = 0`, `c_K(1) = 1`). (a) is the certified Wave 8c `naive_calibration`;
  the reshaping identity of (b), `‖L⁻¹Ũ‖_{M_K} = ‖Ũ‖₂`, is the certified Wave 8c `naive_norm` (`r = ‖Ũ‖`, `θ = Ũ/‖Ũ‖`).
* A `lem:app-references-Pl`: (ii) `refs_Pl_cubic`; necessity: `refs_Pl_hyperplane`, `refs_Pl_cubic_degenerate`,
  `refs_Pl_ball_degenerate`.
* A `lem:app-reflection`: `app_reflection_rank`, `app_reflection_quantile`.
* A `thm:prob-content` (naive reference): `prob_content_naive_pell`, `prob_content_naive_exists`,
  `prob_content_naive`; the a.e. inverse (GHS Lemma 4.3 in `ℝ^K`) is the certified Wave L5 `ghs_inverse_H` at
  `H = ℝ^K` (with `μ = μ_K` by `prob_content_naive_pell`; any other monotone `Q` agrees with it by the certified Wave L3
  `brenier_uniq_H`).
* R `lem:elliptical-proj`, the distributional form: `elliptical_F1_cdf`, `elliptical_proj_law` (the CDF form and the
  properties of `F₁` are the certified Wave 23c `elliptical_proj`, `elliptical_F1`).
* B `prop:trimmed-band`(i): `trimmed_region`, `trimmed_content`, `trimmed_content_limit`, `trimmed_cubic`,
  `trimmed_cubic_compare`.
* B `cor:band-coverage-asymptotic` (i) with (iii): `band_coverage_asymptotic`.
* B `prop:rk-transfer-consistency`(ii): `rk_transfer_unif`.
* C `cor:coordinate-obstruction-empirical`, kernel-ratio step: `coord_kernel_ratio`.
* C `thm:neural-score-learning`, core: `neural_score_excess`, `neural_erm`.
* G `lem:decoupling`, flat case: `decoupling_tonelli` (`eq:decouple`), `decoupling_finite`, `decoupling_argmin`.
* T `cor:linearmodel-mult`(a): `explicitbridge_mult`, `explicitbridge_compare`, `explicitbridge_sA_lt`,
  `explicitbridge_radius`, `explicitbridge_better`.
* `prop:pays`: `pays_bracket`, `pays_isotropic`.
* SB: `field_ell`, `field_ell_root`, `field_local`.
* ICL `cor:consistency`: `icl_dev_vanishes`, `icl_consistency` (CONDITIONAL, see below).

Not covered (declared):
* `prop:calibrations` (b): Gaussianity of `ζ` (only `ζ ≠ 0` a.s. and, for continuity, `R ⫫ ζ`, `P(Π_Kζ = 0) = 0` are
  used); (c) "no simple closed form" (informal). `lem:app-references-Pl` (i), (iii) (a Gaussian on `H`; missing) and
  "consequently `μ_K ∈ 𝒫^ℓ(ℝ^K)`" (that is the certified Wave 1 `lem:app-pullback`).
* `lem:app-reflection`, `thm:prob-content` for `𝒫^ℓ` laws without second moments (McCann; A's `𝒫^ℓ` has them).
* `prop:trimmed-band` (ii) (finiteness of `h^{pop,δ'}`, local boundedness of the Brenier map; the band limits are
  the certified Wave 23a/23c `band_containment` at `A^{δ'}`), (iii) (the product quantile map of the matched model);
  the population coverage at `A^{δ'}` is the certified Wave 5a `pop_band_coverage` (any measurable `A`).
* `cor:band-coverage-asymptotic` (ii) (`p^♮` is the supremum of (i)), (iv) (support-function equivalences).
* `prop:rk-transfer-consistency` (i) (it is the certified Wave 22b `cond_transfer_consistency(_prob)` for one law),
  (ii) in outer probability, and the shell instance `S = Σ_{p₀,δ}`.
* `cor:coordinate-obstruction-empirical`: stability of the empirical entropic potentials (missing), uniformity of
  the `W₁` bound over the `1`-Lipschitz test class (Arzelà–Ascoli), the slow schedule (staircase).
* `thm:neural-score-learning`: that the energy divergence metrizes `W₁` uniformly on the response ball (missing),
  the uniform-in-`x` upgrade, the band edges.
* `lem:decoupling` for a general complete Riemannian `M` (Hopf–Rinow, measurable maximum theorem).
* `cor:linearmodel-mult` on a curve space (only one base point, `T` a point), the existence of a `c_g`-optimal coupling
  (the bound is stated for every one), and (b) (Hadamard comparison, missing).
* `prop:pays`: `d ≥ 2` (the certified `prop:envelope` is `d = 1`), and positivity below `s_crit ≈ 1.46√ε` (numerical,
  upper estimate; the paper itself flags it as uncertified).
* `cor:field-ell`: the `n^{-1/2}` rate (covariance concentration). `cor:field-local`: the `O_P` version and "no test can
  distinguish" (informal; the paper's `rem:local-scope` withdraws it).
* `cor:consistency`: the reduction `J_pool = R(μ_w) + λ_KL KL` and the pool approximation step (hypotheses), and
  `R⋆ ≤ R^{iid⋆}`.

Encodings (to be checked by the critic):
* Measurable-event convention throughout, except `band_coverage_asymptotic` (outer probabilities, no measurability
  hypothesis): probabilities of events are stated for measurable events (or as `∀ᵐ`);
  in-probability limits are Mathlib `TendstoInMeasure`; Bochner integrals only of integrable functions, `[0,∞]`
  lintegrals for `Ψ_t`, `J` (no junk `0`).
* `prop:calibrations`: `H` a separable Hilbert space with a Hilbert basis `e`, `Π_K = truncK e K`; `c_K(τ) = P(R r_K ≤ τ)`
  (`ballCdf`), `r_K = ‖Π_Kζ‖/‖ζ‖` (`ballRatio`; junk `0` only on the null set `ζ = 0`), `R ∼ unifRadius`; the cubic draw is
  `CubicDraw` (`⟨e_k, X⟩ = λ_kV_k` a.s., `V_k ∼ Unif[−½,½]`, `λ_k > 0`, `λ ∈ ℓ²`; `D_∞ > 0` follows), `D_K`, `D_∞`
  (`dK`, `dInf`) genuine square roots of summable sums.
* `lem:app-reflection`: `J : ℝ^K ≃ₗᵢ ℝ^K` (orthogonal); rank/quantile maps are Borel maps, a.e. cyclically monotone
  (Rockafellar: = gradients of convex functions), pushing the right laws.
* `thm:prob-content`: `μ_K = naiveLaw L` (`M_K = LᵀL ≻ 0`), `B_{K,M_K}(τ) = {‖u‖_M ≤ τ}`.
* `elliptical-proj`: `ξ ∼ N(0,1)` independent of a copy `W'` of `W` on any probability space.
* trimmed band: `(1 − δ')𝒰_K` the pointwise scaling (in `trimmed_cubic` written coordinatewise); `A_{K,p}` any convex
  compact subset of `𝒰_K` with `0` interior (the paper's region has these properties).
* band coverage: bands as `EReal` support functions (`InSuppBand`), population `popSupp` (essential supremum), fitted
  `fitSupp`; the fit realisation `Q̂_n(ω)` (no measurability in `ω`); `P` of the coverage events is Mathlib's outer
  measure (= the probability when measurable; continuity from below needs no measurability); `A_{K,p'}` arbitrary.
* rk transfer: one realisation on the event of `prop:app-potential-consistency` (deterministic); `modOn` the modulus.
* coordinate obstruction: `locLaw` (normalised kernel tilt), weak convergence tested on bounded continuous functions.
* neural: `eScore` with iterated integrals; the ERM objects abstract (`R`, `R̂_n`, classes `Θ_n`).
* decoupling: `𝒳 = L²(λ; E)` (`Lp E 2 λ`), `ev` as in the frozen Wave 19a `lem:evaluation` (existence certified there).
* explicitbridge: tangent coordinates `ℝ^K`, frame `ι : ℝ^K →ₗᵢ E` into `x^⊥` on the unit sphere of `E`, `μ_h` the
  product of uniforms scaled by `h a_k` (`cubeModel`), `A = diag(t)`, `c_g = ½ d(Exp_xι·, Exp_xι·)²`, `‖e_k‖_∞ = 1`.
* pays: `d = 1`, `h(x) = wx`, `λ = w²(1+t)`, `a = t/(1+t)`; `T^𝒩` (`certT`) in `EReal`, stated additively.
* field-ell: `γ` spherical (`O#γ = γ` for all orthogonal `O`), mean `0`, covariance `I`, finite second moment;
  `Cov(μ)^{-1/2}` any symmetric `W` with `W W Cov(μ) = I`. field-local: projections `R'_s`, `ν'` in `𝔐`,
  `W₂(R_s, R'_s) ≤ δ`, `Ŝ_{R'_s}` `L_s`-Lipschitz (see Critic notes).
* ICL: `R(μ_ŵ)` as a random variable `Rhat_j`, `A_j = inf_w R(μ_w)` on the pool sequence, `devBound` the `thm:joint`
  right side at `δ = 1/m`.

Critic notes:
* All 43 claims are proved in `Wave24d/Route{Pays,Field,Reflection,ProbContent,BridgeNum,Bridge,Calib,CalibCubic,
  CalibIndep,Transfer,EllProj,Trimmed,FieldEll,Neural,BandCov,Decoupling,RefsPl,RefsCubic,ICL,Coord}.lean` (only
  propext, Classical.choice, Quot.sound). Reused certified results: Wave 21b `envelope_iii_gap`, Wave 9b
  `field_bound_one`, Wave L3 `brenier_uniq_H_swap`, `brenier_exists_H`, `lipnull_of_ac`, `cmConc_map_swap`, Wave 8c
  `naive_calibration`, `naive_density`, Wave 16a `mapcost_mult`, Wave 7b `bilip_gen`, Wave 23c `EllSetting.prob_le`,
  Wave 19a `subgrad_conv_unif`, Wave 22b `continuousAt_gradient`, Wave 23a `band_containment`, Wave 20a
  `app_block_Pl_class`.
* CONDITIONAL: `icl_consistency` (the reduction to the pool objective, for all large `j`, and the approximation step,
  both proved in the paper's text, enter as hypotheses of exactly the printed strength; the pool is fixed on its
  almost-sure event, `P` is the law of the prompt sample given the pool, `inf_w R(μ_w)` is deterministic given it).
* Critic (2026-10-16): removed `calib_ball_reshape` (= Wave 8c `naive_norm`) and `prob_content_inverse` (= Wave L5
  `ghs_inverse_H` at `H = ℝ^K`); `band_coverage_asymptotic` no longer assumes measurable coverage events (outer
  probability; the measurability is not derivable for an arbitrary fit and index set `T`, and is not needed);
  `icl_consistency` assumes the oracle event only eventually (at `m_j = 0` the printed `δ = 1/m` is meaningless).
* Suspected manuscript issues (critic verdicts in brackets): (1) SB `cor:field-local`: moving `R_s` to its projection
  costs `O(δ_n)` only if the plug-in `Ŝ_{R_s}` (equivalently `T̂_s`) is Lipschitz; `def:standardisable`(iii) gives this
  for `Ŝ_ν⁻¹` only, so the hypothesis is missing (here `L_s`-Lipschitz is assumed); `dist(ν, 𝔐) ≤ δ_n` is not used.
  [CONFIRMED, the printed corollary is false: `d = 1`, `γ = ν = Unif[0,1]`, `𝔐 = {ν, μ_b}`, `μ_b` with density
  `|x|^{-1/2}/4` on `[−1,1]`, `S_{μ_b} = F_b`, `Ŝ_μ` = the `S` of the member identified by the sign of the sample
  (exact w.p. `→ 1`); `R_0 = μ_b`, `R_1 = μ_b(· − δ_n)`, both projecting onto `μ_b`. Then `T̂_0 = T̂_1 = F_b` w.p. `→ 1`
  and the gap is `W₂(Unif, F_b#R_1) ≍ δ_n^{3/4}` (comonotone coupling), `≫ r_n + δ_n` for `δ_n = n^{-1/2}`. Also
  implicit: the rate of `Ŝ_{R'_s}` computed from `R_s`-data; here the error term is stated on `R'_s` deterministically.] (2) SB `cor:field-ell`
  "a single affine orbit": the standardiser `Cov^{-1/2}(x − Eμ)` maps the orbit onto one `γ` only for a spherical
  generator (for a non-spherical `γ` it gives `O_A#γ`, `O_A` the polar factor of `A`); the title's "elliptical" supplies
  it. [Wording only: an elliptical family is by definition the orbit of a spherical generator.] (3) T `cor:linearmodel-mult`: "`a² ≥ 1/6`, i.e. `r_h ≤ 2.106`" is a sufficient condition, not an equivalence
  (threshold `≈ 2.10643`). [Cosmetic: the truncation is on the safe side.] (4) A `lem:app-reflection`: the quantile clause does not need `ν ∈ 𝒫^ℓ` (exchanged uniqueness
  needs the target `J#G ∈ 𝒫^ℓ`). [Not a defect: `ν ∈ 𝒫^ℓ` is what makes `Q_G` exist as a map; the
  claim takes `Q` as given.] (5) A/B `prop:calibrations`(b): the limit `c_K(τ) → τ` needs neither Gaussianity nor
  independence (it holds for every `τ ∈ [0,1]`, monotonically from above). [Not a defect: a strengthening;
  independence is used for continuity.]

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TauCeti Matrix
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace Pointwise

namespace StatFormal.Wave24d

open StatFormal.Wave21b (lamClass probOn gaussClass phiLin piB avgLogMgf)
open StatFormal.Wave9b (Standardises BigOP LipschitzWhp)
open StatFormal.OTFD.WaveL1 (IsCMMapAE Euc)
open StatFormal.OTFD.Wave1 (PellClass IsLipHyp lipHyp truncK)
open StatFormal.OTFD.Wave8c (naiveLaw mnorm mvec unifRadius sphereUnif)

/-! ### Robust equality JASA `prop:pays` -/

/-- The certificate `T^𝒩_s(h, λ) = λ r + λ ε Λ^𝒩_s(h, λ)` at radius `r` (`main.tex:349`), in `EReal`. -/
def certT (lam ε r : ℝ) (Λ : EReal) : EReal := ((lam * r : ℝ) : EReal) + ((lam * ε : ℝ) : EReal) * Λ

/-- `η_i = C_b ∫ π_b dν* / E_i`, `C_b = (1 + 2ab²/ε)^{1/2}`, `E_i = ∫ e^{φ(x_i,·)} dν*` (`prop:envelope`(iii)). -/
def etaB {n : ℕ} (K : Set ℝ) (x : Fin n → ℝ) (a b ε : ℝ) (νs : Measure ℝ) (i : Fin n) : ℝ :=
  (1 + 2 * a * b ^ 2 / ε) ^ (1 / 2 : ℝ) * (∫ y, piB K b y ∂νs) / (∫ y, Real.exp (phiLin a ε x i y) ∂νs)

/-! ### otfd T `cor:linearmodel-mult` (the small-dispersion model at one base point) -/

section Bridge
variable {K : ℕ}

/-- The model law `μ_h = 𝓛(h Σ_k a_k W_k e_k)`, `W_k` i.i.d. `Unif[−½, ½]`, in tangent coordinates `ℝ^K`. -/
def cubeModel (a : Fin K → ℝ) (h : ℝ) : Measure (Euc K) :=
  (Measure.pi fun _ : Fin K => volume.restrict (Icc (-(1 / 2) : ℝ) (1 / 2))).map
    fun w => WithLp.toLp 2 fun k => h * a k * w k

/-- The diagonal operator `A e_k = t_k e_k`. -/
def diagMap (t : Fin K → ℝ) (u : Euc K) : Euc K := WithLp.toLp 2 fun k => t k * u k

/-- `S_A = Σ_k (1 − t_k)² a_k²`. -/
def sA (a t : Fin K → ℝ) : ℝ := ∑ k, (1 - t k) ^ 2 * a k ^ 2

/-- `B_2 = ½ max{(Σ a_k²)^{1/2}, (Σ t_k² a_k²)^{1/2}}`. -/
def bTwo (a t : Fin K → ℝ) : ℝ := (1 / 2) * max √(∑ k, a k ^ 2) √(∑ k, t k ^ 2 * a k ^ 2)

/-- `B_∞ = ½ max{Σ a_k ‖e_k‖_∞, Σ t_k a_k ‖e_k‖_∞}` with `‖e_k‖_∞ = 1` (one base point, orthonormal frame). -/
def bInf (a t : Fin K → ℝ) : ℝ := (1 / 2) * max (∑ k, a k) (∑ k, t k * a k)

/-- The geodesic cost `c_g(u, v) = ½ d(Exp_x(ιu), Exp_x(ιv))²` on the unit sphere of `E`, with `ι` an isometric
frame of the tangent space at `x`. -/
def geoCost {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x : E) (ι : Euc K →ₗᵢ[ℝ] E)
    (p : Euc K × Euc K) : ℝ :=
  (1 / 2) * StatFormal.OTFD.Wave6b.sphDist (StatFormal.OTFD.Wave6b.sphExp x (ι p.1))
    (StatFormal.OTFD.Wave6b.sphExp x (ι p.2)) ^ 2

end Bridge

/-! ### otfd A/B `prop:calibrations` -/

section Calib
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The visible fraction of the ball-law direction, `‖Π_K ζ‖_{ℝ^K}/‖ζ‖_H`. -/
def ballRatio (e : HilbertBasis ℕ ℝ H) (K : ℕ) (x : H) : ℝ := ‖truncK e K x‖ / ‖x‖

/-- The ball law's radial CDF `c_K(τ) = P(R ‖Π_K ζ‖/‖ζ‖ ≤ τ)`. -/
def ballCdf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (R : Ω → ℝ) (ζ : Ω → H) (e : HilbertBasis ℕ ℝ H)
    (K : ℕ) (τ : ℝ) : ℝ :=
  P.real {ω | R ω * ballRatio e K (ζ ω) ≤ τ}

/-- `D_K = (Σ_{k<K} (λ_k/2)²)^{1/2}`. -/
def dK (lam : ℕ → ℝ) (K : ℕ) : ℝ := √(∑ k ∈ Finset.range K, (lam k / 2) ^ 2)

/-- `D_∞ = (Σ_k (λ_k/2)²)^{1/2}`. -/
def dInf (lam : ℕ → ℝ) : ℝ := √(∑' k, (lam k / 2) ^ 2)

/-- The cubic draw: `V_k` measurable with law `Unif[−½, ½]`, and `⟨e_k, X⟩ = λ_k V_k` for every `k`, a.s. -/
structure CubicDraw {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace H] (P : Measure Ω) (e : HilbertBasis ℕ ℝ H)
    (lam : ℕ → ℝ) (V : ℕ → Ω → ℝ) (X : Ω → H) : Prop where
  prob : IsProbabilityMeasure P
  pos : ∀ k, 0 < lam k
  sq : Summable fun k => lam k ^ 2
  meas_V : ∀ k, Measurable (V k)
  law_V : ∀ k, P.map (V k) = volume.restrict (Icc (-(1 / 2) : ℝ) (1 / 2))
  meas_X : Measurable X
  coord : ∀ᵐ ω ∂P, ∀ k, ⟪e k, X ω⟫_ℝ = lam k * V k ω

end Calib

/-! ### SB `cor:field-ell` -/

section FieldEll
variable {d : ℕ}

/-- The mean vector `E μ = (∫ x_i dμ)_i`. -/
def meanVec (μ : Measure (Euc d)) : Euc d := WithLp.toLp 2 fun i => ∫ x, x i ∂μ

/-- The covariance matrix `Cov(μ)_{ij} = ∫ (x_i − m_i)(x_j − m_j) dμ`. -/
def covMat (μ : Measure (Euc d)) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => ∫ x, (x i - meanVec μ i) * (x j - meanVec μ j) ∂μ

/-- `γ` is spherically symmetric: `O#γ = γ` for every orthogonal `O`. -/
def IsSpherical (γ : Measure (Euc d)) : Prop := ∀ O ∈ Matrix.orthogonalGroup (Fin d) ℝ, γ.map (mvec O) = γ

end FieldEll

/-! ### otfd G `lem:decoupling` (flat case) -/

/-- `Ψ_t(p) = ∫ ‖p − ev(x, t)‖² ν(dx)`, in `[0, ∞]`. -/
def psiDec {T E : Type*} [MeasurableSpace T] [NormedAddCommGroup E] {lam : Measure T}
    [MeasurableSpace (Lp E 2 lam)] (ν : Measure (Lp E 2 lam)) (ev : Lp E 2 lam × T → E) (t : T) (p : E) : ℝ≥0∞ :=
  ∫⁻ x, ‖p - ev (x, t)‖ₑ ^ 2 ∂ν

/-- The Fréchet objective `J(z) = ∫ D(z, x)² ν(dx)`, `D` the `L²(λ)` distance, in `[0, ∞]`. -/
def jDec {T E : Type*} [MeasurableSpace T] [NormedAddCommGroup E] {lam : Measure T}
    [MeasurableSpace (Lp E 2 lam)] (ν : Measure (Lp E 2 lam)) (z : Lp E 2 lam) : ℝ≥0∞ :=
  ∫⁻ x, ‖z - x‖ₑ ^ 2 ∂ν

/-- The decoupling setting (flat `M = E`, `𝒳 = L²(λ; E)`): `ν` a probability on `𝒳` with `∫ D(m, x)² dν < ∞` for a
base curve `m`, and `ev : 𝒳 × T → E` jointly measurable with `ev(x, ·)` a representative of `x` (`lem:evaluation`). -/
structure DecSetting {T E : Type*} [MeasurableSpace T] [NormedAddCommGroup E] {lam : Measure T}
    [MeasurableSpace (Lp E 2 lam)] [MeasurableSpace E] (ν : Measure (Lp E 2 lam)) (m : Lp E 2 lam)
    (ev : Lp E 2 lam × T → E) : Prop where
  prob : IsProbabilityMeasure ν
  mom : ∫⁻ x, ‖m - x‖ₑ ^ 2 ∂ν < ⊤
  meas_ev : Measurable ev
  rep : ∀ x : Lp E 2 lam, (fun t => ev (x, t)) =ᵐ[lam] ⇑x

/-! ### otfd B `cor:band-coverage-asymptotic` -/

/-- The curve `Y = 𝔪 + ⟨e(·), z⟩` lies in the band with edges `𝔪 − h(−e(t))`, `𝔪 + h(e(t))` (support function `h`
in `EReal`), at every `t`. -/
def InSuppBand {K : ℕ} {T : Type*} (h : Euc K → EReal) (mfrak : T → ℝ) (e : T → Euc K) (z : Euc K) : Prop :=
  ∀ t, (mfrak t : EReal) - h (-e t) ≤ ((mfrak t + ⟪e t, z⟫_ℝ : ℝ) : EReal) ∧
    ((mfrak t + ⟪e t, z⟫_ℝ : ℝ) : EReal) ≤ (mfrak t : EReal) + h (e t)

/-! ### otfd C `thm:neural-score-learning` -/

/-- The negatively oriented energy score `ES(ν, z) = E‖V − z‖ − ½E‖V − V'‖`, `V, V' ∼ ν` independent. -/
def eScore {F : Type*} [NormedAddCommGroup F] [MeasurableSpace F] (ν : Measure F) (z : F) : ℝ :=
  ∫ v, ‖v - z‖ ∂ν - (1 / 2) * ∫ v, ∫ v', ‖v - v'‖ ∂ν ∂ν

/-! ### otfd C `cor:coordinate-obstruction-empirical` -/

/-- The localized law `P^ν_{K,x}` tested on `g`: `∫ k(x, c) g(z) dP^{CZ} / ∫ k(x, c) dP^{CZ}` (for the empirical
measure this is `Σ_i w_i(x) g(Z_i)` with `w_i(x) ∝ k(x, C_i)`). -/
def locLaw {q K : ℕ} (k : Euc q → Euc q → ℝ) (Pm : Measure (Euc q × Euc K)) (x : Euc q) (g : Euc K → ℝ) : ℝ :=
  (∫ p, k x p.1 * g p.2 ∂Pm) / ∫ p, k x p.1 ∂Pm

/-! ### ICL `cor:consistency` -/

/-- The deviation bound of `thm:joint`:
`dev_{m,n,δ} = 4B_L√(2M log n/m) + 4λ_cov(K_max/K_min)√(2 log(2n)/m) + (B_L + λ_cov log(K_max/K_min))√(log(1/δ)/(2m))`. -/
def devBound (BL lcov Kmin Kmax : ℝ) (M n m : ℕ) (δ : ℝ) : ℝ :=
  4 * BL * √(2 * M * Real.log n / m) + 4 * lcov * (Kmax / Kmin) * √(2 * Real.log (2 * n) / m) +
    (BL + lcov * Real.log (Kmax / Kmin)) * √(Real.log (1 / δ) / (2 * m))

/-! ### otfd B `prop:rk-transfer-consistency` -/

/-- The modulus of continuity `ω(s) = sup{‖f a − f b‖ : a, b ∈ D, ‖a − b‖ ≤ s}` of `f` on `D` (genuine for `f`
continuous on a compact `D`). -/
def modOn {K : ℕ} (f : Euc K → Euc K) (D : Set (Euc K)) (s : ℝ) : ℝ :=
  sSup {d | ∃ a ∈ D, ∃ b ∈ D, ‖a - b‖ ≤ s ∧ d = ‖f a - f b‖}

namespace Claims

/-! #### Robust equality JASA `prop:pays` -/

/-- `prop:pays`, the bracket bound (`d = 1`, linear rule `h(x) = w x`, `λ = w²(1 + t)`, `t ≥ 0`, so `a = t/(1+t)`):
`T^{𝒩_b}_s(r̂ + ε τ̂_b) − T^{𝒫(K)}_s(r̂) ≥ λε(τ̂_b − ½ log(1 + 2ab²/ε) − n⁻¹ Σ_i log(1/(1 − η_i)))`, stated additively;
`ν*` attains `Λ^{𝒫(K)}` and every `η_i < 1`. -/
def pays_bracket : Prop :=
  ∀ (n : ℕ) (K : Set ℝ) (x : Fin n → ℝ) (w t b ε r τb : ℝ) (νs : Measure ℝ),
    0 < n → MeasurableSet K → 0 < volume K → w ≠ 0 → 0 ≤ t → 0 < b → 0 < ε → νs ∈ probOn K →
    lamClass (probOn K) (phiLin (t / (1 + t)) ε x) = ((avgLogMgf (phiLin (t / (1 + t)) ε x) νs : ℝ) : EReal) →
    (∀ i, etaB K x (t / (1 + t)) b ε νs i < 1) →
      certT (w ^ 2 * (1 + t)) ε r (lamClass (probOn K) (phiLin (t / (1 + t)) ε x)) +
          ((w ^ 2 * (1 + t) * ε * (τb - (1 / 2) * Real.log (1 + 2 * (t / (1 + t)) * b ^ 2 / ε) -
            (n : ℝ)⁻¹ * ∑ i, Real.log (1 / (1 - etaB K x (t / (1 + t)) b ε νs i))) : ℝ) : EReal) ≤
        certT (w ^ 2 * (1 + t)) ε (r + ε * τb) (lamClass (gaussClass K b) (phiLin (t / (1 + t)) ε x))

/-- `prop:pays`, the isotropic form (`a ≤ 1`): with `τ̂_b ≥ n⁻¹ Σ_i ϰ_i` (the per-box tax of the recorded points), the
bracket is at least `n⁻¹ Σ_i [ϰ_i − ½ log(1 + 2b²/ε)] − n⁻¹ Σ_i log(1/(1 − η_i))`. -/
def pays_isotropic : Prop :=
  ∀ (n : ℕ) (K : Set ℝ) (x : Fin n → ℝ) (w t b ε r τb : ℝ) (κ : Fin n → ℝ) (νs : Measure ℝ),
    0 < n → MeasurableSet K → 0 < volume K → w ≠ 0 → 0 ≤ t → 0 < b → 0 < ε → νs ∈ probOn K →
    lamClass (probOn K) (phiLin (t / (1 + t)) ε x) = ((avgLogMgf (phiLin (t / (1 + t)) ε x) νs : ℝ) : EReal) →
    (∀ i, etaB K x (t / (1 + t)) b ε νs i < 1) → (n : ℝ)⁻¹ * ∑ i, κ i ≤ τb →
      certT (w ^ 2 * (1 + t)) ε r (lamClass (probOn K) (phiLin (t / (1 + t)) ε x)) +
          ((w ^ 2 * (1 + t) * ε * ((n : ℝ)⁻¹ * ∑ i, (κ i - (1 / 2) * Real.log (1 + 2 * b ^ 2 / ε)) -
            (n : ℝ)⁻¹ * ∑ i, Real.log (1 / (1 - etaB K x (t / (1 + t)) b ε νs i))) : ℝ) : EReal) ≤
        certT (w ^ 2 * (1 + t)) ε (r + ε * τb) (lamClass (gaussClass K b) (phiLin (t / (1 + t)) ε x))

/-! #### SB `cor:field-local` -/

/-- `cor:field-local`, deterministic bound: `R'_s`, `ν'` are members of `𝔐` (standardisable onto `γ`) with
`W₂(R_s, R'_s) ≤ δ`; the repair is built from the projections, `T̂_s = Ŝ_{ν'}⁻¹ ∘ Ŝ_{R'_s}`, with `Ŝ_{ν'}⁻¹`
`L`-Lipschitz and `Ŝ_{R'_s}` `L_s`-Lipschitz. Then the parity gap of the plug-in applied to the true `R_s` is at most
`Σ_s (L L_s δ + L‖Ŝ_{R'_s} − S_{R'_s}‖_{L²(R'_s)} + ‖Ŝ_{ν'}⁻¹ − S_{ν'}⁻¹‖_{L²(γ)})`, i.e. `O(r_n + δ_n)`. -/
def field_local : Prop :=
  ∀ (d : ℕ) (R R' : Fin 2 → Measure (EuclideanSpace ℝ (Fin d))) (ν' γ : Measure (EuclideanSpace ℝ (Fin d)))
    (S Sinv Shat : Fin 2 → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (Sν Sνinv Sνinvhat : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L : ℝ≥0) (Ls : Fin 2 → ℝ≥0)
    (δ : ℝ≥0∞),
    (∀ s, IsProbabilityMeasure (R s)) → (∀ s, IsProbabilityMeasure (R' s)) → IsProbabilityMeasure ν' →
    IsProbabilityMeasure γ →
    (∀ s, Standardises (R' s) γ (S s) (Sinv s)) → Standardises ν' γ Sν Sνinv →
    (∀ s, Measurable (Shat s)) → (∀ s, LipschitzWith (Ls s) (Shat s)) → Measurable Sνinvhat →
    LipschitzWith L Sνinvhat → (∀ s, wassersteinEDist 2 (R s) (R' s) ≤ δ) →
      wassersteinEDist 2 ((R 0).map (Sνinvhat ∘ Shat 0)) ((R 1).map (Sνinvhat ∘ Shat 1)) ≤
        ∑ s, ((L : ℝ≥0∞) * Ls s * δ + L * eLpNorm (fun x => Shat s x - S s x) 2 (R' s) +
          eLpNorm (fun z => Sνinvhat z - Sνinv z) 2 γ)

/-! #### otfd A `lem:app-reflection` -/

/-- `lem:app-reflection`, rank maps: `G ∈ 𝒫^ℓ(ℝ^K)`, `ν` a boundedly supported probability, `J` orthogonal with
`J#ν = ν`, `F` a rank map of `G` (Borel, `G`-a.e. cyclically monotone, `F#G = ν`). Then `J#G ∈ 𝒫^ℓ(ℝ^K)`,
`J ∘ F ∘ Jᵀ` is a rank map of `J#G`, and every rank map of `J#G` equals it `J#G`-a.e. -/
def app_reflection_rank : Prop :=
  ∀ (K : ℕ) (G ν : Measure (Euc K)) (J : Euc K ≃ₗᵢ[ℝ] Euc K) (M : ℝ) (F : Euc K → Euc K),
    PellClass G → IsProbabilityMeasure ν → ν (Metric.closedBall 0 M)ᶜ = 0 → ν.map J = ν →
    Measurable F → G.map F = ν → IsCMMapAE G F →
      PellClass (G.map J) ∧ Measurable (J ∘ F ∘ J.symm) ∧ (G.map J).map (J ∘ F ∘ J.symm) = ν ∧
        IsCMMapAE (G.map J) (J ∘ F ∘ J.symm) ∧
        ∀ F' : Euc K → Euc K, Measurable F' → (G.map J).map F' = ν → IsCMMapAE (G.map J) F' →
          F' =ᵐ[G.map J] (J ∘ F ∘ J.symm)

/-- `lem:app-reflection`, quantile maps: with `Q` a quantile map of `G` (Borel, `ν`-a.e. cyclically monotone,
`Q#ν = G`), `J ∘ Q ∘ Jᵀ` is a quantile map of `J#G` and every quantile map of `J#G` equals it `ν`-a.e. The paper
assumes `ν ∈ 𝒫^ℓ(ℝ^K)`; uniqueness in the exchanged form (target `J#G` null on Lipschitz hypersurfaces) needs only
`G ∈ 𝒫^ℓ(ℝ^K)` (generalisation). -/
def app_reflection_quantile : Prop :=
  ∀ (K : ℕ) (G ν : Measure (Euc K)) (J : Euc K ≃ₗᵢ[ℝ] Euc K) (M : ℝ) (Q : Euc K → Euc K),
    PellClass G → IsProbabilityMeasure ν → ν (Metric.closedBall 0 M)ᶜ = 0 → ν.map J = ν →
    Measurable Q → ν.map Q = G → IsCMMapAE ν Q →
      Measurable (J ∘ Q ∘ J.symm) ∧ ν.map (J ∘ Q ∘ J.symm) = G.map J ∧ IsCMMapAE ν (J ∘ Q ∘ J.symm) ∧
        ∀ Q' : Euc K → Euc K, Measurable Q' → ν.map Q' = G.map J → IsCMMapAE ν Q' →
          Q' =ᵐ[ν] (J ∘ Q ∘ J.symm)

/-! #### otfd A `thm:prob-content` (naive spherical reference) -/

/-- The naive spherical reference `μ_K` (`M_K = LᵀL` positive definite) is in `𝒫^ℓ(ℝ^K)`: a probability with a
finite second moment, null on every Lipschitz hypersurface (it is absolutely continuous). -/
def prob_content_naive_pell : Prop :=
  ∀ (K : ℕ) (M L : Matrix (Fin K) (Fin K) ℝ), 1 ≤ K → M.PosDef → Lᵀ * L = M → PellClass (naiveLaw L)

/-- Existence (GHS Thm. 2.4/`thm:app-ghs-existence` in `ℝ^K`, with `𝒫^ℓ`'s second moment): for `P_K ∈ 𝒫^ℓ(ℝ^K)` there
are a monotone (`P_K`-a.e. cyclically monotone, Borel) map `F_{+,K}` with `F_{+,K}#P_K = μ_K` and a monotone
(`μ_K`-a.e. cyclically monotone, Borel) map `Q_{+,K}` with `Q_{+,K}#μ_K = P_K`. -/
def prob_content_naive_exists : Prop :=
  ∀ (K : ℕ) (M L : Matrix (Fin K) (Fin K) ℝ) (P : Measure (Euc K)), 1 ≤ K → M.PosDef → Lᵀ * L = M → PellClass P →
    (∃ F : Euc K → Euc K, Measurable F ∧ P.map F = naiveLaw L ∧ IsCMMapAE P F) ∧
      ∃ Q : Euc K → Euc K, Measurable Q ∧ (naiveLaw L).map Q = P ∧ IsCMMapAE (naiveLaw L) Q

/-- The content: for every Borel `F` pushing `P_K` to `μ_K`, the preimage-form region
`𝒞_K(τ) = F⁻¹(B_{K,M_K}(τ))`, `B_{K,M_K}(τ) = {u : ‖u‖_{M_K} ≤ τ}`, has `P_K(𝒞_K(τ)) = μ_K(B_{K,M_K}(τ)) = τ` for
every `τ ∈ (0,1)` (any probability `P_K`; monotonicity of `F` is not used). -/
def prob_content_naive : Prop :=
  ∀ (K : ℕ) (M L : Matrix (Fin K) (Fin K) ℝ) (P : Measure (Euc K)) (F : Euc K → Euc K),
    1 ≤ K → M.PosDef → Lᵀ * L = M → Measurable F → P.map F = naiveLaw L →
      ∀ τ ∈ Ioo (0 : ℝ) 1,
        P (F ⁻¹' {u | mnorm M u ≤ τ}) = naiveLaw L {u | mnorm M u ≤ τ} ∧
          P (F ⁻¹' {u | mnorm M u ≤ τ}) = ENNReal.ofReal τ

/-! #### otfd T `eq:explicitbridge-mult` -/

/-- `cor:linearmodel-mult`(a), one base point: on the unit sphere of `E` with `r_h = hB_∞ < π`, every optimal
coupling `π_{g,h}` of `μ_h` and `ν_h = A#μ_h` for the geodesic cost satisfies
`∫‖v − Au‖² dπ_{g,h} ≤ (t₊/12)(a_{r_h}^{−2} − 1) h² S_A`, `a_r = sin r / r`. -/
def explicitbridge_mult : Prop :=
  ∀ (K : ℕ) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x : E) (ι : Euc K →ₗᵢ[ℝ] E)
    (a t : Fin K → ℝ) (h tp : ℝ) (π : Measure (Euc K × Euc K)),
    1 ≤ K → ‖x‖ = 1 → (∀ u, ⟪x, ι u⟫_ℝ = 0) → (∀ k, 0 < a k) → (∀ k, 0 < t k ∧ t k ≤ tp) → 0 < h →
    h * bInf a t < Real.pi →
    StatFormal.Wave16a.IsOptPlan (cubeModel a h) ((cubeModel a h).map (diagMap t)) (geoCost x ι) π →
      Integrable (fun p : Euc K × Euc K => ‖p.2 - diagMap t p.1‖ ^ 2) π ∧
        ∫ p, ‖p.2 - diagMap t p.1‖ ^ 2 ∂π ≤
          tp / 12 * ((Real.sin (h * bInf a t) / (h * bInf a t))⁻¹ ^ 2 - 1) * h ^ 2 * sA a t

/-- `cor:linearmodel-mult`(a), the comparison with `eq:explicitbridge`: for `0 < a_r < 1`, the multiplicative bound is
below `4t₊h²B₂²(1 − a_r²)` exactly when `S_A < 48 a_r² B₂²`. -/
def explicitbridge_compare : Prop :=
  ∀ (K : ℕ) (a t : Fin K → ℝ) (h tp ar : ℝ), 0 < h → 0 < tp → 0 < ar → ar < 1 →
    (tp / 12 * (ar⁻¹ ^ 2 - 1) * h ^ 2 * sA a t < 4 * tp * h ^ 2 * bTwo a t ^ 2 * (1 - ar ^ 2) ↔
      sA a t < 48 * ar ^ 2 * bTwo a t ^ 2)

/-- `cor:linearmodel-mult`(a): `S_A < 8B₂²` for every `A` in the model (`(1 − t)² < 1 + t²` for `t > 0`), so
`a_r² ≥ 1/6` makes the multiplicative bound the smaller one. -/
def explicitbridge_sA_lt : Prop :=
  ∀ (K : ℕ) (a t : Fin K → ℝ), 1 ≤ K → (∀ k, 0 < a k) → (∀ k, 0 < t k) → sA a t < 8 * bTwo a t ^ 2

/-- `cor:linearmodel-mult`(a): `r ≤ 2.106` gives `a_r² = (sin r / r)² ≥ 1/6` (sufficient direction of the printed
"i.e."; the exact threshold is the root `≈ 2.1064`). -/
def explicitbridge_radius : Prop :=
  ∀ r : ℝ, 0 < r → r ≤ 2.106 → 1 / 6 ≤ (Real.sin r / r) ^ 2

/-- `cor:linearmodel-mult`(a), assembled: in the model with `0 < r_h ≤ 2.106`, the multiplicative bound is strictly
below the bound of `eq:explicitbridge`, for every admissible `A`. -/
def explicitbridge_better : Prop :=
  ∀ (K : ℕ) (a t : Fin K → ℝ) (h tp : ℝ), 1 ≤ K → (∀ k, 0 < a k) → (∀ k, 0 < t k ∧ t k ≤ tp) → 0 < h →
    h * bInf a t ≤ 2.106 →
      tp / 12 * ((Real.sin (h * bInf a t) / (h * bInf a t))⁻¹ ^ 2 - 1) * h ^ 2 * sA a t <
        4 * tp * h ^ 2 * bTwo a t ^ 2 * (1 - (Real.sin (h * bInf a t) / (h * bInf a t)) ^ 2)

/-! #### otfd A/B `prop:calibrations` -/

/-- (b) `c_K(τ) → τ` for every `τ ∈ [0,1]` as `K → ∞`, for any random direction `ζ ≠ 0` a.s. (Gaussian in the paper;
generalisation) and `R ∼ Unif(0,1)` (no independence needed for the limit). -/
def calib_ball_limit : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (e : HilbertBasis ℕ ℝ H) (ζ : Ω → H) (R : Ω → ℝ),
    Measurable ζ → Measurable R → P.map R = unifRadius → (∀ᵐ ω ∂P, ζ ω ≠ 0) →
      ∀ τ ∈ Icc (0 : ℝ) 1, Tendsto (fun K => ballCdf P R ζ e K τ) atTop (𝓝 τ)

/-- (b), last paragraph: with `R` independent of `ζ` and `P(Π_K ζ = 0) = 0`, `c_K` is a continuous CDF on `[0,1]`:
continuous, `c_K(0) = 0`, `c_K(1) = 1`. -/
def calib_ball_cont : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (e : HilbertBasis ℕ ℝ H) (ζ : Ω → H) (R : Ω → ℝ) (K : ℕ),
    Measurable ζ → Measurable R → P.map R = unifRadius → IndepFun R ζ P → P {ω | truncK e K (ζ ω) = 0} = 0 →
      Continuous (ballCdf P R ζ e K) ∧ ballCdf P R ζ e K 0 = 0 ∧ ballCdf P R ζ e K 1 = 1

/-- (c) For `U = Π_K X ∼ μ_K`, `ρ_box(U) = ‖U‖/D_∞ ∈ [0, D_K/D_∞]` a.s., `D_K/D_∞ < 1`, and on the box
`{|u_k| ≤ λ_k/2}` the value `‖u‖ = D_K` is attained exactly at the corners `|u_k| = λ_k/2`. -/
def calib_cubic_range : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (e : HilbertBasis ℕ ℝ H) (lam : ℕ → ℝ) (V : ℕ → Ω → ℝ) (X : Ω → H) (K : ℕ),
    CubicDraw P e lam V X →
      (∀ᵐ ω ∂P, ‖truncK e K (X ω)‖ / dInf lam ∈ Icc 0 (dK lam K / dInf lam)) ∧ dK lam K / dInf lam < 1 ∧
        ∀ u : Euc K, (∀ k : Fin K, |u k| ≤ lam k / 2) → (‖u‖ = dK lam K ↔ ∀ k : Fin K, |u k| = lam k / 2)

/-- (c) `ρ_box^{(K)}(Π_K X) → ‖X‖/D_∞` almost surely and in `L²`, and the limit is `< 1` almost surely. -/
def calib_cubic_limit : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (e : HilbertBasis ℕ ℝ H) (lam : ℕ → ℝ) (V : ℕ → Ω → ℝ) (X : Ω → H),
    CubicDraw P e lam V X →
      (∀ᵐ ω ∂P, Tendsto (fun K => ‖truncK e K (X ω)‖ / dInf lam) atTop (𝓝 (‖X ω‖ / dInf lam))) ∧
        Tendsto (fun K => ∫ ω, (‖truncK e K (X ω)‖ / dInf lam - ‖X ω‖ / dInf lam) ^ 2 ∂P) atTop (𝓝 0) ∧
        ∀ᵐ ω ∂P, ‖X ω‖ / dInf lam < 1

/-- (c) The limit is nondegenerate: with the `V_k` independent, `Var(ρ_box^{(∞)}(X)) > 0`. -/
def calib_cubic_nondeg : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (e : HilbertBasis ℕ ℝ H) (lam : ℕ → ℝ) (V : ℕ → Ω → ℝ) (X : Ω → H),
    CubicDraw P e lam V X → iIndepFun V P → 0 < Var[fun ω => ‖X ω‖ / dInf lam; P]

/-- (c) `c_K(τ) → c_∞(τ)` at every continuity point `τ` of `c_∞` (`P(ρ_∞ = τ) = 0`). -/
def calib_cubic_cdf : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (e : HilbertBasis ℕ ℝ H) (lam : ℕ → ℝ) (V : ℕ → Ω → ℝ) (X : Ω → H) (τ : ℝ),
    CubicDraw P e lam V X → P {ω | ‖X ω‖ / dInf lam = τ} = 0 →
      Tendsto (fun K => P.real {ω | ‖truncK e K (X ω)‖ / dInf lam ≤ τ}) atTop
        (𝓝 (P.real {ω | ‖X ω‖ / dInf lam ≤ τ}))

/-- (c), last paragraph: with independent `V_k` and `K ≥ 1`, `c_K(τ) = P(ρ_box^{(K)}(Π_K X) ≤ τ)` is continuous with
`c_K(0) = 0`, `c_K(1) = 1`. -/
def calib_cubic_cont : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (e : HilbertBasis ℕ ℝ H) (lam : ℕ → ℝ) (V : ℕ → Ω → ℝ) (X : Ω → H) (K : ℕ),
    CubicDraw P e lam V X → iIndepFun V P → 1 ≤ K →
      Continuous (fun τ => P.real {ω | ‖truncK e K (X ω)‖ / dInf lam ≤ τ}) ∧
        P.real {ω | ‖truncK e K (X ω)‖ / dInf lam ≤ 0} = 0 ∧ P.real {ω | ‖truncK e K (X ω)‖ / dInf lam ≤ 1} = 1

/-! #### otfd B `prop:rk-transfer-consistency` -/

/-- `prop:rk-transfer-consistency`(ii), on the probability-one event of `prop:app-potential-consistency` (the fitted
potentials `g_n` convex on `C = int 𝒰_K` converge to `χ_B` uniformly on compacts; `Q̂_n(u) ∈ ∂g_n(u)`; the
population map is `Q_B = ∇χ_B` on the open `O ⊆ C` where `χ_B` is differentiable; `F_A(𝒵) ⊆ S`, `S ⊆ O` compact):
there is `r > 0` with `S^r ⊆ O` such that (1) whenever `s ≥ sup_𝒵 ‖F̂_A − F_A‖` and `s ≤ r`, and `Δ` bounds
`‖Q̂_n − ∇χ_B‖` on `S^r`, `sup_𝒵 ‖T̂ − T‖ ≤ Δ + ω(s)` (`ω` the modulus of `∇χ_B` on `S^r`); (2) `Δ_n → 0`;
(3) hence `sup_𝒵 ‖T̂ − T‖ → 0` whenever `s_n → 0`. -/
def rk_transfer_unif : Prop :=
  ∀ (K : ℕ) (C O S 𝒵 : Set (Euc K)) (χ : Euc K → ℝ) (g : ℕ → Euc K → ℝ) (Qh : ℕ → Euc K → Euc K)
    (F : Euc K → Euc K) (Fh : ℕ → Euc K → Euc K),
    IsOpen C → Convex ℝ C → (∀ n, ConvexOn ℝ C (g n)) → ConvexOn ℝ C χ →
    (∀ S' ⊆ C, IsCompact S' → TendstoUniformlyOn g χ atTop S') →
    (∀ n, ∀ u ∈ C, Qh n u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (StatFormal.OTFD.Wave19a.extTop C (g n)) u) →
    IsOpen O → O ⊆ C → (∀ w ∈ O, DifferentiableAt ℝ χ w) → S ⊆ O → IsCompact S → (∀ z ∈ 𝒵, F z ∈ S) →
      ∃ r : ℝ, 0 < r ∧ Metric.cthickening r S ⊆ O ∧
        (∀ (n : ℕ) (s Δ : ℝ), s ≤ r → (∀ z ∈ 𝒵, ‖Fh n z - F z‖ ≤ s) →
          (∀ w ∈ Metric.cthickening r S, ‖Qh n w - gradient χ w‖ ≤ Δ) →
            ∀ z ∈ 𝒵, ‖Qh n (Fh n z) - gradient χ (F z)‖ ≤ Δ + modOn (gradient χ) (Metric.cthickening r S) s) ∧
        (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ w ∈ Metric.cthickening r S, ‖Qh n w - gradient χ w‖ ≤ ε) ∧
        ((∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ z ∈ 𝒵, ‖Fh n z - F z‖ ≤ ε) →
          ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ z ∈ 𝒵, ‖Qh n (Fh n z) - gradient χ (F z)‖ ≤ ε)

/-! #### otfd R `lem:elliptical-proj` (the distributional form) -/

/-- `lem:elliptical-proj`, definition of `F₁`: for any `ξ ∼ N(0,1)` independent of a copy `W'` of `W`, the frozen
`F₁(t) = E Φ(t/√W)` (Wave 23c `ellF1`) is the distribution function of `√W' ξ`. -/
def elliptical_F1_cdf : Prop :=
  ∀ (Ω H : Type) [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
    [BorelSpace H] (Pr : Measure Ω) (G : Ω → H) (W : Ω → ℝ), StatFormal.Wave23c.EllSetting Pr G W →
    ∀ (Ω' : Type) [MeasurableSpace Ω'] (Pr' : Measure Ω') [IsProbabilityMeasure Pr'] (W' ξ : Ω' → ℝ),
      Measurable W' → Measurable ξ → IndepFun W' ξ Pr' → Pr'.map W' = Pr.map W → Pr'.map ξ = gaussianReal 0 1 →
        ∀ t, cdf (Pr'.map fun ω => Real.sqrt (W' ω) * ξ ω) t = StatFormal.Wave23c.ellF1 Pr W t

/-- `lem:elliptical-proj`, the display: `⟨v, X⟩ =ᵈ σ_v √W ξ` for `v ≠ 0`, `σ_v = ‖Σ^{1/2}v‖` (`projSd`), with `ξ ∼ N(0,1)`
independent of a copy `W'` of `W`. -/
def elliptical_proj_law : Prop :=
  ∀ (Ω H : Type) [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
    [BorelSpace H] (Pr : Measure Ω) (G : Ω → H) (W : Ω → ℝ), StatFormal.Wave23c.EllSetting Pr G W →
    ∀ v : H, v ≠ 0 →
    ∀ (Ω' : Type) [MeasurableSpace Ω'] (Pr' : Measure Ω') [IsProbabilityMeasure Pr'] (W' ξ : Ω' → ℝ),
      Measurable W' → Measurable ξ → IndepFun W' ξ Pr' → Pr'.map W' = Pr.map W → Pr'.map ξ = gaussianReal 0 1 →
        (StatFormal.Wave23c.ellLaw Pr G W).map (fun z => ⟪v, z⟫_ℝ) =
          Pr'.map fun ω => StatFormal.Wave23c.projSd Pr G v * (Real.sqrt (W' ω) * ξ ω)

/-! #### otfd B `prop:trimmed-band` (i) -/

/-- (i), the region: for a convex compact support `𝒰_K` with `0` interior and a convex compact level region
`A_{K,p} ⊆ 𝒰_K` containing a neighbourhood of `0`, the trimmed region `A^{δ'} = A_{K,p} ∩ (1 − δ')𝒰_K` is convex,
compact, contained in `int 𝒰_K`, and contains a neighbourhood of `0`. -/
def trimmed_region : Prop :=
  ∀ (K : ℕ) (U A : Set (Euc K)) (δ : ℝ), Convex ℝ U → IsCompact U → (0 : Euc K) ∈ interior U →
    A ⊆ U → Convex ℝ A → IsCompact A → (0 : Euc K) ∈ interior A → 0 < δ → δ < 1 →
      Convex ℝ (A ∩ (1 - δ) • U) ∧ IsCompact (A ∩ (1 - δ) • U) ∧ A ∩ (1 - δ) • U ⊆ interior U ∧
        (0 : Euc K) ∈ interior (A ∩ (1 - δ) • U)

/-- (i), the content: `μ_K(A^{δ'}) = p − μ_K(A_{K,p} \ A^{δ'}) ≥ p − μ_K(𝒰_K \ (1 − δ')𝒰_K)` when `μ_K(A_{K,p}) = p`,
and for `μ_K ≪ Leb` the right side tends to `p` as `δ' ↓ 0`. -/
def trimmed_content : Prop :=
  ∀ (K : ℕ) (μ : Measure (Euc K)) [IsFiniteMeasure μ] (U A : Set (Euc K)) (p δ : ℝ),
    MeasurableSet U → MeasurableSet A → A ⊆ U → μ.real A = p → δ < 1 →
      μ.real (A ∩ (1 - δ) • U) = p - μ.real (A \ (1 - δ) • U) ∧
        p - μ.real (U \ (1 - δ) • U) ≤ μ.real (A ∩ (1 - δ) • U)

/-- (i), the limit: for `μ_K ≪ Leb` and `𝒰_K` convex compact with `0` interior, `μ_K(𝒰_K \ (1 − δ')𝒰_K) → 0` as
`δ' ↓ 0`, so the generic lower bound tends to `p`. -/
def trimmed_content_limit : Prop :=
  ∀ (K : ℕ) (μ : Measure (Euc K)) [IsFiniteMeasure μ] (U : Set (Euc K)),
    μ ≪ volume → Convex ℝ U → IsCompact U → (0 : Euc K) ∈ interior U →
      Tendsto (fun δ : ℝ => μ.real (U \ (1 - δ) • U)) (𝓝[>] (0 : ℝ)) (𝓝 0)

/-- (i), the cubic law (frozen `cubicLaw a`, half-widths `a_k > 0`, box `𝒰 = {|u_k| ≤ a_k}`, region
`A = 𝒰 ∩ {ρ_box ≤ τ}`): `μ(A ∩ (1 − δ')𝒰) ≥ (1 − δ')^K μ(A)`, with `(1 − δ')𝒰 = {|u_k| ≤ (1 − δ')a_k}` written
coordinatewise. -/
def trimmed_cubic : Prop :=
  ∀ (N : ℕ) (a : Fin N → ℝ) (Dinf τ δ : ℝ), (∀ k, 0 < a k) → 0 < Dinf → 0 < δ → δ < 1 →
    ENNReal.ofReal ((1 - δ) ^ N) *
        StatFormal.OTFD.Wave8c.cubicLaw a {u | (∀ k, |u k| ≤ a k) ∧ StatFormal.OTFD.Wave8c.rhoBox Dinf u ≤ τ} ≤
      StatFormal.OTFD.Wave8c.cubicLaw a
        {u | ((∀ k, |u k| ≤ a k) ∧ StatFormal.OTFD.Wave8c.rhoBox Dinf u ≤ τ) ∧ ∀ k, |u k| ≤ (1 - δ) * a k}

/-- (i), the elementary comparisons: `(1 − δ')^K p ≥ (1 − Kδ')p` and `(1 − δ')^K p ≥ p − [1 − (1 − δ')^K]` for
`p ∈ [0,1]`, `δ' ∈ (0,1)`. -/
def trimmed_cubic_compare : Prop :=
  ∀ (K : ℕ) (p δ : ℝ), 0 ≤ p → p ≤ 1 → 0 < δ → δ < 1 →
    (1 - K * δ) * p ≤ (1 - δ) ^ K * p ∧ p - (1 - (1 - δ) ^ K) ≤ (1 - δ) ^ K * p

/-! #### SB `cor:field-ell` -/

/-- `cor:field-ell`: the affine orbit `𝔐 = {(z ↦ Az + b)#γ : A invertible}` of a spherical generator `γ` (mean `0`,
covariance `I`, finite second moment) has `E μ = b`, `Cov(μ) = AAᵀ`, and `S_μ(x) = Cov(μ)^{-1/2}(x − Eμ)` standardises
`μ` onto `γ` exactly (`def:standardisable`(i), frozen `Standardises`), for every symmetric `W` with
`W W Cov(μ) = I` (the positive definite root `Cov(μ)^{-1/2}` is one, `field_ell_root`). -/
def field_ell : Prop :=
  ∀ (d : ℕ) (γ : Measure (Euc d)) [IsProbabilityMeasure γ], IsSpherical γ → ∫⁻ x, ‖x‖ₑ ^ 2 ∂γ < ⊤ →
    meanVec γ = 0 → covMat γ = 1 →
    ∀ (A : Matrix (Fin d) (Fin d) ℝ) (b : Euc d), A.det ≠ 0 →
      meanVec (γ.map fun z => mvec A z + b) = b ∧ covMat (γ.map fun z => mvec A z + b) = A * Aᵀ ∧
        ∀ W : Matrix (Fin d) (Fin d) ℝ, Wᵀ = W → W * W * covMat (γ.map fun z => mvec A z + b) = 1 →
          Standardises (γ.map fun z => mvec A z + b) γ
            (fun x => mvec W (x - meanVec (γ.map fun z => mvec A z + b)))
            (fun z => mvec W⁻¹ z + meanVec (γ.map fun z => mvec A z + b))

/-- `Cov(μ)^{-1/2}` exists: every positive definite `C` has a symmetric positive definite `W` with `W W C = I`. -/
def field_ell_root : Prop :=
  ∀ (d : ℕ) (C : Matrix (Fin d) (Fin d) ℝ), C.PosDef → ∃ W : Matrix (Fin d) (Fin d) ℝ, Wᵀ = W ∧ W.PosDef ∧ W * W * C = 1

/-! #### otfd C `thm:neural-score-learning` -/

/-- The excess energy score is half the energy divergence: for laws `ν, P` with finite first moments and `Z ∼ P`,
`E ES(ν, Z) − E ES(P, Z) = ½ 𝒟_E(ν, P)` (the frozen `energyD`); applied at each covariate value `x` this is the
conditional excess `𝒟_E(ν_{ϑ,x}, P_{K,x})/2`. -/
def neural_score_excess : Prop :=
  ∀ (F : Type) [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    (ν P : Measure F) [IsProbabilityMeasure ν] [IsProbabilityMeasure P],
    Integrable (fun v => ‖v‖) ν → Integrable (fun z => ‖z‖) P →
      ∫ z, eScore ν z ∂P - ∫ z, eScore P z ∂P = (1 / 2) * StatFormal.OTFD.Wave22a.energyD ν P

/-- The ERM decomposition behind `thm:neural-score-learning`: with (i) representation error `→ 0` (for every
`ε > 0`, eventually some `ϑ ∈ Θ_n` has `R(ϑ) ≤ R⋆ + ε`), (ii) the uniform deviation `sup_{Θ_n}|R̂_n − R|` bounded by
`dev_n → 0` in probability, and (iii) the optimisation error `opt_n → 0` in probability, the excess risk
`R(ϑ̂_n) − R⋆` tends to `0` in probability (`R⋆ ≤ R` on every class: the proper score's minimum). -/
def neural_erm : Prop :=
  ∀ (Θ Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] (Θn : ℕ → Set Θ) (R : Θ → ℝ)
    (Rstar : ℝ) (Rhat : ℕ → Ω → Θ → ℝ) (θhat : ℕ → Ω → Θ) (dev opt : ℕ → Ω → ℝ),
    (∀ θ, Rstar ≤ R θ) → (∀ n ω, θhat n ω ∈ Θn n) →
    (∀ n ω, ∀ θ ∈ Θn n, |Rhat n ω θ - R θ| ≤ dev n ω) →
    (∀ n ω, ∀ θ ∈ Θn n, Rhat n ω (θhat n ω) ≤ Rhat n ω θ + opt n ω) →
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∃ θ ∈ Θn n, R θ ≤ Rstar + ε) →
    TendstoInMeasure P dev atTop (fun _ => 0) → TendstoInMeasure P opt atTop (fun _ => 0) →
      TendstoInMeasure P (fun n ω => R (θhat n ω) - Rstar) atTop (fun _ => 0)

/-! #### otfd B `cor:band-coverage-asymptotic` -/

/-- `cor:band-coverage-asymptotic`(i) with (iii): under the hypotheses of `thm:band-containment` at level `p` (frozen
Wave 23a: `A = A_{K,p}` measurable, `Q` of bounded essential range on `A`, and, almost surely over the fit,
`Q̂_n → Q` `μ_K|A`-a.e.), let the normalised nesting margin `ς(p') > 0`:
`h^pop_{p'}(σe(t)) + ς‖e(t)‖ ≤ h^pop_p(σe(t))` for `σ = ±1` and every `t` with `e(t) ≠ 0` (`A' = A_{K,p'}`). If the
population band at level `p'` covers `Y = 𝔪 + ⟨e(·), Π_K X⟩` with probability `≥ p'` (`prop:pop-band-coverage`,
certified), then `liminf_n P(Y ∈ B̂_K(p)) ≥ p'`, simultaneously in `t`, with no independence between `X` and the fit.
No measurability of the coverage events is assumed: `P` of a non-measurable event is Mathlib's outer measure (outer
probability), so the claim also covers fits that are not measurable in `ω`. At `t` with `e(t) = 0` both edges equal
`𝔪(t) = Y(t)` (`A ≠ ∅`). -/
def band_coverage_asymptotic : Prop :=
  ∀ (K : ℕ) (T Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure (Euc K))
    (A A' : Set (Euc K)) (Q : Euc K → Euc K) (Qn : ℕ → Ω → Euc K → Euc K) (Z : Ω → Euc K) (mfrak : T → ℝ)
    (e : T → Euc K) (p' ς : ℝ),
    MeasurableSet A → A.Nonempty → (∃ R : ℝ, ∀ᵐ u ∂μ.restrict A, ‖Q u‖ ≤ R) →
    (∀ᵐ ω ∂P, ∀ᵐ u ∂μ.restrict A, Tendsto (fun n => Qn n ω u) atTop (𝓝 (Q u))) →
    0 < ς → (∀ t, e t ≠ 0 → ∀ σ ∈ ({1, -1} : Set ℝ),
      StatFormal.Wave23a.popSupp μ A' Q (σ • e t) + ((ς * ‖e t‖ : ℝ) : EReal) ≤
        StatFormal.Wave23a.popSupp μ A Q (σ • e t)) →
    ENNReal.ofReal p' ≤ P {ω | InSuppBand (StatFormal.Wave23a.popSupp μ A' Q) mfrak e (Z ω)} →
      ENNReal.ofReal p' ≤
        liminf (fun n => P {ω | InSuppBand (StatFormal.Wave23a.fitSupp A (Qn n ω)) mfrak e (Z ω)}) atTop

/-! #### otfd G `lem:decoupling` (flat case) -/

/-- `eq:decouple` (Tonelli): `∫ D(z, x)² ν(dx) = ∫_T Ψ_t(z(t)) λ(dt)` for every `z ∈ 𝒳`. -/
def decoupling_tonelli : Prop :=
  ∀ (T : Type) [MeasurableSpace T] (lam : Measure T) [SigmaFinite lam]
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace (Lp E 2 lam)] [BorelSpace (Lp E 2 lam)]
    (ν : Measure (Lp E 2 lam)) (m : Lp E 2 lam) (ev : Lp E 2 lam × T → E),
    DecSetting ν m ev → ∀ z : Lp E 2 lam, jDec ν z = ∫⁻ t, psiDec ν ev t (z t) ∂lam

/-- `lem:decoupling`, first sentence, with the flat formula: there is a Borel `λ`-null `N_ν` off which `Ψ_t` is finite
and continuous; there, with `m̄_t = ∫ ev(x, t) ν(dx)`, `Ψ_t(p) = Ψ_t(m̄_t) + ‖p − m̄_t‖²` (so `argmin Ψ_t = {m̄_t}`). -/
def decoupling_finite : Prop :=
  ∀ (T : Type) [MeasurableSpace T] (lam : Measure T) [SigmaFinite lam]
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace (Lp E 2 lam)] [BorelSpace (Lp E 2 lam)]
    (ν : Measure (Lp E 2 lam)) (m : Lp E 2 lam) (ev : Lp E 2 lam × T → E),
    DecSetting ν m ev →
      ∃ N : Set T, MeasurableSet N ∧ lam N = 0 ∧ ∀ t ∉ N, (∀ p, psiDec ν ev t p < ⊤) ∧ Continuous (psiDec ν ev t) ∧
        ∀ p, psiDec ν ev t p = psiDec ν ev t (∫ x, ev (x, t) ∂ν) + ‖p - ∫ x, ev (x, t) ∂ν‖ₑ ^ 2

/-- `lem:decoupling`, second sentence: `argmin_𝒳 J` is nonempty, and `z` minimises `J` iff `z(t) ∈ argmin_E Ψ_t` for
`λ`-a.e. `t` (representative-independent). -/
def decoupling_argmin : Prop :=
  ∀ (T : Type) [MeasurableSpace T] (lam : Measure T) [SigmaFinite lam]
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace (Lp E 2 lam)] [BorelSpace (Lp E 2 lam)]
    (ν : Measure (Lp E 2 lam)) (m : Lp E 2 lam) (ev : Lp E 2 lam × T → E),
    DecSetting ν m ev →
      (∃ z : Lp E 2 lam, ∀ z', jDec ν z ≤ jDec ν z') ∧
        ∀ z : Lp E 2 lam, (∀ z', jDec ν z ≤ jDec ν z') ↔ ∀ᵐ t ∂lam, ∀ p, psiDec ν ev t (z t) ≤ psiDec ν ev t p

/-! #### otfd A `lem:app-references-Pl` -/

/-- (ii) The cubic law `𝓛(Σ_k λ_k V_k e_k)` (`V_k` i.i.d. `Unif[−½, ½]`, every `λ_k > 0`, `λ ∈ ℓ²`; frozen-free
`CubicDraw` with `iIndepFun V`) is in `𝒫^ℓ(H)` (frozen `PellClass`, with A's second-moment clause), via the
certified block criterion `lem:app-block-Pl` (Wave 20a) in the sieve basis. -/
def refs_Pl_cubic : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (e : HilbertBasis ℕ ℝ H) (lam : ℕ → ℝ) (V : ℕ → Ω → ℝ) (X : Ω → H),
    CubicDraw P e lam V X → iIndepFun V P → PellClass (P.map X)

/-- "The positivity hypotheses cannot be dropped": a law carried by a hyperplane `w^⊥` (`w ≠ 0`; a Lipschitz
hypersurface with `τ ≡ 0`) is not in `𝒫^ℓ(H)`. -/
def refs_Pl_hyperplane : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure H) (w : H), w ≠ 0 → μ {x | ⟪x, w⟫_ℝ = 0}ᶜ = 0 → ¬ PellClass μ

/-- The cubic instance: if `λ_{k₀} = 0` (all other hypotheses as in (ii)), `μ^cub` is carried by `{⟨x, e_{k₀}⟩ = 0}`
and is not in `𝒫^ℓ(H)`. -/
def refs_Pl_cubic_degenerate : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (e : HilbertBasis ℕ ℝ H) (lam : ℕ → ℝ) (V : ℕ → Ω → ℝ)
    (X : Ω → H) (k₀ : ℕ), Measurable X → (∀ᵐ ω ∂P, ∀ k, ⟪e k, X ω⟫_ℝ = lam k * V k ω) → lam k₀ = 0 →
      ¬ PellClass (P.map X)

/-- The ball instance: if `Cf = 0` for some `f ≠ 0`, i.e. the centred `⟨ζ, f⟩` has variance `0`, then
`μ^ball = 𝓛(Rζ/‖ζ‖)` is carried by `f^⊥` and is not in `𝒫^ℓ(H)` (any radius `R`). -/
def refs_Pl_ball_degenerate : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (ζ : Ω → H) (R : Ω → ℝ) (f : H),
    Measurable ζ → Measurable R → f ≠ 0 → Integrable (fun ω => ⟪ζ ω, f⟫_ℝ) P → ∫ ω, ⟪ζ ω, f⟫_ℝ ∂P = 0 →
    Var[fun ω => ⟪ζ ω, f⟫_ℝ; P] = 0 → MemLp (fun ω => ⟪ζ ω, f⟫_ℝ) 2 P →
      ¬ PellClass (P.map fun ω => (R ω / ‖ζ ω‖) • ζ ω)

/-! #### ICL `cor:consistency` -/

/-- The proof of `cor:consistency`, "the last three terms vanish": along any schedule with `n, m → ∞` and
`log n/m → 0`, `dev_{m,n,1/m} → 0` (`M` fixed). -/
def icl_dev_vanishes : Prop :=
  ∀ (BL lcov Kmin Kmax : ℝ) (M : ℕ) (n m : ℕ → ℕ),
    Tendsto (fun j => (n j : ℝ)) atTop atTop → Tendsto (fun j => (m j : ℝ)) atTop atTop →
    Tendsto (fun j => Real.log (n j) / m j) atTop (𝓝 0) →
      Tendsto (fun j => devBound BL lcov Kmin Kmax M (n j) (m j) (1 / m j)) atTop (𝓝 0)

/-- `cor:consistency`, first claim, CONDITIONAL on the two steps of its proof that are not formalised here: (1) the
reduction (on the almost-sure pool event, `J_pool(w) = R(μ_w) + λ_{KL,n}KL(w|u_n)` with `0 ≤ KL ≤ log n`), which with
the certified `thm:joint` (`δ = 1/m`) and `cor:oracle` gives, on an event of probability `≥ 1 − 1/m`,
`R(μ_ŵ) ≤ inf_w R(μ_w) + λ_{KL,n} log n + ε_opt + 2 dev_{m,n,1/m}` for all large `j` (`thm:joint` needs `n ≥ 2`,
`δ = 1/m ∈ (0,1)`); (2) the approximation step
`limsup_n inf_w R(μ_w) ≤ R⋆`. With `R(μ_ŵ) ≥ R⋆`, `n, m → ∞`, `log n/m → 0`, `λ_{KL,n} log n → 0`, `ε_opt → 0`:
`R(μ_ŵ) → R⋆` in probability. -/
def icl_consistency : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Rhat : ℕ → Ω → ℝ) (A : ℕ → ℝ)
    (Rstar : ℝ) (lamKL eps : ℕ → ℝ) (n m : ℕ → ℕ) (BL lcov Kmin Kmax : ℝ) (M : ℕ),
    (∀ j ω, Rstar ≤ Rhat j ω) →
    (∀ᶠ j in atTop, ∃ S : Set Ω, MeasurableSet S ∧ ENNReal.ofReal (1 - 1 / m j) ≤ P S ∧ ∀ ω ∈ S,
      Rhat j ω ≤ A j + lamKL j * Real.log (n j) + eps j + 2 * devBound BL lcov Kmin Kmax M (n j) (m j) (1 / m j)) →
    (∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, A j ≤ Rstar + ε) →
    Tendsto (fun j => (n j : ℝ)) atTop atTop → Tendsto (fun j => (m j : ℝ)) atTop atTop →
    Tendsto (fun j => Real.log (n j) / m j) atTop (𝓝 0) →
    Tendsto (fun j => lamKL j * Real.log (n j)) atTop (𝓝 0) → Tendsto eps atTop (𝓝 0) →
      TendstoInMeasure P Rhat atTop (fun _ => Rstar)

/-! #### otfd C `cor:coordinate-obstruction-empirical` -/

/-- `cor:coordinate-obstruction-empirical`, the kernel-ratio step of the proof (fixed `ε_X`, on a realisation where
the joint empirical laws `P̂_n` of `(C_i, Z_i)`, carried by `D × B̄(0, R)`, converge weakly to `P`, and the kernels
`k_n(x, c) = e^{(φ_n(c) − ‖x − c‖²)/ε_X}` converge uniformly on `B × D` to a continuous positive `k`): for every
continuous test function `g` of the response, `P̂^ν_{K,n,x}(g) → P^ν_{K,ε_X,x}(g)` uniformly in `x ∈ B`. -/
def coord_kernel_ratio : Prop :=
  ∀ (q K : ℕ) (D B : Set (Euc q)) (R : ℝ) (Pn : ℕ → Measure (Euc q × Euc K)) (P : Measure (Euc q × Euc K))
    (kn : ℕ → Euc q → Euc q → ℝ) (k : Euc q → Euc q → ℝ) (g : Euc K → ℝ),
    (∀ n, IsProbabilityMeasure (Pn n)) → IsProbabilityMeasure P → IsCompact D → IsCompact B →
    (∀ n, Pn n (D ×ˢ Metric.closedBall 0 R)ᶜ = 0) → P (D ×ˢ Metric.closedBall 0 R)ᶜ = 0 →
    (∀ f : BoundedContinuousFunction (Euc q × Euc K) ℝ,
      Tendsto (fun n => ∫ p, f p ∂(Pn n)) atTop (𝓝 (∫ p, f p ∂P))) →
    Continuous (Function.uncurry k) → (∀ x ∈ B, ∀ c ∈ D, 0 < k x c) →
    (∀ n x, Measurable (kn n x)) → TendstoUniformlyOn (fun n => Function.uncurry (kn n)) (Function.uncurry k) atTop
      (B ×ˢ D) → Continuous g →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x ∈ B, |locLaw (kn n) (Pn n) x g - locLaw k P x g| ≤ ε

end Claims
end StatFormal.Wave24d
