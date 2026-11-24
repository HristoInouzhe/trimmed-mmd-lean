import StatFormal.Archive.Wave23a.Statements
import StatFormal.Archive.OTFD.Bands.Statements
import StatFormal.Archive.OTFD.WaveL1.Statements
import Mathlib.InformationTheory.KullbackLeibler.Basic
import StatFormal.Archive.Wave11b.Statements
import StatFormal.Archive.Wave22c.Statements
import StatFormal.Archive.OTFD.Wave22b.Statements

/-!
# FROZEN STATEMENTS — wave 24c (QUEUE rows 330–342): otfd C `prop:cond-paths`; G `prop:equivariance`; T `cor:randomised`
# (theory:374), `prop:equivariance` (supp:814), `cor:smooth` (`eq:smooth`), `thm:coverage-error`, `prop:paths-M`,
# `lem:cf-schedule` (toolkit:401); SB `prop:embed`; ICL `lem:e-measures`, `lem:e-ulln`; NN `prop:average-offset-penalty`,
# `lem:tube-reduction` (with a partial discharge of Wave 22c `thm:tube-singleton`)

Sources (verbatim in `lean-formalisation/inventory/extracted/{otfd-C_conditional,otfd-G_geodesic,otfd-T_tangent,
data-fairness-repair,context-distribution-icl,proliferation-nns}.md`; current text after the 2026-10-16 corrections):
* otfd C `prop:cond-paths` (`otfd/papers/C_conditional/supplement.tex:2933-2944`, proof `:2163-2172`), with
  `def:cond-path` (`:2924-2930`), `eq:conditional-map` (`main.tex:394-398`) and `τ_p = c_K^{-1}(p)` (`main.tex:272-279`).
* otfd G `prop:equivariance` (`otfd/papers/G_geodesic/main.tex:638-645`, proof `:646-652`), with `def:ranks`
  (`:512-524`) and `prop:reference`(d).
* otfd T `cor:randomised` (`otfd/papers/T_tangent/sec_tangent_theory.tex:374-379`, proof `app_proofs.tex:179-191`).
* otfd T `prop:equivariance` (`T_tangent/supp_moved.tex:814-827`).
* otfd T `cor:smooth` (`T_tangent/supp_moved.tex:871-884`, proof `app_proofs.tex:148-156`), with `eq:binned`, `eq:empQ`
  (`sec_tangent_theory.tex:295-308`).
* otfd T `thm:coverage-error` (`T_tangent/supp_moved.tex:955-978`), with `lem:exp` (`:829-845`).
* otfd T `prop:paths-M` (`T_tangent/supp_toolkit.tex:91-115`, proof `:117-133`), with `def:path-M` (`:80-85`) and
  `eq:tk-domain` (`:66-70`).
* otfd T `lem:cf-schedule` (`T_tangent/supp_toolkit.tex:405-416`, proof `:418-433`).
* SB `prop:embed` (`data-fairness-repair/schrodinger_bridge_fairness_repair.tex:2308-2317`), with `def:repair`
  (`:435-446`), `eq:convolution` (`:467-469`), `eq:flowmap` (`:541-544`), `eq:wbary` (`:2144-2145`).
* ICL `lem:e-measures` (`context-distribution-ICL/paper/v3/supp/proofs_score.tex:89-99`, proof `:101-122`),
  `lem:e-ulln` (`:155-159`, proof `:161-177`), with the notation of `supp:score-assumptions` (`:11-80`).
* NN `prop:average-offset-penalty` (`proliferation-and-geometry-in-nns/paper_revised.tex:1029-1036`, proof
  `:1874-1888`), with `lem:marked-block-transform` (`:1003-1027`); `lem:tube-reduction` (`:1892-1905`, proof
  `:1906-1920`).
Imports the frozen `Wave23a` (`cdfK`, `cdfKInv`), `OTFD/Bands` (`softmax`), `OTFD/WaveL1` (`LipNull`, `Mom2`,
`IsCMMapAE`), `Wave11b` (`condLaw`; through it `Wave9b.flowMap`, `Wave4b.endpointMixture1`) and `Wave22c` (`IsLambertW`,
`avgOffset`, `etaQ`, `copyNum`, `Gbar`, `Ubar`, `Qtube`, `tubeT`, `rhoG`, `PhiS`, `zetaQ`, `kappaD`; through it
`NNFibers`: `T`, `LabPart`, `Neuron`) and `OTFD/Wave22b` (`LengthBound`, `Lb` of `lem:exp`) statements, not copied;
Mathlib (`klDiv`) and Tau Ceti otherwise.

Covered:
* C `prop:cond-paths`: `cond_paths_mono` ((i), every query: the covariate moves only the intercepts), `cond_paths_strict`
  ((i), strict when the retained responses affinely span `ℝ^K`). (ii) is the frozen Wave 24a `rk_paths_labels` (B
  `prop:rk-paths`(ii)) with `P_K = P_{K,x}`, as the printed proof says; the critic removed the draft's restatement
  `cond_paths_level`.
* T `prop:paths-M`: `paths_M_mono` ((i), weak and strict), `paths_M_level` ((ii), through the chart),
  `paths_M_uniform` ((iii), `lem:exp` DISCHARGED through the frozen Wave 22b `LengthBound`/`Lb`, `eq:Hembed` and
  `eq:tk-domain` as hypotheses: the `D_∞ ≤ L_bΛ S_n` bound and, for `L_b < ∞`, the uniform convergence).
* T `prop:equivariance` (supp:814): `equivariance_unitary` (`Q' = JQJ⁻¹`, `F' = JFJ⁻¹` a.e., via the certified
  WaveL3 `brenier_uniq_H`; norms, hence calibrated depths and signs, agree).
* G `prop:equivariance`: `equivariance_plan` (the entropic plans of the transformed problem are exactly the pushforwards
  `(Φ × ψ)#π`; uniqueness transfers), `equivariance_quantile` (`φ` maps the quantile SET at `v` onto the one at `dφ v`;
  unique quantiles correspond), `equivariance_rank` (`F'(φ∘x) = dφ F(x)`, `R' = R`, so `D' = D`).
* T `cor:randomised` (theory:374): `randomised_calibration` — CONDITIONAL on the Rigollet–Stromme mean-square dual
  bounds and the DKW–Massart consequence.
* T `cor:smooth`: `smooth_exact` (exact solver ⇒ conditional barycenter = `Q^sm` at the grid atoms),
  `smooth_lipschitz` (`Q^sm` is `2B²/ε`-Lipschitz), `smooth_consistency` (the `(2B²/ε_n)² h_n²` bound and `eq:empQ` for
  `Q^sm_n`, CONDITIONAL on `thm:empirical`).
* T `thm:coverage-error`: `coverage_error` (`lem:exp` DISCHARGED as in `paths_M_uniform`; CONDITIONAL on
  `X = E_m Q(U)`).
* T `lem:cf-schedule` (toolkit:401): `cf_schedule` (the diagonal schedule, Borel–Cantelli; CONDITIONAL on C
  Theorem 4.2 at fixed strength).
* SB `prop:embed`: `embed_corner` (`t = 1`: `μ^ε_{s,1} = ν`, `h̃^flow_{1,ε} = F_ν^{-1} ∘ F_{R_s} ∘ h`, demographic parity
  via the certified `thm:flow`(i)), `embed_identity` (`t = 0`: `μ^ε_{s,0} = R_s`, `h̃^flow_{0,ε} = h` a.s.).
* ICL `lem:e-measures`: `e_measures_pop` ((i) population, (ii)), `e_measures_emp_weak` ((i) empirical, event depending
  on the test function), `e_measures_emp` ((iii)), for i.i.d. nested samples (the compact-parametric Glivenko–Cantelli
  principle is DISCHARGED in the route by the Wave 20b `uniform_slln`).
* ICL `lem:e-ulln`: `e_ulln` — i.i.d. samples; CONDITIONAL on the uniform convergence of the risk term only.
* NN `prop:average-offset-penalty`: `average_offset_penalty` — CONDITIONAL on `lem:marked-block-transform`
  (`eq:marked-pgf-asymptotic` on `(0,1]^q`).
* NN `lem:tube-reduction`: `tube_reduction_ratio` (second claim from the first, CONDITIONAL on the first at `q = r, k`),
  `tube_gamma_shape` (the last step, `P_a(t) = ρ(a)e^{−t}(1 + O(t/a))` with explicit constant), and the PARTIAL
  DISCHARGE `tube_singleton_discharged` of the frozen Wave 22c `tube_singleton`.

Not covered (declared):
* C `prop:cond-paths`: (iii) (`cor:conditional-uniform-x`, L3; the reduction is the inclusion `τ_p v ∈ A_{K,1−δ}`); the
  quadratic penalty in (i) (simplex-projection map; only the entropic map is formalised).
* T `prop:paths-M`: the "equivalently" form through `L_c` and `ι_K` (orthonormal embedding); the Riemannian length
  bound (frozen `LengthBound`), `eq:Hembed`, `eq:tk-domain` and `L_b < ∞` (hypotheses, as in Wave 22b); the
  band-consistency theorem that supplies (iii)'s premise.
* T `prop:equivariance` (supp:814): "if the scores and reference regions are also transformed, calibrated ranks and
  reconstructed manifold regions agree" beyond the a.e. identities of the maps and norms; manifold isometries.
* G `prop:equivariance`: the geometric input `c'_s(dφ v, φ∘x) = c_s(v, x)` (isometries commute with `Exp`, preserve
  `D`; hypothesis on the costs); the derivation of the conditional-law relations `π'(·|dφ v) = φ#π(·|v)`,
  `π'(·|φ∘x) = dφ#π(·|x)` from the plan identity (disintegration, a.e. uniqueness of kernels; hypotheses of
  `equivariance_quantile`, `equivariance_rank`); `prop:reference`(d); the calibrated depth.
* T `cor:randomised`: the Rigollet–Stromme bounds and DKW–Massart themselves (hypotheses); that the antithetic draws
  change the constant by at most `2`.
* T `cor:smooth`: `thm:empirical` (`eq:empQ`, hypothesis; L4).
* T `thm:coverage-error`: `LengthBound`, `L_b < ∞`, `eq:Hembed`, `thm:population` (hypotheses); the "consequently"
  clause on asymptotic content (immediate from the bound with a consistency hypothesis).
* T `lem:cf-schedule`: C Theorem 4.2 and the bias limit `β(σ) → 0` (hypotheses); the measurability of the suprema over
  `D` (hypothesis `E` measurable); the joint-response remark.
* SB `prop:embed`: that `F_{ν^W}^{-1} ∘ F_{R_s} ∘ h` is the optimal demographic-parity predictor (Chzhen et al., Le
  Gouic et al.; cited, not proved here); the stochastic realisation at `t = 0`.
* ICL: `lem:e-normalizers`, `lem:e-vstat` (the risk term of `e_ulln` is a hypothesis); the single almost-sure event of
  (i) for all test functions (countable convergence-determining class); the closed form of `KL(μ_θ‖P₀)` (entered as
  its formula).
* NN `prop:average-offset-penalty`: `lem:marked-block-transform` (Hayman's method; hypothesis).
* NN `lem:tube-reduction`: the first claim (Poisson-mixture sandwich `eq:noncentral-sandwich` for the frozen `ncChiSq`,
  and `λ_s/a(K) → 0` in probability under the tilted laws).

Encodings (to be checked by the critic):
* Entropic map: `lseMap ε κ a z u = Σ_j softmax_j((a_j + κ⟨z_j, u⟩)/ε) z_j` (frozen `Bands.softmax`) on a real inner
  product space; C uses `κ = 2`, `a = a(x)`; T `κ = 2` (`eq:affine`) or `κ = s` (Algorithm 1). "Affinely span" is
  `affineSpan ℝ (range z) = ⊤`. `τ_p = cdfKInv μ ρ p` (frozen); C's radial function `ρ` is any positively homogeneous
  function (norm, gauge), `𝗌(u) = ρ(u)^{-1} u`; T's depth uses `c_K(r) = μ_K(‖u‖ ≤ r)`, and (ii) assumes
  `c_K(ρ_K(p)) = p` (the definition of `ρ_K(p)` as the level-`p` radius). (ii): curves an abstract type `C` with
  chart maps `Φ = E_c(v̄ + ι_K ·)`, `Ψ = Π_K(L_c − v̄)`. (iii): curves `t ↦ Ex t (v̄(t) + (ι_K z)(t))` in a
  pseudo-e-metric `M`, `D_∞ = ⨆_t edist` in `[0,∞]`, `L_b = Lb D b` (no junk: the convergence clause assumes `≠ ⊤`).
* T unitary equivariance: `J : H ≃ₗᵢ[ℝ] H'` between separable Hilbert spaces; the Brenier map is any Borel, a.e.
  cyclically monotone map with the right pushforward (frozen WaveL1 `IsCMMapAE`); uniqueness needs the source null on
  Lipschitz hypersurfaces and second moments (as in WaveL3).
* G: the entropic objective `∫ c dπ + ε KL(π‖μ⊗P)` in `[0,∞]` with `c ≥ 0` (Mathlib `klDiv`); `IsEntPlanG` = finite
  minimiser over couplings; `Φ`, `ψ` measurable equivalences (in the paper `dφ` and `x ↦ φ∘x`); quantiles are the
  Fréchet sets `frechetSet` of `∫ D(z,x)² κ(dx)` in `[0,∞]` (`ψ` an isometry equivalence); kernels are total
  functions with the transformation law at every point (versions).
* T randomized ranks: the law of `U*` given the data is `randCDF` (plan density `exp((f̂_l + ĝ(z) − c)/ε)` w.r.t.
  `μ_{n_ref} ⊗ ν_K`); all exponents `≤ M`; expectations are lower Lebesgue integrals in `[0,∞]` of `sup_ρ` (both
  `ρ ↦` functions are right-continuous, so the suprema are measurable; not used); RS hypotheses as mean-square bounds
  `≤ A(1/n + 1/n_ref)`; DKW as `E sup ≤ (π/(2n_ref))^{1/2}`; `C_ε = 2e^M A^{1/2} + (π/2)^{1/2}`.
* T smooth: `smoothMap ε f y x` with `x = P_{K_n} u`; the grid plan is `a_i n^{-1} e^{(g_i + f_j − ‖ξ_i − y_j‖²)/ε}`;
  integrals are `∫⁻ ‖·‖ₑ²`; `h_n/ε_n → 0` is `ε_n^{-2} h_n² → 0`; `Q̄_n(u) = Q^sm_n(ξ_n(u))` is the hypothesis supplied
  by `smooth_exact`.
* T coverage: fields `H` (separable), curves `t ↦ Ex t ((ι v)(t)) ∈ M` (pseudo-e-metric `M`), `ι` linear with
  `‖(ι v)(t)‖ ≤ Λ‖v‖`; `L = (Lb D b).toReal · Λ` under `Lb D b ≠ ⊤` (so `toReal` is not junk); `X = E(Q(U))`, `U ∼ μ`; the
  expanded tube is "within `δ` of a point of `𝒯(t)`" (a subset of the closed `δ`-expansion, so the bound is no
  weaker); the conclusion is a measurable event, the bound in `[0,∞]` with truncated subtraction.
* T schedule: queries in a finite type; `E^{(a)}_n(σ)`, `β^{(a)}(σ)`, `err^{(a)}_n(σ)` abstract with `err ≤ E + β`
  (the `W₁` triangle inequality); the schedule is one positive nonincreasing `σ_n → 0` (the same for both responses;
  each penalty separately).
* SB: frozen `condLaw`, `flowMap`, `endpointMixture1` (`μ^ε_{s,t}` through `eq:convolution`); any plan with the right
  marginal (in particular `π*_ε`, `π*_0`); atomless is `NullSingletonClass`.
* ICL: `𝒵`, `Θ` compact metric; `μ_θ = (s_θ/c_θ)P₀` (`withDensity`), `μ_{θ,n} = Σ_{j<n} w_j δ_{Z_j}`, coverage
  `ρ_μ(z) = ∫ K(z,·) dμ`; pool `X_i`, validation sample `Y_i` nested sequences, `P_n` averages over `i < n`, `m = m(n) → ∞`;
  pool and validation sequences each i.i.d. `P₀` (`iIndepFun`, measurable, law `P₀`; their mutual independence is
  not needed); uniform convergence is `TendstoUniformly`; `λ_{·,n}` real sequences.
* NN: frozen `avgOffset`, `etaQ`, `Gbar`, `Ubar`, `Qtube`, `rhoG`; `markedPGF q m z = E_{U_{q,m}}[∏ z_i^{N_i}]`;
  `P_a(t) = γ(a,t)/Γ(a)` (`incGammaReg`, interval integral); `∼` is `IsEquivalent atTop` on `ℕ`.

Critic notes:
* All 25 claims are proved in `Wave24c/Route{Paths,EquivT,EquivG,Embed,Coverage,Schedule,RandRank,Smooth,ICL,Offset,
  Tube}.lean`. Routes reuse the certified WaveL3 `brenier_uniq_H`, WaveL1 `graph_fst`, `graph_snd`, `cmConc_graph`,
  Wave23a `cdfK_inv_spec`, Wave11b `flow_push`, Wave22b `exp_pointwise` (route of the certified `exp_bounds`),
  Wave20b `uniform_slln` (route of the certified `e_normalizers`), Wave22c `refined_offset_identity`, `refined_offset_limits`,
  `lambertW_tendsto_atTop`, `T_ne_zero_eventually`, `tube_singleton`, NNFibers `T_pos`, Tau Ceti `quantile_cdf_ae`.
* CONDITIONAL claims and their inputs: `coverage_error` (`X = E_mQ(U)`, `thm:population`); `randomised_calibration`
  (RS (4.3) + Lemma 14 in-sample and out-of-sample dual bounds, DKW–Massart); `smooth_consistency` (`thm:empirical`);
  `cf_schedule` (C Theorem 4.2 at fixed strength; its "consequently" part is the certified Wave 22b
  `selfloc_consistency`, itself conditional on the same input); `e_ulln` (the risk term); `average_offset_penalty`
  (`lem:marked-block-transform`); `tube_reduction_ratio`, `tube_singleton_discharged` (`lem:tube-reduction`, first
  claim). `lem:exp` (`paths_M_uniform`, `coverage_error`) and Glivenko–Cantelli (ICL) were discharged by the critic.
* Observations: (1) C (ii) and T (ii) evaluate the rank map at one (reference-null) point, so they need the continuous
  inverse (stated as a left inverse on the interior); T names it ("with inverse `F_K`"), C does not. (2) T
  `prop:paths-M`(ii) needs `c_K(ρ_K(p)) = p`, which is the definition of `ρ_K(p)`; the parenthetical `ρ_K(p) = p` is
  right only for a reference with `c_K = id` (radially uniform ball law), not for the coherent law of Algorithm 1.
  (3) `cor:randomised`'s `C_ε` is not `thm:rates`' `C_ε` (it carries `e^M A^{1/2}` and `(π/2)^{1/2}`); both depend only
  on `c̄/ε`. (6) `cf_schedule` overlaps the frozen Wave 22b `selfloc_staircase` (one diagonal schedule); it adds the
  finite family of queries sharing one schedule and the `err ≤ E + β` step, so it is not an instance. (4) G's quantile clause holds for the
  argmin sets (as now printed); a pointwise identity needs uniqueness. (5) SB `prop:embed`'s formulas hold for every
  `ε` and every plan with the right marginal (`t(1−t) = 0` kills the Gaussian factor); `t = 0` needs no atomless
  hypothesis.

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Asymptotics Finset
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave24c

/-! ### otfd C / T: the entropic out-of-sample map and scenario paths -/

section Paths
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The entropic out-of-sample map with affine scores `s_j(u) = a_j + κ⟨z_j, u⟩`:
`Q̂(u) = Σ_j softmax_j(s(u)/ε) z_j` (C `eq:conditional-map` with `κ = 2`, `a = a(x)`; T `eq:affine` with `κ = 2`, or
Algorithm 1 with `κ = s`). -/
def lseMap {n : ℕ} (ε κ : ℝ) (a : Fin n → ℝ) (z : Fin n → E) (u : E) : E :=
  ∑ j, StatFormal.OTFD.Bands.softmax (fun i => (a i + κ * ⟪z i, u⟫) / ε) j • z j

/-- The sign `𝗌(u) = u/ρ(u)` of a reference point for the radial function `ρ`. -/
def signMap (ρ : E → ℝ) (u : E) : E := (ρ u)⁻¹ • u

end Paths

/-! ### otfd G: entropic geodesic plans, ranks and quantiles -/

section Geo
variable {V X : Type*} [MeasurableSpace V] [MeasurableSpace X]

/-- The entropic objective `∫ c dπ + ε KL(π ‖ μ ⊗ P)` in `[0,∞]` (cost `c ≥ 0`, e.g. `c_s(v,x) = D(E_m(sv),x)²/(2s²)`). -/
def entObjG (c : V × X → ℝ≥0∞) (ε : ℝ) (μ : Measure V) (P : Measure X) (π : Measure (V × X)) : ℝ≥0∞ :=
  ∫⁻ z, c z ∂π + ENNReal.ofReal ε * InformationTheory.klDiv π (μ.prod P)

/-- `π` is an entropic plan: a coupling of `μ` and `P` with finite objective, minimal among all couplings. -/
def IsEntPlanG (c : V × X → ℝ≥0∞) (ε : ℝ) (μ : Measure V) (P : Measure X) (π : Measure (V × X)) : Prop :=
  IsProbabilityMeasure π ∧ π.map Prod.fst = μ ∧ π.map Prod.snd = P ∧ entObjG c ε μ P π ≠ ∞ ∧
    ∀ π' : Measure (V × X), IsProbabilityMeasure π' → π'.map Prod.fst = μ → π'.map Prod.snd = P →
      entObjG c ε μ P π ≤ entObjG c ε μ P π'

end Geo

/-- The Fréchet (quantile) set `argmin_z ∫ D(z,x)² κ(dx)` of a law `κ` on a metric space of curves (`def:ranks`:
`Q_ε(v)` is a selection from this set for `κ = π_ε(· | v)`). -/
def frechetSet {X : Type*} [PseudoEMetricSpace X] [MeasurableSpace X] (κ : Measure X) : Set X :=
  {z | ∀ z', ∫⁻ x, edist z x ^ 2 ∂κ ≤ ∫⁻ x, edist z' x ^ 2 ∂κ}

/-! ### otfd T: randomized ranks of a new curve -/

section RandRank
variable {E Z : Type*} [Norm E] [MeasurableSpace Z]

/-- Given the data, `P{‖U*‖ ≤ ρ | data} = Σ_l n_ref^{-1} 1{‖U_l‖ ≤ ρ} ∫ p̂(U_l, z) ν_K(dz)`, the fitted plan density
being `p̂(U_l, z) = exp((f̂_l + ĝ(z) − c(U_l, z))/ε)` (the law of the randomized rank `U*` of a new curve `Z ∼ ν_K` is
`Σ_l w_l δ_{U_l}`, `w_l = n_ref^{-1} ∫ p̂(U_l, z) dν_K(z)`). -/
def randCDF {N : ℕ} (ν : Measure Z) (ε : ℝ) (U : Fin N → E) (f : Fin N → ℝ) (g : Z → ℝ) (c : E → Z → ℝ)
    (ρ : ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ l, if ‖U l‖ ≤ ρ then ∫ z, Real.exp ((f l + g z - c (U l) z) / ε) ∂ν else 0

/-- The empirical distribution function of the reference radii, `μ_{n_ref}{‖u‖ ≤ ρ}`. -/
def empNormCDF {N : ℕ} (U : Fin N → E) (ρ : ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ l, if ‖U l‖ ≤ ρ then (1 : ℝ) else 0

end RandRank

/-! ### otfd T: the smooth grid-dual extension -/

/-- `Q^sm(x) = Σ_j q_j(x) y_j`, `q_j(x) = softmax_j((f_j − ‖x − y_j‖²)/ε)` (`eq:smooth`, evaluated at `x = P_{K_n} u`). -/
def smoothMap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ} (ε : ℝ) (f : Fin n → ℝ)
    (y : Fin n → E) (x : E) : E :=
  ∑ j, StatFormal.OTFD.Bands.softmax (fun i => (f i - ‖x - y i‖ ^ 2) / ε) j • y j

/-! ### ICL: score-induced context laws -/

section ICL
variable {Θ Z : Type*} [MeasurableSpace Z]

/-- `c_θ = P₀ s_θ`. -/
def normC (P0 : Measure Z) (s : Θ → Z → ℝ) (θ : Θ) : ℝ := ∫ z, s θ z ∂P0

/-- `μ_θ = g_θ P₀`, `g_θ = s_θ/c_θ`. -/
def ctxLawT (P0 : Measure Z) (s : Θ → Z → ℝ) (θ : Θ) : Measure Z :=
  P0.withDensity fun z => ENNReal.ofReal (s θ z / normC P0 s θ)

/-- The coverage `ρ_μ(z) = ∫ K(z, z') μ(dz')`. -/
def coverRho (K : Z → Z → ℝ) (μ : Measure Z) (z : Z) : ℝ := ∫ z', K z z' ∂μ

/-- The weighted pool law `μ_{θ,n} = Σ_{j<n} w_j δ_{Z_j}`, `w_j = s_θ(Z_j)/Σ_{k<n} s_θ(Z_k)`. -/
def empCtxLaw (s : Θ → Z → ℝ) (X : ℕ → Z) (n : ℕ) (θ : Θ) : Measure Z :=
  ∑ j ∈ Finset.range n, ENNReal.ofReal (s θ (X j) / ∑ k ∈ Finset.range n, s θ (X k)) • Measure.dirac (X j)

/-- The empirical average `P_n f = n^{-1} Σ_{i<n} f(X_i)`. -/
def empAvg (X : ℕ → Z) (n : ℕ) (f : Z → ℝ) : ℝ := (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, f (X i)

/-- `KL(μ_θ ‖ P₀) = P₀(s_θ log s_θ)/P₀ s_θ − log P₀ s_θ` (closed form, `d μ_θ/dP₀ = s_θ/c_θ`). -/
def klPop (P0 : Measure Z) (s : Θ → Z → ℝ) (θ : Θ) : ℝ :=
  (∫ z, s θ z * Real.log (s θ z) ∂P0) / normC P0 s θ - Real.log (normC P0 s θ)

/-- `KL(μ_{θ,n} ‖ P_n) = P_n(s_θ log s_θ)/P_n s_θ − log P_n s_θ`. -/
def klEmp (s : Θ → Z → ℝ) (X : ℕ → Z) (n : ℕ) (θ : Θ) : ℝ :=
  empAvg X n (fun z => s θ z * Real.log (s θ z)) / empAvg X n (s θ) - Real.log (empAvg X n (s θ))

end ICL

/-! ### NN: the marked transform of the copy numbers -/

/-- `E_{U_{q,m}}[∏_i z_i^{N_i}]` (uniform law on the pieces `Γ ∈ C_{q,m}`, `N_i = copyNum Γ i`). -/
def markedPGF (q m : ℕ) (z : Fin q → ℝ) : ℝ :=
  (∑ Γ : StatFormal.NNFibers.Wave1.LabPart q m, ∏ i, z i ^ StatFormal.Wave22c.copyNum Γ i) /
    (StatFormal.NNFibers.T q m : ℝ)

/-- The regularized lower incomplete Gamma function `P_a(t) = γ(a, t)/Γ(a)`, `γ(a, t) = ∫_0^t u^{a−1} e^{−u} du`
(the central `χ²_{2a}` cdf at `2t`). -/
def incGammaReg (a t : ℝ) : ℝ := (∫ u in (0 : ℝ)..t, u ^ (a - 1) * Real.exp (-u)) / Real.Gamma a

namespace Claims

/-! #### C `prop:cond-paths` -/

/-- C `prop:cond-paths` (i), entropic map: for every query (the covariate moves only the intercepts `a = a(x)`), every
reference law `μ_K` with radial function `ρ` and calibration `c_K(1) = 1`, and every direction `v`,
`p ↦ ⟨v, Q̂_x(τ_p v)⟩` is nondecreasing on `[0,1]`, `τ_p = c_K^{-1}(p)`. -/
def cond_paths_mono : Prop :=
  ∀ (K n : ℕ) (ε : ℝ) (a : Fin n → ℝ) (Z : Fin n → EuclideanSpace ℝ (Fin K))
    (μ : Measure (EuclideanSpace ℝ (Fin K))) (ρ : EuclideanSpace ℝ (Fin K) → ℝ) (v : EuclideanSpace ℝ (Fin K)),
    0 < ε → StatFormal.Wave23a.cdfK μ ρ 1 = 1 →
      MonotoneOn (fun p => ⟪v, lseMap ε 2 a Z (StatFormal.Wave23a.cdfKInv μ ρ p • v)⟫) (Icc 0 1)

/-- C `prop:cond-paths` (i), strictness: when the retained responses `Z_i` affinely span `ℝ^K` and `c_K` is a
continuous calibration (`c_K(0) = 0`, `c_K(1) = 1`), the path is strictly increasing in every direction `v ≠ 0`. -/
def cond_paths_strict : Prop :=
  ∀ (K n : ℕ) (ε : ℝ) (a : Fin n → ℝ) (Z : Fin n → EuclideanSpace ℝ (Fin K))
    (μ : Measure (EuclideanSpace ℝ (Fin K))) (ρ : EuclideanSpace ℝ (Fin K) → ℝ) (v : EuclideanSpace ℝ (Fin K)),
    0 < ε → affineSpan ℝ (Set.range Z) = ⊤ → v ≠ 0 →
    ContinuousOn (StatFormal.Wave23a.cdfK μ ρ) (Icc 0 1) →
    StatFormal.Wave23a.cdfK μ ρ 0 = 0 → StatFormal.Wave23a.cdfK μ ρ 1 = 1 →
      StrictMonoOn (fun p => ⟪v, lseMap ε 2 a Z (StatFormal.Wave23a.cdfKInv μ ρ p • v)⟫) (Icc 0 1)

/-! #### T `prop:paths-M` -/

/-- T `prop:paths-M` (i), in coefficient space: for the entropic map with affine scores `a_j + κ⟨z_j, u⟩` (`κ = 2` in
`eq:affine`, `κ = s` in Algorithm 1) and a nondecreasing radius `ρ_K` on `[0,1)`, `p ↦ ⟨v, Q̂(ρ_K(p) v)⟩` is
nondecreasing on `[0,1)`; it is strictly increasing when the fitted coefficients affinely span `ℝ^K`, `ρ_K` is
strictly increasing and `v ≠ 0` (orthonormal coordinates: the inner product is the Euclidean one). -/
def paths_M_mono : Prop :=
  ∀ (K n : ℕ) (ε κ : ℝ) (a : Fin n → ℝ) (z : Fin n → EuclideanSpace ℝ (Fin K)) (ρK : ℝ → ℝ)
    (v : EuclideanSpace ℝ (Fin K)),
    0 < ε → 0 < κ → MonotoneOn ρK (Ico 0 1) →
      MonotoneOn (fun p => ⟪v, lseMap ε κ a z (ρK p • v)⟫) (Ico 0 1) ∧
      (affineSpan ℝ (Set.range z) = ⊤ → StrictMonoOn ρK (Ico 0 1) → v ≠ 0 →
        StrictMonoOn (fun p => ⟪v, lseMap ε κ a z (ρK p • v)⟫) (Ico 0 1))

/-- T `prop:paths-M` (ii): curves `y` in a chart `c`, with `Φ(z) = E_c(v̄ + ι_K z)` and its inverse
`Ψ = Π_K(L_c − v̄)` on the chart domain `‖z‖ ≤ B`; depth and sign of a curve are `1 − c_K(‖F_K(Ψ y)‖)` and
`F_K(Ψ y)/‖F_K(Ψ y)‖`, `c_K(r) = μ_K(‖U‖ ≤ r)`. If `F_K` inverts `Q_K` on `int supp μ_K`, `Q_K` takes values in the
chart domain there, `‖v‖ = 1`, `ρ_K(p) v` is interior and `c_K(ρ_K(p)) = p` (the radius is the level-`p` radius of
`μ_K`), then `γ^pop_v(p) = Φ(Q_K(ρ_K(p) v))` has depth `1 − p`, and sign `v` when `ρ_K(p) > 0`. -/
def paths_M_level : Prop :=
  ∀ (K : ℕ) (C : Type*) (μ : Measure (EuclideanSpace ℝ (Fin K)))
    (Q F : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (Φ : EuclideanSpace ℝ (Fin K) → C)
    (Ψ : C → EuclideanSpace ℝ (Fin K)) (B : ℝ) (ρK : ℝ → ℝ) (p : ℝ) (v : EuclideanSpace ℝ (Fin K)),
    (∀ z, ‖z‖ ≤ B → Ψ (Φ z) = z) → (∀ u ∈ interior μ.support, F (Q u) = u) →
    (∀ u ∈ interior μ.support, ‖Q u‖ ≤ B) → ‖v‖ = 1 → 0 ≤ ρK p → ρK p • v ∈ interior μ.support →
    StatFormal.Wave23a.cdfK μ (fun u => ‖u‖) (ρK p) = p →
      1 - StatFormal.Wave23a.cdfK μ (fun u => ‖u‖) ‖F (Ψ (Φ (Q (ρK p • v))))‖ = 1 - p ∧
      (0 < ρK p → signMap (fun u => ‖u‖) (F (Ψ (Φ (Q (ρK p • v))))) = v)

/-- T `prop:paths-M` (iii), with `lem:exp` DISCHARGED through the frozen Wave 22b `LengthBound` and `L_b = Lb D b`
(`eq:L`): the curve of a coefficient vector `z` is `t ↦ Exp_{m(t)}(v̄(t) + (ι_K z)(t))` (`Ex t = Exp_{c(t)}`, `D t v`
its differential), `ι_K` linear with `sup_t ‖(ι_K z)(t)‖ ≤ Λ‖z‖` (`eq:Hembed`), and every field `v̄ + ι_K z` with
`‖z‖ ≤ B` pointwise bounded by `b` (`eq:tk-domain`). If the fitted coefficients and `Q_K` on the ball of radius
`ρ_K(1−δ)` lie in the `B`-ball, then for every fit `Q̂_n` and every bound `S_n ≥ sup_{‖u‖≤ρ_K(1−δ)} ‖Q̂_n(u) − Q_K(u)‖`,
`D_∞(γ_v(p), γ^pop_v(p)) = sup_t d_M ≤ L_b Λ S_n` for all `p ≤ 1 − δ` and unit `v` (in `[0,∞]`); and if that supremum
tends to `0` and `L_b < ∞`, the scenario paths converge in `D_∞` uniformly in `p ≤ 1 − δ` and `v`. -/
def paths_M_uniform : Prop :=
  ∀ (K n : ℕ) (T V W M : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [PseudoEMetricSpace M] (Ex : T → V → M) (D : T → V → V →L[ℝ] W) (vbar : T → V)
    (ι : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] (T → V)) (Λ b B ε κ δ : ℝ) (ρK : ℝ → ℝ)
    (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (a : ℕ → Fin n → ℝ)
    (z : ℕ → Fin n → EuclideanSpace ℝ (Fin K)),
    0 < ε → 0 < κ → 0 < δ → δ ≤ 1 → 0 ≤ Λ → MonotoneOn ρK (Ico 0 1) → (∀ p ∈ Ico (0 : ℝ) 1, 0 ≤ ρK p) →
    StatFormal.OTFD.Wave22b.LengthBound Ex D → (∀ x t, ‖ι x t‖ ≤ Λ * ‖x‖) →
    (∀ x, ‖x‖ ≤ B → ∀ t, ‖vbar t + ι x t‖ ≤ b) →
    (∀ m j, ‖z m j‖ ≤ B) → (∀ u, ‖u‖ ≤ ρK (1 - δ) → ‖Q u‖ ≤ B) →
      (∀ (m : ℕ) (S : ℝ), (∀ u, ‖u‖ ≤ ρK (1 - δ) → ‖lseMap ε κ (a m) (z m) u - Q u‖ ≤ S) →
        ∀ p ∈ Icc (0 : ℝ) (1 - δ), ∀ v, ‖v‖ = 1 →
          (⨆ t, edist (Ex t (vbar t + ι (lseMap ε κ (a m) (z m) (ρK p • v)) t))
              (Ex t (vbar t + ι (Q (ρK p • v)) t))) ≤
            StatFormal.OTFD.Wave22b.Lb D b * ENNReal.ofReal (Λ * S)) ∧
      (StatFormal.OTFD.Wave22b.Lb D b ≠ ⊤ →
        (∀ η : ℝ, 0 < η → ∀ᶠ m in atTop, ∀ u, ‖u‖ ≤ ρK (1 - δ) → ‖lseMap ε κ (a m) (z m) u - Q u‖ ≤ η) →
        ∀ η : ℝ, 0 < η → ∀ᶠ m in atTop, ∀ p ∈ Icc (0 : ℝ) (1 - δ), ∀ v, ‖v‖ = 1 →
          (⨆ t, edist (Ex t (vbar t + ι (lseMap ε κ (a m) (z m) (ρK p • v)) t))
              (Ex t (vbar t + ι (Q (ρK p • v)) t))) ≤ ENNReal.ofReal η)

/-! #### T `prop:equivariance` (supp:814) -/

/-- T `prop:equivariance` (`supp:814`), Hilbert-space part: let `J : H → H'` be unitary (a linear isometry
equivalence of separable Hilbert spaces), and transform both laws, `P ↦ J#P`, `μ ↦ J#μ`. If `T` is the Brenier map
from `P` to `μ` (Borel, `P`-a.e. cyclically monotone, `T#P = μ`; unique by GHS since `P` is null on Lipschitz
hypersurfaces and both laws have second moments), then every Brenier map `T'` from `J#P` to `J#μ` satisfies
`T' = J T J⁻¹` `J#P`-a.e., equivalently `T'(Jx) = J T(x)` and `‖T'(Jx)‖ = ‖T(x)‖` for `P`-a.e. `x`. Applied with
`(P, μ, T) = (μ_ref, ν, Q)` and with `(ν, μ_ref, F)` this is `Q' = JQJ⁻¹`, `F' = JFJ⁻¹` a.e., and the transformed
rank radius (hence calibrated depth) and sign `F'/‖F'‖ = J(F/‖F‖)` agree a.e. -/
def equivariance_unitary : Prop :=
  ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] [NormedAddCommGroup H'] [InnerProductSpace ℝ H'] [CompleteSpace H']
    [SecondCountableTopology H'] [MeasurableSpace H'] [BorelSpace H']
    (J : H ≃ₗᵢ[ℝ] H') (P μ : Measure H) (T : H → H) (T' : H' → H'),
    IsProbabilityMeasure P → IsProbabilityMeasure μ →
    StatFormal.OTFD.WaveL1.LipNull P → StatFormal.OTFD.WaveL1.Mom2 P ≠ ∞ → StatFormal.OTFD.WaveL1.Mom2 μ ≠ ∞ →
    Measurable T → P.map T = μ → StatFormal.OTFD.WaveL1.IsCMMapAE P T →
    Measurable T' → (P.map J).map T' = μ.map J → StatFormal.OTFD.WaveL1.IsCMMapAE (P.map J) T' →
      (T' =ᵐ[P.map J] fun y => J (T (J.symm y))) ∧ ∀ᵐ x ∂P, T' (J x) = J (T x) ∧ ‖T' (J x)‖ = ‖T x‖

/-! #### G `prop:equivariance` -/

/-- G `prop:equivariance`, the plan: for measurable bijections `Φ` of the reference space (`dφ`) and `ψ` of the curve
space (`x ↦ φ ∘ x`) under which the cost is invariant, `c'(Φ v, ψ x) = c(v, x)` (isometries commute with `Exp` and
preserve `D`), the entropic plans of `(c', Φ#μ, ψ#P)` are exactly the pushforwards `(Φ × ψ)#π` of the entropic plans
`π` of `(c, μ, P)`; in particular, when the latter is unique (`thm:wellposed`), so is the former and
`π'_ε = (Φ × ψ)#π_ε`. -/
def equivariance_plan : Prop :=
  ∀ (V V' X X' : Type*) [MeasurableSpace V] [MeasurableSpace V'] [MeasurableSpace X] [MeasurableSpace X']
    (Φ : V ≃ᵐ V') (ψ : X ≃ᵐ X') (c : V × X → ℝ≥0∞) (c' : V' × X' → ℝ≥0∞) (ε : ℝ) (μ : Measure V)
    (P : Measure X),
    IsProbabilityMeasure μ → IsProbabilityMeasure P → (∀ v x, c' (Φ v, ψ x) = c (v, x)) →
      {π' | IsEntPlanG c' ε (μ.map Φ) (P.map ψ) π'} =
          (fun π => π.map (Prod.map Φ ψ)) '' {π | IsEntPlanG c ε μ P π} ∧
        ∀ π, IsEntPlanG c ε μ P π → (∀ ρ, IsEntPlanG c ε μ P ρ → ρ = π) →
          ∀ π', IsEntPlanG c' ε (μ.map Φ) (P.map ψ) π' → π' = π.map (Prod.map Φ ψ)

/-- G `prop:equivariance`, the quantiles: if the conditional laws transform as `π'(· | Φ v) = ψ#π(· | v)` (`ψ` an
isometry of the curve space), then `ψ` maps the set of quantiles at `v` onto the set of quantiles at `Φ v`, and when
the quantile at `v` is unique (`prop:quantile`(b)), so is the one at `Φ v`, with `Q'(Φ v) = ψ(Q(v))`. -/
def equivariance_quantile : Prop :=
  ∀ (V V' X X' : Type*) [PseudoEMetricSpace X] [MeasurableSpace X] [BorelSpace X] [PseudoEMetricSpace X']
    [MeasurableSpace X'] [BorelSpace X'] (Φ : V → V') (ψ : X ≃ᵢ X') (κ : V → Measure X) (κ' : V' → Measure X'),
    (∀ v, κ' (Φ v) = (κ v).map ψ) →
      ∀ v, ψ '' frechetSet (κ v) = frechetSet (κ' (Φ v)) ∧
        ∀ q, frechetSet (κ v) = {q} → frechetSet (κ' (Φ v)) = {ψ q}

/-- G `prop:equivariance`, ranks and depths: if `dφ = Φ` is a linear isometry of the field spaces and the conditional
reference laws transform as `π'(· | φ ∘ x) = Φ#π(· | x)`, then `F'(φ ∘ x) = Φ F(x)` (`F(x) = ∫ v π(dv | x)`) and
`R'(φ ∘ x) = R(x)` (`R(x) = ∫ ‖v‖ π(dv | x)`), hence `D'(φ ∘ x) = 1 − R'(φ ∘ x) = D(x)` and the rank radius is
preserved. -/
def equivariance_rank : Prop :=
  ∀ (V V' X X' : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] [MeasurableSpace V]
    [BorelSpace V] [NormedAddCommGroup V'] [InnerProductSpace ℝ V'] [CompleteSpace V'] [MeasurableSpace V']
    [BorelSpace V'] (Φ : V ≃ₗᵢ[ℝ] V') (ψ : X → X') (lam : X → Measure V) (lam' : X' → Measure V'),
    (∀ x, lam' (ψ x) = (lam x).map Φ) →
      ∀ x, ∫ v, v ∂lam' (ψ x) = Φ (∫ v, v ∂lam x) ∧ ∫ v, ‖v‖ ∂lam' (ψ x) = ∫ v, ‖v‖ ∂lam x ∧
        ‖∫ v, v ∂lam' (ψ x)‖ = ‖∫ v, v ∂lam x‖

/-! #### SB `prop:embed` -/

/-- SB `prop:embed`, the corner `t = 1`: for any target `ν` and any plans `π_s` of `(R_s, ν)` (in particular the
comonotone `π*_0` at `ε = 0`, with `ν = ν^W`), the repair marginal at `t = 1` is `μ^ε_{s,1} = ν` for every `ε`, so the
deterministic repair is `h̃^flow_{1,ε}(x, s) = F_ν^{-1}(F_{R_s}(h(x)))`; and for atomless `R_s` the repaired
prediction has conditional law `ν` in each group (exact demographic parity), via the certified `thm:flow`(i). -/
def embed_corner : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (S : Ω → Fin 2) (U : Ω → ℝ) (ε : ℝ)
    (π : Fin 2 → Measure (ℝ × ℝ)) (ν : Measure ℝ),
    IsProbabilityMeasure P → Measurable S → Measurable U → IsProbabilityMeasure ν →
    (∀ s, IsProbabilityMeasure (π s)) → (∀ s, (π s).map Prod.snd = ν) →
      (∀ s, StatFormal.Wave9b.flowMap (StatFormal.Wave11b.condLaw P S s U)
          (StatFormal.Wave4b.endpointMixture1 ε 1 (π s)) =
          fun u => ν.quantile (cdf (StatFormal.Wave11b.condLaw P S s U) u)) ∧
      ∀ s, P (S ⁻¹' {s}) ≠ 0 → NullSingletonClass (StatFormal.Wave11b.condLaw P S s U) →
        StatFormal.Wave11b.condLaw P S s (fun ω => StatFormal.Wave9b.flowMap (StatFormal.Wave11b.condLaw P S s U)
          (StatFormal.Wave4b.endpointMixture1 ε 1 (π s)) (U ω)) = ν

/-- SB `prop:embed`, the corner `t = 0`: for any plan `π_s` of `(R_s, ν)` and any `ε`, `μ^ε_{s,0} = R_s`, and the
deterministic repair is the identity, `h̃^flow_{0,ε} = h`, almost surely given `S = s` (no atomless hypothesis:
`F_R^{-1} ∘ F_R = id` `R`-a.e. for every law `R`). -/
def embed_identity : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (S : Ω → Fin 2) (U : Ω → ℝ) (ε : ℝ) (s : Fin 2)
    (π : Measure (ℝ × ℝ)),
    IsProbabilityMeasure P → Measurable S → Measurable U → P (S ⁻¹' {s}) ≠ 0 →
    π.map Prod.fst = StatFormal.Wave11b.condLaw P S s U →
      StatFormal.Wave4b.endpointMixture1 ε 0 π = StatFormal.Wave11b.condLaw P S s U ∧
      (fun ω => StatFormal.Wave9b.flowMap (StatFormal.Wave11b.condLaw P S s U)
          (StatFormal.Wave4b.endpointMixture1 ε 0 π) (U ω)) =ᵐ[P[|S ⁻¹' {s}]] U

/-! #### T `thm:coverage-error` -/

/-- T `thm:coverage-error`, with `lem:exp` DISCHARGED through the frozen Wave 22b `LengthBound` and `L_b = Lb D b`
(`eq:L`, assumed finite as there), and CONDITIONAL on the representation `X = Q^m(U)` (`thm:population`): fields
`H` (separable), the curve of a field `v` is `E_m v = (t ↦ Exp_{m(t)}((ι v)(t)) ∈ M)` (`Ex t = Exp_{m(t)}`, `D t w`
its differential), `ι` linear with `sup_t ‖(ι v)(t)‖ ≤ Λ‖v‖_H` (`eq:Hembed`); both tangent maps have pointwise norms
at most `b`; the fresh trajectory is `X = E_m(Q(U))`, `U ∼ μ`. If a fitted tube `𝒯(t)` contains `E_m(Q̂(u))(t)` for
every `u ∈ A` and `t`, and `μ(A) ≥ p̲`, then for `δ > 0` there is a measurable event, of probability
`≥ p̲ − L_b²Λ²δ^{-2} ∫ ‖Q̂ − Q‖² dμ`, on which `X(t)` lies within `δ` of a point of `𝒯(t)` for every `t` (so
`X(t) ∈ 𝒯^δ(t)` for all `t`). -/
def coverage_error : Prop :=
  ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [SecondCountableTopology H] [MeasurableSpace H]
    [BorelSpace H] (Tm V W M Ω : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
    [NormedSpace ℝ W] [PseudoEMetricSpace M] [MeasurableSpace Ω] (P : Measure Ω) (U : Ω → H)
    (μ : Measure H) (Ex : Tm → V → M) (D : Tm → V → V →L[ℝ] W) (ι : H →ₗ[ℝ] (Tm → V)) (Q Qhat : H → H)
    (tube : Tm → Set M) (A : Set H) (b Λ pbar δ : ℝ),
    IsProbabilityMeasure P → Measurable U → P.map U = μ → Measurable Q → Measurable Qhat → MeasurableSet A →
    0 < δ → 0 ≤ Λ → StatFormal.OTFD.Wave22b.LengthBound Ex D → StatFormal.OTFD.Wave22b.Lb D b ≠ ⊤ →
    (∀ x t, ‖ι x t‖ ≤ Λ * ‖x‖) → (∀ u t, ‖ι (Q u) t‖ ≤ b) → (∀ u t, ‖ι (Qhat u) t‖ ≤ b) →
    (∀ u ∈ A, ∀ t, Ex t (ι (Qhat u) t) ∈ tube t) → ENNReal.ofReal pbar ≤ μ A →
      ∃ Ev : Set Ω, MeasurableSet Ev ∧
        (∀ ω ∈ Ev, ∀ t, ∃ y ∈ tube t, edist (Ex t (ι (Q (U ω)) t)) y ≤ ENNReal.ofReal δ) ∧
        ENNReal.ofReal pbar - ENNReal.ofReal (((StatFormal.OTFD.Wave22b.Lb D b).toReal * Λ) ^ 2 / δ ^ 2) *
            ∫⁻ u, ‖Qhat u - Q u‖ₑ ^ 2 ∂μ ≤ P Ev

/-! #### T `lem:cf-schedule` (toolkit:401) -/

/-- T `lem:cf-schedule` (`toolkit:401`), the diagonal-schedule core, CONDITIONAL on C Theorem 4.2 at fixed strength:
for each query `a` in a finite set (the two charts `x, x'`), `E^{(a)}_n(σ)` is the (measurable) supremum over `ξ ∈ D` of
the `W₁` distance between the weighted law at strength `σ` and the population smoothed law `ν̄^{(a)}_ξ[σ]`, which tends
to `0` almost surely at every fixed `σ > 0` (C Theorem 4.2, hypothesis); `β^{(a)}(σ) → 0` as `σ ↓ 0` is the smoothing
bias; and the error `err^{(a)}_n(σ) = sup_ξ W₁(Σ_i w_i(ξ) δ_{Z_i^{⟨a⟩}}, ν^{(a)}_ξ) ≥ 0` obeys the triangle inequality
`err ≤ E + β`. Then one deterministic schedule `σ_n ↓ 0` (positive, nonincreasing), the same for every query because
the weights depend on the covariates only, makes `err^{(a)}_n(σ_n) → 0` almost surely for every `a` simultaneously. -/
def cf_schedule : Prop :=
  ∀ (Ω ι : Type*) [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω) (E err : ι → ℕ → ℝ → Ω → ℝ) (β : ι → ℝ → ℝ),
    IsProbabilityMeasure P → (∀ a n σ, Measurable (E a n σ)) →
    (∀ a σ, 0 < σ → ∀ᵐ ω ∂P, Tendsto (fun n => E a n σ ω) atTop (𝓝 0)) →
    (∀ a, Tendsto (β a) (𝓝[>] 0) (𝓝 0)) →
    (∀ a n σ ω, 0 < σ → 0 ≤ err a n σ ω ∧ err a n σ ω ≤ E a n σ ω + β a σ) →
      ∃ σ : ℕ → ℝ, (∀ n, 0 < σ n) ∧ Antitone σ ∧ Tendsto σ atTop (𝓝 0) ∧
        ∀ᵐ ω ∂P, ∀ a, Tendsto (fun n => err a n (σ n) ω) atTop (𝓝 0)

/-! #### T `cor:randomised` (theory:374) -/

/-- T `cor:randomised` (`theory:374`), CONDITIONAL on the in-sample and out-of-sample mean-square dual bounds of
Rigollet–Stromme (arXiv:2206.13472v1: (4.3) with Lemma 14, equal sample sizes, normalisation `ν_n(g) = 0` with
the population pair shifted by `ν_n(g⋆)`; unequal sizes via González-Sanz–Hundrieser; `thm:rates`) and on the Dvoretzky–Kiefer–Wolfowitz inequality with Massart's
constant (its consequence `E sup_ρ |μ_{n_ref}{‖u‖ ≤ ρ} − c_K(ρ)| ≤ (π/(2n_ref))^{1/2}`). Data on `(Ω, P)`: reference draws
`U_l` (`l < n_ref`), fitted potentials `f̂_l`, `ĝ`, population potentials `f̄`, `ḡ` jointly normalised
(`∫ exp((f̄(u) + ḡ(z) − c(u,z))/ε) ν_K(dz) = 1` for every `u`), all exponents `≤ M` (bounded potentials and cost). Then
`E sup_ρ |P{‖U*‖ ≤ ρ | data} − c_K(ρ)| ≤ C_ε (n^{-1/2} + n_ref^{-1/2})` with `C_ε = 2e^M A^{1/2} + (π/2)^{1/2}`. -/
def randomised_calibration : Prop :=
  ∀ (K N n : ℕ) (Ω Z : Type*) [MeasurableSpace Ω] [MeasurableSpace Z] (P : Measure Ω) (ν : Measure Z)
    (μK : Measure (EuclideanSpace ℝ (Fin K))) (U : Fin N → Ω → EuclideanSpace ℝ (Fin K)) (fh : Ω → Fin N → ℝ)
    (gh : Ω → Z → ℝ) (fb : EuclideanSpace ℝ (Fin K) → ℝ) (gb : Z → ℝ) (c : EuclideanSpace ℝ (Fin K) → Z → ℝ)
    (ε M A : ℝ),
    IsProbabilityMeasure P → IsProbabilityMeasure ν → 0 < N → 0 < n → 0 < ε → 0 ≤ A →
    (∀ l, Measurable (U l)) → Measurable fh → Measurable (Function.uncurry gh) → Measurable fb →
    Measurable gb → Measurable (Function.uncurry c) →
    (∀ ω l z, (fh ω l + gh ω z - c (U l ω) z) / ε ≤ M) → (∀ u z, (fb u + gb z - c u z) / ε ≤ M) →
    (∀ u, ∫ z, Real.exp ((fb u + gb z - c u z) / ε) ∂ν = 1) →
    ∫⁻ ω, ENNReal.ofReal ((N : ℝ)⁻¹ * ∑ l, ((fh ω l - fb (U l ω)) / ε) ^ 2) ∂P ≤
      ENNReal.ofReal (A * (1 / n + 1 / N)) →
    ∫⁻ ω, ∫⁻ z, ENNReal.ofReal (((gh ω z - gb z) / ε) ^ 2) ∂ν ∂P ≤ ENNReal.ofReal (A * (1 / n + 1 / N)) →
    ∫⁻ ω, ⨆ ρ : ℝ, ENNReal.ofReal |empNormCDF (fun l => U l ω) ρ - StatFormal.Wave23a.cdfK μK (fun u => ‖u‖) ρ| ∂P ≤
      ENNReal.ofReal (Real.sqrt (Real.pi / (2 * N))) →
      ∫⁻ ω, ⨆ ρ : ℝ, ENNReal.ofReal |randCDF ν ε (fun l => U l ω) (fh ω) (gh ω) c ρ -
          StatFormal.Wave23a.cdfK μK (fun u => ‖u‖) ρ| ∂P ≤
        ENNReal.ofReal ((2 * Real.exp M * Real.sqrt A + Real.sqrt (Real.pi / 2)) *
          (1 / Real.sqrt n + 1 / Real.sqrt N))

/-! #### T `cor:smooth` (`eq:smooth`) -/

/-- T `cor:smooth`, the exact-solver step: for a grid plan of Gibbs form
`π_{ij} = a_i n^{-1} exp((g_i + f_j − ‖ξ_i − y_j‖²)/ε)` (exact entropic solver, uniform target label weights), the
conditional target barycenter at every grid atom is the smooth extension: `Σ_j π_{ij} y_j / Σ_j π_{ij} = Q^sm(ξ_i)`
(the source dual terms `g_i` cancel). -/
def smooth_exact : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (m n : ℕ) (ε : ℝ) (a : Fin m → ℝ) (ξ : Fin m → E)
    (g : Fin m → ℝ) (f : Fin n → ℝ) (y : Fin n → E),
    0 < n → (∀ i, 0 < a i) →
      ∀ i, (∑ j, a i * (n : ℝ)⁻¹ * Real.exp ((g i + f j - ‖ξ i - y j‖ ^ 2) / ε))⁻¹ •
          ∑ j, (a i * (n : ℝ)⁻¹ * Real.exp ((g i + f j - ‖ξ i - y j‖ ^ 2) / ε)) • y j = smoothMap ε f y (ξ i)

/-- T `cor:smooth`, the review's derivative bound: the Jacobian of `Q^sm` is `(2/ε) Cov_{q}(y)`, so for data with
`‖y_j‖ ≤ B`, `Q^sm` is `2B²/ε`-Lipschitz: `‖Q^sm(x) − Q^sm(x')‖ ≤ (2B²/ε) ‖x − x'‖`. -/
def smooth_lipschitz : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n : ℕ) (ε B : ℝ) (f : Fin n → ℝ) (y : Fin n → E),
    0 < ε → (∀ j, ‖y j‖ ≤ B) → ∀ x x', ‖smoothMap ε f y x - smoothMap ε f y x'‖ ≤ 2 * B ^ 2 / ε * ‖x - x'‖

/-- T `cor:smooth`, CONDITIONAL on `thm:empirical` (`eq:empQ`, hypothesis: `e_n² = ∫ ‖Q̄_n − Q_ν‖² dμ → 0`): with
`Q̄_n(u) = Q^sm_n(ξ_n(u))` (the binned barycentric estimator, `eq:binned`, by `smooth_exact` at the grid atoms) and
bounded data `‖y_{nj}‖ ≤ B`, `∫ ‖Q^sm_n(P_{K_n} u) − Q̄_n(u)‖² dμ ≤ (2B²/ε_n)² h_n²`, `h_n² = ∫ ‖P_{K_n} u − ξ_n(u)‖² dμ`;
hence if `h_n/ε_n → 0`, `eq:empQ` holds with `Q^sm_n`. -/
def smooth_consistency : Prop :=
  ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [SecondCountableTopology H] [MeasurableSpace H]
    [BorelSpace H] (μ : Measure H) (P ξ Qbar : ℕ → H → H) (Qν : H → H) (ε : ℕ → ℝ) (m : ℕ → ℕ)
    (f : ∀ n, Fin (m n) → ℝ) (y : ∀ n, Fin (m n) → H) (B : ℝ),
    (∀ n, 0 < ε n) → (∀ n j, ‖y n j‖ ≤ B) → (∀ n, Measurable (P n)) → (∀ n, Measurable (ξ n)) → Measurable Qν →
    (∀ n u, Qbar n u = smoothMap (ε n) (f n) (y n) (ξ n u)) →
      (∀ n, ∫⁻ u, ‖smoothMap (ε n) (f n) (y n) (P n u) - Qbar n u‖ₑ ^ 2 ∂μ ≤
          ENNReal.ofReal ((2 * B ^ 2 / ε n) ^ 2) * ∫⁻ u, ‖P n u - ξ n u‖ₑ ^ 2 ∂μ) ∧
      (Tendsto (fun n => ∫⁻ u, ‖Qbar n u - Qν u‖ₑ ^ 2 ∂μ) atTop (𝓝 0) →
        Tendsto (fun n => ENNReal.ofReal ((ε n)⁻¹ ^ 2) * ∫⁻ u, ‖P n u - ξ n u‖ₑ ^ 2 ∂μ) atTop (𝓝 0) →
        Tendsto (fun n => ∫⁻ u, ‖smoothMap (ε n) (f n) (y n) (P n u) - Qν u‖ₑ ^ 2 ∂μ) atTop (𝓝 0))

/-! #### ICL `lem:e-measures` -/

/-- ICL `lem:e-measures` (i), population part, and (ii) (`as:compact`–`as:kernel`): each `μ_θ` is a probability
measure, `θ ↦ μ_θ` is weakly continuous (`θ ↦ ∫ φ dμ_θ` is continuous for every continuous, hence bounded, `φ` on the
compact `𝒵`), `(θ, z) ↦ ρ_{μ_θ}(z)` is continuous, with values in `[K_min, K_max]`. -/
def e_measures_pop : Prop :=
  ∀ (Θ Z : Type) [MetricSpace Θ] [CompactSpace Θ] [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] (P0 : Measure Z) (s : Θ → Z → ℝ) (K : Z → Z → ℝ) (sm sp Kmin Kmax : ℝ),
    IsProbabilityMeasure P0 → Continuous (Function.uncurry s) → 0 < sm → (∀ θ z, sm ≤ s θ z ∧ s θ z ≤ sp) →
    Continuous (Function.uncurry K) → 0 < Kmin → (∀ z z', Kmin ≤ K z z' ∧ K z z' ≤ Kmax) →
      (∀ θ, IsProbabilityMeasure (ctxLawT P0 s θ)) ∧
      (∀ φ : Z → ℝ, Continuous φ → Continuous fun θ => ∫ z, φ z ∂ctxLawT P0 s θ) ∧
      Continuous (fun p : Θ × Z => coverRho K (ctxLawT P0 s p.1) p.2) ∧
      ∀ θ z, Kmin ≤ coverRho K (ctxLawT P0 s θ) z ∧ coverRho K (ctxLawT P0 s θ) z ≤ Kmax

/-- ICL `lem:e-measures` (iii), for an i.i.d. `P₀` pool `X` and an i.i.d. `P₀` validation sequence `Y` (nested samples,
`as:compact`; the compact-parametric Glivenko–Cantelli principle is proved in the route, not assumed; `n, m → ∞`):
almost surely
`sup_{θ,z} |ρ_{μ_{θ,n}}(z) − ρ_{μ_θ}(z)| → 0` and `sup_θ |P_m log ρ_{μ_{θ,n}} − P₀ log ρ_{μ_θ}| → 0`. -/
def e_measures_emp : Prop :=
  ∀ (Θ Z Ω : Type) [MetricSpace Θ] [CompactSpace Θ] [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] [MeasurableSpace Ω] (P : Measure Ω) (P0 : Measure Z) (X Y : ℕ → Ω → Z) (m : ℕ → ℕ)
    (s : Θ → Z → ℝ) (K : Z → Z → ℝ) (sm sp Kmin Kmax : ℝ),
    IsProbabilityMeasure P0 → Continuous (Function.uncurry s) → 0 < sm → (∀ θ z, sm ≤ s θ z ∧ s θ z ≤ sp) →
    Continuous (Function.uncurry K) → 0 < Kmin → (∀ z z', Kmin ≤ K z z' ∧ K z z' ≤ Kmax) →
    Tendsto m atTop atTop → IsProbabilityMeasure P →
    (∀ j, Measurable (X j)) → iIndepFun X P → (∀ j, P.map (X j) = P0) →
    (∀ j, Measurable (Y j)) → iIndepFun Y P → (∀ j, P.map (Y j) = P0) →
      ∀ᵐ ω ∂P,
        TendstoUniformly (fun n (p : Θ × Z) => coverRho K (empCtxLaw s (fun i => X i ω) n p.1) p.2)
          (fun p => coverRho K (ctxLawT P0 s p.1) p.2) atTop ∧
        TendstoUniformly
          (fun n θ => empAvg (fun i => Y i ω) (m n)
            (fun z => Real.log (coverRho K (empCtxLaw s (fun i => X i ω) n θ) z)))
          (fun θ => ∫ z, Real.log (coverRho K (ctxLawT P0 s θ) z) ∂P0) atTop

/-- ICL `lem:e-measures` (i), empirical part, for an i.i.d. `P₀` pool `X` (nested samples), with the quantifiers of the
proof's first step: for every continuous `φ`, almost surely
`∫ φ dμ_{θ_n,n} → ∫ φ dμ_θ` along every `θ_n → θ` (the event depends on `φ`; the paper's single event for all `φ`
needs a countable convergence-determining class, not formalised). -/
def e_measures_emp_weak : Prop :=
  ∀ (Θ Z Ω : Type) [MetricSpace Θ] [CompactSpace Θ] [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] [MeasurableSpace Ω] (P : Measure Ω) (P0 : Measure Z) (X : ℕ → Ω → Z) (s : Θ → Z → ℝ)
    (sm sp : ℝ) (φ : Z → ℝ),
    IsProbabilityMeasure P0 → Continuous (Function.uncurry s) → 0 < sm → (∀ θ z, sm ≤ s θ z ∧ s θ z ≤ sp) →
    Continuous φ → IsProbabilityMeasure P →
    (∀ j, Measurable (X j)) → iIndepFun X P → (∀ j, P.map (X j) = P0) →
      ∀ᵐ ω ∂P, ∀ (θn : ℕ → Θ) (θ : Θ), Tendsto θn atTop (𝓝 θ) →
        Tendsto (fun n => ∫ z, φ z ∂empCtxLaw s (fun i => X i ω) n (θn n)) atTop (𝓝 (∫ z, φ z ∂ctxLawT P0 s θ))

/-! #### ICL `lem:e-ulln` -/

/-- ICL `lem:e-ulln`, for i.i.d. `P₀` pool and validation sequences (nested samples), CONDITIONAL on the uniform
convergence of the risk term (`lem:e-vstat` with `H_θ = L̄` plus the Glivenko–Cantelli step with
index `z_{1:M}`; hypothesis on the abstract risk terms `R_{n,m}`, `R`): if `n, m → ∞` and `λ_{·,n} → λ_·`, then
almost surely `sup_θ |J^iid_{n,m}(θ) − J(θ)| → 0`, where
`J = R − λ_cov P₀ log ρ_{μ_θ} + λ_KL KL(μ_θ‖P₀)` and
`J^iid_{n,m} = R_{n,m} − λ_{cov,n} P_m log ρ_{μ_{θ,n}} + λ_{KL,n} KL(μ_{θ,n}‖P_n)` (KL in closed form). -/
def e_ulln : Prop :=
  ∀ (Θ Z Ω : Type) [MetricSpace Θ] [CompactSpace Θ] [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] [MeasurableSpace Ω] (P : Measure Ω) (P0 : Measure Z) (X Y : ℕ → Ω → Z) (m : ℕ → ℕ)
    (s : Θ → Z → ℝ) (K : Z → Z → ℝ) (sm sp Kmin Kmax : ℝ) (R : Θ → ℝ) (Rn : ℕ → Ω → Θ → ℝ)
    (lc lK : ℝ) (lcn lKn : ℕ → ℝ),
    IsProbabilityMeasure P0 → Continuous (Function.uncurry s) → 0 < sm → (∀ θ z, sm ≤ s θ z ∧ s θ z ≤ sp) →
    Continuous (Function.uncurry K) → 0 < Kmin → (∀ z z', Kmin ≤ K z z' ∧ K z z' ≤ Kmax) →
    Tendsto m atTop atTop → IsProbabilityMeasure P →
    (∀ j, Measurable (X j)) → iIndepFun X P → (∀ j, P.map (X j) = P0) →
    (∀ j, Measurable (Y j)) → iIndepFun Y P → (∀ j, P.map (Y j) = P0) →
    Tendsto lcn atTop (𝓝 lc) → Tendsto lKn atTop (𝓝 lK) →
    (∀ᵐ ω ∂P, TendstoUniformly (fun n => Rn n ω) R atTop) →
      ∀ᵐ ω ∂P, TendstoUniformly
        (fun n θ => Rn n ω θ - lcn n * empAvg (fun i => Y i ω) (m n)
            (fun z => Real.log (coverRho K (empCtxLaw s (fun i => X i ω) n θ) z)) +
          lKn n * klEmp s (fun i => X i ω) n θ)
        (fun θ => R θ - lc * ∫ z, Real.log (coverRho K (ctxLawT P0 s θ) z) ∂P0 + lK * klPop P0 s θ) atTop

/-! #### NN `prop:average-offset-penalty` -/

/-- NN `prop:average-offset-penalty`, CONDITIONAL on `lem:marked-block-transform` (`eq:marked-pgf-asymptotic`,
hypothesis, assumed only for `z ∈ (0,1]^q`; the lemma states it for all `z_i > 0`): for a representative `θ*_q`
and `σ > 0`, `E_{U_{q,m}}[e^{−λ_s/2}] ∼ (w_m/m)^{η_q}`, `w_m = W(m)`. -/
def average_offset_penalty : Prop :=
  ∀ (W : ℝ → ℝ) (din dout q : ℕ) (σ : ℝ) (θs : Fin q → StatFormal.NNFibers.Wave1.Neuron din dout),
    StatFormal.Wave22c.IsLambertW W → 0 < σ →
    (∀ z : Fin q → ℝ, (∀ i, 0 < z i ∧ z i ≤ 1) →
      (fun m : ℕ => markedPGF q m z) ~[atTop]
        (fun m : ℕ => ∏ i, (Real.exp (z i * W m) - 1) / (Real.exp (W m) - 1))) →
      (fun m : ℕ => StatFormal.Wave22c.avgOffset σ θs m) ~[atTop]
        (fun m : ℕ => (W m / m) ^ StatFormal.Wave22c.etaQ σ θs)

/-! #### NN `lem:tube-reduction` -/

/-- NN `lem:tube-reduction`, second claim (`eq:Qtube-is-Uratio`), CONDITIONAL on the first claim at `q = r` and
`q = k` (`Ḡ_q(m) ∼ e^{−t} U_q(m)/T(q,m)`, hypotheses): `Q^tube_{r,k}(m) ∼ U_r(m)/U_k(m)`. -/
def tube_reduction_ratio : Prop :=
  ∀ (din dout r k : ℕ) (δ σ : ℝ) (θr : Fin r → StatFormal.NNFibers.Wave1.Neuron din dout)
    (θk : Fin k → StatFormal.NNFibers.Wave1.Neuron din dout),
    (fun m : ℕ => StatFormal.Wave22c.Gbar din dout δ σ θr m) ~[atTop]
        (fun m : ℕ => Real.exp (-StatFormal.Wave22c.tubeT δ σ) * StatFormal.Wave22c.Ubar din dout δ σ θr m /
          (StatFormal.NNFibers.T r m : ℝ)) →
    (fun m : ℕ => StatFormal.Wave22c.Gbar din dout δ σ θk m) ~[atTop]
        (fun m : ℕ => Real.exp (-StatFormal.Wave22c.tubeT δ σ) * StatFormal.Wave22c.Ubar din dout δ σ θk m /
          (StatFormal.NNFibers.T k m : ℝ)) →
      (fun m : ℕ => StatFormal.Wave22c.Qtube din dout δ σ θr θk m) ~[atTop]
        (fun m : ℕ => StatFormal.Wave22c.Ubar din dout δ σ θr m / StatFormal.Wave22c.Ubar din dout δ σ θk m)

/-- NN `lem:tube-reduction`, the last step of the proof: `P_a(t) = (t^a/Γ(a+1)) e^{−t} (1 + O(t/a))`, with the explicit
two-sided bound `e^{−t} ρ(a) ≤ P_a(t) ≤ e^{−t} ρ(a) (1 + t e^t/(a+1))`, `ρ(a) = t^a/Γ(a+1)` (frozen `rhoG`), for every
`a, t > 0` (uniform in the shape `a = a(K)`). -/
def tube_gamma_shape : Prop :=
  ∀ a t : ℝ, 0 < a → 0 < t →
    Real.exp (-t) * StatFormal.Wave22c.rhoG t a ≤ incGammaReg a t ∧
      incGammaReg a t ≤ Real.exp (-t) * StatFormal.Wave22c.rhoG t a * (1 + t * Real.exp t / (a + 1))

/-- PARTIAL DISCHARGE of the frozen Wave 22c `thm:tube-singleton` (`tube_singleton`): its premise
`eq:Qtube-is-Uratio` replaced by the first claim of `lem:tube-reduction` at `q = r, k` (via `tube_reduction_ratio`);
the cancellation premise `Φ_r/Φ_k → 1` is kept. -/
def tube_singleton_discharged : Prop :=
  ∀ (din dout r k : ℕ) (δ σ : ℝ) (θr : Fin r → StatFormal.NNFibers.Wave1.Neuron din dout)
    (θk : Fin k → StatFormal.NNFibers.Wave1.Neuron din dout),
    dout + 2 < din → 1 ≤ dout → r < k → 0 < δ → 0 < σ →
    (fun m : ℕ => StatFormal.Wave22c.Gbar din dout δ σ θr m) ~[atTop]
        (fun m : ℕ => Real.exp (-StatFormal.Wave22c.tubeT δ σ) * StatFormal.Wave22c.Ubar din dout δ σ θr m /
          (StatFormal.NNFibers.T r m : ℝ)) →
    (fun m : ℕ => StatFormal.Wave22c.Gbar din dout δ σ θk m) ~[atTop]
        (fun m : ℕ => Real.exp (-StatFormal.Wave22c.tubeT δ σ) * StatFormal.Wave22c.Ubar din dout δ σ θk m /
          (StatFormal.NNFibers.T k m : ℝ)) →
    Tendsto (fun m : ℕ => StatFormal.Wave22c.PhiS din dout δ σ θr m / StatFormal.Wave22c.PhiS din dout δ σ θk m)
      atTop (𝓝 1) →
      (fun m : ℕ => StatFormal.Wave22c.Qtube din dout δ σ θr θk m) ~[atTop]
          (fun m : ℕ => StatFormal.Wave22c.zetaQ σ θr / StatFormal.Wave22c.zetaQ σ θk *
            ((dout : ℝ) * σ ^ 2 / δ ^ 2) ^ (((k : ℝ) - r) * din / 2) *
            (m : ℝ) ^ (((k : ℝ) - r) * ((din : ℝ) / 2 - 1))) ∧
        0 < ((k : ℝ) - r) * ((din : ℝ) / 2 - 1) ∧
        Tendsto (fun m : ℕ => StatFormal.Wave22c.Qtube din dout δ σ θr θk m) atTop atTop ∧
        3 / 2 ≤ |StatFormal.Wave22c.kappaD din dout|

end Claims

end StatFormal.Wave24c
