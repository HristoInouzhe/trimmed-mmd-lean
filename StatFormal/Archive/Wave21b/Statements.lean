import StatFormal.Archive.Wave9a.Statements
import StatFormal.Archive.RobustEquality.AllPairs.Statements
import StatFormal.Archive.Wave17a.Statements
import StatFormal.Archive.OTFD.Wave6b.Statements
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# FROZEN STATEMENTS — wave 21b (QUEUE rows 232–240): robust equality JASA `prop:fl-negent`, `prop:envelope`,
# `thm:ad-oracle`; otfd R `cor:uncertainty` (with `thm:nullmass`(a)), A `prop:integrated-sieve-strong`,
# C `thm:conditional-band-limits`, `cor:conditional-test-coverage`, T `thm:rates`, `thm:tubes`

Sources (verbatim in `lean-formalisation/inventory/extracted/{robust-equality-jasa,otfd-R_robustness,otfd-A_sieves,
otfd-C_conditional,otfd-T_tangent}.md`; current text after the 2026-10-13/14/15 corrections; JASA paths under
`robust-equality-outcomes-under-distribution-shift/jasa/`, otfd paths under `otfd/papers/`):
* JASA `prop:fl-negent` (`supp_calibration.tex:98-108`, proof `:110-118`).
* JASA `prop:envelope` (`supp_proofs.tex:333-362`, proof `:364-377`), with the reference convention (`:14-23`: a
  reference is a measure with `0 < ν(K) ≤ 1`) and `Λ^𝒩_s` (`main.tex:349-352`).
* JASA `thm:ad-oracle` (`supp_calibration.tex:330-348`, proof `:350-363`), with `def:ad-rho` (`:295-306`),
  `lem:ad-linear` (`:250-258`, used through its proof), `lem:semidual` (frozen) and `prop:allpairs` (frozen `Vall`).
* otfd R `thm:nullmass`(a) (`R_robustness/sections/s3_infinite.tex:18-29`, proof `appendix_a.tex:161-176`) and
  `cor:uncertainty` (`s3_infinite.tex:41-49`), with `TD_H` (`s2_setting.tex:9`).
* otfd A `prop:integrated-sieve-strong` (`A_sieves/main.tex:800-825`), its last two sentences.
* otfd C `thm:conditional-band-limits` (`C_conditional/main.tex:666-685`, proof `supplement.tex:1121-1141`), with the
  population band `eq:conditional-pop-band` (`main.tex:630-641`), the fitted edges (`main.tex:302`) and
  `lem:full-support-region`; `cor:conditional-test-coverage` (`supplement.tex:2786-2794`, proof `:1161-1166`).
* otfd T `thm:rates` (`T_tangent/sec_tangent_theory.tex:339-351`, setting `:322-337`, proof `app_proofs.tex:159-180`)
  and `thm:tubes` (`sec_tangent_theory.tex:530-545`, proof `:546-554`), with `prop:caps` (`:470-490`, gaps and caps).
Imports the frozen `Wave9a` (`FW`, `rhoN`, `profileUB`, `testProd`; through it `RobustEquality/{Semidual,
SemidualStrong,Coverage}`: `gsoft`, `OTdisc`, `Setting`, `empMeasure`), `RobustEquality/AllPairs` (`Vall`), `Wave17a`
(`hPop`) and `OTFD/Wave6b` (`sphDist`, `sphExp`) statements, not copied. The `Foundations/Distances/TV` library file is
imported only through the frozen `SemidualStrong` statements. Mathlib (Gaussian on `ℝ`, convergence in measure,
independence, Haar measure on Euclidean space, `Measure.support`, `essSup`) otherwise.

Covered:
* `prop:fl-negent`: `fl_negent_formula` (`N(P̂ * U) = −log|E| + n⁻¹Σ_i E_U log(k(X_i+U)/n)`), `fl_negent_bdd_diff`
  (bounded differences `(1 + log n)/n`), `fl_negent_jensen` (`N(P̃) ≤ E N(P̂ * U)`), `fl_negent` (`N(P̃) ≤ N̂` with
  probability `≥ 1 − δ₁ − δ₂`).
* `prop:envelope`: (i) `envelope_i`, `envelope_i_free` (Dirac masses: the pointwise envelope), `envelope_i_classes`
  (monotone in the class; every class of references below `𝒫(K)`); (ii) `envelope_ii_phi` (the algebra, every `d`),
  `envelope_ii` (`d = 1`); (iii) `envelope_iii` (first display, `d = 1`, any `ν* ∈ 𝒫(K)`), `envelope_iii_gap`
  (`0 ≤ Λ^{𝒫(K)} − Λ^{𝒩_b} ≤ ½ log(1 + 2ab²/ε) + n⁻¹Σ log(1/(1 − η_i))`, `d = 1`).
* `thm:ad-oracle`: (i) `ad_oracle_i` (`Ô ≤ ρ_EL(r) ≤ ρ̂_N`); (ii) `ad_oracle_ii` (grid condition for every `f ∈ F_W`),
  `ad_oracle_ii_attained` (the printed "every maximising `f`" reading), `ad_oracle_ii_bound` (the display);
  (iii) `ad_oracle_iii`.
* `thm:nullmass`(a): `nullmass_a`; `cor:uncertainty`, class (a): `uncertainty_a`.
* `prop:integrated-sieve-strong`: `sieve_strong_radial`, `sieve_strong_signs_prob`, `sieve_strong_signs_L2`.
* `thm:conditional-band-limits`: `cond_band_two_sided` (`eq:conditional-two-sided`, uniformly in `p ≤ 1 − δ` and `t`,
  every selection `T`), `cond_band_one_sided` (vanishing edge deficit at a level with bounded essential range).
* `cor:conditional-test-coverage`: `cond_test_coverage_inflated`, `cond_test_coverage_nested`.
* `thm:rates`: `rates_cbar` (`c ≤ c̄`, and Rigollet–Stromme's `2max(sB_μ,B)² ≤ 4c̄`), `rates_barycentre` (barycentric
  maps stay in the `B`-ball), `rates_reconstruction` (the reconstruction bound given the coefficient rate).
* `thm:tubes`: `tubes_content` (containment by composition, content `≥ p̲`), `tubes_metric` ((ii), (iii) with abstract
  `Exp`), `tubes_sphere` ((ii), (iii) on `S^d`, `L_b = 1`), `tubes_nested` (gaps antitone, caps, enclosures and images
  nested).

Not covered (declared):
* fl-negent: that `jitDens` is the Lebesgue density of `P * U` (it is taken as the definition of `P̃`'s density).
* envelope: (ii)–(iii) for `d ≥ 2` (only the algebra of (ii) is stated for every `d`; the Gaussian integrals are the
  `d = 1` core of the queue note); the tail bound `∫π_b dν* ≤ e^{−(δ/b−√d)²/2}` (Gaussian norm concentration, missing
  from Mathlib); the remarks "vanishes when `π_b ≡ 0`", "keeps at most … nats", and the numerical check after the proof.
* ad-oracle: (i) second clause `ρ_EL(s) = sup{Θ(Q) : KL(P̂_m‖Q) ≤ s}` when `H(f) = sup_K g_f` (Honda–Takemura duality
  with `Q ∈ 𝒫(K)`; the virtual-point form used by (ii) is proved inside the route); (iii) the comparison factor
  `√(γ log(N/α)/log(2/α))` with the all-pairs margin (prose).
* nullmass/uncertainty: classes (b) (elliptical) and (c) (Gaussian-dominated); the separability/basis wording (any
  orthonormal sequence is used).
* sieve-strong: the main limit `eq:integrated-sieve-strong` (plan stability, L4), the existence/measurable versions of
  `F_{+,K}`, `𝔽_P`, and that the named references have no atom at `0` (hypothesis `P(Y = 0) = 0`).
* band-limits: the potential convergence (`prop:conditional-potentials`, L3) and the subgradient convergence deriving the
  premises from `ass:conditional-oos`; the limit `→ 0` of the right side of `eq:conditional-two-sided`; the outer-band
  deficit (immediate when the outer band contains the fitted one); in-probability versions (subsequence argument).
* test-coverage: `q_n` as a conditional probability given the training data (stated per realisation of the edges);
  the a.s./in-probability wrappers.
* rates: the two parametric bounds (Rigollet–Stromme sample complexity at fixed `ε`, missing); the fixed-design and
  split conditions; the constant's dependence on `c̄/ε`.
* tubes: compactness of `B_A(t)` (not needed); component boxes of `S_A(t)` and their nesting beyond `tubes_nested`;
  `lem:exp` on a general Riemannian `M` (only `S^d` and the abstract Lipschitz hypothesis).

Encodings (to be checked by the critic):
* fl-negent: `ℝ^d = EuclideanSpace ℝ (Fin d)`, `|E| = volR E` (`toReal` of a finite positive volume: `E` bounded
  measurable, `0 < |E|`); `k(y) = cntE` (sum of indicators of `y − X_j ∈ E`); `P̂ * U` has density `empJitDens = k/(n|E|)`,
  `P̃` density `jitDens = P{x : y − x ∈ E}/|E|`; `N(q) = ∫ q log q` (Bochner; integrability is proved in the routes, so
  no junk); `E_U` is the integral against `unifE E = |E|⁻¹ Leb|_E`; `supp P ⊆ K` is `P Kᶜ = 0`, `K` bounded measurable;
  sample `X ∼ P^n` (`Measure.pi`), jitters `U_{ir}` i.i.d. `unifE E` indexed by `Fin n × Fin R`, independent of `X`
  (product measure); events are measurable subsets (inner form); `0 < δ_i ≤ 1`; `1 ≤ n`, `1 ≤ R`.
* envelope: `K` any measurable type for (i) (paper: compact `K ⊆ ℝ^d`); a reference is `IsRef` (`0 < ν(K) ≤ 1`, finite);
  `φ_i = φ(x_i, ·)` any bounded measurable function per anchor (`n ≥ 1` anchors, `𝒩 ≠ ∅` in the first claim);
  `Λ^𝒩 = lamClass`, a `⨆` in `EReal` (`⊥` for `𝒩 = ∅`), right sides `sSup` of bounded nonempty real sets;
  `𝒫(K)` on a type is `probLaws`, on `K ⊆ ℝ` it is `probOn K` (probability laws on `ℝ` with `m(Kᶜ) = 0`);
  `𝒩_b = gaussClass` (restriction to `K` of the pushforward of `m ⊗ N(0,b²)` under addition), `K` measurable with
  positive Lebesgue measure (so members are references); (ii): `h = ⟨w,·⟩`, `λ = |w|²(1+t)`, basis `e : OrthonormalBasis
  (Fin (d+1))`, `e 0 = w/|w|` (0-indexed), `envA`; `d = 1`: `φ_i(y) = −a(y−x_i)²/ε` with any `a ≥ 0` (paper `a = t/(1+t)`);
  `π_b = piB`; (iii) `ν*` "attains" is `lamClass (probOn K) = avgLogMgf ν*`; positivity of the integrals in
  `envelope_iii` replaces `log 0 = −∞`.
* ad-oracle: fold setting of the frozen `Wave9a` (`Setting`, `OTdisc`, `F_W = FW`, `ρ̂_N = rhoN`, `U_N = profileUB`,
  `H : ℝ^k → ℝ` with `g_f ≤ H(f)` on `F_W × K`); `Ô = OTdisc` of `empMeasure y`; `Ū(φ;s) = elUB` (`sSup` in `ℝ`; the
  set contains the uniform weights for `s ≥ 0` and is bounded by `max(max_j φ(Y_j), H)`; `q_j > 0` because a zero weight
  makes the constraint `+∞`); `ρ_EL = rhoEL` in `EReal`; the geometric grid is `θ_l = γ^{−l}`, `l = 0, …, N−1`
  (`geomGrid`), `r = rThr`; the grid condition is multiplied out (`GridCond`, equivalent when `H > U_N`; at `U_N = H`
  it forces `P̂_m g_f = H`); `sd`, `P̂_m`, `J_{P̂_m}` are `empSd`, `empMean`, `Jemp`; `Gap_{P̂_m}(f) = Ô − J_{P̂_m}(f)` in
  `EReal`; (iii) `sup_{F_W}(H − inf_K g_f)` is any upper bound `b̄` of `H(f) − g_f` (weaker hypothesis), `m ≥ 2`.
* R: `𝓗` any real inner-product space with Borel σ-algebra; "orthonormal basis" is an orthonormal sequence `e : ℕ → 𝓗`
  (generalisation), coordinates `⟨e_k, ·⟩` independent under `μ` (`iIndepFun`) with atomless laws
  (`NullSingletonClass` of the pushforward); `TD_H = depthH` (`⨅` in `ℝ≥0∞`), `D_α = depthRegion`; `μ(D_α) = 0` is
  the outer measure (no measurability of `D_α` needed); `0 < α ≤ ½`, `0 < p ≤ 1`.
* A: `Y_K, Y : Ω → H` on any probability space, `H` a real normed space; `L²` convergence is `∫⁻ ‖·‖ₑ² → 0`;
  normalized sign `nsign c` with fixed convention `c` at `0`; convergence in probability is `TendstoInMeasure`.
* C: `ℝ^K = EuclideanSpace ℝ (Fin K)`; `h^pop = hPop` (frozen; `μ_K`-ess sup in `EReal`); fitted support
  `sup_{u∈A}⟨v,T(u)⟩ = supE` in `EReal`; `E_K` any bound of `sup_t ‖𝐞_K(t)‖`; two-sided: `A_p` compact convex with
  nonempty interior inside `supp μ_K` and `S`, `Q` continuous on `S` (for `∇χ_{K,x}` with `χ` differentiable near `S`),
  any map `T` with `sup_S ‖T − Q‖ ≤ η`; one-sided: `Q` essentially bounded on `A`, any fitted maps `Q_n → Q` pointwise
  `μ_K`-a.e. on `A` (the premise that the potential/subgradient argument delivers); `Δ_{n,p,x} → 0` as "for every `η > 0`,
  eventually both edge deficits `≤ η` for all `t`"; coverage: new projected response `∼ P_{K,x} = Q#μ_K`
  (`Measurable Q`), edges `U_n, L_n : 𝒯 → EReal` arbitrary (fitted or outer), `liminf q_n ≥ p` as "eventually
  `≥ p` (inflated) / `≥ p'` for every `p' < p` (nested)", coverage as a measurable event inside the band; strict nesting
  with a uniform gap `η` per `p' < p` (the printed `inf_t … > 0`).
* T: `c(u,z) = ½‖su − z‖²`, `s ≥ 0`; barycentres of a finite measure carried by the closed `B`-ball with a nonnegative
  integrable weight of positive mass; reconstruction: `ι_K` a continuous linear map into a normed space `F` (the sup
  norm of `eq:Hembed`) with `‖ι x‖ ≤ Λ‖x‖`, `E_m : F → Y` `L_b`-Lipschitz on the `ΛB`-ball (`eq:L`), maps bounded by
  `B`, expectations as iterated lower integrals; tubes: `Exp_{m(t)} = Ex t : V → M` abstract, `v̂_u(t) = vh u t`, the
  fitted law is the pushforward of `μ_K` under `u ↦ (t ↦ Exp v̂_u(t))` on `𝒯 → M` (product σ-algebra), its
  measurability and that of the membership event are hypotheses (as printed); the sphere uses the frozen
  `sphDist = arccos⟨·,·⟩`, `sphExp`; gaps `δ_j(A) = gapDelta` (`sInf` over the image of nonempty `A`, bounded below by
  `0`), caps `capEnt`, `capQuad`, `𝒫_κ = capPoly`, `S_A(t) = enclS`.

Critic notes:
* All 32 claims are proved in `Wave21b/Route{Negent,Envelope,AdOracle,Uncertainty,SieveStrong,CondBand,Tangent}.lean`
  (axioms: propext, Classical.choice, Quot.sound). Routes use the untrusted Foundations libraries
  `Concentration/EmpiricalProcess` (McDiarmid), `Bernstein/Hoeffding`, `SemiDiscrete/Coverage`, Mathlib's Hoeffding
  (`HasSubgaussianMGF`), the routes/proofs of Wave 9a (`RouteAdValid`), `RobustEquality/{Semidual,SemidualStrong,
  Coverage,AllPairs}`, Gaps1 (`RouteSupport`), Wave 17a (`RouteCondBand`), Wave 6b (`RouteSphere`) and Tau Ceti
  (`Quantile`) — routes only.
* No statement was found false. `fl_negent` holds as printed (the case `n = 1`, where `log n = 0`, is degenerate but true).
  `fl_negent` uses the same `jitDens` encoding as Wave 21a's `prop:fl-radius` hypothesis (definitionally).
* ad-oracle (ii): the printed hypothesis "every maximising `f`" is vacuous when `ρ̂_N` is not attained; both the
  "every `f ∈ F_W`" form and the attained form are stated. (ii) needs the equality direction of Honda–Takemura with the
  virtual point; the route proves it on the finite simplex (the concave `F̂_t` is maximised at `θ* ∈ [0,1]` and the
  tilted weights `1/(m(1 − θ*z_j))` plus the mass at `H` are feasible).
* Near-definitional cores (the queue notes' L1/L2 cores): `tubes_content`, `tubes_metric` and `rates_reconstruction` are
  compositions of their hypotheses; `tubes_sphere` instantiates them with the certified `eq:sphereone` of Wave 6b
  (`Exp` of `S^d` is `1`-Lipschitz, `d(m, Exp_m v) ≤ ‖v‖`); the genuinely new content of `thm:tubes` is small, as the
  queue note anticipates ("no injectivity needed" is what makes it Lean-friendly).
* Generalisations: envelope (i) on any measurable space; envelope (ii)/(iii) for any `a ≥ 0` and any measurable `K` of
  positive length; `envelope_iii` for any `ν* ∈ 𝒫(K)`; nullmass (a) for any orthonormal sequence; band limits for any
  measure `μ_K` and any selection.

* Critic (2026-10-15): ACCEPT / ACCEPT-WITH-NOTE except `tubes_metric`, which is a TAUTOLOGY (part (ii) is `le_trans`
  of its own hypothesis, (iii) instantiates the Lipschitz hypothesis): it is kept as a helper but NOT registered as a
  certified target; `thm:tubes` (ii),(iii) are covered only on `S^d` (`tubes_sphere`). Partial items: envelope (d = 1),
  ad-oracle (one clause of (i) declared; `ad_oracle_ii_attained` is the non-vacuous reading), A sieve-strong (only the
  "Consequently" sentences, given the main limit), T rates (auxiliary; Rigollet–Stromme not covered). C band limits /
  test coverage are CONDITIONAL on premises one convex-analysis step beyond `prop:conditional-potentials` (uncovered).
  Paper S4 (DEFECTS #69): `thm:ad-oracle`(ii) "every maximising f" is vacuous when `ρ̂_N` is not attained.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/
set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave21b

open StatFormal.RobustEquality.Semidual StatFormal.RobustEquality.SemidualStrong
open StatFormal.Wave9a (FW rhoN profileUB testProd)

/-! ### JASA `prop:fl-negent` -/

section Negent
variable {d : ℕ}

/-- `|E|`, the Lebesgue volume of `E ⊆ ℝ^d`, as a real number. -/
def volR (E : Set (EuclideanSpace ℝ (Fin d))) : ℝ := (volume E).toReal

/-- `k(y) = #{j ≤ n : y − X_j ∈ E}`. -/
def cntE (E : Set (EuclideanSpace ℝ (Fin d))) {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin d))
    (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ j, E.indicator (fun _ => (1 : ℝ)) (y - x j)

/-- The Lebesgue density `k/(n|E|)` of `P̂ * U`, `U` uniform on `E`. -/
def empJitDens (E : Set (EuclideanSpace ℝ (Fin d))) {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin d))
    (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  cntE E x y / (n * volR E)

/-- The Lebesgue density `P{x : y − x ∈ E}/|E|` of `P̃ = P * U`. -/
def jitDens (P : Measure (EuclideanSpace ℝ (Fin d))) (E : Set (EuclideanSpace ℝ (Fin d)))
    (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  P.real {x | y - x ∈ E} / volR E

/-- The negentropy `N(Q) = ∫ q log q` of a law with Lebesgue density `q`. -/
def negent (q : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ := ∫ y, q y * Real.log (q y)

/-- The uniform law on `E`. -/
def unifE (E : Set (EuclideanSpace ℝ (Fin d))) : Measure (EuclideanSpace ℝ (Fin d)) :=
  (volume E)⁻¹ • volume.restrict E

/-- The data-driven bound `N̂` (jitters `U_{ir}`, `i ≤ n`, `r ≤ R`). -/
def negentHat (E : Set (EuclideanSpace ℝ (Fin d))) (n R : ℕ) (δ₁ δ₂ : ℝ)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) (u : Fin n × Fin R → EuclideanSpace ℝ (Fin d)) : ℝ :=
  -Real.log (volR E) + (1 / ((n : ℝ) * R)) * ∑ ir : Fin n × Fin R, Real.log (cntE E x (x ir.1 + u ir) / n) +
    (1 + Real.log n) * √(Real.log (1 / δ₁) / (2 * n)) + Real.log n * √(Real.log (1 / δ₂) / (2 * n * R))

end Negent

/-! ### JASA `prop:envelope` -/

section Envelope
variable {K : Type*} [MeasurableSpace K]

/-- A reference: a measure `ν` with `0 < ν(K) ≤ 1` (`supp_proofs.tex:14-23`). -/
def IsRef (ν : Measure K) : Prop := 0 < ν univ ∧ ν univ ≤ 1

/-- `n⁻¹ Σ_i log ∫ e^{φ_i} dν`. -/
def avgLogMgf {n : ℕ} (φ : Fin n → K → ℝ) (ν : Measure K) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, Real.log (∫ x, Real.exp (φ i x) ∂ν)

/-- `Λ^𝒩 = sup_{ν ∈ 𝒩} n⁻¹ Σ_i log ∫ e^{φ_i} dν`, in `EReal`. -/
def lamClass {n : ℕ} (𝒩 : Set (Measure K)) (φ : Fin n → K → ℝ) : EReal :=
  ⨆ ν ∈ 𝒩, ((avgLogMgf φ ν : ℝ) : EReal)

/-- `𝒫(K)`. -/
def probLaws (K : Type*) [MeasurableSpace K] : Set (Measure K) := {ν | IsProbabilityMeasure ν}

/-- `𝒫(K)` for `K ⊆ ℝ`: probability measures on `ℝ` carried by `K`. -/
def probOn (K : Set ℝ) : Set (Measure ℝ) := {m | IsProbabilityMeasure m ∧ m Kᶜ = 0}

/-- `G_b = N(0, b²)` on `ℝ`. -/
def gaussB (b : ℝ) : Measure ℝ := gaussianReal 0 (b ^ 2).toNNReal

/-- The smoothed class `𝒩_b = {(G_b * m)|_K : m ∈ 𝒫(K)}` on `ℝ`. -/
def gaussClass (K : Set ℝ) (b : ℝ) : Set (Measure ℝ) :=
  {ν | ∃ m ∈ probOn K, ν = ((m.prod (gaussB b)).map fun p => p.1 + p.2).restrict K}

/-- `φ(x_i, y) = −a (y − x_i)²/ε` (the `d = 1` form of (ii)). -/
def phiLin {n : ℕ} (a ε : ℝ) (x : Fin n → ℝ) : Fin n → ℝ → ℝ := fun i y => -(a * (y - x i) ^ 2) / ε

/-- The weights `a_1 = t/(1+t)`, `a_k = 1` (`k ≥ 2`; 0-indexed: `k = 0` is the direction of `w`). -/
def envA {d : ℕ} (t : ℝ) (k : Fin d) : ℝ := if (k : ℕ) = 0 then t / (1 + t) else 1

/-- `π_b(y) = G_b(K^c − y)`. -/
def piB (K : Set ℝ) (b y : ℝ) : ℝ := (gaussB b).real {z | y + z ∉ K}

/-- The `d = 1` kernel `(1 + 2ab²/ε)^{−1/2} e^{−a(y−x_i)²/(ε+2ab²)}`. -/
def smoothK (a b ε xi y : ℝ) : ℝ :=
  (1 + 2 * a * b ^ 2 / ε) ^ (-(1 / 2 : ℝ)) * Real.exp (-(a * (y - xi) ^ 2) / (ε + 2 * a * b ^ 2))

end Envelope

/-! ### JASA `thm:ad-oracle` -/

section AdOracle
variable {K : Type*}

/-- `Ū(φ;s) = sup{Σ_j q_j φ(Y_j) + q_∞H : q ∈ Δ_{m+1}, m⁻¹ Σ_j log(1/(m q_j)) ≤ s}` (`q_j > 0`: a zero weight
makes the constraint `+∞`). -/
def elUB {m : ℕ} (H s : ℝ) (φ : K → ℝ) (y : Fin m → K) : ℝ :=
  sSup {v | ∃ (q : Fin m → ℝ) (q0 : ℝ), (∀ j, 0 < q j) ∧ 0 ≤ q0 ∧ ∑ j, q j + q0 = 1 ∧
    (m : ℝ)⁻¹ * ∑ j, Real.log (1 / (m * q j)) ≤ s ∧ v = ∑ j, q j * φ (y j) + q0 * H}

/-- `ρ_EL(s) = sup_{f ∈ F_W} {⟨a,f⟩ + Ū(g_f; s)}`, in `EReal`. -/
def rhoEL [MeasurableSpace K] {k m : ℕ} (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ) (H : (Fin k → ℝ) → ℝ)
    (s : ℝ) (y : Fin m → K) : EReal :=
  ⨆ f ∈ FW c, (((∑ i, a i * f i) + elUB (H f) s (gsoft ε a f c) y : ℝ) : EReal)

/-- `P̂_m φ = m⁻¹ Σ_j φ(Y_j)`. -/
def empMean {m : ℕ} (φ : K → ℝ) (y : Fin m → K) : ℝ := (m : ℝ)⁻¹ * ∑ j, φ (y j)

/-- `sd_{P̂_m}(φ) = (m⁻¹ Σ_j (φ(Y_j) − P̂_mφ)²)^{1/2}`. -/
def empSd {m : ℕ} (φ : K → ℝ) (y : Fin m → K) : ℝ := √((m : ℝ)⁻¹ * ∑ j, (φ (y j) - empMean φ y) ^ 2)

/-- `J_{P̂_m}(f) = ⟨a,f⟩ + P̂_m g_f`. -/
def Jemp {k m : ℕ} (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ) (y : Fin m → K) (f : Fin k → ℝ) : ℝ :=
  ∑ i, a i * f i + empMean (gsoft ε a f c) y

/-- The geometric grid `θ_1 = 1 > θ_2 = θ_1/γ > … > θ_N` (0-indexed: `θ_l = γ^{−l}`). -/
def geomGrid (γ : ℝ) (N : ℕ) : Fin N → ℝ := fun l => γ⁻¹ ^ (l : ℕ)

/-- `r = log(N/α)/m`. -/
def rThr (N m : ℕ) (α : ℝ) : ℝ := Real.log (N / α) / m

/-- The grid condition `θ_N (U_N(φ) − P̂_mφ)/(H − U_N(φ)) ≤ γr`, multiplied out (`θ_N = γ^{−(N−1)}`). -/
def GridCond {m : ℕ} (N : ℕ) (α γ H : ℝ) (φ : K → ℝ) (y : Fin m → K) : Prop :=
  γ⁻¹ ^ (N - 1) * (profileUB α H (geomGrid γ N) φ y - empMean φ y) ≤
    γ * rThr N m α * (H - profileUB α H (geomGrid γ N) φ y)

end AdOracle

/-! ### otfd R `thm:nullmass`(a), `cor:uncertainty` -/

section Depth
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]

/-- `TD_H(u;μ) = inf_{v ≠ 0} μ{z : ⟨v, z − u⟩ ≤ 0}`. -/
def depthH (μ : Measure H) (u : H) : ℝ≥0∞ := ⨅ (v : H) (_ : v ≠ 0), μ {z | ⟪v, z - u⟫ ≤ 0}

/-- `D_α(μ) = {u : TD_H(u;μ) ≥ α}`. -/
def depthRegion (μ : Measure H) (α : ℝ) : Set H := {u | ENNReal.ofReal α ≤ depthH μ u}

end Depth

/-! ### otfd A `prop:integrated-sieve-strong` -/

open Classical in
/-- The normalized sign `y/‖y‖`, with the fixed convention `c` at `0`. -/
def nsign {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] (c y : H) : H :=
  if y = 0 then c else ‖y‖⁻¹ • y

/-! ### otfd C `thm:conditional-band-limits`, `cor:conditional-test-coverage` -/

/-- The fitted support function `sup_{u ∈ A} ⟨v, F(u)⟩`, in `EReal`. -/
def supE {K : ℕ} (A : Set (EuclideanSpace ℝ (Fin K))) (F : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (v : EuclideanSpace ℝ (Fin K)) : EReal :=
  ⨆ u ∈ A, ((⟪v, F u⟫ : ℝ) : EReal)

/-! ### otfd T `thm:tubes` -/

section Tubes
variable {K J : ℕ}

/-- The affine scores `s_j(u) = a_j + ⟨b_j, u⟩`. -/
def scoreAff (a : Fin J → ℝ) (b : Fin J → EuclideanSpace ℝ (Fin K)) (j : Fin J) (u : EuclideanSpace ℝ (Fin K)) : ℝ :=
  a j + ⟪b j, u⟫

/-- The exact score gap `δ_j(A) = inf_{u ∈ A} (max_l s_l(u) − s_j(u))`. -/
def gapDelta (a : Fin J → ℝ) (b : Fin J → EuclideanSpace ℝ (Fin K)) (A : Set (EuclideanSpace ℝ (Fin K)))
    (j : Fin J) : ℝ :=
  sInf ((fun u => (⨆ l, scoreAff a b l u) - scoreAff a b j u) '' A)

/-- The entropic cap `κ_j = exp(−δ_j/ε)`. -/
def capEnt (ε δ : ℝ) : ℝ := Real.exp (-δ / ε)

/-- The quadratic cap `κ_j = (1 − δ_j/λ)_+`. -/
def capQuad (lam δ : ℝ) : ℝ := max 0 (1 - δ / lam)

/-- `𝒫_κ = {q ∈ Δ : q_j ≤ κ_j}`. -/
def capPoly (κ : Fin J → ℝ) : Set (Fin J → ℝ) := {q | (∀ j, 0 ≤ q j) ∧ ∑ j, q j = 1 ∧ ∀ j, q j ≤ κ j}

/-- `S_A(t) = {Σ_j q_j v_j(t) : q ∈ 𝒫_κ}`. -/
def enclS {T V : Type*} [AddCommGroup V] [Module ℝ V] (κ : Fin J → ℝ) (v : Fin J → T → V) (t : T) : Set V :=
  {w | ∃ q ∈ capPoly κ, w = ∑ j, q j • v j t}

end Tubes

namespace Claims

/-! #### JASA `prop:fl-negent` -/

/-- The formula `N(P̂ * U) = −log|E| + n⁻¹ Σ_i E_U log(k(X_i + U)/n)`. -/
def fl_negent_formula : Prop :=
  ∀ (d n : ℕ) (E : Set (EuclideanSpace ℝ (Fin d))) (x : Fin n → EuclideanSpace ℝ (Fin d)),
    0 < n → MeasurableSet E → Bornology.IsBounded E → 0 < volume E →
      negent (empJitDens E x) =
        -Real.log (volR E) + (n : ℝ)⁻¹ * ∑ i, ∫ u, Real.log (cntE E x (x i + u) / n) ∂(unifE E)

/-- Bounded differences: replacing one `X_j` moves `N(P̂ * U)` by at most `(1 + log n)/n`. -/
def fl_negent_bdd_diff : Prop :=
  ∀ (d n : ℕ) (E : Set (EuclideanSpace ℝ (Fin d))) (x : Fin n → EuclideanSpace ℝ (Fin d)) (j : Fin n)
    (z : EuclideanSpace ℝ (Fin d)),
    0 < n → MeasurableSet E → Bornology.IsBounded E → 0 < volume E →
      |negent (empJitDens E (Function.update x j z)) - negent (empJitDens E x)| ≤ (1 + Real.log n) / n

/-- Jensen + Tonelli: `N(P̃) ≤ E N(P̂ * U)` for `X_1, …, X_n` i.i.d. `P`, `supp P ⊆ K` bounded. -/
def fl_negent_jensen : Prop :=
  ∀ (d n : ℕ) (E K : Set (EuclideanSpace ℝ (Fin d))) (P : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P],
    0 < n → MeasurableSet E → Bornology.IsBounded E → 0 < volume E →
    MeasurableSet K → Bornology.IsBounded K → P Kᶜ = 0 →
      negent (jitDens P E) ≤ ∫ x, negent (empJitDens E x) ∂(Measure.pi fun _ : Fin n => P)

/-- `prop:fl-negent`: with probability `≥ 1 − δ₁ − δ₂` over `X ∼ P^n` and independent jitters `U_{ir}`,
`N(P̃) ≤ N̂`. -/
def fl_negent : Prop :=
  ∀ (d n R : ℕ) (E K : Set (EuclideanSpace ℝ (Fin d))) (P : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P] (δ₁ δ₂ : ℝ),
    0 < n → 0 < R → MeasurableSet E → Bornology.IsBounded E → 0 < volume E →
    MeasurableSet K → Bornology.IsBounded K → P Kᶜ = 0 → 0 < δ₁ → δ₁ ≤ 1 → 0 < δ₂ → δ₂ ≤ 1 →
      ∃ S : Set ((Fin n → EuclideanSpace ℝ (Fin d)) × (Fin n × Fin R → EuclideanSpace ℝ (Fin d))),
        MeasurableSet S ∧ S ⊆ {w | negent (jitDens P E) ≤ negentHat E n R δ₁ δ₂ w.1 w.2} ∧
        ENNReal.ofReal (1 - δ₁ - δ₂) ≤
          ((Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin n × Fin R => unifE E)) S

/-! #### JASA `prop:envelope` -/

/-- (i) `Λ^𝒩 ≤ E_{P̂} log sup_{ν ∈ 𝒩} E_ν e^{φ(x₀,·)}`, every nonempty class of references. -/
def envelope_i : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n : ℕ) (𝒩 : Set (Measure K)) (φ : Fin n → K → ℝ) (B : ℝ),
    0 < n → 𝒩.Nonempty → (∀ ν ∈ 𝒩, IsRef ν) → (∀ i, Measurable (φ i)) → (∀ i x, |φ i x| ≤ B) →
      lamClass 𝒩 φ ≤
        (((n : ℝ)⁻¹ * ∑ i, Real.log (sSup ((fun ν => ∫ x, Real.exp (φ i x) ∂ν) '' 𝒩)) : ℝ) : EReal)

/-- (i) for `𝒩 = 𝒫(K)` the right side is the pointwise envelope `E_{P̂} sup_{x ∈ K} φ(x₀, x)`. -/
def envelope_i_free : Prop :=
  ∀ (K : Type) [MeasurableSpace K] [Nonempty K] (n : ℕ) (φ : Fin n → K → ℝ) (B : ℝ),
    0 < n → (∀ i, Measurable (φ i)) → (∀ i x, |φ i x| ≤ B) →
      (n : ℝ)⁻¹ * ∑ i, Real.log (sSup ((fun ν => ∫ x, Real.exp (φ i x) ∂ν) '' probLaws K)) =
        (n : ℝ)⁻¹ * ∑ i, ⨆ x, φ i x

/-- (i) `𝒩 ⊆ 𝒩'` gives `Λ^𝒩 ≤ Λ^{𝒩'}`, and every class of references has `Λ^𝒩 ≤ Λ^{𝒫(K)}`. -/
def envelope_i_classes : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n : ℕ) (𝒩 𝒩' : Set (Measure K)) (φ : Fin n → K → ℝ) (B : ℝ),
    (∀ i, Measurable (φ i)) → (∀ i x, |φ i x| ≤ B) →
      (𝒩 ⊆ 𝒩' → lamClass 𝒩 φ ≤ lamClass 𝒩' φ) ∧
      ((∀ ν ∈ 𝒩, IsRef ν) → lamClass 𝒩 φ ≤ lamClass (probLaws K) φ)

/-- (ii) the algebra, every `d`: for `h = ⟨w,·⟩`, `λ = |w|²(1+t)` and an orthonormal basis with `e_1 = w/|w|`,
`φ(x₀,x) = (f_h − λc)/(λε) = −ε⁻¹ Σ_k a_k ⟨e_k, x − x₀⟩²`. -/
def envelope_ii_phi : Prop :=
  ∀ (d : ℕ) (e : OrthonormalBasis (Fin (d + 1)) ℝ (EuclideanSpace ℝ (Fin (d + 1))))
    (w x0 x : EuclideanSpace ℝ (Fin (d + 1))) (t ε : ℝ),
    w ≠ 0 → e 0 = ‖w‖⁻¹ • w → 0 ≤ t → 0 < ε →
      ((⟪w, x⟫ - ⟪w, x0⟫) ^ 2 - ‖w‖ ^ 2 * (1 + t) * ‖x - x0‖ ^ 2) / (‖w‖ ^ 2 * (1 + t) * ε) =
        -ε⁻¹ * ∑ k, envA t k * ⟪e k, x - x0⟫ ^ 2

/-- (ii), `d = 1`: `Λ^{𝒩_b} ≤ −½ log(1 + 2ab²/ε) + sup_{m ∈ 𝒫(K)} E_{P̂} log ∫ e^{−a(y−x₀)²/(ε+2ab²)} m(dy)`. -/
def envelope_ii : Prop :=
  ∀ (n : ℕ) (K : Set ℝ) (x : Fin n → ℝ) (a b ε : ℝ),
    0 < n → MeasurableSet K → 0 < volume K → 0 ≤ a → 0 < b → 0 < ε →
      lamClass (gaussClass K b) (phiLin a ε x) ≤
        ((-(1 / 2) * Real.log (1 + 2 * a * b ^ 2 / ε) : ℝ) : EReal) +
          ⨆ m ∈ probOn K, (((n : ℝ)⁻¹ * ∑ i,
            Real.log (∫ y, Real.exp (-(a * (y - x i) ^ 2) / (ε + 2 * a * b ^ 2)) ∂m) : ℝ) : EReal)

/-- (iii), `d = 1`, first display, for any `ν* ∈ 𝒫(K)` (the paper takes the maximiser) whose integrals are
positive (otherwise the right side is `−∞`). -/
def envelope_iii : Prop :=
  ∀ (n : ℕ) (K : Set ℝ) (x : Fin n → ℝ) (a b ε : ℝ) (νs : Measure ℝ),
    0 < n → MeasurableSet K → 0 < volume K → 0 ≤ a → 0 < b → 0 < ε → νs ∈ probOn K →
    (∀ i, 0 < ∫ y, max 0 (smoothK a b ε (x i) y - piB K b y) ∂νs) →
      (((n : ℝ)⁻¹ * ∑ i, Real.log (∫ y, max 0 (smoothK a b ε (x i) y - piB K b y) ∂νs) : ℝ) : EReal) ≤
        lamClass (gaussClass K b) (phiLin a ε x)

/-- (iii), `d = 1`, the gap: with `ν*` attaining `Λ^{𝒫(K)}`, `C_b = (1 + 2ab²/ε)^{1/2}`, `E_i = ∫ e^{φ(x_i,·)} dν*`,
`η_i = C_b ∫π_b dν*/E_i < 1`: `0 ≤ Λ^{𝒫(K)} − Λ^{𝒩_b} ≤ ½ log(1 + 2ab²/ε) + n⁻¹ Σ_i log(1/(1 − η_i))`. -/
def envelope_iii_gap : Prop :=
  ∀ (n : ℕ) (K : Set ℝ) (x : Fin n → ℝ) (a b ε : ℝ) (νs : Measure ℝ),
    0 < n → MeasurableSet K → 0 < volume K → 0 ≤ a → 0 < b → 0 < ε → νs ∈ probOn K →
    lamClass (probOn K) (phiLin a ε x) = ((avgLogMgf (phiLin a ε x) νs : ℝ) : EReal) →
    (∀ i, (1 + 2 * a * b ^ 2 / ε) ^ (1 / 2 : ℝ) * (∫ y, piB K b y ∂νs) /
        (∫ y, Real.exp (phiLin a ε x i y) ∂νs) < 1) →
      lamClass (gaussClass K b) (phiLin a ε x) ≤ lamClass (probOn K) (phiLin a ε x) ∧
      lamClass (probOn K) (phiLin a ε x) ≤ lamClass (gaussClass K b) (phiLin a ε x) +
        (((1 / 2) * Real.log (1 + 2 * a * b ^ 2 / ε) + (n : ℝ)⁻¹ * ∑ i, Real.log (1 / (1 -
          (1 + 2 * a * b ^ 2 / ε) ^ (1 / 2 : ℝ) * (∫ y, piB K b y ∂νs) /
            (∫ y, Real.exp (phiLin a ε x i y) ∂νs))) : ℝ) : EReal)

/-! #### JASA `thm:ad-oracle` -/

/-- (i) `Ô ≤ ρ_EL(r) ≤ ρ̂_N`, `Ô = OT_ε(μ, P̂_m)`, for every grid in `[0,1]^N`. -/
def ad_oracle_i : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k m N : ℕ) (ε α : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (H : (Fin k → ℝ) → ℝ) (θ : Fin N → ℝ) (y : Fin m → K),
    Setting ε a c → 0 < m → 0 < N → 0 < α → α < 1 → (∀ l, 0 ≤ θ l ∧ θ l ≤ 1) →
    (∀ f ∈ FW c, ∀ z, gsoft ε a f c z ≤ H f) →
      OTdisc ε a c (StatFormal.RobustEquality.Coverage.empMeasure y) ≤ rhoEL ε a c H (rThr N m α) y ∧
        rhoEL ε a c H (rThr N m α) y ≤ rhoN ε α a c H θ y

/-- (ii) under the grid condition for every `f ∈ F_W`, `ρ̂_N ≤ ρ_EL(γr)`. -/
def ad_oracle_ii : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k m N : ℕ) (ε α γ : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (H : (Fin k → ℝ) → ℝ) (y : Fin m → K),
    Setting ε a c → 0 < m → 0 < N → 0 < α → α < 1 → 1 < γ →
    (∀ f ∈ FW c, ∀ z, gsoft ε a f c z ≤ H f) →
    (∀ f ∈ FW c, GridCond N α γ (H f) (gsoft ε a f c) y) →
      rhoN ε α a c H (geomGrid γ N) y ≤ rhoEL ε a c H (γ * rThr N m α) y

/-- (ii), the paper's reading "every maximising `f`": if `ρ̂_N` is attained at `f* ∈ F_W` and `f*` satisfies the
grid condition, then `ρ̂_N ≤ ρ_EL(γr)`. -/
def ad_oracle_ii_attained : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k m N : ℕ) (ε α γ : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (H : (Fin k → ℝ) → ℝ) (y : Fin m → K) (fs : Fin k → ℝ),
    Setting ε a c → 0 < m → 0 < N → 0 < α → α < 1 → 1 < γ →
    (∀ f ∈ FW c, ∀ z, gsoft ε a f c z ≤ H f) → fs ∈ FW c →
    rhoN ε α a c H (geomGrid γ N) y =
      (((∑ i, a i * fs i) + profileUB α (H fs) (geomGrid γ N) (gsoft ε a fs c) y : ℝ) : EReal) →
    GridCond N α γ (H fs) (gsoft ε a fs c) y →
      rhoN ε α a c H (geomGrid γ N) y ≤ rhoEL ε a c H (γ * rThr N m α) y

/-- (ii) the display: `ρ̂_N − Ô ≤ sup_f {sd_{P̂_m}(g_f) √(2γr) + 2γr (H(f) − P̂_m g_f) − Gap_{P̂_m}(f)}`, with
`Gap_{P̂_m}(f) = Ô − J_{P̂_m}(f)`. -/
def ad_oracle_ii_bound : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k m N : ℕ) (ε α γ : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (H : (Fin k → ℝ) → ℝ) (y : Fin m → K),
    Setting ε a c → 0 < m → 0 < N → 0 < α → α < 1 → 1 < γ →
    (∀ f ∈ FW c, ∀ z, gsoft ε a f c z ≤ H f) →
    (∀ f ∈ FW c, GridCond N α γ (H f) (gsoft ε a f c) y) →
      rhoN ε α a c H (geomGrid γ N) y ≤
        OTdisc ε a c (StatFormal.RobustEquality.Coverage.empMeasure y) +
          ⨆ f ∈ FW c, (((empSd (gsoft ε a f c) y * √(2 * γ * rThr N m α) +
              2 * γ * rThr N m α * (H f - empMean (gsoft ε a f c) y) : ℝ) : EReal) -
            (OTdisc ε a c (StatFormal.RobustEquality.Coverage.empMeasure y) - (Jemp ε a c y f : EReal)))

/-- (iii) `ρ̂_N − Ô ≤ √(2γr V_U) + 2γr sup_{F_W}(H(f) − inf_K g_f)`, `V_U` the all-pairs envelope (any upper
bound `b̄` of `H(f) − g_f` on `F_W × K`). -/
def ad_oracle_iii : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k m N : ℕ) (ε α γ bbar : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (H : (Fin k → ℝ) → ℝ) (y : Fin m → K),
    Setting ε a c → 2 ≤ m → 0 < N → 0 < α → α < 1 → 1 < γ →
    (∀ f ∈ FW c, ∀ z, gsoft ε a f c z ≤ H f) →
    (∀ f ∈ FW c, GridCond N α γ (H f) (gsoft ε a f c) y) →
    (∀ f ∈ FW c, ∀ z, H f - gsoft ε a f c z ≤ bbar) →
      rhoN ε α a c H (geomGrid γ N) y ≤
        OTdisc ε a c (StatFormal.RobustEquality.Coverage.empMeasure y) +
          ((√(2 * γ * rThr N m α * StatFormal.RobustEquality.AllPairs.Vall c y) +
            2 * γ * rThr N m α * bbar : ℝ) : EReal)

/-! #### otfd R `thm:nullmass`(a), `cor:uncertainty` -/

/-- `thm:nullmass`(a): independent atomless coordinates along an orthonormal sequence give `μ(D_α(μ)) = 0`. -/
def nullmass_a : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure H) [IsProbabilityMeasure μ] (e : ℕ → H) (α : ℝ),
    Orthonormal ℝ e → iIndepFun (fun k (z : H) => ⟪e k, z⟫) μ →
    (∀ k, NullSingletonClass (μ.map fun z => ⟪e k, z⟫)) → 0 < α → α ≤ 1 / 2 →
      μ (depthRegion μ α) = 0

/-- `cor:uncertainty`, class (a): no Borel `A` with `μ(A) ≥ p > 0` has depth `≥ α` at every point. -/
def uncertainty_a : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure H) [IsProbabilityMeasure μ] (e : ℕ → H) (α p : ℝ),
    Orthonormal ℝ e → iIndepFun (fun k (z : H) => ⟪e k, z⟫) μ →
    (∀ k, NullSingletonClass (μ.map fun z => ⟪e k, z⟫)) → 0 < p → p ≤ 1 → 0 < α → α ≤ 1 / 2 →
      ¬ ∃ A : Set H, MeasurableSet A ∧ ENNReal.ofReal p ≤ μ A ∧ ∀ u ∈ A, ENNReal.ofReal α ≤ depthH μ u

/-! #### otfd A `prop:integrated-sieve-strong` -/

/-- "the geometric radial ranks converge in `L²`": `E‖Y_K − Y‖² → 0` gives `E(‖Y_K‖ − ‖Y‖)² → 0`. -/
def sieve_strong_radial : Prop :=
  ∀ (Ω H : Type) [MeasurableSpace Ω] [NormedAddCommGroup H] [NormedSpace ℝ H] (P : Measure Ω)
    (Y : ℕ → Ω → H) (Yl : Ω → H),
    Tendsto (fun K => ∫⁻ ω, ‖Y K ω - Yl ω‖ₑ ^ 2 ∂P) atTop (𝓝 0) →
      Tendsto (fun K => ∫⁻ ω, ‖‖Y K ω‖ - ‖Yl ω‖‖ₑ ^ 2 ∂P) atTop (𝓝 0)

/-- "the corresponding normalized signs converge in probability" (no atom of the limit at `0`). -/
def sieve_strong_signs_prob : Prop :=
  ∀ (Ω H : Type) [MeasurableSpace Ω] [NormedAddCommGroup H] [NormedSpace ℝ H] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : ℕ → Ω → H) (Yl : Ω → H) (c : H),
    (∀ K, AEStronglyMeasurable (Y K) P) → AEStronglyMeasurable Yl P →
    Tendsto (fun K => ∫⁻ ω, ‖Y K ω - Yl ω‖ₑ ^ 2 ∂P) atTop (𝓝 0) → P {ω | Yl ω = 0} = 0 →
      TendstoInMeasure P (fun K ω => nsign c (Y K ω)) atTop (fun ω => nsign c (Yl ω))

/-- "… and, being uniformly bounded, also in `L²`". -/
def sieve_strong_signs_L2 : Prop :=
  ∀ (Ω H : Type) [MeasurableSpace Ω] [NormedAddCommGroup H] [NormedSpace ℝ H] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : ℕ → Ω → H) (Yl : Ω → H) (c : H),
    (∀ K, AEStronglyMeasurable (Y K) P) → AEStronglyMeasurable Yl P →
    Tendsto (fun K => ∫⁻ ω, ‖Y K ω - Yl ω‖ₑ ^ 2 ∂P) atTop (𝓝 0) → P {ω | Yl ω = 0} = 0 →
      Tendsto (fun K => ∫⁻ ω, ‖nsign c (Y K ω) - nsign c (Yl ω)‖ₑ ^ 2 ∂P) atTop (𝓝 0)

/-! #### otfd C `thm:conditional-band-limits` -/

/-- Two-sided: on level regions `A_p ⊆ S` (`0 < p ≤ 1 − δ`) of full support, with `Q` continuous on `S`, every
band edge of any map `T` with `sup_S ‖T − Q‖ ≤ η` is within `E_K η` of the population edge (`E_K ≥ sup_t ‖𝐞(t)‖`),
uniformly in `p` and `t`: `eq:conditional-two-sided`. -/
def cond_band_two_sided : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ : Measure (EuclideanSpace ℝ (Fin K))) (A : ℝ → Set (EuclideanSpace ℝ (Fin K)))
    (S : Set (EuclideanSpace ℝ (Fin K))) (Q T : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (e : 𝒯 → EuclideanSpace ℝ (Fin K)) (δ η EK : ℝ),
    ContinuousOn Q S → (∀ u ∈ S, ‖T u - Q u‖ ≤ η) → (∀ t, ‖e t‖ ≤ EK) →
    (∀ p, 0 < p → p ≤ 1 - δ → IsCompact (A p) ∧ Convex ℝ (A p) ∧ (interior (A p)).Nonempty ∧
      A p ⊆ μ.support ∧ A p ⊆ S) →
      ∀ p, 0 < p → p ≤ 1 - δ → ∀ t, ∀ v ∈ ({e t, -e t} : Set (EuclideanSpace ℝ (Fin K))),
        ∃ r s : ℝ, StatFormal.Wave17a.hPop μ (A p) Q v = r ∧ supE (A p) T v = s ∧ |s - r| ≤ EK * η

/-- One-sided: at a level whose population essential range is bounded, pointwise convergence of the fitted maps
`μ_K`-a.e. on `A_{K,p}` (any selection) makes the edge deficit `Δ_{n,p,x}` vanish. -/
def cond_band_one_sided : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ : Measure (EuclideanSpace ℝ (Fin K))) (A : Set (EuclideanSpace ℝ (Fin K)))
    (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (Qn : ℕ → EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (e : 𝒯 → EuclideanSpace ℝ (Fin K)) (R EK : ℝ),
    MeasurableSet A → (∀ᵐ u ∂μ.restrict A, ‖Q u‖ ≤ R) →
    (∀ᵐ u ∂μ.restrict A, Tendsto (fun n => Qn n u) atTop (𝓝 (Q u))) → (∀ t, ‖e t‖ ≤ EK) →
      ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t,
        StatFormal.Wave17a.hPop μ A Q (e t) ≤ supE A (Qn n) (e t) + η ∧
        StatFormal.Wave17a.hPop μ A Q (-e t) ≤ supE A (Qn n) (-e t) + η

/-! #### otfd C `cor:conditional-test-coverage` -/

/-- Every fixed inflation `κ > 0` of a band whose edge deficit vanishes eventually contains the population band, so
its test coverage (a measurable event under the law `P_{K,x} = Q#μ_K` of the new projected response) is `≥ p` for
all large `n`: `liminf q_n ≥ p`. Edges `U_n, L_n` are any (fitted or certified outer) band edges. -/
def cond_test_coverage_inflated : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure μ]
    (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (A : Set (EuclideanSpace ℝ (Fin K))) (p κ : ℝ)
    (m : 𝒯 → ℝ) (e : 𝒯 → EuclideanSpace ℝ (Fin K)) (U L : ℕ → 𝒯 → EReal),
    Measurable Q → MeasurableSet A → ENNReal.ofReal p ≤ μ A → 0 < κ →
    (∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t,
      (m t : EReal) + StatFormal.Wave17a.hPop μ A Q (e t) ≤ U n t + η ∧
      L n t ≤ (m t : EReal) - StatFormal.Wave17a.hPop μ A Q (-e t) + η) →
      ∀ᶠ n in atTop, ∃ E : Set (EuclideanSpace ℝ (Fin K)), MeasurableSet E ∧
        E ⊆ {z | ∀ t, L n t - κ ≤ ((m t + ⟪e t, z⟫ : ℝ) : EReal) ∧ ((m t + ⟪e t, z⟫ : ℝ) : EReal) ≤ U n t + κ} ∧
        ENNReal.ofReal p ≤ μ.map Q E

/-- Under strict nesting of the population bands below `p`, the uninflated band has coverage `≥ p'` for all large
`n`, every `p' < p`: `liminf q_n ≥ p`. -/
def cond_test_coverage_nested : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure μ]
    (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (A : ℝ → Set (EuclideanSpace ℝ (Fin K))) (p : ℝ)
    (m : 𝒯 → ℝ) (e : 𝒯 → EuclideanSpace ℝ (Fin K)) (U L : ℕ → 𝒯 → EReal),
    Measurable Q → (∀ p', MeasurableSet (A p')) → (∀ p', 0 < p' → p' ≤ p → ENNReal.ofReal p' ≤ μ (A p')) →
    (∀ p', 0 < p' → p' < p → ∃ η : ℝ, 0 < η ∧ ∀ t,
      StatFormal.Wave17a.hPop μ (A p') Q (e t) + η ≤ StatFormal.Wave17a.hPop μ (A p) Q (e t) ∧
      StatFormal.Wave17a.hPop μ (A p') Q (-e t) + η ≤ StatFormal.Wave17a.hPop μ (A p) Q (-e t)) →
    (∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t,
      (m t : EReal) + StatFormal.Wave17a.hPop μ (A p) Q (e t) ≤ U n t + η ∧
      L n t ≤ (m t : EReal) - StatFormal.Wave17a.hPop μ (A p) Q (-e t) + η) →
      ∀ p', 0 < p' → p' < p → ∀ᶠ n in atTop, ∃ E : Set (EuclideanSpace ℝ (Fin K)), MeasurableSet E ∧
        E ⊆ {z | ∀ t, L n t ≤ ((m t + ⟪e t, z⟫ : ℝ) : EReal) ∧ ((m t + ⟪e t, z⟫ : ℝ) : EReal) ≤ U n t} ∧
        ENNReal.ofReal p' ≤ μ.map Q E

/-! #### otfd T `thm:rates` -/

/-- `c̄ = ½(sB_μ + B)²` bounds `c(u,z) = ½‖su − z‖²` on the product of the supports, and Rigollet–Stromme's
`2 max(sB_μ, B)²` is `≤ 4c̄`. -/
def rates_cbar : Prop :=
  ∀ (K : ℕ) (s Bμ B : ℝ) (u z : EuclideanSpace ℝ (Fin K)), 0 ≤ s → ‖u‖ ≤ Bμ → ‖z‖ ≤ B →
    (1 / 2) * ‖s • u - z‖ ^ 2 ≤ (1 / 2) * (s * Bμ + B) ^ 2 ∧
      2 * max (s * Bμ) B ^ 2 ≤ 4 * ((1 / 2) * (s * Bμ + B) ^ 2)

/-- Barycentric maps of laws carried by the `B`-ball (`Q_ε(u)`, `Q̂(u)`, `F_ε(z)`, `F̂(z)`) stay in the `B`-ball. -/
def rates_barycentre : Prop :=
  ∀ (K : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) (w : EuclideanSpace ℝ (Fin K) → ℝ) (B : ℝ),
    IsFiniteMeasure ν → ν (Metric.closedBall 0 B)ᶜ = 0 → (∀ z, 0 ≤ w z) → Integrable w ν →
    Integrable (fun z => w z • z) ν → 0 < ∫ z, w z ∂ν →
      ‖(∫ z, w z ∂ν)⁻¹ • ∫ z, w z • z ∂ν‖ ≤ B

/-- The reconstruction step: with `‖ι_K x‖_∞ ≤ Λ‖x‖` (`eq:Hembed`) and `E_m` `L_b`-Lipschitz in `D_∞` on fields of
sup-norm `≤ b = ΛB` (`eq:L`), the coefficient rate `E∫‖Q̂ − Q_ε‖² dμ_K ≤ C B²(1/n + 1/n_ref)` gives
`E∫ D_∞(E_m ι_K Q̂, E_m ι_K Q_ε)² dμ_K ≤ L_b² Λ² C B² (1/n + 1/n_ref)`. -/
def rates_reconstruction : Prop :=
  ∀ (K : ℕ) (Ω F Y : Type) [MeasurableSpace Ω] [NormedAddCommGroup F] [NormedSpace ℝ F] [PseudoMetricSpace Y]
    (P : Measure Ω) (μ : Measure (EuclideanSpace ℝ (Fin K))) (ι : EuclideanSpace ℝ (Fin K) →L[ℝ] F) (Ex : F → Y)
    (Qh : Ω → EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (Qe : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (Λ L B C : ℝ) (n nref : ℕ),
    0 ≤ Λ → 0 ≤ L → 0 ≤ C → (∀ x, ‖ι x‖ ≤ Λ * ‖x‖) →
    (∀ f g : F, ‖f‖ ≤ Λ * B → ‖g‖ ≤ Λ * B → dist (Ex f) (Ex g) ≤ L * ‖f - g‖) →
    (∀ ω u, ‖Qh ω u‖ ≤ B) → (∀ u, ‖Qe u‖ ≤ B) →
    ∫⁻ ω, ∫⁻ u, ‖Qh ω u - Qe u‖ₑ ^ 2 ∂μ ∂P ≤ ENNReal.ofReal (C * B ^ 2 * (1 / n + 1 / nref)) →
      ∫⁻ ω, ∫⁻ u, edist (Ex (ι (Qh ω u))) (Ex (ι (Qe u))) ^ 2 ∂μ ∂P ≤
        ENNReal.ofReal (L ^ 2 * Λ ^ 2 * C * B ^ 2 * (1 / n + 1 / nref))

/-! #### otfd T `thm:tubes` -/

/-- Containment by pointwise composition, and fitted-law content `≥ p̲` of the image tube (membership event
measurable, as hypothesised in the theorem); no injectivity of `Exp` and no compactness of `B_A(t)` used. -/
def tubes_content : Prop :=
  ∀ (K : ℕ) (𝒯 V M : Type) [MeasurableSpace M] (μ : Measure (EuclideanSpace ℝ (Fin K)))
    (A : Set (EuclideanSpace ℝ (Fin K))) (p : ℝ) (Ex : 𝒯 → V → M) (vh : EuclideanSpace ℝ (Fin K) → 𝒯 → V)
    (B : 𝒯 → Set V),
    MeasurableSet A → ENNReal.ofReal p ≤ μ A → (∀ u ∈ A, ∀ t, vh u t ∈ B t) →
    Measurable (fun u t => Ex t (vh u t)) → MeasurableSet {x : 𝒯 → M | ∀ t, x t ∈ Ex t '' B t} →
      (∀ u ∈ A, ∀ t, Ex t (vh u t) ∈ Ex t '' B t) ∧
        ENNReal.ofReal p ≤ (μ.map fun u t => Ex t (vh u t)) {x | ∀ t, x t ∈ Ex t '' B t}

/-- (ii) and (iii), abstract `Exp`: a radius enclosing `‖v‖` gives a ball about `m(t)` of that radius when
`d(m, Exp_m v) ≤ ‖v‖`; a tangent radius about `c(t)` gives a ball about `Exp_{m(t)} c(t)` of radius `L_b R` when
`Exp_{m(t)}` is `L_b`-Lipschitz on the `b`-ball (`lem:exp`). -/
def tubes_metric : Prop :=
  ∀ (K : ℕ) (𝒯 V M : Type) [NormedAddCommGroup V] [PseudoMetricSpace M] (A : Set (EuclideanSpace ℝ (Fin K)))
    (m : 𝒯 → M) (Ex : 𝒯 → V → M) (vh : EuclideanSpace ℝ (Fin K) → 𝒯 → V) (c : 𝒯 → V) (R Rc : 𝒯 → ℝ) (b Lb : ℝ),
    ((∀ t v, dist (m t) (Ex t v) ≤ ‖v‖) → (∀ u ∈ A, ∀ t, ‖vh u t‖ ≤ R t) →
      ∀ u ∈ A, ∀ t, Ex t (vh u t) ∈ Metric.closedBall (m t) (R t)) ∧
    (0 ≤ Lb → (∀ t v w, ‖v‖ ≤ b → ‖w‖ ≤ b → dist (Ex t v) (Ex t w) ≤ Lb * ‖v - w‖) →
      (∀ u ∈ A, ∀ t, ‖vh u t‖ ≤ b) → (∀ t, ‖c t‖ ≤ b) → (∀ u ∈ A, ∀ t, ‖vh u t - c t‖ ≤ Rc t) →
      ∀ u ∈ A, ∀ t, Ex t (vh u t) ∈ Metric.closedBall (Ex t (c t)) (Lb * Rc t))

/-- (ii) and (iii) on the unit sphere `S^d` (`d_{S^d} = arccos⟨·,·⟩`, `Exp` of `Wave 6b`): radius `R` about `m(t)`,
and radius `R_A^c(t)` about `Exp_{m(t)} c(t)` with `L_b = 1` for every `b`. -/
def tubes_sphere : Prop :=
  ∀ (d K : ℕ) (𝒯 : Type) (A : Set (EuclideanSpace ℝ (Fin K))) (m c : 𝒯 → EuclideanSpace ℝ (Fin (d + 1)))
    (vh : EuclideanSpace ℝ (Fin K) → 𝒯 → EuclideanSpace ℝ (Fin (d + 1))) (R Rc : 𝒯 → ℝ),
    (∀ t, ‖m t‖ = 1) → (∀ u ∈ A, ∀ t, ⟪m t, vh u t⟫ = 0) → (∀ t, ⟪m t, c t⟫ = 0) →
      ((∀ u ∈ A, ∀ t, ‖vh u t‖ ≤ R t) →
        ∀ u ∈ A, ∀ t, StatFormal.OTFD.Wave6b.sphDist (m t) (StatFormal.OTFD.Wave6b.sphExp (m t) (vh u t)) ≤ R t) ∧
      ((∀ u ∈ A, ∀ t, ‖vh u t - c t‖ ≤ Rc t) →
        ∀ u ∈ A, ∀ t, StatFormal.OTFD.Wave6b.sphDist (StatFormal.OTFD.Wave6b.sphExp (m t) (vh u t))
          (StatFormal.OTFD.Wave6b.sphExp (m t) (c t)) ≤ Rc t)

/-- Nesting: for nonempty `A ⊆ A'` the exact gaps decrease, so both caps grow, `𝒫_κ` grows, the enclosures
`S_A(t)` grow and so do their exponential images. -/
def tubes_nested : Prop :=
  ∀ (K J : ℕ) (𝒯 V M : Type) [AddCommGroup V] [Module ℝ V] (a : Fin J → ℝ) (b : Fin J → EuclideanSpace ℝ (Fin K))
    (A A' : Set (EuclideanSpace ℝ (Fin K))) (v : Fin J → 𝒯 → V) (Ex : 𝒯 → V → M) (ε lam : ℝ),
    A.Nonempty → A ⊆ A' → 0 < ε → 0 < lam →
      (∀ j, gapDelta a b A' j ≤ gapDelta a b A j) ∧
      (∀ t, Ex t '' enclS (fun j => capEnt ε (gapDelta a b A j)) v t ⊆
        Ex t '' enclS (fun j => capEnt ε (gapDelta a b A' j)) v t) ∧
      (∀ t, Ex t '' enclS (fun j => capQuad lam (gapDelta a b A j)) v t ⊆
        Ex t '' enclS (fun j => capQuad lam (gapDelta a b A' j)) v t)

end Claims

end StatFormal.Wave21b
