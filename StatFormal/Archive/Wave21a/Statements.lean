import StatFormal.Archive.Wave19b.Statements
import StatFormal.Archive.Wave21b.Statements
import StatFormal.Archive.Wave15a.Statements
import StatFormal.Archive.RobustEquality.Coverage.Statements
import StatFormal.Archive.RobustEquality.CoverageRandom.Statements
import StatFormal.Archive.RobustEquality.Paper2.Alternating.Statements
import StatFormal.Archive.Wave12c.Statements
import StatFormal.Archive.Wave16a.Statements
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# FROZEN STATEMENTS — wave 21a (QUEUE rows 225–231): robust equality JASA `prop:tax`, `prop:ddradius`, `prop:fl-radius`
# (+ the discharge of the frozen `thm:fl-coverage`), `lem:ad-linear`; paper 2 `prop:jointmin`; ICL
# `prop:cond-weight-mixing`; otfd A `prop:app-fixed-soft-consistency`

Sources (verbatim in `lean-formalisation/inventory/extracted/{robust-equality-jasa,robust-equality-paper2,
context-distribution-icl,otfd-A_sieves}.md`; current text after the 2026-10-13/14/15 corrections; JASA paths under
`robust-equality-outcomes-under-distribution-shift/jasa/`):
* JASA `prop:tax` (`supp_proofs.tex:633-643`, proof `:645-656`), with `H_J`, `𝒩^res_β` (`:628-631`) and the frozen
  `lem:tax` / `τ_𝒩` (`RobustEquality/Tax`).
* JASA `prop:ddradius` (`supp_calibration.tex:18-30`, proof `:32-48`), with `eq:subgrad`, `lem:convex` and
  `thm:coverage-general` (`supp_proofs.tex`).
* JASA `prop:fl-radius` (`supp_calibration.tex:120-134`, proof `:136-142`), with `prop:fl-negent` (`:98-108`) and the
  frozen `thm:fl-coverage` (Wave 19b, `:144-156`).
* JASA `lem:ad-linear` (`supp_calibration.tex:250-261`, proof `:263-274`), with `def:ad-moduli` (frozen `Λ_P`, Wave 15a).
* paper 2 `prop:jointmin` (`paper2/main.tex:305-313`, proof `app_proofs.tex:47-57`), with `thm:certificate`
  (`:254-262`), `(P_η)` (`eq:problems`, `:277-282`), `lem:delta-inf` (`:296-303`) and `thm:npmle` (`:502-519`).
* ICL `prop:cond-weight-mixing` (`context-distribution-ICL/paper/v3/supp/proofs_conditional.tex:479-496`, proof
  `:498-533`), with `thm:cond-dev`(ii) (frozen Wave 12c), `lem:cond-types` (frozen Wave 16a), `lem:cond-tilt` and
  `lem:cond-osc` (frozen `ICL/Cond`).
* otfd A `prop:app-fixed-soft-consistency` (`otfd/papers/A_sieves/supplement.tex:3525-3542`, proof `:3544-3632`).
Imports the frozen `Wave19b` (`worstDisp`, and through it `RobustEquality/{Tax,Strong,Certificate,SemidualStrong}`:
`Wdisc`, `tax`, `OTdisc`, `klRef`, `Tref1`, `centre`, `KernelWitness`; `Wave18a`: `jitterPrice`), `Wave15a` (`lamMod`),
`RobustEquality/Coverage` (`empMeasure`), `RobustEquality/CoverageRandom` (`empOn`), `RobustEquality/Paper2/Alternating`
(`pcost`, `Plans`; through it `Paper2/Seminorm`: `Phi`, `Tfin`, `nuMix`, `Deltafin`, `simplex`), `Wave12c` (`Giid`,
`empRisk`, `poolRisk`, `IsGateNet`, `ellIid`, `ellSwor`; through it `ICL`: `Grisk`; `ICL/Diag`: `klUnif`) and `Wave16a`
(`mixW`, `simplexW`, `typesA`) and `Wave21b` (`negentHat`, `negent`, `jitDens`, `unifE`; `prop:fl-negent`) statements,
not copied. No `Foundations` library file is imported directly. Mathlib
(`Distributions.Gaussian.Real`, `Moments.Variance`, `UniformSpace.UniformConvergence`) and Tau Ceti
(`wassersteinEDist`) otherwise.

Covered:
* `prop:tax`: (a) `tax_a_bound` (`0 ≤ ϰ(β) ≤ log(√(2π)β) + 1/(24β²)`), `tax_a_mono`, `tax_a_lim` (`ϰ(β) → 0` as `β ↓ 0`);
  (c) `tax_c` — CONDITIONAL on (b) (the inequality `τ_𝒩(P) ≤ E_{P^rec} g` is a hypothesis).
* `prop:ddradius`: `dd_plugin_kl` (the plug-in `KL(P̂ ‖ ν_q)` of (E2) is the paper's `KL`), `dd_radius_E2`,
  `dd_radius_E1`.
* `prop:fl-radius`: `fl_radius` (any deviation terms of `thm:coverage`, given as events; CONDITIONAL on `prop:fl-negent`),
  `fl_radius_hoeffding` (Hoeffding deviation terms PROVED; CONDITIONAL on `prop:fl-negent` only).
* `thm:fl-coverage` with its `prop:fl-radius` hypothesis DISCHARGED: `fl_coverage_discharged` (the frozen Wave 19b
  conclusion, verbatim, for the centres/references/radii of `prop:fl-radius`; CONDITIONAL on `prop:fl-negent` only);
  `fl_coverage_unconditional` (the same with `N̂` the frozen Wave 21b `negentHat` from an independent sample and jitters
  of law `P_s^{n_E} ⊗ U_θ^{n_E R_E}`: UNCONDITIONAL, via the certified Wave 21b `fl_negent`).
* `lem:ad-linear`: `ad_linear_upper` (both upper bounds), `ad_linear_lower`, `ad_linear_kinf_dv` (weak duality, any
  `K`), `ad_linear_kinf` (duality and attainment, finite `K`), `ad_linear_profile` (finite `K`).
* `prop:jointmin`, split per model: single reference — `jointmin_upper` (every value of `Ψ(λ,γ)` bounds `R + ηF`),
  `jointmin_inf` (`inf_{λ,γ} Ψ` is the objective of `(P_η)`); the free end with a finite mixture class and linear
  rules — `jointmin_free` (feasible points dominate the certificate; same infimum).
* `prop:cond-weight-mixing`: `weight_mixing_i` (i.i.d. contexts), `weight_mixing_ii` (without replacement).
* `prop:app-fixed-soft-consistency`: `fixed_soft_dual` (existence, uniqueness up to constants of the population and
  empirical dual minimisers — "we verify existence and uniqueness rather than assume them"), `fixed_soft_consistency`
  (a.s. uniform convergence of the barycentric maps, measurability of the averaged error, convergence in mean).

Not covered (declared):
* `prop:tax`(b) (tensorisation and joint convexity under `H_J` for the smooth and resolution classes; it needs the
  `d`-dimensional box model, the classes `𝒩_b`, `𝒩^res_β` and scale invariance of `ϰ`) — hence (c) is conditional;
  the sentences after the proposition (tightness, `ϰ(β) ≈ 0.61β`, Table `tab:box`: numerical).
* `prop:fl-radius`/`thm:fl-coverage`: `prop:fl-negent` itself (certified in Wave 21b, used by
  `fl_coverage_unconditional`; assumed in `fl_radius`, `fl_coverage_discharged`); the construction of the
  fold centres from the sample with fresh jitters (any fold-measurable atoms are allowed); the mortgage numbers.
* `prop:ddradius`: "the calibration of the journal version", the exact-coverage study (prose).
* `lem:ad-linear`: the `K_inf` duality and the profile identity on infinite `K` (the "virtual point" `H > sup_K φ`
  clause); here `K` is finite and the maximiser of `φ` exists.
* `prop:jointmin`: `ε = 0`, anisotropic sets, structured sets with a finite cell cover, Feller kernels on a compact
  `L` (only finitely supported mixture kernels with finite `L`); the remark after it.
* `prop:cond-weight-mixing`: "conditionally on the pool" is built in (pool losses are data); the "Mixing weights
  versus mixing laws" example after the proof.
* `prop:app-fixed-soft-consistency`: the identification of the critical points with the entropic couplings (the
  primal step; `T^g` is taken as the barycentric map of the Gibbs coupling `p^g`), and "no strong convexity ... is
  used" (a remark).

Encodings (to be checked by the critic):
* tax: `U[−½,½] = Leb|_{[−½,½]}` (`boxU`); `ϰ(β) = ⨅_{m ∈ 𝒫(ℝ)} klRef(U ‖ N(0,β²) ∗ m)` in `EReal` (`varkappa`;
  `gaussianReal 0 (β²).toNNReal`, Mathlib `Measure.conv`), stated for `β > 0`; (c) for any measurable `g` with range
  `[g₋, g₊]` (paper: `g = Σ_k ϰ(b_k/s_k)`), `n` i.i.d. recorded values `Prec^n`, measurable event of probability `≥ 1 − a`.
* ddradius: sample `X ∼ P^N` (`Measure.pi`), fixed folds (`fold`, enumerations `e v`), fold `v` = centre
  `P̂_v` (weights `1/n_v`), held-out `P̂_{−v} = empOn` on `{i // fold i ≠ v}`, `m_v = |{i : fold i ≠ v}|`,
  `w_v = n_v/N`; "`ν_v` built from fold `v` alone" is `FoldOnly` (the reference data depend on `X` only through the
  fold-`v` coordinates) + measurability; references are finite with mass `≤ 1` (the paper's convention for `ν`), (E2):
  `ν_v = Σ_{a∈A} q_v(a) δ_a` (`massRef`, `q_v > 0` on `A`, `Σ_A q_v ≤ 1`, osc of `log q_v` on `A` `≤ R_v`), `Ê_v` is the
  plug-in `Σ_A p̂ log(p̂/q)` (`klPlug`, `= KL(P̂_{−v} ‖ ν_v)` by `dd_plugin_kl`); (E1): `P = p·λ`, `λ` σ-finite,
  `p log p ∈ L¹(λ)`, `ν_v = q_v·λ` (`densRef`), `q_v > 0`, osc of `log q_v` `≤ R_v`; `OT_ε(P̂_v, P̂_{−v})` is the
  `toReal` of the frozen `OTdisc` (finite); `W^ν_ε` is the frozen `Wdisc` (`ν = foldMix`).
* fl-radius: `ℝ^d = EuclideanSpace ℝ (Fin d)`; `U = U_J` uniform on a bounded measurable `J` of positive volume
  (`unifOn`), `C ⊇ K + J` measurable (paper: a box); `P̃ = P ∗ U_J`; `N(P̃) = ∫ p̃ log p̃` with the explicit density
  `p̃(y) = P{y − J}/|J|` (`jitDens`, `negEnt`); data on an abstract `(Ω, Pr)`: centre atoms `x ω` and reference densities
  are functions of a fold datum `D_v` independent of the `m_v` jittered held-out points `Y_v`, i.i.d. `P̃` (`FlSetting`);
  `prop:fl-negent` and the `thm:coverage` deviation terms are hypotheses as measurable events; `ν_v = q_v·Leb|_C`
  (`boxRef`, mass `≤ 1`). The discharge instantiates the frozen `fl_coverage` with `U_θ = U_{J_θ}`, `ν = flRef`,
  `r = flRadius` (Hoeffding terms) at total level `Σ_v 2δ + δ₁ + δ₂ ≤ α/(2|𝒢|)`; its conclusion is copied verbatim.
* ad-linear: `Λ_P` is the frozen `lamMod` (`EReal` `⨆`, `KL = klDiv`); `G = H − Pφ` for any `H ≥ sup_K φ` and
  `b₋ = Pφ − l` for any `P`-a.e. lower bound `l` (both include the paper's `sup`/`ess inf`); `F(θ) = kinfObj`;
  `K_inf(P, μ) = sInf{KL(P‖Q) : Qφ ≥ μ}` (`ℝ≥0∞`), attained (`IsLeast`), `= sup_{θ∈[0,1)} F` (`IsLUB`; the paper's
  `max_{θ∈[0,1]}`, `F(1)` read as the left limit); profile: `⨆` over real `μ < max φ` in `EReal`.
* jointmin: centres uniform on labelled atoms; `γ ∈ Plans` (couplings of the two uniform weight vectors),
  `E_γ{h(X)−h(Y)}² = pcost`; `T_s = Tref1` (single reference, `√` of a real; `Tref1 < 0` only for an empty ball);
  `F(h)` the frozen `worstDisp` over the two `lem:kernel` balls (`kerBall`); `(P_η)` objective `penObj`
  (`Δ = W₂.toReal`, finite); the infimum statements are `IsGLB`-equivalences (same set of lower bounds, no `sInf` junk);
  free end: linear rules `⟨w,·⟩`, mixture kernels `κ y = Σ_k κ_{yk} δ_{ξ_k}` (`p` points `y`), feasibility
  `Φ_y ≤ 0` for all `y`, `T^𝒩_s = max_m Tfin(·, nuMix κ m, ·)` given by `IsGreatest`.
* weight-mixing: the frozen `thm:cond-dev`(ii) setting (pool losses `L z S` / `L z j` measurable in the query, in
  `[0, B_L]`; validation sample `P₀^m`; gates measurable in `z`, continuous in `γ`, `Γ` separable and first countable —
  the hypothesis added and critic-approved in Wave 12c); `w(x) = mixW (g z γ) W`; `N_𝒢(η)` / `N^log_𝒢(η/(4M))` encoded by
  quantifying over internal nets (`IsGateNet`, `IsLogGateNet`) with `log |N|` in the bound; `K = |typesA R M|`.
* fixed-soft: grid `u : Fin m → ℝ^K` (distinctness not needed — generalisation), `c_j(x) = ‖x − u_j‖²`; `𝒥`, `𝒥_n`
  (`Jpop`, Bochner integral finite under `E‖X‖² < ∞`; `Jemp`); minimisers are `IsMinOn … univ` (no normalisation;
  uniqueness up to `g + t𝟙`); `T^g = baryT`; samples `X₁, X₂, …` i.i.d. `P` (`iIndepFun`), the `n`-th estimator uses the
  first `n + 1` points and is ANY minimiser `ĝ_n(ω)` (no measurability assumed — the averaged error is proved
  measurable); "uniformly on `ℝ^K`" is `TendstoUniformly`; `P ∈ 𝒫^ℓ` is weakened to a finite second moment.

Critic notes:
* All 23 claims are proved in `Wave21a/Route{Tax,DdRadius,FlRadius,FlCoverage,AdLinear,Kinf,JointMin,WeightMix,
  FixedSoft}.lean` (+ `RouteCommon`). Routes use the untrusted Foundations libraries (`Tax/Tax`: `Wdisc_eq`,
  `klRef_eq_klDiv`; `SemiDiscrete/{Convex,RandomFolds,HeldOut,Coverage}`; `Concentration/EmpiricalProcess`:
  McDiarmid via Tau Ceti), the certified `kernel_iff` (Wave 11a), `fl_coverage` (Wave 19b), `cond_types_i/ii`
  (Wave 16a), `cover_ball` and the `thm:cond-dev`(ii) machinery (Wave 12c), `cond_tilt`, `cond_osc_i` (`ICL/Cond`),
  `certificate`, `delta_inf_W2`, `npmle_programme` — routes only. `weight_mixing_ii` uses
  `set_option maxHeartbeats 1000000`.
* The fl-coverage hypothesis IS discharged: `fl_coverage_discharged` (conditional on `prop:fl-negent` only) and
  `fl_coverage_unconditional` (no hypothesis beyond the setting; `negEnt P J` is definitionally the Wave 21b
  `negent (jitDens P J)`, `unifOn` is `unifE`). `fl_radius` is CONDITIONAL on `prop:fl-negent`.
* (a) `tax_c` is CONDITIONAL on `prop:tax`(b), the tensorisation under `H_J` (not covered).
* (b) `jointmin_free` bounds the certificate `F̄^𝒩` (with `T^𝒩_s = max_m T`), not `R + ηF` directly (the certified
  `thm:certificate`/`thm:npmle` give `F ≤ F̄^𝒩`), and fixes the cost `‖·‖²` (linear rules, `Tfin`).
* (c) fixed-soft: the step identifying the dual solution with the primal entropic coupling (`γ^g`) is not covered;
  `T^g` is the barycentric map of the softmax weights `p^g`.
* (d) Paper S4, `lem:ad-linear` proof: "add mass at a maximiser of `φ`" assumes a maximiser exists. On `K = [0,1)`,
  `φ = x`, `P = δ₀`, `μ = ½`, the infimum `inf{KL(P‖Q) : Qφ ≥ ½} = log 2` is not attained (although the equality with
  `sup_θ F(θ)` still holds); here `K` is finite.
* (e) Paper S4, `thm:fl-coverage` says "jitter laws `U_θ`", but the radius of `prop:fl-radius` (density bound,
  `prop:fl-negent`) needs them uniform on a set `E` of positive volume; the claims use `U_θ = U_{J_θ}`.
* No statement was found false. Observations: the `lem:ad-linear` bounds hold for any `H ≥ sup φ` / a.e. lower bound
  `l`; the `K_inf` minimiser is explicit (`P/(1 − θ⋆z)`, or `P/(1 − z)` plus mass at a maximiser when `P` does not charge
  the maximisers), no virtual point is needed on a finite `K`; `prop:app-fixed-soft-consistency` needs neither distinct
  grid points nor convexity in the argmin step (uniform coercivity, equi-Lipschitz objectives and uniqueness up to
  constants suffice), and the empirical minimiser is a continuous function of the sample; `prop:ddradius`(E2) is
  proved with the bounded difference `(B_c + ε(R_v + 1 + log m_v))/m_v` as printed (the old typo J18 is corrected
  in the current text); `ϰ(β) ≤ −log((1−β)/(1+2√β))` (mixing law `U[−½−√β, ½+√β]`) gives the limit without
  dominated convergence.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TauCeti
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave21a

open StatFormal.RobustEquality StatFormal.RobustEquality.Semidual StatFormal.RobustEquality.SemidualStrong

/-! ### JASA `prop:tax` -/

section Tax

/-- The uniform law `U[−½, ½]` on `ℝ`. -/
def boxU : Measure ℝ := volume.restrict (Icc (-(1 / 2 : ℝ)) (1 / 2))

/-- `ϰ(β) = inf_{m ∈ 𝒫(ℝ)} KL(U[−½,½] ‖ N(0, β²) ∗ m)` (paper KL `klRef`, infimum in `EReal`). -/
def varkappa (β : ℝ) : EReal :=
  ⨅ (m : Measure ℝ) (_ : IsProbabilityMeasure m), klRef boxU (gaussianReal 0 (β ^ 2).toNNReal ∗ m)

end Tax

/-! ### JASA `prop:ddradius` -/

section DdRadius

variable {K : Type*} [MeasurableSpace K]

/-- The reference with mass function `q` on the finite set `A`: `ν_q = Σ_{a ∈ A} q(a) δ_a`. -/
def massRef (A : Finset K) (q : K → ℝ) : Measure K := ∑ a ∈ A, ENNReal.ofReal (q a) • Measure.dirac a

open Classical in
/-- The empirical frequency `p̂(a) = #{j : y_j = a} / |ι|`. -/
def empFreq {ι : Type*} [Fintype ι] (y : ι → K) (a : K) : ℝ :=
  ((Finset.univ.filter fun j => y j = a).card : ℝ) / Fintype.card ι

/-- The plug-in relative entropy on `A`, `Σ_{a ∈ A} p̂(a) log(p̂(a)/q(a))` (`0 log 0 = 0`); it is
`KL(P̂ ‖ ν_q)` whenever every `y_j ∈ A` (`dd_plugin_kl`). -/
def klPlug {ι : Type*} [Fintype ι] (A : Finset K) (q : K → ℝ) (y : ι → K) : ℝ :=
  ∑ a ∈ A, empFreq y a * Real.log (empFreq y a / q a)

/-- The reference with density `q` with respect to the base measure `λ`: `ν = q · λ`. -/
def densRef (lam : Measure K) (q : K → ℝ) : Measure K := lam.withDensity fun y => ENNReal.ofReal (q y)

variable {N V : ℕ} {fold : Fin N → Fin V} {n : Fin V → ℕ}

/-- The fold-mixture reference `ν = Σ_v w_v ν_v`, `w_v = n_v / N`. -/
def foldMix (nu : Fin V → Measure K) (n : Fin V → ℕ) (N : ℕ) : Measure K :=
  ∑ v, ENNReal.ofReal ((n v : ℝ) / N) • nu v

/-- `OT_ε(P̂_v, P̂_{−v})` (finite; `toReal` of the frozen `OTdisc`). -/
def otFold (ε : ℝ) (c : K → K → ℝ) (e : ∀ v, Fin (n v) ≃ {i // fold i = v}) (v : Fin V)
    (X : Fin N → K) : ℝ :=
  (OTdisc ε (fun _ : Fin (n v) => (1 : ℝ) / n v) (fun j => c (X (e v j)))
    (StatFormal.RobustEquality.CoverageRandom.empOn fun i : {i // ¬ fold i = v} => X i)).toReal

/-- `prop:ddradius` (E2) radius:
`r̂ = Σ_v w_v [OT_ε(P̂_v, P̂_{−v}) + ε KL(P̂_{−v} ‖ ν_v) + (B_c + ε(R_v + 1 + log m_v)) √(log(V/a)/(2m_v))]`. -/
def ddRadiusE2 (ε Bc a : ℝ) (c : K → K → ℝ) (e : ∀ v, Fin (n v) ≃ {i // fold i = v}) (A : Finset K)
    (q : Fin V → (Fin N → K) → K → ℝ) (R : Fin V → ℝ) (X : Fin N → K) : ℝ :=
  ∑ v, ((n v : ℝ) / N) * (otFold ε c e v X + ε * klPlug A (q v X) (fun i : {i // ¬ fold i = v} => X i) +
    (Bc + ε * (R v + 1 + Real.log (Fintype.card {i // ¬ fold i = v}))) *
      √(Real.log (V / a) / (2 * Fintype.card {i // ¬ fold i = v})))

/-- `prop:ddradius` (E1) radius:
`r̂ = Σ_v w_v [OT_ε(P̂_v, P̂_{−v}) + ε (H̄ + E_{P̂_{−v}}[−log q_v]) + (B_c + ε R_v) √(log(V/a)/(2m_v))]`. -/
def ddRadiusE1 (ε Bc a Hbar : ℝ) (c : K → K → ℝ) (e : ∀ v, Fin (n v) ≃ {i // fold i = v})
    (q : Fin V → (Fin N → K) → K → ℝ) (R : Fin V → ℝ) (X : Fin N → K) : ℝ :=
  ∑ v, ((n v : ℝ) / N) * (otFold ε c e v X +
    ε * (Hbar + (1 / (Fintype.card {i // ¬ fold i = v} : ℝ)) *
      ∑ i : {i // ¬ fold i = v}, -Real.log (q v X (X i))) +
    (Bc + ε * R v) * √(Real.log (V / a) / (2 * Fintype.card {i // ¬ fold i = v})))

/-- "`ν_v` is built from fold `v` alone": `q v X` depends on `X` only through the fold-`v` coordinates. -/
def FoldOnly (fold : Fin N → Fin V) (v : Fin V) {β : Type*} (f : (Fin N → K) → β) : Prop :=
  ∀ X X' : Fin N → K, (∀ i, fold i = v → X i = X' i) → f X = f X'

end DdRadius

/-! ### JASA `prop:fl-radius` (and the discharge of the hypothesis of the frozen `thm:fl-coverage`) -/

section FlRadius

variable {d : ℕ}

/-- The uniform law on a set `J ⊆ ℝ^d` of finite positive volume. -/
def unifOn (J : Set (EuclideanSpace ℝ (Fin d))) : Measure (EuclideanSpace ℝ (Fin d)) :=
  (volume J)⁻¹ • volume.restrict J

/-- The Lebesgue density of the jittered law `P ∗ U_J`: `p̃(y) = P{x : y − x ∈ J} / |J|`. -/
def jitDens (P : Measure (EuclideanSpace ℝ (Fin d))) (J : Set (EuclideanSpace ℝ (Fin d)))
    (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (P {x | y - x ∈ J}).toReal / (volume J).toReal

/-- The negentropy `N(P̃) = ∫ p̃ log p̃` of the jittered law `P̃ = P ∗ U_J` (`prop:fl-negent`). -/
def negEnt (P : Measure (EuclideanSpace ℝ (Fin d))) (J : Set (EuclideanSpace ℝ (Fin d))) : ℝ :=
  ∫ y, jitDens P J y * Real.log (jitDens P J y)

/-- A reference on the box `C` with Lebesgue density `q`: `ν = q · Leb|_C`. -/
def boxRef (C : Set (EuclideanSpace ℝ (Fin d))) (q : EuclideanSpace ℝ (Fin d) → ℝ) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  (volume.restrict C).withDensity fun y => ENNReal.ofReal (q y)

variable {Ω Z : Type*} [MeasurableSpace Ω] {N V : ℕ} {k m : Fin V → ℕ}

/-- `ν = Σ_v w_v ν_v`, `w_v = k_v / N`, `ν_v` the box reference of density `q_v(D_v)`. -/
def flRef (C : Set (EuclideanSpace ℝ (Fin d))) (q : Fin V → Z → EuclideanSpace ℝ (Fin d) → ℝ)
    (D : Fin V → Ω → Z) (ω : Ω) : Measure (EuclideanSpace ℝ (Fin d)) :=
  ∑ v, ENNReal.ofReal ((k v : ℝ) / N) • boxRef C (q v (D v ω))

/-- The fold-`v` centre `μ_v` (uniform on its `k_v` atoms) against the jittered held-out law `Q̂_{−v}`:
`OT_ε(μ_v, Q̂_{−v})` (finite; `toReal` of the frozen `OTdisc`). -/
def otHeld {fold : Fin N → Fin V} (ε : ℝ) (c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ)
    (e : ∀ v, Fin (k v) ≃ {i // fold i = v}) (x : Ω → Fin N → EuclideanSpace ℝ (Fin d))
    (Y : ∀ v, Fin (m v) → Ω → EuclideanSpace ℝ (Fin d)) (v : Fin V) (ω : Ω) : ℝ :=
  (OTdisc ε (fun _ : Fin (k v) => (1 : ℝ) / k v) (fun j => c (x ω (e v j)))
    (StatFormal.RobustEquality.Coverage.empMeasure fun j => Y v j ω)).toReal

/-- `prop:fl-radius`:
`r̂ = Σ_v w_v [OT_ε(μ_v, Q̂_{−v}) + dev_v + ε (E_{Q̂_{−v}}[−log q_v] + R_v √(log(1/δ)/(2m_v)))] + ε N̂`. -/
def flRadius {fold : Fin N → Fin V} (ε δ : ℝ) (c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ)
    (e : ∀ v, Fin (k v) ≃ {i // fold i = v}) (x : Ω → Fin N → EuclideanSpace ℝ (Fin d))
    (D : Fin V → Ω → Z) (q : Fin V → Z → EuclideanSpace ℝ (Fin d) → ℝ) (R : Fin V → ℝ)
    (Y : ∀ v, Fin (m v) → Ω → EuclideanSpace ℝ (Fin d)) (dev : Fin V → Ω → ℝ) (Nhat : Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ v, ((k v : ℝ) / N) * (otHeld ε c e x Y v ω + dev v ω +
    ε * ((1 / (m v : ℝ)) * ∑ j, -Real.log (q v (D v ω) (Y v j ω)) +
      R v * √(Real.log (1 / δ) / (2 * m v)))) + ε * Nhat ω

/-- The Hoeffding deviation term of `thm:coverage` at level `δ`, `dev_v = B_c √(log(1/δ)/(2m_v))`. -/
def hoeffDev (Bc δ : ℝ) (m : Fin V → ℕ) (v : Fin V) (_ω : Ω) : ℝ := Bc * √(Real.log (1 / δ) / (2 * m v))

/-- The standing setting of `prop:fl-radius` for one group (and one tuning parameter): the support `K`, the jitter
set `J` (`U = U_J`), the box `C ⊇ K + J`; a bounded measurable cost with oscillation `≤ B_c`; folds of the centre's
`N` atoms (`fold`, enumerations `e`); the fold-`v` atoms and reference density are functions of a fold datum `D_v`
(the fold and independent randomisation) that is independent of the `m_v` jittered held-out points `Y_v`, which are
i.i.d. `P ∗ U_J`; `q_v > 0` on `C`, `ν_v(C) ≤ 1`, `osc_C log q_v ≤ R_v`. -/
def FlSetting [MeasurableSpace Z] (Pr : Measure Ω) (K J C : Set (EuclideanSpace ℝ (Fin d)))
    (P : Measure (EuclideanSpace ℝ (Fin d))) (c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ)
    (ε Bc : ℝ) (fold : Fin N → Fin V) (e : ∀ v, Fin (k v) ≃ {i // fold i = v})
    (x : Ω → Fin N → EuclideanSpace ℝ (Fin d)) (D : Fin V → Ω → Z)
    (A : ∀ v, Z → Fin (k v) → EuclideanSpace ℝ (Fin d)) (q : Fin V → Z → EuclideanSpace ℝ (Fin d) → ℝ)
    (R : Fin V → ℝ) (Y : ∀ v, Fin (m v) → Ω → EuclideanSpace ℝ (Fin d)) : Prop :=
  IsProbabilityMeasure Pr ∧ IsProbabilityMeasure P ∧
  Bornology.IsBounded K ∧ MeasurableSet K ∧ P Kᶜ = 0 ∧
  Bornology.IsBounded J ∧ MeasurableSet J ∧ 0 < volume J ∧
  MeasurableSet C ∧ (∀ y ∈ K, ∀ u ∈ J, y + u ∈ C) ∧
  0 < ε ∧ Measurable (Function.uncurry c) ∧ (∃ B, ∀ a b, |c a b| ≤ B) ∧ 0 < Bc ∧
  (∀ a y y', c a y - c a y' ≤ Bc) ∧
  0 < N ∧ Function.Surjective fold ∧ (∀ v, 0 < m v) ∧
  (∀ v, Measurable (D v)) ∧ (∀ v j, Measurable fun z => A v z j) ∧ (∀ ω v j, x ω (e v j) = A v (D v ω) j) ∧
  (∀ v, Measurable (Function.uncurry (q v))) ∧ (∀ v z y, y ∈ C → 0 < q v z y) ∧
  (∀ v z, boxRef C (q v z) Set.univ ≤ 1) ∧
  (∀ v z y y', y ∈ C → y' ∈ C → Real.log (q v z y) - Real.log (q v z y') ≤ R v) ∧
  (∀ v j, Measurable (Y v j)) ∧ (∀ v, iIndepFun (Y v) Pr) ∧ (∀ v j, Pr.map (Y v j) = P ∗ unifOn J) ∧
  (∀ v, IndepFun (D v) (fun ω j => Y v j ω) Pr)

end FlRadius

/-! ### JASA `lem:ad-linear` (`Λ_P` is the frozen `StatFormal.Wave15a.lamMod`) -/

section AdLinear

variable {K : Type*} [MeasurableSpace K]

/-- `F(θ) = E_P log(1 − θ z_μ)`, `z_μ = (φ − μ)/(H − μ)`. -/
def kinfObj (P : Measure K) (φ : K → ℝ) (H μ θ : ℝ) : ℝ :=
  ∫ x, Real.log (1 - θ * ((φ x - μ) / (H - μ))) ∂P

end AdLinear

/-! ### paper 2 `prop:jointmin` -/

section JointMin

variable {K : Type} [MeasurableSpace K]

/-- The objective of the joint minimisation at a single reference per group: for multipliers `λ`, a plan `γ` of the
two (uniform) centres, `Ψ = R + η (√E_γ{h(X)−h(Y)}² + √T₀(h,λ₀) + √T₁(h,λ₁))²`. -/
def jointObj {n₀ n₁ : ℕ} (x₀ : Fin n₀ → K) (x₁ : Fin n₁ → K) (c : K → K → ℝ) (h : K → ℝ) (ε r₀ r₁ : ℝ)
    (ν₀ ν₁ : Measure K) (Rh η lam₀ lam₁ : ℝ) (γ : Fin n₀ → Fin n₁ → ℝ) : ℝ :=
  Rh + η * (√(StatFormal.RobustEquality.Paper2.Alternating.pcost (fun i => h (x₀ i)) (fun j => h (x₁ j)) γ) +
    √(StatFormal.RobustEquality.Certificate.Tref1 x₀ c h ε r₀ lam₀ ν₀) +
    √(StatFormal.RobustEquality.Certificate.Tref1 x₁ c h ε r₁ lam₁ ν₁)) ^ 2

/-- The objective of `(P_η)` at the rule `h` and multipliers `λ`: `R + η F̄(h; λ)`, `Δ(h) = W₂(h#P̂₀, h#P̂₁)`. -/
def penObj {n₀ n₁ : ℕ} (x₀ : Fin n₀ → K) (x₁ : Fin n₁ → K) (c : K → K → ℝ) (h : K → ℝ) (ε r₀ r₁ : ℝ)
    (ν₀ ν₁ : Measure K) (Rh η lam₀ lam₁ : ℝ) : ℝ :=
  Rh + η * ((wassersteinEDist 2 ((StatFormal.RobustEquality.Certificate.centre x₀).map h)
      ((StatFormal.RobustEquality.Certificate.centre x₁).map h)).toReal +
    √(StatFormal.RobustEquality.Certificate.Tref1 x₀ c h ε r₀ lam₀ ν₀) +
    √(StatFormal.RobustEquality.Certificate.Tref1 x₁ c h ε r₁ lam₁ ν₁)) ^ 2

/-- The `lem:kernel` ball `{Q ∈ 𝒫(K) : Q ∈ 𝓑^{{ν}}(P̂; r)}` (frozen `KernelWitness` form). -/
def kerBall {n : ℕ} (x : Fin n → K) (c : K → K → ℝ) (ε r : ℝ) (ν : Measure K) : Set (Measure K) :=
  {Q | IsProbabilityMeasure Q ∧ StatFormal.RobustEquality.Certificate.KernelWitness x c ε r ν Q}

end JointMin

section JointMinFree

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open StatFormal.RobustEquality.Paper2.Seminorm in
/-- The joint objective at the free end (mixture class, finite `L`), linear rule `h_w`: with dual variables `z_s`,
`Ψ = R + η (√E_γ⟨w, X − Y⟩² + √(λ₀ r₀ − n₀⁻¹ Σ z⁰) + √(λ₁ r₁ − n₁⁻¹ Σ z¹))²`. -/
def jointObjFree {n₀ n₁ : ℕ} (x₀ : Fin n₀ → E) (x₁ : Fin n₁ → E) (w : E) (r₀ r₁ Rh η lam₀ lam₁ : ℝ)
    (γ : Fin n₀ → Fin n₁ → ℝ) (z₀ : Fin n₀ → ℝ) (z₁ : Fin n₁ → ℝ) : ℝ :=
  Rh + η * (√(StatFormal.RobustEquality.Paper2.Alternating.pcost (fun i => ⟪w, x₀ i⟫) (fun j => ⟪w, x₁ j⟫) γ) +
    √(lam₀ * r₀ - (1 / (n₀ : ℝ)) * ∑ i, z₀ i) + √(lam₁ * r₁ - (1 / (n₁ : ℝ)) * ∑ i, z₁ i)) ^ 2

end JointMinFree

/-! ### ICL `prop:cond-weight-mixing` -/

section WeightMixing

variable {𝒵 Γ : Type*} {n M R : ℕ}

/-- Risk plus penalty of the mixture of weights, i.i.d. contexts:
`f(z) = G^iid(z; w(x)) + λ Σ_r g_r(x;γ) KL(w_r | u_n)`, `w(x) = Σ_r g_r(x;γ) w_r`. -/
def fMixIid (g : 𝒵 → Γ → Fin R → ℝ) (L : 𝒵 → (Fin M → Fin n) → ℝ) (lam : ℝ) (γ : Γ)
    (W : Fin R → Fin n → ℝ) (z : 𝒵) : ℝ :=
  StatFormal.Wave12c.Giid (StatFormal.Wave16a.mixW (g z γ) W) M (L z) +
    lam * ∑ r, g z γ r * StatFormal.ICL.Diag.klUnif n (W r)

/-- The same without replacement: `G(z; w(x)) = Σ_{|T| = M} Π_{w(x)}(T) L(z; z_T)`. -/
def fMixSwor (M : ℕ) (g : 𝒵 → Γ → Fin R → ℝ) (L : 𝒵 → Finset (Fin n) → ℝ) (lam : ℝ) (γ : Γ)
    (W : Fin R → Fin n → ℝ) (z : 𝒵) : ℝ :=
  StatFormal.ICL.Grisk (StatFormal.Wave16a.mixW (g z γ) W) M (L z) +
    lam * ∑ r, g z γ r * StatFormal.ICL.Diag.klUnif n (W r)

/-- `N` is an internal `η`-net of the gate class for `ρ^log(γ,γ') = sup_{x,r} |log g_r(x;γ) − log g_r(x;γ')|`. -/
def IsLogGateNet (g : 𝒵 → Γ → Fin R → ℝ) (η : ℝ) (N : Finset Γ) : Prop :=
  ∀ γ, ∃ γ' ∈ N, ∀ z r, |Real.log (g z γ r) - Real.log (g z γ' r)| ≤ η

/-- The bound of `prop:cond-weight-mixing`(i): `B M η + 2B √(2[K ℓ_n + R log 2 + log N + log 2]/m) + B √(log(1/δ)/(2m))`. -/
def devBoundMixI (B ℓ η δ : ℝ) (Kt R N M m : ℕ) : ℝ :=
  B * M * η + 2 * B * √(2 * (Kt * ℓ + R * Real.log 2 + Real.log N + Real.log 2) / m) +
    B * √(Real.log (1 / δ) / (2 * m))

/-- `Ξ_η = K ℓ_n + K log(1 + 16 g_min^{−M}/η) + log N + log 2` (`N` the size of the log-net at radius `η/(4M)`). -/
def xiMix (ℓ η gmin : ℝ) (Kt M N : ℕ) : ℝ :=
  Kt * ℓ + Kt * Real.log (1 + 16 * (gmin ^ M)⁻¹ / η) + Real.log N + Real.log 2

/-- The bound of `prop:cond-weight-mixing`(ii): `B η + 2B √(2 Ξ_η/m) + B √(log(1/δ)/(2m))`. -/
def devBoundMixII (B Ξ η δ : ℝ) (m : ℕ) : ℝ :=
  B * η + 2 * B * √(2 * Ξ / m) + B * √(Real.log (1 / δ) / (2 * m))

end WeightMixing

/-! ### otfd A `prop:app-fixed-soft-consistency` -/

section FixedSoft

variable {d mg : ℕ}

/-- `ε log Σ_j exp{(g_j − ‖x − u_j‖²)/ε}`. -/
def lseGrid (ε : ℝ) (u : Fin mg → EuclideanSpace ℝ (Fin d)) (g : Fin mg → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ε * Real.log (∑ j, Real.exp ((g j - ‖x - u j‖ ^ 2) / ε))

/-- The population dual objective `𝒥(g) = E[ε log Σ_j exp{(g_j − c_j(X))/ε}] − m⁻¹ Σ_j g_j`. -/
def Jpop (ε : ℝ) (u : Fin mg → EuclideanSpace ℝ (Fin d)) (P : Measure (EuclideanSpace ℝ (Fin d)))
    (g : Fin mg → ℝ) : ℝ :=
  ∫ x, lseGrid ε u g x ∂P - (1 / (mg : ℝ)) * ∑ j, g j

/-- The empirical dual objective `𝒥_n(g) = n⁻¹ Σ_i ε log Σ_j exp{(g_j − c_j(X_i))/ε} − m⁻¹ Σ_j g_j`. -/
def Jemp {n : ℕ} (ε : ℝ) (u : Fin mg → EuclideanSpace ℝ (Fin d)) (X : Fin n → EuclideanSpace ℝ (Fin d))
    (g : Fin mg → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, lseGrid ε u g (X i) - (1 / (mg : ℝ)) * ∑ j, g j

/-- The Gibbs weights `p^g_j(x) = softmax_j{(g_j − ‖x − u_j‖²)/ε}`. -/
def softP (ε : ℝ) (u : Fin mg → EuclideanSpace ℝ (Fin d)) (g : Fin mg → ℝ) (x : EuclideanSpace ℝ (Fin d))
    (j : Fin mg) : ℝ :=
  Real.exp ((g j - ‖x - u j‖ ^ 2) / ε) / ∑ l, Real.exp ((g l - ‖x - u l‖ ^ 2) / ε)

/-- The barycentric map `T^g(x) = Σ_j p^g_j(x) u_j`. -/
def baryT (ε : ℝ) (u : Fin mg → EuclideanSpace ℝ (Fin d)) (g : Fin mg → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  ∑ j, softP ε u g x j • u j

end FixedSoft

namespace Claims

open StatFormal.RobustEquality.Certificate StatFormal.RobustEquality.Strong
local notation "Wdisc" => StatFormal.RobustEquality.Tax.Wdisc

/-! #### JASA `prop:tax` -/

/-- (a), the point-mass bound: `0 ≤ ϰ(β) ≤ log(√(2π) β) + 1/(24β²)` for `β > 0` (mixing law `m = δ₀`). -/
def tax_a_bound : Prop :=
  ∀ β : ℝ, 0 < β → 0 ≤ varkappa β ∧ varkappa β ≤ ((Real.log (√(2 * Real.pi) * β) + 1 / (24 * β ^ 2) : ℝ) : EReal)

/-- (a), monotonicity: `ϰ` is nondecreasing on `(0, ∞)`. -/
def tax_a_mono : Prop := MonotoneOn varkappa (Ioi 0)

/-- (a), the limit: `ϰ(β) → 0` as `β ↓ 0`. -/
def tax_a_lim : Prop := Tendsto varkappa (𝓝[>] 0) (𝓝 0)

/-- (c), CONDITIONAL on (b): if `τ_𝒩(P) ≤ E_{P^rec} g` (the bound of (b)) and `g` has the a priori range
`[g₋, g₊]`, then with probability `≥ 1 − a` over `n` i.i.d. recorded values,
`τ_𝒩(P) ≤ ḡ + (g₊ − g₋) √(log(1/a)/(2n))`. -/
def tax_c : Prop :=
  ∀ (Y K : Type) [MeasurableSpace Y] [MeasurableSpace K] (Prec : Measure Y) [IsProbabilityMeasure Prec]
    (𝒩 : Set (Measure K)) (P : Measure K) (g : Y → ℝ) (gm gp a : ℝ) (n : ℕ),
    0 < n → 0 < a → a ≤ 1 → Measurable g → (∀ y, gm ≤ g y ∧ g y ≤ gp) →
    StatFormal.RobustEquality.Tax.tax 𝒩 P ≤ ((∫ y, g y ∂Prec : ℝ) : EReal) →
      ∃ E : Set (Fin n → Y), MeasurableSet E ∧ ENNReal.ofReal (1 - a) ≤ Measure.pi (fun _ : Fin n => Prec) E ∧
        E ⊆ {y | StatFormal.RobustEquality.Tax.tax 𝒩 P ≤
          (((1 / (n : ℝ)) * ∑ i, g (y i) + (gp - gm) * √(Real.log (1 / a) / (2 * n)) : ℝ) : EReal)}

/-! #### JASA `prop:ddradius` -/

/-- The plug-in `KL(P̂ ‖ ν_q)` of `prop:ddradius`(E2) is the paper's `KL` when the points lie in `A`, `q > 0` on `A`. -/
def dd_plugin_kl : Prop :=
  ∀ (K ι : Type) [MeasurableSpace K] [MeasurableSingletonClass K] [Fintype ι] [Nonempty ι] (A : Finset K)
    (q : K → ℝ) (y : ι → K),
    (∀ a ∈ A, 0 < q a) → (∀ j, y j ∈ A) →
      klRef (StatFormal.RobustEquality.CoverageRandom.empOn y) (massRef A q) = ((klPlug A q y : ℝ) : EReal)

/-- `prop:ddradius` under (E2): `P` supported on a known finite set `A`; for each fold a reference with mass function
`q_v > 0` on `A` (built from fold `v` alone, `Σ_A q_v ≤ 1`) whose `−log q_v` has range `≤ R_v` on `A`; then with
probability `≥ 1 − a`, `W^ν_ε(P̂, P) ≤ r̂`, `ν = Σ_v w_v ν_v`. -/
def dd_radius_E2 : Prop :=
  ∀ (K : Type) [MeasurableSpace K] [MeasurableSingletonClass K] (P : Measure K) [IsProbabilityMeasure P]
    (A : Finset K) (N V : ℕ) (fold : Fin N → Fin V) (n : Fin V → ℕ) (e : ∀ v, Fin (n v) ≃ {i // fold i = v})
    (c : K → K → ℝ) (B Bc ε a : ℝ) (q : Fin V → (Fin N → K) → K → ℝ) (R : Fin V → ℝ),
    Function.Surjective fold → (∀ v, ∃ i, ¬ fold i = v) → Measurable (Function.uncurry c) →
    (∀ x y, |c x y| ≤ B) → 0 < ε → 0 < Bc → (∀ x y y', c x y - c x y' ≤ Bc) → 0 < a → a < 1 → 0 < N →
    P (↑A)ᶜ = 0 →
    (∀ v, FoldOnly fold v (q v)) → (∀ v y, Measurable fun X => q v X y) →
    (∀ v X, ∀ y ∈ A, 0 < q v X y) → (∀ v X, ∑ y ∈ A, q v X y ≤ 1) →
    (∀ v X, ∀ y ∈ A, ∀ y' ∈ A, Real.log (q v X y) - Real.log (q v X y') ≤ R v) →
      ∃ E : Set (Fin N → K), MeasurableSet E ∧ ENNReal.ofReal (1 - a) ≤ Measure.pi (fun _ : Fin N => P) E ∧
        E ⊆ {X | Wdisc ε (fun _ : Fin N => (1 : ℝ) / N) (fun i => c (X i))
            (foldMix (fun v => massRef A (q v X)) n N) P ≤ (ddRadiusE2 ε Bc a c e A q R X : EReal)}

/-- `prop:ddradius` under (E1): `P = p · λ` for a σ-finite base `λ` with `∫ p log p dλ ≤ H̄`; for each fold a reference
`ν_v = q_v · λ` (built from fold `v` alone, `ν_v(K) ≤ 1`, `q_v > 0`) whose `−log q_v` has range `≤ R_v`; then with
probability `≥ 1 − a`, `W^ν_ε(P̂, P) ≤ r̂`, `ν = Σ_v w_v ν_v`. -/
def dd_radius_E1 : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (lam : Measure K) [SigmaFinite lam] (p : K → ℝ) (N V : ℕ)
    (fold : Fin N → Fin V) (n : Fin V → ℕ) (e : ∀ v, Fin (n v) ≃ {i // fold i = v})
    (c : K → K → ℝ) (B Bc ε a Hbar : ℝ) (q : Fin V → (Fin N → K) → K → ℝ) (R : Fin V → ℝ),
    Function.Surjective fold → (∀ v, ∃ i, ¬ fold i = v) → Measurable (Function.uncurry c) →
    (∀ x y, |c x y| ≤ B) → 0 < ε → 0 < Bc → (∀ x y y', c x y - c x y' ≤ Bc) → 0 < a → a < 1 → 0 < N →
    Measurable p → (∀ y, 0 ≤ p y) → IsProbabilityMeasure (densRef lam p) →
    Integrable (fun y => p y * Real.log (p y)) lam → ∫ y, p y * Real.log (p y) ∂lam ≤ Hbar →
    (∀ v, FoldOnly fold v (q v)) → (∀ v, Measurable fun z : (Fin N → K) × K => q v z.1 z.2) →
    (∀ v X y, 0 < q v X y) → (∀ v X, densRef lam (q v X) Set.univ ≤ 1) →
    (∀ v X y y', Real.log (q v X y) - Real.log (q v X y') ≤ R v) →
      ∃ E : Set (Fin N → K), MeasurableSet E ∧
        ENNReal.ofReal (1 - a) ≤ Measure.pi (fun _ : Fin N => densRef lam p) E ∧
        E ⊆ {X | Wdisc ε (fun _ : Fin N => (1 : ℝ) / N) (fun i => c (X i))
            (foldMix (fun v => densRef lam (q v X)) n N) (densRef lam p) ≤
          (ddRadiusE1 ε Bc a Hbar c e q R X : EReal)}

/-! #### JASA `prop:fl-radius` -/

/-- `prop:fl-radius`, CONDITIONAL on `prop:fl-negent` (assumed: a measurable event of probability `≥ 1 − δ₁ − δ₂` on
which `N(P̃) ≤ N̂`), with any deviation terms `dev_v` valid for `thm:coverage` (assumed: per fold, a measurable event of
probability `≥ 1 − ℓ_v δ` on which `OT_ε(μ_v, P̃) ≤ OT_ε(μ_v, Q̂_{−v}) + dev_v`): with probability
`≥ 1 − Σ_v (ℓ_v + 1)δ − δ₁ − δ₂`, `W^ν_ε(μ, P̃) ≤ r̂`, `μ = Σ_v w_v μ_v` (uniform on the `N` atoms), `ν = Σ_v w_v ν_v`. -/
def fl_radius : Prop :=
  ∀ (d : ℕ) (Ω Z : Type) [MeasurableSpace Ω] [MeasurableSpace Z] (Pr : Measure Ω)
    (K J C : Set (EuclideanSpace ℝ (Fin d))) (P : Measure (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ) (ε Bc δ δ₁ δ₂ : ℝ)
    (N V : ℕ) (fold : Fin N → Fin V) (k : Fin V → ℕ) (e : ∀ v, Fin (k v) ≃ {i // fold i = v})
    (x : Ω → Fin N → EuclideanSpace ℝ (Fin d)) (D : Fin V → Ω → Z)
    (A : ∀ v, Z → Fin (k v) → EuclideanSpace ℝ (Fin d)) (q : Fin V → Z → EuclideanSpace ℝ (Fin d) → ℝ)
    (R : Fin V → ℝ) (m : Fin V → ℕ) (Y : ∀ v, Fin (m v) → Ω → EuclideanSpace ℝ (Fin d))
    (dev : Fin V → Ω → ℝ) (ℓ : Fin V → ℕ) (Nhat : Ω → ℝ),
    FlSetting Pr K J C P c ε Bc fold e x D A q R Y → 0 < δ → δ ≤ 1 →
    (∀ v, ∃ T : Set Ω, MeasurableSet T ∧ ENNReal.ofReal (1 - ℓ v * δ) ≤ Pr T ∧
      ∀ ω ∈ T, OTdisc ε (fun _ : Fin (k v) => (1 : ℝ) / k v) (fun j => c (x ω (e v j))) (P ∗ unifOn J) ≤
        OTdisc ε (fun _ : Fin (k v) => (1 : ℝ) / k v) (fun j => c (x ω (e v j)))
          (StatFormal.RobustEquality.Coverage.empMeasure fun j => Y v j ω) + ((dev v ω : ℝ) : EReal)) →
    (∃ F : Set Ω, MeasurableSet F ∧ ENNReal.ofReal (1 - δ₁ - δ₂) ≤ Pr F ∧ ∀ ω ∈ F, negEnt P J ≤ Nhat ω) →
      ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - ∑ v, ((ℓ v : ℝ) + 1) * δ - δ₁ - δ₂) ≤ Pr E ∧
        ∀ ω ∈ E, Wdisc ε (fun _ : Fin N => (1 : ℝ) / N) (fun i => c (x ω i)) (flRef (N := N) (k := k) C q D ω) (P ∗ unifOn J) ≤
          (flRadius ε δ c e x D q R Y dev Nhat ω : EReal)

/-- `prop:fl-radius` with the Hoeffding deviation term of `thm:coverage` (`dev_v = B_c √(log(1/δ)/(2m_v))`, one event
per fold, PROVED here, not assumed), CONDITIONAL on `prop:fl-negent` only: with probability `≥ 1 − Σ_v 2δ − δ₁ − δ₂`,
`W^ν_ε(μ, P̃) ≤ r̂`. -/
def fl_radius_hoeffding : Prop :=
  ∀ (d : ℕ) (Ω Z : Type) [MeasurableSpace Ω] [MeasurableSpace Z] (Pr : Measure Ω)
    (K J C : Set (EuclideanSpace ℝ (Fin d))) (P : Measure (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ) (ε Bc δ δ₁ δ₂ : ℝ)
    (N V : ℕ) (fold : Fin N → Fin V) (k : Fin V → ℕ) (e : ∀ v, Fin (k v) ≃ {i // fold i = v})
    (x : Ω → Fin N → EuclideanSpace ℝ (Fin d)) (D : Fin V → Ω → Z)
    (A : ∀ v, Z → Fin (k v) → EuclideanSpace ℝ (Fin d)) (q : Fin V → Z → EuclideanSpace ℝ (Fin d) → ℝ)
    (R : Fin V → ℝ) (m : Fin V → ℕ) (Y : ∀ v, Fin (m v) → Ω → EuclideanSpace ℝ (Fin d)) (Nhat : Ω → ℝ),
    FlSetting Pr K J C P c ε Bc fold e x D A q R Y → 0 < δ → δ ≤ 1 →
    (∃ F : Set Ω, MeasurableSet F ∧ ENNReal.ofReal (1 - δ₁ - δ₂) ≤ Pr F ∧ ∀ ω ∈ F, negEnt P J ≤ Nhat ω) →
      ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - ∑ _v : Fin V, 2 * δ - δ₁ - δ₂) ≤ Pr E ∧
        ∀ ω ∈ E, Wdisc ε (fun _ : Fin N => (1 : ℝ) / N) (fun i => c (x ω i)) (flRef (N := N) (k := k) C q D ω) (P ∗ unifOn J) ≤
          (flRadius ε δ c e x D q R Y (hoeffDev Bc δ m) Nhat ω : EReal)

/-- The frozen `thm:fl-coverage` (`Wave19b.Claims.fl_coverage`) with its `prop:fl-radius` hypothesis DISCHARGED: the
centres, references and radii are those of `prop:fl-radius` (Hoeffding deviation terms, `U_θ = U_{J_θ}`), each group
and grid point at total level `Σ_v 2δ + δ₁ + δ₂ ≤ α/(2|𝒢|)`; what remains assumed is `prop:fl-negent` (one measurable
event per group and grid point, of probability `≥ 1 − δ₁ − δ₂`, on which `N(P_s ∗ U_θ) ≤ N̂`). Conclusion: verbatim
the frozen one. -/
def fl_coverage_discharged : Prop :=
  ∀ (d : ℕ) (Ω G Z : Type) [MeasurableSpace Ω] [Fintype G] [Nonempty G] [MeasurableSpace Z] (Pr : Measure Ω)
    (K C : Set (EuclideanSpace ℝ (Fin d))) (J : G → Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ) (ε α Bc : ℝ)
    (P : Fin 2 → Measure (EuclideanSpace ℝ (Fin d)))
    (N V : G → Fin 2 → ℕ) (fold : ∀ θ s, Fin (N θ s) → Fin (V θ s)) (k : ∀ θ s, Fin (V θ s) → ℕ)
    (e : ∀ θ s v, Fin (k θ s v) ≃ {i // fold θ s i = v})
    (x : ∀ θ s, Ω → Fin (N θ s) → EuclideanSpace ℝ (Fin d)) (D : ∀ θ s, Fin (V θ s) → Ω → Z)
    (A : ∀ θ s v, Z → Fin (k θ s v) → EuclideanSpace ℝ (Fin d))
    (q : ∀ θ s, Fin (V θ s) → Z → EuclideanSpace ℝ (Fin d) → ℝ) (R : ∀ θ s, Fin (V θ s) → ℝ)
    (m : ∀ θ s, Fin (V θ s) → ℕ) (Y : ∀ θ s v, Fin (m θ s v) → Ω → EuclideanSpace ℝ (Fin d))
    (Nhat : G → Fin 2 → Ω → ℝ) (δ δ₁ δ₂ : G → Fin 2 → ℝ),
    0 < α → α < 1 → (∀ a b, 0 ≤ c a b) →
    (∀ θ s, FlSetting Pr K (J θ) C (P s) c ε Bc (fold θ s) (e θ s) (x θ s) (D θ s) (A θ s) (q θ s) (R θ s) (Y θ s)) →
    (∀ θ s, 0 < δ θ s ∧ δ θ s ≤ 1) →
    (∀ θ s, ∑ _v : Fin (V θ s), 2 * δ θ s + δ₁ θ s + δ₂ θ s ≤ α / (2 * Fintype.card G)) →
    (∀ θ s, ∃ F : Set Ω, MeasurableSet F ∧ ENNReal.ofReal (1 - δ₁ θ s - δ₂ θ s) ≤ Pr F ∧
      ∀ ω ∈ F, negEnt (P s) (J θ) ≤ Nhat θ s ω) →
      ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - α) ≤ Pr E ∧
        ∀ ω ∈ E, ∀ (θ : G) (h : EuclideanSpace ℝ (Fin d) → ℝ) (lam : Fin 2 → ℝ),
          Measurable h → (∃ H, ∀ z, |h z| ≤ H) → (∀ s, 0 < lam s) →
            wassersteinEDist 2 ((P 0).map h) ((P 1).map h) ≤
              wassersteinEDist 2 ((centre (x θ 0 ω)).map h) ((centre (x θ 1 ω)).map h) +
                ENNReal.ofReal √(Tref1 (x θ 0 ω) c h ε
                  (flRadius ε (δ θ 0) c (e θ 0) (x θ 0) (D θ 0) (q θ 0) (R θ 0) (Y θ 0)
                    (hoeffDev Bc (δ θ 0) (m θ 0)) (Nhat θ 0) ω) (lam 0) (flRef (N := N θ 0) (k := k θ 0) C (q θ 0) (D θ 0) ω)) +
                ENNReal.ofReal √(Tref1 (x θ 1 ω) c h ε
                  (flRadius ε (δ θ 1) c (e θ 1) (x θ 1) (D θ 1) (q θ 1) (R θ 1) (Y θ 1)
                    (hoeffDev Bc (δ θ 1) (m θ 1)) (Nhat θ 1) ω) (lam 1) (flRef (N := N θ 1) (k := k θ 1) C (q θ 1) (D θ 1) ω)) +
                2 * StatFormal.Wave18a.jitterPrice K h (unifOn (J θ))

/-- The frozen `thm:fl-coverage` with BOTH hypotheses discharged: as `fl_coverage_discharged`, with `N̂` the
data-driven negentropy bound of the certified `prop:fl-negent` (frozen Wave 21b `negentHat`), computed from `n_E`
sample points `Xe` and `n_E × R_E` jitters `Ue` whose joint law is `P_s^{n_E} ⊗ U_θ^{n_E R_E}`. Unconditional. -/
def fl_coverage_unconditional : Prop :=
  ∀ (d : ℕ) (Ω G Z : Type) [MeasurableSpace Ω] [Fintype G] [Nonempty G] [MeasurableSpace Z] (Pr : Measure Ω)
    (K C : Set (EuclideanSpace ℝ (Fin d))) (J : G → Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ) (ε α Bc : ℝ)
    (P : Fin 2 → Measure (EuclideanSpace ℝ (Fin d)))
    (N V : G → Fin 2 → ℕ) (fold : ∀ θ s, Fin (N θ s) → Fin (V θ s)) (k : ∀ θ s, Fin (V θ s) → ℕ)
    (e : ∀ θ s v, Fin (k θ s v) ≃ {i // fold θ s i = v})
    (x : ∀ θ s, Ω → Fin (N θ s) → EuclideanSpace ℝ (Fin d)) (D : ∀ θ s, Fin (V θ s) → Ω → Z)
    (A : ∀ θ s v, Z → Fin (k θ s v) → EuclideanSpace ℝ (Fin d))
    (q : ∀ θ s, Fin (V θ s) → Z → EuclideanSpace ℝ (Fin d) → ℝ) (R : ∀ θ s, Fin (V θ s) → ℝ)
    (m : ∀ θ s, Fin (V θ s) → ℕ) (Y : ∀ θ s v, Fin (m θ s v) → Ω → EuclideanSpace ℝ (Fin d))
    (nE RE : G → Fin 2 → ℕ) (Xe : ∀ θ s, Ω → Fin (nE θ s) → EuclideanSpace ℝ (Fin d))
    (Ue : ∀ θ s, Ω → Fin (nE θ s) × Fin (RE θ s) → EuclideanSpace ℝ (Fin d)) (δ δ₁ δ₂ : G → Fin 2 → ℝ),
    0 < α → α < 1 → (∀ a b, 0 ≤ c a b) →
    (∀ θ s, FlSetting Pr K (J θ) C (P s) c ε Bc (fold θ s) (e θ s) (x θ s) (D θ s) (A θ s) (q θ s) (R θ s) (Y θ s)) →
    (∀ θ s, 0 < δ θ s ∧ δ θ s ≤ 1) →
    (∀ θ s, ∑ _v : Fin (V θ s), 2 * δ θ s + δ₁ θ s + δ₂ θ s ≤ α / (2 * Fintype.card G)) →
    (∀ θ s, 0 < nE θ s ∧ 0 < RE θ s) →
    (∀ θ s, 0 < δ₁ θ s ∧ δ₁ θ s ≤ 1 ∧ 0 < δ₂ θ s ∧ δ₂ θ s ≤ 1) →
    (∀ θ s, Measurable fun ω => (Xe θ s ω, Ue θ s ω)) →
    (∀ θ s, Pr.map (fun ω => (Xe θ s ω, Ue θ s ω)) =
      (Measure.pi fun _ : Fin (nE θ s) => P s).prod (Measure.pi fun _ : Fin (nE θ s) × Fin (RE θ s) => unifOn (J θ))) →
      ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - α) ≤ Pr E ∧
        ∀ ω ∈ E, ∀ (θ : G) (h : EuclideanSpace ℝ (Fin d) → ℝ) (lam : Fin 2 → ℝ),
          Measurable h → (∃ H, ∀ z, |h z| ≤ H) → (∀ s, 0 < lam s) →
            wassersteinEDist 2 ((P 0).map h) ((P 1).map h) ≤
              wassersteinEDist 2 ((centre (x θ 0 ω)).map h) ((centre (x θ 1 ω)).map h) +
                ENNReal.ofReal √(Tref1 (x θ 0 ω) c h ε
                  (flRadius ε (δ θ 0) c (e θ 0) (x θ 0) (D θ 0) (q θ 0) (R θ 0) (Y θ 0)
                    (hoeffDev Bc (δ θ 0) (m θ 0))
                    (fun ω => StatFormal.Wave21b.negentHat (J θ) (nE θ 0) (RE θ 0) (δ₁ θ 0) (δ₂ θ 0) (Xe θ 0 ω) (Ue θ 0 ω)) ω)
                  (lam 0) (flRef (N := N θ 0) (k := k θ 0) C (q θ 0) (D θ 0) ω)) +
                ENNReal.ofReal √(Tref1 (x θ 1 ω) c h ε
                  (flRadius ε (δ θ 1) c (e θ 1) (x θ 1) (D θ 1) (q θ 1) (R θ 1) (Y θ 1)
                    (hoeffDev Bc (δ θ 1) (m θ 1))
                    (fun ω => StatFormal.Wave21b.negentHat (J θ) (nE θ 1) (RE θ 1) (δ₁ θ 1) (δ₂ θ 1) (Xe θ 1 ω) (Ue θ 1 ω)) ω)
                  (lam 1) (flRef (N := N θ 1) (k := k θ 1) C (q θ 1) (D θ 1) ω)) +
                2 * StatFormal.Wave18a.jitterPrice K h (unifOn (J θ))

/-! #### JASA `lem:ad-linear` -/

open StatFormal.Wave15a (lamMod) in
/-- Upper bounds: `Λ_P(φ; r) ≤ rG + √(r²G² + 2rσ²) ≤ σ√(2r) + 2rG`, `G = H − Pφ` for any `H ≥ sup_K φ`
(the paper's `H = sup_K φ`), `σ² = Var_P φ`. -/
def ad_linear_upper : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (P : Measure K) [IsProbabilityMeasure P] (φ : K → ℝ) (H r : ℝ),
    Measurable φ → (∃ L, ∀ x, L ≤ φ x) → (∀ x, φ x ≤ H) → 0 ≤ r →
      lamMod P φ r ≤ ((r * (H - ∫ x, φ x ∂P) +
          √(r ^ 2 * (H - ∫ x, φ x ∂P) ^ 2 + 2 * r * variance φ P) : ℝ) : EReal) ∧
      r * (H - ∫ x, φ x ∂P) + √(r ^ 2 * (H - ∫ x, φ x ∂P) ^ 2 + 2 * r * variance φ P) ≤
        √(variance φ P) * √(2 * r) + 2 * r * (H - ∫ x, φ x ∂P)

open StatFormal.Wave15a (lamMod) in
/-- Lower bound: `σ√(2r) − 2r b₋ ≤ Λ_P(φ; r)`, `b₋ = Pφ − l` for any `P`-a.e. lower bound `l` of `φ`
(the paper's `l = ess inf_P φ`). -/
def ad_linear_lower : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (P : Measure K) [IsProbabilityMeasure P] (φ : K → ℝ) (l r : ℝ),
    Measurable φ → (∃ L, ∀ x, L ≤ φ x) → (∃ H, ∀ x, φ x ≤ H) → 0 ≤ r → (∀ᵐ x ∂P, l ≤ φ x) →
      ((√(variance φ P) * √(2 * r) - 2 * r * (∫ x, φ x ∂P - l) : ℝ) : EReal) ≤ lamMod P φ r

/-- `K_inf`, the Donsker–Varadhan direction (any `K`): if `Qφ ≥ μ`, `μ < H`, `H ≥ sup_K φ`, then
`E_P log(1 − θ z_μ) ≤ KL(P ‖ Q)` for every `θ ∈ [0, 1)`. -/
def ad_linear_kinf_dv : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (P Q : Measure K) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : K → ℝ) (H μ θ : ℝ),
    Measurable φ → (∃ L, ∀ x, L ≤ φ x) → (∀ x, φ x ≤ H) → μ < H → 0 ≤ θ → θ < 1 → μ ≤ ∫ x, φ x ∂Q →
      ENNReal.ofReal (kinfObj P φ H μ θ) ≤ InformationTheory.klDiv P Q

/-- `K_inf` duality on a finite `K` (the maximiser of `φ` exists): for `μ < max_K φ`,
`inf{KL(P ‖ Q) : Q ∈ 𝒫(K), Qφ ≥ μ}` is attained and equals `sup_{θ ∈ [0,1)} E_P log(1 − θ z_μ)` (= the paper's
`max_{θ ∈ [0,1]}`). -/
def ad_linear_kinf : Prop :=
  ∀ (K : Type) [Fintype K] [Nonempty K] [MeasurableSpace K] [MeasurableSingletonClass K] (P : Measure K)
    [IsProbabilityMeasure P] (φ : K → ℝ) (μ : ℝ),
    μ < ⨆ x, φ x →
      ∃ kv : ℝ, IsLUB (kinfObj P φ (⨆ x, φ x) μ '' Ico 0 1) kv ∧
        IsLeast {v | ∃ Q : Measure K, IsProbabilityMeasure Q ∧ μ ≤ ∫ x, φ x ∂Q ∧ v = InformationTheory.klDiv P Q}
          (ENNReal.ofReal kv)

open StatFormal.Wave15a (lamMod) in
/-- The profile identity on a finite `K`: `Pφ + Λ_P(φ; r) = sup{μ < max φ : K_inf(P, μ) ≤ r}`. -/
def ad_linear_profile : Prop :=
  ∀ (K : Type) [Fintype K] [Nonempty K] [MeasurableSpace K] [MeasurableSingletonClass K] (P : Measure K)
    [IsProbabilityMeasure P] (φ : K → ℝ) (r : ℝ), 0 ≤ r →
      ((∫ x, φ x ∂P : ℝ) : EReal) + lamMod P φ r =
        ⨆ (μ : ℝ) (_ : μ < ⨆ x, φ x)
          (_ : sInf {v | ∃ Q : Measure K, IsProbabilityMeasure Q ∧ μ ≤ ∫ x, φ x ∂Q ∧
            v = InformationTheory.klDiv P Q} ≤ ENNReal.ofReal r), (μ : EReal)

/-! #### paper 2 `prop:jointmin` -/

/-- Single reference per group, any bounded measurable rule and cost: every value of the joint objective `Ψ(λ, γ)`
bounds `R(h) + η F(h)` from above, `F(h) = sup_{Q_s ∈ 𝓑_s} W₂²(h#Q₀, h#Q₁)`. -/
def jointmin_upper : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n₀ n₁ : ℕ) (x₀ : Fin n₀ → K) (x₁ : Fin n₁ → K) (c : K → K → ℝ) (h : K → ℝ)
    (ε r₀ r₁ Rh η lam₀ lam₁ : ℝ) (ν₀ ν₁ : Measure K) [IsFiniteMeasure ν₀] [IsFiniteMeasure ν₁]
    (γ : Fin n₀ → Fin n₁ → ℝ),
    0 < n₀ → 0 < n₁ → 0 < ε → 0 ≤ Rh → 0 < η → 0 < lam₀ → 0 < lam₁ →
    Measurable (Function.uncurry c) → (∀ a b, 0 ≤ c a b) → (∃ B, ∀ a b, c a b ≤ B) →
    Measurable h → (∃ H, ∀ z, |h z| ≤ H) →
    ν₀ Set.univ ≠ 0 → ν₀ Set.univ ≤ 1 → ν₁ Set.univ ≠ 0 → ν₁ Set.univ ≤ 1 →
    γ ∈ StatFormal.RobustEquality.Paper2.Alternating.Plans (fun _ => (1 : ℝ) / n₀) (fun _ => (1 : ℝ) / n₁) →
      ENNReal.ofReal Rh + ENNReal.ofReal η *
          StatFormal.Wave19b.worstDisp (kerBall x₀ c ε r₀ ν₀) (kerBall x₁ c ε r₁ ν₁) h ≤
        ENNReal.ofReal (jointObj x₀ x₁ c h ε r₀ r₁ ν₀ ν₁ Rh η lam₀ lam₁ γ)

/-- Single reference per group: the infimum of `Ψ` over `(λ₀, λ₁, γ)` is the objective of `(P_η)` at `h`,
`inf_λ {R + η F̄(h; λ)}` (same greatest lower bound, for every candidate value). -/
def jointmin_inf : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n₀ n₁ : ℕ) (x₀ : Fin n₀ → K) (x₁ : Fin n₁ → K) (c : K → K → ℝ) (h : K → ℝ)
    (ε r₀ r₁ Rh η : ℝ) (ν₀ ν₁ : Measure K) (t : ℝ),
    0 < n₀ → 0 < n₁ → 0 < η → Measurable h →
      (IsGLB {v | ∃ lam₀ lam₁ γ, 0 < lam₀ ∧ 0 < lam₁ ∧
          γ ∈ StatFormal.RobustEquality.Paper2.Alternating.Plans (fun _ => (1 : ℝ) / n₀) (fun _ => (1 : ℝ) / n₁) ∧
          v = jointObj x₀ x₁ c h ε r₀ r₁ ν₀ ν₁ Rh η lam₀ lam₁ γ} t ↔
        IsGLB {v | ∃ lam₀ lam₁, 0 < lam₀ ∧ 0 < lam₁ ∧ v = penObj x₀ x₁ c h ε r₀ r₁ ν₀ ν₁ Rh η lam₀ lam₁} t)

open StatFormal.RobustEquality.Paper2.Seminorm in
/-- The free end (mixture class with finite `L`, finitely supported kernels), linear rules, finite form: every
feasible point `(λ, γ, z₀, z₁)` (`Φ_y(z_s, w, λ_s) ≤ 0` for all `y`) has `Ψ ≥ R + η (Δ + √T^𝒩₀ + √T^𝒩₁)²` (the
certificate at `λ`, `T^𝒩_s = max_m T`), and the infimum of `Ψ` over feasible points is `inf_λ {R + η F̄(w; λ)}`. -/
def jointmin_free : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n₀ n₁ p s : ℕ) (ε r₀ r₁ Rh η : ℝ)
    (x₀ : Fin n₀ → E) (x₁ : Fin n₁ → E) (κ : Fin p → Fin s → ℝ) (ξ : Fin s → E) (w : E),
    0 < n₀ → 0 < n₁ → 0 < p → 0 < ε → 0 < η → (∀ y k, 0 ≤ κ y k) → (∀ y, 0 < ∑ k, κ y k) →
      (∀ lam₀ lam₁ γ z₀ z₁ T₀ T₁, 0 < lam₀ → 0 < lam₁ →
        γ ∈ StatFormal.RobustEquality.Paper2.Alternating.Plans (fun _ => (1 : ℝ) / n₀) (fun _ => (1 : ℝ) / n₁) →
        (∀ y, Phi ε x₀ (κ y) ξ z₀ w lam₀ ≤ 0) → (∀ y, Phi ε x₁ (κ y) ξ z₁ w lam₁ ≤ 0) →
        IsGreatest {v | ∃ m ∈ StatFormal.RobustEquality.Paper2.Seminorm.simplex p, v = Tfin ε r₀ (fun _ => 1 / (n₀ : ℝ)) x₀ (nuMix κ m) ξ w lam₀} T₀ →
        IsGreatest {v | ∃ m ∈ StatFormal.RobustEquality.Paper2.Seminorm.simplex p, v = Tfin ε r₁ (fun _ => 1 / (n₁ : ℝ)) x₁ (nuMix κ m) ξ w lam₁} T₁ →
          Rh + η * (Deltafin (fun _ => 1 / (n₀ : ℝ)) x₀ (fun _ => 1 / (n₁ : ℝ)) x₁ w + √T₀ + √T₁) ^ 2 ≤
            jointObjFree x₀ x₁ w r₀ r₁ Rh η lam₀ lam₁ γ z₀ z₁) ∧
      ∀ t : ℝ,
        IsGLB {v | ∃ lam₀ lam₁ γ z₀ z₁, 0 < lam₀ ∧ 0 < lam₁ ∧
            γ ∈ StatFormal.RobustEquality.Paper2.Alternating.Plans (fun _ => (1 : ℝ) / n₀) (fun _ => (1 : ℝ) / n₁) ∧
            (∀ y, Phi ε x₀ (κ y) ξ z₀ w lam₀ ≤ 0) ∧ (∀ y, Phi ε x₁ (κ y) ξ z₁ w lam₁ ≤ 0) ∧
            v = jointObjFree x₀ x₁ w r₀ r₁ Rh η lam₀ lam₁ γ z₀ z₁} t ↔
          IsGLB {v | ∃ lam₀ lam₁ T₀ T₁, 0 < lam₀ ∧ 0 < lam₁ ∧
            IsGreatest {u | ∃ m ∈ StatFormal.RobustEquality.Paper2.Seminorm.simplex p, u = Tfin ε r₀ (fun _ => 1 / (n₀ : ℝ)) x₀ (nuMix κ m) ξ w lam₀} T₀ ∧
            IsGreatest {u | ∃ m ∈ StatFormal.RobustEquality.Paper2.Seminorm.simplex p, u = Tfin ε r₁ (fun _ => 1 / (n₁ : ℝ)) x₁ (nuMix κ m) ξ w lam₁} T₁ ∧
            v = Rh + η * (Deltafin (fun _ => 1 / (n₀ : ℝ)) x₀ (fun _ => 1 / (n₁ : ℝ)) x₁ w + √T₀ + √T₁) ^ 2} t

/-! #### ICL `prop:cond-weight-mixing` -/

/-- (i), i.i.d. contexts: simultaneously for all `η > 0` and all internal `η`-nets of the gate class (`sup_x ‖·‖₁`),
`sup |J_m − J_pool| ≤ B M η + 2B √(2[K ℓ_n + R log 2 + log N_𝒢(η) + log 2]/m) + B √(log(1/δ)/(2m))`,
`K = |𝖠| = binom(R+M−1, M)`, `ℓ_n = M log(2n)`, `B = B_L + λ log n`. -/
def weight_mixing_i : Prop :=
  ∀ (𝒵 Γ : Type) [MeasurableSpace 𝒵] [TopologicalSpace Γ] [TopologicalSpace.SeparableSpace Γ]
    [FirstCountableTopology Γ] (P0 : Measure 𝒵) [IsProbabilityMeasure P0] (n M m R : ℕ)
    (g : 𝒵 → Γ → Fin R → ℝ) (L : 𝒵 → (Fin M → Fin n) → ℝ) (BL lam δ : ℝ),
    1 ≤ M → M ≤ n → 1 ≤ m → 0 ≤ lam → 0 < δ → δ < 1 →
    (∀ z γ r, 0 ≤ g z γ r) → (∀ z γ, ∑ r, g z γ r = 1) → (∀ z r, Continuous fun γ => g z γ r) →
    (∀ γ r, Measurable fun z => g z γ r) →
    (∀ j, Measurable fun z => L z j) → (∀ z j, 0 ≤ L z j ∧ L z j ≤ BL) →
      ∃ E : Set (Fin m → 𝒵), MeasurableSet E ∧ 1 - δ ≤ (Measure.pi fun _ : Fin m => P0).real E ∧
        E ⊆ {zt | ∀ η : ℝ, 0 < η → ∀ N : Finset Γ, StatFormal.Wave12c.IsGateNet g η N →
          ∀ (γ : Γ) (W : Fin R → Fin n → ℝ), (∀ r, W r ∈ StatFormal.Wave16a.simplexW (Fin n)) →
            |StatFormal.Wave12c.empRisk (fMixIid g L lam γ W) zt - StatFormal.Wave12c.poolRisk P0 (fMixIid g L lam γ W)| ≤
              devBoundMixI (BL + lam * Real.log n) (StatFormal.Wave12c.ellIid n M) η δ
                (StatFormal.Wave16a.typesA R M).card R N.card M m}

/-- (ii), without replacement, gates `≥ g_min > 0`, `|⋃_r supp w_r| ≥ M`: simultaneously for all `η > 0` and all
internal `η/(4M)`-nets of the gate class for `ρ^log`, `sup |J_m − J_pool| ≤ B η + 2B √(2Ξ_η/m) + B √(log(1/δ)/(2m))`,
`ℓ_n = M log(2en/M)`. -/
def weight_mixing_ii : Prop :=
  ∀ (𝒵 Γ : Type) [MeasurableSpace 𝒵] [TopologicalSpace Γ] [TopologicalSpace.SeparableSpace Γ]
    [FirstCountableTopology Γ] (P0 : Measure 𝒵) [IsProbabilityMeasure P0] (n M m R : ℕ)
    (g : 𝒵 → Γ → Fin R → ℝ) (L : 𝒵 → Finset (Fin n) → ℝ) (BL lam δ gmin : ℝ),
    1 ≤ M → M ≤ n → 1 ≤ m → 0 ≤ lam → 0 < δ → δ < 1 → 0 < gmin →
    (∀ z γ r, gmin ≤ g z γ r) → (∀ z γ, ∑ r, g z γ r = 1) → (∀ z r, Continuous fun γ => g z γ r) →
    (∀ γ r, Measurable fun z => g z γ r) →
    (∀ S, Measurable fun z => L z S) → (∀ z S, 0 ≤ L z S ∧ L z S ≤ BL) →
      ∃ E : Set (Fin m → 𝒵), MeasurableSet E ∧ 1 - δ ≤ (Measure.pi fun _ : Fin m => P0).real E ∧
        E ⊆ {zt | ∀ η : ℝ, 0 < η → ∀ N : Finset Γ, IsLogGateNet g (η / (4 * M)) N →
          ∀ (γ : Γ) (W : Fin R → Fin n → ℝ), (∀ r, W r ∈ StatFormal.Wave16a.simplexW (Fin n)) →
            M ≤ (Finset.univ.filter fun j : Fin n => ∃ r, W r j ≠ 0).card →
            |StatFormal.Wave12c.empRisk (fMixSwor M g L lam γ W) zt -
                StatFormal.Wave12c.poolRisk P0 (fMixSwor M g L lam γ W)| ≤
              devBoundMixII (BL + lam * Real.log n)
                (xiMix (StatFormal.Wave12c.ellSwor n M) η gmin (StatFormal.Wave16a.typesA R M).card M N.card) η δ m}

/-! #### otfd A `prop:app-fixed-soft-consistency` -/

/-- Existence and uniqueness of the dual optimisers: for `P` with a finite second moment, `𝒥` and every `𝒥_n` have
minimisers, unique up to an additive constant (`g' = g + t𝟙`), so the barycentric maps `T^g` are well defined. -/
def fixed_soft_dual : Prop :=
  ∀ (d mg : ℕ) (ε : ℝ) (u : Fin mg → EuclideanSpace ℝ (Fin d)) (P : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P],
    0 < mg → 0 < ε → Integrable (fun x => ‖x‖ ^ 2) P →
      (∃ gs, IsMinOn (Jpop ε u P) univ gs) ∧
      (∀ g g', IsMinOn (Jpop ε u P) univ g → IsMinOn (Jpop ε u P) univ g' → ∃ t : ℝ, g' = fun j => g j + t) ∧
      ∀ (n : ℕ) (X : Fin n → EuclideanSpace ℝ (Fin d)), 0 < n →
        (∃ g, IsMinOn (Jemp ε u X) univ g) ∧
        (∀ g g', IsMinOn (Jemp ε u X) univ g → IsMinOn (Jemp ε u X) univ g' → ∃ t : ℝ, g' = fun j => g j + t)

/-- `prop:app-fixed-soft-consistency`: for `X_1, X_2, …` i.i.d. `P` with a finite second moment and any minimisers
`ĝ_n` of `𝒥_n` (sample `X_1, …, X_n`) and `g⋆` of `𝒥`: almost surely `T^{ĝ_n} → T^{g⋆}` uniformly on `ℝ^K`, and
`E[n⁻¹ Σ_{i ≤ n} ‖T^{ĝ_n}(X_i) − T^{g⋆}(X_i)‖²] → 0` (the integrand is measurable). -/
def fixed_soft_consistency : Prop :=
  ∀ (d mg : ℕ) (ε : ℝ) (u : Fin mg → EuclideanSpace ℝ (Fin d)) (P : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P] (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (ghat : ℕ → Ω → Fin mg → ℝ) (gs : Fin mg → ℝ),
    0 < mg → 0 < ε → Integrable (fun x => ‖x‖ ^ 2) P →
    (∀ i, Measurable (X i)) → iIndepFun X Pr → (∀ i, Pr.map (X i) = P) →
    (∀ n ω, IsMinOn (Jemp ε u fun i : Fin (n + 1) => X (i : ℕ) ω) univ (ghat n ω)) → IsMinOn (Jpop ε u P) univ gs →
      (∀ᵐ ω ∂Pr, TendstoUniformly (fun n => baryT ε u (ghat n ω)) (baryT ε u gs) atTop) ∧
      (∀ n : ℕ, Measurable fun ω => (1 / ((n : ℝ) + 1)) *
        ∑ i : Fin (n + 1), ‖baryT ε u (ghat n ω) (X (i : ℕ) ω) - baryT ε u gs (X (i : ℕ) ω)‖ ^ 2) ∧
      Tendsto (fun n : ℕ => ∫ ω, (1 / ((n : ℝ) + 1)) *
        ∑ i : Fin (n + 1), ‖baryT ε u (ghat n ω) (X (i : ℕ) ω) - baryT ε u gs (X (i : ℕ) ω)‖ ^ 2 ∂Pr) atTop (𝓝 0)

end Claims

end StatFormal.Wave21a
