import StatFormal.Archive.Wave28e.Statements
import StatFormal.Archive.Wave29l.Statements
import StatFormal.Archive.Wave29w.Statements
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

/-!
# FROZEN STATEMENTS — wave 30d: paper 2 `prop:jointmin` for ENTROPIC sets (`ε > 0`, single reference) on an
# unbounded `K = E` (certificate with an unbounded Gibbs exponent, joint objective, infimum); trimmed MMD
# `thm:split` at `α = 0` with the printed nonparametric bootstrap (bootstrap-SE consistency, bootstrap CLT,
# bootstrap-SE certificate, percentile certificate)

Sources (current text, read 2026-10-20, `research-lines/`):
* paper 2 `prop:jointmin` (`robust-equality-outcomes-under-distribution-shift/paper2/main.tex:305-317`, proof
  `app_proofs.tex:47-61`), with the entropic sets `eq:BN` (`main.tex:222-226`: `{Q ∈ 𝒫(K) : inf_{γ ∈ Π(P̂,Q)}
  E_γ c + ε KL(γ ‖ P̂ ⊗ ν) ≤ r}`), the anisotropic cost (`:230-232`), `eq:F` (`:240-243`), `eq:T` (`:247-252`),
  `thm:certificate` and its proof (`:254-262`, `app_proofs.tex:14-31`: "applying `eq:gibbs` anchor by anchor with
  `τ = λε` … For a linear rule and `K = ℝ^d` every quantity above is finite for laws with finite second moments,
  which is all the argument uses"), the Gibbs principle `eq:gibbs` (`app_proofs.tex:5-12`, "`g` bounded above on the
  support of `ν`"), `eq:problems` (`main.tex:276-282`) and `lem:delta-inf` (`:296-303`). Frozen coverage: bounded
  costs (compact `K`, entropic) Wave 21a `jointmin_upper`/`jointmin_inf`; `ε = 0` Wave P2d; anisotropic `ε = 0` sets on
  an unbounded `K` Wave 28e, which declares "entropic sets (`ε > 0`) on an unbounded `K` (the Gibbs principle with an
  unbounded exponent)" not covered — the gap closed here.
* trimmed MMD `thm:split` (`trimmed-mmd/paper.tex:1166-1180`: "a variance consistently estimated by the
  nonparametric bootstrap on the scalars `f̂(X_i^{(2)})`, `f̂(Y_j^{(2)})` … asymptotic level `δ`, and rejection
  certifies `TV(P,Q) > α`"), `ass:split` (`:1154-1163`: "If `α = 0` both terms are sample means and no condition is
  imposed"), `eq:splitstat` (`:1146-1152`), proof `supplement.tex:398-413` ("the nonparametric bootstrap is consistent
  for them … The implementation takes the percentile bootstrap limit"). Frozen coverage: the bootstrap for `α > 0`
  (Wave 29l, under quantile uniqueness, unsatisfiable at `α = 0`: `splitUQ P h 1 q` asks `1 < P(h ≤ q + d)`), and
  `α = 0` with the PLUG-IN standard error only (Wave 29w, which declares the bootstrap at `α = 0` not covered).
Imports the frozen `Wave28e` statements (through them Wave 20a `ProbW`, `Polytope`, `gamNorm`, `sqrtE`;
`Paper2.Seminorm` `T0`, `Deltafin`; `Paper2.Alternating` `centre`; Wave 19b `worstDisp`; Tau Ceti `IsCoupling`,
`wassersteinEDist`), `Wave29l` (`splitBootVar`, `splitBootSE`, `splitBootSEn`, `splitBootCdfn`, `splitBootPercn`;
through it Wave 29i `splitSE`, `splitStat`, `splitSEn`, Wave 17a `sepVal`, `TrimmedMMD/Concentration` `region`,
`Distances` `tvDist`) and `Wave29w`; not copied. Mathlib `klDiv` (`InformationTheory.KullbackLeibler`) and
`ENNReal.log`. New definitions: `entBall`, `Tent`, `jointObjEnt`, `penObjEnt` (paper 2 only; no new trimmed-MMD
definition — the frozen Wave 29l bootstrap objects are used at `α = 0`).

Covered:
* paper 2, entropic sets on `K = E` (a separable real Hilbert space, so unbounded), single reference per group,
  linear rules `h_w = ⟪w, ·⟫`, ANY multiplier `λ > 0`: `jointmin_ent_group` (the groupwise certificate
  `W₂²(h_w#P̂, h_w#Q) ≤ T(w, λ)` for `Q` in the entropic set, with the exponent `(f − λc)/(λε)` allowed to be unbounded
  above), `jointmin_ent_cert` (`thm:certificate` for these sets: `W₂(h_w#Q₀, h_w#Q₁) ≤ Δ(w) + √T₀ + √T₁`),
  `jointmin_ent_upper` (`prop:jointmin`: every value of `Ψ(λ, γ)` bounds `R + ηF`), `jointmin_ent_inf`
  (`prop:jointmin`: `inf_{λ,γ} Ψ` is the objective of `(P_η)`, `inf_λ {R + η F̄}`, and is finite). The equality is
  the printed one for INDEPENDENT sets, which DEFECTS #102 kept ("a single reference … any `ε ≥ 0`"); #102 restricted
  only the STRUCTURED (cell-cover) case, which is not claimed here. Non-vacuity (route lemmas, not targets:
  `RouteEntExamples`): `jointmin_ent_nonempty` (the reference lies in its own set once `r ≥ Σ_i a_i E_ν c(x_i, ·)`),
  `jointmin_ent_unbounded` (on `ℝ` with a Gaussian reference there is `0 < λ < w²` with an exponent unbounded above at
  every anchor, `T(w, λ) < ∞` and `T⁰(w, λ) = ∞` — the claims are not confined to the bounded-exponent regime of
  `eq:gibbs`).
* trimmed MMD `thm:split` at `α = 0`, the printed bootstrap: `split_zero_boot_se` (`n ŝe*² → σ₀² = Var_P h + Var_Q h/κ` in probability with no condition, also for `σ₀² = 0`;
  `ŝe*/(σ₀/√n) → 1` if `σ₀² > 0`), `split_zero_boot_clt` (the bootstrap cdf of the root `√n (T̂* − T̂)` converges in
  probability to `Φ_{σ₀}` at every point, `σ₀² > 0`), `split_zero_level_bootstrap` (coverage, asymptotic level `δ`,
  certification `TV > 0`, UNCONDITIONAL, for `T̂ − z ŝe*`), `split_zero_boot_percentile` (the same for the percentile
  limit `splitBootPercn`, UNCONDITIONAL, including `σ₀² = 0`). Route lemma (not printed, not a target):
  `split_zero_boot_exact` (`RouteSplitBoot`; `n, m ≥ 1`: the frozen ideal bootstrap variance is `s²_X/n + s²_Y/m`,
  so the frozen bootstrap SE EQUALS the frozen plug-in SE at `α = 0`).

Not covered (declared):
* paper 2: a CLASS of references (the free end / the mixture assumption of `thm:npmle`) on an unbounded `K`, and the
  `sup_{ν ∈ 𝒩}` of `eq:T`; sub-probability references (`ν(K) ≤ 1`, the paper's convention: here `ν` is a
  probability measure, so `KL` is Mathlib's `klDiv`); non-linear rules on an unbounded `K`; structured sets with
  entropic differential sets ("the cell bounds of the companion paper"); a closed form of `inf_λ T` for `ε > 0`
  (`thm:seminorm` is not used; only finiteness is claimed); non-separable Hilbert spaces (needed for the Borel
  product structure of `E × E` in the Gibbs step; `ℝ^d` is covered).
* trimmed MMD: as in the frozen Wave 29l/29w claims — the first fold is fixed (`f̂ = f`), only the ratio regime
  `m(n)/n → κ ∈ (0, ∞)`, the ideal bootstrap (all `n^n m^m` resamples) rather than a `B`-replicate Monte Carlo, the
  `⌈δN⌉`-th order statistic instead of `np.quantile`'s interpolation; for the percentile form only the `liminf`
  coverage (what level and certification need).

Encodings (to be checked by the critic):
* paper 2: covariates in `E` (`NormedAddCommGroup`, `InnerProductSpace ℝ`, `SecondCountableTopology`, Borel); the
  weighted centre `P̂ = centre a x` with `ProbW a` (generalises `1/n_s`, labelled atoms); the cost `‖G(x' − x)‖²` with
  a continuous linear automorphism `G` (`G = id` is the printed `|x − x'|²`; `G = M^{−1/2}` the anisotropic cost, as in
  the frozen Wave 28e `anisoBall`); `entBall` is `eq:BN` at a single probability reference, LITERALLY in coupling form:
  `inf_{γ : IsCoupling γ P̂ Q} ∫⁻ c dγ + ε·klDiv(γ ‖ P̂ ⊗ ν) ≤ r` in `ℝ≥0∞` (no Markov-kernel witness, unlike the
  frozen `KernelWitness`/`kerBall` of the bounded case); `T = Tent` is `eq:T` at `{ν}` in `EReal` with
  `log = ENNReal.log` of the `ℝ≥0∞`-valued integral (`log ⊤ = ⊤`, so a divergent exponential moment gives `T = +∞`,
  never a Bochner `0`), the expectation over `P̂` as `Σ_i a_i ·` (`0 · ⊤ = 0` for an atom of weight `0`, which is not
  in `P̂`); `√T_s` is the frozen `sqrtE`; `Ψ = jointObjEnt` and the `(P_η)` objective `penObjEnt` mirror the frozen
  Wave 28e `jointObjAniso`/`penObjAniso` with `T⁰` replaced by `T`; `F(w)` is the frozen `worstDisp` over the two
  entropic sets; `R(w)` a constant `Rh ≥ 0`, `η > 0`, `λ_s` over `Ioi 0`, `γ` over the frozen `Polytope`, budgets
  `r_s ≥ 0` in the claims that involve the sets, one `ε > 0` for both groups.
* route `jointmin_ent_unbounded`: `E = ℝ`, `G = id` (`ContinuousLinearEquiv.refl`), `ν = N(0, s²)`
  (`gaussianReal`), "unbounded above" is `¬ BddAbove` of the exponent's range at each anchor `z₀`; `T⁰` is the frozen
  `Paper2.Seminorm` `T0` with budget `r`.
* trimmed MMD: the frozen Wave 29l bootstrap objects at `α = 0` literally (`splitBootVar n m 0`, `splitBootSE`,
  `splitBootSEn … 0`, `splitBootCdfn … 0`, `splitBootPercn … 0 δ`), the hypotheses of the frozen Wave 29w
  `split_zero_*` claims (for `split_zero_boot_se`/`_clt` without the fold-independence of `X` and `Y`, as in the frozen
  Wave 29l `split_boot_se`/`split_boot_clt`), `σ₀² = Var_P h + Var_Q h/κ` as in Wave 29w, "in probability" is
  `TendstoInMeasure` to a constant, `H_{0,0}` is `tvDist P Q ≤ 0`, `δ = Φ(Ioi z)`.

Junk-value audit:
* `entBall`: `ofReal r` only for `r ≥ 0` in every claim that uses a set (for `r < 0` the set would read
  `inf = 0`, not `∅`; `jointmin_ent_inf` does not use the sets); `klDiv` of probability measures is the paper's `KL`
  (`+∞` when not absolutely continuous or the log-likelihood ratio is not integrable); the cost is an `ℝ≥0∞` lower
  integral (no Bochner `0` for an infinite second moment). `Tent`: `λε > 0`, no `/0`; the integrand is `> 0` and `ν`
  is a probability, so the integral is `> 0` and `log` is never `⊥`; `log ⊤ = ⊤` is the true value. `sqrtE` truncates
  negative values to `0`, but whenever the set is non-empty `T ≥ W₂² ≥ 0` by `jointmin_ent_group`, so it is not
  truncating there (for an empty set `F = 0` and the claims are about `R + η·0`). `Measure.map` only of the continuous
  (measurable) `⟪w, ·⟫`. `Deltafin` is the `√` of an attained minimum (frozen).
  `jointmin_ent_inf` has no `r_s ≥ 0`, `Rh ≥ 0` or non-emptiness hypothesis: its equality holds pointwise in `λ`
  whatever the values of `T_s` (they do not depend on `γ`), so the truncation of `sqrtE` (possible only for an empty
  set, where the paper's `√T` is undefined) and `ofReal Rh` for `Rh < 0` enter both sides identically; the finiteness
  is genuine (`T_s ≤ λ_s r_s` at `λ_s = ‖(G_s⁻¹)ᵀw‖² + 1`). `T = +∞` makes the certificate trivially true only at
  multipliers where `+∞` is the true value; non-vacuity: the route lemmas `jointmin_ent_nonempty` and
  `jointmin_ent_unbounded` give a non-empty set and a FINITE `T` inside the unbounded-exponent regime.
* trimmed MMD: as in the frozen Wave 29l audit (`(n:ℝ)^n m^m ≥ 1`, genuine averages; `√` of a variance; the
  percentile index `⌈δN⌉₊ ∈ [1, N]` for `δ ∈ (0,1)`); the route `split_zero_boot_exact` assumes `n, m ≥ 1` (no `/0`); `σ₀²` is
  a variance of a bounded measurable function, `toNNReal` of `σ₀² > 0` is faithful; the `σ₀² = 0` cases of
  `split_zero_boot_se` (first conjunct), `split_zero_level_bootstrap` and `split_zero_boot_percentile` are genuine
  (`h(X_i) = P h`, `h(Y_j) = Q h` a.s., every replicate equals `P h − Q h`), not `√0` artefacts.

Proof notes (author of the draft, 2026-10-20; `#print axioms`: propext, Classical.choice, Quot.sound for all 8
claims and the 3 route lemmas; no `sorry`): routes `Wave30d/Route{JointMinEnt,EntExamples,SplitBoot}.lean`; new library
`Foundations/GibbsUnbounded/Basic.lean` and `Foundations/Bootstrap/AlphaZero.lean`.
* `jointmin_ent_group`: `GibbsUnbounded.coupling_gibbs` — for a coupling `γ` of `P̂` with finite cost and finite
  `KL(γ ‖ P̂ ⊗ ν)`, truncate `f = ⟪w, x' − x⟫²` at `M`, normalise ANCHOR BY ANCHOR, `g = (f_M − λc)/τ − log Z_M(x₀)`,
  so that `∫ e^g d(P̂ ⊗ ν) = 1` for every `x₀` (no disintegration of `γ`), apply the integrable Gibbs inequality
  `gibbs_le_log` (Mathlib's `integral_llr_tilted_right`; `g` integrable since `c ∈ L¹(γ)` and the first marginal is
  discrete), integrate `log Z_M(x₀)` against the first marginal `P̂`, and let `M → ∞` by monotone convergence; then a
  near-optimal coupling (budget `≤ r + δ/λ`) and Tau Ceti `wassersteinEDist_rpow_le_lintegral`; `δ ↓ 0` in `EReal`.
* `jointmin_ent_cert/upper/inf`: the Wave 28e route skeleton (`W₂` triangle inequality, `delta_plan`,
  `delta_attained` from the certified `lem:delta-inf`); finiteness at `λ = ‖(G⁻¹)ᵀw‖² + 1` (exponent `≤ 0`).
* `jointmin_ent_nonempty`: `γ = P̂ ⊗ ν`, `klDiv_self`, `lintegral_prod_le`. `jointmin_ent_unbounded`:
  `λ = w²·8s²/(8s² + ε)`, exponent `(z − x₀)²/(8s²)`, `e^{(z−x₀)²/(8s²)} ≤ e^{x₀²/(4s²)} e^{z²/(4s²)}` and the Gaussian
  density times `e^{z²/(4s²)}` is `(2πs²)^{−1/2} e^{−z²/(4s²)}` (`integrable_exp_neg_mul_sq`); `T⁰ = ⊤` by the Wave 28e
  route `T0_cases`.
* `split_zero_*`: `Bootstrap/AlphaZero` — `bootD_zero` (the duality remainder vanishes at `α = 0`), `bootVar2_zero`
  (`Var*(v̄*) = s²/n` by `bAvg_resample_sq`), `tip0_bootVar2_zero`/`tip0_bootSE_zero` (plug-in consistency
  `tip0_varLo_zero`), `tip0_bootCdf_zero` (the deterministic uniform bootstrap CLT `boot_root_unif` at `α = 0`),
  `perc_coverage_zero` (`perc_coverage_of` with `clt_zero`), `perc_le_degenerate`; the level/certification triples
  through the certified frozen `Wave29w.split_zero_level` (bootstrap SE = plug-in SE eventually) and
  `Wave22c.split_level`.

Paper notes:
(1) paper 2, `eq:gibbs` and the proof of `thm:certificate`: the Gibbs principle is stated for `g` bounded above, but
  for a linear rule on `K = ℝ^d` the exponent `g = f_{h_w}(x₀, ·) − λc(x₀, ·)` is unbounded above whenever
  `λ < ‖w‖²_M` — exactly the multipliers at which the entropic `T` can be finite while `T⁰ = ∞`
  (`jointmin_ent_unbounded`: Gaussian reference). The sentence "every quantity above is finite for laws with finite
  second moments, which is all the argument uses" holds for `E_Γ f` and `E_Γ c` but not for `T(w, λ)` itself, which
  may be `+∞` (for a Gaussian `ν` it is finite only for `λ` above a threshold below `‖w‖²`). The certificate nevertheless holds for EVERY `λ > 0` (with
  `log ∞ = ∞`): apply `eq:gibbs` to the truncations `min(f, M) − λc` (bounded above) and let `M → ∞` by monotone
  convergence; only `E_γ c < ∞` and `KL < ∞` (membership) are used. Suggested wording: "for `g` measurable with
  `E_Γ g⁻ < ∞` the inequality `E_Γ g − τ KL(Γ‖ν) ≤ τ log E_ν e^{g/τ}` holds with `log ∞ = ∞`".
(2) paper 2, proof of `thm:certificate`: with the coupling definition `eq:BN` the "Markov kernel witness" step (the
  companion paper's lemma on membership, a disintegration of `γ`) is not needed: normalising the exponent anchor by
  anchor, `g(x₀, x) − log E_ν e^{g(x₀,·)}`, makes `P̂ ⊗ ν`-exponential moment `1`, and the Gibbs inequality on the
  product gives the anchor-wise `T` directly. (Expository.)
(3) paper 2, `prop:jointmin`: correct as printed for entropic sets with a single (probability) reference on `K = ℝ^d`
  and linear rules — every value of the joint function bounds `R + ηF`, its infimum is the objective of `(P_η)`, and
  that objective is finite.
(4) trimmed MMD `thm:split` at `α = 0`: correct as printed with no condition, including `Var_P f̂ = Var_Q f̂ = 0`. At
  `α = 0` the ideal bootstrap standard error coincides EXACTLY with the plug-in standard error (`Var*(T̂*) =
  s²_X/n + s²_Y/m`, `1/n` sample variances), and the percentile limit is consistent by the classical bootstrap CLT for
  means; the citation `[Thm 19.3, Lem 21.4, §23.2]` (`L`-statistics) concerns `α > 0`; at `α = 0` the relevant result
  is the bootstrap of the mean (e.g. van der Vaart 1998, Thm 23.4). (Expository.)

Critic notes (adversarial fidelity review, 2026-10-20):
* `entBall` is `eq:BN` at `𝒩 = {ν}` literally (coupling form, `KL(γ ‖ P̂ ⊗ ν)` with the product reference, `Q ∈ 𝒫(K)`);
  Mathlib's `klDiv` of two probability measures is the paper's `KL` (its `⊤` for a non-integrable `llr` is the true
  value: the negative part of `llr` is always integrable). `Tent` is `eq:T` at `{ν}` with `f_{h_w}(x₀, x) =
  ⟪w, x − x₀⟫²` (the intercept cancels), `E_{x₀ ∼ P̂} = Σ_i a_i`, `log ⊤ = ⊤`, never `⊥`. `penObjEnt` is the
  `(P_η)` objective of `eq:problems` at fixed `w`; `jointObjEnt` the joint function of `prop:jointmin`.
* Moved out of the targets (not printed): `jointmin_ent_nonempty`, `jointmin_ent_unbounded` (non-vacuity, now
  `RouteEntExamples`) and `split_zero_boot_exact` (an exact finite identity, not a definitional one — it needs
  `capped n 0 = {uniform}` and the variance of the resampled mean — but `thm:split` prints only consistency; now a
  `RouteSplitBoot` lemma).
* Restatement: no target is implied by a frozen claim. Wave 29l `split_boot_*` assume quantile uniqueness, which is
  unsatisfiable at `α = 0`; Wave 29w `split_zero_level` is the PLUG-IN form (the proof's "its plug-in estimate … is
  equally valid"), while `split_zero_level_bootstrap` is the theorem's printed bootstrap form (a corollary of Wave 29w
  through the route identity, as Wave 29l `split_level_bootstrap` is of Wave 29i). Wave 28e `jointmin_aniso_*` and
  Wave 21a (compact `K`, kernel witness) do not contain the entropic sets on an unbounded `K`; the equality half of
  `jointmin_ent_inf` repeats the Wave 28e pattern with `T` in place of `T⁰` (low new content beyond finiteness).
* Note (1) is a genuine minor proof gap (S4; exact old/new text in the critic report). Note (4) is not a defect: §23.2
  of van der Vaart (1998) contains the bootstrap of the mean (Thm 23.4); an optional pinpoint only.

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TauCeti InformationTheory
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave30d

/-! ### paper 2 `prop:jointmin`: entropic sets (`ε > 0`, single reference) on an unbounded `K = E` -/

section JointMinEnt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] {n₀ n₁ : ℕ}

open StatFormal.RobustEquality.Paper2.Seminorm StatFormal.Wave20a
open StatFormal.RobustEquality.Paper2.Alternating (centre)

/-- The entropic set `eq:BN` with a single reference `ν` around `P̂ = Σ_i a_i δ_{x_i}`, cost
`c(x, x') = ‖G(x' − x)‖²` (`G = id`: the printed `|x − x'|²`; `G = M^{−1/2}`: anisotropic):
`{Q : inf_{γ ∈ Π(P̂,Q)} E_γ c + ε KL(γ ‖ P̂ ⊗ ν) ≤ r}`. -/
def entBall (G : E ≃L[ℝ] E) (ε : ℝ) (ν : Measure E) {n : ℕ} (a : Fin n → ℝ) (x : Fin n → E) (r : ℝ) :
    Set (Measure E) :=
  {Q | IsProbabilityMeasure Q ∧
    (⨅ (γ : Measure (E × E)) (_ : IsCoupling γ (centre a x) Q),
      (∫⁻ z, ENNReal.ofReal (‖G (z.2 - z.1)‖ ^ 2) ∂γ + ENNReal.ofReal ε * klDiv γ ((centre a x).prod ν))) ≤
      ENNReal.ofReal r}

/-- `eq:T` at a single reference for the linear rule `h_w = ⟪w, ·⟫`, cost `‖G(x − x₀)‖²`, `ε > 0`, in `EReal`:
`T(w, λ) = λ r + λ ε Σ_i a_i log E_{z ∼ ν} exp{(⟪w, z − x_i⟫² − λ ‖G(z − x_i)‖²)/(λ ε)}` (`log ⊤ = ⊤`). -/
def Tent (G : E ≃L[ℝ] E) (ε : ℝ) (ν : Measure E) {n : ℕ} (a : Fin n → ℝ) (x : Fin n → E) (r : ℝ) (w : E)
    (l : ℝ) : EReal :=
  ((l * r : ℝ) : EReal) + ((l * ε : ℝ) : EReal) * ∑ i, ((a i : ℝ) : EReal) *
    ENNReal.log (∫⁻ z, ENNReal.ofReal (Real.exp ((⟪w, z - x i⟫ ^ 2 - l * ‖G (z - x i)‖ ^ 2) / (l * ε))) ∂ν)

/-- The joint objective for independent entropic sets and the linear rule `h_w`:
`Ψ(λ, γ) = R + η (|M_γ^{1/2} w| + √T₀(w, λ₀) + √T₁(w, λ₁))²`, in `ℝ≥0∞`. -/
def jointObjEnt (G₀ G₁ : E ≃L[ℝ] E) (ε r₀ r₁ : ℝ) (ν₀ ν₁ : Measure E) (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E)
    (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (w : E) (Rh η lam₀ lam₁ : ℝ) (γ : Fin n₀ → Fin n₁ → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal Rh + ENNReal.ofReal η *
    (ENNReal.ofReal (gamNorm γ x₀ x₁ w) + sqrtE (Tent G₀ ε ν₀ a₀ x₀ r₀ w lam₀) +
      sqrtE (Tent G₁ ε ν₁ a₁ x₁ r₁ w lam₁)) ^ 2

/-- The objective of `(P_η)` at `w` and `λ` for entropic sets: `R + η (Δ(w) + √T₀ + √T₁)²`. -/
def penObjEnt (G₀ G₁ : E ≃L[ℝ] E) (ε r₀ r₁ : ℝ) (ν₀ ν₁ : Measure E) (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E)
    (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (w : E) (Rh η lam₀ lam₁ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal Rh + ENNReal.ofReal η *
    (ENNReal.ofReal (Deltafin a₀ x₀ a₁ x₁ w) + sqrtE (Tent G₀ ε ν₀ a₀ x₀ r₀ w lam₀) +
      sqrtE (Tent G₁ ε ν₁ a₁ x₁ r₁ w lam₁)) ^ 2

end JointMinEnt

namespace Claims

/-! #### paper 2 `prop:jointmin`, entropic sets on `K = E` -/

open StatFormal.RobustEquality.Paper2.Seminorm StatFormal.Wave20a
open StatFormal.RobustEquality.Paper2.Alternating (centre)

/-- The groupwise certificate (`thm:certificate`, proof `app_proofs.tex:14-31`) for an entropic set on the whole
space and a linear rule, ANY `λ > 0` (the exponent `(f − λc)/(λε)` may be unbounded above):
`W₂²(h_w#P̂, h_w#Q) ≤ T(w, λ)`, in `EReal`. -/
def jointmin_ent_group : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [SecondCountableTopology E] [MeasurableSpace E]
    [BorelSpace E] (n : ℕ) (G : E ≃L[ℝ] E) (ε r : ℝ) (ν : Measure E) [IsProbabilityMeasure ν] (a : Fin n → ℝ)
    (x : Fin n → E) (w : E) (lam : ℝ) (Q : Measure E),
    ProbW a → 0 < ε → 0 ≤ r → 0 < lam → Q ∈ entBall G ε ν a x r →
      ((wassersteinEDist 2 ((centre a x).map fun z => ⟪w, z⟫) (Q.map fun z => ⟪w, z⟫) ^ 2 : ℝ≥0∞) : EReal) ≤
        Tent G ε ν a x r w lam

/-- The certificate for independent entropic sets on `K = E` and a linear rule:
`W₂(h_w#Q₀, h_w#Q₁) ≤ Δ(w) + √T₀(w, λ₀) + √T₁(w, λ₁)`, `Δ(w) = W₂(h_w#P̂₀, h_w#P̂₁)`. -/
def jointmin_ent_cert : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [SecondCountableTopology E] [MeasurableSpace E]
    [BorelSpace E] (n₀ n₁ : ℕ) (G₀ G₁ : E ≃L[ℝ] E) (ε r₀ r₁ : ℝ) (ν₀ ν₁ : Measure E) [IsProbabilityMeasure ν₀]
    [IsProbabilityMeasure ν₁] (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (w : E)
    (lam₀ lam₁ : ℝ) (Q₀ Q₁ : Measure E),
    ProbW a₀ → ProbW a₁ → 0 < ε → 0 ≤ r₀ → 0 ≤ r₁ → 0 < lam₀ → 0 < lam₁ →
    Q₀ ∈ entBall G₀ ε ν₀ a₀ x₀ r₀ → Q₁ ∈ entBall G₁ ε ν₁ a₁ x₁ r₁ →
      wassersteinEDist 2 (Q₀.map fun z => ⟪w, z⟫) (Q₁.map fun z => ⟪w, z⟫) ≤
        wassersteinEDist 2 ((centre a₀ x₀).map fun z => ⟪w, z⟫) ((centre a₁ x₁).map fun z => ⟪w, z⟫) +
          sqrtE (Tent G₀ ε ν₀ a₀ x₀ r₀ w lam₀) + sqrtE (Tent G₁ ε ν₁ a₁ x₁ r₁ w lam₁)

/-- `prop:jointmin`, independent entropic sets on `K = E`, linear rule: every value of the joint objective
`Ψ(λ, γ)` bounds `R(w) + η F(w)` from above, `F(w) = sup_{Q_s ∈ 𝓑_s} W₂²(h_w#Q₀, h_w#Q₁)`. -/
def jointmin_ent_upper : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] (n₀ n₁ : ℕ) (G₀ G₁ : E ≃L[ℝ] E) (ε r₀ r₁ : ℝ) (ν₀ ν₁ : Measure E)
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁] (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ)
    (x₁ : Fin n₁ → E) (w : E) (Rh η lam₀ lam₁ : ℝ) (γ : Fin n₀ → Fin n₁ → ℝ),
    ProbW a₀ → ProbW a₁ → 0 < ε → 0 ≤ r₀ → 0 ≤ r₁ → 0 ≤ Rh → 0 < η → 0 < lam₀ → 0 < lam₁ →
    γ ∈ Polytope a₀ a₁ →
      ENNReal.ofReal Rh + ENNReal.ofReal η *
          StatFormal.Wave19b.worstDisp (entBall G₀ ε ν₀ a₀ x₀ r₀) (entBall G₁ ε ν₁ a₁ x₁ r₁) (fun z => ⟪w, z⟫) ≤
        jointObjEnt G₀ G₁ ε r₀ r₁ ν₀ ν₁ a₀ x₀ a₁ x₁ w Rh η lam₀ lam₁ γ

/-- `prop:jointmin`, independent entropic sets on `K = E`: the infimum of `Ψ` over `(λ₀, λ₁, γ)` is the objective
of `(P_η)`, `inf_λ {R + η F̄(w; λ)}`, and it is finite (so the bounds of `jointmin_ent_upper` are not vacuous). -/
def jointmin_ent_inf : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
    (n₀ n₁ : ℕ) (G₀ G₁ : E ≃L[ℝ] E) (ε r₀ r₁ : ℝ) (ν₀ ν₁ : Measure E) [IsProbabilityMeasure ν₀]
    [IsProbabilityMeasure ν₁] (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (w : E)
    (Rh η : ℝ),
    ProbW a₀ → ProbW a₁ → 0 < ε → 0 < η →
      (⨅ (lam₀ : Set.Ioi (0 : ℝ)) (lam₁ : Set.Ioi (0 : ℝ)) (γ : Polytope a₀ a₁),
          jointObjEnt G₀ G₁ ε r₀ r₁ ν₀ ν₁ a₀ x₀ a₁ x₁ w Rh η lam₀ lam₁ γ) =
        (⨅ (lam₀ : Set.Ioi (0 : ℝ)) (lam₁ : Set.Ioi (0 : ℝ)),
          penObjEnt G₀ G₁ ε r₀ r₁ ν₀ ν₁ a₀ x₀ a₁ x₁ w Rh η lam₀ lam₁) ∧
      (⨅ (lam₀ : Set.Ioi (0 : ℝ)) (lam₁ : Set.Ioi (0 : ℝ)),
          penObjEnt G₀ G₁ ε r₀ r₁ ν₀ ν₁ a₀ x₀ a₁ x₁ w Rh η lam₀ lam₁) < ⊤

/-! #### trimmed MMD `thm:split` at `α = 0`: the nonparametric bootstrap -/

open StatFormal.Wave29i (splitSE splitStat splitSEn)
open StatFormal.Wave29l (splitBootVar splitBootSE splitBootSEn splitBootCdfn splitBootPercn)
open StatFormal.Wave17a (sepVal)
open StatFormal.TrimmedMMD.Concentration (region)

/-- `thm:split` at `α = 0`, "a variance consistently estimated by the nonparametric bootstrap", NO condition:
`n ŝe*_n² → σ₀² = Var_P h + Var_Q h/κ` in probability (also when `σ₀² = 0`), and, if `σ₀² > 0`,
`ŝe*_n / (σ₀/√n) → 1` in probability. -/
def split_zero_boot_se : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ' κ : ℝ) (f : H)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → 𝒳) (m : ℕ → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ') →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X μ → iIndepFun Y μ →
    (∀ i, μ.map (X i) = P) → (∀ i, μ.map (Y i) = Q) →
    0 < κ → Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ) →
      TendstoInMeasure μ (fun (n : ℕ) ω => (n : ℝ) * splitBootSEn φ f X Y m 0 n ω ^ 2) atTop
          (fun _ => Var[fun x => ⟪f, φ x⟫; P] + Var[fun x => ⟪f, φ x⟫; Q] / κ) ∧
        (0 < Var[fun x => ⟪f, φ x⟫; P] + Var[fun x => ⟪f, φ x⟫; Q] / κ →
          TendstoInMeasure μ (fun (n : ℕ) ω => splitBootSEn φ f X Y m 0 n ω /
              (√(Var[fun x => ⟪f, φ x⟫; P] + Var[fun x => ⟪f, φ x⟫; Q] / κ) / √(n : ℝ))) atTop (fun _ => 1))

/-- The bootstrap CLT at `α = 0` (the classical bootstrap CLT for a difference of means): if `σ₀² > 0`, for every `t`
the bootstrap cdf of the root `√n (T̂* − T̂)` at `t` converges in probability to `N(0, σ₀²)(−∞, t]`. -/
def split_zero_boot_clt : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ' κ : ℝ) (f : H)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → 𝒳) (m : ℕ → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ') →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X μ → iIndepFun Y μ →
    (∀ i, μ.map (X i) = P) → (∀ i, μ.map (Y i) = Q) →
    0 < κ → Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ) →
    0 < Var[fun x => ⟪f, φ x⟫; P] + Var[fun x => ⟪f, φ x⟫; Q] / κ →
      ∀ t : ℝ, TendstoInMeasure μ (fun (n : ℕ) ω => splitBootCdfn φ f X Y m 0 n ω t) atTop
        (fun _ => (gaussianReal 0 (Var[fun x => ⟪f, φ x⟫; P] + Var[fun x => ⟪f, φ x⟫; Q] / κ).toNNReal).real
          (Iic t))

/-- `thm:split` at `α = 0` with the bootstrap standard error, UNCONDITIONAL (no regularity condition, no
non-degeneracy): coverage `liminf P(T̂_δ ≤ sep) ≥ 1 − δ`, asymptotic level `δ` of "reject `H_{0,0}` if `T̂_δ > 0`",
and certification `TV(P,Q) > 0` on the coverage event, for `T̂_δ = T̂_n − z ŝe*_n`, `Φ(Ioi z) = δ`. -/
def split_zero_level_bootstrap : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ' κ δ z : ℝ) (f : H)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → 𝒳) (m : ℕ → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ') →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X μ → iIndepFun Y μ →
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ → (∀ i, μ.map (X i) = P) → (∀ i, μ.map (Y i) = Q) →
    0 < κ → Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ) →
    (gaussianReal 0 1).real (Ioi z) = δ →
      (∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, 1 - δ - η ≤ μ.real {ω |
          ((splitStat φ f X Y m 0 n ω - z * splitBootSEn φ f X Y m 0 n ω : ℝ) : EReal) ≤
            sepVal f (region φ 0 P) (region φ 0 Q)}) ∧
      (StatFormal.Distances.tvDist P Q ≤ 0 →
          ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
            μ {ω | 0 < splitStat φ f X Y m 0 n ω - z * splitBootSEn φ f X Y m 0 n ω} ≤ ENNReal.ofReal (δ + η)) ∧
      (∀ n, ∀ ω, ((splitStat φ f X Y m 0 n ω - z * splitBootSEn φ f X Y m 0 n ω : ℝ) : EReal) ≤
          sepVal f (region φ 0 P) (region φ 0 Q) →
          0 < splitStat φ f X Y m 0 n ω - z * splitBootSEn φ f X Y m 0 n ω → 0 < StatFormal.Distances.tvDist P Q)

/-- `thm:split` at `α = 0` with the percentile bootstrap lower limit (the implementation), UNCONDITIONAL (also for
`σ₀² = 0`): coverage, asymptotic level `δ` and certification for `T̂_δ = splitBootPercn` (the bootstrap `δ`-quantile
of `T̂*`), `δ = Φ(Ioi z)`. -/
def split_zero_boot_percentile : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ' κ δ z : ℝ) (f : H)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → 𝒳) (m : ℕ → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ') →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X μ → iIndepFun Y μ →
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ → (∀ i, μ.map (X i) = P) → (∀ i, μ.map (Y i) = Q) →
    0 < κ → Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ) →
    (gaussianReal 0 1).real (Ioi z) = δ →
      (∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, 1 - δ - η ≤ μ.real {ω |
          ((splitBootPercn φ f X Y m 0 δ n ω : ℝ) : EReal) ≤ sepVal f (region φ 0 P) (region φ 0 Q)}) ∧
      (StatFormal.Distances.tvDist P Q ≤ 0 →
          ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
            μ {ω | 0 < splitBootPercn φ f X Y m 0 δ n ω} ≤ ENNReal.ofReal (δ + η)) ∧
      (∀ n, ∀ ω, ((splitBootPercn φ f X Y m 0 δ n ω : ℝ) : EReal) ≤ sepVal f (region φ 0 P) (region φ 0 Q) →
          0 < splitBootPercn φ f X Y m 0 δ n ω → 0 < StatFormal.Distances.tvDist P Q)

end Claims

end StatFormal.Wave30d
