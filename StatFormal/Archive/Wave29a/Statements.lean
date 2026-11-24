import StatFormal.Archive.Wave12b.Statements
import StatFormal.Archive.Wave10b.Statements
import StatFormal.Archive.Wave23b.Statements
import StatFormal.Archive.Wave24d.Statements
import StatFormal.Archive.Wave24f.Statements
import StatFormal.Archive.Wave26b.Statements
import Mathlib.Probability.Independence.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# FROZEN STATEMENTS — wave 29a: otfd C `lem:ref-potential-limit` (a), (b); `lem:conditional-weights` (almost sure
# version); `prop:metric-uniform-localization` (quadratic penalty); `cor:coordinate-obstruction-empirical`
# (stability, uniformity over the Lipschitz class, the fixed-strength statement)

Sources (current text of 2026-10-17, `otfd/papers/C_conditional/`):
* `lem:ref-potential-limit` (`supplement.tex:279-291`, proof `:293-347`), with the setting of
  `subsec:supp-coordinate` (`supplement.tex:236-258`: `ν_X`, `P_C` with compact supports `S = supp ν_X`,
  `D = supp P_C`, `Δ = max_{S×D} ‖r − c‖`, the Schrödinger system `eq:ref-cov-schroedinger`, normalised by
  `∫ φ dP_C = 0`) and the conjugate Kantorovich pairs (`:270-277`).
* `lem:conditional-weights` (`main.tex:438-452`), last sentence: "If locality holds almost surely and
  `v_n(x) log n → 0` almost surely, the convergence is almost sure."
* `prop:metric-uniform-localization` (`supplement.tex:728-763`, proof `:765-860`), the quadratic penalty, with the
  set-up of `subsec:supp-estimated-metric` (`:713-726`), the quadratic self-transport equation `eq:quad-self-pop` and
  weights `eq:self-quad-weights` (`:532-552`), main `eq:self-quad` (`main.tex:340-344`), `n_eff = 1/Σ_i w_i²`
  (`main.tex:353`).
* `cor:coordinate-obstruction-empirical` (`supplement.tex:501-515`, proof `:517-533`).
Imports the frozen `Wave12b` (`Euc`, `wEmp`, `locMass`, `vn`; through it `OTFD/Bands` `softmax`), `Wave10b`
(`IsCompactSupport`, `locLaw` = `P^ν_{K,ε,r}`), `Wave23b` (`empW`), `Wave24d` (`locLaw` as a test-function ratio),
`Wave24f` (`IsConjPair`) and `Wave26b` (`GLq`, `sSet`, `LocModel`) statements, not copied; Mathlib and Tau Ceti
(`wassersteinEDist`) otherwise.

Covered:
* `lem:ref-potential-limit` (the frozen Wave 24f `ref_potential_unique` is (c)):
  `refpot_bounds` (the equicontinuity step: `2Δ`-Lipschitz on `D` and `S`, `|φ| ≤ 2Δ diam D`,
  `|ψ| ≤ Δ² + 2Δ diam D`), `refpot_subseq` ((a): every null sequence of strengths has a uniformly convergent
  subsequence, and every uniform limit along a null sequence is a conjugate Kantorovich pair with `∫ φ₀ dP_C = 0`),
  `refpot_tendsto` ((b)), `refpot_tendsto_closure` ((b) with (c): on `S = closure Ω`, `Ω` bounded, open, connected, a
  normalised conjugate pair exists and the potentials converge to it uniformly).
* `lem:conditional-weights`, a.s. version: `cweights_as`.
* `prop:metric-uniform-localization`, quadratic penalty: `metricloc_quad_uniform` (main display, `inf n_eff/log n → ∞`
  over `𝒮_j × D_X`, `n η_n/log n → ∞`, and (i); (ii) is (i) for a constant sequence), `metricloc_quad_fixed`
  ((iii)), `metricloc_quad_selfpot` (the reduction step: existence and uniqueness of the population and of the
  empirical quadratic self-potentials for every metric). The entropic half is the frozen Wave 26b.
* `cor:coordinate-obstruction-empirical`: `coordobs_schr_unique` (uniqueness of the normalised continuous
  Schrödinger pair at fixed strength, the "by uniqueness of that solution" of the proof and the setting `:255-258`),
  `coordobs_schr_stability` (stability of the potentials under weak convergence of both marginals),
  `coordobs_kernel_lip` (the kernel-ratio step uniformly over the normalised `1`-Lipschitz tests; the frozen Wave 24d
  `coord_kernel_ratio` is the single-test version), `coordobs_fixed_eps` (the first assertion: for each fixed
  `ε_X > 0` and compact `B`, almost surely `sup_{x ∈ B} W₁(P̂^ν_{K,n,x}, P^ν_{K,ε_X,x}) → 0`).

Not covered (declared):
* `lem:ref-potential-limit`: existence of the Schrödinger potentials for each `ε_X` (the setting cites
  González-Sanz–Eckstein–Nutz; the claims quantify over a family of solutions); the weak limit of the entropic plans
  is not needed (see Proof notes). Non-vacuity (critic, 2026-10-17): for every probability `ν` and every `S`,
  `P_C = δ_b`, `D = {b}`, the pair `ψ = ‖· − b‖²`, `φ = 0` satisfies `RefPot ν δ_b S {b} ε` at every `ε` (checked in
  Lean); with `ν` uniform on a closed ball this instantiates every `refpot_*` and `coordobs_*` hypothesis (for
  `coordobs_fixed_eps`, `P̂_{C,n} = δ_b` a.s.). In general existence follows from the certified Wave 26a
  `schpot_exists` (bounded cost on the subtypes `S`, `D`) plus continuity of the `log`-integral formulas.
* `cor:coordinate-obstruction-empirical`: the slow schedule `ε_{X,n} ↓ 0` with `W₁(P̂^ν_{K,n,x}, P_{K,T_X(x)}) → 0` a.s.
  (staircase with the bias bound of the frozen Wave 10b `coord_limit`); existence of the empirical potentials.
* `prop:metric-uniform-localization`, quadratic: the examples sentence of (i) and the remark of (iii) (informal, as
  for the entropic half).

Encodings (to be checked by the critic):
* `ℝ^q = Euc q`. "`S = supp ν_X` compact" is the frozen `IsCompactSupport ν S` (`S` compact, `ν(Sᶜ) = 0`, every open
  set meeting `S` has positive mass), likewise `D`. The Schrödinger system (`RefPot`): `ψ` continuous on `S`, `φ`
  continuous on `D`, `e^{ψ(r)/ε} ∫ e^{(φ(c) − ‖r−c‖²)/ε} dP_C(c) = 1` for `r ∈ S`,
  `e^{φ(c)/ε} ∫ e^{(ψ(r) − ‖r−c‖²)/ε} dν_X(r) = 1` for `c ∈ D` (the exponential form of `eq:ref-cov-schroedinger`; the
  paper also asks the equations on all of `ℝ^q`, which is not used: required only on `S`, `D`, the claims are
  stronger), and `∫ φ dP_C = 0`. Families `ψ φ : ℝ → Euc q → ℝ` with the system at every `ε > 0`; "`ε_k ↓ 0`" is any
  positive sequence tending to `0` (monotonicity not needed); "as `ε_X ↓ 0`" is `𝓝[>] 0`; uniform convergence on `S`,
  `D` is `TendstoUniformlyOn`. Uniqueness of the normalised conjugate pair (hypothesis of (b)) is stated on `S × D`
  (values off `S`, `D` are irrelevant).
* `cweights_as`: the model of the frozen `cw_prob` (`κ c` carried by `B̄(0,R)` for every `c`, the `W₁`-continuity of
  `c ↦ κ c` at `x` in ε–δ form, measurable weights depending on the covariates only, nonnegative, summing to one for
  `n ≥ 1`), with an infinite i.i.d. sequence of pairs on `(Ω, P)` (`iIndepFun`, each pair of law `P_C ⊗ κ`,
  measurable coordinates) and sample size `n` using the first `n` pairs. "Locality a.s." is: for every `a > 0`,
  a.s. `Σ_i w_i 1{‖C_i − x‖ > a} → 0` (weaker than one null set for all `a`); "`v_n log n → 0` a.s." literally.
* `metricloc_quad_*`: the model `LocModel` and `𝒮_j` of Wave 26b. The empirical quadratic self-potential for the metric
  `Λ` (`IsEmpQuadPot`, `n ≥ 1`) is a function `H` on `ℝ^q` with `n⁻¹ Σ_l [H(x) + H(X_l) − ‖Λ(x − X_l)‖²]_+ = η` at every
  `x` (sample points and out-of-sample extension; unique, `metricloc_quad_selfpot`); the weights are
  `w^Q_{n,i}(x) = [H(x) + H(X_i) − ‖Λ(x − X_i)‖²]_+/(nη)` (`quadW`, = `eq:self-quad-weights` in whitened coordinates
  `C_i = ΛX_i`, query `Λx`; equal to the simplex projection of `eq:self-quad` by the frozen OTFD Wave 22b
  `selfloc_weight_quad`); the localized law `Σ_i w_i δ_{Z_i}` (`locEmpQ`). The population potential (`IsPopQuadPot`) is
  continuous on `D_X` with `∫ [H(x) + H(y) − ‖Λ(x − y)‖²]_+ dP_X(y) = η` on `D_X`; the smoothed law `locPopQ`
  (`(α(·|x)·P_X).bind κ`, `α = [·]_+/η`). Schedules as in Wave 26b (deterministic, positive, antitone, `→ 0`, chosen
  before the potentials and before `Λ̂_n`, `ŝ_n`); "`n η_n/log n → ∞`" as `∀ C, eventually C log n ≤ n η_n`.
* `coordobs_*`: weak convergence of laws tested on `BoundedContinuousFunction`s; the reference measures `ν_{m_n}` are
  any `ν_n(ω)`, probability measures carried by `S`, converging weakly to `ν_X` a.s. (random references allowed; no
  measurability in `ω` needed); the empirical covariate law `P̂_{C,n} = empW (1/n) (C_0, …, C_{n−1})`; the empirical
  potentials are quantified inside the a.s. event over every solution of the system for `(ν_n(ω), P̂_{C,n}(ω))` on
  `S`, `D` with `∫ φ_n dP̂_{C,n} = 0` (one null set for all choices); the weights are
  `w_{n,i}(x) = softmax_i((φ_n(C_i) − ‖x − C_i‖²)/ε_X)`, the empirical law `wEmp w Z`; the population law is the frozen
  Wave 10b `locLaw P_C D κ φ ε_X x`. `κ c` carried by `B̄(0, R)` for `c ∈ D`.

Junk audit: the Schrödinger and self-transport equations are in exponential/hinge form with right side `1` or `η > 0`,
so a non-integrable integrand (Bochner integral `0`) cannot satisfy them; `∫ φ dP_C = 0` concerns a function bounded
and continuous on the compact carrier `D` (integrable, so not a junk `0`); for empirical measures (finite sums of
Dirac masses) every function is integrable. `1/n`, `(nη)⁻¹` only for `n ≥ 1`, `η > 0`. `W₁ = wassersteinEDist 1` in
`ℝ≥0∞` (no `toReal`); `IsConjPair` uses `(W₂²).toReal` with `W₂ < ∞` (compact supports). `⨆` in `ℝ≥0∞`. `Measure.map`
only of measurable pairs (guarded by `Measurable` hypotheses). `Real.log n` with `n ≥ 1` eventually. No `sInf`, `sSup`
in the new definitions.

Proof notes (author of the draft, 2026-10-17): all 12 claims are proved in `Wave29a/Route{RefPot,CWeights,QuadSelf,
QuadCore,QuadFixed,QuadMain,CoordObs,CoordObsFixed}.lean` (`#print axioms`: propext, Classical.choice, Quot.sound), on
the new libraries `Foundations/RefSchrodinger/{Basic,Bounds,Duality}`, `Foundations/Localization/{QuadPot,QuadLaw}`,
`Foundations/Concentration/WeightedHoeffding`, the certified `Foundations/{Localization,SelfPotentials,Empirical}`,
the certified Wave 12b, 23b, 24f, 26b, 28c routes and the frozen Wave 22b staircase.
* `refpot_*`: bounds by comparing Schrödinger rows whose exponents differ by at most `2Δ‖·‖`; (a) by Arzelà–Ascoli on
  the subtypes `S`, `D` and a uniform Laplace principle (`e^{a_k/ε_k} ∫ e^{h_k/ε_k} dμ = 1 ⇒ a = min_D(−h)`, full
  support); optimality WITHOUT weak limits of plans: the entropic plan is a coupling and `p·g ≤ ε(1 − p)`
  (`u log u ≥ u − 1`) gives `W₂² ≤ ∫ψ_ε dν + ∫φ_ε dP → ∫ψ₀ dν + ∫φ₀ dP ≤ W₂²`; (b) by subsequences; (b)+(c) with the
  certified Wave 24f `ref_potential_unique`.
* `cweights_as`: the `A + B` split of Wave 12b; the law of the first `n` pairs disintegrates as
  `(⊗P_C) ⊗ (c ↦ ⊗_i κ(c_i))`; conditional Hoeffding gives `P(|A| ≥ t, v_n log n ≤ t²/(4L²)) ≤ 2/n²`; Borel–Cantelli,
  countably many tests, thresholds and radii, and the Kantorovich–Rubinstein net bound.
* `metricloc_quad_*`: reduction `H = G ∘ Λ` to the Euclidean potentials of `Λ#P_X` (Wave 28c, 23b); the Wave 26b
  argument with the quadratic localized law (joint `W₁`-continuity from stability with varying law, cost and `η`;
  Giry = Borel neighbourhoods, no measurability of suprema); bias `= ω(b)` once `‖H‖_∞ ≤ m_b/4` (Laplace bound);
  `max_i w_i ≤ (sη + 3‖Λ‖²d²)/(nsη)` and the staircase also force `n η_n/log n → ∞`.
* `coordobs_*`: uniqueness by the max argument (`ν`'s full support is not used); stability by Arzelà–Ascoli,
  Tietze extensions and uniqueness; the Lipschitz-uniform kernel ratio by compactness (bad sequences
  `(n_j, x_j, h_j)` have convergent subsequences); `coordobs_fixed_eps` by Varadarajan on `D × B̄(0,R)`, stability,
  the kernel ratio and Kantorovich–Rubinstein normalised at `0`.
* No tautology: no conclusion is among the hypotheses; families of potentials are quantified, and existence of the
  limit objects is proved where claimed (`refpot_tendsto_closure`, `metricloc_quad_selfpot`).
* Manuscript notes: (1) the optimality step of `lem:ref-potential-limit` needs no weak limit of the entropic plans;
  (2) the Schrödinger equations are needed only on `S` and `D`, not on `ℝ^q`; (3) fixed-strength uniqueness of the
  normalised pair has an elementary proof (no plan uniqueness, only `D = supp P_C`, `S` compact); (4) the a.s. part of
  `lem:conditional-weights` holds with locality a.s. for each radius separately. No manuscript defect found.

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace StatFormal.Wave29a

open StatFormal.Wave12b (Euc wEmp locMass vn)
open StatFormal.Wave10b (IsCompactSupport)
open StatFormal.Wave23b (empW)
open StatFormal.Wave24f.Claims (IsConjPair)
open StatFormal.Wave26b (GLq sSet LocModel)

/-! ### `lem:ref-potential-limit`: the reference-to-covariate Schrödinger system -/

section RefPot

/-- The normalised continuous Schrödinger pair of `eq:ref-cov-schroedinger` for `(ν_X, P_C)` at strength `ε`, on the
supports `S`, `D`: `ψ` continuous on `S`, `φ` continuous on `D`,
`e^{ψ(r)/ε} ∫ e^{(φ(c) − ‖r − c‖²)/ε} dP_C(c) = 1` (`r ∈ S`), `e^{φ(c)/ε} ∫ e^{(ψ(r) − ‖r − c‖²)/ε} dν_X(r) = 1`
(`c ∈ D`), and `∫ φ dP_C = 0`. -/
def RefPot {q : ℕ} (ν P : Measure (Euc q)) (S D : Set (Euc q)) (ε : ℝ) (ψ φ : Euc q → ℝ) : Prop :=
  ContinuousOn ψ S ∧ ContinuousOn φ D ∧
    (∀ r ∈ S, Real.exp (ψ r / ε) * ∫ c, Real.exp ((φ c - ‖r - c‖ ^ 2) / ε) ∂P = 1) ∧
    (∀ c ∈ D, Real.exp (φ c / ε) * ∫ r, Real.exp ((ψ r - ‖r - c‖ ^ 2) / ε) ∂ν = 1) ∧
    ∫ c, φ c ∂P = 0

end RefPot

/-! ### `prop:metric-uniform-localization`: the quadratic self-transport weights for a metric `Λ` -/

section Quad

/-- The quadratic self-transport weights `w^Q_{n,i}(x) = [H(x) + H(X_i) − ‖Λ(x − X_i)‖²]_+/(nη)`
(`eq:self-quad-weights` for the whitened covariates `C_i = ΛX_i` at the query `Λx`). -/
def quadW {q n : ℕ} (Λ : GLq q) (η : ℝ) (xs : Fin n → Euc q) (H : Euc q → ℝ) (x : Euc q) (i : Fin n) : ℝ :=
  max (H x + H (xs i) - ‖((Λ : GLq q) : Euc q →L[ℝ] Euc q) (x - xs i)‖ ^ 2) 0 / (n * η)

/-- The empirical symmetric quadratic self-potential (`eq:quad-self-pop` for `P̂_{X,n}` and the cost `‖Λ(x − y)‖²`),
with its out-of-sample extension: `n⁻¹ Σ_l [H(x) + H(X_l) − ‖Λ(x − X_l)‖²]_+ = η` for every `x`. -/
def IsEmpQuadPot {q n : ℕ} (Λ : GLq q) (η : ℝ) (xs : Fin n → Euc q) (H : Euc q → ℝ) : Prop :=
  ∀ x, (1 / (n : ℝ)) * ∑ l, max (H x + H (xs l) - ‖((Λ : GLq q) : Euc q →L[ℝ] Euc q) (x - xs l)‖ ^ 2) 0 = η

/-- The localized law `P̂^Q_{K,n,x}[Λ, η] = Σ_i w^Q_{n,i}(x) δ_{Z_i}`. -/
def locEmpQ {q K n : ℕ} (Λ : GLq q) (η : ℝ) (xs : Fin n → Euc q) (zs : Fin n → Euc K) (H : Euc q → ℝ)
    (x : Euc q) : Measure (Euc K) :=
  ∑ i, ENNReal.ofReal (quadW Λ η xs H x i) • Measure.dirac (zs i)

/-- The population symmetric quadratic self-potential on `D_X = supp P_X` for the metric `Λ`: continuous on `D_X` with
`∫ [H(x) + H(y) − ‖Λ(x − y)‖²]_+ dP_X(y) = η` for `x ∈ D_X`. -/
def IsPopQuadPot {q : ℕ} (PX : Measure (Euc q)) (Λ : GLq q) (η : ℝ) (H : Euc q → ℝ) : Prop :=
  ContinuousOn H PX.support ∧ ∀ x ∈ PX.support,
    ∫ y, max (H x + H y - ‖((Λ : GLq q) : Euc q →L[ℝ] Euc q) (x - y)‖ ^ 2) 0 ∂PX = η

/-- The population smoothed law `P^Q_{K,x}[Λ, η] = ∫ P_{K,y} α(y | x) dP_X(y)`,
`α(y | x) = [H(x) + H(y) − ‖Λ(x − y)‖²]_+/η`. -/
def locPopQ {q K : ℕ} (PX : Measure (Euc q)) (κ : Kernel (Euc q) (Euc K)) (Λ : GLq q) (η : ℝ) (H : Euc q → ℝ)
    (x : Euc q) : Measure (Euc K) :=
  (PX.withDensity fun y =>
    ENNReal.ofReal (max (H x + H y - ‖((Λ : GLq q) : Euc q →L[ℝ] Euc q) (x - y)‖ ^ 2) 0 / η)).bind κ

end Quad

namespace Claims

/-! #### `lem:ref-potential-limit` -/

/-- The equicontinuity step of the proof of `lem:ref-potential-limit`: with `‖r − c‖ ≤ Δ` on `S × D` and
`diam D ≤ d_D`, a normalised Schrödinger pair is `2Δ`-Lipschitz on `D` and on `S`, `|φ| ≤ 2Δ d_D` on `D` and
`|ψ| ≤ Δ² + 2Δ d_D` on `S`. -/
def refpot_bounds : Prop :=
  ∀ (q : ℕ) (S D : Set (Euc q)) (ν P : Measure (Euc q)) [IsProbabilityMeasure ν] [IsProbabilityMeasure P]
    (ε Δ dD : ℝ) (ψ φ : Euc q → ℝ),
    IsCompact S → IsCompact D → ν Sᶜ = 0 → P Dᶜ = 0 → 0 < ε →
    (∀ r ∈ S, ∀ c ∈ D, ‖r - c‖ ≤ Δ) → (∀ c ∈ D, ∀ c' ∈ D, ‖c - c'‖ ≤ dD) → RefPot ν P S D ε ψ φ →
      (∀ c ∈ D, ∀ c' ∈ D, |φ c - φ c'| ≤ 2 * Δ * ‖c - c'‖) ∧
      (∀ r ∈ S, ∀ r' ∈ S, |ψ r - ψ r'| ≤ 2 * Δ * ‖r - r'‖) ∧
      (∀ c ∈ D, |φ c| ≤ 2 * Δ * dD) ∧ ∀ r ∈ S, |ψ r| ≤ Δ ^ 2 + 2 * Δ * dD

/-- `lem:ref-potential-limit` (a): for compact supports `S = supp ν_X`, `D = supp P_C` and the normalised Schrödinger
pairs `(ψ_ε, φ_ε)`, every positive sequence `ε_k → 0` has a subsequence along which `ψ_{ε_k}` and `φ_{ε_k}` converge
uniformly on `S` and `D`; and every such uniform limit (along any positive null sequence) is a conjugate Kantorovich
pair with `∫ φ₀ dP_C = 0`. -/
def refpot_subseq : Prop :=
  ∀ (q : ℕ) (S D : Set (Euc q)) (ν P : Measure (Euc q)) [IsProbabilityMeasure ν] [IsProbabilityMeasure P]
    (ψ φ : ℝ → Euc q → ℝ),
    IsCompactSupport ν S → IsCompactSupport P D → (∀ ε, 0 < ε → RefPot ν P S D ε (ψ ε) (φ ε)) →
      ∀ εs : ℕ → ℝ, (∀ k, 0 < εs k) → Tendsto εs atTop (𝓝 0) →
        (∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ ψ₀ φ₀ : Euc q → ℝ,
          TendstoUniformlyOn (fun k => ψ (εs (σ k))) ψ₀ atTop S ∧
          TendstoUniformlyOn (fun k => φ (εs (σ k))) φ₀ atTop D) ∧
        ∀ ψ₀ φ₀ : Euc q → ℝ, TendstoUniformlyOn (fun k => ψ (εs k)) ψ₀ atTop S →
          TendstoUniformlyOn (fun k => φ (εs k)) φ₀ atTop D →
            IsConjPair ν P S D ψ₀ φ₀ ∧ ∫ c, φ₀ c ∂P = 0

/-- `lem:ref-potential-limit` (b): if the conjugate Kantorovich pair with `∫ φ₀ dP_C = 0` is unique (on `S × D`), then
`ψ_ε → ψ₀` uniformly on `S` and `φ_ε → φ₀` uniformly on `D` as `ε ↓ 0`. -/
def refpot_tendsto : Prop :=
  ∀ (q : ℕ) (S D : Set (Euc q)) (ν P : Measure (Euc q)) [IsProbabilityMeasure ν] [IsProbabilityMeasure P]
    (ψ φ : ℝ → Euc q → ℝ) (ψ₀ φ₀ : Euc q → ℝ),
    IsCompactSupport ν S → IsCompactSupport P D → (∀ ε, 0 < ε → RefPot ν P S D ε (ψ ε) (φ ε)) →
    (∀ ψ₁ φ₁ ψ₂ φ₂ : Euc q → ℝ, IsConjPair ν P S D ψ₁ φ₁ → IsConjPair ν P S D ψ₂ φ₂ →
      ∫ c, φ₁ c ∂P = 0 → ∫ c, φ₂ c ∂P = 0 → EqOn ψ₁ ψ₂ S ∧ EqOn φ₁ φ₂ D) →
    IsConjPair ν P S D ψ₀ φ₀ → ∫ c, φ₀ c ∂P = 0 →
      TendstoUniformlyOn ψ ψ₀ (𝓝[>] 0) S ∧ TendstoUniformlyOn φ φ₀ (𝓝[>] 0) D

/-- `lem:ref-potential-limit` (b) with (c): if `S = supp ν_X = closure Ω` with `Ω ⊆ ℝ^q` bounded, open and connected
(no density), a conjugate Kantorovich pair with `∫ φ₀ dP_C = 0` exists, and the normalised Schrödinger pairs converge
to it uniformly on `S` and `D` as `ε ↓ 0`. -/
def refpot_tendsto_closure : Prop :=
  ∀ (q : ℕ) (Ω D : Set (Euc q)) (ν P : Measure (Euc q)) [IsProbabilityMeasure ν] [IsProbabilityMeasure P]
    (ψ φ : ℝ → Euc q → ℝ),
    IsOpen Ω → IsConnected Ω → Bornology.IsBounded Ω →
    IsCompactSupport ν (closure Ω) → IsCompactSupport P D →
    (∀ ε, 0 < ε → RefPot ν P (closure Ω) D ε (ψ ε) (φ ε)) →
      (∃ ψ₀ φ₀ : Euc q → ℝ, IsConjPair ν P (closure Ω) D ψ₀ φ₀ ∧ ∫ c, φ₀ c ∂P = 0) ∧
      ∀ ψ₀ φ₀ : Euc q → ℝ, IsConjPair ν P (closure Ω) D ψ₀ φ₀ → ∫ c, φ₀ c ∂P = 0 →
        TendstoUniformlyOn ψ ψ₀ (𝓝[>] 0) (closure Ω) ∧ TendstoUniformlyOn φ φ₀ (𝓝[>] 0) D

/-! #### `lem:conditional-weights`, almost sure version -/

/-- `lem:conditional-weights`, last sentence: i.i.d. pairs `(C_i, Z_i) ∼ P_C ⊗ P_{K,·}` with `Z_i ∈ B̄(0,R)`, weights
`w_{n,i}(x) ≥ 0` summing to one and depending on the covariates only, `c ↦ P_{K,c}` `W₁`-continuous at `x`; if
locality holds almost surely and `v_n(x) log n → 0` almost surely, then `W₁(P̂_{K,n,x}, P_{K,x}) → 0` almost surely. -/
def cweights_as : Prop :=
  ∀ (X : Type) [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] (K : ℕ) (R : ℝ)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (PC : Measure X) [IsProbabilityMeasure PC] (κ : Kernel X (Euc K)) [IsMarkovKernel κ]
    (Cs : ℕ → Ω → X) (Zs : ℕ → Ω → Euc K) (W : ∀ n : ℕ, (Fin n → X) → Fin n → ℝ) (x : X),
    (∀ i, Measurable (Cs i)) → (∀ i, Measurable (Zs i)) → iIndepFun (fun i ω => (Cs i ω, Zs i ω)) P →
    (∀ i, P.map (fun ω => (Cs i ω, Zs i ω)) = PC ⊗ₘ κ) →
    (∀ c, κ c (Metric.closedBall 0 R)ᶜ = 0) →
    (∀ n, 0 < n → Measurable (W n) ∧ ∀ c, (∀ i, 0 ≤ W n c i) ∧ ∑ i, W n c i = 1) →
    (∀ η, 0 < η → ∃ a, 0 < a ∧ ∀ c, dist c x < a →
      TauCeti.wassersteinEDist 1 (κ c) (κ x) ≤ ENNReal.ofReal η) →
    (∀ a, 0 < a → ∀ᵐ ω ∂P,
      Tendsto (fun n => locMass (W n (fun i : Fin n => Cs i ω)) (fun i : Fin n => Cs i ω) x a) atTop (𝓝 0)) →
    (∀ᵐ ω ∂P, Tendsto (fun n => vn (W n (fun i : Fin n => Cs i ω)) * Real.log n) atTop (𝓝 0)) →
      ∀ᵐ ω ∂P, Tendsto (fun n => TauCeti.wassersteinEDist 1
        (wEmp (W n (fun i : Fin n => Cs i ω)) (fun i : Fin n => Zs i ω)) (κ x)) atTop (𝓝 0)

/-! #### `prop:metric-uniform-localization`, quadratic penalty -/

/-- The reduction step for the quadratic penalty (`lem:self-potentials` for the cost `‖Λ(x − y)‖²` on raw
covariates): for every `Λ ∈ GL_q` and `η > 0`, the population quadratic self-potential on a compact `D_X = supp P_X`
exists and is unique on `D_X`, and for every sample of size `n ≥ 1` the empirical one exists and is unique. -/
def metricloc_quad_selfpot : Prop :=
  ∀ (q : ℕ) (PX : Measure (Euc q)) [IsProbabilityMeasure PX] (Λ : GLq q) (η : ℝ), IsCompact PX.support → 0 < η →
    ((∃ H, IsPopQuadPot PX Λ η H) ∧
      ∀ H H', IsPopQuadPot PX Λ η H → IsPopQuadPot PX Λ η H' → EqOn H H' PX.support) ∧
    ∀ (n : ℕ) (xs : Fin n → Euc q), 0 < n → (∃ H, IsEmpQuadPot Λ η xs H) ∧
      ∀ H H', IsEmpQuadPot Λ η xs H → IsEmpQuadPot Λ η xs H' → H = H'

/-- `prop:metric-uniform-localization`, main display and (i), quadratic penalty: there is a deterministic schedule
`η_n ↓ 0` with `n η_n/log n → ∞` such that, for the (unique) empirical quadratic self-potentials, almost surely for
every `j`, `sup_{(Λ,s) ∈ 𝒮_j} sup_{x ∈ D_X} W₁(P̂^Q_{K,n,x}[Λ, s η_n], P_{K,x}) → 0` and `inf n_eff(x)/log n → ∞`
over `𝒮_j × D_X`; and (i): for any metrics `Λ̂_n` and scales `ŝ_n` that almost surely eventually stay in a compact
subset of `GL_q × (0,∞)`, or converge almost surely there, `sup_{x ∈ D_X} W₁(P̂^Q_{K,n,x}[Λ̂_n, ŝ_n η_n], P_{K,x}) → 0`
and `inf_x n_eff(x)/log n → ∞` almost surely. -/
def metricloc_quad_uniform : Prop :=
  ∀ (q K : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (PX : Measure (Euc q))
    [IsProbabilityMeasure PX] (κ : Kernel (Euc q) (Euc K)) [IsMarkovKernel κ] (R : ℝ)
    (Xs : ℕ → Ω → Euc q) (Zs : ℕ → Ω → Euc K),
    LocModel P PX κ R Xs Zs →
    ∃ ηX : ℕ → ℝ, (∀ n, 0 < ηX n) ∧ Antitone ηX ∧ Tendsto ηX atTop (𝓝 0) ∧
      (∀ C : ℝ, ∀ᶠ n : ℕ in atTop, C * Real.log (n : ℝ) ≤ n * ηX n) ∧
      ∀ Hn : (n : ℕ) → GLq q → ℝ → Ω → Euc q → ℝ,
        (∀ n Λ η ω, 0 < n → 0 < η → IsEmpQuadPot Λ η (fun i : Fin n => Xs i ω) (Hn n Λ η ω)) →
        (∀ᵐ ω ∂P, ∀ j : ℕ,
          Tendsto (fun n => ⨆ p ∈ sSet q j, ⨆ x ∈ PX.support,
            TauCeti.wassersteinEDist 1 (locEmpQ p.1 (p.2 * ηX n) (fun i : Fin n => Xs i ω) (fun i => Zs i ω)
              (Hn n p.1 (p.2 * ηX n) ω) x) (κ x)) atTop (𝓝 0) ∧
          ∀ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ p ∈ sSet q j, ∀ x ∈ PX.support,
            C * Real.log (n : ℝ) ≤
              (∑ i, quadW p.1 (p.2 * ηX n) (fun i : Fin n => Xs i ω) (Hn n p.1 (p.2 * ηX n) ω) x i ^ 2)⁻¹) ∧
        ∀ (Λh : ℕ → Ω → GLq q) (sh : ℕ → Ω → ℝ),
          ((∀ᵐ ω ∂P, ∃ Cs : Set (GLq q × ℝ), IsCompact Cs ∧ (∀ p ∈ Cs, 0 < p.2) ∧
              ∀ᶠ n in atTop, (Λh n ω, sh n ω) ∈ Cs) ∨
            (∀ᵐ ω ∂P, ∃ (Λ : GLq q) (s : ℝ), 0 < s ∧ Tendsto (fun n => (Λh n ω, sh n ω)) atTop (𝓝 (Λ, s)))) →
          ∀ᵐ ω ∂P, Tendsto (fun n => ⨆ x ∈ PX.support,
            TauCeti.wassersteinEDist 1 (locEmpQ (Λh n ω) (sh n ω * ηX n) (fun i : Fin n => Xs i ω)
              (fun i => Zs i ω) (Hn n (Λh n ω) (sh n ω * ηX n) ω) x) (κ x)) atTop (𝓝 0) ∧
            ∀ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ x ∈ PX.support,
              C * Real.log (n : ℝ) ≤ (∑ i, quadW (Λh n ω) (sh n ω * ηX n) (fun i : Fin n => Xs i ω)
                (Hn n (Λh n ω) (sh n ω * ηX n) ω) x i ^ 2)⁻¹

/-- `prop:metric-uniform-localization` (iii), quadratic penalty: for a fixed strength `η > 0` and
`(Λ̂_n, ŝ_n) → (Λ, s)` almost surely in `GL_q × (0,∞)` (random limit),
`sup_{x ∈ D_X} W₁(P̂^Q_{K,n,x}[Λ̂_n, ŝ_n η], P^Q_{K,x}[Λ, s η]) → 0` almost surely, `P^Q_{K,x}[Λ, η]` the population
smoothed law for the metric `Λ` (any population self-potentials). -/
def metricloc_quad_fixed : Prop :=
  ∀ (q K : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (PX : Measure (Euc q))
    [IsProbabilityMeasure PX] (κ : Kernel (Euc q) (Euc K)) [IsMarkovKernel κ] (R : ℝ)
    (Xs : ℕ → Ω → Euc q) (Zs : ℕ → Ω → Euc K),
    LocModel P PX κ R Xs Zs → ∀ η₀ : ℝ, 0 < η₀ →
      ∀ Hn : (n : ℕ) → GLq q → ℝ → Ω → Euc q → ℝ,
        (∀ n Λ η ω, 0 < n → 0 < η → IsEmpQuadPot Λ η (fun i : Fin n => Xs i ω) (Hn n Λ η ω)) →
      ∀ Hp : GLq q → ℝ → Euc q → ℝ, (∀ Λ η, 0 < η → IsPopQuadPot PX Λ η (Hp Λ η)) →
      ∀ (Λh : ℕ → Ω → GLq q) (sh : ℕ → Ω → ℝ) (Λ : Ω → GLq q) (s : Ω → ℝ),
        (∀ᵐ ω ∂P, 0 < s ω ∧ Tendsto (fun n => (Λh n ω, sh n ω)) atTop (𝓝 (Λ ω, s ω))) →
        ∀ᵐ ω ∂P, Tendsto (fun n => ⨆ x ∈ PX.support,
          TauCeti.wassersteinEDist 1 (locEmpQ (Λh n ω) (sh n ω * η₀) (fun i : Fin n => Xs i ω) (fun i => Zs i ω)
            (Hn n (Λh n ω) (sh n ω * η₀) ω) x) (locPopQ PX κ (Λ ω) (s ω * η₀) (Hp (Λ ω) (s ω * η₀)) x)) atTop (𝓝 0)

/-! #### `cor:coordinate-obstruction-empirical` -/

/-- Uniqueness of the normalised continuous Schrödinger pair at a fixed strength (setting of
`subsec:supp-coordinate`; used in the proof of `cor:coordinate-obstruction-empirical`): for compact supports
`S = supp ν_X`, `D = supp P_C` and `ε > 0`, two normalised pairs agree on `S` and on `D`. Not a restatement, but close
to a corollary of the certified Wave 26a `schpot_unique` (otfd G `thm:rates`: bounded measurable cost, equations at
every point), transferred to the subtypes `S`, `D` and normalised; proved here directly. -/
def coordobs_schr_unique : Prop :=
  ∀ (q : ℕ) (S D : Set (Euc q)) (ν P : Measure (Euc q)) [IsProbabilityMeasure ν] [IsProbabilityMeasure P]
    (ε : ℝ) (ψ φ ψ' φ' : Euc q → ℝ),
    IsCompactSupport ν S → IsCompactSupport P D → 0 < ε →
    RefPot ν P S D ε ψ φ → RefPot ν P S D ε ψ' φ' → EqOn ψ ψ' S ∧ EqOn φ φ' D

/-- Stability of the normalised Schrödinger pairs at a fixed strength (proof of
`cor:coordinate-obstruction-empirical`): if `ν_n → ν_X` and `P_n → P_C` weakly, all carried by the compact `S`, `D`,
with `S = supp ν_X`, `D = supp P_C`, then the normalised pairs of `(ν_n, P_n)` converge uniformly on `S` and `D` to
the normalised pair of `(ν_X, P_C)`. -/
def coordobs_schr_stability : Prop :=
  ∀ (q : ℕ) (S D : Set (Euc q)) (ν P : Measure (Euc q)) [IsProbabilityMeasure ν] [IsProbabilityMeasure P]
    (νn Pn : ℕ → Measure (Euc q)) (ε : ℝ) (ψ φ : Euc q → ℝ) (ψn φn : ℕ → Euc q → ℝ),
    IsCompactSupport ν S → IsCompactSupport P D → 0 < ε →
    (∀ n, IsProbabilityMeasure (νn n)) → (∀ n, IsProbabilityMeasure (Pn n)) →
    (∀ n, νn n Sᶜ = 0) → (∀ n, Pn n Dᶜ = 0) →
    (∀ f : BoundedContinuousFunction (Euc q) ℝ, Tendsto (fun n => ∫ r, f r ∂(νn n)) atTop (𝓝 (∫ r, f r ∂ν))) →
    (∀ f : BoundedContinuousFunction (Euc q) ℝ, Tendsto (fun n => ∫ c, f c ∂(Pn n)) atTop (𝓝 (∫ c, f c ∂P))) →
    (∀ n, RefPot (νn n) (Pn n) S D ε (ψn n) (φn n)) → RefPot ν P S D ε ψ φ →
      TendstoUniformlyOn ψn ψ atTop S ∧ TendstoUniformlyOn φn φ atTop D

/-- The kernel-ratio step of `cor:coordinate-obstruction-empirical`, uniformly over the test class (the hypotheses of
the frozen Wave 24d `coord_kernel_ratio`): `P̂^ν_{K,n,x}(h) → P^ν_{K,ε_X,x}(h)` uniformly over `x ∈ B` and over the
`1`-Lipschitz `h` with `h(0) = 0`. -/
def coordobs_kernel_lip : Prop :=
  ∀ (q K : ℕ) (D B : Set (Euc q)) (R : ℝ) (Pn : ℕ → Measure (Euc q × Euc K)) (P : Measure (Euc q × Euc K))
    (kn : ℕ → Euc q → Euc q → ℝ) (k : Euc q → Euc q → ℝ),
    (∀ n, IsProbabilityMeasure (Pn n)) → IsProbabilityMeasure P → IsCompact D → IsCompact B →
    (∀ n, Pn n (D ×ˢ Metric.closedBall 0 R)ᶜ = 0) → P (D ×ˢ Metric.closedBall 0 R)ᶜ = 0 →
    (∀ f : BoundedContinuousFunction (Euc q × Euc K) ℝ,
      Tendsto (fun n => ∫ p, f p ∂(Pn n)) atTop (𝓝 (∫ p, f p ∂P))) →
    Continuous (Function.uncurry k) → (∀ x ∈ B, ∀ c ∈ D, 0 < k x c) →
    (∀ n x, Measurable (kn n x)) → TendstoUniformlyOn (fun n => Function.uncurry (kn n)) (Function.uncurry k) atTop
      (B ×ˢ D) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x ∈ B, ∀ h : Euc K → ℝ, LipschitzWith 1 h → h 0 = 0 →
        |StatFormal.Wave24d.locLaw (kn n) (Pn n) x h - StatFormal.Wave24d.locLaw k P x h| ≤ ε

/-- `cor:coordinate-obstruction-empirical`, first assertion: i.i.d. pairs `(C_i, Z_i) ∼ P_C ⊗ P_{K,·}`,
`D = supp P_C` compact, `Z ∈ B̄(0,R)`, reference measures `ν_n` (possibly random) carried by `S` with `ν_n → ν_X`
weakly almost surely, `S = supp ν_X` compact. For each fixed `ε_X > 0` and compact `B ⊆ ℝ^q`, almost surely, for every
choice of the normalised empirical potentials of `(ν_n, P̂_{C,n})`,
`sup_{x ∈ B} W₁(P̂^ν_{K,n,x}, P^ν_{K,ε_X,x}) → 0`, with `P̂^ν_{K,n,x} = Σ_i w_{n,i}(x) δ_{Z_i}`,
`w_{n,i}(x) ∝ e^{(φ_n(C_i) − ‖x − C_i‖²)/ε_X}`. -/
def coordobs_fixed_eps : Prop :=
  ∀ (q K : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (PC ν : Measure (Euc q)) [IsProbabilityMeasure PC] [IsProbabilityMeasure ν] (κ : Kernel (Euc q) (Euc K))
    [IsMarkovKernel κ] (R ε : ℝ) (S D B : Set (Euc q)) (νs : ℕ → Ω → Measure (Euc q))
    (Cs : ℕ → Ω → Euc q) (Zs : ℕ → Ω → Euc K) (ψ φ : Euc q → ℝ),
    0 < ε → IsCompactSupport ν S → IsCompactSupport PC D → IsCompact B →
    (∀ c ∈ D, κ c (Metric.closedBall 0 R)ᶜ = 0) →
    (∀ i, Measurable (Cs i)) → (∀ i, Measurable (Zs i)) → iIndepFun (fun i ω => (Cs i ω, Zs i ω)) P →
    (∀ i, P.map (fun ω => (Cs i ω, Zs i ω)) = PC ⊗ₘ κ) →
    (∀ n ω, IsProbabilityMeasure (νs n ω) ∧ νs n ω Sᶜ = 0) →
    (∀ᵐ ω ∂P, ∀ f : BoundedContinuousFunction (Euc q) ℝ,
      Tendsto (fun n => ∫ r, f r ∂(νs n ω)) atTop (𝓝 (∫ r, f r ∂ν))) →
    RefPot ν PC S D ε ψ φ →
      ∀ᵐ ω ∂P, ∀ ψn φn : ℕ → Euc q → ℝ,
        (∀ n, 0 < n → RefPot (νs n ω) (empW (fun _ : Fin n => 1 / (n : ℝ)) (fun i => Cs i ω)) S D ε (ψn n) (φn n)) →
          Tendsto (fun n => ⨆ x ∈ B, TauCeti.wassersteinEDist 1
            (wEmp (StatFormal.OTFD.Bands.softmax fun i : Fin n => (φn n (Cs i ω) - ‖x - Cs i ω‖ ^ 2) / ε)
              (fun i : Fin n => Zs i ω))
            (StatFormal.Wave10b.locLaw PC D κ φ ε x)) atTop (𝓝 0)

end Claims

end StatFormal.Wave29a
