import StatFormal.Archive.OTFD.WaveL3.Statements
import StatFormal.Archive.Wave15b.Statements

/-!
# FROZEN STATEMENTS — otfd wave L4 (discharges): C `prop:conditional-potentials` and the unconditional wave-22b C
# band / coverage / transfer limits for INEXACT hard fits (`ζ_n ≥ 0`, `ζ_n → 0`, `eq:weighted-hard-gap`)

Sources (verbatim in `lean-formalisation/inventory/extracted/otfd-C_conditional.md`; current text of `otfd/papers/`):
* C `ass:conditional-oos` (`C_conditional/main.tex:653-661`), with `eq:weighted-hard-gap` (`supplement.tex:957-970`:
  `χ_{n,x} = max_{i∈I} {⟨u, Z_i⟩ − ½(‖Z_i‖² − f_i)}`, `φ⁰ = ‖u‖² − 2χ`, `∫φ⁰ dμ_{K,m_n} + Σ w_i f_i ≥ W₂² − ζ_{n,x}`)
  and `lem:weighted-duality` (`:972-990`, proof `:991-1031`: `0 ≤ ∫X^* + ∫X − 𝒞 ≤ ζ/2`, the "dual sandwich").
* C `prop:conditional-potentials` (`supplement.tex:1081-1085`, proof `:1087-1119`: the sandwich identifies the limit
  pair), used by `thm:conditional-band-limits` (`main.tex:666`, proof `supplement.tex:1121`),
  `cor:conditional-test-coverage` (`supplement.tex:2787`, proof `:1161`) and `prop:cond-transfer-consistency`
  (`main.tex:1017`, proof `supplement.tex:2116`).
* The frozen wave-L3 claims (`OTFD/WaveL3/Statements.lean`) `cond_potentials`, `cond_maps_ae_plans`,
  `cond_band_one_sided_plans`, `cond_test_coverage_plans`, `cond_transfer_consistency_plans`,
  `cond_transfer_consistency_prob_plans`, each assuming an EXACT hard fit (`HardFit`: `ζ_n = 0`, plans carried by
  `∂χ_n`); through them the frozen wave-22b originals `cond_maps_ae`, `cond_band_one_sided_potentials`,
  `cond_test_coverage_potentials`, `cond_transfer_consistency`, `cond_transfer_consistency_prob` (potential-convergence
  premise).
Imports the frozen `OTFD/WaveL3` (`Mom1`, `RefLaw`, `HardFit`; through it `OTFD/WaveL1` `IsCMMapAE`, `Euc`,
`OTFD/Wave22b`, `OTFD/Wave19a` `extTop`, `Wave17a` `hPop`, `Wave21b` `supE`, Tau Ceti `subdifferential`) and
`Wave15b` (`w2sq`, `phiHard`, `chiI`, `posRows`: the frozen objects of C `lem:weighted-duality`) statements, not copied.

Covered:
* `InexactFit` (plan form of the inexact fit: `ζ_n`-integrated `d_n`-subgradient concentration of the plans) and
  `WeightedFit` (C `ass:conditional-oos` with `eq:weighted-hard-gap`, verbatim discrete form).
* Bridges: `inexactFit_of_hardFit` (exact fits with grids in `U` are inexact fits with `ζ = 0`: generalisation);
  `weighted_gap_plan_form` (at fixed `n`, `eq:weighted-hard-gap` with gap `ζ` gives a coupling of the atomic laws and a
  Borel defect `d` with `∫ d dπ ≤ ζ/2` and the `d`-subgradient inequality everywhere: `lem:weighted-duality`
  integrated against an optimal plan); `inexactFit_of_weightedFit` (the sequence version, gaps `ζ_n/2`).
* C `prop:conditional-potentials` for inexact fits: `cond_potentials_inexact`, `cond_potentials_weighted`.
* Unconditional C limits for inexact fits (the wave-22b potential premise discharged): `cond_maps_ae_inexact`,
  `cond_band_one_sided_inexact`, `cond_test_coverage_inexact`, `cond_transfer_consistency_inexact`,
  `cond_transfer_consistency_prob_inexact`, and the same five `*_weighted` under `WeightedFit`.

Not covered (declared):
* Existence of the population map `Q` (McCann under a first moment) and of LP-optimal dual vectors (`ζ = 0`) remain
  premises / not claimed (as in wave L3; Mathlib has no LP duality theorem).
* The entropic and quadratic soft-fit sufficient conditions of `lem:weighted-duality` (`ζ ≤ r + ε log N`,
  `ζ ≤ r^Q + λ/2`) are the certified wave-15b claims; composing them with `WeightedFit` is left to the reader (the
  `_weighted` claims take the hard gap `ζ_n` as the paper's assumption does).
* `cor:conditional-uniform-x` (uniformity in the query) and the weak ("in probability") premises: not attempted.

Encodings (to be checked by the critic):
* `InexactFit μ P U α ν π χn g ζ d` = `HardFit` with the exact subgradient concentration replaced by: grids carried by
  `U` (`α_n(Uᶜ) = 0`, C: "the reference grids lie in `𝒰_K`"), `ζ_n ≥ 0`, `ζ_n → 0`, Borel `d_n` with
  `∫⁻ ofReal(d_n) dπ_n ≤ ofReal(ζ_n)` and, `π_n`-a.e., `χ_n(u) + ⟨z, v − u⟩ ≤ χ_n(v) + d_n(u, z)` for all `v ∈ U`. The
  canonical `d_n` is the Fenchel–Young defect `χ_n(u) − ⟨u, z⟩ + X_n(z)`, `X_n = (χ_n + ι_U)^*` (continuous), which is
  `≥ 0` on `U × ℝ^K`; with `π_n` correlation-optimal its integral is `∫χ_n dα_n + ∫X_n dν_n − 𝒞 ≤ ζ_n/2` (the
  upper half of the sandwich, via `X_n(Z_i) ≤ (‖Z_i‖² − f_i)/2`), so C's assumption gives `InexactFit` with `ζ_n/2`
  (`inexactFit_of_weightedFit`). `ofReal` clamps negative defects (harmless: `InexactFit` with `d_n` holds iff it
  holds with `max(d_n, 0)`, as a negative defect only strengthens the inequality). Conversely (not formalised)
  `InexactFit` gives `∫X_n^* dα_n + ∫X_n dν_n − 𝒞 ≤ ζ_n` (`d_n` dominates the Fenchel–Young defect a.e.,
  `X_n^* ≤ χ_n` on `U`), i.e. C's sandwich with `2ζ_n`. Not a generalisation of `HardFit` in one respect: grids
  must lie in `U` (`inexactFit_of_hardFit` needs it; C assumes it, and without it `lem:weighted-duality` fails:
  `weighted_duality_grid_needed`). The subgradient inequality is required only for `v ∈ U` (`HardFit`: all `v`).
* `WeightedFit μ P U α ν χn g ζ`: `α_n ⇀ μ`, `ν_n ⇀ P`, `ζ_n ≥ 0`, `ζ_n → 0`; at each `n` there are atomic data
  `(β, u_j)` (grid, `u_j ∈ U`, any weights `β_j ≥ 0` summing to one) and `(w, Z_i, f)` (weighted responses and fitted
  dual vector) with `α_n = Σ_j β_j δ_{u_j}`, `ν_n = Σ_i w_i δ_{Z_i}` (as measures), `χ_n = chiI (posRows w) Z f` (the
  Laguerre potential over `I = {w_i > 0}`, `I ≠ ∅`), the frozen wave-15b gap hypothesis
  `w2sq − ζ_n ≤ Σ_j β_j φ⁰(u_j) + Σ_i w_i f_i` (the hypothesis of `weighted_duality` verbatim), and
  `sup_U |g_n − χ_n| → 0` (C: "after a common normalization": one constant for both, any constant).
  Domain of the sup: C's text writes `sup_u` without fixing the domain; the sufficient conditions of
  `lem:weighted-duality` (wave-15b `weighted_entropic`, `weighted_quadratic`) bound `|g_n − χ_n|` on all of `ℝ^K`,
  and C's proof uses the margin only on compacts of `int 𝒰_K`; `U = 𝒰_K` is the weakest reading (generalisation).
  "Common normalization" is read as one shared constant (equivalently none, since it cancels in `g_n − χ_n`); the
  alternative reading "each normalised separately" (`sup_U |g_n − χ_n − a_n| → 0` for some constants `a_n`) is weaker
  and is NOT covered for the `g_n` half of `cond_potentials_*` (whose conclusion subtracts `c_n = inf_U χ_n` from
  `g_n`); the map claims are unaffected (subgradients ignore constants), but they still assume the shared-constant
  form. Nothing else in `WeightedFit` is stronger than C: weights `β_j` arbitrary (C: reference grid), `g_n` only
  convex on `int 𝒰_K` with any subgradient selection (C: convex differentiable, `∇g_n`), weak convergence (C: `W₁`).
* The `W₁` convergences of C are used only as weak convergence (for grids in the compact `U` they are equivalent; for
  the targets weak convergence plus `m₁(P) < ∞` is weaker than `W₁`); "almost surely" is per realisation
  (`∀ᵐ ω, WeightedFit …`, plans chosen per `ω`, no measurability needed). The fitted map is any subgradient selection
  `Q_n` of `g_n` (C: `∇g_n`, `g_n` differentiable).
* As in wave L3: `RefLaw μ U` = `μ_K ≪ Leb`, `𝒰_K` convex compact, `μ_K(𝒰_Kᶜ) = 0`, `int 𝒰_K ⊆ supp μ_K`; population
  facts `Mom1 P < ∞`, `Q` Borel, `Q#μ_K = P`, `Q` `μ_K`-a.e. cyclically monotone (`cond_potentials_*`) or `μ_K`-a.e.
  `∇χ`, `χ` convex on `int 𝒰_K` (discharge claims); normalisations by `IsGLB`.

Critic notes:
* Mechanical diff: each `*_inexact` claim differs from its frozen wave-L3 counterpart (`cond_potentials`,
  `*_plans`) only by `HardFit μ P U α ν π χn g` ↦ `InexactFit μ P U α ν π χn g ζ d` and the binders `ζ`, `d` (per `ω`
  in the transfer claims); each `*_weighted` claim from its `*_inexact` one by deleting the binders `π`, `d` and
  `InexactFit μ P U α ν π χn g ζ d` ↦ `WeightedFit μ P U α ν χn g ζ`. All other objects are the imported frozen ones;
  so each claim is the wave-22b original with its potential-convergence premise replaced by `RefLaw`, `m₁(P) < ∞`,
  `Q` Borel, `Q#μ_K = P` and the inexact fit.
* Proofs (routes `OTFD/WaveL4/Route{Approx,Inexact,Claims,Bridge,Weighted}.lean`; axioms: propext,
  Classical.choice, Quot.sound): Markov's inequality makes the pairs that are not `δ`-subgradient pairs of `χ_n` of
  `π_n`-mass `≤ ζ_n/δ → 0`; weak limits of the plans then have cyclically monotone support (a cycle violation `s > 0`
  persists on neighbourhoods, which eventually contain `δ`-pairs with `δ = s/(2(m+1))`), so by the wave-L3 uniqueness
  of cyclically monotone couplings with a bounded Lipschitz-null source the plans converge to `(Id × Q)#μ_K`; the
  library's potential stability (`Foundations/Potentials` `LocalBound`, `Stability`) is re-proved for approximate
  potentials (`RouteApprox`: every use of a support point is replaced by a `δ`-pair in a set of mass `> π V / 2`);
  normalisation, transfer to `g_n` and the wave-22b theorems as in wave L3. This replaces C's conjugate /
  epi-convergence route (the sandwich enters only through `weighted_gap_plan_form`).
* No tautology: `InexactFit` and `WeightedFit` contain no convergence of potentials or maps (only of the marginals,
  the gaps and the uniform closeness `g_n − χ_n → 0`); in `weighted_gap_plan_form` the defect is constrained both by
  the inequality everywhere and by `∫ d dπ ≤ ζ/2` with prescribed marginals.
* No junk: `w2sq` is an `sInf` of a nonempty set bounded below (plans exist, costs `≥ 0`); `chiI` an `iSup` over the
  nonempty `posRows w`; defects enter through `ENNReal.ofReal` (clamping only weakens the integral premise for
  negative defects, which strengthen the inequality); `ζ_n/2` is real division by `2`; no `Measure.map` of a
  non-measurable map, no `toReal`. Nonvacuity: `InexactFit` is satisfied by exact fits with grids in `U`
  (`inexactFit_of_hardFit`); `WeightedFit` with `ζ_n = 0` by LP-optimal duals (satisfiable, not claimed).
  Genuinely inexact witnesses (argument, not formalised): `InexactFit` is monotone in `ζ` (any `ζ'_n ≥ ζ_n`,
  `ζ'_n → 0`), so `ζ_n > 0` is never excluded; and plans off the subdifferential graph occur: from an exact fit with
  atomic `ν_n`, take `π'_n = (1 − t_n)π_n + t_n α_n ⊗ ν_n` (same marginals), `d_n` the Fenchel–Young defect, bounded
  by some `C_n` on `U × supp ν_n`, and `t_n = 1/((n + 1)(1 + C_n))`, `ζ_n = t_n C_n + 1/(n + 1) > 0`. For
  `WeightedFit`, any dual vector `f` has gap `ζ = W₂² − (∫φ⁰ dα + Σ w_i f_i) ≥ 0` (weak duality), and the semi-dual
  value is `2`-Lipschitz in `‖f‖_∞`, so perturbed LP-optimal duals `f*_n + e_i/n` give gaps `0 ≤ ζ_n ≤ 2/n`.
* Critic (2026-10-15): ACCEPT-WITH-NOTE. Mechanical token diff: each `*_inexact` claim differs from its frozen
  wave-L3 counterpart only by the binders `ζ`, `d` and `HardFit … ↦ InexactFit … ζ d`; each `*_weighted` from its
  `*_inexact` only by deleting `π`, `d` and `InexactFit … ↦ WeightedFit …`. `WeightedFit` is C's assumption with the
  frozen wave-15b objects verbatim (`w2sq` = `sInf` over nonempty plan costs `≥ 0`; `chiI` over the nonempty
  `posRows w`); the note on "common normalization" above is the only reading choice not weaker than C. Defects enter
  through a lower integral of `ofReal`, so no Bochner junk.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/
set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.OTFD.WaveL4

open StatFormal.OTFD.WaveL1 (IsCMMapAE Euc)
open StatFormal.OTFD.WaveL3 (Mom1 RefLaw HardFit)
open StatFormal.OTFD.Wave19a (extTop)
open StatFormal.Wave15b (w2sq phiHard chiI posRows)

/-! ### Definitions -/

/-- C `ass:conditional-oos` at one query with an **inexact hard fit**, in the plan form of `eq:weighted-hard-gap`
(`lem:weighted-duality`): grids `α_n ⇀ μ` carried by `U` ("the reference grids lie in `𝒰_K`"), weighted targets
`ν_n ⇀ P`, plans `π_n ∈ Π(α_n, ν_n)`, finite convex (Laguerre) potentials `χ_n`, gaps `ζ_n ≥ 0` with `ζ_n → 0`, and
Borel defects `d_n` with `∫ d_n dπ_n ≤ ζ_n` such that for `π_n`-a.e. `(u, z)` the point `z` is a `d_n(u, z)`-subgradient
of `χ_n` relative to `U` (`χ_n(u) + ⟨z, v − u⟩ ≤ χ_n(v) + d_n(u, z)` for all `v ∈ U`); fitted potentials `g_n` with
`sup_U |g_n − χ_n| → 0`. -/
def InexactFit {K : ℕ} (μ P : ProbabilityMeasure (Euc K)) (U : Set (Euc K)) (α ν : ℕ → ProbabilityMeasure (Euc K))
    (π : ℕ → ProbabilityMeasure (Euc K × Euc K)) (χn g : ℕ → Euc K → ℝ) (ζ : ℕ → ℝ)
    (d : ℕ → Euc K × Euc K → ℝ) : Prop :=
  Tendsto α atTop (𝓝 μ) ∧ Tendsto ν atTop (𝓝 P) ∧
    (∀ n, (π n : Measure (Euc K × Euc K)).fst = α n) ∧ (∀ n, (π n : Measure (Euc K × Euc K)).snd = ν n) ∧
    (∀ n, (α n : Measure (Euc K)) Uᶜ = 0) ∧ (∀ n, ConvexOn ℝ univ (χn n)) ∧
    (∀ n, 0 ≤ ζ n) ∧ Tendsto ζ atTop (𝓝 0) ∧ (∀ n, Measurable (d n)) ∧
    (∀ n, ∫⁻ z, ENNReal.ofReal (d n z) ∂(π n : Measure (Euc K × Euc K)) ≤ ENNReal.ofReal (ζ n)) ∧
    (∀ n, ∀ᵐ z ∂(π n : Measure (Euc K × Euc K)), ∀ x ∈ U, χn n z.1 + ⟪z.2, x - z.1⟫ ≤ χn n x + d n z) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ u ∈ U, |g n u - χn n u| ≤ ε)

/-- C `ass:conditional-oos` at one query, **verbatim discrete form** with the hard semi-dual gap
`eq:weighted-hard-gap`: grids `α_n ⇀ μ`, weighted targets `ν_n ⇀ P`, gaps `ζ_n ≥ 0`, `ζ_n → 0`; at each `n` the
grid is atomic, `α_n = Σ_j β_j δ_{u_j}` with `u_j ∈ U`, the target is `ν_n = Σ_i w_i δ_{Z_i}`, `χ_n` is the Laguerre
potential `max_{i : w_i > 0} {⟨u, Z_i⟩ − ½(‖Z_i‖² − f_i)}` of the fitted dual vector `f`, and
`∫φ⁰_n dα_n + Σ_i w_i f_i ≥ W₂²(α_n, ν_n) − ζ_n` (`φ⁰_n = ‖·‖² − 2χ_n`); fitted potentials `g_n` with
`sup_U |g_n − χ_n| → 0`. -/
def WeightedFit {K : ℕ} (μ P : ProbabilityMeasure (Euc K)) (U : Set (Euc K)) (α ν : ℕ → ProbabilityMeasure (Euc K))
    (χn g : ℕ → Euc K → ℝ) (ζ : ℕ → ℝ) : Prop :=
  Tendsto α atTop (𝓝 μ) ∧ Tendsto ν atTop (𝓝 P) ∧ (∀ n, 0 ≤ ζ n) ∧ Tendsto ζ atTop (𝓝 0) ∧
    (∀ n, ∃ (m N : ℕ) (β : Fin m → ℝ) (ug : Fin m → Euc K) (w : Fin N → ℝ) (Z : Fin N → Euc K) (f : Fin N → ℝ),
      (∀ j, 0 ≤ β j) ∧ ∑ j, β j = 1 ∧ (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ (∀ j, ug j ∈ U) ∧
      (α n : Measure (Euc K)) = ∑ j, ENNReal.ofReal (β j) • Measure.dirac (ug j) ∧
      (ν n : Measure (Euc K)) = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (Z i) ∧
      χn n = chiI (posRows w) Z f ∧
      w2sq β ug w Z - ζ n ≤ ∑ j, β j * phiHard (posRows w) Z f (ug j) + ∑ i, w i * f i) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ u ∈ U, |g n u - χn n u| ≤ ε)

namespace Claims

/-! #### Inexact fits generalise exact fits -/

/-- An exact hard fit (`HardFit`, wave L3) whose grids lie in `U` is an inexact fit with `ζ_n = 0`, `d_n = 0`. -/
def inexactFit_of_hardFit : Prop :=
  ∀ (K : ℕ) (μ P : ProbabilityMeasure (Euc K)) (U : Set (Euc K)) (α ν : ℕ → ProbabilityMeasure (Euc K))
    (π : ℕ → ProbabilityMeasure (Euc K × Euc K)) (χn g : ℕ → Euc K → ℝ),
    HardFit μ P U α ν π χn g → (∀ n, (α n : Measure (Euc K)) Uᶜ = 0) →
      InexactFit μ P U α ν π χn g (fun _ => 0) (fun _ _ => 0)

/-- **The paper's gap gives the plan form** (C `eq:weighted-hard-gap` ⇒ the per-`n` conditions of `InexactFit`, the
sandwich of `lem:weighted-duality` integrated against an optimal plan): for a grid `μ_{K,m} = Σ_j β_j δ_{u_j}` in the
compact `U` and a weighted target `P̂ = Σ_i w_i δ_{Z_i}`, if the hard cost transform `φ⁰ = ‖·‖² − 2χ` of the Laguerre
potential `χ = max_{i : w_i > 0} ℓ_i` has semi-dual gap `ζ` (`∫φ⁰ dμ_{K,m} + Σ_i w_i f_i ≥ W₂²(μ_{K,m}, P̂) − ζ`), then
`χ` is finite convex and some coupling `π ∈ Π(μ_{K,m}, P̂)` and Borel defect `d` satisfy `∫ d dπ ≤ ζ/2` and
`χ(u) + ⟨z, v − u⟩ ≤ χ(v) + d(u, z)` for every `(u, z)` and `v ∈ U`. -/
def weighted_gap_plan_form : Prop :=
  ∀ (K m n : ℕ) (β : Fin m → ℝ) (ug : Fin m → Euc K) (w : Fin n → ℝ) (Z : Fin n → Euc K) (f : Fin n → ℝ)
    (U : Set (Euc K)) (ζ : ℝ),
    (∀ j, 0 ≤ β j) → ∑ j, β j = 1 → (∀ i, 0 ≤ w i) → ∑ i, w i = 1 → IsCompact U → (∀ j, ug j ∈ U) →
    w2sq β ug w Z - ζ ≤ ∑ j, β j * phiHard (posRows w) Z f (ug j) + ∑ i, w i * f i →
      ConvexOn ℝ univ (chiI (posRows w) Z f) ∧
      ∃ (π : ProbabilityMeasure (Euc K × Euc K)) (d : Euc K × Euc K → ℝ),
        (π : Measure (Euc K × Euc K)).fst = ∑ j, ENNReal.ofReal (β j) • Measure.dirac (ug j) ∧
        (π : Measure (Euc K × Euc K)).snd = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (Z i) ∧
        Measurable d ∧ ∫⁻ z, ENNReal.ofReal (d z) ∂(π : Measure (Euc K × Euc K)) ≤ ENNReal.ofReal (ζ / 2) ∧
        ∀ (z : Euc K × Euc K), ∀ x ∈ U, chiI (posRows w) Z f z.1 + ⟪z.2, x - z.1⟫ ≤ chiI (posRows w) Z f x + d z

/-- The verbatim discrete assumption gives the plan form, with gaps `ζ_n / 2` (for compact `U`). -/
def inexactFit_of_weightedFit : Prop :=
  ∀ (K : ℕ) (μ P : ProbabilityMeasure (Euc K)) (U : Set (Euc K)) (α ν : ℕ → ProbabilityMeasure (Euc K))
    (χn g : ℕ → Euc K → ℝ) (ζ : ℕ → ℝ),
    IsCompact U → WeightedFit μ P U α ν χn g ζ →
      ∃ (π : ℕ → ProbabilityMeasure (Euc K × Euc K)) (d : ℕ → Euc K × Euc K → ℝ),
        InexactFit μ P U α ν π χn g (fun n => ζ n / 2) d

/-! #### C `prop:conditional-potentials` (inexact hard fits) -/

/-- C `prop:conditional-potentials` for inexact hard fits: `cond_potentials` (wave L3) with `HardFit` replaced by
`InexactFit` (`ζ_n → 0`). -/
def cond_potentials_inexact : Prop :=
  ∀ (K : ℕ) (μ P : ProbabilityMeasure (Euc K)) (U : Set (Euc K)) (Q : Euc K → Euc K)
    (α ν : ℕ → ProbabilityMeasure (Euc K)) (π : ℕ → ProbabilityMeasure (Euc K × Euc K)) (χn g : ℕ → Euc K → ℝ)
    (ζ : ℕ → ℝ) (d : ℕ → Euc K × Euc K → ℝ),
    RefLaw (μ : Measure (Euc K)) U → Mom1 (P : Measure (Euc K)) ≠ ∞ →
    Measurable Q → (μ : Measure (Euc K)).map Q = P → IsCMMapAE (μ : Measure (Euc K)) Q →
    InexactFit μ P U α ν π χn g ζ d →
      (∃ χ : Euc K → ℝ, ConvexOn ℝ (interior U) χ ∧ Q =ᵐ[(μ : Measure (Euc K))] gradient χ ∧
          IsGLB (χ '' interior U) 0) ∧
        ∀ χ : Euc K → ℝ, ConvexOn ℝ (interior U) χ → Q =ᵐ[(μ : Measure (Euc K))] gradient χ →
          IsGLB (χ '' interior U) 0 → ∀ c : ℕ → ℝ, (∀ n, IsGLB (χn n '' U) (c n)) →
            ∀ S ⊆ interior U, IsCompact S →
              TendstoUniformlyOn (fun n u => χn n u - c n) χ atTop S ∧
                TendstoUniformlyOn (fun n u => g n u - c n) χ atTop S

/-! #### Unconditional C limits for inexact fits (wave 22b with the potential premise discharged) -/

/-- `cond_maps_ae` from an inexact hard fit (`cond_maps_ae_plans` with `HardFit` ↦ `InexactFit`). -/
def cond_maps_ae_inexact : Prop :=
  ∀ (K : ℕ) (μ P : ProbabilityMeasure (Euc K)) (U : Set (Euc K)) (χ : Euc K → ℝ) (Q : Euc K → Euc K)
    (Qn : ℕ → Euc K → Euc K) (α ν : ℕ → ProbabilityMeasure (Euc K)) (π : ℕ → ProbabilityMeasure (Euc K × Euc K))
    (χn g : ℕ → Euc K → ℝ) (ζ : ℕ → ℝ) (d : ℕ → Euc K × Euc K → ℝ),
    RefLaw (μ : Measure (Euc K)) U → Mom1 (P : Measure (Euc K)) ≠ ∞ →
    Measurable Q → (μ : Measure (Euc K)).map Q = P →
    ConvexOn ℝ (interior U) χ → Q =ᵐ[(μ : Measure (Euc K))] gradient χ →
    InexactFit μ P U α ν π χn g ζ d → (∀ n, ConvexOn ℝ (interior U) (g n)) →
    (∀ n, ∀ u ∈ interior U, Qn n u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n)) u) →
      ∀ᵐ u ∂(μ : Measure (Euc K)), u ∈ interior U ∧ DifferentiableAt ℝ χ u ∧ Tendsto (fun n => Qn n u) atTop (𝓝 (Q u))

/-- `cond_band_one_sided_potentials` from an inexact hard fit. -/
def cond_band_one_sided_inexact : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ P : ProbabilityMeasure (Euc K)) (U A : Set (Euc K)) (χ : Euc K → ℝ) (Q : Euc K → Euc K)
    (Qn : ℕ → Euc K → Euc K) (α ν : ℕ → ProbabilityMeasure (Euc K)) (π : ℕ → ProbabilityMeasure (Euc K × Euc K))
    (χn g : ℕ → Euc K → ℝ) (ζ : ℕ → ℝ) (d : ℕ → Euc K × Euc K → ℝ) (e : 𝒯 → Euc K) (R EK : ℝ),
    RefLaw (μ : Measure (Euc K)) U → Mom1 (P : Measure (Euc K)) ≠ ∞ →
    Measurable Q → (μ : Measure (Euc K)).map Q = P →
    ConvexOn ℝ (interior U) χ → Q =ᵐ[(μ : Measure (Euc K))] gradient χ →
    InexactFit μ P U α ν π χn g ζ d → (∀ n, ConvexOn ℝ (interior U) (g n)) →
    (∀ n, ∀ u ∈ interior U, Qn n u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n)) u) →
    MeasurableSet A → (∀ᵐ u ∂(μ : Measure (Euc K)).restrict A, ‖Q u‖ ≤ R) → (∀ t, ‖e t‖ ≤ EK) →
      ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t,
        StatFormal.Wave17a.hPop (μ : Measure (Euc K)) A Q (e t) ≤ StatFormal.Wave21b.supE A (Qn n) (e t) + η ∧
          StatFormal.Wave17a.hPop (μ : Measure (Euc K)) A Q (-e t) ≤ StatFormal.Wave21b.supE A (Qn n) (-e t) + η

/-- `cond_test_coverage_potentials` from an inexact hard fit. -/
def cond_test_coverage_inexact : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ P : ProbabilityMeasure (Euc K)) (U A : Set (Euc K)) (χ : Euc K → ℝ) (Q : Euc K → Euc K)
    (Qn : ℕ → Euc K → Euc K) (α ν : ℕ → ProbabilityMeasure (Euc K)) (π : ℕ → ProbabilityMeasure (Euc K × Euc K))
    (χn g : ℕ → Euc K → ℝ) (ζ : ℕ → ℝ) (d : ℕ → Euc K × Euc K → ℝ) (m : 𝒯 → ℝ) (e : 𝒯 → Euc K)
    (Ue Le : ℕ → 𝒯 → EReal) (R EK p κ : ℝ),
    RefLaw (μ : Measure (Euc K)) U → Mom1 (P : Measure (Euc K)) ≠ ∞ →
    Measurable Q → (μ : Measure (Euc K)).map Q = P →
    ConvexOn ℝ (interior U) χ → Q =ᵐ[(μ : Measure (Euc K))] gradient χ →
    InexactFit μ P U α ν π χn g ζ d → (∀ n, ConvexOn ℝ (interior U) (g n)) →
    (∀ n, ∀ u ∈ interior U, Qn n u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n)) u) →
    MeasurableSet A → (∀ᵐ u ∂(μ : Measure (Euc K)).restrict A, ‖Q u‖ ≤ R) → (∀ t, ‖e t‖ ≤ EK) →
    ENNReal.ofReal p ≤ (μ : Measure (Euc K)) A → 0 < κ →
    (∀ n t, (m t : EReal) + StatFormal.Wave21b.supE A (Qn n) (e t) ≤ Ue n t ∧
      Le n t ≤ (m t : EReal) - StatFormal.Wave21b.supE A (Qn n) (-e t)) →
      ∀ᶠ n in atTop, ∃ E : Set (Euc K), MeasurableSet E ∧
        E ⊆ {z | ∀ t, Le n t - κ ≤ ((m t + ⟪e t, z⟫ : ℝ) : EReal) ∧ ((m t + ⟪e t, z⟫ : ℝ) : EReal) ≤ Ue n t + κ} ∧
        ENNReal.ofReal p ≤ (μ : Measure (Euc K)).map Q E

/-- `cond_transfer_consistency` from an inexact hard fit at `x'` (a.s. along the sample, with random `ζ_n`). -/
def cond_transfer_consistency_inexact : Prop :=
  ∀ (K : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (μ P' : ProbabilityMeasure (Euc K)) (U DF : Set (Euc K))
    (Z : Ω → Euc K) (F : Euc K → Euc K) (Fh : ℕ → Ω → Euc K → Euc K) (χ' : Euc K → ℝ) (Q' : Euc K → Euc K)
    (Qh : ℕ → Ω → Euc K → Euc K) (α ν : ℕ → Ω → ProbabilityMeasure (Euc K))
    (π : ℕ → Ω → ProbabilityMeasure (Euc K × Euc K)) (χn g : ℕ → Ω → Euc K → ℝ) (ζ : ℕ → Ω → ℝ)
    (d : ℕ → Ω → Euc K × Euc K → ℝ),
    RefLaw (μ : Measure (Euc K)) U → Measurable Z → Measurable F → P.map (fun ω => F (Z ω)) = μ →
    (∀ᵐ ω ∂P, Z ω ∈ DF) → (∀ᵐ ω ∂P, ∀ z ∈ DF, Tendsto (fun n => Fh n ω z) atTop (𝓝 (F z))) →
    ConvexOn ℝ (interior U) χ' → Q' =ᵐ[(μ : Measure (Euc K))] gradient χ' →
    Mom1 (P' : Measure (Euc K)) ≠ ∞ → Measurable Q' → (μ : Measure (Euc K)).map Q' = P' →
    (∀ᵐ ω ∂P, InexactFit μ P' U (fun n => α n ω) (fun n => ν n ω) (fun n => π n ω) (fun n => χn n ω)
        (fun n => g n ω) (fun n => ζ n ω) (fun n => d n ω) ∧
      ∀ n, ConvexOn ℝ (interior U) (g n ω)) →
    (∀ n ω, ∀ u ∈ interior U, Qh n ω u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n ω)) u) →
      ∀ᵐ ω ∂P, F (Z ω) ∈ interior U ∧ DifferentiableAt ℝ χ' (F (Z ω)) ∧ Q' (F (Z ω)) = gradient χ' (F (Z ω)) ∧
        Tendsto (fun n => Qh n ω (Fh n ω (Z ω))) atTop (𝓝 (Q' (F (Z ω))))

/-- `cond_transfer_consistency_prob` from an inexact hard fit ("… hence in probability"). -/
def cond_transfer_consistency_prob_inexact : Prop :=
  ∀ (K : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] (μ P' : ProbabilityMeasure (Euc K))
    (U DF : Set (Euc K)) (Z : Ω → Euc K) (F : Euc K → Euc K) (Fh : ℕ → Ω → Euc K → Euc K) (χ' : Euc K → ℝ)
    (Q' : Euc K → Euc K) (Qh : ℕ → Ω → Euc K → Euc K) (α ν : ℕ → Ω → ProbabilityMeasure (Euc K))
    (π : ℕ → Ω → ProbabilityMeasure (Euc K × Euc K)) (χn g : ℕ → Ω → Euc K → ℝ) (ζ : ℕ → Ω → ℝ)
    (d : ℕ → Ω → Euc K × Euc K → ℝ),
    RefLaw (μ : Measure (Euc K)) U → Measurable Z → Measurable F → P.map (fun ω => F (Z ω)) = μ →
    (∀ᵐ ω ∂P, Z ω ∈ DF) → (∀ᵐ ω ∂P, ∀ z ∈ DF, Tendsto (fun n => Fh n ω z) atTop (𝓝 (F z))) →
    ConvexOn ℝ (interior U) χ' → Q' =ᵐ[(μ : Measure (Euc K))] gradient χ' →
    Mom1 (P' : Measure (Euc K)) ≠ ∞ → Measurable Q' → (μ : Measure (Euc K)).map Q' = P' →
    (∀ᵐ ω ∂P, InexactFit μ P' U (fun n => α n ω) (fun n => ν n ω) (fun n => π n ω) (fun n => χn n ω)
        (fun n => g n ω) (fun n => ζ n ω) (fun n => d n ω) ∧
      ∀ n, ConvexOn ℝ (interior U) (g n ω)) →
    (∀ n ω, ∀ u ∈ interior U, Qh n ω u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n ω)) u) →
    (∀ n, AEStronglyMeasurable (fun ω => Qh n ω (Fh n ω (Z ω))) P) →
      TendstoInMeasure P (fun n ω => Qh n ω (Fh n ω (Z ω))) atTop (fun ω => Q' (F (Z ω)))

/-! #### The same limits under the verbatim discrete assumption -/

/-- `cond_potentials_inexact` for the verbatim discrete assumption (`WeightedFit`, C `ass:conditional-oos` with
`eq:weighted-hard-gap`; `U` compact by `RefLaw`). -/
def cond_potentials_weighted : Prop :=
  ∀ (K : ℕ) (μ P : ProbabilityMeasure (Euc K)) (U : Set (Euc K)) (Q : Euc K → Euc K)
    (α ν : ℕ → ProbabilityMeasure (Euc K)) (χn g : ℕ → Euc K → ℝ)
    (ζ : ℕ → ℝ),
    RefLaw (μ : Measure (Euc K)) U → Mom1 (P : Measure (Euc K)) ≠ ∞ →
    Measurable Q → (μ : Measure (Euc K)).map Q = P → IsCMMapAE (μ : Measure (Euc K)) Q →
    WeightedFit μ P U α ν χn g ζ →
      (∃ χ : Euc K → ℝ, ConvexOn ℝ (interior U) χ ∧ Q =ᵐ[(μ : Measure (Euc K))] gradient χ ∧
          IsGLB (χ '' interior U) 0) ∧
        ∀ χ : Euc K → ℝ, ConvexOn ℝ (interior U) χ → Q =ᵐ[(μ : Measure (Euc K))] gradient χ →
          IsGLB (χ '' interior U) 0 → ∀ c : ℕ → ℝ, (∀ n, IsGLB (χn n '' U) (c n)) →
            ∀ S ⊆ interior U, IsCompact S →
              TendstoUniformlyOn (fun n u => χn n u - c n) χ atTop S ∧
                TendstoUniformlyOn (fun n u => g n u - c n) χ atTop S

/-- `cond_maps_ae_inexact` for the verbatim discrete assumption (`WeightedFit`, C `ass:conditional-oos` with
`eq:weighted-hard-gap`; `U` compact by `RefLaw`). -/
def cond_maps_ae_weighted : Prop :=
  ∀ (K : ℕ) (μ P : ProbabilityMeasure (Euc K)) (U : Set (Euc K)) (χ : Euc K → ℝ) (Q : Euc K → Euc K)
    (Qn : ℕ → Euc K → Euc K) (α ν : ℕ → ProbabilityMeasure (Euc K))
    (χn g : ℕ → Euc K → ℝ) (ζ : ℕ → ℝ),
    RefLaw (μ : Measure (Euc K)) U → Mom1 (P : Measure (Euc K)) ≠ ∞ →
    Measurable Q → (μ : Measure (Euc K)).map Q = P →
    ConvexOn ℝ (interior U) χ → Q =ᵐ[(μ : Measure (Euc K))] gradient χ →
    WeightedFit μ P U α ν χn g ζ → (∀ n, ConvexOn ℝ (interior U) (g n)) →
    (∀ n, ∀ u ∈ interior U, Qn n u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n)) u) →
      ∀ᵐ u ∂(μ : Measure (Euc K)), u ∈ interior U ∧ DifferentiableAt ℝ χ u ∧ Tendsto (fun n => Qn n u) atTop (𝓝 (Q u))

/-- `cond_band_one_sided_inexact` for the verbatim discrete assumption (`WeightedFit`, C `ass:conditional-oos` with
`eq:weighted-hard-gap`; `U` compact by `RefLaw`). -/
def cond_band_one_sided_weighted : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ P : ProbabilityMeasure (Euc K)) (U A : Set (Euc K)) (χ : Euc K → ℝ) (Q : Euc K → Euc K)
    (Qn : ℕ → Euc K → Euc K) (α ν : ℕ → ProbabilityMeasure (Euc K))
    (χn g : ℕ → Euc K → ℝ) (ζ : ℕ → ℝ) (e : 𝒯 → Euc K) (R EK : ℝ),
    RefLaw (μ : Measure (Euc K)) U → Mom1 (P : Measure (Euc K)) ≠ ∞ →
    Measurable Q → (μ : Measure (Euc K)).map Q = P →
    ConvexOn ℝ (interior U) χ → Q =ᵐ[(μ : Measure (Euc K))] gradient χ →
    WeightedFit μ P U α ν χn g ζ → (∀ n, ConvexOn ℝ (interior U) (g n)) →
    (∀ n, ∀ u ∈ interior U, Qn n u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n)) u) →
    MeasurableSet A → (∀ᵐ u ∂(μ : Measure (Euc K)).restrict A, ‖Q u‖ ≤ R) → (∀ t, ‖e t‖ ≤ EK) →
      ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t,
        StatFormal.Wave17a.hPop (μ : Measure (Euc K)) A Q (e t) ≤ StatFormal.Wave21b.supE A (Qn n) (e t) + η ∧
          StatFormal.Wave17a.hPop (μ : Measure (Euc K)) A Q (-e t) ≤ StatFormal.Wave21b.supE A (Qn n) (-e t) + η

/-- `cond_test_coverage_inexact` for the verbatim discrete assumption (`WeightedFit`, C `ass:conditional-oos` with
`eq:weighted-hard-gap`; `U` compact by `RefLaw`). -/
def cond_test_coverage_weighted : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ P : ProbabilityMeasure (Euc K)) (U A : Set (Euc K)) (χ : Euc K → ℝ) (Q : Euc K → Euc K)
    (Qn : ℕ → Euc K → Euc K) (α ν : ℕ → ProbabilityMeasure (Euc K))
    (χn g : ℕ → Euc K → ℝ) (ζ : ℕ → ℝ) (m : 𝒯 → ℝ) (e : 𝒯 → Euc K)
    (Ue Le : ℕ → 𝒯 → EReal) (R EK p κ : ℝ),
    RefLaw (μ : Measure (Euc K)) U → Mom1 (P : Measure (Euc K)) ≠ ∞ →
    Measurable Q → (μ : Measure (Euc K)).map Q = P →
    ConvexOn ℝ (interior U) χ → Q =ᵐ[(μ : Measure (Euc K))] gradient χ →
    WeightedFit μ P U α ν χn g ζ → (∀ n, ConvexOn ℝ (interior U) (g n)) →
    (∀ n, ∀ u ∈ interior U, Qn n u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n)) u) →
    MeasurableSet A → (∀ᵐ u ∂(μ : Measure (Euc K)).restrict A, ‖Q u‖ ≤ R) → (∀ t, ‖e t‖ ≤ EK) →
    ENNReal.ofReal p ≤ (μ : Measure (Euc K)) A → 0 < κ →
    (∀ n t, (m t : EReal) + StatFormal.Wave21b.supE A (Qn n) (e t) ≤ Ue n t ∧
      Le n t ≤ (m t : EReal) - StatFormal.Wave21b.supE A (Qn n) (-e t)) →
      ∀ᶠ n in atTop, ∃ E : Set (Euc K), MeasurableSet E ∧
        E ⊆ {z | ∀ t, Le n t - κ ≤ ((m t + ⟪e t, z⟫ : ℝ) : EReal) ∧ ((m t + ⟪e t, z⟫ : ℝ) : EReal) ≤ Ue n t + κ} ∧
        ENNReal.ofReal p ≤ (μ : Measure (Euc K)).map Q E

/-- `cond_transfer_consistency_inexact` for the verbatim discrete assumption (`WeightedFit`, C `ass:conditional-oos` with
`eq:weighted-hard-gap`; `U` compact by `RefLaw`). -/
def cond_transfer_consistency_weighted : Prop :=
  ∀ (K : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (μ P' : ProbabilityMeasure (Euc K)) (U DF : Set (Euc K))
    (Z : Ω → Euc K) (F : Euc K → Euc K) (Fh : ℕ → Ω → Euc K → Euc K) (χ' : Euc K → ℝ) (Q' : Euc K → Euc K)
    (Qh : ℕ → Ω → Euc K → Euc K) (α ν : ℕ → Ω → ProbabilityMeasure (Euc K)) (χn g : ℕ → Ω → Euc K → ℝ) (ζ : ℕ → Ω → ℝ),
    RefLaw (μ : Measure (Euc K)) U → Measurable Z → Measurable F → P.map (fun ω => F (Z ω)) = μ →
    (∀ᵐ ω ∂P, Z ω ∈ DF) → (∀ᵐ ω ∂P, ∀ z ∈ DF, Tendsto (fun n => Fh n ω z) atTop (𝓝 (F z))) →
    ConvexOn ℝ (interior U) χ' → Q' =ᵐ[(μ : Measure (Euc K))] gradient χ' →
    Mom1 (P' : Measure (Euc K)) ≠ ∞ → Measurable Q' → (μ : Measure (Euc K)).map Q' = P' →
    (∀ᵐ ω ∂P, WeightedFit μ P' U (fun n => α n ω) (fun n => ν n ω) (fun n => χn n ω) (fun n => g n ω)
        (fun n => ζ n ω) ∧
      ∀ n, ConvexOn ℝ (interior U) (g n ω)) →
    (∀ n ω, ∀ u ∈ interior U, Qh n ω u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n ω)) u) →
      ∀ᵐ ω ∂P, F (Z ω) ∈ interior U ∧ DifferentiableAt ℝ χ' (F (Z ω)) ∧ Q' (F (Z ω)) = gradient χ' (F (Z ω)) ∧
        Tendsto (fun n => Qh n ω (Fh n ω (Z ω))) atTop (𝓝 (Q' (F (Z ω))))

/-- `cond_transfer_consistency_prob_inexact` for the verbatim discrete assumption (`WeightedFit`, C `ass:conditional-oos` with
`eq:weighted-hard-gap`; `U` compact by `RefLaw`). -/
def cond_transfer_consistency_prob_weighted : Prop :=
  ∀ (K : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] (μ P' : ProbabilityMeasure (Euc K))
    (U DF : Set (Euc K)) (Z : Ω → Euc K) (F : Euc K → Euc K) (Fh : ℕ → Ω → Euc K → Euc K) (χ' : Euc K → ℝ)
    (Q' : Euc K → Euc K) (Qh : ℕ → Ω → Euc K → Euc K) (α ν : ℕ → Ω → ProbabilityMeasure (Euc K)) (χn g : ℕ → Ω → Euc K → ℝ) (ζ : ℕ → Ω → ℝ),
    RefLaw (μ : Measure (Euc K)) U → Measurable Z → Measurable F → P.map (fun ω => F (Z ω)) = μ →
    (∀ᵐ ω ∂P, Z ω ∈ DF) → (∀ᵐ ω ∂P, ∀ z ∈ DF, Tendsto (fun n => Fh n ω z) atTop (𝓝 (F z))) →
    ConvexOn ℝ (interior U) χ' → Q' =ᵐ[(μ : Measure (Euc K))] gradient χ' →
    Mom1 (P' : Measure (Euc K)) ≠ ∞ → Measurable Q' → (μ : Measure (Euc K)).map Q' = P' →
    (∀ᵐ ω ∂P, WeightedFit μ P' U (fun n => α n ω) (fun n => ν n ω) (fun n => χn n ω) (fun n => g n ω)
        (fun n => ζ n ω) ∧
      ∀ n, ConvexOn ℝ (interior U) (g n ω)) →
    (∀ n ω, ∀ u ∈ interior U, Qh n ω u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n ω)) u) →
    (∀ n, AEStronglyMeasurable (fun ω => Qh n ω (Fh n ω (Z ω))) P) →
      TendstoInMeasure P (fun n ω => Qh n ω (Fh n ω (Z ω))) atTop (fun ω => Q' (F (Z ω)))

end Claims

end StatFormal.OTFD.WaveL4
