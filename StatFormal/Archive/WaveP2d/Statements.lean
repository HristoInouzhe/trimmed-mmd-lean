import StatFormal.Archive.Wave24a.Statements
import StatFormal.Archive.Wave14a.Statements
import StatFormal.Archive.Wave15b.Statements
import StatFormal.Archive.Wave24e.Statements
import StatFormal.Archive.Wave17a.Statements
import StatFormal.Archive.Wave21a.Statements
import StatFormal.Archive.Wave16a.Statements
import StatFormal.Archive.OTFD.WaveL2.Statements

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave P2d (partial-audit waves 2a MINK + A rates, 2e mixed): A `prop:emp-bijective-weak`,
# `cor:app-entropic-weak`, `cor:app-bijective-rate` (sharp (a), (b)), `prop:lift-consistency`, `prop:selector` (ii),
# `prop:parsimony`; ICL `prop:fixed-point` (existence); TM `lem:rffkernel` (sup), `thm:rffjoint` (unconditional),
# `prop:otstructure` (LP strong duality); paper 2 `prop:jointmin` (`ε = 0`)

Sources (current text, read 2026-10-16; paths under `~/pCloudDrive/research-lines/`):
* A (`otfd/papers/A_sieves/`): `prop:emp-bijective-weak` (`supplement.tex:2528-2546`, last sentence), with
  `ass:app-weak-conditioning` (`:2493-2508`); `cor:app-bijective-rate` (`:2566-2591`), with `prop:rate-decomp`
  (`:2361-2413`: `Δ^{emp,(m)}_n`, `Δ^{grid}_n`, `Δ^{sieve,L²}_n`, `eq:app-rate-decomp`) and `ass:app-grid-stability`
  (`:2445-2480`); `cor:app-entropic-weak` (`:2597-2619`, the Minkowski sentence); `prop:lift-consistency`
  (`:5464-5475`, the "Hence" sentence); `prop:selector` (`main.tex:1251-1267`, (ii) and the remark after the list,
  proof `supplement.tex:4969-5000`); `prop:parsimony` (`main.tex:1330-1338`, first conclusion, proof
  `supplement.tex:5022-`), with `lem:T-stability` (`main.tex:1228-1233`).
* ICL `prop:fixed-point` (`context-distribution-ICL/paper/v3/supp/theory.tex:9-20`), first sentence (existence).
* TM (`trimmed-mmd/paper.tex`): `prop:otstructure` (`:1498-1511`, with `eq:ptp` `:1485-1490`); `lem:rffkernel`
  (`:1694-1707`); `thm:rffjoint` (`:1709-1727`).
* paper 2 `prop:jointmin` (`robust-equality-outcomes-under-distribution-shift/paper2/main.tex:305-313`), the case
  `ε = 0` with `T⁰_s` as read after `eq:T` (`:244-252`).
* Frozen objects reused (imported, not copied): Wave 8b `SubgradAt`, `OneSidedAt`, `IsOptAssign`, `IsEntPlan`,
  `entBary`, `embed`; Wave 6b `empMeasure`; Wave 1 `truncK`, `edStat`; WaveL1 `LipNull`, `IsCMMapAE`; Wave 12b `Euc`;
  Wave 14a `IsMFMinimizer`, `T0`; Wave 6a `epBall`; Wave 15b `PtpFeasible`, `PtpDualFeasible`, `ptpCost`,
  `ptpDualVal`, `rowRed`, `colRed`; Wave 24e `unifCircle`, `rffKernel`, `bochnerKernel`; TrimmedMMD `rn`, `Demp`,
  `Dpop`; Wave 21a/paper 2 `Plans`, `pcost`, Certificate `centre`, Wave 19b `worstDisp`; Wave 16a `sqn`, `IsHeadMap`,
  `IsSepTail`, `liftMap`, `quadTail`, `varK`; Scale `IsGauge`, `ScaleHyp`, `ups`; Wave 22a `energyD`, `IsConvGradAE`.
  New definitions: `rffFeat` (the feature map `z_r`), `rffH`, `rffEps` (`h`, `ε_r(δ)`), `jointObj0`, `penObj0`
  (`Ψ⁰`, `R + ηF̄⁰`), `parsSel` (the parsimonious rule).

Covered:
* `prop:emp-bijective-weak`: `emp_bijective_weak_mink` ("Consequently `Δ^{emp,(n)}_n` is bounded by the square root
  of the right-hand side plus `Δ^{grid}_n`", for any Borel map in the role of `F_{+,K_n,n}`).
* `cor:app-entropic-weak`: `app_entropic_weak_mink` (the Minkowski sentence; "the latter vanishes" is the frozen WaveL3
  `sieve_strong_limit_uncond`, already used by the frozen Wave 24a `app_entropic_rate`).
* `cor:app-bijective-rate`: `app_bijective_rate_sharp` ((a) as printed: `{E…}^{1/2} ≤ √B_n + S(K_n)` for every
  `n ≥ 1`, and `S(K_n) → 0`; the frozen Wave 24a premise `B_n → 0` removed; it implies the frozen
  `app_bijective_rate`, route `RouteImplies`); `app_bijective_rate_b` ((b): `Δ^{emp,(n)}_n ≤ √B_n + Δ^{grid}_n`,
  `Δ^{grid}_n → 0`, and all three terms of `eq:app-rate-decomp` vanish when `B_n → 0`).
* `prop:lift-consistency`: `lift_hence_sep`, `lift_hence_quad` (the "Hence" sentence, finite ambient `T`, both
  tail families of `prop:lift-dual`; no condition on `K_n`).
* `prop:selector`: `selector_ii` ((ii) and the `s_n`-remark, random training fold; with `P_K ≪ Leb` and second moments
  of `P_K`, `μ_K` added, see Encodings).
* `prop:parsimony`: `parsimony_ii` ("The conclusions of `prop:selector`(ii) hold for `θ̃`"; same added hypotheses).
* `prop:fixed-point`: `fixed_point_exists` (existence of a minimizer).
* `prop:otstructure`: `ptp_strong_duality` (LP strong duality for `eq:ptp`), `otstructure_opt` (the proposition as
  printed, for an optimal primal and an OPTIMAL dual solution, no zero-gap premise; it implies the frozen Wave 15b
  `otstructure`).
* `lem:rffkernel`: `rff_sup` (the supremum over the compact domain, `r^{−1/2}` with an explicit `h`).
* `thm:rffjoint`: `rffjoint_uncond` (the frozen Wave 17a `rffjoint` with its `lem:rffkernel` premise discharged).
* `prop:jointmin`: `jointmin_upper0`, `jointmin_inf0` (the case `ε = 0`).

Not covered (declared):
* A `cor:app-bijective-rate`, `cor:app-entropic-rate`: the "transparent sufficient set" sentences.
* A `prop:lift-consistency`: the `T = ∞` inequality (the lift of `prop:lift-dual` in `H` is not formalised).
* A `cor:matched-gaussian-cubic`: `α_K = √(2π)`, the midpoint bound `q⁻¹Σ_ℓ{Φ⁻¹((ℓ−½)/q)}² ≤ 1`, the `W₂` grid bound
  (need the probit's convexity calculus, the Gaussian quantile identification and a quantiser coupling on the
  cubic law; not attempted).
* A `prop:parsimony`: the interpretive last sentence ("the spread of the criterion…") and the diagnostic paragraph.
* ICL `prop:fixed-point`: "For `M ≥ 2` the objective need not be convex, and the fixed point need not be unique"
  (existential remarks).
* TM `lem:rffkernel`: "Sriperumbudur–Szabó show that rate is optimal" (a citation).
* paper 2 `prop:jointmin`: structured sets with a finite cell cover (the structured certificate is not frozen); the
  anisotropic sets on an unbounded `K` (on a bounded `K` an anisotropic cost is bounded and is an instance of the
  frozen Wave 21a `jointmin_upper`, any bounded measurable cost).

Encodings (to be checked by the critic):
* Minkowski claims: the frozen Wave 8b / Wave 24a encodings verbatim (lower integrals `∫⁻` of `ENNReal.ofReal` of the
  averages, `{·}^{1/2} = rpow (1/2)` in `ℝ≥0∞`, `W₂` Tau Ceti's `wassersteinEDist 2`). `F_{+,K_n,m_n}` (the
  finite-grid population map, not formalised) is any Borel map `G` (generalisation: the inequalities hold for every
  `G`); `F_{+,K}` and `𝔽_P` Borel (`Δ^{grid}`, `Δ^{sieve}` are then genuine integrals; the fitted maps need no
  measurability). `Δ^{sieve,L²}_n` is printed with the sample average, `S(K)` with one draw (equal by identical
  laws). `ass:app-grid-stability`: `L_n ∈ ℝ` (`ENNReal.ofReal L_n`), `a ∈ (0,1]` (the printed `α`), the product
  `L_n W₂^a` in `ℝ≥0∞`.
* `lift_hence_*`: the frozen Wave 16a finite-`T` setting; "computed sieve ranks converge in mean square" is
  `E‖F̂_n(X) − F(X)‖² → 0` for head maps `F̂_n = ι_{K_n}F̂_{K_n}` (any schedule, in particular those of
  `thm:app-hard-diagonal`, `thm:app-entropic-diagonal`).
* `selector_ii`, `parsimony_ii`: `ℝ^K` with `P_K = P`; the training fold is a probability space `(Ω_t, P_t)` shared by
  all `n` (any training-fold law); candidates `F̂_{n,θ}(ω)` jointly measurable in `(ω, x)`, each `P_K`-a.e. the
  gradient of a convex function (frozen `IsConvGradAE`); `Θ_n` a nonempty `Fintype` (`|Θ_n|` its card);
  validation draws `(Z, U)` with law `P_K^{⊗n_v} ⊗ μ_K^{⊗m_v}`, independent of the fold (product with `P_t`);
  `D(θ) = ED(Υ#F̂_θ#P_K, Υ#μ_K)` is the frozen `energyD` (the form of `lem:T-stability`), `D̂` the frozen `edStat` of
  `a_i = ΥF̂_θ(Z_i)`, `b_j = Υ(U_j)`; `θ̂` any selection (a function of fold and validation draws, no
  measurability) with `D̂(θ̂) ≤ D̂(θ) + s_n` for all `θ` (the printed minimiser is `s_n = 0`); `log|Θ_n| =
  o(min(n_v, m_v))` is `log|Θ_n| / min(n_v, m_v) → 0`; "`X_n → X` in `Q`-probability" is
  `∀η>0, Q{η < ‖X_n − X‖} → 0` (for `F̂ → F_K` in `P_K`-probability, in probability:
  `P_t{ω : η < P_K{η < ‖F̂(ω) − F_K‖}} → 0`, the Ky Fan form; equivalent); events that need not be measurable are
  measured by the outer measure (a stronger conclusion). The assumptions of `lem:T-stability` are those of the
  frozen WaveL2 `t_stability_delta` (gauge `g`, `ass:scale`, `P_K ≪ Leb`, second moments, `F_K` a convex gradient with
  `F_K#P_K = μ_K`); `R ≥ ‖Υ‖` (`R_Υ`). DEVIATION (conditionalisation): `P_K ≪ Leb` replaces `P_K ∈ 𝒫^ℓ(ℝ^K)` and
  `MemLp id 2` of `P_K` and `μ_K` is assumed, although the remark after `prop:selector` says "No moment of `P_K` or of
  the reference is needed" (both inherited from the frozen `t_stability_delta`; a moment-free `lem:T-stability` would
  remove them). The oracle index `θ*_n` may depend on the training fold (generalisation).
* `fixed_point_exists`: `𝒵` a compact metric space with its Borel σ-algebra, `L` continuous on `𝒵 × 𝒵^M` (bounded by
  compactness); the frozen Wave 14a objective (`Π_μ = μ^{⊗M}` built in, so `P₀` atomless is not needed) and
  minimiser notion (over probability measures with `KL(·|P₀) < ∞`).
* `ptp_strong_duality`, `otstructure_opt`: the frozen Wave 15b LP encoding; "`(u, z, θ)` optimal dual" is dual
  feasibility plus maximality of `ptpDualVal` among dual-feasible triples; `Π⋆` solves `eq:ptp`: feasible and of
  minimal `ptpCost`.
* `rff_sup`: the frozen Wave 24e feature encoding (`(ω_j, b_j)` i.i.d. `Λ ⊗ Unif[0,2π]` on `Ω`, measurable,
  `iIndepFun`); `𝒳 ⊂ ℝ^d` compact (a set; `supp P ∪ supp Q ⊆ 𝒳` only matters in `thm:rffjoint`); `σ_Λ² = ∫‖ω‖² dΛ`
  with `‖·‖²` integrable; `h(d, diam 𝒳, σ_Λ)` is the explicit `rffH (diam 𝒳) σ_Λ = 4 + 12 diam(𝒳) σ_Λ` (a valid
  choice: the printed lemma asserts some `h` free of `r`); "with probability at least `1 − δ`": a measurable event of
  `Pr`-measure `≥ 1 − δ` carrying the bound for all `x, y ∈ 𝒳`.
* `rffjoint_uncond`: the frozen Wave 17a encoding with `𝒳` the subtype of the compact set (laws `P, Q` on it), the
  kernel `k = bochnerKernel κ Λ` realised by any feature map `φ` into a separable Hilbert space with `⟨φx, φy⟩ = k`
  and `‖φ‖ ≤ κ` (`ass:regularity`), the random features `z_r = rffFeat` on the feature space `Ω` (the frozen `ν` is
  `Pr`), `ε = ε_r(δ/3)`.
* `jointmin_*0`: the frozen Wave 21a encoding at a single reference per group, with the `ε = 0` set (the frozen Wave
  6a `epBall … 0 r`: `Q(supp ν) = 1`, `W₂²(P̂, Q) ≤ r`) and the cost `c = d²` of a Polish metric space (the setting of
  the certified `thm:ep-cert0`(i), frozen Wave 14a `ep_cert0_i`); `T⁰_s(h, λ) = λr_s + n⁻¹Σ_i sup_{x∈supp ν}
  {f_h(x_i, x) − λd(x_i, x)²}` is the frozen `T0`; `λ_s > 0`.

Route notes (untrusted proofs in `WaveP2d/Route*.lean`, axioms `propext, Classical.choice, Quot.sound`):
* Minkowski for lower integrals with one measurable summand (`RouteMink.mink_lower`: measurable minorant of the
  integrand, truncated subtraction, `ENNReal.lintegral_Lp_add_le`); the frozen Wave 8b, Wave 6b
  (`empirical_wass_rate20`), WaveL3 and Wave 24a route lemmas for the other terms.
* `fixed_point_exists`: Prokhorov (Mathlib: `𝒫(𝒵)` compact), `ProbabilityMeasure.continuous_pi` and dominated
  convergence (weak continuity of the mean risk), weak lower semicontinuity of `KL(·|P₀)` (Foundations/Giry).
* `ptp_strong_duality`: dummy-node reduction to Tau Ceti's finite Kantorovich duality (`exists_cost_eq_finiteDualValue`)
  with cost `Σ|C_ij|` on the dummy pair; the rescaled real block is `eq:ptp`-feasible.
* `rff_sup`: library Foundations/Concentration (McDiarmid over a countable dense set, symmetrisation, the
  contraction principle), the product-to-sum formula, the linear-class bound `E_σ sup_v |Σσ_jω_jᵀv| ≤
  R(Σ‖ω_j‖²)^{1/2}`, Jensen; continuity of both kernels extends the bound off the dense set.
* `selector_ii`: the frozen Wave 23b `selector_dev` per candidate at level `γ/|Θ_n|` (one-point class), a union bound
  and Tonelli over the training fold; `edPop = energyD` for bounded pushforwards; `D(θ*_n) → 0` from the coupling bound
  `ED ≤ 2E‖ΥF̂ − ΥF_K‖` (continuity and uniform continuity of `Υ`, tightness of `F_K#P_K`); the frozen WaveL2
  `t_stability_delta` for the map.
* Observations (manuscript): (1) `lem:rffkernel` holds with the dimension-free `h = 4 + 12 diam(𝒳) σ_Λ` (the contraction
  principle reduces the class to the linear class `ω ↦ ωᵀv`, whose Rademacher average is `≤ ‖v‖ E‖Σσ_jω_j‖`); the
  deviation term `2√(2 log(1/δ))` is exact. (2) `prop:selector`(ii): the proof's "for every fixed `γ` we have `Δ → 0`"
  fails when `|Θ_n| = 1` and `min(n_v, m_v)` stays bounded (then `log|Θ_n| = 0 = o(·)`, but `Δ ≥ 2R_Υh` does not
  vanish); the proposition is still true (one candidate is selected trivially), and the route treats that case
  separately. Minimal fix of the proof: "If `|Θ_n| = 1`, then `θ̂ = θ*_n`; otherwise `log|Θ_n| ≥ log 2`, so
  `log|Θ_n| = o(min(n_v, m_v))` forces `h → 0`, and for every fixed `γ` we have `Δ → 0`" (minor: proof gap only). (3) `prop:otstructure`: strong duality holds for every feasible instance of `eq:ptp` (no condition on
  `a, b, C`), so the optimal dual solution of the statement always exists with zero gap. (4) `prop:fixed-point`:
  existence needs neither the atomless `P₀` nor the symmetry of `L` (both used only to identify `Π_μ = μ^{⊗M}` and for
  the first-order condition). (5) `cor:app-bijective-rate`(b): "`Δ^{grid}_n → 0`" is the second clause of
  `ass:app-grid-stability` itself. (6) `prop:lift-consistency`: the tail term never needs `K_n → ∞`: for head maps
  `E‖U_⊥‖² ≤ E‖ι_K F̂_K − F‖²`, so the lift error is at most four times the sieve error.

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.WaveP2d

/-! ### TM random features: the feature map and the constant of `lem:rffkernel` -/

/-- The phased random-feature map `z_r(x) = κ √(2/r) [cos(ω_jᵀx + b_j)]_{j ≤ r}` (so that `⟨z_r(x), z_r(y)⟩` is the
frozen Wave 24e `rffKernel`). -/
def rffFeat {d r : ℕ} (κ : ℝ) (w : Fin r → EuclideanSpace ℝ (Fin d)) (b : Fin r → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin r) :=
  WithLp.toLp 2 fun j => κ * √(2 / r) * Real.cos (⟪w j, x⟫ + b j)

/-- The constant `h(d, diam 𝒳, σ_Λ)` of `lem:rffkernel`, here explicit and free of `d`: `h = 4 + 12 diam(𝒳) σ_Λ`. -/
def rffH (D σ : ℝ) : ℝ := 4 + 12 * D * σ

/-- `ε_r(δ) = κ²[h + 2√(2 log(1/δ))]/√r`. -/
def rffEps (κ D σ : ℝ) (r : ℕ) (δ : ℝ) : ℝ := κ ^ 2 * (rffH D σ + 2 * √(2 * Real.log (1 / δ))) / √(r : ℝ)

/-! ### paper 2 `prop:jointmin` at `ε = 0`: the objectives -/

section JointMin0
variable {𝒦 : Type} [MetricSpace 𝒦] [MeasurableSpace 𝒦]

/-- The joint objective at `ε = 0` (single reference per group, `T⁰_s` read as in `eq:T` for `ε = 0`, the frozen Wave
14a `T0` over `supp ν_s`): `Ψ⁰ = R + η (√E_γ{h(X)−h(Y)}² + √T⁰₀(h,λ₀) + √T⁰₁(h,λ₁))²`. -/
def jointObj0 {n₀ n₁ : ℕ} (x₀ : Fin n₀ → 𝒦) (x₁ : Fin n₁ → 𝒦) (h : 𝒦 → ℝ) (r₀ r₁ : ℝ) (ν₀ ν₁ : Measure 𝒦)
    (Rh η lam₀ lam₁ : ℝ) (γ : Fin n₀ → Fin n₁ → ℝ) : ℝ :=
  Rh + η * (√(StatFormal.RobustEquality.Paper2.Alternating.pcost (fun i => h (x₀ i)) (fun j => h (x₁ j)) γ) +
    √(StatFormal.Wave14a.T0 x₀ ν₀.support h r₀ lam₀) + √(StatFormal.Wave14a.T0 x₁ ν₁.support h r₁ lam₁)) ^ 2

/-- The objective of `(P_η)` at `ε = 0`: `R + η F̄⁰(h; λ)`, `Δ(h) = W₂(h#P̂₀, h#P̂₁)`. -/
def penObj0 {n₀ n₁ : ℕ} (x₀ : Fin n₀ → 𝒦) (x₁ : Fin n₁ → 𝒦) (h : 𝒦 → ℝ) (r₀ r₁ : ℝ) (ν₀ ν₁ : Measure 𝒦)
    (Rh η lam₀ lam₁ : ℝ) : ℝ :=
  Rh + η * ((TauCeti.wassersteinEDist 2 ((StatFormal.RobustEquality.Certificate.centre x₀).map h)
      ((StatFormal.RobustEquality.Certificate.centre x₁).map h)).toReal +
    √(StatFormal.Wave14a.T0 x₀ ν₀.support h r₀ lam₀) + √(StatFormal.Wave14a.T0 x₁ ν₁.support h r₁ lam₁)) ^ 2

end JointMin0

/-! ### A `prop:parsimony`: the parsimonious selection rule -/

/-- `prop:parsimony`'s rule: in the complexity order of `Θ` (a linear order), the first candidate `θ̃` with
`D̂(θ̃) ≤ min_Θ D̂ + s` (for `s ≥ 0` the set is nonempty, as it contains the minimisers; otherwise an arbitrary
candidate). -/
def parsSel {Θ : Type} [Fintype Θ] [LinearOrder Θ] [Nonempty Θ] (Dh : Θ → ℝ) (s : ℝ) : Θ :=
  if h : (Finset.univ.filter fun θ => Dh θ ≤ Finset.univ.inf' Finset.univ_nonempty Dh + s).Nonempty then
    (Finset.univ.filter fun θ => Dh θ ≤ Finset.univ.inf' Finset.univ_nonempty Dh + s).min' h
  else Classical.arbitrary Θ

namespace Claims

/-! ### A `prop:emp-bijective-weak`, "Consequently" -/

/-- `prop:emp-bijective-weak`, last sentence: with `G` in the role of the finite-grid population map `F_{+,K_n,n}`,
`Δ^{emp,(n)}_n = {E[n⁻¹Σ‖F̂(x_i) − G(x_i)‖²]}^{1/2}` is at most the square root of the displayed right-hand side plus
`Δ^{grid}_n = {E[n⁻¹Σ‖G(x_i) − F(x_i)‖²]}^{1/2}` (frozen Wave 8b `emp_bijective_weak` setting, `F`, `G` Borel). -/
def emp_bijective_weak_mink : Prop :=
  ∀ (K n : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (PK μ : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure μ]
    (x : Fin n → Ω → EuclideanSpace ℝ (Fin K)) (F G : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (u s : Fin n → EuclideanSpace ℝ (Fin K)) (f : EuclideanSpace ℝ (Fin K) → ℝ) (α β : ℝ)
    (σ : Ω → Equiv.Perm (Fin n)),
    1 ≤ n → 0 < α → (∀ i, Measurable (x i)) → (∀ i, P.map (x i) = PK) →
    Integrable (fun z => ‖z‖ ^ 2) PK → (1 / n : ℝ) * ∑ j, ‖s j‖ ^ 2 ≤ β ^ 2 →
    (∀ᵐ ω ∂P, StatFormal.OTFD.Wave8b.SubgradAt f u s (fun i => F (x i ω)) ∧
      StatFormal.OTFD.Wave8b.OneSidedAt α f u (fun i => x i ω) (fun i => F (x i ω))) →
    (∀ ω, StatFormal.OTFD.Wave8b.IsOptAssign (fun i => x i ω) u (σ ω)) →
    Measurable F → Measurable G →
      (∫⁻ ω, ENNReal.ofReal ((1 / n : ℝ) * ∑ i, ‖u (σ ω i) - G (x i ω)‖ ^ 2) ∂P) ^ (1 / 2 : ℝ) ≤
        (ENNReal.ofReal (4 / α * Real.sqrt (β ^ 2 + ∫ z, ‖z‖ ^ 2 ∂PK)) *
          (∫⁻ ω, TauCeti.wassersteinEDist 2 (StatFormal.OTFD.Wave6b.empMeasure fun i => F (x i ω)) μ ^ 2 ∂P +
              TauCeti.wassersteinEDist 2 (StatFormal.OTFD.Wave6b.empMeasure u) μ ^ 2) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) +
        (∫⁻ ω, ENNReal.ofReal ((1 / n : ℝ) * ∑ i, ‖G (x i ω) - F (x i ω)‖ ^ 2) ∂P) ^ (1 / 2 : ℝ)

/-! ### A `cor:app-entropic-weak`, the Minkowski sentence -/

/-- `cor:app-entropic-weak`, "After taking square roots and inserting `ι_K F_{+,K_n}(x_i)`, Minkowski's inequality
bounds the Hilbert-space root mean squared error by the square root of this display's right-hand side plus
`Δ^{sieve,L²}_n`": data `X_i` with law `P` on `H`, `x_i = Π_K X_i`, `𝔽_P = F`, `F_{+,K} = FK` (Borel), the frozen
Wave 8b `app_entropic_weak` hypotheses at `P_K = Π_K#P`, `μ_K = Π_K#μ`. -/
def app_entropic_weak_mink : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    [SecondCountableTopology H] (e : ℕ → H) (K n m : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (PH μ : Measure H) [IsProbabilityMeasure PH] [IsProbabilityMeasure μ]
    (X : Fin n → Ω → H) (F : H → H) (FK : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (u s : Fin m → EuclideanSpace ℝ (Fin K)) (f : EuclideanSpace ℝ (Fin K) → ℝ) (α β ε : ℝ)
    (π : Ω → Matrix (Fin n) (Fin m) ℝ),
    Orthonormal ℝ e → 1 ≤ n → 1 ≤ m → 0 < α → 0 < ε → (∀ i, Measurable (X i)) → (∀ i, P.map (X i) = PH) →
    Integrable (fun z => ‖z‖ ^ 2) (PH.map (StatFormal.OTFD.Wave1.truncK e K)) →
    (1 / m : ℝ) * ∑ j, ‖s j‖ ^ 2 ≤ β ^ 2 →
    (∀ᵐ ω ∂P, StatFormal.OTFD.Wave8b.SubgradAt f u s (fun i => FK (StatFormal.OTFD.Wave1.truncK e K (X i ω))) ∧
      StatFormal.OTFD.Wave8b.OneSidedAt α f u (fun i => StatFormal.OTFD.Wave1.truncK e K (X i ω))
        (fun i => FK (StatFormal.OTFD.Wave1.truncK e K (X i ω)))) →
    (∀ ω, StatFormal.OTFD.Wave8b.IsEntPlan ε (fun i => StatFormal.OTFD.Wave1.truncK e K (X i ω)) u (π ω)) →
    Measurable F → Measurable FK →
      (∫⁻ ω, ENNReal.ofReal ((1 / n : ℝ) * ∑ i,
          ‖StatFormal.OTFD.Wave8b.embed e K (StatFormal.OTFD.Wave8b.entBary (π ω) u i) - F (X i ω)‖ ^ 2) ∂P) ^
          (1 / 2 : ℝ) ≤
        (ENNReal.ofReal (4 / α * Real.sqrt (β ^ 2 + ∫ z, ‖z‖ ^ 2 ∂(PH.map (StatFormal.OTFD.Wave1.truncK e K)))) *
            (∫⁻ ω, TauCeti.wassersteinEDist 2 (StatFormal.OTFD.Wave6b.empMeasure fun i =>
                FK (StatFormal.OTFD.Wave1.truncK e K (X i ω))) (μ.map (StatFormal.OTFD.Wave1.truncK e K)) ^ 2 ∂P +
              TauCeti.wassersteinEDist 2 (StatFormal.OTFD.Wave6b.empMeasure u)
                (μ.map (StatFormal.OTFD.Wave1.truncK e K)) ^ 2) ^ (1 / 2 : ℝ) +
          ENNReal.ofReal (ε / α * Real.log (min n m))) ^ (1 / 2 : ℝ) +
        (∫⁻ ω, ENNReal.ofReal ((1 / n : ℝ) * ∑ i,
          ‖StatFormal.OTFD.Wave8b.embed e K (FK (StatFormal.OTFD.Wave1.truncK e K (X i ω))) - F (X i ω)‖ ^ 2) ∂P) ^
          (1 / 2 : ℝ)

/-! ### A `cor:app-bijective-rate` (a), the sharp Minkowski display, and (b) -/

/-- `cor:app-bijective-rate` (a) as printed: in the frozen Wave 24a `app_bijective_rate` setting, WITHOUT the premise
`B_n → 0`, for every `n ≥ 1`
`{E[n⁻¹Σ_i ‖ι_{K_n}F̂^{(n)}(x_i) − 𝔽_P(X_i)‖²_H]}^{1/2} ≤ √B_n + S(K_n)`,
`S(K) = {E‖ι_K F_{+,K}(Π_K X) − 𝔽_P(X)‖²_H}^{1/2}`, and `S(K_n) → 0`. -/
def app_bijective_rate_sharp : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (e : ℕ → H) (P μ : ProbabilityMeasure H) (F : H → H)
    (M : ℝ) (FK : (K : ℕ) → StatFormal.Wave12b.Euc K → StatFormal.Wave12b.Euc K) (Ω : Type) [MeasurableSpace Ω]
    (Pr : Measure Ω) [IsProbabilityMeasure Pr] (Kn : ℕ → ℕ) (X : (n : ℕ) → Fin n → Ω → H)
    (α β : ℕ → ℝ) (u s : (n : ℕ) → Fin n → StatFormal.Wave12b.Euc (Kn n))
    (f : (n : ℕ) → StatFormal.Wave12b.Euc (Kn n) → ℝ) (σ : (n : ℕ) → Ω → Equiv.Perm (Fin n)),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    StatFormal.OTFD.WaveL1.LipNull (P : Measure H) → ∫⁻ x, ‖x‖ₑ ^ 2 ∂(P : Measure H) < ⊤ →
    (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 → Measurable F → (P : Measure H).map F = μ →
    StatFormal.OTFD.WaveL1.IsCMMapAE (P : Measure H) F → (∀ K, Measurable (FK K)) →
    (∀ K, ((P : Measure H).map (StatFormal.OTFD.Wave1.truncK e K)).map (FK K) =
      (μ : Measure H).map (StatFormal.OTFD.Wave1.truncK e K)) →
    (∀ K, StatFormal.OTFD.WaveL1.IsCMMapAE ((P : Measure H).map (StatFormal.OTFD.Wave1.truncK e K)) (FK K)) →
    (∀ n i, Measurable (X n i)) → (∀ n, iIndepFun (X n) Pr) → (∀ n i, Pr.map (X n i) = P) →
    Tendsto Kn atTop atTop →
    (∀ n, 0 < α n) → (∀ n : ℕ, (1 / (n : ℝ)) * ∑ j, ‖s n j‖ ^ 2 ≤ β n ^ 2) →
    (∀ n, ∀ᵐ ω ∂Pr,
      StatFormal.OTFD.Wave8b.SubgradAt (f n) (u n) (s n)
        (fun i => FK (Kn n) (StatFormal.OTFD.Wave1.truncK e (Kn n) (X n i ω))) ∧
      StatFormal.OTFD.Wave8b.OneSidedAt (α n) (f n) (u n) (fun i => StatFormal.OTFD.Wave1.truncK e (Kn n) (X n i ω))
        (fun i => FK (Kn n) (StatFormal.OTFD.Wave1.truncK e (Kn n) (X n i ω)))) →
    (∀ n ω, StatFormal.OTFD.Wave8b.IsOptAssign (fun i => StatFormal.OTFD.Wave1.truncK e (Kn n) (X n i ω)) (u n)
      (σ n ω)) →
      (∀ n : ℕ, 1 ≤ n →
        (∫⁻ ω, ENNReal.ofReal ((1 / (n : ℝ)) * ∑ i,
            ‖StatFormal.OTFD.Wave8b.embed e (Kn n) (u n (σ n ω i)) - F (X n i ω)‖ ^ 2) ∂Pr) ^ (1 / 2 : ℝ) ≤
          (ENNReal.ofReal (4 / α n * √(β n ^ 2 +
              ∫ z, ‖z‖ ^ 2 ∂((P : Measure H).map (StatFormal.OTFD.Wave1.truncK e (Kn n))))) *
            (ENNReal.ofReal (20 * M ^ 2 * (Kn n + 1) * (n : ℝ) ^ (-(2 : ℝ) / (Kn n + 4))) +
              TauCeti.wassersteinEDist 2 (StatFormal.OTFD.Wave6b.empMeasure (u n))
                ((μ : Measure H).map (StatFormal.OTFD.Wave1.truncK e (Kn n))) ^ 2) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) +
          (∫⁻ x, ‖StatFormal.OTFD.Wave8b.embed e (Kn n) (FK (Kn n) (StatFormal.OTFD.Wave1.truncK e (Kn n) x)) - F x‖ₑ ^ 2
            ∂(P : Measure H)) ^ (1 / 2 : ℝ)) ∧
      Tendsto (fun n : ℕ => (∫⁻ x, ‖StatFormal.OTFD.Wave8b.embed e (Kn n)
          (FK (Kn n) (StatFormal.OTFD.Wave1.truncK e (Kn n) x)) - F x‖ₑ ^ 2 ∂(P : Measure H)) ^ (1 / 2 : ℝ))
        atTop (𝓝 0)

/-- `cor:app-bijective-rate` (b): in the same setting, with Borel maps `G_n` in the role of the finite-grid population
maps `F_{+,K_n,n}` and `ass:app-grid-stability` (`Δ^{grid}_n ≤ L_n W₂(μ_{K_n,n}, μ_{K_n})^a`, `a ∈ (0,1]`,
`L_n W₂(μ_{K_n,n}, μ_{K_n})^a → 0`): for every `n ≥ 1`, `Δ^{emp,(n)}_n ≤ √B_n + Δ^{grid}_n`; `Δ^{grid}_n → 0`; and
when `B_n → 0`, each of the three terms `Δ^{emp,(n)}_n`, `Δ^{grid}_n`, `Δ^{sieve,L²}_n` of `eq:app-rate-decomp`
tends to `0`. -/
def app_bijective_rate_b : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (e : ℕ → H) (P μ : ProbabilityMeasure H) (F : H → H)
    (M : ℝ) (FK : (K : ℕ) → StatFormal.Wave12b.Euc K → StatFormal.Wave12b.Euc K) (Ω : Type) [MeasurableSpace Ω]
    (Pr : Measure Ω) [IsProbabilityMeasure Pr] (Kn : ℕ → ℕ) (X : (n : ℕ) → Fin n → Ω → H)
    (α β : ℕ → ℝ) (u s : (n : ℕ) → Fin n → StatFormal.Wave12b.Euc (Kn n))
    (f : (n : ℕ) → StatFormal.Wave12b.Euc (Kn n) → ℝ) (σ : (n : ℕ) → Ω → Equiv.Perm (Fin n))
    (G : (n : ℕ) → StatFormal.Wave12b.Euc (Kn n) → StatFormal.Wave12b.Euc (Kn n)) (L : ℕ → ℝ) (a : ℝ),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    StatFormal.OTFD.WaveL1.LipNull (P : Measure H) → ∫⁻ x, ‖x‖ₑ ^ 2 ∂(P : Measure H) < ⊤ →
    (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 → Measurable F → (P : Measure H).map F = μ →
    StatFormal.OTFD.WaveL1.IsCMMapAE (P : Measure H) F → (∀ K, Measurable (FK K)) →
    (∀ K, ((P : Measure H).map (StatFormal.OTFD.Wave1.truncK e K)).map (FK K) =
      (μ : Measure H).map (StatFormal.OTFD.Wave1.truncK e K)) →
    (∀ K, StatFormal.OTFD.WaveL1.IsCMMapAE ((P : Measure H).map (StatFormal.OTFD.Wave1.truncK e K)) (FK K)) →
    (∀ n i, Measurable (X n i)) → (∀ n, iIndepFun (X n) Pr) → (∀ n i, Pr.map (X n i) = P) →
    Tendsto Kn atTop atTop →
    (∀ n, 0 < α n) → (∀ n : ℕ, (1 / (n : ℝ)) * ∑ j, ‖s n j‖ ^ 2 ≤ β n ^ 2) →
    (∀ n, ∀ᵐ ω ∂Pr,
      StatFormal.OTFD.Wave8b.SubgradAt (f n) (u n) (s n)
        (fun i => FK (Kn n) (StatFormal.OTFD.Wave1.truncK e (Kn n) (X n i ω))) ∧
      StatFormal.OTFD.Wave8b.OneSidedAt (α n) (f n) (u n) (fun i => StatFormal.OTFD.Wave1.truncK e (Kn n) (X n i ω))
        (fun i => FK (Kn n) (StatFormal.OTFD.Wave1.truncK e (Kn n) (X n i ω)))) →
    (∀ n ω, StatFormal.OTFD.Wave8b.IsOptAssign (fun i => StatFormal.OTFD.Wave1.truncK e (Kn n) (X n i ω)) (u n)
      (σ n ω)) →
    (∀ n, Measurable (G n)) → 0 < a → a ≤ 1 →
    (∀ n : ℕ, (∫⁻ ω, ENNReal.ofReal ((1 / (n : ℝ)) * ∑ i,
        ‖G n (StatFormal.OTFD.Wave1.truncK e (Kn n) (X n i ω)) -
          FK (Kn n) (StatFormal.OTFD.Wave1.truncK e (Kn n) (X n i ω))‖ ^ 2) ∂Pr) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (L n) * TauCeti.wassersteinEDist 2 (StatFormal.OTFD.Wave6b.empMeasure (u n))
        ((μ : Measure H).map (StatFormal.OTFD.Wave1.truncK e (Kn n))) ^ a) →
    Tendsto (fun n : ℕ => ENNReal.ofReal (L n) * TauCeti.wassersteinEDist 2 (StatFormal.OTFD.Wave6b.empMeasure (u n))
        ((μ : Measure H).map (StatFormal.OTFD.Wave1.truncK e (Kn n))) ^ a) atTop (𝓝 0) →
      (∀ n : ℕ, 1 ≤ n →
        (∫⁻ ω, ENNReal.ofReal ((1 / (n : ℝ)) * ∑ i,
            ‖u n (σ n ω i) - G n (StatFormal.OTFD.Wave1.truncK e (Kn n) (X n i ω))‖ ^ 2) ∂Pr) ^ (1 / 2 : ℝ) ≤
          (ENNReal.ofReal (4 / α n * √(β n ^ 2 +
              ∫ z, ‖z‖ ^ 2 ∂((P : Measure H).map (StatFormal.OTFD.Wave1.truncK e (Kn n))))) *
            (ENNReal.ofReal (20 * M ^ 2 * (Kn n + 1) * (n : ℝ) ^ (-(2 : ℝ) / (Kn n + 4))) +
              TauCeti.wassersteinEDist 2 (StatFormal.OTFD.Wave6b.empMeasure (u n))
                ((μ : Measure H).map (StatFormal.OTFD.Wave1.truncK e (Kn n))) ^ 2) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) +
          (∫⁻ ω, ENNReal.ofReal ((1 / (n : ℝ)) * ∑ i,
            ‖G n (StatFormal.OTFD.Wave1.truncK e (Kn n) (X n i ω)) -
              FK (Kn n) (StatFormal.OTFD.Wave1.truncK e (Kn n) (X n i ω))‖ ^ 2) ∂Pr) ^ (1 / 2 : ℝ)) ∧
      Tendsto (fun n : ℕ => (∫⁻ ω, ENNReal.ofReal ((1 / (n : ℝ)) * ∑ i,
          ‖G n (StatFormal.OTFD.Wave1.truncK e (Kn n) (X n i ω)) -
            FK (Kn n) (StatFormal.OTFD.Wave1.truncK e (Kn n) (X n i ω))‖ ^ 2) ∂Pr) ^ (1 / 2 : ℝ)) atTop (𝓝 0) ∧
      (Tendsto (fun n : ℕ => ENNReal.ofReal (4 / α n * √(β n ^ 2 +
            ∫ z, ‖z‖ ^ 2 ∂((P : Measure H).map (StatFormal.OTFD.Wave1.truncK e (Kn n))))) *
          (ENNReal.ofReal (20 * M ^ 2 * (Kn n + 1) * (n : ℝ) ^ (-(2 : ℝ) / (Kn n + 4))) +
            TauCeti.wassersteinEDist 2 (StatFormal.OTFD.Wave6b.empMeasure (u n))
              ((μ : Measure H).map (StatFormal.OTFD.Wave1.truncK e (Kn n))) ^ 2) ^ (1 / 2 : ℝ)) atTop (𝓝 0) →
        Tendsto (fun n : ℕ => (∫⁻ ω, ENNReal.ofReal ((1 / (n : ℝ)) * ∑ i,
            ‖u n (σ n ω i) - G n (StatFormal.OTFD.Wave1.truncK e (Kn n) (X n i ω))‖ ^ 2) ∂Pr) ^ (1 / 2 : ℝ))
          atTop (𝓝 0) ∧
        Tendsto (fun n : ℕ => (∫⁻ ω, ENNReal.ofReal ((1 / (n : ℝ)) * ∑ i,
            ‖StatFormal.OTFD.Wave8b.embed e (Kn n) (FK (Kn n) (StatFormal.OTFD.Wave1.truncK e (Kn n) (X n i ω))) -
              F (X n i ω)‖ ^ 2) ∂Pr) ^ (1 / 2 : ℝ)) atTop (𝓝 0))

/-! ### ICL `prop:fixed-point`, existence -/

/-- `prop:fixed-point`, first sentence: on a compact metric space `𝒵` (Borel σ-algebra), for a probability `P₀`, a
loss `L` continuous on `𝒵 × 𝒵^M` (hence bounded) and `λ_KL = λ > 0`, a minimizer `μ⋆` of `J` over the probability
measures with `KL(·|P₀) < ∞` (the frozen Wave 14a `IsMFMinimizer`) exists. -/
def fixed_point_exists : Prop :=
  ∀ (𝒵 : Type) [MetricSpace 𝒵] [CompactSpace 𝒵] [MeasurableSpace 𝒵] [BorelSpace 𝒵] (P0 : Measure 𝒵)
    [IsProbabilityMeasure P0] (m : ℕ) (L : 𝒵 → (Fin (m + 1) → 𝒵) → ℝ) (lam : ℝ),
    0 < lam → Continuous (Function.uncurry L) → ∃ μ : Measure 𝒵, StatFormal.Wave14a.IsMFMinimizer P0 L lam μ

/-! ### TM `prop:otstructure`, LP strong duality -/

/-- LP strong duality for `eq:ptp` (the dummy-node reduction of `agullo2018trimming` to a balanced transport problem):
if `eq:ptp` is feasible, there are a feasible plan `Q` and a feasible dual `(u, z, θ)` with equal values. -/
def ptp_strong_duality : Prop :=
  ∀ (n m : ℕ) (a : Fin n → ℝ) (b : Fin m → ℝ) (C : Fin n → Fin m → ℝ) (P : Fin n → Fin m → ℝ),
    StatFormal.Wave15b.PtpFeasible a b P →
      ∃ (Q : Fin n → Fin m → ℝ) (u : Fin n → ℝ) (z : Fin m → ℝ) (θ : ℝ),
        StatFormal.Wave15b.PtpFeasible a b Q ∧ StatFormal.Wave15b.PtpDualFeasible C u z θ ∧
          StatFormal.Wave15b.ptpCost C Q = StatFormal.Wave15b.ptpDualVal a b u z θ

/-- `prop:otstructure` as printed: `Π⋆` solves `eq:ptp` and `(u, z, θ)`, `u, z ≥ 0`, is an OPTIMAL dual solution (the
frozen Wave 15b `otstructure` with the zero-gap premise replaced by the two optimality conditions): `r_i < θ ⇒
w_i = a_i`, `r_i > θ ⇒ w_i = 0`, symmetrically for `v` with `s_j`, and fractional weight only on the tie sets. -/
def otstructure_opt : Prop :=
  ∀ (n m : ℕ) (a : Fin n → ℝ) (b : Fin m → ℝ) (C : Fin n → Fin m → ℝ) (P : Fin n → Fin m → ℝ)
    (u : Fin n → ℝ) (z : Fin m → ℝ) (θ : ℝ),
    0 < n → 0 < m → StatFormal.Wave15b.PtpFeasible a b P →
    (∀ P', StatFormal.Wave15b.PtpFeasible a b P' → StatFormal.Wave15b.ptpCost C P ≤ StatFormal.Wave15b.ptpCost C P') →
    StatFormal.Wave15b.PtpDualFeasible C u z θ →
    (∀ u' z' θ', StatFormal.Wave15b.PtpDualFeasible C u' z' θ' →
      StatFormal.Wave15b.ptpDualVal a b u' z' θ' ≤ StatFormal.Wave15b.ptpDualVal a b u z θ) →
      (∀ i, (StatFormal.Wave15b.rowRed C z i < θ → ∑ j, P i j = a i) ∧
        (θ < StatFormal.Wave15b.rowRed C z i → ∑ j, P i j = 0)) ∧
      (∀ j, (StatFormal.Wave15b.colRed C u j < θ → ∑ i, P i j = b j) ∧
        (θ < StatFormal.Wave15b.colRed C u j → ∑ i, P i j = 0)) ∧
      (∀ i, 0 < ∑ j, P i j → ∑ j, P i j < a i → StatFormal.Wave15b.rowRed C z i = θ) ∧
      (∀ j, 0 < ∑ i, P i j → ∑ i, P i j < b j → StatFormal.Wave15b.colRed C u j = θ)

/-! ### TM `lem:rffkernel` (sup over the domain) and `thm:rffjoint` (premise discharged) -/

/-- `lem:rffkernel` as printed, the supremum over the compact domain: with i.i.d. features `(ω_j, b_j) ∼ Λ ⊗ Unif[0, 2π]`,
`σ_Λ² = E‖ω‖² < ∞`, `𝒳 ⊂ ℝ^d` compact and `δ ∈ (0, 1)`, with probability at least `1 − δ` (a measurable event)
`sup_{x,y∈𝒳} |z_r(x)ᵀz_r(y) − k(x, y)| ≤ ε_r(δ) = κ²[h + 2√(2 log(1/δ))]/√r`, `h = 4 + 12 diam(𝒳) σ_Λ`. -/
def rff_sup : Prop :=
  ∀ (d r : ℕ) (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (Λ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure Λ] (β : Measure ℝ) [IsProbabilityMeasure β]
    (W : Fin r → Ω → EuclideanSpace ℝ (Fin d)) (B : Fin r → Ω → ℝ) (κ δ : ℝ) (𝒳 : Set (EuclideanSpace ℝ (Fin d))),
    β = StatFormal.Wave24e.unifCircle → 0 < r → 0 < δ → δ < 1 → IsCompact 𝒳 →
    Integrable (fun ω => ‖ω‖ ^ 2) Λ → (∀ j, Measurable (W j)) → (∀ j, Measurable (B j)) →
    iIndepFun (fun j ω => (W j ω, B j ω)) Pr → (∀ j, Pr.map (fun ω => (W j ω, B j ω)) = Λ.prod β) →
      ∃ A : Set Ω, MeasurableSet A ∧ ENNReal.ofReal (1 - δ) ≤ Pr A ∧
        ∀ ω ∈ A, ∀ x ∈ 𝒳, ∀ y ∈ 𝒳,
          |StatFormal.Wave24e.rffKernel κ (fun j => W j ω) (fun j => B j ω) x y -
              StatFormal.Wave24e.bochnerKernel κ Λ x y| ≤
            rffEps κ (Metric.diam 𝒳) √(∫ ω, ‖ω‖ ^ 2 ∂Λ) r δ

/-- `thm:rffjoint` UNCONDITIONAL: the frozen Wave 17a `rffjoint` with its `lem:rffkernel` premise discharged by
`rff_sup` at `δ/3`. Laws `P, Q` on the compact `𝒳 ⊂ ℝ^d` (measures on the subtype), the kernel
`k = bochnerKernel` with an RKHS feature map `φ` (`⟨φx, φy⟩ = k(x, y)`, `‖φ‖ ≤ κ`), the phased features `z_r`
(`rffFeat`) of an i.i.d. draw on `Ω`: one measurable event of probability `≥ 1 − δ` jointly over the two samples
and the feature draw on which `|D̂^{(r)} − D| ≤ r_n(α,δ/3) + r_m(α,δ/3) + 2√ε_r(δ/3)` and
`|D̂^{(r)} − D̂| ≤ 4ε_r(δ/3)/(D̂^{(r)} + D̂)`. -/
def rffjoint_uncond : Prop :=
  ∀ (d r : ℕ) (𝒳 : Set (EuclideanSpace ℝ (Fin d))) (H Ω : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H] [MeasurableSpace Ω] (Pr : Measure Ω)
    [IsProbabilityMeasure Pr] (Λ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure Λ] (β : Measure ℝ)
    [IsProbabilityMeasure β] (W : Fin r → Ω → EuclideanSpace ℝ (Fin d)) (B : Fin r → Ω → ℝ)
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ α δ : ℝ) (n m : ℕ),
    β = StatFormal.Wave24e.unifCircle → 0 < r → IsCompact 𝒳 → Integrable (fun ω => ‖ω‖ ^ 2) Λ →
    (∀ j, Measurable (W j)) → (∀ j, Measurable (B j)) →
    iIndepFun (fun j ω => (W j ω, B j ω)) Pr → (∀ j, Pr.map (fun ω => (W j ω, B j ω)) = Λ.prod β) →
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 < κ →
    (∀ x y : 𝒳, ⟪φ x, φ y⟫ = StatFormal.Wave24e.bochnerKernel κ Λ x y) →
    0 ≤ α → α < 1 → 0 < δ → δ < 1 → 1 ≤ n → 1 ≤ m →
      ∃ E : Set ((Fin n → 𝒳) × (Fin m → 𝒳) × Ω), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤ ((Measure.pi fun _ : Fin n => P).prod
          ((Measure.pi fun _ : Fin m => Q).prod Pr)) E ∧
        ∀ s ∈ E,
          |StatFormal.TrimmedMMD.Unconditional.Demp
              (fun x : 𝒳 => rffFeat κ (fun j => W j s.2.2) (fun j => B j s.2.2) x) s.1 s.2.1 α -
              StatFormal.TrimmedMMD.Unconditional.Dpop φ P Q α| ≤
            StatFormal.TrimmedMMD.rn κ α (δ / 3) n + StatFormal.TrimmedMMD.rn κ α (δ / 3) m +
              2 * Real.sqrt (rffEps κ (Metric.diam 𝒳) √(∫ ω, ‖ω‖ ^ 2 ∂Λ) r (δ / 3)) ∧
          (0 < StatFormal.TrimmedMMD.Unconditional.Demp
              (fun x : 𝒳 => rffFeat κ (fun j => W j s.2.2) (fun j => B j s.2.2) x) s.1 s.2.1 α +
              StatFormal.TrimmedMMD.Unconditional.Demp φ s.1 s.2.1 α →
            |StatFormal.TrimmedMMD.Unconditional.Demp
                (fun x : 𝒳 => rffFeat κ (fun j => W j s.2.2) (fun j => B j s.2.2) x) s.1 s.2.1 α -
                StatFormal.TrimmedMMD.Unconditional.Demp φ s.1 s.2.1 α| ≤
              4 * rffEps κ (Metric.diam 𝒳) √(∫ ω, ‖ω‖ ^ 2 ∂Λ) r (δ / 3) /
                (StatFormal.TrimmedMMD.Unconditional.Demp
                  (fun x : 𝒳 => rffFeat κ (fun j => W j s.2.2) (fun j => B j s.2.2) x) s.1 s.2.1 α +
                  StatFormal.TrimmedMMD.Unconditional.Demp φ s.1 s.2.1 α))

/-! ### paper 2 `prop:jointmin`, `ε = 0` -/

/-- `prop:jointmin` at `ε = 0` (Wasserstein balls with the support constraint, the frozen Wave 6a `epBall` at `ε = 0`,
cost `c = d²` on a Polish metric space, any bounded measurable rule): every value of `Ψ⁰(λ, γ)` bounds
`R(h) + η F(h)`, `F(h) = sup_{Q_s ∈ 𝓑_s} W₂²(h#Q₀, h#Q₁)`. -/
def jointmin_upper0 : Prop :=
  ∀ (𝒦 : Type) [MetricSpace 𝒦] [MeasurableSpace 𝒦] [BorelSpace 𝒦] [SecondCountableTopology 𝒦] [CompleteSpace 𝒦]
    (n₀ n₁ : ℕ) (x₀ : Fin n₀ → 𝒦) (x₁ : Fin n₁ → 𝒦) (h : 𝒦 → ℝ) (r₀ r₁ Rh η lam₀ lam₁ : ℝ) (ν₀ ν₁ : Measure 𝒦)
    (γ : Fin n₀ → Fin n₁ → ℝ),
    0 < n₀ → 0 < n₁ → 0 ≤ Rh → 0 < η → 0 < lam₀ → 0 < lam₁ → Measurable h → (∃ H, ∀ z, |h z| ≤ H) →
    γ ∈ StatFormal.RobustEquality.Paper2.Alternating.Plans (fun _ => (1 : ℝ) / n₀) (fun _ => (1 : ℝ) / n₁) →
      ENNReal.ofReal Rh + ENNReal.ofReal η *
          StatFormal.Wave19b.worstDisp (StatFormal.Wave6a.epBall x₀ ν₀ 0 r₀) (StatFormal.Wave6a.epBall x₁ ν₁ 0 r₁) h ≤
        ENNReal.ofReal (jointObj0 x₀ x₁ h r₀ r₁ ν₀ ν₁ Rh η lam₀ lam₁ γ)

/-- `prop:jointmin` at `ε = 0`: the infimum of `Ψ⁰` over `(λ₀, λ₁, γ)` is the objective of `(P_η)` at `h`,
`inf_λ {R + η F̄⁰(h; λ)}` (same greatest lower bound, for every candidate value). Any measurable `h`: both sides
carry the same `T⁰_s` (for an unbounded `h` the `⨆` in `T0` is a junk value, shared by both sides). -/
def jointmin_inf0 : Prop :=
  ∀ (𝒦 : Type) [MetricSpace 𝒦] [MeasurableSpace 𝒦] (n₀ n₁ : ℕ) (x₀ : Fin n₀ → 𝒦) (x₁ : Fin n₁ → 𝒦) (h : 𝒦 → ℝ)
    (r₀ r₁ Rh η : ℝ) (ν₀ ν₁ : Measure 𝒦) (t : ℝ),
    0 < n₀ → 0 < n₁ → 0 < η → Measurable h →
      (IsGLB {v | ∃ lam₀ lam₁ γ, 0 < lam₀ ∧ 0 < lam₁ ∧
          γ ∈ StatFormal.RobustEquality.Paper2.Alternating.Plans (fun _ => (1 : ℝ) / n₀) (fun _ => (1 : ℝ) / n₁) ∧
          v = jointObj0 x₀ x₁ h r₀ r₁ ν₀ ν₁ Rh η lam₀ lam₁ γ} t ↔
        IsGLB {v | ∃ lam₀ lam₁, 0 < lam₀ ∧ 0 < lam₁ ∧ v = penObj0 x₀ x₁ h r₀ r₁ ν₀ ν₁ Rh η lam₀ lam₁} t)

/-! ### A `prop:lift-consistency`, the "Hence" sentence (finite ambient dimension `T`) -/

/-- `prop:lift-consistency`, "Hence along every schedule along which the computed sieve ranks converge in mean
square, so do their lifts", separable tails (`prop:lift-dual`(i)): for head maps `F̂_n = ι_{K_n}F̂_{K_n}` with
`E‖F̂_n(X) − F(X)‖² → 0`, the lifts satisfy `E‖F̂_n^{lift}(X) − F(X)‖² → 0` (no condition on `K_n`). -/
def lift_hence_sep : Prop :=
  ∀ (T : ℕ) (P μ : Measure (Fin T → ℝ)) [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    (F : (Fin T → ℝ) → Fin T → ℝ) (Kn : ℕ → ℕ) (Fh : ℕ → (Fin T → ℝ) → Fin T → ℝ) (t : ℕ → Fin T → ℝ → ℝ),
    Measurable F → P.map F = μ → (∀ n, Measurable (Fh n)) → (∀ n, StatFormal.Wave16a.IsHeadMap (Kn n) (Fh n)) →
    (∀ n, StatFormal.Wave16a.IsSepTail P μ (Kn n) (t n)) →
    Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (StatFormal.Wave16a.sqn (Fh n x - F x)) ∂P) atTop (𝓝 0) →
      Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (StatFormal.Wave16a.sqn
        (StatFormal.Wave16a.liftMap (Kn n) (Fh n) (t n) x - F x)) ∂P) atTop (𝓝 0)

/-- The same for diagonal quadratic tails (`prop:lift-dual`(ii)). -/
def lift_hence_quad : Prop :=
  ∀ (T : ℕ) (P μ : Measure (Fin T → ℝ)) [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    (F : (Fin T → ℝ) → Fin T → ℝ) (Kn : ℕ → ℕ) (Fh : ℕ → (Fin T → ℝ) → Fin T → ℝ),
    Measurable F → P.map F = μ → (∀ n, Measurable (Fh n)) → (∀ n, StatFormal.Wave16a.IsHeadMap (Kn n) (Fh n)) →
    (∀ n, ∀ k : Fin T, Kn n ≤ (k : ℕ) → Integrable (fun x => x k ^ 2) P ∧ 0 < StatFormal.Wave16a.varK P k ∧
      Integrable (fun u => u k ^ 2) μ) →
    Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (StatFormal.Wave16a.sqn (Fh n x - F x)) ∂P) atTop (𝓝 0) →
      Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (StatFormal.Wave16a.sqn
        (StatFormal.Wave16a.liftMap (Kn n) (Fh n) (StatFormal.Wave16a.quadTail P μ) x - F x)) ∂P) atTop (𝓝 0)

/-! ### A `prop:selector` (ii) and its `s_n`-remark; `prop:parsimony` (the selector (ii) dependence) -/

/-- `prop:selector` (ii) with the remark after the proposition: training-fold candidates `F̂_{n,θ}(ω)`, `θ ∈ Θ_n`
finite, jointly measurable and `P_K`-a.e. gradients of convex functions; independent validation draws
`Z_i ∼ P_K`, `U_j ∼ μ_K` (the joint law `P_t ⊗ P_K^{n_v} ⊗ μ_K^{m_v}`); `log|Θ_n| = o(min(n_v, m_v))`; `Θ_n ∋ θ*_n`
with `F̂_{θ*_n} → F_K` in `P_K`-probability, in probability over the training fold. Then for every `θ̂` with
`D̂(θ̂) ≤ min_{Θ_n} D̂ + s_n`, `s_n ≥ 0`, `s_n → 0` in probability (`s_n = 0`: the minimiser of the printed (ii)),
`D(θ̂) = ED(Υ#F̂_θ̂#P_K, Υ#μ_K) → 0` and `F̂_θ̂ → F_K` in `P_K`-probability, in probability. Hypotheses of the
frozen `lem:T-stability` (WaveL2 `t_stability_delta`): `Υ` from a gauge `g` with `ass:scale`, `P_K ≪ Leb`, second
moments, `F_K` a convex gradient pushing `P_K` to `μ_K`; `‖Υ‖ ≤ R`. DEVIATION: `P_K ≪ Leb` (for `𝒫^ℓ`) and the
second moments of `P_K`, `μ_K` are extra hypotheses (the printed remark needs no moment). Probabilities of events that
need not be measurable (`θ̂` is any selection) are outer measures. -/
def selector_ii : Prop :=
  ∀ (K : ℕ) (P μ : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    (g : EuclideanSpace ℝ (Fin K) → ℝ) (F : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (R : ℝ)
    (Ωt : Type) [MeasurableSpace Ωt] (Pt : Measure Ωt) [IsProbabilityMeasure Pt] (nv mv : ℕ → ℕ)
    (Θ : ℕ → Type) [∀ n, Fintype (Θ n)] [∀ n, Nonempty (Θ n)]
    (Fh : (n : ℕ) → Θ n → Ωt → EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (θs : (n : ℕ) → Ωt → Θ n)
    (θh : (n : ℕ) → Ωt × ((Fin (nv n) → EuclideanSpace ℝ (Fin K)) × (Fin (mv n) → EuclideanSpace ℝ (Fin K))) → Θ n)
    (s : (n : ℕ) → Ωt × ((Fin (nv n) → EuclideanSpace ℝ (Fin K)) × (Fin (mv n) → EuclideanSpace ℝ (Fin K))) → ℝ),
    StatFormal.OTFD.Scale.IsGauge g → StatFormal.OTFD.Scale.ScaleHyp μ g → MemLp id 2 μ → P ≪ volume →
    MemLp id 2 P → Measurable F → P.map F = μ → StatFormal.OTFD.Wave22a.IsConvGradAE P F →
    (∀ r, ‖StatFormal.OTFD.Scale.ups μ g r‖ ≤ R) →
    (∀ n θ, Measurable (Function.uncurry (Fh n θ))) → (∀ n θ ω, StatFormal.OTFD.Wave22a.IsConvGradAE P (Fh n θ ω)) →
    (∀ n, 1 ≤ nv n) → (∀ n, 1 ≤ mv n) →
    Tendsto (fun n => Real.log (Fintype.card (Θ n)) / (min (nv n) (mv n) : ℕ)) atTop (𝓝 0) →
    (∀ η : ℝ, 0 < η → Tendsto (fun n => Pt {ω | ENNReal.ofReal η < P {x | η < ‖Fh n (θs n ω) ω x - F x‖}})
      atTop (𝓝 0)) →
    (∀ n w, 0 ≤ s n w) →
    (∀ η : ℝ, 0 < η → Tendsto (fun n => (Pt.prod ((Measure.pi fun _ : Fin (nv n) => P).prod
      (Measure.pi fun _ : Fin (mv n) => μ))) {w | η < s n w}) atTop (𝓝 0)) →
    (∀ n w θ, StatFormal.OTFD.Wave1.edStat (fun i => StatFormal.OTFD.Scale.ups μ g (Fh n (θh n w) w.1 (w.2.1 i)))
        (fun j => StatFormal.OTFD.Scale.ups μ g (w.2.2 j)) ≤
      StatFormal.OTFD.Wave1.edStat (fun i => StatFormal.OTFD.Scale.ups μ g (Fh n θ w.1 (w.2.1 i)))
        (fun j => StatFormal.OTFD.Scale.ups μ g (w.2.2 j)) + s n w) →
      (∀ η : ℝ, 0 < η → Tendsto (fun n => (Pt.prod ((Measure.pi fun _ : Fin (nv n) => P).prod
          (Measure.pi fun _ : Fin (mv n) => μ))) {w | η < StatFormal.OTFD.Wave22a.energyD
            ((P.map (Fh n ((θh n w)) w.1)).map (StatFormal.OTFD.Scale.ups μ g)) (μ.map (StatFormal.OTFD.Scale.ups μ g))})
        atTop (𝓝 0)) ∧
      (∀ η : ℝ, 0 < η → Tendsto (fun n => (Pt.prod ((Measure.pi fun _ : Fin (nv n) => P).prod
          (Measure.pi fun _ : Fin (mv n) => μ))) {w | ENNReal.ofReal η < P {x | η < ‖Fh n ((θh n w)) w.1 x - F x‖}})
        atTop (𝓝 0))

/-- `prop:parsimony`, "The conclusions of `prop:selector`(ii) hold for `θ̃`": `Θ_n` ordered by complexity (a linear
order), `θ̃` the first candidate with `D̂(θ̃) ≤ min D̂ + s_n` (`parsSel`), `s_n ≥ 0`, `s_n → 0` in probability; the
setting and the DEVIATIONS (`P_K ≪ Leb`, second moments) of `selector_ii`. -/
def parsimony_ii : Prop :=
  ∀ (K : ℕ) (P μ : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    (g : EuclideanSpace ℝ (Fin K) → ℝ) (F : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (R : ℝ)
    (Ωt : Type) [MeasurableSpace Ωt] (Pt : Measure Ωt) [IsProbabilityMeasure Pt] (nv mv : ℕ → ℕ)
    (Θ : ℕ → Type) [∀ n, Fintype (Θ n)] [∀ n, Nonempty (Θ n)] [∀ n, LinearOrder (Θ n)]
    (Fh : (n : ℕ) → Θ n → Ωt → EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (θs : (n : ℕ) → Ωt → Θ n)
    (s : (n : ℕ) → Ωt × ((Fin (nv n) → EuclideanSpace ℝ (Fin K)) × (Fin (mv n) → EuclideanSpace ℝ (Fin K))) → ℝ),
    StatFormal.OTFD.Scale.IsGauge g → StatFormal.OTFD.Scale.ScaleHyp μ g → MemLp id 2 μ → P ≪ volume →
    MemLp id 2 P → Measurable F → P.map F = μ → StatFormal.OTFD.Wave22a.IsConvGradAE P F →
    (∀ r, ‖StatFormal.OTFD.Scale.ups μ g r‖ ≤ R) →
    (∀ n θ, Measurable (Function.uncurry (Fh n θ))) → (∀ n θ ω, StatFormal.OTFD.Wave22a.IsConvGradAE P (Fh n θ ω)) →
    (∀ n, 1 ≤ nv n) → (∀ n, 1 ≤ mv n) →
    Tendsto (fun n => Real.log (Fintype.card (Θ n)) / (min (nv n) (mv n) : ℕ)) atTop (𝓝 0) →
    (∀ η : ℝ, 0 < η → Tendsto (fun n => Pt {ω | ENNReal.ofReal η < P {x | η < ‖Fh n (θs n ω) ω x - F x‖}})
      atTop (𝓝 0)) →
    (∀ n w, 0 ≤ s n w) →
    (∀ η : ℝ, 0 < η → Tendsto (fun n => (Pt.prod ((Measure.pi fun _ : Fin (nv n) => P).prod
      (Measure.pi fun _ : Fin (mv n) => μ))) {w | η < s n w}) atTop (𝓝 0)) →
      (∀ η : ℝ, 0 < η → Tendsto (fun n => (Pt.prod ((Measure.pi fun _ : Fin (nv n) => P).prod
          (Measure.pi fun _ : Fin (mv n) => μ))) {w | η < StatFormal.OTFD.Wave22a.energyD
            ((P.map (Fh n ((parsSel (fun θ => StatFormal.OTFD.Wave1.edStat (fun i => StatFormal.OTFD.Scale.ups μ g (Fh n θ w.1 (w.2.1 i))) (fun j => StatFormal.OTFD.Scale.ups μ g (w.2.2 j))) (s n w))) w.1)).map (StatFormal.OTFD.Scale.ups μ g)) (μ.map (StatFormal.OTFD.Scale.ups μ g))})
        atTop (𝓝 0)) ∧
      (∀ η : ℝ, 0 < η → Tendsto (fun n => (Pt.prod ((Measure.pi fun _ : Fin (nv n) => P).prod
          (Measure.pi fun _ : Fin (mv n) => μ))) {w | ENNReal.ofReal η < P {x | η < ‖Fh n ((parsSel (fun θ => StatFormal.OTFD.Wave1.edStat (fun i => StatFormal.OTFD.Scale.ups μ g (Fh n θ w.1 (w.2.1 i))) (fun j => StatFormal.OTFD.Scale.ups μ g (w.2.2 j))) (s n w))) w.1 x - F x‖}})
        atTop (𝓝 0))

end Claims

end StatFormal.WaveP2d
