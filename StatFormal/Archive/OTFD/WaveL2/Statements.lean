import StatFormal.Archive.OTFD.Wave22a.Statements
import StatFormal.Archive.OTFD.Wave5a.Statements
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Probability.Independence.Basic

/-!
# FROZEN STATEMENTS — otfd wave L2: limit and consistency clauses of A `thm:rt-fixedK`, `thm:rt-coherent` (last
# clause), `prop:rt-randomized`(c),(d), `prop:rt-lift`(ii), `lem:T-stability`, `prop:rt-adaptive`(ii); energy-distance
# identifiability in `ℝ^K`

Sources (verbatim in `lean-formalisation/inventory/extracted/otfd-A_sieves.md`; current text of
`otfd/papers/A_sieves/`):
* `thm:rt-coherent` (`main.tex:1479-1491`), last clause ("every fixed-`K` test with `K ≥ K_1` is consistent").
* `thm:rt-fixedK` (`main.tex:1461-1471`), with the setting paragraph (`main.tex:1378-1402`: pooled ranks
  `R_i = u_{σ̂(i)}`, the rank-energy statistic `𝖤_N`, `Λ = θP + (1−θ)Q`, `F^Λ_K`, `𝓔_K = 𝒟(ν^P_K, ν^Q_K)`, "the energy
  distance `𝒟` is nonnegative and vanishes only for equal laws, in `ℝ^K` …") and `def:sieve-rank-test`
  (`main.tex:1404-1414`: `c_{N,α}` the `(1−α)`-quantile of `T(u_{π(1)}, …, u_{π(N)})`, `π` uniform).
* `prop:rt-randomized`(c),(d) (`supplement.tex:5471-5503`): "every consistency statement for `R`
  (`thm:rt-fixedK`, …) applies to `R̃`".
* `prop:rt-lift`(ii) (`supplement.tex:5558-5570`): "their energy distance is positive for every such alternative".
* `lem:T-stability` (`main.tex:1229-1235`), the `δ–η` clause and the "in particular" with `ED = 0`.
* `prop:rt-adaptive`(ii) (`supplement.tex:5743-5755`), consistency, with its proof (`:5757-5768`).
Imports the frozen `OTFD/Wave22a` statements (`mix`, `energyD`, `IsConvGradAE`, `headT`, `liftMap`, `pFull`,
`pAdFull`; through them the frozen `OTFD/Wave10a`, `OTFD/Scale` (`IsGauge`, `ScaleHyp`, `ups`), `OTFD/Wave1`
(`truncK`), `OTFD/Ranks` (`IsMin`)) and `OTFD/Wave5a` (`rtSigma`), not copied. Mathlib otherwise. The library
notions used by the routes (Varadarajan, the library `energyDist`, plan stability) are not imported here; the energy
distance is the frozen `energyD`.

Covered:
* Energy distance on a finite-dimensional real inner product space (`ℝ^K`): `ed_nonneg`, `ed_eq_zero_iff`
  (`𝒟 ≥ 0`, `𝒟(ν, ν') = 0 ⇔ ν = ν'`, finite first moments).
* `thm:rt-fixedK`: `rt_fixedK_sep` (`𝓔_K > 0 ⇔ P_K ≠ Q_K`, with the a.e. invertibility of `F^Λ_K` now *derived*
  from Brenier–McCann instead of assumed as in the frozen `rt_fixedK_laws`), `rt_fixedK_crit` (`c_{N,α} → 0`),
  `rt_fixedK_limit` (`𝖤_N → 𝓔_K` almost surely, for every sequence of optimal assignments), `rt_fixedK_consistent`
  (power `→ 1` for every `α ∈ (0,1)` against every alternative `P_K ≠ Q_K`).
* `thm:rt-coherent`, last clause: `rt_coherent_consistent` (the fixed-`K` test is consistent against every alternative
  with `𝓔_K(P, Q) > 0`; for `K ≥ K_1` this is supplied by the frozen `rt_coherent_eventually`, `𝓔_K ≥ 𝓔_∞/2`, once
  `𝓔_∞ > 0`).
* `prop:rt-randomized`(c),(d): `rt_randomized_limit` (the randomized ranks `R̃` satisfy `𝖤_N → 𝓔_K` a.s., for any
  shuffles `τ`, without the uniqueness/equivariance of (c)).
* `prop:rt-lift`(ii): `rt_lift_sep` (the lifted rank laws have positive energy distance iff `P_T ≠ Q_T`).
* `lem:T-stability`: `t_stability_ed` (the "in particular" as printed, `ED = 0 ⇒ G = F_K` a.e.),
  `t_stability_delta` (the `δ–η` clause).
* `prop:rt-adaptive`(ii): `rt_adaptive_consistent` (full permutation distribution: `P(p^ad ≤ α) → 1` against every
  alternative visible at some level).

Not covered (declared):
* `thm:rt-coherent`: `S_Λ(K) → 0` for the cubic/ball laws (`prop:integrated-sieve-strong` for `Λ`) and `𝓔_∞ > 0`
  (energy-distance identifiability in an infinite-dimensional separable Hilbert space, Lyons 2013, and the a.e.
  injectivity of `𝔽_Λ`; the library has identifiability in finite dimension only). The consistency for `K ≥ K_1` is
  therefore covered only conditionally on `𝓔_K > 0` (`rt_coherent_consistent`). The bridge from the frozen
  `rt_coherent_eventually` (where `𝓔_K = energyD (P.map (ι_K ∘ F^Λ_K ∘ Π_K)) (Q.map …)`, laws on `H`) to the `ℝ^K` form
  used here (`energyD ((P.map Π_K).map F^Λ_K) …`; `Measure.map_map` and isometry invariance of `𝒟`) is not a claim.
* `thm:rt-fixedK`: the hypotheses `P, Q ∈ 𝒫^ℓ(H)` and `μ_K ∈ 𝒫^ℓ(ℝ^K)` are replaced by absolute continuity of
  `Λ_K` and of `μ_K` (Tau Ceti's Brenier theorem needs `≪` Haar; `𝒫^ℓ` (Lipschitz hypersurfaces null) is weaker).
  (Restriction: `≪ Leb` is strictly stronger than `𝒫^ℓ(ℝ^K)`, e.g. singular atomless laws for `K = 1`; and
  `P, Q ∈ 𝒫^ℓ(H)` does not give `Λ_K ≪ Leb`.) `μ_K ≪ Leb` is used only for `𝓔_K > 0 ⇐ P_K ≠ Q_K` (`rt_fixedK_sep`,
  `rt_fixedK_consistent`), not for the limit or the critical value.
* `thm:rt-fixedK` grids — no restriction: the paper's `𝒰_{K,N} ⊆ supp μ_K` (bounded) and `W_2(μ_{K,N}, μ_K) → 0` imply
  the encoding's `‖u_i‖ ≤ R` and weak convergence of `μ_{K,N}` (and are equivalent to them for grids in a fixed
  ball), so `grid_bdd`, `grid_lim` are weaker than printed (generalisation; `μ_K` is then supported in `B̄(0,R)`,
  bounded support is not a separate hypothesis; distinct grid points and `𝒰_{K,N} ⊆ supp μ_K` are not needed).
* `prop:rt-lift`(ii): the injectivity of the population tail maps (positive densities on intervals) and of the head
  map remain hypotheses, as in the frozen `rt_lift_laws` (conditional). Integrability of the lifted map under `P_T`,
  `Q_T` is added (the condition for `𝒟` to be finite, implicit in the paper; automatic for bounded tail maps).
* `prop:rt-randomized`(c),(d): only the limit `𝖤_N(R̃) → 𝓔_K` is stated; the consistency of the `R̃`-test (power
  `→ 1`, rejection event measurable for measurable `τ`) is a short corollary of `rt_randomized_limit`,
  `rt_fixedK_crit`, `rt_fixedK_sep` (the critical value depends on the grid only) but is not a claim.
* `prop:rt-adaptive`(ii): the levels, bases and grids are fixed (data-dependent levels are not treated).
* `lem:T-stability`: `P_K ∈ 𝒫^ℓ(ℝ^K)` without moments; the frozen encoding (`P_K ≪` Haar, finite second moments,
  finite potentials `IsConvGradAE`) is kept (Tau Ceti's Brenier uniqueness needs a finite optimal cost; McCann's
  moment-free uniqueness is missing). Restrictions: `MemLp id 2 μ_K` excludes the heavy-tailed references that
  motivate the probability scale (`main.tex:1222`); with an unbounded reference, `IsConvGradAE P F` (finite
  potential) can fail for the true `F_K` (vacuous instance), and in the `δ–η` clause the competitors `G` are only
  those with everywhere-finite potentials (fewer `G` than printed).
* `prop:rt-randomized`(c): the a.s. identity `σ̃ = 𝔯(𝔛)` under equivariance (not needed: (d) already makes `σ̃` optimal,
  which suffices for the limit).

Encodings (to be checked by the critic):
* `ℝ^K = EuclideanSpace ℝ (Fin K)` (`M_K = I`), `volume` its Lebesgue measure. In the fixed-`K` claims the laws `P`,
  `Q` on `ℝ^K` are the projected laws `P_K`, `Q_K` (the claims hold for any laws on `ℝ^K`; with a fixed basis,
  `Z_i = Π_KX_i` are iid `P_K`), `Z i`, `W j` the projected curves of the two groups (two iid sequences, `iIndepFun`;
  no independence *between* the groups is needed). At stage `ν` the sizes are `n₁ ν, n₂ ν` with
  `n₁ + n₂ → ∞`, `n₁/(n₁ + n₂) → θ ∈ (0,1)`; the pooled sample is `pool` (`Fin.append`, group `P` first);
  the grid is `u ν : Fin (n₁+n₂) → ℝ^K`, all points in the closed ball of radius `R` (`𝒰_{K,N} ⊆ supp μ_K`, bounded),
  with `N⁻¹ Σ_i f(u_i) → ∫ f dμ_K` for every bounded continuous `f` (weak convergence; implied by `W_2 → 0`).
  Distinct grid points are not needed.
* `F^Λ_K` is any measurable `F` with `F#Λ_K = μ_K` that is `Λ_K`-a.e. the gradient of an everywhere-finite convex
  function (frozen `IsConvGradAE`; with a bounded reference the Brenier potential is finite and Lipschitz, so no
  restriction); `Λ_K = mix θ P Q` (frozen). Moments: `MemLp id 2` for `P_K`, `Q_K` (`𝒫^ℓ` has them).
* Hard assignment: any `σ` with the frozen `IsMin u z σ` (`Σ_i ‖z_i − u_{σ(i)}‖²` minimal), `R_i = u_{σ(i)}`, i.e. the
  rank vector `u ∘ σ`. `rt_fixedK_limit` quantifies over **every** sequence of optimal assignments, pathwise on one
  `Pr`-full event (a.s. convergence; stronger than the printed "in probability", and no measurable selection needed).
* `𝖤_N = rankEnergy n₁ n₂ (u ∘ σ)`, the displayed formula with group `P` the first `n₁` indices (`Fin.castAdd`) and
  group `Q` the last `n₂` (`Fin.natAdd`); `1/0 = 0` at `n₁ = 0` or `n₂ = 0` only, irrelevant for limits.
  `𝓔_K = energyD (P.map F) (Q.map F)` (frozen iterated Bochner integrals; the integrands are integrable in every claim).
* `c_{N,α} = critVal T y α = inf{c : #{π : c < T(y∘π)} ≤ α N!}`, the `(1−α)`-quantile of `T(y ∘ π)` under uniform
  `π`; for `0 < α < 1` the set is nonempty (large `c`) and bounded below (`c < min_π T(y∘π)` violates it), so the
  infimum is genuine. The test rejects when `c_{N,α} < 𝖤_N` (non-randomized, as in `def:sieve-rank-test`).
* Consistency: for a measurable selection rule `sel ν` of optimal assignments (fibres measurable, as in the frozen
  `fixedK_rank_law`) the rejection event is measurable and its probability tends to `1`. `rt_coherent_consistent`
  replaces `μ_K ≪ Leb`, `P_K ≠ Q_K` by `0 < 𝓔_K(P, Q)` (the form produced by `rt_coherent_eventually`).
* Randomized ranks: `R̃ = u ∘ σ̃`, `σ̃ = rtSigma r z τ = 𝔯(z∘τ)∘τ⁻¹` (frozen Wave 5a) for an optimal rule `r` on the
  (reordering-invariant) projected coefficients; `τ ν ω` arbitrary.
* rt-lift: the hypotheses of the frozen `rt_lift_laws` plus integrability of the lifted map under `P_T`, `Q_T`.
* T-stability: the frozen `t_stability_eq` hypotheses; `ED(Υ#G#P_K, Υ#μ_K)` is `energyD ((P.map G).map Υ) (μ.map Υ)`
  (`Υ = ups μ g` takes values in `{g ≤ 1}`, bounded, so no integrability junk). `δ–η`: for every `η > 0` some
  `δ > 0` works for every measurable `G` that is `P_K`-a.e. the gradient of a finite convex function;
  `P_K{‖G − F_K‖ > η} < η` with `η` cast by `ENNReal.ofReal`.
* rt-adaptive: curves in a real inner product space `H` (Borel), fixed orthonormal-type system `e`, levels
  `l : Fin (L+1)` with `K l` and the projections `truncK e (K l)` (frozen); the pooled level-`l` ranks of curve `i` are
  `u l ν (sel l ν (z_l) i)`; the data vector of `pAdFull` (frozen) is the vector of all levels' ranks of curve `i`, the
  level-`l` statistic is `rankEnergy` of the level-`l` component, so `pFull T x l σ` is `p_l(σ)` with the full
  permutation distribution (ranks computed once on the pooled sample, relabelled by `σ`). The fixed-`K` assumptions are
  required at one level `l₀` with `P_{K_{l₀}} ≠ Q_{K_{l₀}}` only (generalisation of "at each level").

Critic notes:
* All 12 claims are proved in `WaveL2/Route{ED,CM,Crit,Limit,FixedK,Stab}.lean` (axioms: propext, Classical.choice,
  Quot.sound). Routes use the untrusted libraries `Foundations/Empirical` (Varadarajan a.s. weak convergence,
  `energyDist` nonnegativity/identifiability), `Foundations/OTLimits` (Villani 5.20 `tendsto_of_forall_isOptimalCoupling_eq`,
  `isCyclicallyMonotone_support_of_tendsto`, `tendsto_measure_edist_ge_of_tendsto_graphPlan`), Tau Ceti
  (Schachermayer–Teichmann, Brenier uniqueness, Prokhorov for couplings, Rockafellar), Mathlib (Prokhorov,
  portmanteau, `continuous_prod`), and the frozen-route Wave 22a theorems `rt_fixedK_laws`, `rt_lift_laws`,
  `t_stability_eq`, `t_stability_push`, `rt_adaptive_bound` — routes only.
* Proof structure of `rt_fixedK_limit`: label the pooled points by group (`ℝ^K × Bool`); the plan of an optimal
  assignment is cyclically monotone (finite permutation argument, `RouteCM`), hence optimal between the labelled
  empirical law and the grid law; the labelled limit problem `(θP⊗δ₁ + (1−θ)Q⊗δ₀, μ_K)` has the unique optimal plan
  `(id, F ∘ fst)#Λ̃`, so the plans converge (Villani 5.20); `𝖤_N` is a combination of integrals of bounded continuous
  kernels against the product of the plan with itself (`‖F‖ ≤ R` `Λ`-a.e. by the portmanteau theorem).
* `c_{N,α} ≤ 2R(1/n₁ + 1/n₂)/α` (route `critVal_bounds`: the permutation mean of `𝖤` is `R`-bounded times
  `1/n₁ + 1/n₂`, Markov), so `c_{N,α} → 0` holds for any bounded grids, not only `W_2`-convergent ones.
* No tautology: every conclusion (a limit, a positivity, an implication from a vanishing or small energy distance) is
  absent from the hypotheses; `FixedKSetting` is satisfiable (Brenier–McCann gives `F`; e.g. uniform grids).
* Strengthenings found: `𝖤_N → 𝓔_K` holds almost surely (not only in probability), simultaneously for every sequence
  of optimal assignments (ties broken arbitrarily, no measurable selection); the grids need not consist of distinct
  points; `prop:rt-randomized`(d) alone carries the consistency to `R̃` for arbitrary shuffles (the equivariance of
  (c) is not needed).
* No statement was found false.
* Critic (2026-10-15): all 12 TRUE (routes build), none tautological. Fixed: `rt_coherent_consistent` now also
  concludes measurability of the rejection events (as `rt_fixedK_consistent`; without it `Pr` is an outer measure
  and the conclusion is weaker). Documented: the grid hypotheses are a generalisation of `W_2` convergence;
  `≪ Leb` (for `𝒫^ℓ`) and `MemLp id 2 μ_K` (T-stability) are restrictions; `rt_coherent_consistent` and `rt_lift_sep`
  are conditional (`𝓔_K > 0`, injectivity); `rt_randomized_limit` covers the limit only. `rankEnergy`, `critVal`,
  `pool`, `FixedKSetting` are new (no frozen `𝖤_N`, `c_{N,α}` exists); `𝓔_K`, `Λ`, rank laws use the frozen
  `energyD`, `mix`, `IsConvGradAE`; assignments the frozen `IsMin`; `p^ad` the frozen `pAdFull`.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/
set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace BoundedContinuousFunction

namespace StatFormal.OTFD.WaveL2

open StatFormal.OTFD.Scale (IsGauge ScaleHyp ups)
open StatFormal.OTFD.Wave1 (truncK)
open StatFormal.OTFD.Ranks (IsMin)
open StatFormal.OTFD.Wave5a (rtSigma)
open StatFormal.OTFD.Wave22a (mix energyD IsConvGradAE headT liftMap pFull pAdFull)

local notation "𝔼" K => EuclideanSpace ℝ (Fin K)

/-- The pooled sample `(Z_1, …, Z_{n₁}, W_1, …, W_{n₂})`, group `P` first. -/
def pool {Ω E : Type*} (n₁ n₂ : ℕ) (Z W : ℕ → Ω → E) (ω : Ω) : Fin (n₁ + n₂) → E :=
  Fin.append (fun i : Fin n₁ => Z i ω) (fun j : Fin n₂ => W j ω)

/-- The rank-energy statistic `𝖤_N = 2/(n₁n₂) Σ_{i≤n₁<j} ‖R_i − R_j‖ − n₁⁻² Σ_{i,i'≤n₁} ‖R_i − R_{i'}‖
− n₂⁻² Σ_{j,j'>n₁} ‖R_j − R_{j'}‖` of a labelled vector `R`. -/
def rankEnergy {E : Type*} [NormedAddCommGroup E] (n₁ n₂ : ℕ) (y : Fin (n₁ + n₂) → E) : ℝ :=
  2 / ((n₁ : ℝ) * n₂) * ∑ i : Fin n₁, ∑ j : Fin n₂, ‖y (Fin.castAdd n₂ i) - y (Fin.natAdd n₁ j)‖ -
    1 / (n₁ : ℝ) ^ 2 * ∑ i : Fin n₁, ∑ i' : Fin n₁, ‖y (Fin.castAdd n₂ i) - y (Fin.castAdd n₂ i')‖ -
    1 / (n₂ : ℝ) ^ 2 * ∑ j : Fin n₂, ∑ j' : Fin n₂, ‖y (Fin.natAdd n₁ j) - y (Fin.natAdd n₁ j')‖

open scoped Classical in
/-- The permutation critical value `c_{N,α} = inf{c : #{π : T(y∘π) > c} ≤ α N!}`, the `(1−α)`-quantile of
`T(y∘π)` for uniform `π`. -/
def critVal {Y : Type*} {N : ℕ} (T : (Fin N → Y) → ℝ) (y : Fin N → Y) (α : ℝ) : ℝ :=
  sInf {c : ℝ | ((Finset.univ.filter fun π : Equiv.Perm (Fin N) => c < T (y ∘ ⇑π)).card : ℝ) ≤
    α * (Nat.factorial N : ℝ)}

/-- The standing assumptions of `thm:rt-fixedK` at one level `K`, along a sequence of sample sizes. -/
structure FixedKSetting (K : ℕ) {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω)
    (P Q μ : Measure (𝔼 K)) (θ R : ℝ) (F : (𝔼 K) → 𝔼 K) (Z W : ℕ → Ω → 𝔼 K) (n₁ n₂ : ℕ → ℕ)
    (u : ∀ ν, Fin (n₁ ν + n₂ ν) → 𝔼 K) : Prop where
  theta_pos : 0 < θ
  theta_lt_one : θ < 1
  sizes : Tendsto (fun ν => n₁ ν + n₂ ν) atTop atTop
  ratio : Tendsto (fun ν => (n₁ ν : ℝ) / (n₁ ν + n₂ ν)) atTop (𝓝 θ)
  mom_P : MemLp id 2 P
  mom_Q : MemLp id 2 Q
  ac : mix θ P Q ≪ volume
  meas_F : Measurable F
  push : (mix θ P Q).map F = μ
  grad : IsConvGradAE (mix θ P Q) F
  meas_Z : ∀ i, Measurable (Z i)
  meas_W : ∀ j, Measurable (W j)
  indep_Z : iIndepFun Z Pr
  indep_W : iIndepFun W Pr
  law_Z : ∀ i, Pr.map (Z i) = P
  law_W : ∀ j, Pr.map (W j) = Q
  grid_bdd : ∀ ν i, ‖u ν i‖ ≤ R
  grid_lim : ∀ f : (𝔼 K) →ᵇ ℝ,
    Tendsto (fun ν => ((n₁ ν + n₂ ν : ℕ) : ℝ)⁻¹ * ∑ i, f (u ν i)) atTop (𝓝 (∫ x, f x ∂μ))

namespace Claims

/-! #### Energy distance in finite dimension -/

/-- `𝒟(ν, ν') ≥ 0` for laws with finite first moments on a finite-dimensional real inner product space. -/
def ed_nonneg : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (ν ν' : Measure E) [IsProbabilityMeasure ν] [IsProbabilityMeasure ν'],
    Integrable id ν → Integrable id ν' → 0 ≤ energyD ν ν'

/-- `𝒟(ν, ν') = 0` only for equal laws (finite first moments, finite dimension). -/
def ed_eq_zero_iff : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (ν ν' : Measure E) [IsProbabilityMeasure ν] [IsProbabilityMeasure ν'],
    Integrable id ν → Integrable id ν' → (energyD ν ν' = 0 ↔ ν = ν')

/-! #### `thm:rt-fixedK` -/

/-- `𝓔_K(P, Q) > 0` iff `P_K ≠ Q_K`, for the Brenier map `F^Λ_K` of `Λ_K ≪ Leb` onto `μ_K ≪ Leb`. -/
def rt_fixedK_sep : Prop :=
  ∀ (K : ℕ) (P Q μ : Measure (𝔼 K)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure μ]
    (θ : ℝ) (F : (𝔼 K) → 𝔼 K),
    0 < θ → θ < 1 → MemLp id 2 P → MemLp id 2 Q → MemLp id 2 μ → mix θ P Q ≪ volume → μ ≪ volume →
    Measurable F → (mix θ P Q).map F = μ → IsConvGradAE (mix θ P Q) F →
      (0 < energyD (P.map F) (Q.map F) ↔ P ≠ Q)

/-- `c_{N,α} → 0` for the rank-energy statistic on bounded grids, `n₁, n₂ → ∞`, `0 < α < 1`. -/
def rt_fixedK_crit : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (n₁ n₂ : ℕ → ℕ)
    (u : ∀ ν, Fin (n₁ ν + n₂ ν) → E) (R α : ℝ),
    0 < α → α < 1 → Tendsto n₁ atTop atTop → Tendsto n₂ atTop atTop → (∀ ν i, ‖u ν i‖ ≤ R) →
      Tendsto (fun ν => critVal (rankEnergy (n₁ ν) (n₂ ν)) (u ν) α) atTop (𝓝 0)

/-- `𝖤_N → 𝓔_K(P, Q)` almost surely, simultaneously for every sequence of optimal assignments of the pooled
sample to the grids. -/
def rt_fixedK_limit : Prop :=
  ∀ (K : ℕ) (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (P Q μ : Measure (𝔼 K))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure μ] (θ R : ℝ) (F : (𝔼 K) → 𝔼 K)
    (Z W : ℕ → Ω → 𝔼 K) (n₁ n₂ : ℕ → ℕ) (u : ∀ ν, Fin (n₁ ν + n₂ ν) → 𝔼 K),
    FixedKSetting K Pr P Q μ θ R F Z W n₁ n₂ u →
      ∀ᵐ ω ∂Pr, ∀ σ : ∀ ν, Equiv.Perm (Fin (n₁ ν + n₂ ν)),
        (∀ ν, IsMin (u ν) (pool (n₁ ν) (n₂ ν) Z W ω) (σ ν)) →
          Tendsto (fun ν => rankEnergy (n₁ ν) (n₂ ν) (u ν ∘ ⇑(σ ν))) atTop
            (𝓝 (energyD (P.map F) (Q.map F)))

/-- Consistency: for every `α ∈ (0,1)` and every alternative `P_K ≠ Q_K`, the rank-energy test that rejects when
`𝖤_N > c_{N,α}` has power tending to `1` (measurable selection of optimal assignments; measurable event). -/
def rt_fixedK_consistent : Prop :=
  ∀ (K : ℕ) (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (P Q μ : Measure (𝔼 K))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure μ] (θ R : ℝ) (F : (𝔼 K) → 𝔼 K)
    (Z W : ℕ → Ω → 𝔼 K) (n₁ n₂ : ℕ → ℕ) (u : ∀ ν, Fin (n₁ ν + n₂ ν) → 𝔼 K)
    (sel : ∀ ν, (Fin (n₁ ν + n₂ ν) → 𝔼 K) → Equiv.Perm (Fin (n₁ ν + n₂ ν))) (α : ℝ),
    FixedKSetting K Pr P Q μ θ R F Z W n₁ n₂ u → μ ≪ volume → P ≠ Q → 0 < α → α < 1 →
    (∀ ν z, IsMin (u ν) z (sel ν z)) → (∀ ν h, MeasurableSet {z | sel ν z = h}) →
      (∀ ν, MeasurableSet {ω | critVal (rankEnergy (n₁ ν) (n₂ ν)) (u ν) α <
        rankEnergy (n₁ ν) (n₂ ν) (u ν ∘ ⇑(sel ν (pool (n₁ ν) (n₂ ν) Z W ω)))}) ∧
      Tendsto (fun ν => Pr {ω | critVal (rankEnergy (n₁ ν) (n₂ ν)) (u ν) α <
        rankEnergy (n₁ ν) (n₂ ν) (u ν ∘ ⇑(sel ν (pool (n₁ ν) (n₂ ν) Z W ω)))}) atTop (𝓝 1)

/-- `thm:rt-coherent`, last clause, at a fixed level: the fixed-`K` test is consistent against every alternative with
`𝓔_K(P, Q) > 0` (for `K ≥ K_1`, `𝓔_K ≥ 𝓔_∞/2 > 0` by the frozen `rt_coherent_eventually`); no absolute continuity
of `μ_K` is needed (measurable selection of optimal assignments; measurable event). -/
def rt_coherent_consistent : Prop :=
  ∀ (K : ℕ) (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (P Q μ : Measure (𝔼 K))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure μ] (θ R : ℝ) (F : (𝔼 K) → 𝔼 K)
    (Z W : ℕ → Ω → 𝔼 K) (n₁ n₂ : ℕ → ℕ) (u : ∀ ν, Fin (n₁ ν + n₂ ν) → 𝔼 K)
    (sel : ∀ ν, (Fin (n₁ ν + n₂ ν) → 𝔼 K) → Equiv.Perm (Fin (n₁ ν + n₂ ν))) (α : ℝ),
    FixedKSetting K Pr P Q μ θ R F Z W n₁ n₂ u → 0 < energyD (P.map F) (Q.map F) → 0 < α → α < 1 →
    (∀ ν z, IsMin (u ν) z (sel ν z)) → (∀ ν h, MeasurableSet {z | sel ν z = h}) →
      (∀ ν, MeasurableSet {ω | critVal (rankEnergy (n₁ ν) (n₂ ν)) (u ν) α <
        rankEnergy (n₁ ν) (n₂ ν) (u ν ∘ ⇑(sel ν (pool (n₁ ν) (n₂ ν) Z W ω)))}) ∧
      Tendsto (fun ν => Pr {ω | critVal (rankEnergy (n₁ ν) (n₂ ν)) (u ν) α <
        rankEnergy (n₁ ν) (n₂ ν) (u ν ∘ ⇑(sel ν (pool (n₁ ν) (n₂ ν) Z W ω)))}) atTop (𝓝 1)

/-! #### `prop:rt-randomized` (c), (d) -/

/-- The randomized ranks `R̃ = u ∘ σ̃`, `σ̃ = 𝔯(z∘τ)∘τ⁻¹`, `𝔯` an optimal assignment rule, satisfy
`𝖤_N(R̃) → 𝓔_K` almost surely, whatever the shuffles `τ`. -/
def rt_randomized_limit : Prop :=
  ∀ (K : ℕ) (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (P Q μ : Measure (𝔼 K))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure μ] (θ R : ℝ) (F : (𝔼 K) → 𝔼 K)
    (Z W : ℕ → Ω → 𝔼 K) (n₁ n₂ : ℕ → ℕ) (u : ∀ ν, Fin (n₁ ν + n₂ ν) → 𝔼 K)
    (r : ∀ ν, (Fin (n₁ ν + n₂ ν) → 𝔼 K) → Equiv.Perm (Fin (n₁ ν + n₂ ν)))
    (τ : ∀ ν, Ω → Equiv.Perm (Fin (n₁ ν + n₂ ν))),
    FixedKSetting K Pr P Q μ θ R F Z W n₁ n₂ u → (∀ ν z, IsMin (u ν) z (r ν z)) →
      ∀ᵐ ω ∂Pr, Tendsto (fun ν => rankEnergy (n₁ ν) (n₂ ν)
        (u ν ∘ ⇑(rtSigma (r ν) (pool (n₁ ν) (n₂ ν) Z W ω) (τ ν ω)))) atTop (𝓝 (energyD (P.map F) (Q.map F)))

/-! #### `prop:rt-lift` (ii) -/

/-- Under the injectivity hypotheses of the frozen `rt_lift_laws` and integrable lifted maps, the energy distance
of the two groups' lifted rank laws is positive iff `P_T ≠ Q_T`, whatever `K`. -/
def rt_lift_sep : Prop :=
  ∀ (K m : ℕ) (P Q : Measure (EuclideanSpace ℝ (Fin K ⊕ Fin m))) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (θ : ℝ) (FK : (𝔼 K) → 𝔼 K) (SK : Set (𝔼 K)) (t : Fin m → ℝ → ℝ) (I : Fin m → Set ℝ),
    0 < θ → θ < 1 → Measurable FK → MeasurableSet SK → InjOn FK SK →
    mix θ P Q {x | headT x ∉ SK} = 0 →
    (∀ j, Measurable (t j)) → (∀ j, MeasurableSet (I j)) → (∀ j, InjOn (t j) (I j)) →
    (∀ j, mix θ P Q {x | x (Sum.inr j) ∉ I j} = 0) →
    Integrable (liftMap FK t) P → Integrable (liftMap FK t) Q →
      (0 < energyD (P.map (liftMap FK t)) (Q.map (liftMap FK t)) ↔ P ≠ Q)

/-! #### `lem:T-stability` -/

/-- "In particular", as printed: `ED(Υ#G#P_K, Υ#μ_K) = 0` only if `G = F_K` `P_K`-a.e. -/
def t_stability_ed : Prop :=
  ∀ (K : ℕ) (ρ : Measure (𝔼 K)) [ρ.IsAddHaarMeasure]
    (μ : Measure (𝔼 K)) [IsProbabilityMeasure μ] (g : (𝔼 K) → ℝ)
    (P : Measure (𝔼 K)) [IsProbabilityMeasure P] (F G : (𝔼 K) → 𝔼 K),
    IsGauge g → ScaleHyp μ g → MemLp id 2 μ → P ≪ ρ → MemLp id 2 P →
    Measurable F → Measurable G → P.map F = μ → IsConvGradAE P F → IsConvGradAE P G →
    energyD ((P.map G).map (ups μ g)) (μ.map (ups μ g)) = 0 →
      G =ᵐ[P] F

/-- The `δ–η` clause: for every `η > 0` there is `δ > 0` such that every measurable `G` that is `P_K`-a.e. the
gradient of a convex function with `ED(Υ#G#P_K, Υ#μ_K) < δ` satisfies `P_K{‖G − F_K‖ > η} < η`. -/
def t_stability_delta : Prop :=
  ∀ (K : ℕ) (ρ : Measure (𝔼 K)) [ρ.IsAddHaarMeasure]
    (μ : Measure (𝔼 K)) [IsProbabilityMeasure μ] (g : (𝔼 K) → ℝ)
    (P : Measure (𝔼 K)) [IsProbabilityMeasure P] (F : (𝔼 K) → 𝔼 K),
    IsGauge g → ScaleHyp μ g → MemLp id 2 μ → P ≪ ρ → MemLp id 2 P →
    Measurable F → P.map F = μ → IsConvGradAE P F →
      ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ G : (𝔼 K) → 𝔼 K, Measurable G → IsConvGradAE P G →
        energyD ((P.map G).map (ups μ g)) (μ.map (ups μ g)) < δ →
          P {x | η < ‖G x - F x‖} < ENNReal.ofReal η

/-! #### `prop:rt-adaptive` (ii) -/

/-- Consistency of the adaptive test with the full permutation distribution: if the fixed-`K` assumptions hold at a
level `l₀` with `P_{K_{l₀}} ≠ Q_{K_{l₀}}`, then `P(p^ad ≤ α) → 1` for every `α ∈ (0,1)` (measurable event). -/
def rt_adaptive_consistent : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H] (e : ℕ → H)
    (L : ℕ) (K : Fin (L + 1) → ℕ) (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (P Q : Measure H) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (μ : ∀ l, Measure (𝔼 (K l)))
    [∀ l, IsProbabilityMeasure (μ l)] (θ R : ℝ)
    (F : ∀ l, (𝔼 (K l)) → 𝔼 (K l)) (X Y : ℕ → Ω → H) (n₁ n₂ : ℕ → ℕ)
    (u : ∀ l ν, Fin (n₁ ν + n₂ ν) → 𝔼 (K l))
    (sel : ∀ l ν, (Fin (n₁ ν + n₂ ν) → 𝔼 (K l)) → Equiv.Perm (Fin (n₁ ν + n₂ ν))) (l₀ : Fin (L + 1)) (α : ℝ),
    FixedKSetting (K l₀) Pr (P.map (truncK e (K l₀))) (Q.map (truncK e (K l₀))) (μ l₀) θ R (F l₀)
      (fun i ω => truncK e (K l₀) (X i ω)) (fun j ω => truncK e (K l₀) (Y j ω)) n₁ n₂ (u l₀) →
    μ l₀ ≪ volume → P.map (truncK e (K l₀)) ≠ Q.map (truncK e (K l₀)) → 0 < α → α < 1 →
    (∀ ν z, IsMin (u l₀ ν) z (sel l₀ ν z)) → (∀ l ν h, MeasurableSet {z | sel l ν z = h}) →
    (∀ i, Measurable (X i)) → (∀ j, Measurable (Y j)) →
      (∀ ν, MeasurableSet {ω | pAdFull (fun l (y : Fin (n₁ ν + n₂ ν) → ∀ l', 𝔼 (K l')) =>
          rankEnergy (n₁ ν) (n₂ ν) (fun i => y i l))
        (fun i l => u l ν (sel l ν (pool (n₁ ν) (n₂ ν) (fun i ω => truncK e (K l) (X i ω))
          (fun j ω => truncK e (K l) (Y j ω)) ω) i)) ≤ α}) ∧
      Tendsto (fun ν => Pr {ω | pAdFull (fun l (y : Fin (n₁ ν + n₂ ν) → ∀ l', 𝔼 (K l')) =>
          rankEnergy (n₁ ν) (n₂ ν) (fun i => y i l))
        (fun i l => u l ν (sel l ν (pool (n₁ ν) (n₂ ν) (fun i ω => truncK e (K l) (X i ω))
          (fun j ω => truncK e (K l) (Y j ω)) ω) i)) ≤ α}) atTop (𝓝 1)

end Claims

end StatFormal.OTFD.WaveL2
