import StatFormal.Archive.OTFD.WaveL1.Statements
import StatFormal.Archive.OTFD.Wave22b.Statements
import TauCeti.MeasureTheory.OptimalTransport.Cost.CyclicalMonotonicity

/-!
# FROZEN STATEMENTS — otfd wave L3 (discharges): Brenier uniqueness in `H` (A `lem:app-cm-plans`(iv)) and the
# unconditional wave-L1 limits; uniqueness for `W₁` targets; C `prop:conditional-potentials` and the unconditional
# wave-22b C band / coverage / transfer limits

Sources (verbatim in `lean-formalisation/inventory/extracted/{otfd-A_sieves,otfd-R_robustness,otfd-C_conditional}.md`;
current text of `otfd/papers/`):
* A `lem:app-cm-plans`(iv) (`A_sieves/supplement.tex`, used by `lem:plan-stability-H`, `:5145-5168`), GHS 2026 / AGS
  Thm 6.2.10; R setting paragraph (`R_robustness/sections/s6_references.tex:11-16`), now with finite second moments.
* The frozen wave-L1 claims (`OTFD/WaveL1/Statements.lean`) `plan_stab_a/_b/_b_map`, `sieve_strong_limit`,
  `sieve_strong_full`, `integrated_quantile`, `plan_w2_a/_b/_b_map`, `moment_sieve_a/_b`, each conditional on the
  declared hypothesis `BrenierUniq`.
* C `prop:conditional-potentials` (`C_conditional/supplement.tex:1081-1120`) under `ass:conditional-oos`
  (`main.tex:654-661`, with `eq:weighted-hard-gap`, `supplement.tex:960-970`, and `lem:weighted-duality`,
  `:973-990`: `X_n = (χ_n + ι_{𝒰_K})^*`, `X_n(0) = 0`, i.e. `inf_{𝒰_K} χ_n = 0`).
* The frozen wave-22b claims (`OTFD/Wave22b/Statements.lean`) `cond_maps_ae`, `cond_band_one_sided_potentials`,
  `cond_test_coverage_potentials`, `cond_transfer_consistency`, `cond_transfer_consistency_prob`, each with the
  conclusion of `prop:conditional-potentials` (locally uniform convergence of the potentials) as a premise.
Imports the frozen `OTFD/WaveL1` (`CycMon`, `CMConc`, `IsCMMapAE`, `Graph`, `BrenierUniq`, `LipNull`, `Mom2`,
`W2Conv`, `Euc`; through it `OTFD/Wave1` `PellClass`, `truncK`, `OTFD/Wave8b` `embed`, `Wave21b` `nsign`) and
`OTFD/Wave22b` (through it `OTFD/Wave19a` `extTop`, Tau Ceti `subdifferential`, `Wave17a` `hPop`, `Wave21b` `supE`)
statements, not copied; Tau Ceti's `IsCyclicallyMonotone`. Mathlib otherwise.

Covered:
* Cyclical monotonicity: `cycmon_iff` (paper cycle form `CycMon` ⇔ Tau Ceti's permutation form for `‖x − y‖²/2`).
* Brenier in a separable Hilbert space `H` (`P` null on Lipschitz hypersurfaces, finite second moments):
  `brenier_uniq_H` (the frozen `BrenierUniq P μ F`: A `lem:app-cm-plans`(iv) generalised to unbounded `μ` (GHS) and
  specialised to `m₂(P), m₂(μ) < ∞`; A (iv) itself assumes a bounded target and no moment), `brenier_uniq_H_swap` (the exchanged
  form `BrenierUniq μ P Q` used by the quantile claims, `P` the Lipschitz-null *target*), `brenier_exists_H` (the map
  exists: nonvacuity). Beyond second moments: `brenier_uniq_H_bdd` (bounded target, first moment of `P`),
  `brenier_uniq_bdd_source` (bounded Lipschitz-null source, first moment of the target: C's `W₁` targets).
* Unconditional wave-L1 limits (`BrenierUniq` replaced by `F#P = μ`, `F` `P`-a.e. cyclically monotone and, where the
  frozen claim has no moment of `P` (the five A items, bounded targets), a first moment `m₁(P) < ∞` (via
  `brenier_uniq_H_bdd`); "unconditional" means `BrenierUniq`-free, see Not covered):
  `plan_stab_a_uncond`, `plan_stab_b_uncond`, `plan_stab_b_map_uncond`, `sieve_strong_limit_uncond`,
  `sieve_strong_full_uncond`, `integrated_quantile_uncond`, `plan_w2_a_uncond`, `plan_w2_b_uncond`,
  `plan_w2_b_map_uncond`, `moment_sieve_a_uncond`, `moment_sieve_b_uncond`.
* `lipnull_of_ac` (in `ℝ^K`, `≪` Lebesgue ⇒ null on Lipschitz hypersurfaces), `plan_stab_w1` (plan stability for a
  bounded Lipschitz-null source and first-moment targets: the "plan convergence for `W₁` targets" of C).
* C `prop:conditional-potentials`, exact hard fits: `cond_potentials` (a normalised population potential exists; the
  `inf`-normalised `χ_n` and `g_n` converge to it uniformly on compact subsets of `int 𝒰_K`).
* Unconditional C limits (the potential premise replaced by the fitted plans and potentials of `HardFit`):
  `cond_maps_ae_plans`, `cond_band_one_sided_plans`, `cond_test_coverage_plans`, `cond_transfer_consistency_plans`,
  `cond_transfer_consistency_prob_plans`.

Not covered (declared):
* C with an inexact hard fit (`ζ_n > 0`, `ζ_n → 0`): RESTRICTION — `HardFit` assumes an exact hard fit (a fitted
  plan in `Π(μ_{K,m_n}, P̂_{K,n,x})` carried by the subdifferential graph of a finite convex potential `χ_n`; by finite
  LP duality `ζ_n = 0` implies it, with `χ_n` the Laguerre potential and an optimal plan). The `ζ_n → 0` case needs the
  duality-sandwich identification of C's proof (approximate contact sets), not formalised; so for inexact fits the
  C limits remain conditional (frozen wave-22b claims). `HardFit` is otherwise more general than
  `ass:conditional-oos`: any finite convex `χ_n` (not only Laguerre), grids not required to lie in `𝒰_K`, weak instead
  of `W₁` convergence (with `m₁(P_{K,x}) < ∞`), `g_n` not required differentiable.
* C: the `W₁` convergence is used only through weak convergence (plus the first moment of the limit law); the
  "almost surely" of `prop:conditional-potentials` is per realisation (`HardFit` holds on an event); the entropic and
  quadratic soft-fit sufficient conditions of `lem:weighted-duality` (its conclusion `sup_u |g_n − χ_n| → 0` is the
  hypothesis of `HardFit`).
* A `thm:sieve-convergence` limit clauses (infinite-dimensional Rockafellar 24.5): not attempted.
* Moments (remaining restriction vs A): A `lem:plan-stability-H` and `prop:integrated-sieve-strong` assume NO moment
  of `P` (A `def:app-lipschitz-hypersurface`: "the moment clause is not used"), and `lem:app-cm-plans`(iv) none either;
  the `_uncond` forms of `plan_stab_a/_b/_b_map`, `sieve_strong_limit`, `sieve_strong_full` add a first moment
  `m₁(P) < ∞` (the targets are bounded; `brenier_uniq_H_bdd`: with `|⟪x, y⟫| ≤ M‖x‖` the cost `(M‖x‖ − ⟪x, y⟫)₊` has
  finite total, so cyclically monotone couplings are optimal). The moment-free case needs McCann/GHS uniqueness of
  gradients of Lipschitz convex functions pushing `P` to `μ` without an integrable cost (Aleksandrov-type argument,
  not available in `H`); it is covered only by the conditional frozen claims. (`integrated_quantile` already assumes
  `P ∈ 𝒫^ℓ` with second moment, and R's standing setting assumes second moments, so `plan_w2_*` and `moment_sieve_*`
  keep `m₂`: no strengthening there.)

Encodings (to be checked by the critic):
* As in wave L1: `H : Type` a separable real Hilbert space with its Borel σ-algebra, `ℝ^K = Euc K`; weak convergence
  in Mathlib's topology on `ProbabilityMeasure`; `π ∈ Π(α, ν)` via Mathlib marginals; the Brenier map `𝔽^μ_P` is any
  Borel `F` with `F#P = μ` and `IsCMMapAE P F` (exactly the finite-dimensional encoding of wave L1).
* `Mom1 μ = ∫⁻ ‖y‖ₑ dμ` (first moment, `ℝ≥0∞`); `m₂ = Mom2`; `𝒫^ℓ` with second moment `= PellClass`.
* C: `RefLaw μ U` = `μ_K ≪ Leb`, `𝒰_K` convex compact, `μ_K(𝒰_K^c) = 0`, `int 𝒰_K ⊆ supp μ_K` (C has `𝒰_K = supp
  μ_K`). `HardFit` = grids `α_n ⇀ μ_K`, weighted targets `ν_n ⇀ P_{K,x}`, fitted plans `π_n ∈ Π(α_n, ν_n)`, Laguerre
  potentials `χ_n` finite convex on `ℝ^K` with `π_n`-a.e. `(u, z)`: `z ∈ ∂χ_n(u)` (global subgradient inequality),
  and the fitted potentials `g_n` with `sup_{𝒰_K} |g_n − χ_n| → 0` (same normalising constant). C's normalisation
  `inf_{𝒰_K} χ_n = 0` is "subtract any `c_n` with `IsGLB (χ_n '' 𝒰_K) c_n`" (no `sInf` junk); the population
  potential is normalised by `IsGLB (χ '' int 𝒰_K) 0`. The population map `Q_{K,x}` is any Borel `Q` with
  `Q#μ_K = P_{K,x}` that is `μ_K`-a.e. cyclically monotone (`cond_potentials`) or `μ_K`-a.e. `∇χ` for a convex `χ`
  on `int 𝒰_K` (the frozen form, in the discharge claims).
* The discharge claims restate the frozen wave-22b claims verbatim except: the premise "`g_n` convex on `int 𝒰_K`,
  `g_n → χ` uniformly on compacts of `int 𝒰_K`" is replaced by `RefLaw`, the population facts (`Mom1 P < ∞`, `Q`
  Borel, `Q#μ = P`) and `HardFit` with `g_n` convex on `int 𝒰_K` (no normalisation of `g_n` or of `χ` is assumed:
  the conclusions only involve subgradients and gradients); `μ` is a probability measure.

Critic notes:
* All 25 claims are proved in `OTFD/WaveL3/Route{CycMon,BrenierH,Uniq,Norm,Hilbert,Cond,CondClaims}.lean`, checked in
  `OTFD/WaveL3/Proofs.lean` (axioms: propext, Classical.choice, Quot.sound). They use the untrusted libraries `Foundations/Potentials` (`HilbertUniqueness`: AGS 6.2.10, the
  Lipschitz-hypersurface cover, graph plans from a.e. single-valued supports; `LocalBound`: limit potential from plan
  convergence; `Stability`; `Uniqueness`: potentials unique up to constants), `Foundations/OTLimits`, Tau Ceti
  (Schachermayer–Teichmann, Gangbo–McCann support monotonicity, `IsOptimalCoupling.add`) and the certified routes of
  waves L1 (`tendsto_of_cmConc`, the frozen L1 theorems) and 22b (the frozen C theorems) — routes only.
* `brenier_uniq_bdd_source` / `brenier_uniq_H_bdd` generalise the library's second-moment proof: for a cost
  `(a(x) + b(y) − ⟪x, y⟫)₊` with `|⟪x, y⟫| ≤ a(x) + b(y)` on the (closed) supports and `a ∈ L¹(μ)`, `b ∈ L¹(ν)`,
  paper-CM couplings are optimal; the sum of two is optimal with monotone support; Lipschitz-null sources make it
  single-valued.
* No tautology: every conclusion is a limit, a uniqueness or an existence statement not among the hypotheses;
  `HardFit` contains no convergence of potentials (only of the marginals and the uniform closeness `g_n − χ_n → 0`).
* Nonvacuity: `brenier_exists_H` (the Hilbert claims), `cond_potentials` (existence of the normalised population
  potential as part of the conclusion; the population map `Q` itself is a premise — for `m₂(P) < ∞` it exists by
  `brenier_exists_H` + `lipnull_of_ac` in `H = ℝ^K`; McCann's first-moment existence is not claimed). `HardFit` is
  satisfiable, not claimed: e.g. finitely supported `α_n ⇀ μ_K`, `ν_n ⇀ P`, `π_n` optimal (finite support, cyclically
  monotone), `χ_n` its Rockafellar potential (a finite max of affine functions), `g_n = χ_n`. (`χ_n = χ`, `π_n` the
  Brenier plan works only for bounded `P`: a finite convex function on `ℝ^K` has locally bounded subgradients.)
* Critic (2026-10-15): ACCEPT-WITH-NOTE. Mechanical diff against the frozen claims: each `_uncond` claim differs from
  its wave-L1 original only by `BrenierUniq` ↦ `F#P = μ ∧ IsCMMapAE` (plus `m₁(P) < ∞` in the five A items above);
  each `_plans` claim differs from its wave-22b original only by the potential-convergence premise ↦ `RefLaw`,
  `m₁(P) < ∞`, `Q` Borel, `Q#μ_K = P`, `HardFit` (and `μ` a probability). All objects are the imported frozen ones.
  No junk: every `Measure.map` is of an assumed-measurable (or continuous `truncK`) map, moments are `ℝ≥0∞`
  lower integrals, normalisations are `IsGLB` (attained: `χ_n` continuous on the compact nonempty `𝒰_K`), and
  `gradient` junk lies on a `μ_K`-null set.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/
set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.OTFD.WaveL3

open StatFormal.OTFD.WaveL1 (CycMon CMConc IsCMMapAE Graph BrenierUniq LipNull Mom2 W2Conv Euc)
open StatFormal.OTFD.Wave1 (PellClass truncK)
open StatFormal.OTFD.Wave8b (embed)
open StatFormal.Wave21b (nsign)
open StatFormal.OTFD.Wave19a (extTop)

/-! ### Definitions -/

section Defs
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]

/-- The first moment `m₁(μ) = ∫ ‖y‖ dμ`, in `ℝ≥0∞`. -/
def Mom1 (μ : Measure E) : ℝ≥0∞ := ∫⁻ y, ‖y‖ₑ ∂μ

end Defs

/-- C's reference law at fixed `K`: `μ_K ≪ Leb`, carried by the compact convex set `𝒰_K`, whose interior lies in
`supp μ_K`. -/
def RefLaw {K : ℕ} (μ : Measure (Euc K)) (U : Set (Euc K)) : Prop :=
  μ ≪ volume ∧ Convex ℝ U ∧ IsCompact U ∧ μ Uᶜ = 0 ∧ interior U ⊆ μ.support

/-- C `ass:conditional-oos` at one query with an **exact hard fit**: grids `α_n ⇀ μ`, weighted targets `ν_n ⇀ P`,
fitted plans `π_n ∈ Π(α_n, ν_n)` carried by the subdifferential graph of the finite convex (Laguerre) potentials
`χ_n`, and fitted potentials `g_n` uniformly close to `χ_n` on `U` (`sup_U |g_n − χ_n| → 0`). -/
def HardFit {K : ℕ} (μ P : ProbabilityMeasure (Euc K)) (U : Set (Euc K)) (α ν : ℕ → ProbabilityMeasure (Euc K))
    (π : ℕ → ProbabilityMeasure (Euc K × Euc K)) (χn g : ℕ → Euc K → ℝ) : Prop :=
  Tendsto α atTop (𝓝 μ) ∧ Tendsto ν atTop (𝓝 P) ∧
    (∀ n, (π n : Measure (Euc K × Euc K)).fst = α n) ∧ (∀ n, (π n : Measure (Euc K × Euc K)).snd = ν n) ∧
    (∀ n, ConvexOn ℝ univ (χn n)) ∧
    (∀ n, ∀ᵐ z ∂(π n : Measure (Euc K × Euc K)), ∀ x, χn n z.1 + ⟪z.2, x - z.1⟫ ≤ χn n x) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ u ∈ U, |g n u - χn n u| ≤ ε)

namespace Claims

/-! #### Cyclical monotonicity: the two forms -/

/-- The paper's cycle form `Σ ⟨y_i, x_{i+1} − x_i⟩ ≤ 0` is Tau Ceti's permutation form for `‖x − y‖²/2`. -/
def cycmon_iff : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (S : Set (E × E)),
    CycMon S ↔ TauCeti.IsCyclicallyMonotone (fun p : E × E => ‖p.1 - p.2‖ ^ 2 / 2) S

/-! #### Brenier uniqueness and existence in a separable Hilbert space -/

/-- Brenier–GHS uniqueness in `H` (A `lem:app-cm-plans`(iv) for unbounded targets, with second moments in place of
(iv)'s bounded target): `P` null on Lipschitz hypersurfaces, `m₂(P), m₂(μ) < ∞`, `F` Borel, `P`-a.e. cyclically
monotone, `F#P = μ` ⇒ every coupling of `P` and `μ` concentrated on a Borel cyclically monotone set is `(Id × F)#P`. -/
def brenier_uniq_H : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (P μ : ProbabilityMeasure H) (F : H → H),
    LipNull (P : Measure H) → Mom2 (P : Measure H) ≠ ∞ → Mom2 (μ : Measure H) ≠ ∞ →
    Measurable F → (P : Measure H).map F = μ → IsCMMapAE (P : Measure H) F →
      BrenierUniq (P : Measure H) μ F

/-- The exchanged form (quantile maps, GHS Lemma 4.3): the *target* `P` null on Lipschitz hypersurfaces,
`m₂(P), m₂(μ) < ∞`, `Q` Borel, `μ`-a.e. cyclically monotone, `Q#μ = P` ⇒ every cyclically monotone coupling of `μ`
and `P` is `(Id × Q)#μ`. -/
def brenier_uniq_H_swap : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (P μ : ProbabilityMeasure H) (Q : H → H),
    LipNull (P : Measure H) → Mom2 (P : Measure H) ≠ ∞ → Mom2 (μ : Measure H) ≠ ∞ →
    Measurable Q → (μ : Measure H).map Q = P → IsCMMapAE (μ : Measure H) Q →
      BrenierUniq (μ : Measure H) P Q

/-- Existence of `𝔽^μ_P`: a Borel map, `P`-a.e. cyclically monotone, pushing `P` to `μ`. -/
def brenier_exists_H : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (P μ : ProbabilityMeasure H),
    LipNull (P : Measure H) → Mom2 (P : Measure H) ≠ ∞ → Mom2 (μ : Measure H) ≠ ∞ →
      ∃ F : H → H, Measurable F ∧ (P : Measure H).map F = μ ∧ IsCMMapAE (P : Measure H) F

/-- A `lem:app-cm-plans`(iv) uniqueness (bounded target), with a first moment of the Lipschitz-null source ((iv)
assumes no moment). -/
def brenier_uniq_H_bdd : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (P μ : ProbabilityMeasure H) (F : H → H) (M : ℝ),
    LipNull (P : Measure H) → Mom1 (P : Measure H) ≠ ∞ → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
    Measurable F → (P : Measure H).map F = μ → IsCMMapAE (P : Measure H) F →
      BrenierUniq (P : Measure H) μ F

/-- Uniqueness with a bounded Lipschitz-null source and only a first moment of the target (C: `μ_K` and `W₁`
targets). -/
def brenier_uniq_bdd_source : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (μ P : ProbabilityMeasure H) (Q : H → H) (M : ℝ),
    LipNull (μ : Measure H) → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 → Mom1 (P : Measure H) ≠ ∞ →
    Measurable Q → (μ : Measure H).map Q = P → IsCMMapAE (μ : Measure H) Q →
      BrenierUniq (μ : Measure H) P Q

/-! #### Unconditional A `lem:plan-stability-H` (wave L1 with `BrenierUniq` discharged) -/

/-- `plan_stab_a` without `BrenierUniq`: `P` null on Lipschitz hypersurfaces with a first moment `m₁(P) < ∞` (A assumes
no moment), `𝔽^μ_P` any Borel map, `P`-a.e. cyclically monotone, pushing `P` to `μ`. -/
def plan_stab_a_uncond : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (P μ : ProbabilityMeasure H) (F : H → H) (M : ℝ) (α ν : ℕ → ProbabilityMeasure H)
    (π : ℕ → ProbabilityMeasure (H × H)) (G : ProbabilityMeasure (H × H)),
    LipNull (P : Measure H) → Mom1 (P : Measure H) ≠ ∞ → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
    Measurable F → (P : Measure H).map F = μ → IsCMMapAE (P : Measure H) F →
    Tendsto α atTop (𝓝 P) → Tendsto ν atTop (𝓝 μ) →
    (∀ K, (π K : Measure (H × H)).fst = α K) → (∀ K, (π K : Measure (H × H)).snd = ν K) →
    (∀ K, CMConc (π K : Measure (H × H))) →
    (G : Measure (H × H)) = Graph (P : Measure H) F →
      Tendsto π atTop (𝓝 G)

/-- `plan_stab_b` without `BrenierUniq`, with `m₁(P) < ∞`. -/
def plan_stab_b_uncond : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (P μ : ProbabilityMeasure H) (F : H → H) (M : ℝ) (ν : ℕ → ProbabilityMeasure H)
    (π : ℕ → ProbabilityMeasure (H × H)),
    LipNull (P : Measure H) → Mom1 (P : Measure H) ≠ ∞ →
    Measurable F → (P : Measure H).map F = μ → IsCMMapAE (P : Measure H) F →
    Tendsto ν atTop (𝓝 μ) → (∀ K, (ν K : Measure H) (Metric.closedBall 0 M)ᶜ = 0) →
    (∀ K, (π K : Measure (H × H)).fst = P) → (∀ K, (π K : Measure (H × H)).snd = ν K) →
    (∀ K, CMConc (π K : Measure (H × H))) →
      Tendsto (fun K => ∫⁻ z, ‖z.2 - F z.1‖ₑ ^ 2 ∂(π K : Measure (H × H))) atTop (𝓝 0)

/-- `plan_stab_b_map` without `BrenierUniq`, with `m₁(P) < ∞`. -/
def plan_stab_b_map_uncond : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (P μ : ProbabilityMeasure H) (F : H → H) (M : ℝ) (ν : ℕ → ProbabilityMeasure H)
    (T : ℕ → H → H),
    LipNull (P : Measure H) → Mom1 (P : Measure H) ≠ ∞ →
    Measurable F → (P : Measure H).map F = μ → IsCMMapAE (P : Measure H) F →
    Tendsto ν atTop (𝓝 μ) → (∀ K, (ν K : Measure H) (Metric.closedBall 0 M)ᶜ = 0) →
    (∀ K, Measurable (T K)) → (∀ K, (P : Measure H).map (T K) = ν K) →
    (∀ K, IsCMMapAE (P : Measure H) (T K)) →
      Tendsto (fun K => ∫⁻ x, ‖T K x - F x‖ₑ ^ 2 ∂(P : Measure H)) atTop (𝓝 0)

/-! #### Unconditional A `prop:integrated-sieve-strong`, `prop:integrated-quantile` -/

/-- `sieve_strong_limit` without `BrenierUniq`, with `m₁(P) < ∞` (A assumes no moment). -/
def sieve_strong_limit_uncond : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (P μ : ProbabilityMeasure H) (F : H → H) (M : ℝ) (FK : (K : ℕ) → Euc K → Euc K),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    LipNull (P : Measure H) → Mom1 (P : Measure H) ≠ ∞ → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
    Measurable F → (P : Measure H).map F = μ → IsCMMapAE (P : Measure H) F →
    (∀ K, Measurable (FK K)) →
    (∀ K, ((P : Measure H).map (truncK e K)).map (FK K) = (μ : Measure H).map (truncK e K)) →
    (∀ K, IsCMMapAE ((P : Measure H).map (truncK e K)) (FK K)) →
      Tendsto (fun K => ∫⁻ x, ‖embed e K (FK K (truncK e K x)) - F x‖ₑ ^ 2 ∂(P : Measure H))
        atTop (𝓝 0)

/-- `sieve_strong_full` without `BrenierUniq`, with `m₁(P) < ∞`. -/
def sieve_strong_full_uncond : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (P μ : ProbabilityMeasure H) (F : H → H) (M : ℝ) (FK : (K : ℕ) → Euc K → Euc K)
    (c : H),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    LipNull (P : Measure H) → Mom1 (P : Measure H) ≠ ∞ → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
    (μ : Measure H) {0} = 0 →
    Measurable F → (P : Measure H).map F = μ → IsCMMapAE (P : Measure H) F →
    (∀ K, Measurable (FK K)) →
    (∀ K, ((P : Measure H).map (truncK e K)).map (FK K) = (μ : Measure H).map (truncK e K)) →
    (∀ K, IsCMMapAE ((P : Measure H).map (truncK e K)) (FK K)) →
      Tendsto (fun K => ∫⁻ x, ‖‖embed e K (FK K (truncK e K x))‖ - ‖F x‖‖ₑ ^ 2 ∂(P : Measure H))
          atTop (𝓝 0) ∧
        TendstoInMeasure (P : Measure H) (fun K x => nsign c (embed e K (FK K (truncK e K x))))
          atTop (fun x => nsign c (F x)) ∧
        Tendsto (fun K => ∫⁻ x, ‖nsign c (embed e K (FK K (truncK e K x))) - nsign c (F x)‖ₑ ^ 2
          ∂(P : Measure H)) atTop (𝓝 0)

/-- `integrated_quantile` without `BrenierUniq`: `𝕼_P` any Borel map, `μ`-a.e. cyclically monotone, pushing `μ`
to `P` (`P ∈ 𝒫^ℓ(H)` with its second moment). -/
def integrated_quantile_uncond : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (P μ : ProbabilityMeasure H) (Q : H → H) (M : ℝ) (QK : (K : ℕ) → Euc K → Euc K),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    PellClass (P : Measure H) → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
    Measurable Q → (μ : Measure H).map Q = P → IsCMMapAE (μ : Measure H) Q →
    (∀ K, Measurable (QK K)) →
    (∀ K, ((μ : Measure H).map (truncK e K)).map (QK K) = (P : Measure H).map (truncK e K)) →
    (∀ K, IsCMMapAE ((μ : Measure H).map (truncK e K)) (QK K)) →
      Tendsto (fun K => ∫⁻ u, ‖embed e K (QK K (truncK e K u)) - Q u‖ₑ ^ 2 ∂(μ : Measure H))
        atTop (𝓝 0)

/-! #### Unconditional R `lem:plan-w2`, `thm:moment-sieve` -/

/-- `plan_w2_a` without `BrenierUniq`. -/
def plan_w2_a_uncond : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (P μ : ProbabilityMeasure H) (F : H → H) (α ν : ℕ → ProbabilityMeasure H)
    (π : ℕ → ProbabilityMeasure (H × H)) (G : ProbabilityMeasure (H × H)),
    PellClass (P : Measure H) → Mom2 (μ : Measure H) ≠ ∞ →
    Measurable F → (P : Measure H).map F = μ → IsCMMapAE (P : Measure H) F →
    W2Conv α P → W2Conv ν μ →
    (∀ K, (π K : Measure (H × H)).fst = α K) → (∀ K, (π K : Measure (H × H)).snd = ν K) →
    (∀ K, CMConc (π K : Measure (H × H))) →
    (G : Measure (H × H)) = Graph (P : Measure H) F →
      Tendsto π atTop (𝓝 G)

/-- `plan_w2_b` without `BrenierUniq`. -/
def plan_w2_b_uncond : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (P μ : ProbabilityMeasure H) (F : H → H) (ν : ℕ → ProbabilityMeasure H)
    (π : ℕ → ProbabilityMeasure (H × H)),
    PellClass (P : Measure H) → Mom2 (μ : Measure H) ≠ ∞ →
    Measurable F → (P : Measure H).map F = μ → IsCMMapAE (P : Measure H) F → W2Conv ν μ →
    (∀ K, (π K : Measure (H × H)).fst = P) → (∀ K, (π K : Measure (H × H)).snd = ν K) →
    (∀ K, CMConc (π K : Measure (H × H))) →
      Tendsto (fun K => ∫⁻ z, ‖z.2 - F z.1‖ₑ ^ 2 ∂(π K : Measure (H × H))) atTop (𝓝 0)

/-- `plan_w2_b_map` without `BrenierUniq`. -/
def plan_w2_b_map_uncond : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (P μ : ProbabilityMeasure H) (F : H → H) (ν : ℕ → ProbabilityMeasure H) (T : ℕ → H → H),
    PellClass (P : Measure H) → Mom2 (μ : Measure H) ≠ ∞ →
    Measurable F → (P : Measure H).map F = μ → IsCMMapAE (P : Measure H) F → W2Conv ν μ →
    (∀ K, Measurable (T K)) → (∀ K, (P : Measure H).map (T K) = ν K) →
    (∀ K, IsCMMapAE (P : Measure H) (T K)) →
      Tendsto (fun K => ∫⁻ x, ‖T K x - F x‖ₑ ^ 2 ∂(P : Measure H)) atTop (𝓝 0)

/-- `moment_sieve_a` without `BrenierUniq`. -/
def moment_sieve_a_uncond : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (P μ : ProbabilityMeasure H) (F : H → H) (FK : (K : ℕ) → Euc K → Euc K),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    PellClass (P : Measure H) → Mom2 (μ : Measure H) ≠ ∞ →
    Measurable F → (P : Measure H).map F = μ → IsCMMapAE (P : Measure H) F →
    (∀ K, Measurable (FK K)) →
    (∀ K, ((P : Measure H).map (truncK e K)).map (FK K) = (μ : Measure H).map (truncK e K)) →
    (∀ K, IsCMMapAE ((P : Measure H).map (truncK e K)) (FK K)) →
      Tendsto (fun K => ∫⁻ x, ‖embed e K (FK K (truncK e K x)) - F x‖ₑ ^ 2 ∂(P : Measure H))
        atTop (𝓝 0)

/-- `moment_sieve_b` without `BrenierUniq`. -/
def moment_sieve_b_uncond : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (P μ : ProbabilityMeasure H) (Q : H → H) (QK : (K : ℕ) → Euc K → Euc K),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    PellClass (P : Measure H) → PellClass (μ : Measure H) →
    Measurable Q → (μ : Measure H).map Q = P → IsCMMapAE (μ : Measure H) Q →
    (∀ K, Measurable (QK K)) →
    (∀ K, ((μ : Measure H).map (truncK e K)).map (QK K) = (P : Measure H).map (truncK e K)) →
    (∀ K, IsCMMapAE ((μ : Measure H).map (truncK e K)) (QK K)) →
      Tendsto (fun K => ∫⁻ u, ‖embed e K (QK K (truncK e K u)) - Q u‖ₑ ^ 2 ∂(μ : Measure H))
        atTop (𝓝 0)

/-! #### `W₁` targets: Lipschitz-null laws in `ℝ^K`, plan stability -/

/-- In `ℝ^K`, a law `≪` Lebesgue gives zero mass to every Lipschitz hypersurface. -/
def lipnull_of_ac : Prop :=
  ∀ (K : ℕ) (μ : Measure (Euc K)), μ ≪ volume → LipNull μ

/-- Plan stability with a bounded Lipschitz-null source and first-moment targets: `α_n ⇀ μ`, `ν_n ⇀ P`,
`π_n ∈ Π(α_n, ν_n)` concentrated on Borel cyclically monotone sets ⇒ `π_n ⇀ (Id × Q)#μ`. -/
def plan_stab_w1 : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (μ P : ProbabilityMeasure H) (Q : H → H) (M : ℝ) (α ν : ℕ → ProbabilityMeasure H)
    (π : ℕ → ProbabilityMeasure (H × H)) (G : ProbabilityMeasure (H × H)),
    LipNull (μ : Measure H) → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 → Mom1 (P : Measure H) ≠ ∞ →
    Measurable Q → (μ : Measure H).map Q = P → IsCMMapAE (μ : Measure H) Q →
    Tendsto α atTop (𝓝 μ) → Tendsto ν atTop (𝓝 P) →
    (∀ n, (π n : Measure (H × H)).fst = α n) → (∀ n, (π n : Measure (H × H)).snd = ν n) →
    (∀ n, CMConc (π n : Measure (H × H))) →
    (G : Measure (H × H)) = Graph (μ : Measure H) Q →
      Tendsto π atTop (𝓝 G)

/-! #### C `prop:conditional-potentials` (exact hard fits) -/

/-- C `prop:conditional-potentials`: under `RefLaw`, a first-moment target `P = P_{K,x}` with population map `Q`
(Borel, `Q#μ_K = P`, `μ_K`-a.e. cyclically monotone) and an exact hard fit, (i) a population potential exists:
`χ` convex on `int 𝒰_K`, `Q = ∇χ` `μ_K`-a.e., `inf_{int 𝒰_K} χ = 0`; (ii) for every such `χ` and every choice of the
normalising constants `c_n = inf_{𝒰_K} χ_n`, `χ_n − c_n → χ` and `g_n − c_n → χ` uniformly on every compact subset
of `int 𝒰_K`. -/
def cond_potentials : Prop :=
  ∀ (K : ℕ) (μ P : ProbabilityMeasure (Euc K)) (U : Set (Euc K)) (Q : Euc K → Euc K)
    (α ν : ℕ → ProbabilityMeasure (Euc K)) (π : ℕ → ProbabilityMeasure (Euc K × Euc K)) (χn g : ℕ → Euc K → ℝ),
    RefLaw (μ : Measure (Euc K)) U → Mom1 (P : Measure (Euc K)) ≠ ∞ →
    Measurable Q → (μ : Measure (Euc K)).map Q = P → IsCMMapAE (μ : Measure (Euc K)) Q →
    HardFit μ P U α ν π χn g →
      (∃ χ : Euc K → ℝ, ConvexOn ℝ (interior U) χ ∧ Q =ᵐ[(μ : Measure (Euc K))] gradient χ ∧
          IsGLB (χ '' interior U) 0) ∧
        ∀ χ : Euc K → ℝ, ConvexOn ℝ (interior U) χ → Q =ᵐ[(μ : Measure (Euc K))] gradient χ →
          IsGLB (χ '' interior U) 0 → ∀ c : ℕ → ℝ, (∀ n, IsGLB (χn n '' U) (c n)) →
            ∀ S ⊆ interior U, IsCompact S →
              TendstoUniformlyOn (fun n u => χn n u - c n) χ atTop S ∧
                TendstoUniformlyOn (fun n u => g n u - c n) χ atTop S

/-! #### Unconditional C limits (wave 22b with the potential premise discharged) -/

/-- `cond_maps_ae` from an exact hard fit (`ζ_n = 0`, see Not covered): `Q_n(u) → Q(u)` for `μ_K`-a.e. `u` (in `int 𝒰_K`, at differentiability points
of `χ`), every subgradient selection `Q_n` of the fitted potentials `g_n`. -/
def cond_maps_ae_plans : Prop :=
  ∀ (K : ℕ) (μ P : ProbabilityMeasure (Euc K)) (U : Set (Euc K)) (χ : Euc K → ℝ) (Q : Euc K → Euc K)
    (Qn : ℕ → Euc K → Euc K) (α ν : ℕ → ProbabilityMeasure (Euc K)) (π : ℕ → ProbabilityMeasure (Euc K × Euc K))
    (χn g : ℕ → Euc K → ℝ),
    RefLaw (μ : Measure (Euc K)) U → Mom1 (P : Measure (Euc K)) ≠ ∞ →
    Measurable Q → (μ : Measure (Euc K)).map Q = P →
    ConvexOn ℝ (interior U) χ → Q =ᵐ[(μ : Measure (Euc K))] gradient χ →
    HardFit μ P U α ν π χn g → (∀ n, ConvexOn ℝ (interior U) (g n)) →
    (∀ n, ∀ u ∈ interior U, Qn n u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n)) u) →
      ∀ᵐ u ∂(μ : Measure (Euc K)), u ∈ interior U ∧ DifferentiableAt ℝ χ u ∧ Tendsto (fun n => Qn n u) atTop (𝓝 (Q u))

/-- `cond_band_one_sided_potentials` from an exact hard fit: at a level with bounded essential range the edge deficit
vanishes. -/
def cond_band_one_sided_plans : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ P : ProbabilityMeasure (Euc K)) (U A : Set (Euc K)) (χ : Euc K → ℝ) (Q : Euc K → Euc K)
    (Qn : ℕ → Euc K → Euc K) (α ν : ℕ → ProbabilityMeasure (Euc K)) (π : ℕ → ProbabilityMeasure (Euc K × Euc K))
    (χn g : ℕ → Euc K → ℝ) (e : 𝒯 → Euc K) (R EK : ℝ),
    RefLaw (μ : Measure (Euc K)) U → Mom1 (P : Measure (Euc K)) ≠ ∞ →
    Measurable Q → (μ : Measure (Euc K)).map Q = P →
    ConvexOn ℝ (interior U) χ → Q =ᵐ[(μ : Measure (Euc K))] gradient χ →
    HardFit μ P U α ν π χn g → (∀ n, ConvexOn ℝ (interior U) (g n)) →
    (∀ n, ∀ u ∈ interior U, Qn n u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n)) u) →
    MeasurableSet A → (∀ᵐ u ∂(μ : Measure (Euc K)).restrict A, ‖Q u‖ ≤ R) → (∀ t, ‖e t‖ ≤ EK) →
      ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t,
        StatFormal.Wave17a.hPop (μ : Measure (Euc K)) A Q (e t) ≤ StatFormal.Wave21b.supE A (Qn n) (e t) + η ∧
          StatFormal.Wave17a.hPop (μ : Measure (Euc K)) A Q (-e t) ≤ StatFormal.Wave21b.supE A (Qn n) (-e t) + η

/-- `cond_test_coverage_potentials` from an exact hard fit: inflated bands containing the fitted band have test coverage
`≥ p` eventually. -/
def cond_test_coverage_plans : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ P : ProbabilityMeasure (Euc K)) (U A : Set (Euc K)) (χ : Euc K → ℝ) (Q : Euc K → Euc K)
    (Qn : ℕ → Euc K → Euc K) (α ν : ℕ → ProbabilityMeasure (Euc K)) (π : ℕ → ProbabilityMeasure (Euc K × Euc K))
    (χn g : ℕ → Euc K → ℝ) (m : 𝒯 → ℝ) (e : 𝒯 → Euc K) (Ue Le : ℕ → 𝒯 → EReal) (R EK p κ : ℝ),
    RefLaw (μ : Measure (Euc K)) U → Mom1 (P : Measure (Euc K)) ≠ ∞ →
    Measurable Q → (μ : Measure (Euc K)).map Q = P →
    ConvexOn ℝ (interior U) χ → Q =ᵐ[(μ : Measure (Euc K))] gradient χ →
    HardFit μ P U α ν π χn g → (∀ n, ConvexOn ℝ (interior U) (g n)) →
    (∀ n, ∀ u ∈ interior U, Qn n u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n)) u) →
    MeasurableSet A → (∀ᵐ u ∂(μ : Measure (Euc K)).restrict A, ‖Q u‖ ≤ R) → (∀ t, ‖e t‖ ≤ EK) →
    ENNReal.ofReal p ≤ (μ : Measure (Euc K)) A → 0 < κ →
    (∀ n t, (m t : EReal) + StatFormal.Wave21b.supE A (Qn n) (e t) ≤ Ue n t ∧
      Le n t ≤ (m t : EReal) - StatFormal.Wave21b.supE A (Qn n) (-e t)) →
      ∀ᶠ n in atTop, ∃ E : Set (Euc K), MeasurableSet E ∧
        E ⊆ {z | ∀ t, Le n t - κ ≤ ((m t + ⟪e t, z⟫ : ℝ) : EReal) ∧ ((m t + ⟪e t, z⟫ : ℝ) : EReal) ≤ Ue n t + κ} ∧
        ENNReal.ofReal p ≤ (μ : Measure (Euc K)).map Q E

/-- `cond_transfer_consistency` from an exact hard fit at `x'`: the frozen claim with its potential premise
("a.s., `g_n` convex on `int 𝒰_K` and `g_n → χ'` uniformly on compacts") replaced by "a.s., an exact hard fit at `x'`
towards `P' = P_{K,x'}` with `g_n` convex on `int 𝒰_K`", `P'` with a first moment and `Q'` Borel with `Q'#μ_K = P'`. -/
def cond_transfer_consistency_plans : Prop :=
  ∀ (K : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (μ P' : ProbabilityMeasure (Euc K)) (U DF : Set (Euc K))
    (Z : Ω → Euc K) (F : Euc K → Euc K) (Fh : ℕ → Ω → Euc K → Euc K) (χ' : Euc K → ℝ) (Q' : Euc K → Euc K)
    (Qh : ℕ → Ω → Euc K → Euc K) (α ν : ℕ → Ω → ProbabilityMeasure (Euc K))
    (π : ℕ → Ω → ProbabilityMeasure (Euc K × Euc K)) (χn g : ℕ → Ω → Euc K → ℝ),
    RefLaw (μ : Measure (Euc K)) U → Measurable Z → Measurable F → P.map (fun ω => F (Z ω)) = μ →
    (∀ᵐ ω ∂P, Z ω ∈ DF) → (∀ᵐ ω ∂P, ∀ z ∈ DF, Tendsto (fun n => Fh n ω z) atTop (𝓝 (F z))) →
    ConvexOn ℝ (interior U) χ' → Q' =ᵐ[(μ : Measure (Euc K))] gradient χ' →
    Mom1 (P' : Measure (Euc K)) ≠ ∞ → Measurable Q' → (μ : Measure (Euc K)).map Q' = P' →
    (∀ᵐ ω ∂P, HardFit μ P' U (fun n => α n ω) (fun n => ν n ω) (fun n => π n ω) (fun n => χn n ω) (fun n => g n ω) ∧
      ∀ n, ConvexOn ℝ (interior U) (g n ω)) →
    (∀ n ω, ∀ u ∈ interior U, Qh n ω u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n ω)) u) →
      ∀ᵐ ω ∂P, F (Z ω) ∈ interior U ∧ DifferentiableAt ℝ χ' (F (Z ω)) ∧ Q' (F (Z ω)) = gradient χ' (F (Z ω)) ∧
        Tendsto (fun n => Qh n ω (Fh n ω (Z ω))) atTop (𝓝 (Q' (F (Z ω))))

/-- `cond_transfer_consistency_prob` from an exact hard fit ("… hence in probability"). -/
def cond_transfer_consistency_prob_plans : Prop :=
  ∀ (K : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] (μ P' : ProbabilityMeasure (Euc K))
    (U DF : Set (Euc K)) (Z : Ω → Euc K) (F : Euc K → Euc K) (Fh : ℕ → Ω → Euc K → Euc K) (χ' : Euc K → ℝ)
    (Q' : Euc K → Euc K) (Qh : ℕ → Ω → Euc K → Euc K) (α ν : ℕ → Ω → ProbabilityMeasure (Euc K))
    (π : ℕ → Ω → ProbabilityMeasure (Euc K × Euc K)) (χn g : ℕ → Ω → Euc K → ℝ),
    RefLaw (μ : Measure (Euc K)) U → Measurable Z → Measurable F → P.map (fun ω => F (Z ω)) = μ →
    (∀ᵐ ω ∂P, Z ω ∈ DF) → (∀ᵐ ω ∂P, ∀ z ∈ DF, Tendsto (fun n => Fh n ω z) atTop (𝓝 (F z))) →
    ConvexOn ℝ (interior U) χ' → Q' =ᵐ[(μ : Measure (Euc K))] gradient χ' →
    Mom1 (P' : Measure (Euc K)) ≠ ∞ → Measurable Q' → (μ : Measure (Euc K)).map Q' = P' →
    (∀ᵐ ω ∂P, HardFit μ P' U (fun n => α n ω) (fun n => ν n ω) (fun n => π n ω) (fun n => χn n ω) (fun n => g n ω) ∧
      ∀ n, ConvexOn ℝ (interior U) (g n ω)) →
    (∀ n ω, ∀ u ∈ interior U, Qh n ω u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n ω)) u) →
    (∀ n, AEStronglyMeasurable (fun ω => Qh n ω (Fh n ω (Z ω))) P) →
      TendstoInMeasure P (fun n ω => Qh n ω (Fh n ω (Z ω))) atTop (fun ω => Q' (F (Z ω)))

end Claims

end StatFormal.OTFD.WaveL3
