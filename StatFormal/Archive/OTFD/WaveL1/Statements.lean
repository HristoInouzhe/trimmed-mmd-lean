import StatFormal.Archive.OTFD.Wave1.Statements
import StatFormal.Archive.OTFD.Wave8b.Statements
import StatFormal.Archive.Wave21b.Statements
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# FROZEN STATEMENTS — otfd wave L1 (OT limit theory): A `lem:plan-stability-H`, the main limit of
# A `prop:integrated-sieve-strong`, A `prop:integrated-quantile`; R `lem:plan-w2`, R `thm:moment-sieve`

Sources (verbatim in `lean-formalisation/inventory/extracted/{otfd-A_sieves,otfd-R_robustness}.md`; current text of
`otfd/papers/`):
* A `lem:plan-stability-H` (`A_sieves/supplement.tex:5145-5168`, proof `subsec:app-plan-stability`, `:1416`).
* A `prop:integrated-sieve-strong` (`A_sieves/main.tex:800-825`), with `def:ghs-rank` (`:721-736`); its last two
  sentences are frozen in Wave 21b (`sieve_strong_radial`, `sieve_strong_signs_prob`, `sieve_strong_signs_L2`, as
  implications from the main limit).
* A `prop:integrated-quantile` (`A_sieves/main.tex:827-843`).
* R `lem:plan-w2` (`R_robustness/sections/s6_references.tex:18-27`) with the setting paragraph (`:11-16`: `𝒫^ℓ(𝓗)`,
  the `μ`-distribution function `F` and "every coupling … concentrated on a cyclically monotone set is induced by it").
* R `thm:moment-sieve` (`s6_references.tex:33-42`, proof outline `:44-51`).
Imports the frozen `OTFD/Wave1` (`PellClass`, `IsLipHyp`, `truncK` = `Π_K`), `OTFD/Wave8b` (`embed` = `ι_K`) and
`Wave21b` (`nsign`, and the three implications it certifies) statements, not copied. Mathlib otherwise.

Covered:
* `lem:plan-stability-H`, separable Hilbert space (uniqueness declared, see below): (a) `plan_stab_a`; (b) `plan_stab_b`;
  "in particular" `plan_stab_b_map`. In `ℝ^d` (uniqueness proved): `plan_stab_fd_a`, `plan_stab_fd_b`,
  `plan_stab_fd_b_map`; the uniqueness itself in `ℝ^d`: `brenier_uniq_fd`.
* `lem:plan-w2`, Hilbert: `plan_w2_a`, `plan_w2_b`, `plan_w2_b_map`; `ℝ^d`: `plan_w2_fd_a`, `plan_w2_fd_b`,
  `plan_w2_fd_b_map`.
* `prop:integrated-sieve-strong`: the main limit `eq:integrated-sieve-strong` (`sieve_strong_limit`) and the whole
  proposition (`sieve_strong_full`: limit, radial ranks in `L²`, signs in probability and in `L²`), for every
  boundedly supported reference.
* `prop:integrated-quantile`: `integrated_quantile`.
* `thm:moment-sieve`: (a) `moment_sieve_a`, (b) `moment_sieve_b`.

Not covered (declared):
* Hilbert space: the uniqueness theorem itself (GHS 2026 / A `lem:app-cm-plans`: for `P ∈ 𝒫^ℓ(H)` every coupling of
  `P` and `μ` concentrated on a cyclically monotone set is induced by `𝔽^μ_P`; for the quantile items, the exchanged
  statement for `(μ, P)` with `𝕼_P`, GHS Lemma 4.3) is the hypothesis `BrenierUniq`; the `𝒫^ℓ` hypotheses are then
  kept for fidelity but unused. Existence of `𝔽^μ_P`, `F_{+,K}`, `Q_{+,K}` (GHS / McCann) is not claimed: they are
  quantified maps with the defining properties.
* `ℝ^d`: `P ∈ 𝒫^ℓ(ℝ^d)` is specialised to `P ≪` Lebesgue, and A's (a),(b) additionally assume `m₂(P) < ∞` (Tau Ceti's
  Brenier uniqueness needs a finite optimal cost; McCann's moment-free uniqueness of monotone maps is missing). So
  A's "no moment" remark is covered only in the Hilbert form (where `m₂(P)` is never used).
* `prop:integrated-sieve-strong`/`prop:integrated-quantile`: the two named references specifically (generalised to
  any boundedly supported `μ`); "no atom at the origin" is the hypothesis `μ{0} = 0`; the ball-law remark (no local
  uniform statement); nonvacuity (`rem:nonvacuity`).
* `thm:sieve-convergence` limit clauses (weak/norm local-uniform subgradient convergence on compacts
  `𝒦₀ ⊆ int dom ∇ψ̃ ∩ int supp P`, and the quantile clauses): still out of reach, see critic notes.
* `thm:moment-sieve`: existence of `F_K`, `Q_K` (`P_K ∈ 𝒫^ℓ(ℝ^K)`); the closing sample-level remarks.

Encodings (to be checked by the critic):
* `H : Type` a real inner-product space, complete, second countable (= separable Hilbert), Borel. `ℝ^d =
  EuclideanSpace ℝ (Fin d)` (`Euc d`), Lebesgue `volume`. Weak (narrow) convergence is convergence in Mathlib's topology
  on `ProbabilityMeasure`; `π_K ∈ Π(α_K, ν_K)` is `π_K.fst = α_K ∧ π_K.snd = ν_K` (Mathlib marginals).
* Cyclical monotonicity is the paper's cycle form `CycMon` (`Σ ⟨y_i, x_{i+1} − x_i⟩ ≤ 0`, `x_{m+1} = x_1`, via
  `finRotate`); "gives full mass to a Borel cyclically monotone set" is `CMConc` (`∃ Γ` measurable, `CycMon Γ`,
  `π Γᶜ = 0`). The routes prove that `CycMon` implies Tau Ceti's permutation form for `‖x − y‖²/2`.
* `𝔽^μ_P` ("the `P`-a.e. unique gradient of a convex function pushing `P` to `μ`"): Hilbert — any measurable `F` with
  `BrenierUniq P μ F` (every CM coupling of `(P, μ)` equals `Graph P F = (Id × F)#P`); `F#P = μ` and the cyclical
  monotonicity of `F` follow (proved in the routes). `ℝ^d` — any measurable `F` with `P.map F = μ` and `IsCMMapAE P F`
  (graph over a Borel `P`-conull set is CM; with `P ≪` Lebesgue, by Rockafellar + Rademacher, exactly "`P`-a.e. the
  gradient of a convex function", allowing potentials that are `+∞` off a convex set — needed for unbounded targets,
  where the frozen `IsConvGradAE` (finite potentials) would make the quantile items vacuous). The same `IsCMMapAE`
  encodes the finite-dimensional maps `F_{+,K}`, `Q_{+,K}`, `F_K`, `Q_K` (generalisation of "gradient") and "`π_K =
  (Id × T_K)#P` concentrated on CM sets" (`T_K` measurable, `T_K#P = ν_K`, `IsCMMapAE P T_K`).
* `supp μ ⊆ B̄(0, M)` is `μ (closedBall 0 M)ᶜ = 0`; "`supp μ` bounded" quantifies `M`. `m₂ = Mom2 = ∫⁻ ‖y‖ₑ²`.
  `W₂`-convergence is `W2Conv`: weak convergence plus `m₂(α_K) → m₂(P)` (Villani, Thm 6.9; equivalent to `W₂ → 0`).
  A (b) omits (a)'s "`supp μ` bounded" (implied by `supp ν_K ⊆ B̄(0, M)` and the portmanteau theorem).
  "Zero mass on Lipschitz hypersurfaces" is `LipNull` (frozen `IsLipHyp`); A's `P ∈ 𝒫^ℓ(H)` with the moment clause
  unused is `LipNull` (generalisation); `P ∈ 𝒫^ℓ` with its second moment (A quantile, R) is the frozen `PellClass`.
* Sieve: `e` orthonormal with dense span (Hilbert basis), `Π_K = truncK e K`, `ι_K = embed e K`, `μ_K = Π_K#μ`
  (`Measure.map`), `P_K = Π_K#P`; `Y_K = ι_K F_{+,K}(Π_K X)`, `X ∼ P`, so `E‖Y_K − Y‖² = ∫⁻ ‖ι_K F_K(Π_K x) − F x‖ₑ² dP`
  (lower integral, no integrability junk); "arbitrary measurable versions" — all maps are measurable and every
  hypothesis is invariant under a.e. modification. Radial ranks are `‖Y_K‖` and signs `nsign c` as in Wave 21b.

Critic notes:
* All 18 claims are proved in `WaveL1/Route{CM,L2,PlanStab,FD,Sieve}.lean` (axioms: propext, Classical.choice,
  Quot.sound). Routes use the untrusted libraries `Foundations/OTLimits` (`eventually_pos_measure_of_tendsto`,
  `tendsto_lintegral_enorm_sub_sq_of_tendsto_graphPlan`, `transportCost_quadCost_ne_top`), Tau Ceti (`Compactness`:
  Prokhorov for couplings; `Brenier`: Knott–Smith optimality of CM plans and uniqueness; Rüschendorf's potential) and
  the certified Wave 21b route `RouteSieveStrong` — routes only.
* Proof structure: (i) supports of weak limits of CM plans are CM (paper form, portmanteau); (ii) tightness of the
  marginals + uniqueness of the CM coupling of the limit marginals ⇒ convergence of the whole sequence; (iii) fixed
  source + moment convergence of the targets ⇒ `L²` concentration on the graph; (iv) coherent truncations converge
  weakly with moments (Hilbert basis, Bessel), and `ι_K ∘ F_K ∘ Π_K` is CM (`⟨ι_K u, x⟩ = ⟨u, Π_K x⟩`).
* No tautology: every conclusion is a limit not among the hypotheses; `BrenierUniq` is a property of the limit pair
  only. It is where the infinite-dimensional depth lies (declared), and it is satisfiable (proved in `ℝ^d`:
  claim `brenier_uniq_fd`).
* `BrenierUniq` is exactly A `lem:app-cm-plans`(iv); A proves it itself, so the Hilbert claims are a genuine
  conditionalisation (on a result of the same paper, not formalised here).
* The `ℝ^d` forms need `P ≪` Lebesgue (narrower than `𝒫^ℓ(ℝ^d)`) and `m₂(P) < ∞`, against A's "no moment" remark;
  that remark is covered only via the Hilbert form.
* `IsCMMapAE` generalises "gradient of a convex function" and is equivalent to it on `LipNull`/`≪ Leb` laws.
* `LipNull` is kept for fidelity but unused in the proofs.
* Paper S3: R `s6_references.tex:13-15` and `appendix_b.tex:70` credit InouzheA for "every CM coupling is induced by
  `F`" for any Borel `μ`, but A proves it only for bounded `μ` (`lem:app-cm-plans`(iv)); for unbounded `μ` it rests on
  GHS2026 alone.
* Paper S4: R's "Following InouzheA, `𝒫^ℓ(𝓗)` denotes …" drops A's second-moment clause, so it actually follows GHS's
  definition.
* No statement was found false. A's remark that (a) needs no uniform support bound and that the sieve limit uses no
  second moment of `P` is confirmed by the Hilbert claims (`plan_stab_a`, `sieve_strong_limit` assume neither).
* `thm:sieve-convergence` limits are skipped: they need (1) convergence of the normalised embedded potentials
  `ψ_K → ψ̃` on `int supp P` in infinite dimension (GHS Lemma 3.4 / Thm 3.1, with uniqueness of potentials up to
  constants), and (2) an infinite-dimensional Rockafellar 24.5 (uniform subgradient convergence over strongly compact
  sets with Gâteaux/Fréchet differentiability of the limit); `Foundations/Convex` is finite-dimensional only.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/
set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.OTFD.WaveL1

open StatFormal.OTFD.Wave1 (PellClass IsLipHyp truncK)
open StatFormal.OTFD.Wave8b (embed)
open StatFormal.Wave21b (nsign)

/-! ### Cyclical monotonicity, couplings, uniqueness -/

section Defs
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `Γ ⊆ E × E` is cyclically monotone: `Σ_{i=1}^m ⟨y_i, x_{i+1} − x_i⟩ ≤ 0` for all `m` and all
`(x_1,y_1), …, (x_m,y_m) ∈ Γ`, with `x_{m+1} := x_1` (`finRotate m` is `i ↦ i + 1 mod m`). -/
def CycMon (Γ : Set (E × E)) : Prop :=
  ∀ (m : ℕ) (z : Fin m → E × E), (∀ i, z i ∈ Γ) →
    ∑ i, ⟪(z i).2, (z (finRotate m i)).1 - (z i).1⟫ ≤ 0

variable [MeasurableSpace E]

/-- `π` gives full mass to a Borel cyclically monotone set. -/
def CMConc (π : Measure (E × E)) : Prop :=
  ∃ Γ : Set (E × E), MeasurableSet Γ ∧ CycMon Γ ∧ π Γᶜ = 0

/-- `G` is `μ`-a.e. a cyclically monotone map: its graph over a Borel `μ`-conull set is cyclically
monotone (by Rockafellar's theorem, `μ`-a.e. a selection of the subdifferential of a convex
function; for `μ ≪ Lebesgue`, `μ`-a.e. the gradient of a convex function). -/
def IsCMMapAE (μ : Measure E) (G : E → E) : Prop :=
  ∃ S : Set E, MeasurableSet S ∧ μ Sᶜ = 0 ∧ CycMon {z : E × E | z.1 ∈ S ∧ z.2 = G z.1}

/-- The graph plan `(Id × F)#P`. -/
def Graph (P : Measure E) (F : E → E) : Measure (E × E) := P.map fun x => (x, F x)

/-- **Brenier–McCann–GHS uniqueness** for `(P, μ)` with map `F`: every coupling of `P` and `μ`
concentrated on a Borel cyclically monotone set is induced by `F`. -/
def BrenierUniq (P μ : Measure E) (F : E → E) : Prop :=
  ∀ π : Measure (E × E), IsProbabilityMeasure π → π.fst = P → π.snd = μ → CMConc π →
    π = Graph P F

/-- `P` gives zero mass to every Lipschitz hypersurface (frozen `IsLipHyp`). -/
def LipNull (P : Measure E) : Prop := ∀ S : Set E, IsLipHyp S → P S = 0

/-- The second moment `m₂(μ) = ∫ ‖y‖² dμ`, in `ℝ≥0∞`. -/
def Mom2 (μ : Measure E) : ℝ≥0∞ := ∫⁻ y, ‖y‖ₑ ^ 2 ∂μ

variable [OpensMeasurableSpace E] in
/-- `α_K → P` in `W₂`: weakly, with converging second moments (Villani, Thm 6.9). -/
def W2Conv (α : ℕ → ProbabilityMeasure E) (P : ProbabilityMeasure E) : Prop :=
  Tendsto α atTop (𝓝 P) ∧
    Tendsto (fun K => Mom2 (α K : Measure E)) atTop (𝓝 (Mom2 (P : Measure E)))

end Defs

/-- `ℝ^K`. -/
abbrev Euc (K : ℕ) := EuclideanSpace ℝ (Fin K)

namespace Claims

/-! #### A `lem:plan-stability-H` in a separable Hilbert space (uniqueness declared) -/

/-- (a) `α_K ⇀ P`, `ν_K ⇀ μ` (`supp μ` bounded), `π_K ∈ Π(α_K, ν_K)` concentrated on Borel cyclically
monotone sets ⇒ `π_K ⇀ (Id × 𝔽^μ_P)#P`. -/
def plan_stab_a : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (P μ : ProbabilityMeasure H) (F : H → H) (M : ℝ) (α ν : ℕ → ProbabilityMeasure H)
    (π : ℕ → ProbabilityMeasure (H × H)) (G : ProbabilityMeasure (H × H)),
    LipNull (P : Measure H) → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
    Measurable F → BrenierUniq (P : Measure H) μ F →
    Tendsto α atTop (𝓝 P) → Tendsto ν atTop (𝓝 μ) →
    (∀ K, (π K : Measure (H × H)).fst = α K) → (∀ K, (π K : Measure (H × H)).snd = ν K) →
    (∀ K, CMConc (π K : Measure (H × H))) →
    (G : Measure (H × H)) = Graph (P : Measure H) F →
      Tendsto π atTop (𝓝 G)

/-- (b) With `α_K = P` and `supp ν_K ⊆ B̄(0, M)`: `∫ ‖y − 𝔽^μ_P(x)‖² dπ_K → 0`. -/
def plan_stab_b : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (P μ : ProbabilityMeasure H) (F : H → H) (M : ℝ) (ν : ℕ → ProbabilityMeasure H)
    (π : ℕ → ProbabilityMeasure (H × H)),
    LipNull (P : Measure H) → Measurable F → BrenierUniq (P : Measure H) μ F →
    Tendsto ν atTop (𝓝 μ) → (∀ K, (ν K : Measure H) (Metric.closedBall 0 M)ᶜ = 0) →
    (∀ K, (π K : Measure (H × H)).fst = P) → (∀ K, (π K : Measure (H × H)).snd = ν K) →
    (∀ K, CMConc (π K : Measure (H × H))) →
      Tendsto (fun K => ∫⁻ z, ‖z.2 - F z.1‖ₑ ^ 2 ∂(π K : Measure (H × H))) atTop (𝓝 0)

/-- (b), "in particular": for `π_K = (Id × T_K)#P` with Borel `T_K`, `‖T_K − 𝔽^μ_P‖_{L²(P)} → 0`. -/
def plan_stab_b_map : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (P μ : ProbabilityMeasure H) (F : H → H) (M : ℝ) (ν : ℕ → ProbabilityMeasure H)
    (T : ℕ → H → H),
    LipNull (P : Measure H) → Measurable F → BrenierUniq (P : Measure H) μ F →
    Tendsto ν atTop (𝓝 μ) → (∀ K, (ν K : Measure H) (Metric.closedBall 0 M)ᶜ = 0) →
    (∀ K, Measurable (T K)) → (∀ K, (P : Measure H).map (T K) = ν K) →
    (∀ K, IsCMMapAE (P : Measure H) (T K)) →
      Tendsto (fun K => ∫⁻ x, ‖T K x - F x‖ₑ ^ 2 ∂(P : Measure H)) atTop (𝓝 0)

/-! #### A `lem:plan-stability-H` in `ℝ^d` (uniqueness proved; `P ≪ Leb`, `m₂(P) < ∞`) -/

/-- Uniqueness of cyclically monotone couplings in `ℝ^d` (Brenier–McCann): for `P ≪ Leb` with
`m₂(P), m₂(μ) < ∞` and any Borel `F`, `P`-a.e. cyclically monotone, pushing `P` to `μ`, `BrenierUniq P μ F` holds. -/
def brenier_uniq_fd : Prop :=
  ∀ (d : ℕ) (P μ : ProbabilityMeasure (Euc d)) (F : Euc d → Euc d),
    (P : Measure (Euc d)) ≪ volume → Mom2 (P : Measure (Euc d)) ≠ ∞ → Mom2 (μ : Measure (Euc d)) ≠ ∞ →
    Measurable F → (P : Measure (Euc d)).map F = μ → IsCMMapAE (P : Measure (Euc d)) F →
      BrenierUniq (P : Measure (Euc d)) μ F

/-- (a) in `ℝ^d`, with `𝔽^μ_P` any Borel map, `P`-a.e. cyclically monotone, pushing `P` to `μ`. -/
def plan_stab_fd_a : Prop :=
  ∀ (d : ℕ) (P μ : ProbabilityMeasure (Euc d)) (F : Euc d → Euc d) (M : ℝ)
    (α ν : ℕ → ProbabilityMeasure (Euc d)) (π : ℕ → ProbabilityMeasure (Euc d × Euc d))
    (G : ProbabilityMeasure (Euc d × Euc d)),
    (P : Measure (Euc d)) ≪ volume → Mom2 (P : Measure (Euc d)) ≠ ∞ →
    (μ : Measure (Euc d)) (Metric.closedBall 0 M)ᶜ = 0 →
    Measurable F → (P : Measure (Euc d)).map F = μ → IsCMMapAE (P : Measure (Euc d)) F →
    Tendsto α atTop (𝓝 P) → Tendsto ν atTop (𝓝 μ) →
    (∀ K, (π K : Measure (Euc d × Euc d)).fst = α K) →
    (∀ K, (π K : Measure (Euc d × Euc d)).snd = ν K) →
    (∀ K, CMConc (π K : Measure (Euc d × Euc d))) →
    (G : Measure (Euc d × Euc d)) = Graph (P : Measure (Euc d)) F →
      Tendsto π atTop (𝓝 G)

/-- (b) in `ℝ^d`. -/
def plan_stab_fd_b : Prop :=
  ∀ (d : ℕ) (P μ : ProbabilityMeasure (Euc d)) (F : Euc d → Euc d) (M : ℝ)
    (ν : ℕ → ProbabilityMeasure (Euc d)) (π : ℕ → ProbabilityMeasure (Euc d × Euc d)),
    (P : Measure (Euc d)) ≪ volume → Mom2 (P : Measure (Euc d)) ≠ ∞ →
    Measurable F → (P : Measure (Euc d)).map F = μ → IsCMMapAE (P : Measure (Euc d)) F →
    Tendsto ν atTop (𝓝 μ) → (∀ K, (ν K : Measure (Euc d)) (Metric.closedBall 0 M)ᶜ = 0) →
    (∀ K, (π K : Measure (Euc d × Euc d)).fst = P) →
    (∀ K, (π K : Measure (Euc d × Euc d)).snd = ν K) →
    (∀ K, CMConc (π K : Measure (Euc d × Euc d))) →
      Tendsto (fun K => ∫⁻ z, ‖z.2 - F z.1‖ₑ ^ 2 ∂(π K : Measure (Euc d × Euc d))) atTop (𝓝 0)

/-- (b), "in particular", in `ℝ^d`. -/
def plan_stab_fd_b_map : Prop :=
  ∀ (d : ℕ) (P μ : ProbabilityMeasure (Euc d)) (F : Euc d → Euc d) (M : ℝ)
    (ν : ℕ → ProbabilityMeasure (Euc d)) (T : ℕ → Euc d → Euc d),
    (P : Measure (Euc d)) ≪ volume → Mom2 (P : Measure (Euc d)) ≠ ∞ →
    Measurable F → (P : Measure (Euc d)).map F = μ → IsCMMapAE (P : Measure (Euc d)) F →
    Tendsto ν atTop (𝓝 μ) → (∀ K, (ν K : Measure (Euc d)) (Metric.closedBall 0 M)ᶜ = 0) →
    (∀ K, Measurable (T K)) → (∀ K, (P : Measure (Euc d)).map (T K) = ν K) →
    (∀ K, IsCMMapAE (P : Measure (Euc d)) (T K)) →
      Tendsto (fun K => ∫⁻ x, ‖T K x - F x‖ₑ ^ 2 ∂(P : Measure (Euc d))) atTop (𝓝 0)

/-! #### R `lem:plan-w2` in a separable Hilbert space (uniqueness declared, as the paper's setting states) -/

/-- (a) `α_K → P`, `ν_K → μ` in `W₂`, `π_K ∈ Π(α_K, ν_K)` concentrated on cyclically monotone sets ⇒
`π_K → (Id × F)#P` narrowly. -/
def plan_w2_a : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (P μ : ProbabilityMeasure H) (F : H → H) (α ν : ℕ → ProbabilityMeasure H)
    (π : ℕ → ProbabilityMeasure (H × H)) (G : ProbabilityMeasure (H × H)),
    PellClass (P : Measure H) → Mom2 (μ : Measure H) ≠ ∞ →
    Measurable F → BrenierUniq (P : Measure H) μ F →
    W2Conv α P → W2Conv ν μ →
    (∀ K, (π K : Measure (H × H)).fst = α K) → (∀ K, (π K : Measure (H × H)).snd = ν K) →
    (∀ K, CMConc (π K : Measure (H × H))) →
    (G : Measure (H × H)) = Graph (P : Measure H) F →
      Tendsto π atTop (𝓝 G)

/-- (b) If `α_K = P`: `∫ ‖y − F(x)‖² dπ_K → 0`. -/
def plan_w2_b : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (P μ : ProbabilityMeasure H) (F : H → H) (ν : ℕ → ProbabilityMeasure H)
    (π : ℕ → ProbabilityMeasure (H × H)),
    PellClass (P : Measure H) → Mom2 (μ : Measure H) ≠ ∞ →
    Measurable F → BrenierUniq (P : Measure H) μ F → W2Conv ν μ →
    (∀ K, (π K : Measure (H × H)).fst = P) → (∀ K, (π K : Measure (H × H)).snd = ν K) →
    (∀ K, CMConc (π K : Measure (H × H))) →
      Tendsto (fun K => ∫⁻ z, ‖z.2 - F z.1‖ₑ ^ 2 ∂(π K : Measure (H × H))) atTop (𝓝 0)

/-- (b), "in particular": `π_K = (Id × T_K)#P` ⇒ `T_K → F` in `L²(P; 𝓗)`. -/
def plan_w2_b_map : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (P μ : ProbabilityMeasure H) (F : H → H) (ν : ℕ → ProbabilityMeasure H) (T : ℕ → H → H),
    PellClass (P : Measure H) → Mom2 (μ : Measure H) ≠ ∞ →
    Measurable F → BrenierUniq (P : Measure H) μ F → W2Conv ν μ →
    (∀ K, Measurable (T K)) → (∀ K, (P : Measure H).map (T K) = ν K) →
    (∀ K, IsCMMapAE (P : Measure H) (T K)) →
      Tendsto (fun K => ∫⁻ x, ‖T K x - F x‖ₑ ^ 2 ∂(P : Measure H)) atTop (𝓝 0)

/-! #### R `lem:plan-w2` in `ℝ^d` (uniqueness proved; `P ≪ Leb`) -/

/-- (a) in `ℝ^d`. -/
def plan_w2_fd_a : Prop :=
  ∀ (d : ℕ) (P μ : ProbabilityMeasure (Euc d)) (F : Euc d → Euc d)
    (α ν : ℕ → ProbabilityMeasure (Euc d)) (π : ℕ → ProbabilityMeasure (Euc d × Euc d))
    (G : ProbabilityMeasure (Euc d × Euc d)),
    (P : Measure (Euc d)) ≪ volume → Mom2 (P : Measure (Euc d)) ≠ ∞ → Mom2 (μ : Measure (Euc d)) ≠ ∞ →
    Measurable F → (P : Measure (Euc d)).map F = μ → IsCMMapAE (P : Measure (Euc d)) F →
    W2Conv α P → W2Conv ν μ →
    (∀ K, (π K : Measure (Euc d × Euc d)).fst = α K) →
    (∀ K, (π K : Measure (Euc d × Euc d)).snd = ν K) →
    (∀ K, CMConc (π K : Measure (Euc d × Euc d))) →
    (G : Measure (Euc d × Euc d)) = Graph (P : Measure (Euc d)) F →
      Tendsto π atTop (𝓝 G)

/-- (b) in `ℝ^d`. -/
def plan_w2_fd_b : Prop :=
  ∀ (d : ℕ) (P μ : ProbabilityMeasure (Euc d)) (F : Euc d → Euc d)
    (ν : ℕ → ProbabilityMeasure (Euc d)) (π : ℕ → ProbabilityMeasure (Euc d × Euc d)),
    (P : Measure (Euc d)) ≪ volume → Mom2 (P : Measure (Euc d)) ≠ ∞ → Mom2 (μ : Measure (Euc d)) ≠ ∞ →
    Measurable F → (P : Measure (Euc d)).map F = μ → IsCMMapAE (P : Measure (Euc d)) F →
    W2Conv ν μ →
    (∀ K, (π K : Measure (Euc d × Euc d)).fst = P) →
    (∀ K, (π K : Measure (Euc d × Euc d)).snd = ν K) →
    (∀ K, CMConc (π K : Measure (Euc d × Euc d))) →
      Tendsto (fun K => ∫⁻ z, ‖z.2 - F z.1‖ₑ ^ 2 ∂(π K : Measure (Euc d × Euc d))) atTop (𝓝 0)

/-- (b), "in particular", in `ℝ^d`. -/
def plan_w2_fd_b_map : Prop :=
  ∀ (d : ℕ) (P μ : ProbabilityMeasure (Euc d)) (F : Euc d → Euc d)
    (ν : ℕ → ProbabilityMeasure (Euc d)) (T : ℕ → Euc d → Euc d),
    (P : Measure (Euc d)) ≪ volume → Mom2 (P : Measure (Euc d)) ≠ ∞ → Mom2 (μ : Measure (Euc d)) ≠ ∞ →
    Measurable F → (P : Measure (Euc d)).map F = μ → IsCMMapAE (P : Measure (Euc d)) F →
    W2Conv ν μ →
    (∀ K, Measurable (T K)) → (∀ K, (P : Measure (Euc d)).map (T K) = ν K) →
    (∀ K, IsCMMapAE (P : Measure (Euc d)) (T K)) →
      Tendsto (fun K => ∫⁻ x, ‖T K x - F x‖ₑ ^ 2 ∂(P : Measure (Euc d))) atTop (𝓝 0)

/-! #### Sieve limits: A `prop:integrated-sieve-strong` (main limit), A `prop:integrated-quantile`,
R `thm:moment-sieve` -/

/-- A `eq:integrated-sieve-strong`: `E‖ι_K F_{+,K}(Π_K X) − 𝔽_P(X)‖² → 0`, `X ∼ P`, for a boundedly supported
reference `μ`, `μ_K = Π_K#μ`, `F_{+,K}` any Borel map, `P_K`-a.e. cyclically monotone, pushing `P_K` to `μ_K`. -/
def sieve_strong_limit : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (P μ : ProbabilityMeasure H) (F : H → H) (M : ℝ) (FK : (K : ℕ) → Euc K → Euc K),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    LipNull (P : Measure H) → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
    Measurable F → BrenierUniq (P : Measure H) μ F →
    (∀ K, Measurable (FK K)) →
    (∀ K, ((P : Measure H).map (truncK e K)).map (FK K) = (μ : Measure H).map (truncK e K)) →
    (∀ K, IsCMMapAE ((P : Measure H).map (truncK e K)) (FK K)) →
      Tendsto (fun K => ∫⁻ x, ‖embed e K (FK K (truncK e K x)) - F x‖ₑ ^ 2 ∂(P : Measure H))
        atTop (𝓝 0)

/-- A `prop:integrated-sieve-strong`, whole statement: the main limit together with its "Consequently"
sentences (frozen in Wave 21b as implications): radial ranks converge in `L²` and, the reference having no atom
at the origin, the normalized signs (any convention `c` at `0`) converge in probability and in `L²`. -/
def sieve_strong_full : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (P μ : ProbabilityMeasure H) (F : H → H) (M : ℝ) (FK : (K : ℕ) → Euc K → Euc K)
    (c : H),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    LipNull (P : Measure H) → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 → (μ : Measure H) {0} = 0 →
    Measurable F → BrenierUniq (P : Measure H) μ F →
    (∀ K, Measurable (FK K)) →
    (∀ K, ((P : Measure H).map (truncK e K)).map (FK K) = (μ : Measure H).map (truncK e K)) →
    (∀ K, IsCMMapAE ((P : Measure H).map (truncK e K)) (FK K)) →
      Tendsto (fun K => ∫⁻ x, ‖‖embed e K (FK K (truncK e K x))‖ - ‖F x‖‖ₑ ^ 2 ∂(P : Measure H))
          atTop (𝓝 0) ∧
        TendstoInMeasure (P : Measure H) (fun K x => nsign c (embed e K (FK K (truncK e K x))))
          atTop (fun x => nsign c (F x)) ∧
        Tendsto (fun K => ∫⁻ x, ‖nsign c (embed e K (FK K (truncK e K x))) - nsign c (F x)‖ₑ ^ 2
          ∂(P : Measure H)) atTop (𝓝 0)

/-- A `prop:integrated-quantile`: `E‖ι_K Q_{+,K}(Π_K U) − 𝕼_P(U)‖² → 0`, `U ∼ μ`, `μ` boundedly supported,
`P ∈ 𝒫^ℓ(H)` with its second moment, `Q_{+,K}` any Borel map, `μ_K`-a.e. cyclically monotone, pushing `μ_K`
to `P_K`. -/
def integrated_quantile : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (P μ : ProbabilityMeasure H) (Q : H → H) (M : ℝ) (QK : (K : ℕ) → Euc K → Euc K),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    PellClass (P : Measure H) → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
    Measurable Q → BrenierUniq (μ : Measure H) P Q →
    (∀ K, Measurable (QK K)) →
    (∀ K, ((μ : Measure H).map (truncK e K)).map (QK K) = (P : Measure H).map (truncK e K)) →
    (∀ K, IsCMMapAE ((μ : Measure H).map (truncK e K)) (QK K)) →
      Tendsto (fun K => ∫⁻ u, ‖embed e K (QK K (truncK e K u)) - Q u‖ₑ ^ 2 ∂(μ : Measure H))
        atTop (𝓝 0)

/-- R `thm:moment-sieve`(a): `m₂(μ) < ∞`, `P ∈ 𝒫^ℓ(𝓗)` (with `m₂(P) < ∞`): `E‖ι_K F_K(Π_K X) − F(X)‖² → 0`. -/
def moment_sieve_a : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (P μ : ProbabilityMeasure H) (F : H → H) (FK : (K : ℕ) → Euc K → Euc K),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    PellClass (P : Measure H) → Mom2 (μ : Measure H) ≠ ∞ →
    Measurable F → BrenierUniq (P : Measure H) μ F →
    (∀ K, Measurable (FK K)) →
    (∀ K, ((P : Measure H).map (truncK e K)).map (FK K) = (μ : Measure H).map (truncK e K)) →
    (∀ K, IsCMMapAE ((P : Measure H).map (truncK e K)) (FK K)) →
      Tendsto (fun K => ∫⁻ x, ‖embed e K (FK K (truncK e K x)) - F x‖ₑ ^ 2 ∂(P : Measure H))
        atTop (𝓝 0)

/-- R `thm:moment-sieve`(b): if moreover `μ ∈ 𝒫^ℓ(𝓗)`: `E‖ι_K Q_K(Π_K U) − Q(U)‖² → 0`, `U ∼ μ`. -/
def moment_sieve_b : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (P μ : ProbabilityMeasure H) (Q : H → H) (QK : (K : ℕ) → Euc K → Euc K),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    PellClass (P : Measure H) → PellClass (μ : Measure H) →
    Measurable Q → BrenierUniq (μ : Measure H) P Q →
    (∀ K, Measurable (QK K)) →
    (∀ K, ((μ : Measure H).map (truncK e K)).map (QK K) = (P : Measure H).map (truncK e K)) →
    (∀ K, IsCMMapAE ((μ : Measure H).map (truncK e K)) (QK K)) →
      Tendsto (fun K => ∫⁻ u, ‖embed e K (QK K (truncK e K u)) - Q u‖ₑ ^ 2 ∂(μ : Measure H))
        atTop (𝓝 0)

end Claims

end StatFormal.OTFD.WaveL1
