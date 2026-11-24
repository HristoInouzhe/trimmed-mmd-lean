import StatFormal.Archive.OTFD.WaveL3.Statements
import StatFormal.Archive.Wave23d.Statements

/-!
# FROZEN STATEMENTS — otfd limits wave L7 (discharges): moment-free uniqueness of the cyclically monotone coupling in
# `H` for a bounded target (A `lem:app-cm-plans`(iv), GHS Cor. 2.7); the five A limit claims without `m₁(P) < ∞`

Sources (verbatim in `lean-formalisation/inventory/extracted/otfd-A_sieves.md`; current text of `otfd/papers/`):
* A `lem:app-cm-plans`(iv) (`A_sieves/supplement.tex:1429-1472`, proof `:1474-1610`; uniqueness via GHS Cor. 2.7,
  `cor:app-ghs-lipschitz`, `:1067-1078`), used by `lem:plan-stability-H` and `prop:integrated-sieve-strong`;
  A `def:app-lipschitz-hypersurface` (`:931-943`: "the moment clause is not used").
* The frozen wave-L3 claims (`OTFD/WaveL3/Statements.lean`) `brenier_uniq_H_bdd`, `plan_stab_a_uncond`,
  `plan_stab_b_uncond`, `plan_stab_b_map_uncond`, `sieve_strong_limit_uncond`, `sieve_strong_full_uncond`, each with
  the added first moment `Mom1 P ≠ ∞` (declared there as the remaining restriction against A).
* The frozen wave-23d claims (`Wave23d/Statements.lean`) `cm_unique_cond` (conditional on the declared premise
  `GHSGradUnique`), `ghs_grad_unique_m1` and `cm_unique_uncond` (both with `Mom1 A ≠ ∞`).
Imports the frozen `OTFD/WaveL3` (`Mom1`; through it `OTFD/WaveL1` `CMConc`, `IsCMMapAE`, `Graph`, `BrenierUniq`,
`LipNull`, `OTFD/Wave1` `truncK`, `OTFD/Wave8b` `embed`, `Wave21b` `nsign`) and `Wave23d` (`GHSGradUnique`) statements,
not copied. Mathlib otherwise.

Covered:
* `brenier_uniq_H_bdd`: A `lem:app-cm-plans`(iv) uniqueness exactly as printed — `P` null on Lipschitz hypersurfaces,
  target carried by `B̄(0, M)`, NO moment: every coupling of `P` and `μ` concentrated on a Borel cyclically monotone
  set is `(Id × F)#P`.
* The five A items without the first moment (exactly the frozen wave-L1 claims with `BrenierUniq` replaced by
  `F#P = μ ∧ IsCMMapAE P F`, as in wave L3 but with `Mom1 P ≠ ∞` deleted): `plan_stab_a_uncond`,
  `plan_stab_b_uncond`, `plan_stab_b_map_uncond`, `sieve_strong_limit_uncond`, `sieve_strong_full_uncond`.
* GHS Cor. 2.7 for finite convex Lipschitz potentials (the premise `GHSGradUnique` of the frozen `cm_unique_cond`),
  moment-free and for EVERY target `B`: `ghs_grad_unique`; hence `cm_unique_uncond` (A (iv) uniqueness in the
  wave-23d form, no moment, no premise).

Not covered (declared):
* Unbounded targets without moments (GHS for proper l.s.c. potentials that may take the value `+∞`; the route needs
  finite continuous potentials, which Rockafellar's construction gives only for bounded slopes, i.e. bounded
  targets). The exchanged forms (`brenier_uniq_bdd_source`, bounded Lipschitz-null *source*, first moment of the
  target) keep their moment.
* `integrated_quantile_uncond`, `plan_w2_*`, `moment_sieve_*`: their frozen forms already assume second moments
  (`PellClass` / R's standing setting), so nothing to remove.

Encodings (to be checked by the critic):
* Every claim is the frozen claim of the same name (wave L3 or wave 23d) with the moment hypothesis
  `Mom1 _ ≠ ∞` deleted; `ghs_grad_unique` is the frozen `ghs_grad_unique_m1` with `Mom1 A ≠ ∞` AND the bound
  `B (closedBall 0 M)ᶜ = 0` deleted. Only the moment deletion is substantive: an `L`-Lipschitz `f` has Gâteaux
  gradients of norm `≤ L`, so `T#A = B` already forces `B` to be carried by `B̄(0, L)`; "every `B`" is the bounded
  case restated. As in the frozen `GHSGradUnique`, uniqueness is among finite convex Lipschitz potentials only (not
  among all proper l.s.c. convex `ψ` as in GHS Cor. 2.7); that is all A's proof of (iv) uses. All objects are the
  imported frozen ones.

Critic notes:
* Proved in `OTFD/WaveL7/Route{McCann,Claims}.lean` with the untrusted library `Foundations/McCannH/Uniqueness`
  (McCann's moment-free argument: with `u = φ₁ − φ₂`, `v = φ₂* − φ₁*`, `u(x) ≤ v(y)` along one coupling and `≥` along
  the other; equal laws of `u(x)` and `v(y)` under both couplings force equality a.e. by comparing tails, with no
  integration; then both couplings are carried by `∂φ₁`, single-valued `P`-a.e. on Lipschitz-null laws), the
  certified wave-23d `cm_rockafellar_thm` (finite `M`-Lipschitz Rockafellar potentials), `subgrad_of_gatDiff`,
  `cm_unique_cond_thm`, the certified wave-L1 limit theorems, and the library `Potentials/HilbertUniqueness`.
* No tautology: the conclusions (equality of couplings / a.e. equality of maps / limits) are not among the
  hypotheses. No junk: `Measure.map` only of assumed-measurable maps or continuous `truncK`; no moments appear. The
  `EReal` conjugates live only in the untrusted library (each `φᵢ*` is finite `ν`-a.e. because a coupling is carried
  by `∂φᵢ`, and `toReal` is used only on that set), not in any statement.
* Nonvacuity, and strictly stronger than wave L3: `H = ℝ` (Lipschitz hypersurfaces are points, so `LipNull` =
  atomless), `P` the standard Cauchy law (`Mom1 P = ∞`), `F = arctan` (monotone, hence cyclically monotone),
  `μ = F#P` uniform on `(-π/2, π/2)`, `M = 2`: every hypothesis of `brenier_uniq_H_bdd` holds while the frozen wave-L3
  form is vacuous there; `γ = (Id × F)#P` does the same for `cm_unique_uncond`; `f(x) = √(1 + x²)` (1-Lipschitz,
  convex, differentiable) for `ghs_grad_unique`.
* Critic (2026-10-16): ACCEPT. Mechanical diff: each claim equals its frozen original with exactly the moment
  hypothesis deleted (`ghs_grad_unique`: also the automatic target bound); typechecked `Claims.X → frozen X` by
  `fun h … _ => h …` for all eight, so every name resolves to the same frozen object.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/
set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.OTFD.WaveL7

open StatFormal.OTFD.WaveL1 (CMConc IsCMMapAE Graph BrenierUniq LipNull Euc)
open StatFormal.OTFD.Wave1 (truncK)
open StatFormal.OTFD.Wave8b (embed)
open StatFormal.Wave21b (nsign)
open StatFormal.Wave23d (GHSGradUnique)

namespace Claims

/-! #### A `lem:app-cm-plans`(iv): bounded target, no moment -/

/-- A `lem:app-cm-plans`(iv) uniqueness (bounded target), moment-free as printed: `P` null on Lipschitz
hypersurfaces, `μ` carried by `B̄(0, M)`, `F` Borel, `P`-a.e. cyclically monotone, `F#P = μ` ⇒ every coupling of
`P` and `μ` concentrated on a Borel cyclically monotone set is `(Id × F)#P`. -/
def brenier_uniq_H_bdd : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (P μ : ProbabilityMeasure H) (F : H → H) (M : ℝ),
    LipNull (P : Measure H) → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
    Measurable F → (P : Measure H).map F = μ → IsCMMapAE (P : Measure H) F →
      BrenierUniq (P : Measure H) μ F

/-! #### Unconditional, moment-free A `lem:plan-stability-H` -/

/-- `plan_stab_a` without `BrenierUniq` and without a moment of `P` (as printed in A). -/
def plan_stab_a_uncond : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (P μ : ProbabilityMeasure H) (F : H → H) (M : ℝ) (α ν : ℕ → ProbabilityMeasure H)
    (π : ℕ → ProbabilityMeasure (H × H)) (G : ProbabilityMeasure (H × H)),
    LipNull (P : Measure H) → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
    Measurable F → (P : Measure H).map F = μ → IsCMMapAE (P : Measure H) F →
    Tendsto α atTop (𝓝 P) → Tendsto ν atTop (𝓝 μ) →
    (∀ K, (π K : Measure (H × H)).fst = α K) → (∀ K, (π K : Measure (H × H)).snd = ν K) →
    (∀ K, CMConc (π K : Measure (H × H))) →
    (G : Measure (H × H)) = Graph (P : Measure H) F →
      Tendsto π atTop (𝓝 G)

/-- `plan_stab_b` without `BrenierUniq` and without a moment of `P`. -/
def plan_stab_b_uncond : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (P μ : ProbabilityMeasure H) (F : H → H) (M : ℝ) (ν : ℕ → ProbabilityMeasure H)
    (π : ℕ → ProbabilityMeasure (H × H)),
    LipNull (P : Measure H) →
    Measurable F → (P : Measure H).map F = μ → IsCMMapAE (P : Measure H) F →
    Tendsto ν atTop (𝓝 μ) → (∀ K, (ν K : Measure H) (Metric.closedBall 0 M)ᶜ = 0) →
    (∀ K, (π K : Measure (H × H)).fst = P) → (∀ K, (π K : Measure (H × H)).snd = ν K) →
    (∀ K, CMConc (π K : Measure (H × H))) →
      Tendsto (fun K => ∫⁻ z, ‖z.2 - F z.1‖ₑ ^ 2 ∂(π K : Measure (H × H))) atTop (𝓝 0)

/-- `plan_stab_b_map` without `BrenierUniq` and without a moment of `P`. -/
def plan_stab_b_map_uncond : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (P μ : ProbabilityMeasure H) (F : H → H) (M : ℝ) (ν : ℕ → ProbabilityMeasure H)
    (T : ℕ → H → H),
    LipNull (P : Measure H) →
    Measurable F → (P : Measure H).map F = μ → IsCMMapAE (P : Measure H) F →
    Tendsto ν atTop (𝓝 μ) → (∀ K, (ν K : Measure H) (Metric.closedBall 0 M)ᶜ = 0) →
    (∀ K, Measurable (T K)) → (∀ K, (P : Measure H).map (T K) = ν K) →
    (∀ K, IsCMMapAE (P : Measure H) (T K)) →
      Tendsto (fun K => ∫⁻ x, ‖T K x - F x‖ₑ ^ 2 ∂(P : Measure H)) atTop (𝓝 0)

/-! #### Unconditional, moment-free A `prop:integrated-sieve-strong` -/

/-- `sieve_strong_limit` without `BrenierUniq` and without a moment of `P` (as printed in A). -/
def sieve_strong_limit_uncond : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (P μ : ProbabilityMeasure H) (F : H → H) (M : ℝ) (FK : (K : ℕ) → Euc K → Euc K),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    LipNull (P : Measure H) → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
    Measurable F → (P : Measure H).map F = μ → IsCMMapAE (P : Measure H) F →
    (∀ K, Measurable (FK K)) →
    (∀ K, ((P : Measure H).map (truncK e K)).map (FK K) = (μ : Measure H).map (truncK e K)) →
    (∀ K, IsCMMapAE ((P : Measure H).map (truncK e K)) (FK K)) →
      Tendsto (fun K => ∫⁻ x, ‖embed e K (FK K (truncK e K x)) - F x‖ₑ ^ 2 ∂(P : Measure H))
        atTop (𝓝 0)

/-- `sieve_strong_full` without `BrenierUniq` and without a moment of `P`. -/
def sieve_strong_full_uncond : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (P μ : ProbabilityMeasure H) (F : H → H) (M : ℝ) (FK : (K : ℕ) → Euc K → Euc K)
    (c : H),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    LipNull (P : Measure H) → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
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

/-! #### Wave-23d form: GHS Cor. 2.7 and (iv) uniqueness, moment-free -/

/-- GHS Cor. 2.7's uniqueness clause for finite convex Lipschitz potentials (the premise `GHSGradUnique` of the frozen
`cm_unique_cond`), DISCHARGED without any moment and with no bound on `B` assumed (none is needed: Lipschitz
potentials have gradients bounded by their constants, so such a `B` is boundedly supported): for a probability `A`
null on Lipschitz hypersurfaces, two Borel maps that are `A`-a.e. Gâteaux gradients of finite convex Lipschitz
functions and push `A` to `B` agree `A`-a.e. -/
def ghs_grad_unique : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (A B : Measure H), IsProbabilityMeasure A → LipNull A → GHSGradUnique A B

/-- (iv), uniqueness, UNCONDITIONAL and moment-free (as printed): with `γ²` carried by `B̄(0, M)`, `γ` is the only
element of `Π(A, γ²)` concentrated on a cyclically monotone set. -/
def cm_unique_uncond : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (γ γ' : Measure (H × H)) (M : ℝ), IsProbabilityMeasure γ →
    IsProbabilityMeasure γ' → γ'.fst = γ.fst → γ'.snd = γ.snd → LipNull γ.fst →
    γ.snd (Metric.closedBall 0 M)ᶜ = 0 → CMConc γ → CMConc γ' → γ' = γ

end Claims

end StatFormal.OTFD.WaveL7
