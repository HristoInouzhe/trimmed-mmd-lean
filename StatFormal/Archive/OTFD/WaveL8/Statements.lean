import StatFormal.Archive.OTFD.WaveL1.Statements
import StatFormal.Archive.OTFD.WaveL3.Statements
import StatFormal.Archive.OTFD.WaveL4.Statements
import StatFormal.Archive.OTFD.WaveL5.Statements
import StatFormal.Archive.OTFD.WaveL6.Statements
import StatFormal.Archive.Wave23b.Statements
import StatFormal.Archive.Wave24c.Statements
import StatFormal.Archive.Wave24e.Statements
import StatFormal.Archive.Wave24f.Statements

/-!
# FROZEN STATEMENTS — otfd limits wave L8 (discharges): moment-free uniqueness of the cyclically monotone coupling in
# `H` for EVERY target (McCann with extended-valued potentials); 35 frozen claims with their moment deleted

Sources (verbatim in `lean-formalisation/inventory/extracted/{otfd-A_sieves,otfd-R_robustness,otfd-C_conditional}.md`;
current text of `otfd/papers/`):
* A `lem:app-cm-plans`(iv) and (viii) (`A_sieves/supplement.tex:1429-1610`; GHS Cor. 2.7 and Lemma 4.3, which assume
  no moment but a bounded target; A `def:app-lipschitz-hypersurface`: "the moment clause is not used"). GHS Thm 2.3
  (Bernoulli 2026) has no moment and any target, but its uniqueness (ii) is only among `∇f` with `P(int dom f) = 1`;
  McCann, Duke Math. J. 80 (1995), Main Theorem (uniqueness with no moments).
* The frozen claims restated, each with ONLY its moment hypothesis deleted: wave L1 (`OTFD/WaveL1/Statements.lean`)
  `brenier_uniq_fd`, `plan_stab_fd_a/_b/_b_map`; wave L3 `brenier_uniq_H`, `brenier_uniq_H_swap`,
  `brenier_uniq_bdd_source`, `plan_stab_w1`, `cond_potentials`, `cond_{maps_ae,band_one_sided,test_coverage,
  transfer_consistency,transfer_consistency_prob}_plans`; wave L4 the twelve `cond_*_inexact`, `cond_*_weighted`; wave
  L5 `ghs_inverse_H`; wave L6 `sieve_conv_weak`, `sieve_conv_norm`, `sieve_conv_norm_cube`; wave 23b
  `convref_a_uncond`, `convref_b_uncond`; wave 24c `equivariance_unitary`; wave 24e `cond_rank_consistency_uncond`;
  wave 24f `app_sample_rate`.
Imports those nine frozen statement files, not copied (every object — `BrenierUniq`, `CMConc`, `IsCMMapAE`, `LipNull`,
`Graph`, `RefLaw`, `HardFit`, `InexactFit`, `WeightedFit`, `truncK`, `embed`, … — is the imported frozen one; each
section re-opens exactly the namespaces its source file opened). No new definitions.

Covered:
* Uniqueness with NO moment and NO bound on the target: `brenier_uniq_H` (`m₂(P), m₂(μ)` deleted), `brenier_uniq_H_swap`
  (both `m₂` deleted; Lipschitz-null target), `brenier_uniq_bdd_source` (`m₁(P)` deleted), `brenier_uniq_fd` (`P ≪ Leb`
  in `ℝ^d`, both `m₂` deleted — McCann's theorem), `ghs_inverse_H` (both `m₂` deleted: the a.e. inverse exists without
  any existence theorem), `equivariance_unitary` (both `m₂` deleted).
* Limits whose moment was used only for uniqueness: `plan_stab_fd_a/_b/_b_map` (`m₂(P)`), `plan_stab_w1` (`m₁(P)`, C's
  `W₁` targets), all C potential/map/band/coverage/transfer claims for exact, inexact and weighted fits and the C rank
  consistency (`m₁(P_{K,x})`), the A sieve limits `sieve_conv_*`, `convref_*`, `app_sample_rate` (`m₁(P)`).

Not covered (declared):
* Existence without moments: `brenier_exists_H` (AGS route, needs `m₂`) keeps its moments; McCann's existence
  without moments is not formalised (it is not needed for any claim here: `ghs_inverse_H` builds the inverse from the
  given map).
* Claims whose moment is part of the setting (not used only for uniqueness): `integrated_quantile_uncond`
  (`P ∈ 𝒫^ℓ`), `plan_w2_*`, `plan_w2_fd_*`, `moment_sieve_*` (`W₂` convergence, R's standing second moments).
* Bounds that became superfluous are kept (only moments are deleted): the ball carrying the Lipschitz-null source `μ`
  in `brenier_uniq_bdd_source` / `plan_stab_w1`, and the targets' balls in the bounded-target limit claims (used there
  beyond uniqueness).

Encodings (to be checked by the critic):
* Every claim is the frozen claim of the same name, copied mechanically (script) with exactly the hypotheses
  `Mom1 _ ≠ ∞` / `Mom2 _ ≠ ∞` removed (the docstring of each names the deleted hypotheses); typechecked
  `Claims.X → <frozen>.Claims.X` for all 35 (by unfolding and applying), so each name resolves to the same objects.
* `LipNull` stays on the same law as in the frozen claim (the source `P`/`μ_K`, or the target `P` in the swap form).

Critic notes:
* Proved in `OTFD/WaveL8/Route{General,Brenier,Sieve,Cond}.lean` with the untrusted library
  `Foundations/McCannH/Extended` (relative potentials `(D, φ)`: `∂_D φ = {(x, y) : x ∈ D, φ(x) + ⟪y, x' − x⟫ ≤ φ(x')
  ∀ x' ∈ D}`, relative conjugate `φ*_D` in `EReal`; McCann's tail comparison of `u = φ₁ − φ₂` and `v = φ₂* − φ₁*` works
  because `D₁, D₂` are conull for the common source marginal and `φᵢ*_D` are finite along the common target marginal;
  Rockafellar's chain functional in `EReal` is lower semicontinuous and finite on the first projection of `Γ`, so
  `D = {f < ∞}`, `φ = f.toReal` carries every cyclically monotone coupling), the library `Foundations/McCannH/Uniqueness`
  (tail lemma), `Foundations/Potentials/HilbertUniqueness` (multi-valued points of a monotone set are covered by
  Lipschitz hypersurfaces — no interior of the domain needed; graph plans), the certified wave-23d `chainVal`, and,
  for the limit claims, the frozen routes of the same claims with the moment use (`brenierUniq_of_bdd_source`,
  `brenier_uniq_H_bdd`, `sieve_strong_limit_uncond`, `brenier_uniq_H`, `exists_brenierMap_of_lipNull`) replaced by the
  moment-free uniqueness (or the certified wave-L7 forms for bounded targets). Checked in `OTFD/WaveL8/Proofs.lean`.
* Relation to GHS (checked against the local PDF): GHS's abstract says "In case ℋ is infinite-dimensional, P-a.e.
  uniqueness is not guaranteed, though; we show that uniqueness holds among all gradients of convex functions ∇ψ
  pushing P forward to Q for which the boundary of the domain of ψ has P-probability zero". That is a limit of their
  proof (step (a) of the proof of Thm 2.3 runs Alexandrov's Lemma 2.10 at points of `cont f ∩ cont g = int dom f ∩
  int dom g`), not a counterexample: their Remark 2.2 shows only that `int dom ψ = ∅` can occur for a Gaussian `P`, and
  no two distinct cyclically monotone couplings are exhibited. The route here never uses an interior: McCann's
  comparison is run with conjugates relative to the conull domains `D`, the tail lemma needs no integrability, and
  the Lipschitz-hypersurface cover of the multi-valued set uses monotonicity alone. It covers every GHS gradient (the
  graph of `∂ψ` is closed and cyclically monotone), so it strictly extends GHS Thm 2.3(ii) for `P ∈ 𝒫^ℓ`.
* `LipNull`/`IsLipHyp` are GHS's `𝒫^ℓ(ℋ)` without a moment (`τ` Lipschitz on `w^⊥` is no restriction: `τ ∘ proj_{w^⊥}`
  extends it). `CMConc` asks for a Borel cyclically monotone carrier, no restriction either (the closure of a
  cyclically monotone set is one).
* No tautology: conclusions (equality of couplings, a.e. inverses, limits) are not among the hypotheses. No junk:
  no moments remain; the `EReal` potentials and `toReal` live only in the untrusted library.
* Nonvacuity and strictly stronger than the frozen forms: `H = ℝ`, `P` the standard Cauchy law (atomless, hence
  Lipschitz-null; `m₁(P) = m₂(P) = ∞`), `F = id`, `μ = P`: all hypotheses of `brenier_uniq_H`, `brenier_uniq_H_swap`,
  `ghs_inverse_H`, `equivariance_unitary` (`J = id`) hold, while the frozen forms are vacuous there; `brenier_uniq_bdd_source`
  / `plan_stab_w1` with `μ` uniform on `[0, 1]` and `Q` the Cauchy quantile function (monotone); `brenier_uniq_fd` with
  `d = 1`, `P` Cauchy; C claims with `μ_K` uniform on a ball and a heavy-tailed `P_{K,x}`.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/
set_option linter.style.longLine false

noncomputable section

namespace StatFormal.OTFD.WaveL8

namespace Claims

/-! ### From `OTFD/WaveL1/Statements.lean` -/

section OTFD_WaveL1

open StatFormal.OTFD.WaveL1
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace
open StatFormal.OTFD.Wave1 (PellClass IsLipHyp truncK)
open StatFormal.OTFD.Wave8b (embed)
open StatFormal.Wave21b (nsign)

/-- A `lem:plan-stability-H`, moment-free: the frozen `StatFormal.OTFD.WaveL1.Claims.brenier_uniq_fd` with `Mom2 (P : Measure (Euc d)) ≠ ∞`, `Mom2 (μ : Measure (Euc d)) ≠ ∞` deleted (otherwise verbatim). -/
def brenier_uniq_fd : Prop :=
  ∀ (d : ℕ) (P μ : ProbabilityMeasure (Euc d)) (F : Euc d → Euc d),
    (P : Measure (Euc d)) ≪ volume →
    Measurable F → (P : Measure (Euc d)).map F = μ → IsCMMapAE (P : Measure (Euc d)) F →
      BrenierUniq (P : Measure (Euc d)) μ F

/-- A `lem:plan-stability-H`, moment-free: the frozen `StatFormal.OTFD.WaveL1.Claims.plan_stab_fd_a` with `Mom2 (P : Measure (Euc d)) ≠ ∞` deleted (otherwise verbatim). -/
def plan_stab_fd_a : Prop :=
  ∀ (d : ℕ) (P μ : ProbabilityMeasure (Euc d)) (F : Euc d → Euc d) (M : ℝ)
    (α ν : ℕ → ProbabilityMeasure (Euc d)) (π : ℕ → ProbabilityMeasure (Euc d × Euc d))
    (G : ProbabilityMeasure (Euc d × Euc d)),
    (P : Measure (Euc d)) ≪ volume →
    (μ : Measure (Euc d)) (Metric.closedBall 0 M)ᶜ = 0 →
    Measurable F → (P : Measure (Euc d)).map F = μ → IsCMMapAE (P : Measure (Euc d)) F →
    Tendsto α atTop (𝓝 P) → Tendsto ν atTop (𝓝 μ) →
    (∀ K, (π K : Measure (Euc d × Euc d)).fst = α K) →
    (∀ K, (π K : Measure (Euc d × Euc d)).snd = ν K) →
    (∀ K, CMConc (π K : Measure (Euc d × Euc d))) →
    (G : Measure (Euc d × Euc d)) = Graph (P : Measure (Euc d)) F →
      Tendsto π atTop (𝓝 G)

/-- A `lem:plan-stability-H`, moment-free: the frozen `StatFormal.OTFD.WaveL1.Claims.plan_stab_fd_b` with `Mom2 (P : Measure (Euc d)) ≠ ∞` deleted (otherwise verbatim). -/
def plan_stab_fd_b : Prop :=
  ∀ (d : ℕ) (P μ : ProbabilityMeasure (Euc d)) (F : Euc d → Euc d) (M : ℝ)
    (ν : ℕ → ProbabilityMeasure (Euc d)) (π : ℕ → ProbabilityMeasure (Euc d × Euc d)),
    (P : Measure (Euc d)) ≪ volume →
    Measurable F → (P : Measure (Euc d)).map F = μ → IsCMMapAE (P : Measure (Euc d)) F →
    Tendsto ν atTop (𝓝 μ) → (∀ K, (ν K : Measure (Euc d)) (Metric.closedBall 0 M)ᶜ = 0) →
    (∀ K, (π K : Measure (Euc d × Euc d)).fst = P) →
    (∀ K, (π K : Measure (Euc d × Euc d)).snd = ν K) →
    (∀ K, CMConc (π K : Measure (Euc d × Euc d))) →
      Tendsto (fun K => ∫⁻ z, ‖z.2 - F z.1‖ₑ ^ 2 ∂(π K : Measure (Euc d × Euc d))) atTop (𝓝 0)

/-- A `lem:plan-stability-H`, moment-free: the frozen `StatFormal.OTFD.WaveL1.Claims.plan_stab_fd_b_map` with `Mom2 (P : Measure (Euc d)) ≠ ∞` deleted (otherwise verbatim). -/
def plan_stab_fd_b_map : Prop :=
  ∀ (d : ℕ) (P μ : ProbabilityMeasure (Euc d)) (F : Euc d → Euc d) (M : ℝ)
    (ν : ℕ → ProbabilityMeasure (Euc d)) (T : ℕ → Euc d → Euc d),
    (P : Measure (Euc d)) ≪ volume →
    Measurable F → (P : Measure (Euc d)).map F = μ → IsCMMapAE (P : Measure (Euc d)) F →
    Tendsto ν atTop (𝓝 μ) → (∀ K, (ν K : Measure (Euc d)) (Metric.closedBall 0 M)ᶜ = 0) →
    (∀ K, Measurable (T K)) → (∀ K, (P : Measure (Euc d)).map (T K) = ν K) →
    (∀ K, IsCMMapAE (P : Measure (Euc d)) (T K)) →
      Tendsto (fun K => ∫⁻ x, ‖T K x - F x‖ₑ ^ 2 ∂(P : Measure (Euc d))) atTop (𝓝 0)

end OTFD_WaveL1

/-! ### From `OTFD/WaveL3/Statements.lean` -/

section OTFD_WaveL3

open StatFormal.OTFD.WaveL3
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace
open StatFormal.OTFD.WaveL1 (CycMon CMConc IsCMMapAE Graph BrenierUniq LipNull Mom2 W2Conv Euc)
open StatFormal.OTFD.Wave1 (PellClass truncK)
open StatFormal.OTFD.Wave8b (embed)
open StatFormal.Wave21b (nsign)
open StatFormal.OTFD.Wave19a (extTop)

/-- A `lem:app-cm-plans`, moment-free: the frozen `StatFormal.OTFD.WaveL3.Claims.brenier_uniq_H` with `Mom2 (P : Measure H) ≠ ∞`, `Mom2 (μ : Measure H) ≠ ∞` deleted (otherwise verbatim). -/
def brenier_uniq_H : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (P μ : ProbabilityMeasure H) (F : H → H),
    LipNull (P : Measure H) →
    Measurable F → (P : Measure H).map F = μ → IsCMMapAE (P : Measure H) F →
      BrenierUniq (P : Measure H) μ F

/-- A `lem:app-cm-plans`, moment-free: the frozen `StatFormal.OTFD.WaveL3.Claims.brenier_uniq_H_swap` with `Mom2 (P : Measure H) ≠ ∞`, `Mom2 (μ : Measure H) ≠ ∞` deleted (otherwise verbatim). -/
def brenier_uniq_H_swap : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (P μ : ProbabilityMeasure H) (Q : H → H),
    LipNull (P : Measure H) →
    Measurable Q → (μ : Measure H).map Q = P → IsCMMapAE (μ : Measure H) Q →
      BrenierUniq (μ : Measure H) P Q

/-- C `prop:conditional-potentials`, moment-free: the frozen `StatFormal.OTFD.WaveL3.Claims.brenier_uniq_bdd_source` with `Mom1 (P : Measure H) ≠ ∞` deleted (otherwise verbatim). -/
def brenier_uniq_bdd_source : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (μ P : ProbabilityMeasure H) (Q : H → H) (M : ℝ),
    LipNull (μ : Measure H) → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
    Measurable Q → (μ : Measure H).map Q = P → IsCMMapAE (μ : Measure H) Q →
      BrenierUniq (μ : Measure H) P Q

/-- C `prop:conditional-potentials`, moment-free: the frozen `StatFormal.OTFD.WaveL3.Claims.plan_stab_w1` with `Mom1 (P : Measure H) ≠ ∞` deleted (otherwise verbatim). -/
def plan_stab_w1 : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (μ P : ProbabilityMeasure H) (Q : H → H) (M : ℝ) (α ν : ℕ → ProbabilityMeasure H)
    (π : ℕ → ProbabilityMeasure (H × H)) (G : ProbabilityMeasure (H × H)),
    LipNull (μ : Measure H) → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
    Measurable Q → (μ : Measure H).map Q = P → IsCMMapAE (μ : Measure H) Q →
    Tendsto α atTop (𝓝 μ) → Tendsto ν atTop (𝓝 P) →
    (∀ n, (π n : Measure (H × H)).fst = α n) → (∀ n, (π n : Measure (H × H)).snd = ν n) →
    (∀ n, CMConc (π n : Measure (H × H))) →
    (G : Measure (H × H)) = Graph (μ : Measure H) Q →
      Tendsto π atTop (𝓝 G)

/-- C `prop:conditional-potentials`, moment-free: the frozen `StatFormal.OTFD.WaveL3.Claims.cond_potentials` with `Mom1 (P : Measure (Euc K)) ≠ ∞` deleted (otherwise verbatim). -/
def cond_potentials : Prop :=
  ∀ (K : ℕ) (μ P : ProbabilityMeasure (Euc K)) (U : Set (Euc K)) (Q : Euc K → Euc K)
    (α ν : ℕ → ProbabilityMeasure (Euc K)) (π : ℕ → ProbabilityMeasure (Euc K × Euc K)) (χn g : ℕ → Euc K → ℝ),
    RefLaw (μ : Measure (Euc K)) U →
    Measurable Q → (μ : Measure (Euc K)).map Q = P → IsCMMapAE (μ : Measure (Euc K)) Q →
    HardFit μ P U α ν π χn g →
      (∃ χ : Euc K → ℝ, ConvexOn ℝ (interior U) χ ∧ Q =ᵐ[(μ : Measure (Euc K))] gradient χ ∧
          IsGLB (χ '' interior U) 0) ∧
        ∀ χ : Euc K → ℝ, ConvexOn ℝ (interior U) χ → Q =ᵐ[(μ : Measure (Euc K))] gradient χ →
          IsGLB (χ '' interior U) 0 → ∀ c : ℕ → ℝ, (∀ n, IsGLB (χn n '' U) (c n)) →
            ∀ S ⊆ interior U, IsCompact S →
              TendstoUniformlyOn (fun n u => χn n u - c n) χ atTop S ∧
                TendstoUniformlyOn (fun n u => g n u - c n) χ atTop S

/-- C `thm:conditional-band-limits`, moment-free: the frozen `StatFormal.OTFD.WaveL3.Claims.cond_maps_ae_plans` with `Mom1 (P : Measure (Euc K)) ≠ ∞` deleted (otherwise verbatim). -/
def cond_maps_ae_plans : Prop :=
  ∀ (K : ℕ) (μ P : ProbabilityMeasure (Euc K)) (U : Set (Euc K)) (χ : Euc K → ℝ) (Q : Euc K → Euc K)
    (Qn : ℕ → Euc K → Euc K) (α ν : ℕ → ProbabilityMeasure (Euc K)) (π : ℕ → ProbabilityMeasure (Euc K × Euc K))
    (χn g : ℕ → Euc K → ℝ),
    RefLaw (μ : Measure (Euc K)) U →
    Measurable Q → (μ : Measure (Euc K)).map Q = P →
    ConvexOn ℝ (interior U) χ → Q =ᵐ[(μ : Measure (Euc K))] gradient χ →
    HardFit μ P U α ν π χn g → (∀ n, ConvexOn ℝ (interior U) (g n)) →
    (∀ n, ∀ u ∈ interior U, Qn n u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n)) u) →
      ∀ᵐ u ∂(μ : Measure (Euc K)), u ∈ interior U ∧ DifferentiableAt ℝ χ u ∧ Tendsto (fun n => Qn n u) atTop (𝓝 (Q u))

/-- C `thm:conditional-band-limits`, moment-free: the frozen `StatFormal.OTFD.WaveL3.Claims.cond_band_one_sided_plans` with `Mom1 (P : Measure (Euc K)) ≠ ∞` deleted (otherwise verbatim). -/
def cond_band_one_sided_plans : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ P : ProbabilityMeasure (Euc K)) (U A : Set (Euc K)) (χ : Euc K → ℝ) (Q : Euc K → Euc K)
    (Qn : ℕ → Euc K → Euc K) (α ν : ℕ → ProbabilityMeasure (Euc K)) (π : ℕ → ProbabilityMeasure (Euc K × Euc K))
    (χn g : ℕ → Euc K → ℝ) (e : 𝒯 → Euc K) (R EK : ℝ),
    RefLaw (μ : Measure (Euc K)) U →
    Measurable Q → (μ : Measure (Euc K)).map Q = P →
    ConvexOn ℝ (interior U) χ → Q =ᵐ[(μ : Measure (Euc K))] gradient χ →
    HardFit μ P U α ν π χn g → (∀ n, ConvexOn ℝ (interior U) (g n)) →
    (∀ n, ∀ u ∈ interior U, Qn n u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n)) u) →
    MeasurableSet A → (∀ᵐ u ∂(μ : Measure (Euc K)).restrict A, ‖Q u‖ ≤ R) → (∀ t, ‖e t‖ ≤ EK) →
      ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t,
        StatFormal.Wave17a.hPop (μ : Measure (Euc K)) A Q (e t) ≤ StatFormal.Wave21b.supE A (Qn n) (e t) + η ∧
          StatFormal.Wave17a.hPop (μ : Measure (Euc K)) A Q (-e t) ≤ StatFormal.Wave21b.supE A (Qn n) (-e t) + η

/-- C `cor:conditional-test-coverage`, moment-free: the frozen `StatFormal.OTFD.WaveL3.Claims.cond_test_coverage_plans` with `Mom1 (P : Measure (Euc K)) ≠ ∞` deleted (otherwise verbatim). -/
def cond_test_coverage_plans : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ P : ProbabilityMeasure (Euc K)) (U A : Set (Euc K)) (χ : Euc K → ℝ) (Q : Euc K → Euc K)
    (Qn : ℕ → Euc K → Euc K) (α ν : ℕ → ProbabilityMeasure (Euc K)) (π : ℕ → ProbabilityMeasure (Euc K × Euc K))
    (χn g : ℕ → Euc K → ℝ) (m : 𝒯 → ℝ) (e : 𝒯 → Euc K) (Ue Le : ℕ → 𝒯 → EReal) (R EK p κ : ℝ),
    RefLaw (μ : Measure (Euc K)) U →
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

/-- C `prop:cond-transfer-consistency`, moment-free: the frozen `StatFormal.OTFD.WaveL3.Claims.cond_transfer_consistency_plans` with `Mom1 (P' : Measure (Euc K)) ≠ ∞` deleted (otherwise verbatim). -/
def cond_transfer_consistency_plans : Prop :=
  ∀ (K : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (μ P' : ProbabilityMeasure (Euc K)) (U DF : Set (Euc K))
    (Z : Ω → Euc K) (F : Euc K → Euc K) (Fh : ℕ → Ω → Euc K → Euc K) (χ' : Euc K → ℝ) (Q' : Euc K → Euc K)
    (Qh : ℕ → Ω → Euc K → Euc K) (α ν : ℕ → Ω → ProbabilityMeasure (Euc K))
    (π : ℕ → Ω → ProbabilityMeasure (Euc K × Euc K)) (χn g : ℕ → Ω → Euc K → ℝ),
    RefLaw (μ : Measure (Euc K)) U → Measurable Z → Measurable F → P.map (fun ω => F (Z ω)) = μ →
    (∀ᵐ ω ∂P, Z ω ∈ DF) → (∀ᵐ ω ∂P, ∀ z ∈ DF, Tendsto (fun n => Fh n ω z) atTop (𝓝 (F z))) →
    ConvexOn ℝ (interior U) χ' → Q' =ᵐ[(μ : Measure (Euc K))] gradient χ' →
    Measurable Q' → (μ : Measure (Euc K)).map Q' = P' →
    (∀ᵐ ω ∂P, HardFit μ P' U (fun n => α n ω) (fun n => ν n ω) (fun n => π n ω) (fun n => χn n ω) (fun n => g n ω) ∧
      ∀ n, ConvexOn ℝ (interior U) (g n ω)) →
    (∀ n ω, ∀ u ∈ interior U, Qh n ω u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n ω)) u) →
      ∀ᵐ ω ∂P, F (Z ω) ∈ interior U ∧ DifferentiableAt ℝ χ' (F (Z ω)) ∧ Q' (F (Z ω)) = gradient χ' (F (Z ω)) ∧
        Tendsto (fun n => Qh n ω (Fh n ω (Z ω))) atTop (𝓝 (Q' (F (Z ω))))

/-- C `prop:cond-transfer-consistency`, moment-free: the frozen `StatFormal.OTFD.WaveL3.Claims.cond_transfer_consistency_prob_plans` with `Mom1 (P' : Measure (Euc K)) ≠ ∞` deleted (otherwise verbatim). -/
def cond_transfer_consistency_prob_plans : Prop :=
  ∀ (K : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] (μ P' : ProbabilityMeasure (Euc K))
    (U DF : Set (Euc K)) (Z : Ω → Euc K) (F : Euc K → Euc K) (Fh : ℕ → Ω → Euc K → Euc K) (χ' : Euc K → ℝ)
    (Q' : Euc K → Euc K) (Qh : ℕ → Ω → Euc K → Euc K) (α ν : ℕ → Ω → ProbabilityMeasure (Euc K))
    (π : ℕ → Ω → ProbabilityMeasure (Euc K × Euc K)) (χn g : ℕ → Ω → Euc K → ℝ),
    RefLaw (μ : Measure (Euc K)) U → Measurable Z → Measurable F → P.map (fun ω => F (Z ω)) = μ →
    (∀ᵐ ω ∂P, Z ω ∈ DF) → (∀ᵐ ω ∂P, ∀ z ∈ DF, Tendsto (fun n => Fh n ω z) atTop (𝓝 (F z))) →
    ConvexOn ℝ (interior U) χ' → Q' =ᵐ[(μ : Measure (Euc K))] gradient χ' →
    Measurable Q' → (μ : Measure (Euc K)).map Q' = P' →
    (∀ᵐ ω ∂P, HardFit μ P' U (fun n => α n ω) (fun n => ν n ω) (fun n => π n ω) (fun n => χn n ω) (fun n => g n ω) ∧
      ∀ n, ConvexOn ℝ (interior U) (g n ω)) →
    (∀ n ω, ∀ u ∈ interior U, Qh n ω u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n ω)) u) →
    (∀ n, AEStronglyMeasurable (fun ω => Qh n ω (Fh n ω (Z ω))) P) →
      TendstoInMeasure P (fun n ω => Qh n ω (Fh n ω (Z ω))) atTop (fun ω => Q' (F (Z ω)))

end OTFD_WaveL3

/-! ### From `OTFD/WaveL4/Statements.lean` -/

section OTFD_WaveL4

open StatFormal.OTFD.WaveL4
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace
open StatFormal.OTFD.WaveL1 (IsCMMapAE Euc)
open StatFormal.OTFD.WaveL3 (Mom1 RefLaw HardFit)
open StatFormal.OTFD.Wave19a (extTop)
open StatFormal.Wave15b (w2sq phiHard chiI posRows)

/-- C `prop:conditional-potentials`, moment-free: the frozen `StatFormal.OTFD.WaveL4.Claims.cond_potentials_inexact` with `Mom1 (P : Measure (Euc K)) ≠ ∞` deleted (otherwise verbatim). -/
def cond_potentials_inexact : Prop :=
  ∀ (K : ℕ) (μ P : ProbabilityMeasure (Euc K)) (U : Set (Euc K)) (Q : Euc K → Euc K)
    (α ν : ℕ → ProbabilityMeasure (Euc K)) (π : ℕ → ProbabilityMeasure (Euc K × Euc K)) (χn g : ℕ → Euc K → ℝ)
    (ζ : ℕ → ℝ) (d : ℕ → Euc K × Euc K → ℝ),
    RefLaw (μ : Measure (Euc K)) U →
    Measurable Q → (μ : Measure (Euc K)).map Q = P → IsCMMapAE (μ : Measure (Euc K)) Q →
    InexactFit μ P U α ν π χn g ζ d →
      (∃ χ : Euc K → ℝ, ConvexOn ℝ (interior U) χ ∧ Q =ᵐ[(μ : Measure (Euc K))] gradient χ ∧
          IsGLB (χ '' interior U) 0) ∧
        ∀ χ : Euc K → ℝ, ConvexOn ℝ (interior U) χ → Q =ᵐ[(μ : Measure (Euc K))] gradient χ →
          IsGLB (χ '' interior U) 0 → ∀ c : ℕ → ℝ, (∀ n, IsGLB (χn n '' U) (c n)) →
            ∀ S ⊆ interior U, IsCompact S →
              TendstoUniformlyOn (fun n u => χn n u - c n) χ atTop S ∧
                TendstoUniformlyOn (fun n u => g n u - c n) χ atTop S

/-- C `thm:conditional-band-limits`, moment-free: the frozen `StatFormal.OTFD.WaveL4.Claims.cond_maps_ae_inexact` with `Mom1 (P : Measure (Euc K)) ≠ ∞` deleted (otherwise verbatim). -/
def cond_maps_ae_inexact : Prop :=
  ∀ (K : ℕ) (μ P : ProbabilityMeasure (Euc K)) (U : Set (Euc K)) (χ : Euc K → ℝ) (Q : Euc K → Euc K)
    (Qn : ℕ → Euc K → Euc K) (α ν : ℕ → ProbabilityMeasure (Euc K)) (π : ℕ → ProbabilityMeasure (Euc K × Euc K))
    (χn g : ℕ → Euc K → ℝ) (ζ : ℕ → ℝ) (d : ℕ → Euc K × Euc K → ℝ),
    RefLaw (μ : Measure (Euc K)) U →
    Measurable Q → (μ : Measure (Euc K)).map Q = P →
    ConvexOn ℝ (interior U) χ → Q =ᵐ[(μ : Measure (Euc K))] gradient χ →
    InexactFit μ P U α ν π χn g ζ d → (∀ n, ConvexOn ℝ (interior U) (g n)) →
    (∀ n, ∀ u ∈ interior U, Qn n u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n)) u) →
      ∀ᵐ u ∂(μ : Measure (Euc K)), u ∈ interior U ∧ DifferentiableAt ℝ χ u ∧ Tendsto (fun n => Qn n u) atTop (𝓝 (Q u))

/-- C `thm:conditional-band-limits`, moment-free: the frozen `StatFormal.OTFD.WaveL4.Claims.cond_band_one_sided_inexact` with `Mom1 (P : Measure (Euc K)) ≠ ∞` deleted (otherwise verbatim). -/
def cond_band_one_sided_inexact : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ P : ProbabilityMeasure (Euc K)) (U A : Set (Euc K)) (χ : Euc K → ℝ) (Q : Euc K → Euc K)
    (Qn : ℕ → Euc K → Euc K) (α ν : ℕ → ProbabilityMeasure (Euc K)) (π : ℕ → ProbabilityMeasure (Euc K × Euc K))
    (χn g : ℕ → Euc K → ℝ) (ζ : ℕ → ℝ) (d : ℕ → Euc K × Euc K → ℝ) (e : 𝒯 → Euc K) (R EK : ℝ),
    RefLaw (μ : Measure (Euc K)) U →
    Measurable Q → (μ : Measure (Euc K)).map Q = P →
    ConvexOn ℝ (interior U) χ → Q =ᵐ[(μ : Measure (Euc K))] gradient χ →
    InexactFit μ P U α ν π χn g ζ d → (∀ n, ConvexOn ℝ (interior U) (g n)) →
    (∀ n, ∀ u ∈ interior U, Qn n u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n)) u) →
    MeasurableSet A → (∀ᵐ u ∂(μ : Measure (Euc K)).restrict A, ‖Q u‖ ≤ R) → (∀ t, ‖e t‖ ≤ EK) →
      ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t,
        StatFormal.Wave17a.hPop (μ : Measure (Euc K)) A Q (e t) ≤ StatFormal.Wave21b.supE A (Qn n) (e t) + η ∧
          StatFormal.Wave17a.hPop (μ : Measure (Euc K)) A Q (-e t) ≤ StatFormal.Wave21b.supE A (Qn n) (-e t) + η

/-- C `cor:conditional-test-coverage`, moment-free: the frozen `StatFormal.OTFD.WaveL4.Claims.cond_test_coverage_inexact` with `Mom1 (P : Measure (Euc K)) ≠ ∞` deleted (otherwise verbatim). -/
def cond_test_coverage_inexact : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ P : ProbabilityMeasure (Euc K)) (U A : Set (Euc K)) (χ : Euc K → ℝ) (Q : Euc K → Euc K)
    (Qn : ℕ → Euc K → Euc K) (α ν : ℕ → ProbabilityMeasure (Euc K)) (π : ℕ → ProbabilityMeasure (Euc K × Euc K))
    (χn g : ℕ → Euc K → ℝ) (ζ : ℕ → ℝ) (d : ℕ → Euc K × Euc K → ℝ) (m : 𝒯 → ℝ) (e : 𝒯 → Euc K)
    (Ue Le : ℕ → 𝒯 → EReal) (R EK p κ : ℝ),
    RefLaw (μ : Measure (Euc K)) U →
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

/-- C `prop:cond-transfer-consistency`, moment-free: the frozen `StatFormal.OTFD.WaveL4.Claims.cond_transfer_consistency_inexact` with `Mom1 (P' : Measure (Euc K)) ≠ ∞` deleted (otherwise verbatim). -/
def cond_transfer_consistency_inexact : Prop :=
  ∀ (K : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (μ P' : ProbabilityMeasure (Euc K)) (U DF : Set (Euc K))
    (Z : Ω → Euc K) (F : Euc K → Euc K) (Fh : ℕ → Ω → Euc K → Euc K) (χ' : Euc K → ℝ) (Q' : Euc K → Euc K)
    (Qh : ℕ → Ω → Euc K → Euc K) (α ν : ℕ → Ω → ProbabilityMeasure (Euc K))
    (π : ℕ → Ω → ProbabilityMeasure (Euc K × Euc K)) (χn g : ℕ → Ω → Euc K → ℝ) (ζ : ℕ → Ω → ℝ)
    (d : ℕ → Ω → Euc K × Euc K → ℝ),
    RefLaw (μ : Measure (Euc K)) U → Measurable Z → Measurable F → P.map (fun ω => F (Z ω)) = μ →
    (∀ᵐ ω ∂P, Z ω ∈ DF) → (∀ᵐ ω ∂P, ∀ z ∈ DF, Tendsto (fun n => Fh n ω z) atTop (𝓝 (F z))) →
    ConvexOn ℝ (interior U) χ' → Q' =ᵐ[(μ : Measure (Euc K))] gradient χ' →
    Measurable Q' → (μ : Measure (Euc K)).map Q' = P' →
    (∀ᵐ ω ∂P, InexactFit μ P' U (fun n => α n ω) (fun n => ν n ω) (fun n => π n ω) (fun n => χn n ω)
        (fun n => g n ω) (fun n => ζ n ω) (fun n => d n ω) ∧
      ∀ n, ConvexOn ℝ (interior U) (g n ω)) →
    (∀ n ω, ∀ u ∈ interior U, Qh n ω u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n ω)) u) →
      ∀ᵐ ω ∂P, F (Z ω) ∈ interior U ∧ DifferentiableAt ℝ χ' (F (Z ω)) ∧ Q' (F (Z ω)) = gradient χ' (F (Z ω)) ∧
        Tendsto (fun n => Qh n ω (Fh n ω (Z ω))) atTop (𝓝 (Q' (F (Z ω))))

/-- C `prop:cond-transfer-consistency`, moment-free: the frozen `StatFormal.OTFD.WaveL4.Claims.cond_transfer_consistency_prob_inexact` with `Mom1 (P' : Measure (Euc K)) ≠ ∞` deleted (otherwise verbatim). -/
def cond_transfer_consistency_prob_inexact : Prop :=
  ∀ (K : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] (μ P' : ProbabilityMeasure (Euc K))
    (U DF : Set (Euc K)) (Z : Ω → Euc K) (F : Euc K → Euc K) (Fh : ℕ → Ω → Euc K → Euc K) (χ' : Euc K → ℝ)
    (Q' : Euc K → Euc K) (Qh : ℕ → Ω → Euc K → Euc K) (α ν : ℕ → Ω → ProbabilityMeasure (Euc K))
    (π : ℕ → Ω → ProbabilityMeasure (Euc K × Euc K)) (χn g : ℕ → Ω → Euc K → ℝ) (ζ : ℕ → Ω → ℝ)
    (d : ℕ → Ω → Euc K × Euc K → ℝ),
    RefLaw (μ : Measure (Euc K)) U → Measurable Z → Measurable F → P.map (fun ω => F (Z ω)) = μ →
    (∀ᵐ ω ∂P, Z ω ∈ DF) → (∀ᵐ ω ∂P, ∀ z ∈ DF, Tendsto (fun n => Fh n ω z) atTop (𝓝 (F z))) →
    ConvexOn ℝ (interior U) χ' → Q' =ᵐ[(μ : Measure (Euc K))] gradient χ' →
    Measurable Q' → (μ : Measure (Euc K)).map Q' = P' →
    (∀ᵐ ω ∂P, InexactFit μ P' U (fun n => α n ω) (fun n => ν n ω) (fun n => π n ω) (fun n => χn n ω)
        (fun n => g n ω) (fun n => ζ n ω) (fun n => d n ω) ∧
      ∀ n, ConvexOn ℝ (interior U) (g n ω)) →
    (∀ n ω, ∀ u ∈ interior U, Qh n ω u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n ω)) u) →
    (∀ n, AEStronglyMeasurable (fun ω => Qh n ω (Fh n ω (Z ω))) P) →
      TendstoInMeasure P (fun n ω => Qh n ω (Fh n ω (Z ω))) atTop (fun ω => Q' (F (Z ω)))

/-- C `prop:conditional-potentials`, moment-free: the frozen `StatFormal.OTFD.WaveL4.Claims.cond_potentials_weighted` with `Mom1 (P : Measure (Euc K)) ≠ ∞` deleted (otherwise verbatim). -/
def cond_potentials_weighted : Prop :=
  ∀ (K : ℕ) (μ P : ProbabilityMeasure (Euc K)) (U : Set (Euc K)) (Q : Euc K → Euc K)
    (α ν : ℕ → ProbabilityMeasure (Euc K)) (χn g : ℕ → Euc K → ℝ)
    (ζ : ℕ → ℝ),
    RefLaw (μ : Measure (Euc K)) U →
    Measurable Q → (μ : Measure (Euc K)).map Q = P → IsCMMapAE (μ : Measure (Euc K)) Q →
    WeightedFit μ P U α ν χn g ζ →
      (∃ χ : Euc K → ℝ, ConvexOn ℝ (interior U) χ ∧ Q =ᵐ[(μ : Measure (Euc K))] gradient χ ∧
          IsGLB (χ '' interior U) 0) ∧
        ∀ χ : Euc K → ℝ, ConvexOn ℝ (interior U) χ → Q =ᵐ[(μ : Measure (Euc K))] gradient χ →
          IsGLB (χ '' interior U) 0 → ∀ c : ℕ → ℝ, (∀ n, IsGLB (χn n '' U) (c n)) →
            ∀ S ⊆ interior U, IsCompact S →
              TendstoUniformlyOn (fun n u => χn n u - c n) χ atTop S ∧
                TendstoUniformlyOn (fun n u => g n u - c n) χ atTop S

/-- C `thm:conditional-band-limits`, moment-free: the frozen `StatFormal.OTFD.WaveL4.Claims.cond_maps_ae_weighted` with `Mom1 (P : Measure (Euc K)) ≠ ∞` deleted (otherwise verbatim). -/
def cond_maps_ae_weighted : Prop :=
  ∀ (K : ℕ) (μ P : ProbabilityMeasure (Euc K)) (U : Set (Euc K)) (χ : Euc K → ℝ) (Q : Euc K → Euc K)
    (Qn : ℕ → Euc K → Euc K) (α ν : ℕ → ProbabilityMeasure (Euc K))
    (χn g : ℕ → Euc K → ℝ) (ζ : ℕ → ℝ),
    RefLaw (μ : Measure (Euc K)) U →
    Measurable Q → (μ : Measure (Euc K)).map Q = P →
    ConvexOn ℝ (interior U) χ → Q =ᵐ[(μ : Measure (Euc K))] gradient χ →
    WeightedFit μ P U α ν χn g ζ → (∀ n, ConvexOn ℝ (interior U) (g n)) →
    (∀ n, ∀ u ∈ interior U, Qn n u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n)) u) →
      ∀ᵐ u ∂(μ : Measure (Euc K)), u ∈ interior U ∧ DifferentiableAt ℝ χ u ∧ Tendsto (fun n => Qn n u) atTop (𝓝 (Q u))

/-- C `thm:conditional-band-limits`, moment-free: the frozen `StatFormal.OTFD.WaveL4.Claims.cond_band_one_sided_weighted` with `Mom1 (P : Measure (Euc K)) ≠ ∞` deleted (otherwise verbatim). -/
def cond_band_one_sided_weighted : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ P : ProbabilityMeasure (Euc K)) (U A : Set (Euc K)) (χ : Euc K → ℝ) (Q : Euc K → Euc K)
    (Qn : ℕ → Euc K → Euc K) (α ν : ℕ → ProbabilityMeasure (Euc K))
    (χn g : ℕ → Euc K → ℝ) (ζ : ℕ → ℝ) (e : 𝒯 → Euc K) (R EK : ℝ),
    RefLaw (μ : Measure (Euc K)) U →
    Measurable Q → (μ : Measure (Euc K)).map Q = P →
    ConvexOn ℝ (interior U) χ → Q =ᵐ[(μ : Measure (Euc K))] gradient χ →
    WeightedFit μ P U α ν χn g ζ → (∀ n, ConvexOn ℝ (interior U) (g n)) →
    (∀ n, ∀ u ∈ interior U, Qn n u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n)) u) →
    MeasurableSet A → (∀ᵐ u ∂(μ : Measure (Euc K)).restrict A, ‖Q u‖ ≤ R) → (∀ t, ‖e t‖ ≤ EK) →
      ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t,
        StatFormal.Wave17a.hPop (μ : Measure (Euc K)) A Q (e t) ≤ StatFormal.Wave21b.supE A (Qn n) (e t) + η ∧
          StatFormal.Wave17a.hPop (μ : Measure (Euc K)) A Q (-e t) ≤ StatFormal.Wave21b.supE A (Qn n) (-e t) + η

/-- C `cor:conditional-test-coverage`, moment-free: the frozen `StatFormal.OTFD.WaveL4.Claims.cond_test_coverage_weighted` with `Mom1 (P : Measure (Euc K)) ≠ ∞` deleted (otherwise verbatim). -/
def cond_test_coverage_weighted : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ P : ProbabilityMeasure (Euc K)) (U A : Set (Euc K)) (χ : Euc K → ℝ) (Q : Euc K → Euc K)
    (Qn : ℕ → Euc K → Euc K) (α ν : ℕ → ProbabilityMeasure (Euc K))
    (χn g : ℕ → Euc K → ℝ) (ζ : ℕ → ℝ) (m : 𝒯 → ℝ) (e : 𝒯 → Euc K)
    (Ue Le : ℕ → 𝒯 → EReal) (R EK p κ : ℝ),
    RefLaw (μ : Measure (Euc K)) U →
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

/-- C `prop:cond-transfer-consistency`, moment-free: the frozen `StatFormal.OTFD.WaveL4.Claims.cond_transfer_consistency_weighted` with `Mom1 (P' : Measure (Euc K)) ≠ ∞` deleted (otherwise verbatim). -/
def cond_transfer_consistency_weighted : Prop :=
  ∀ (K : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (μ P' : ProbabilityMeasure (Euc K)) (U DF : Set (Euc K))
    (Z : Ω → Euc K) (F : Euc K → Euc K) (Fh : ℕ → Ω → Euc K → Euc K) (χ' : Euc K → ℝ) (Q' : Euc K → Euc K)
    (Qh : ℕ → Ω → Euc K → Euc K) (α ν : ℕ → Ω → ProbabilityMeasure (Euc K)) (χn g : ℕ → Ω → Euc K → ℝ) (ζ : ℕ → Ω → ℝ),
    RefLaw (μ : Measure (Euc K)) U → Measurable Z → Measurable F → P.map (fun ω => F (Z ω)) = μ →
    (∀ᵐ ω ∂P, Z ω ∈ DF) → (∀ᵐ ω ∂P, ∀ z ∈ DF, Tendsto (fun n => Fh n ω z) atTop (𝓝 (F z))) →
    ConvexOn ℝ (interior U) χ' → Q' =ᵐ[(μ : Measure (Euc K))] gradient χ' →
    Measurable Q' → (μ : Measure (Euc K)).map Q' = P' →
    (∀ᵐ ω ∂P, WeightedFit μ P' U (fun n => α n ω) (fun n => ν n ω) (fun n => χn n ω) (fun n => g n ω)
        (fun n => ζ n ω) ∧
      ∀ n, ConvexOn ℝ (interior U) (g n ω)) →
    (∀ n ω, ∀ u ∈ interior U, Qh n ω u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n ω)) u) →
      ∀ᵐ ω ∂P, F (Z ω) ∈ interior U ∧ DifferentiableAt ℝ χ' (F (Z ω)) ∧ Q' (F (Z ω)) = gradient χ' (F (Z ω)) ∧
        Tendsto (fun n => Qh n ω (Fh n ω (Z ω))) atTop (𝓝 (Q' (F (Z ω))))

/-- C `prop:cond-transfer-consistency`, moment-free: the frozen `StatFormal.OTFD.WaveL4.Claims.cond_transfer_consistency_prob_weighted` with `Mom1 (P' : Measure (Euc K)) ≠ ∞` deleted (otherwise verbatim). -/
def cond_transfer_consistency_prob_weighted : Prop :=
  ∀ (K : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] (μ P' : ProbabilityMeasure (Euc K))
    (U DF : Set (Euc K)) (Z : Ω → Euc K) (F : Euc K → Euc K) (Fh : ℕ → Ω → Euc K → Euc K) (χ' : Euc K → ℝ)
    (Q' : Euc K → Euc K) (Qh : ℕ → Ω → Euc K → Euc K) (α ν : ℕ → Ω → ProbabilityMeasure (Euc K)) (χn g : ℕ → Ω → Euc K → ℝ) (ζ : ℕ → Ω → ℝ),
    RefLaw (μ : Measure (Euc K)) U → Measurable Z → Measurable F → P.map (fun ω => F (Z ω)) = μ →
    (∀ᵐ ω ∂P, Z ω ∈ DF) → (∀ᵐ ω ∂P, ∀ z ∈ DF, Tendsto (fun n => Fh n ω z) atTop (𝓝 (F z))) →
    ConvexOn ℝ (interior U) χ' → Q' =ᵐ[(μ : Measure (Euc K))] gradient χ' →
    Measurable Q' → (μ : Measure (Euc K)).map Q' = P' →
    (∀ᵐ ω ∂P, WeightedFit μ P' U (fun n => α n ω) (fun n => ν n ω) (fun n => χn n ω) (fun n => g n ω)
        (fun n => ζ n ω) ∧
      ∀ n, ConvexOn ℝ (interior U) (g n ω)) →
    (∀ n ω, ∀ u ∈ interior U, Qh n ω u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n ω)) u) →
    (∀ n, AEStronglyMeasurable (fun ω => Qh n ω (Fh n ω (Z ω))) P) →
      TendstoInMeasure P (fun n ω => Qh n ω (Fh n ω (Z ω))) atTop (fun ω => Q' (F (Z ω)))

end OTFD_WaveL4

/-! ### From `OTFD/WaveL5/Statements.lean` -/

section OTFD_WaveL5

open StatFormal.OTFD.WaveL5
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace
open StatFormal.OTFD.WaveL2 (FixedKSetting critVal rankEnergy pool)
open StatFormal.OTFD.Wave22a (mix energyD IsConvGradAE headT liftMap)
open StatFormal.OTFD.WaveL1 (IsCMMapAE LipNull Mom2 Euc)
open StatFormal.OTFD.Wave1 (PellClass truncK)
open StatFormal.OTFD.Wave8b (embed)
open StatFormal.OTFD.Ranks (IsMin)

/-- A `lem:app-cm-plans`, moment-free: the frozen `StatFormal.OTFD.WaveL5.Claims.ghs_inverse_H` with `Mom2 P ≠ ∞`, `Mom2 μ ≠ ∞` deleted (otherwise verbatim). -/
def ghs_inverse_H : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (P μ : Measure H) [IsProbabilityMeasure P] [IsProbabilityMeasure μ] (F : H → H),
    LipNull P → LipNull μ →
    Measurable F → P.map F = μ → IsCMMapAE P F →
      ∃ G : H → H, Measurable G ∧ μ.map G = P ∧ IsCMMapAE μ G ∧
        (∀ᵐ x ∂P, G (F x) = x) ∧ ∀ᵐ u ∂μ, F (G u) = u

end OTFD_WaveL5

/-! ### From `OTFD/WaveL6/Statements.lean` -/

section OTFD_WaveL6

open StatFormal.OTFD.WaveL6
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace
open StatFormal.OTFD.WaveL1 (LipNull Euc)
open StatFormal.OTFD.WaveL3 (Mom1)
open StatFormal.OTFD.Wave1 (PellClass truncK)
open StatFormal.OTFD.Wave22a (IsSubgrad supAff cubeH)

/-- A `thm:sieve-convergence`, moment-free: the frozen `StatFormal.OTFD.WaveL6.Claims.sieve_conv_weak` with `Mom1 (P : Measure H) ≠ ∞` deleted (otherwise verbatim). -/
def sieve_conv_weak : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (P μ : ProbabilityMeasure H) (ψ : H → ℝ) (F : H → H) (M Lψ Lφ : ℝ)
    (φ : (K : ℕ) → Euc K → ℝ) (FK : (K : ℕ) → Euc K → Euc K) (K₀ : Set H) (h : H),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    LipNull (P : Measure H) → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
    ConvexOn ℝ univ ψ → (∀ x x', |ψ x - ψ x'| ≤ Lψ * ‖x - x'‖) →
    Measurable F → (P : Measure H).map F = μ → (∀ᵐ x ∂(P : Measure H), IsSubgrad ψ x (F x)) →
    (∀ K z z', |φ K z - φ K z'| ≤ Lφ * ‖z - z'‖) → (∀ K, Measurable (FK K)) →
    (∀ K, ((P : Measure H).map (truncK e K)).map (FK K) = (μ : Measure H).map (truncK e K)) →
    (∀ K, ∀ᵐ z ∂((P : Measure H).map (truncK e K)), IsSubgrad (φ K) z (FK K z)) →
    IsCompact K₀ → K₀ ⊆ interior (P : Measure H).support →
    (∀ x ∈ K₀, ∀ v, HasLineDerivAt ℝ ψ ⟪F x, v⟫ x v) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ K in atTop, ∀ x ∈ K₀, ∀ y,
        IsSubgrad (fun x' => φ K (truncK e K x')) x y → |⟪y - F x, h⟫| ≤ ε

/-- A `thm:sieve-convergence`, moment-free: the frozen `StatFormal.OTFD.WaveL6.Claims.sieve_conv_norm` with `Mom1 (P : Measure H) ≠ ∞` deleted (otherwise verbatim). -/
def sieve_conv_norm : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (P μ : ProbabilityMeasure H) (ψ : H → ℝ) (F : H → H) (M Lψ Lφ : ℝ)
    (φ : (K : ℕ) → Euc K → ℝ) (FK : (K : ℕ) → Euc K → Euc K) (K₀ C : Set H),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    LipNull (P : Measure H) → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
    ConvexOn ℝ univ ψ → (∀ x x', |ψ x - ψ x'| ≤ Lψ * ‖x - x'‖) →
    Measurable F → (P : Measure H).map F = μ → (∀ᵐ x ∂(P : Measure H), IsSubgrad ψ x (F x)) →
    (∀ K z z', |φ K z - φ K z'| ≤ Lφ * ‖z - z'‖) → (∀ K, Measurable (FK K)) →
    (∀ K, ((P : Measure H).map (truncK e K)).map (FK K) = (μ : Measure H).map (truncK e K)) →
    (∀ K, ∀ᵐ z ∂((P : Measure H).map (truncK e K)), IsSubgrad (φ K) z (FK K z)) →
    IsCompact K₀ → K₀ ⊆ interior (P : Measure H).support →
    (∀ x ∈ K₀, ∀ v, HasLineDerivAt ℝ ψ ⟪F x, v⟫ x v) →
    IsCompact C → (∀ K, ∀ x ∈ K₀, ∀ y, IsSubgrad (fun x' => φ K (truncK e K x')) x y → y ∈ C) →
    (∀ x ∈ K₀, F x ∈ C) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ K in atTop, ∀ x ∈ K₀, ∀ y,
        IsSubgrad (fun x' => φ K (truncK e K x')) x y → ‖y - F x‖ ≤ ε

/-- A `thm:sieve-convergence`, moment-free: the frozen `StatFormal.OTFD.WaveL6.Claims.sieve_conv_norm_cube` with `Mom1 (P : Measure H) ≠ ∞` deleted (otherwise verbatim). -/
def sieve_conv_norm_cube : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (lam : ℕ → ℝ) (P μ : ProbabilityMeasure H) (S : Set H) (b : H → ℝ) (x₀ : H) (F : H → H) (M : ℝ)
    (SK : (K : ℕ) → Set (Euc K)) (bK : (K : ℕ) → Euc K → ℝ) (zK : (K : ℕ) → Euc K)
    (FK : (K : ℕ) → Euc K → Euc K) (K₀ : Set H),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    (∀ k, 0 ≤ lam k) → Summable (fun k => lam k ^ 2) →
    LipNull (P : Measure H) → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
    S.Nonempty → S ⊆ cubeH e lam → BddAbove (range fun y : S => ⟪x₀, (y : H)⟫ - b y) →
    Measurable F → (P : Measure H).map F = μ → (∀ᵐ x ∂(P : Measure H), IsSubgrad (supAff S b) x (F x)) →
    (∀ K, (SK K).Nonempty) → (∀ K, ∀ z ∈ SK K, ∀ k : Fin K, |z k| ≤ lam k) →
    (∀ K, BddAbove (range fun z : SK K => ⟪zK K, (z : Euc K)⟫ - bK K z)) → (∀ K, Measurable (FK K)) →
    (∀ K, ((P : Measure H).map (truncK e K)).map (FK K) = (μ : Measure H).map (truncK e K)) →
    (∀ K, ∀ᵐ z ∂((P : Measure H).map (truncK e K)), IsSubgrad (supAff (SK K) (bK K)) z (FK K z)) →
    IsCompact K₀ → K₀ ⊆ interior (P : Measure H).support →
    (∀ x ∈ K₀, ∀ v, HasLineDerivAt ℝ (supAff S b) ⟪F x, v⟫ x v) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ K in atTop, ∀ x ∈ K₀, ∀ y,
        IsSubgrad (fun x' => supAff (SK K) (bK K) (truncK e K x')) x y → ‖y - F x‖ ≤ ε

end OTFD_WaveL6

/-! ### From `Wave23b/Statements.lean` -/

section Wave23b

open StatFormal.Wave23b
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace BoundedContinuousFunction
open StatFormal.OTFD.Wave1 (edStat truncK IsLipHyp)
open StatFormal.OTFD.Wave5b (GibbsHyp gibbsPlan gibbsMean)
open StatFormal.OTFD.Wave8c (IsRankPair IsGradMap)
open StatFormal.OTFD.Wave8b (embed proj embLaw)
open StatFormal.OTFD.WaveL1 (LipNull BrenierUniq IsCMMapAE)
open StatFormal.Wave21b (depthRegion depthH)

/-- A `cor:convergent-references`, moment-free: the frozen `StatFormal.Wave23b.Claims.convref_a_uncond` with `StatFormal.OTFD.WaveL3.Mom1 (P : Measure H) ≠ ∞` deleted (otherwise verbatim). -/
def convref_a_uncond : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (P μ : ProbabilityMeasure H) (e : ℕ → H) (M : ℝ)
    (ν : ∀ K, Measure (Euc K)) (F : ∀ K, Euc K → Euc K) (νH : ℕ → ProbabilityMeasure H) (Fμ : H → H),
    Orthonormal ℝ e → LipNull (P : Measure H) →
    (∀ K, ν K (Metric.closedBall 0 M)ᶜ = 0) →
    (∀ K, Measurable (F K)) → (∀ K, ((P : Measure H).map (truncK e K)).map (F K) = ν K) →
    (∀ K, IsCMMapAE ((P : Measure H).map (truncK e K)) (F K)) →
    (∀ K, (νH K : Measure H) = (ν K).map (embed e K)) → Tendsto νH atTop (𝓝 μ) →
    Measurable Fμ → (P : Measure H).map Fμ = μ → IsCMMapAE (P : Measure H) Fμ →
      (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 ∧
        Tendsto (fun K => ∫⁻ x, ‖embed e K (F K (truncK e K x)) - Fμ x‖ₑ ^ 2 ∂(P : Measure H)) atTop (𝓝 0)

/-- A `cor:convergent-references`, moment-free: the frozen `StatFormal.Wave23b.Claims.convref_b_uncond` with `StatFormal.OTFD.WaveL3.Mom1 (Pr.map X) ≠ ∞` deleted (otherwise verbatim). -/
def convref_b_uncond : Prop :=
  ∀ (H Ω : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (X Y : Ω → H) (e : ℕ → H) (M : ℝ) (ν : ∀ K, Measure (Euc K)) (F : ∀ K, Euc K → Euc K)
    (νH : ℕ → ProbabilityMeasure H) (μY : ProbabilityMeasure H),
    Measurable X → Measurable Y → Orthonormal ℝ e → LipNull (Pr.map X) →
    (∀ K, ν K (Metric.closedBall 0 M)ᶜ = 0) →
    (∀ K, Measurable (F K)) → (∀ K, ((Pr.map X).map (truncK e K)).map (F K) = ν K) →
    (∀ K, IsCMMapAE ((Pr.map X).map (truncK e K)) (F K)) →
    (∀ K, (νH K : Measure H) = (ν K).map (embed e K)) → (μY : Measure H) = Pr.map Y →
    TendstoInMeasure Pr (fun K ω => embed e K (F K (truncK e K (X ω)))) atTop Y →
      Tendsto νH atTop (𝓝 μY) ∧
        ∀ Fμ : H → H, Measurable Fμ → (Pr.map X).map Fμ = μY → IsCMMapAE (Pr.map X) Fμ →
          ∀ᵐ ω ∂Pr, Y ω = Fμ (X ω)

end Wave23b

/-! ### From `Wave24c/Statements.lean` -/

section Wave24c

open StatFormal.Wave24c
open MeasureTheory ProbabilityTheory Set Filter Topology Asymptotics Finset
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

/-- T `supp:814`, moment-free: the frozen `StatFormal.Wave24c.Claims.equivariance_unitary` with `StatFormal.OTFD.WaveL1.Mom2 P ≠ ∞`, `StatFormal.OTFD.WaveL1.Mom2 μ ≠ ∞` deleted (otherwise verbatim). -/
def equivariance_unitary : Prop :=
  ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] [NormedAddCommGroup H'] [InnerProductSpace ℝ H'] [CompleteSpace H']
    [SecondCountableTopology H'] [MeasurableSpace H'] [BorelSpace H']
    (J : H ≃ₗᵢ[ℝ] H') (P μ : Measure H) (T : H → H) (T' : H' → H'),
    IsProbabilityMeasure P → IsProbabilityMeasure μ →
    StatFormal.OTFD.WaveL1.LipNull P →
    Measurable T → P.map T = μ → StatFormal.OTFD.WaveL1.IsCMMapAE P T →
    Measurable T' → (P.map J).map T' = μ.map J → StatFormal.OTFD.WaveL1.IsCMMapAE (P.map J) T' →
      (T' =ᵐ[P.map J] fun y => J (T (J.symm y))) ∧ ∀ᵐ x ∂P, T' (J x) = J (T x) ∧ ‖T' (J x)‖ = ‖T x‖

end Wave24c

/-! ### From `Wave24e/Statements.lean` -/

section Wave24e

open StatFormal.Wave24e
open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace
open StatFormal.Wave23a (popSupp fitSupp)
open StatFormal.Wave23c (FixedKOOS entMap lagPot)
open TauCeti (IsKantorovichOptimalTransportMap)
open StatFormal.OTFD.Wave13a (tukeyDepthH)
open StatFormal.OTFD.Wave8c (unifSym)
open StatFormal.Wave18a (transportPolytope frob IsRegMin entReg)
open StatFormal.SBFairness.Stability (tv)
open StatFormal.Wave9b (Standardises)
open StatFormal.Wave23c (ellF1)

/-- C `lem:cond-rank-consistency`, moment-free: the frozen `StatFormal.Wave24e.Claims.cond_rank_consistency_uncond` with `StatFormal.OTFD.WaveL3.Mom1 (P : Measure (EuclideanSpace ℝ (Fin K))) ≠ ∞` deleted (otherwise verbatim). -/
def cond_rank_consistency_uncond : Prop :=
  ∀ (K : ℕ) (n M : ℕ → ℕ) (ε : ℕ → ℝ) (R : ℝ) (z : ∀ k, Fin (n k + 1) → EuclideanSpace ℝ (Fin K))
    (f : ∀ k, Fin (n k + 1) → ℝ) (u : ∀ k, Fin (M k + 1) → EuclideanSpace ℝ (Fin K)) (g : ∀ k, Fin (M k + 1) → ℝ)
    (μ P : ProbabilityMeasure (EuclideanSpace ℝ (Fin K))) (U : Set (EuclideanSpace ℝ (Fin K)))
    (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (α ν : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin K))) (ζ : ℕ → ℝ) (ρ : Measure (EuclideanSpace ℝ (Fin K))),
    StatFormal.OTFD.WaveL3.RefLaw (μ : Measure (EuclideanSpace ℝ (Fin K))) U →
    Measurable Q →
    (μ : Measure (EuclideanSpace ℝ (Fin K))).map Q = P →
    StatFormal.OTFD.WaveL1.IsCMMapAE (μ : Measure (EuclideanSpace ℝ (Fin K))) Q →
    StatFormal.OTFD.WaveL4.WeightedFit μ P U α ν (fun k => lagPot (z k) (f k)) (fun k => lagPot (z k) (f k)) ζ →
    (∀ k, (α k : Measure (EuclideanSpace ℝ (Fin K))) =
      ∑ j, ENNReal.ofReal (1 / ((M k : ℝ) + 1)) • Measure.dirac (u k j)) → (∀ k j, u k j ∈ U) →
    (∀ k, 0 < ε k) → Tendsto (fun k => ε k * Real.log (((M k : ℝ) + 1) * ((n k : ℝ) + 1))) atTop (𝓝 0) →
    (∀ k, ColumnEq (ε k) (z k) (f k) (u k) (g k)) → (∀ k i, ‖z k i‖ ≤ R) → ρ ≪ volume →
      (∃ χ : EuclideanSpace ℝ (Fin K) → ℝ, ConvexOn ℝ (interior U) χ ∧
          Q =ᵐ[(μ : Measure (EuclideanSpace ℝ (Fin K)))] gradient χ ∧ IsGLB (χ '' interior U) 0) ∧
        ∀ χ : EuclideanSpace ℝ (Fin K) → ℝ, ConvexOn ℝ (interior U) χ →
          Q =ᵐ[(μ : Measure (EuclideanSpace ℝ (Fin K)))] gradient χ → IsGLB (χ '' interior U) 0 →
          (∀ y, DifferentiableAt ℝ (fun y' => sSup ((fun w => ⟪w, y'⟫ - χ w) '' interior U)) y →
            Tendsto (fun k => rankMap (ε k) (u k) (g k) y) atTop
              (𝓝 (gradient (fun y' => sSup ((fun w => ⟪w, y'⟫ - χ w) '' interior U)) y))) ∧
          ∀ᵐ y ∂ρ, Tendsto (fun k => rankMap (ε k) (u k) (g k) y) atTop
            (𝓝 (gradient (fun y' => sSup ((fun w => ⟪w, y'⟫ - χ w) '' interior U)) y))

end Wave24e

/-! ### From `Wave24f/Statements.lean` -/

section Wave24f

open StatFormal.Wave24f
open MeasureTheory Set Filter Topology Finset
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace
open StatFormal.OTFD.WaveL1 (Euc LipNull IsCMMapAE)
open StatFormal.OTFD.Wave8b (embed)
open StatFormal.OTFD.Wave1 (truncK)
open StatFormal.OTFD.WaveL3 (Mom1)
open StatFormal.OTFD.Wave16b (rmsE)

/-- A `cor:app-sample-rate`, moment-free: the frozen `StatFormal.Wave24f.Claims.app_sample_rate` with `Mom1 (P : Measure H) ≠ ∞` deleted (otherwise verbatim). -/
def app_sample_rate : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (P μ : ProbabilityMeasure H) (F : H → H) (M : ℝ) (FK : (K : ℕ) → Euc K → Euc K)
    (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (Kn : ℕ → ℕ) (X : (n : ℕ) → Ω → Fin n → H) (Fhat Fm : (n : ℕ) → Ω → Fin n → Euc (Kn n))
    (μgrid : (n : ℕ) → Measure (Euc (Kn n))) (L : ℕ → ℝ≥0∞) (α : ℝ),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    LipNull (P : Measure H) → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
    Measurable F → (P : Measure H).map F = μ → IsCMMapAE (P : Measure H) F →
    (∀ K, Measurable (FK K)) →
    (∀ K, ((P : Measure H).map (truncK e K)).map (FK K) = (μ : Measure H).map (truncK e K)) →
    (∀ K, IsCMMapAE ((P : Measure H).map (truncK e K)) (FK K)) →
    Tendsto Kn atTop atTop →
    (∀ n i, Measurable fun ω => X n ω i) → (∀ n i, Pr.map (fun ω => X n ω i) = (P : Measure H)) →
    (∀ n i, Measurable fun ω => ‖Fhat n ω i - Fm n ω i‖) →
    (∀ n i, Measurable fun ω => ‖Fm n ω i - FK (Kn n) (truncK e (Kn n) (X n ω i))‖) →
    0 < α → α ≤ 1 →
    (∀ n, rmsE Pr (fun ω i => ‖Fm n ω i - FK (Kn n) (truncK e (Kn n) (X n ω i))‖) ≤
      L n * TauCeti.wassersteinEDist 2 (μgrid n) ((μ : Measure H).map (truncK e (Kn n))) ^ α) →
    Tendsto (fun n => L n * TauCeti.wassersteinEDist 2 (μgrid n) ((μ : Measure H).map (truncK e (Kn n))) ^ α)
      atTop (𝓝 0) →
      limsup (fun n => rmsE Pr (fun ω i => ‖embed e (Kn n) (Fhat n ω i) - F (X n ω i)‖)) atTop ≤
          limsup (fun n => rmsE Pr (fun ω i => ‖Fhat n ω i - Fm n ω i‖)) atTop ∧
        (Tendsto (fun n => rmsE Pr (fun ω i => ‖Fhat n ω i - Fm n ω i‖)) atTop (𝓝 0) →
          Tendsto (fun n => rmsE Pr (fun ω i => ‖embed e (Kn n) (Fhat n ω i) - F (X n ω i)‖)) atTop (𝓝 0))

end Wave24f

end Claims

end StatFormal.OTFD.WaveL8
