import StatFormal.Archive.OTFD.WaveL8.Statements
import StatFormal.Archive.Wave25b.Statements
import StatFormal.Archive.Wave24a.Statements
import TauCeti.Probability.Process.EmpiricalMeasure

/-!
# FROZEN STATEMENTS — wave P3c (partial-audit waves 3a MCCANN consumers, 3b Ghosal–Sen start): McCann existence with
# no moment; DISCHARGE of the population-map premise of C `prop:conditional-potentials`, `thm:conditional-band-limits`,
# `cor:conditional-test-coverage`, `prop:cond-transfer-consistency`, `lem:cond-rank-consistency` and of the potentials
# of A `thm:sieve-convergence`; A `thm:app-ghosalsen-rate` on compacts of the interior and the DISCHARGE of the
# Ghosal–Sen premise of A/B `thm:consistency`

Sources (verbatim in `lean-formalisation/inventory/extracted/{otfd-A_sieves,otfd-B_bands,otfd-C_conditional}.md`;
current text of `otfd/papers/`):
* A `thm:app-ghs-existence` (`A_sieves/supplement.tex:1068-1074`, GHS Thm 2.3: any target, no moment of the target;
  frozen wave 25b `app_ghs_existence` with `P ∈ 𝒫^ℓ`, i.e. with a second moment of the source) and
  `cor:app-ghs-lipschitz` (`:1076-1088`); McCann, Duke Math. J. 80 (1995), Main Theorem (existence of a monotone map
  with NO moments, `P ≪ Leb` in `ℝ^d`).
* C `prop:conditional-potentials` (`C_conditional/supplement.tex:1081-`), `thm:conditional-band-limits`
  (`main.tex:666-`), `cor:conditional-test-coverage`, `prop:cond-transfer-consistency` (`main.tex:1016-`),
  `lem:cond-rank-consistency` (`main.tex:1002-`): the population quantile map `Q_{K,x}` ("the McCann map pushing `μ_K`
  to `P_{K,x}`") is a given object; the frozen moment-free forms (wave L8, under the paper's fit assumption
  `WeightedFit` of wave L4) take `Q` (and its potential `χ`) as PREMISES.
* A `thm:sieve-convergence` (frozen wave L8 `sieve_conv_weak`, `sieve_conv_norm`): the potentials `ψ`, `φ_K` and maps
  `F`, `F_K` are premises.
* A `thm:app-ghosalsen-rate` (`A_sieves/supplement.tex:2769-2789`, Ghosal–Sen, Ann. Statist. 2022, Thm 4.1(b), with
  their eqs. (14)–(16) for the estimator) and A/B `thm:consistency` (`A_sieves/supplement.tex:5089-5114`; B
  `supplement.tex:6137-`, cost `‖z − u‖²_{M_K}`; frozen wave 24a `consistency_A`,
  `consistency_B`, CONDITIONAL on "`F̂_n → F` uniformly on `𝒦` almost surely").
Imports the frozen statement files of waves L8 (and through it L1, L3, L4, L6, 24e, 22a, 1: `IsCMMapAE`, `LipNull`,
`RefLaw`, `WeightedFit`, `Euc`, `extTop`, `rankMap`, `ColumnEq`, `lagPot`, `hPop`, `supE`, `truncK`, `IsSubgrad`),
25b (`app_ghs_existence`) and 24a, not copied; Tau Ceti `empiricalMeasure`. No new definitions.

Covered:
* McCann existence: `ghs_existence_lipNull` (the frozen wave-25b `app_ghs_existence` with `PellClass P` replaced by
  `LipNull P`: the second moment of the source DELETED — GHS Thm 2.3 with no moment at all); `mccann_exists_H` (its
  `IsCMMapAE` form, `P` Lipschitz-null, ANY `Q`); `mccann_exists_fd` (`P ≪ Leb` in `ℝ^K`, any `Q`, no moment);
  `ghs_lipschitz_exists` (bounded `Q`: an everywhere-finite convex `M`-Lipschitz potential whose `P`-a.e. subgradient
  pushes `P` to `Q`; A `cor:app-ghs-lipschitz` together with existence, no moment).
* C DISCHARGES (paper's fit assumption, moment-free): `cond_potentials_weighted_mccann`, `cond_maps_ae_weighted_mccann`,
  `cond_band_one_sided_weighted_mccann`, `cond_test_coverage_weighted_mccann`,
  `cond_transfer_consistency_weighted_mccann`, `cond_transfer_consistency_prob_weighted_mccann`,
  `cond_rank_consistency_mccann`. Each is `(existence) ∧ (the frozen wave-L8 claim of the same stem)`: under the
  claim's setting premises (population-map premises deleted), a population map exists — Borel, pushing `μ_K` to
  `P_{K,x}`, `μ_K`-a.e. cyclically monotone and (where the frozen claim takes one) `μ_K`-a.e. the gradient of a
  convex `χ` on `int 𝒰_K` with `inf χ = 0` — and the frozen conclusion holds for every such map.
* A DISCHARGES: `sieve_conv_weak_mccann`, `sieve_conv_norm_mccann` (for `P` Lipschitz-null, no moment, `μ` in
  `B(0, M)`: the potentials `ψ`, `φ_K` — convex, `M`-Lipschitz — and maps `F`, `F_K` exist, `Π_K#P` staying
  Lipschitz-null; the frozen claim holds for every such choice).
* Ghosal–Sen: `ghosal_sen_uniform` (A `thm:app-ghosalsen-rate`, uniform a.s. convergence of the semi-discrete
  empirical rank map on a compact `𝒦 ⊆ int supp P_K`, no moment of `P_K`); `semidiscrete_exists` (the estimator's
  hypotheses are satisfiable at every `n`, `ω`); `consistency_A_gs`, `consistency_B_gs` (the frozen wave-24a
  `consistency_A`, `consistency_B` at `E = ℝ^K` with their uniform-convergence premise replaced by the hypotheses of
  `ghosal_sen_uniform`: UNCONDITIONAL given the paper's setting; B at the Euclidean cost `M_K = I` only).

Not covered (declared):
* The exact-fit (`_plans`) and inexact-fit (`_inexact`) variants of the C claims (same discharge, not restated; the
  paper's assumption is the weighted one); A `sieve_conv_norm_cube` (its potential is the specific `supAff` form).
* C `lem:cond-rank-consistency`: Step 6 and the joint satisfiability of `WeightedFit` with the column equations (other
  blockers of the same row).
* Ghosal–Sen part (a) (empirical quantile maps on compacts of `int S_K`; not restated by A) and part (c) (uniformity
  on all of `ℝ^K`; not used by the paper); general random `ν̂_n ⇀ ν` in place of the empirical measure.
* The implication "population quantile map a homeomorphism `int S_K → int 𝒴_K` ⇒ the potential is differentiable on
  `𝒦` with gradient `F`" is not formalised (the claims assume the weaker differentiability, see Encodings); nor is the
  membership of Ghosal–Sen's own estimator (their eqs. (14)–(15)) in the estimator class (`semidiscrete_exists` only
  shows the class is nonempty at every `n`, `ω`).
* B `thm:consistency` for a general symmetric positive definite `M_K` (cost `‖z − u‖²_{M_K}`): `consistency_B_gs` is
  the case `M_K = I` (where B identifies its hypotheses with those of A `thm:app-ghosalsen-rate`); the general case reduces to it by the
  linear change of variables `u ↦ M_K u` on the reference side (not formalised). The quantifier order "almost surely,
  for every compact `𝒦`" (B; A is ambiguous) is formalised as "for every compact `𝒦`, almost surely" (the frozen
  wave-24a order); a countable compact exhaustion of `int 𝒴_K` recovers the former (not formalised).

Encodings (to be checked by the critic):
* The C and sieve discharges copy the frozen wave-L8 claim of their stem verbatim as the second conjunct (with the
  setting variables bound outside), so each implies the frozen claim (`RouteImplies`: `Claims.X_mccann →
  WaveL8.Claims.X`, typechecked); the first conjunct asserts existence of the population objects with exactly the
  frozen premises on them (plus `IsCMMapAE`, the normalisation `IsGLB (χ '' int 𝒰) 0`, convexity of `φ_K` and the
  Lipschitz constant `M` where the frozen claim does not demand them — strengthening).
* `ghs_existence_lipNull` is the frozen `app_ghs_existence` with only `PellClass (P : Measure H)` (probability,
  `∫‖x‖² < ∞`, Lipschitz-null) replaced by `LipNull (P : Measure H)`; it implies the frozen one (`RouteImplies`).
* Ghosal–Sen. Data `Z_i` iid `P_K` (`iIndepFun`, `HasLaw`), `P_K ≪ Leb`, no moment; reference `μ_K` carried by
  `B(0, M)` (its compact support `S_K`; `μ_K ≪ Leb` is not needed for the convergence, it is used only in
  `semidiscrete_exists`). The population rank map: `F` Borel, `F#P_K = μ_K`, `P_K`-a.e. a subgradient of a convex
  `L`-Lipschitz `ψ` (exists by `ghs_lipschitz_exists`, any `L ≥ M`), with `HasGradientAt ψ (F x) x` on `𝒦` (it pins
  `F` on the `P_K`-null part of `𝒦` too, as the sup over `𝒦` requires). This REPLACES the paper's homeomorphism
  hypothesis by a WEAKER one (generalisation): if `Q_{+,K}` is a homeomorphism `int S_K → int 𝒴_K`, its inverse `F` is
  continuous on the open `int 𝒴_K` and lies in `∂ψ` on a `P_K`-full, hence dense, subset of it; closedness of the
  graph of `∂ψ` makes `F` a continuous selection of `∂ψ` on `int 𝒴_K`, and monotonicity (`⟨F(x + t d) − y, d⟩ ≥ 0`
  for `y ∈ ∂ψ(x)`, `t ↓ 0`) forces `∂ψ(x) = {F x}`, i.e. `ψ` differentiable with gradient `F` on `int 𝒴_K ⊇ 𝒦`. The
  implication is not formalised. Also not assumed: `μ_K ≪ Leb`, convexity of `S_K` (generalisations). The estimator at sample size `n + 1` (`P̂_n` = Tau Ceti `empiricalMeasure`
  of `Z_0, …, Z_n`): a potential `ψ̂_n` that is `M`-Lipschitz (it is the conjugate over `S_K ⊆ B(0, M)` of the
  reference-side dual potential), a coupling `γ_n` of `P̂_n` and `μ_K` carried by the subgradient graph of `ψ̂_n`
  (cyclically monotone, hence optimal — Knott–Smith, the semi-discrete OT solution), and `F̂_n(x)` ANY subgradient of
  `ψ̂_n` at `x ∈ 𝒦` (the paper's "any selection"). This CLASS CONTAINS Ghosal–Sen's estimator — their eq. (14)
  `ψ̂*_n(x) = sup_{u ∈ S_K} ⟨x, u⟩ − ψ̂_n(u)` is convex and `sup_{S_K} ‖u‖ ≤ M`-Lipschitz, the semi-discrete coupling
  `(∇ψ̂_n, id)#μ_K` is carried by the (closed) graph of `∂ψ̂*_n` by Fenchel–Young, and `R̂_n = ∂ψ̂*_n` (eq. (15)) with
  the randomised ranks (16) is a selection — so the claims (for EVERY member) are stronger than the paper's; the
  membership is argued here, not formalised. No measurability in `ω` is assumed (the conclusion is outside a null
  set). The A/B conclusions are the frozen ones verbatim (B at `M_K = I`).

Critic notes:
* Proved in `WaveP3c/Route{McCann,Cond,Lip,Sieve,GS,Implies}.lean` with the new library
  `Foundations/GhosalSen/LipschitzPotential` (untrusted). McCann without moments (`RouteMcCann`): the source is
  truncated as well as the target — `P_n = P[· | B(0, n + N)]` (bounded, Lipschitz-null, `P_n ⇀ P`), `Q_n = T_n#Q`
  (wave 25b) — the frozen `brenier_exists_H` gives cyclically monotone maps `P_n → Q_n`, a cluster point of the graph
  plans (Prokhorov for couplings, Tau Ceti) couples `P` and `Q` with cyclically monotone support, Rockafellar's theorem
  puts it in `∂ψ`, and the Lipschitz-hypersurface cover of the multivalued set of `∂ψ` makes it a graph plan (the
  wave-25b route truncated the target only). The graph of `∂ψ` (any `ψ : H → EReal`) is cyclically monotone (Tau
  Ceti), so the map is `IsCMMapAE`. Lipschitz potentials: `φ(z) = sup_{(x,y) ∈ C} ψ(x) + ⟨y, z − x⟩` over the bounded
  piece `C` of the graph of `∂ψ` (Rockafellar §24). The C discharges combine `mccann_exists_fd` with the first conjunct
  of the certified wave-L8 `cond_potentials_weighted` for `χ`; the transfer claims extract a fitted `ω` from
  `∀ᵐ ω ∂P` (`P ≠ 0` because `P.map (F ∘ Z) = μ` is a probability). Ghosal–Sen: on the Varadarajan event
  (`Foundations/Empirical`, no moment) the certified wave-25b `app_ghs_stability_fd` applies with `P_n = P̂_n`,
  `Q_n = μ_K`, `D_n = ℝ^K` (subgradients of the `M`-Lipschitz `ψ̂_n` have norm `≤ M`); then the frozen
  `consistency_A`, `consistency_B`. `semidiscrete_exists`: the McCann map from `μ_K` to `P̂_n`, swapped,
  Rockafellar and the Lipschitz regularisation (the subgradient graph of a continuous function is closed, so it
  contains the support).
* Critic check (mechanical): each second conjunct is proved in `RouteCond`/`RouteSieve` by the frozen wave-L8 theorem
  applied to exactly its own hypotheses and `RouteImplies` derives the frozen claim from it, so the second conjunct is
  the frozen claim (no premise added or dropped beyond the discharged ones); `consistency_{A,B}_gs` apply the frozen
  wave-24a theorems at `E = ℝ^K` to `ghosal_sen_uniform`. All 17 claims: `example : Claims.X := X`, kernel dependencies
  `propext`, `Classical.choice`, `Quot.sound` only.
* No tautology: the existence conjuncts and the uniform convergence are not among the hypotheses. No junk: every `map`
  is guarded by `Measurable` (or is Tau Ceti's `ProbabilityMeasure` push-forward of a continuous map); the only
  `sSup` is the frozen one of `cond_rank_consistency_uncond`.
* Nonvacuity: C — `K = 1`, `μ` uniform on `[0, 1]`, `P` standard Cauchy: `RefLaw` holds and McCann's map (the Cauchy
  quantile function) is produced, where the frozen forms needed it as input. Ghosal–Sen — `K = 1`, `P_K` uniform on
  `[0, 1]`, `μ_K = P_K`, `ψ = x²/2` on `[0,1]` extended linearly (convex, 1-Lipschitz, `F = id` on `[0, 1]`), `𝒦 =
  [1/4, 3/4]`, and the estimator of `semidiscrete_exists` at every `(n, ω)`.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/
set_option linter.style.longLine false

noncomputable section

namespace StatFormal.WaveP3c

namespace Claims

/-! ### McCann existence with no moment -/

section McCann

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace
open StatFormal.OTFD.WaveL1 (IsCMMapAE LipNull Euc)

/-- A `thm:app-ghs-existence` (GHS Thm 2.3), NO moment: the frozen `StatFormal.Wave25b.Claims.app_ghs_existence` with
`PellClass (P : Measure H)` replaced by `LipNull (P : Measure H)` (the second moment of the source deleted). -/
def ghs_existence_lipNull : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (P Q : ProbabilityMeasure H),
    LipNull (P : Measure H) →
      ∃ (ψ : H → EReal) (F : H → H), Convex ℝ {p : H × ℝ | ψ p.1 ≤ p.2} ∧ LowerSemicontinuous ψ ∧
        (∀ x, ψ x ≠ ⊥) ∧ (∃ x, ψ x ≠ ⊤) ∧ Measurable F ∧ (P : Measure H).map F = Q ∧
        ∀ᵐ x ∂(P : Measure H), TauCeti.subdifferential (innerₗ H) ψ x = {F x}

/-- McCann existence in `H`, no moment: for `P` null on Lipschitz hypersurfaces and ANY target `Q`, a Borel map `F`,
`P`-a.e. cyclically monotone, pushes `P` to `Q`. -/
def mccann_exists_H : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (P Q : ProbabilityMeasure H),
    LipNull (P : Measure H) →
      ∃ F : H → H, Measurable F ∧ (P : Measure H).map F = Q ∧ IsCMMapAE (P : Measure H) F

/-- McCann (1995), existence: `P ≪ Leb` in `ℝ^K`, ANY target `Q`, no moment. -/
def mccann_exists_fd : Prop :=
  ∀ (K : ℕ) (P Q : ProbabilityMeasure (Euc K)), (P : Measure (Euc K)) ≪ volume →
    ∃ F : Euc K → Euc K, Measurable F ∧ (P : Measure (Euc K)).map F = Q ∧ IsCMMapAE (P : Measure (Euc K)) F

end McCann

/-! ### C: the population map is no longer a premise (paper's fit assumption, moment-free) -/

section CondMcCann

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace
open StatFormal.OTFD.WaveL1 (IsCMMapAE Euc)
open StatFormal.OTFD.WaveL3 (RefLaw)
open StatFormal.OTFD.WaveL4 (WeightedFit)
open StatFormal.OTFD.Wave19a (extTop)

/-- C `prop:conditional-potentials`, population map DISCHARGED: a McCann map `Q` from `μ_K` to `P_K` exists, and the
frozen moment-free `StatFormal.OTFD.WaveL8.Claims.cond_potentials_weighted` holds for every such map. -/
def cond_potentials_weighted_mccann : Prop :=
  ∀ (K : ℕ) (μ P : ProbabilityMeasure (Euc K)) (U : Set (Euc K))
    (α ν : ℕ → ProbabilityMeasure (Euc K)) (χn g : ℕ → Euc K → ℝ) (ζ : ℕ → ℝ),
    RefLaw (μ : Measure (Euc K)) U → WeightedFit μ P U α ν χn g ζ →
      (∃ Q : Euc K → Euc K, Measurable Q ∧ (μ : Measure (Euc K)).map Q = P ∧ IsCMMapAE (μ : Measure (Euc K)) Q) ∧
      ∀ Q : Euc K → Euc K, Measurable Q → (μ : Measure (Euc K)).map Q = P → IsCMMapAE (μ : Measure (Euc K)) Q →
      (∃ χ : Euc K → ℝ, ConvexOn ℝ (interior U) χ ∧ Q =ᵐ[(μ : Measure (Euc K))] gradient χ ∧
          IsGLB (χ '' interior U) 0) ∧
        ∀ χ : Euc K → ℝ, ConvexOn ℝ (interior U) χ → Q =ᵐ[(μ : Measure (Euc K))] gradient χ →
          IsGLB (χ '' interior U) 0 → ∀ c : ℕ → ℝ, (∀ n, IsGLB (χn n '' U) (c n)) →
            ∀ S ⊆ interior U, IsCompact S →
              TendstoUniformlyOn (fun n u => χn n u - c n) χ atTop S ∧
                TendstoUniformlyOn (fun n u => g n u - c n) χ atTop S

/-- C `thm:conditional-band-limits` (maps), population map DISCHARGED: a McCann map `Q` from `μ_K` to `P_K` with a
normalised convex potential `χ` (`Q = ∇χ` `μ_K`-a.e.) exists, and the frozen moment-free
`StatFormal.OTFD.WaveL8.Claims.cond_maps_ae_weighted` holds for every such pair. -/
def cond_maps_ae_weighted_mccann : Prop :=
  ∀ (K : ℕ) (μ P : ProbabilityMeasure (Euc K)) (U : Set (Euc K))
    (Qn : ℕ → Euc K → Euc K) (α ν : ℕ → ProbabilityMeasure (Euc K))
    (χn g : ℕ → Euc K → ℝ) (ζ : ℕ → ℝ),
    RefLaw (μ : Measure (Euc K)) U →
    WeightedFit μ P U α ν χn g ζ → (∀ n, ConvexOn ℝ (interior U) (g n)) →
    (∀ n, ∀ u ∈ interior U, Qn n u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n)) u) →
      (∃ (χ : Euc K → ℝ) (Q : Euc K → Euc K), Measurable Q ∧ (μ : Measure (Euc K)).map Q = P ∧
          IsCMMapAE (μ : Measure (Euc K)) Q ∧ ConvexOn ℝ (interior U) χ ∧
          Q =ᵐ[(μ : Measure (Euc K))] gradient χ ∧ IsGLB (χ '' interior U) 0) ∧
      ∀ (χ : Euc K → ℝ) (Q : Euc K → Euc K), Measurable Q → (μ : Measure (Euc K)).map Q = P →
        ConvexOn ℝ (interior U) χ → Q =ᵐ[(μ : Measure (Euc K))] gradient χ →
        ∀ᵐ u ∂(μ : Measure (Euc K)), u ∈ interior U ∧ DifferentiableAt ℝ χ u ∧
          Tendsto (fun n => Qn n u) atTop (𝓝 (Q u))

/-- C `thm:conditional-band-limits` (one-sided band limits), population map DISCHARGED: the population pair `(χ, Q)`
exists as in `cond_maps_ae_weighted_mccann`, and the frozen moment-free
`StatFormal.OTFD.WaveL8.Claims.cond_band_one_sided_weighted` holds for every such pair. -/
def cond_band_one_sided_weighted_mccann : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ P : ProbabilityMeasure (Euc K)) (U : Set (Euc K))
    (Qn : ℕ → Euc K → Euc K) (α ν : ℕ → ProbabilityMeasure (Euc K))
    (χn g : ℕ → Euc K → ℝ) (ζ : ℕ → ℝ) (e : 𝒯 → Euc K) (EK : ℝ),
    RefLaw (μ : Measure (Euc K)) U →
    WeightedFit μ P U α ν χn g ζ → (∀ n, ConvexOn ℝ (interior U) (g n)) →
    (∀ n, ∀ u ∈ interior U, Qn n u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n)) u) →
    (∀ t, ‖e t‖ ≤ EK) →
      (∃ (χ : Euc K → ℝ) (Q : Euc K → Euc K), Measurable Q ∧ (μ : Measure (Euc K)).map Q = P ∧
          IsCMMapAE (μ : Measure (Euc K)) Q ∧ ConvexOn ℝ (interior U) χ ∧
          Q =ᵐ[(μ : Measure (Euc K))] gradient χ ∧ IsGLB (χ '' interior U) 0) ∧
      ∀ (A : Set (Euc K)) (χ : Euc K → ℝ) (Q : Euc K → Euc K) (R : ℝ), Measurable Q →
        (μ : Measure (Euc K)).map Q = P →
        ConvexOn ℝ (interior U) χ → Q =ᵐ[(μ : Measure (Euc K))] gradient χ →
        MeasurableSet A → (∀ᵐ u ∂(μ : Measure (Euc K)).restrict A, ‖Q u‖ ≤ R) →
          ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t,
            StatFormal.Wave17a.hPop (μ : Measure (Euc K)) A Q (e t) ≤ StatFormal.Wave21b.supE A (Qn n) (e t) + η ∧
              StatFormal.Wave17a.hPop (μ : Measure (Euc K)) A Q (-e t) ≤ StatFormal.Wave21b.supE A (Qn n) (-e t) + η

/-- C `cor:conditional-test-coverage`, population map DISCHARGED: the population pair `(χ, Q)` exists as in
`cond_maps_ae_weighted_mccann`, and the frozen moment-free `StatFormal.OTFD.WaveL8.Claims.cond_test_coverage_weighted`
holds for every such pair. -/
def cond_test_coverage_weighted_mccann : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ P : ProbabilityMeasure (Euc K)) (U : Set (Euc K))
    (Qn : ℕ → Euc K → Euc K) (α ν : ℕ → ProbabilityMeasure (Euc K))
    (χn g : ℕ → Euc K → ℝ) (ζ : ℕ → ℝ) (m : 𝒯 → ℝ) (e : 𝒯 → Euc K)
    (Ue Le : ℕ → 𝒯 → EReal) (EK κ : ℝ),
    RefLaw (μ : Measure (Euc K)) U →
    WeightedFit μ P U α ν χn g ζ → (∀ n, ConvexOn ℝ (interior U) (g n)) →
    (∀ n, ∀ u ∈ interior U, Qn n u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n)) u) →
    (∀ t, ‖e t‖ ≤ EK) → 0 < κ →
      (∃ (χ : Euc K → ℝ) (Q : Euc K → Euc K), Measurable Q ∧ (μ : Measure (Euc K)).map Q = P ∧
          IsCMMapAE (μ : Measure (Euc K)) Q ∧ ConvexOn ℝ (interior U) χ ∧
          Q =ᵐ[(μ : Measure (Euc K))] gradient χ ∧ IsGLB (χ '' interior U) 0) ∧
      ∀ (A : Set (Euc K)) (χ : Euc K → ℝ) (Q : Euc K → Euc K) (R p : ℝ), Measurable Q →
        (μ : Measure (Euc K)).map Q = P →
        ConvexOn ℝ (interior U) χ → Q =ᵐ[(μ : Measure (Euc K))] gradient χ →
        MeasurableSet A → (∀ᵐ u ∂(μ : Measure (Euc K)).restrict A, ‖Q u‖ ≤ R) →
        ENNReal.ofReal p ≤ (μ : Measure (Euc K)) A →
        (∀ n t, (m t : EReal) + StatFormal.Wave21b.supE A (Qn n) (e t) ≤ Ue n t ∧
          Le n t ≤ (m t : EReal) - StatFormal.Wave21b.supE A (Qn n) (-e t)) →
          ∀ᶠ n in atTop, ∃ E : Set (Euc K), MeasurableSet E ∧
            E ⊆ {z | ∀ t, Le n t - κ ≤ ((m t + ⟪e t, z⟫ : ℝ) : EReal) ∧ ((m t + ⟪e t, z⟫ : ℝ) : EReal) ≤ Ue n t + κ} ∧
            ENNReal.ofReal p ≤ (μ : Measure (Euc K)).map Q E

/-- C `prop:cond-transfer-consistency`, population map DISCHARGED: a McCann map `Q'` from `μ_K` to `P'_K` with a
normalised convex potential `χ'` exists, and the frozen moment-free
`StatFormal.OTFD.WaveL8.Claims.cond_transfer_consistency_weighted` holds for every such pair. -/
def cond_transfer_consistency_weighted_mccann : Prop :=
  ∀ (K : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (μ P' : ProbabilityMeasure (Euc K)) (U DF : Set (Euc K))
    (Z : Ω → Euc K) (F : Euc K → Euc K) (Fh : ℕ → Ω → Euc K → Euc K)
    (Qh : ℕ → Ω → Euc K → Euc K) (α ν : ℕ → Ω → ProbabilityMeasure (Euc K)) (χn g : ℕ → Ω → Euc K → ℝ) (ζ : ℕ → Ω → ℝ),
    RefLaw (μ : Measure (Euc K)) U → Measurable Z → Measurable F → P.map (fun ω => F (Z ω)) = μ →
    (∀ᵐ ω ∂P, Z ω ∈ DF) → (∀ᵐ ω ∂P, ∀ z ∈ DF, Tendsto (fun n => Fh n ω z) atTop (𝓝 (F z))) →
    (∀ᵐ ω ∂P, WeightedFit μ P' U (fun n => α n ω) (fun n => ν n ω) (fun n => χn n ω) (fun n => g n ω)
        (fun n => ζ n ω) ∧
      ∀ n, ConvexOn ℝ (interior U) (g n ω)) →
    (∀ n ω, ∀ u ∈ interior U, Qh n ω u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n ω)) u) →
      (∃ (χ' : Euc K → ℝ) (Q' : Euc K → Euc K), Measurable Q' ∧ (μ : Measure (Euc K)).map Q' = P' ∧
          IsCMMapAE (μ : Measure (Euc K)) Q' ∧ ConvexOn ℝ (interior U) χ' ∧
          Q' =ᵐ[(μ : Measure (Euc K))] gradient χ' ∧ IsGLB (χ' '' interior U) 0) ∧
      ∀ (χ' : Euc K → ℝ) (Q' : Euc K → Euc K),
        ConvexOn ℝ (interior U) χ' → Q' =ᵐ[(μ : Measure (Euc K))] gradient χ' →
        Measurable Q' → (μ : Measure (Euc K)).map Q' = P' →
          ∀ᵐ ω ∂P, F (Z ω) ∈ interior U ∧ DifferentiableAt ℝ χ' (F (Z ω)) ∧ Q' (F (Z ω)) = gradient χ' (F (Z ω)) ∧
            Tendsto (fun n => Qh n ω (Fh n ω (Z ω))) atTop (𝓝 (Q' (F (Z ω))))

/-- C `prop:cond-transfer-consistency` (in probability), population map DISCHARGED: as
`cond_transfer_consistency_weighted_mccann`, with the frozen moment-free
`StatFormal.OTFD.WaveL8.Claims.cond_transfer_consistency_prob_weighted` as the second conjunct. -/
def cond_transfer_consistency_prob_weighted_mccann : Prop :=
  ∀ (K : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] (μ P' : ProbabilityMeasure (Euc K))
    (U DF : Set (Euc K)) (Z : Ω → Euc K) (F : Euc K → Euc K) (Fh : ℕ → Ω → Euc K → Euc K)
    (Qh : ℕ → Ω → Euc K → Euc K) (α ν : ℕ → Ω → ProbabilityMeasure (Euc K)) (χn g : ℕ → Ω → Euc K → ℝ) (ζ : ℕ → Ω → ℝ),
    RefLaw (μ : Measure (Euc K)) U → Measurable Z → Measurable F → P.map (fun ω => F (Z ω)) = μ →
    (∀ᵐ ω ∂P, Z ω ∈ DF) → (∀ᵐ ω ∂P, ∀ z ∈ DF, Tendsto (fun n => Fh n ω z) atTop (𝓝 (F z))) →
    (∀ᵐ ω ∂P, WeightedFit μ P' U (fun n => α n ω) (fun n => ν n ω) (fun n => χn n ω) (fun n => g n ω)
        (fun n => ζ n ω) ∧
      ∀ n, ConvexOn ℝ (interior U) (g n ω)) →
    (∀ n ω, ∀ u ∈ interior U, Qh n ω u ∈ TauCeti.subdifferential (innerₗ (Euc K)) (extTop (interior U) (g n ω)) u) →
    (∀ n, AEStronglyMeasurable (fun ω => Qh n ω (Fh n ω (Z ω))) P) →
      (∃ (χ' : Euc K → ℝ) (Q' : Euc K → Euc K), Measurable Q' ∧ (μ : Measure (Euc K)).map Q' = P' ∧
          IsCMMapAE (μ : Measure (Euc K)) Q' ∧ ConvexOn ℝ (interior U) χ' ∧
          Q' =ᵐ[(μ : Measure (Euc K))] gradient χ' ∧ IsGLB (χ' '' interior U) 0) ∧
      ∀ (χ' : Euc K → ℝ) (Q' : Euc K → Euc K),
        ConvexOn ℝ (interior U) χ' → Q' =ᵐ[(μ : Measure (Euc K))] gradient χ' →
        Measurable Q' → (μ : Measure (Euc K)).map Q' = P' →
          TendstoInMeasure P (fun n ω => Qh n ω (Fh n ω (Z ω))) atTop (fun ω => Q' (F (Z ω)))

end CondMcCann

section RankMcCann

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace
open StatFormal.Wave24e (ColumnEq rankMap)
open StatFormal.Wave23c (lagPot)

/-- C `lem:cond-rank-consistency`, population map DISCHARGED: a McCann map `Q` from `μ_K` to `P_K` exists, and the
frozen moment-free `StatFormal.OTFD.WaveL8.Claims.cond_rank_consistency_uncond` holds for every such map. -/
def cond_rank_consistency_mccann : Prop :=
  ∀ (K : ℕ) (n M : ℕ → ℕ) (ε : ℕ → ℝ) (R : ℝ) (z : ∀ k, Fin (n k + 1) → EuclideanSpace ℝ (Fin K))
    (f : ∀ k, Fin (n k + 1) → ℝ) (u : ∀ k, Fin (M k + 1) → EuclideanSpace ℝ (Fin K)) (g : ∀ k, Fin (M k + 1) → ℝ)
    (μ P : ProbabilityMeasure (EuclideanSpace ℝ (Fin K))) (U : Set (EuclideanSpace ℝ (Fin K)))
    (α ν : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin K))) (ζ : ℕ → ℝ) (ρ : Measure (EuclideanSpace ℝ (Fin K))),
    StatFormal.OTFD.WaveL3.RefLaw (μ : Measure (EuclideanSpace ℝ (Fin K))) U →
    StatFormal.OTFD.WaveL4.WeightedFit μ P U α ν (fun k => lagPot (z k) (f k)) (fun k => lagPot (z k) (f k)) ζ →
    (∀ k, (α k : Measure (EuclideanSpace ℝ (Fin K))) =
      ∑ j, ENNReal.ofReal (1 / ((M k : ℝ) + 1)) • Measure.dirac (u k j)) → (∀ k j, u k j ∈ U) →
    (∀ k, 0 < ε k) → Tendsto (fun k => ε k * Real.log (((M k : ℝ) + 1) * ((n k : ℝ) + 1))) atTop (𝓝 0) →
    (∀ k, ColumnEq (ε k) (z k) (f k) (u k) (g k)) → (∀ k i, ‖z k i‖ ≤ R) → ρ ≪ volume →
      (∃ Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K), Measurable Q ∧
          (μ : Measure (EuclideanSpace ℝ (Fin K))).map Q = P ∧
          StatFormal.OTFD.WaveL1.IsCMMapAE (μ : Measure (EuclideanSpace ℝ (Fin K))) Q) ∧
      ∀ Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K), Measurable Q →
        (μ : Measure (EuclideanSpace ℝ (Fin K))).map Q = P →
        StatFormal.OTFD.WaveL1.IsCMMapAE (μ : Measure (EuclideanSpace ℝ (Fin K))) Q →
      (∃ χ : EuclideanSpace ℝ (Fin K) → ℝ, ConvexOn ℝ (interior U) χ ∧
          Q =ᵐ[(μ : Measure (EuclideanSpace ℝ (Fin K)))] gradient χ ∧ IsGLB (χ '' interior U) 0) ∧
        ∀ χ : EuclideanSpace ℝ (Fin K) → ℝ, ConvexOn ℝ (interior U) χ →
          Q =ᵐ[(μ : Measure (EuclideanSpace ℝ (Fin K)))] gradient χ → IsGLB (χ '' interior U) 0 →
          (∀ y, DifferentiableAt ℝ (fun y' => sSup ((fun w => ⟪w, y'⟫ - χ w) '' interior U)) y →
            Tendsto (fun k => rankMap (ε k) (u k) (g k) y) atTop
              (𝓝 (gradient (fun y' => sSup ((fun w => ⟪w, y'⟫ - χ w) '' interior U)) y))) ∧
          ∀ᵐ y ∂ρ, Tendsto (fun k => rankMap (ε k) (u k) (g k) y) atTop
            (𝓝 (gradient (fun y' => sSup ((fun w => ⟪w, y'⟫ - χ w) '' interior U)) y))

end RankMcCann

/-! ### A `thm:app-ghosalsen-rate` (Ghosal–Sen Thm 4.1, compacts of the interior) and the discharge of A/B
`thm:consistency` -/

section GhosalSen

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace
open StatFormal.OTFD.WaveL1 (Euc)
open StatFormal.OTFD.Wave22a (IsSubgrad)
open TauCeti.Probability (empiricalMeasure)

/-- A `cor:app-ghs-lipschitz` with the existence of `thm:app-ghs-existence`, NO moment: for `P` null on Lipschitz
hypersurfaces and `Q` carried by `B(0, M)`, a convex `M`-Lipschitz `ψ : H → ℝ` and a Borel `F` with `F#P = Q` and
`F(x)` a subgradient of `ψ` at `x` for `P`-a.e. `x` (the population block of hypotheses of `app_ghs_stability_*`,
`sieve_conv_*` and `ghosal_sen_uniform`). -/
def ghs_lipschitz_exists : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (P Q : ProbabilityMeasure H) (M : ℝ),
    StatFormal.OTFD.WaveL1.LipNull (P : Measure H) → (Q : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
      ∃ (ψ : H → ℝ) (F : H → H), ConvexOn ℝ univ ψ ∧ (∀ x x', |ψ x - ψ x'| ≤ M * ‖x - x'‖) ∧
        Measurable F ∧ (P : Measure H).map F = Q ∧ ∀ᵐ x ∂(P : Measure H), IsSubgrad ψ x (F x)

/-- The semi-discrete estimator of `thm:consistency` exists: for a Lipschitz-null reference `μ` carried by `B(0, M)`
and ANY law `α` (in particular every empirical measure `P̂_n`), a convex `M`-Lipschitz potential `ψ̂` and a coupling
of `α` and `μ` carried by the subgradient graph of `ψ̂` (so the estimator hypotheses of `ghosal_sen_uniform` can be
met at every `n` and `ω`). -/
def semidiscrete_exists : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (α μ : ProbabilityMeasure H) (M : ℝ),
    StatFormal.OTFD.WaveL1.LipNull (μ : Measure H) → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
      ∃ (ψh : H → ℝ) (γ : ProbabilityMeasure (H × H)), ConvexOn ℝ univ ψh ∧
        (∀ x x', |ψh x - ψh x'| ≤ M * ‖x - x'‖) ∧ (γ : Measure (H × H)).fst = α ∧
        (γ : Measure (H × H)).snd = μ ∧ (γ : Measure (H × H)).support ⊆ {p | IsSubgrad ψh p.1 p.2}

/-- A `thm:app-ghosalsen-rate` (Ghosal–Sen 2022, Thm 4.1(b), semi-discrete rank map): data `Z_0, Z_1, …` iid
`P_K ≪ Leb` on `ℝ^K` (no moment), reference `μ_K` carried by `B(0, M)`; the population rank map `F` is `P_K`-a.e. a
subgradient of a convex `L`-Lipschitz `ψ` with `F#P_K = μ_K`, and `ψ` is differentiable with gradient `F` at every
point of the compact `𝒦 ⊆ int supp P_K` (implied by the paper's homeomorphism hypothesis). The semi-discrete estimator at sample size `n + 1`: a convex `M`-Lipschitz potential
`ψ̂_n` (the conjugate of the reference-side dual potential over a set in `B(0, M)`) and a coupling `γ_n` of the
empirical measure `P̂_n` and `μ_K` carried by the subdifferential graph of `ψ̂_n` (a cyclically monotone, hence
optimal, coupling); `F̂_n(x)` any subgradient of `ψ̂_n` at `x ∈ 𝒦`. Then almost surely `F̂_n → F` uniformly on `𝒦`. -/
def ghosal_sen_uniform : Prop :=
  ∀ (K : ℕ) (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (Z : ℕ → Ω → Euc K)
    (P μ : ProbabilityMeasure (Euc K)) (ψ : Euc K → ℝ) (F : Euc K → Euc K) (M L : ℝ)
    (ψh : ℕ → Ω → Euc K → ℝ) (γ : ℕ → Ω → ProbabilityMeasure (Euc K × Euc K)) (Fh : ℕ → Ω → Euc K → Euc K)
    (𝒦 : Set (Euc K)),
    iIndepFun Z Pr → (∀ i, HasLaw (Z i) (P : Measure (Euc K)) Pr) → (P : Measure (Euc K)) ≪ volume →
    (μ : Measure (Euc K)) (Metric.closedBall 0 M)ᶜ = 0 →
    ConvexOn ℝ univ ψ → (∀ x x', |ψ x - ψ x'| ≤ L * ‖x - x'‖) →
    Measurable F → (P : Measure (Euc K)).map F = μ → (∀ᵐ x ∂(P : Measure (Euc K)), IsSubgrad ψ x (F x)) →
    IsCompact 𝒦 → 𝒦 ⊆ interior (P : Measure (Euc K)).support → (∀ x ∈ 𝒦, HasGradientAt ψ (F x) x) →
    (∀ n ω, (γ n ω : Measure (Euc K × Euc K)).fst = (empiricalMeasure (fun i => Z i ω) n : Measure (Euc K))) →
    (∀ n ω, (γ n ω : Measure (Euc K × Euc K)).snd = μ) →
    (∀ n ω, (γ n ω : Measure (Euc K × Euc K)).support ⊆ {p | IsSubgrad (ψh n ω) p.1 p.2}) →
    (∀ n ω x x', |ψh n ω x - ψh n ω x'| ≤ M * ‖x - x'‖) →
    (∀ n ω, ∀ x ∈ 𝒦, IsSubgrad (ψh n ω) x (Fh n ω x)) →
      ∀ᵐ ω ∂Pr, TendstoUniformlyOn (fun n => Fh n ω) F atTop 𝒦

/-- A `thm:consistency`, Ghosal–Sen premise DISCHARGED: the frozen `StatFormal.Wave24a.Claims.consistency_A` at
`E = ℝ^K` with its hypothesis "`F̂ → F` uniformly on `𝒦` almost surely" replaced by the hypotheses of
`ghosal_sen_uniform` (the semi-discrete estimator of `thm:consistency`). -/
def consistency_A_gs : Prop :=
  ∀ (K : ℕ) (Ω H : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (Z : ℕ → Ω → Euc K)
    (P μ : ProbabilityMeasure (Euc K)) (ψ : Euc K → ℝ) (F : Euc K → Euc K) (M L : ℝ)
    (ψh : ℕ → Ω → Euc K → ℝ) (γ : ℕ → Ω → ProbabilityMeasure (Euc K × Euc K)) (Fh : ℕ → Ω → Euc K → Euc K)
    (𝒦 : Set (Euc K)) (PiK : H → Euc K) (Lm : Euc K →L[ℝ] Euc K),
    iIndepFun Z Pr → (∀ i, HasLaw (Z i) (P : Measure (Euc K)) Pr) → (P : Measure (Euc K)) ≪ volume →
    (μ : Measure (Euc K)) (Metric.closedBall 0 M)ᶜ = 0 →
    ConvexOn ℝ univ ψ → (∀ x x', |ψ x - ψ x'| ≤ L * ‖x - x'‖) →
    Measurable F → (P : Measure (Euc K)).map F = μ → (∀ᵐ x ∂(P : Measure (Euc K)), IsSubgrad ψ x (F x)) →
    IsCompact 𝒦 → 𝒦 ⊆ interior (P : Measure (Euc K)).support → (∀ x ∈ 𝒦, HasGradientAt ψ (F x) x) →
    (∀ n ω, (γ n ω : Measure (Euc K × Euc K)).fst = (empiricalMeasure (fun i => Z i ω) n : Measure (Euc K))) →
    (∀ n ω, (γ n ω : Measure (Euc K × Euc K)).snd = μ) →
    (∀ n ω, (γ n ω : Measure (Euc K × Euc K)).support ⊆ {p | IsSubgrad (ψh n ω) p.1 p.2}) →
    (∀ n ω x x', |ψh n ω x - ψh n ω x'| ≤ M * ‖x - x'‖) →
    (∀ n ω, ∀ x ∈ 𝒦, IsSubgrad (ψh n ω) x (Fh n ω x)) →
      ∀ᵐ ω ∂Pr, TendstoUniformlyOn (fun n x => 1 - ‖Lm (Fh n ω (PiK x))‖) (fun x => 1 - ‖Lm (F (PiK x))‖) atTop
        {x | PiK x ∈ 𝒦}

/-- B `thm:consistency` at the Euclidean cost `M_K = I`, Ghosal–Sen premise DISCHARGED: the frozen
`StatFormal.Wave24a.Claims.consistency_B` at `E = ℝ^K` with its hypothesis "`F̂ → F` uniformly on `𝒦` almost surely"
replaced by the hypotheses of `ghosal_sen_uniform`. -/
def consistency_B_gs : Prop :=
  ∀ (K : ℕ) (Ω H : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (Z : ℕ → Ω → Euc K)
    (P μ : ProbabilityMeasure (Euc K)) (ψ : Euc K → ℝ) (F : Euc K → Euc K) (M L : ℝ)
    (ψh : ℕ → Ω → Euc K → ℝ) (γ : ℕ → Ω → ProbabilityMeasure (Euc K × Euc K)) (Fh : ℕ → Ω → Euc K → Euc K)
    (𝒦 : Set (Euc K)) (PiK : H → Euc K) (g : Euc K → ℝ) (cK : ℝ → ℝ) (c' : ℝ),
    iIndepFun Z Pr → (∀ i, HasLaw (Z i) (P : Measure (Euc K)) Pr) → (P : Measure (Euc K)) ≪ volume →
    (μ : Measure (Euc K)) (Metric.closedBall 0 M)ᶜ = 0 →
    ConvexOn ℝ univ ψ → (∀ x x', |ψ x - ψ x'| ≤ L * ‖x - x'‖) →
    Measurable F → (P : Measure (Euc K)).map F = μ → (∀ᵐ x ∂(P : Measure (Euc K)), IsSubgrad ψ x (F x)) →
    IsCompact 𝒦 → 𝒦 ⊆ interior (P : Measure (Euc K)).support → (∀ x ∈ 𝒦, HasGradientAt ψ (F x) x) →
    (∀ n ω, (γ n ω : Measure (Euc K × Euc K)).fst = (empiricalMeasure (fun i => Z i ω) n : Measure (Euc K))) →
    (∀ n ω, (γ n ω : Measure (Euc K × Euc K)).snd = μ) →
    (∀ n ω, (γ n ω : Measure (Euc K × Euc K)).support ⊆ {p | IsSubgrad (ψh n ω) p.1 p.2}) →
    (∀ n ω x x', |ψh n ω x - ψh n ω x'| ≤ M * ‖x - x'‖) →
    (∀ n ω, ∀ x ∈ 𝒦, IsSubgrad (ψh n ω) x (Fh n ω x)) →
    (∀ a b, g (a + b) ≤ g a + g b) → (∀ a, g (-a) = g a) → (∀ a, g a ≤ c' * ‖a‖) → Continuous cK →
    (∀ z ∈ 𝒦, g (F z) ≤ 1) →
      (∀ n ω x, |(1 - g (Fh n ω (PiK x))) - (1 - g (F (PiK x)))| ≤ c' * ‖Fh n ω (PiK x) - F (PiK x)‖) ∧
      ∀ᵐ ω ∂Pr, TendstoUniformlyOn (fun n x => 1 - g (Fh n ω (PiK x))) (fun x => 1 - g (F (PiK x))) atTop
          {x | PiK x ∈ 𝒦} ∧
        TendstoUniformlyOn (fun n x => 1 - cK (g (Fh n ω (PiK x)))) (fun x => 1 - cK (g (F (PiK x)))) atTop
          {x | PiK x ∈ 𝒦}

end GhosalSen

/-! ### A `thm:sieve-convergence`: the potentials are no longer premises -/

section SieveMcCann

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace
open StatFormal.OTFD.WaveL1 (LipNull Euc)
open StatFormal.OTFD.Wave1 (truncK)
open StatFormal.OTFD.Wave22a (IsSubgrad)

/-- A `thm:sieve-convergence` (weak form), potentials DISCHARGED: for `P` Lipschitz-null (no moment) and `μ` carried by
`B(0, M)`, the population potential `ψ` (convex, `M`-Lipschitz, `F = ∇ψ` `P`-a.e., `F#P = μ`) and the projected
potentials `φ_K` (convex, `M`-Lipschitz, `F_K = ∇φ_K` `P_K`-a.e., `F_K#P_K = μ_K`, `P_K = Π_K#P`, `μ_K = Π_K#μ`)
exist, and the frozen moment-free `StatFormal.OTFD.WaveL8.Claims.sieve_conv_weak` holds at `(e, P, μ, M)` for every
such choice. -/
def sieve_conv_weak_mccann : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (P μ : ProbabilityMeasure H) (M : ℝ),
    Orthonormal ℝ e → LipNull (P : Measure H) → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
      (∃ (ψ : H → ℝ) (F : H → H) (φ : (K : ℕ) → Euc K → ℝ) (FK : (K : ℕ) → Euc K → Euc K),
        ConvexOn ℝ univ ψ ∧ (∀ x x', |ψ x - ψ x'| ≤ M * ‖x - x'‖) ∧
        Measurable F ∧ (P : Measure H).map F = μ ∧ (∀ᵐ x ∂(P : Measure H), IsSubgrad ψ x (F x)) ∧
        (∀ K, ConvexOn ℝ univ (φ K)) ∧ (∀ K z z', |φ K z - φ K z'| ≤ M * ‖z - z'‖) ∧ (∀ K, Measurable (FK K)) ∧
        (∀ K, ((P : Measure H).map (truncK e K)).map (FK K) = (μ : Measure H).map (truncK e K)) ∧
        (∀ K, ∀ᵐ z ∂((P : Measure H).map (truncK e K)), IsSubgrad (φ K) z (FK K z))) ∧
      ∀ (ψ : H → ℝ) (F : H → H) (Lψ Lφ : ℝ) (φ : (K : ℕ) → Euc K → ℝ) (FK : (K : ℕ) → Euc K → Euc K) (K₀ : Set H)
        (h : H),
        ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
        ConvexOn ℝ univ ψ → (∀ x x', |ψ x - ψ x'| ≤ Lψ * ‖x - x'‖) →
        Measurable F → (P : Measure H).map F = μ → (∀ᵐ x ∂(P : Measure H), IsSubgrad ψ x (F x)) →
        (∀ K z z', |φ K z - φ K z'| ≤ Lφ * ‖z - z'‖) → (∀ K, Measurable (FK K)) →
        (∀ K, ((P : Measure H).map (truncK e K)).map (FK K) = (μ : Measure H).map (truncK e K)) →
        (∀ K, ∀ᵐ z ∂((P : Measure H).map (truncK e K)), IsSubgrad (φ K) z (FK K z)) →
        IsCompact K₀ → K₀ ⊆ interior (P : Measure H).support →
        (∀ x ∈ K₀, ∀ v, HasLineDerivAt ℝ ψ ⟪F x, v⟫ x v) →
          ∀ ε : ℝ, 0 < ε → ∀ᶠ K in atTop, ∀ x ∈ K₀, ∀ y,
            IsSubgrad (fun x' => φ K (truncK e K x')) x y → |⟪y - F x, h⟫| ≤ ε

/-- A `thm:sieve-convergence` (norm form under `(⋆)`), potentials DISCHARGED: the same existence conjunct, and the
frozen moment-free `StatFormal.OTFD.WaveL8.Claims.sieve_conv_norm` at `(e, P, μ, M)` for every such choice. -/
def sieve_conv_norm_mccann : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (P μ : ProbabilityMeasure H) (M : ℝ),
    Orthonormal ℝ e → LipNull (P : Measure H) → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
      (∃ (ψ : H → ℝ) (F : H → H) (φ : (K : ℕ) → Euc K → ℝ) (FK : (K : ℕ) → Euc K → Euc K),
        ConvexOn ℝ univ ψ ∧ (∀ x x', |ψ x - ψ x'| ≤ M * ‖x - x'‖) ∧
        Measurable F ∧ (P : Measure H).map F = μ ∧ (∀ᵐ x ∂(P : Measure H), IsSubgrad ψ x (F x)) ∧
        (∀ K, ConvexOn ℝ univ (φ K)) ∧ (∀ K z z', |φ K z - φ K z'| ≤ M * ‖z - z'‖) ∧ (∀ K, Measurable (FK K)) ∧
        (∀ K, ((P : Measure H).map (truncK e K)).map (FK K) = (μ : Measure H).map (truncK e K)) ∧
        (∀ K, ∀ᵐ z ∂((P : Measure H).map (truncK e K)), IsSubgrad (φ K) z (FK K z))) ∧
      ∀ (ψ : H → ℝ) (F : H → H) (Lψ Lφ : ℝ) (φ : (K : ℕ) → Euc K → ℝ) (FK : (K : ℕ) → Euc K → Euc K)
        (K₀ C : Set H),
        ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
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

end SieveMcCann

end Claims

end StatFormal.WaveP3c
