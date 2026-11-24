import StatFormal.Archive.OTFD.WaveL7.Statements

/-!
# FROZEN STATEMENTS — otfd limits wave L9: A `lem:app-cm-plans`(iv), middle clause — the cyclically monotone map is
# the `A`-a.e. UNIQUE gradient of ANY convex function (finite, or proper extended-valued) pushing `A` to a bounded `μ`

Sources (verbatim in `lean-formalisation/inventory/extracted/otfd-A_sieves.md`; current text of `otfd/papers/`):
* A `lem:app-cm-plans`(iv) (`A_sieves/supplement.tex:1443-1448`): "If moreover `supp γ² ⊆ B̄_H(0,M)`, then `T = ∇f`
  `A`-a.e. for a finite convex `M`-Lipschitz `f`, so `T` is `A`-a.e. the unique gradient of a convex function pushing
  `A` forward to `γ²` (`cor:app-ghs-lipschitz`)", with the convention paragraph (`:1416-1427`: `D_f` = Gâteaux
  differentiability points; "the subdifferential graph of any convex `χ : H → (-∞, ∞]` is cyclically monotone").
* A `thm:app-ghs-existence` / `cor:app-ghs-lipschitz` (`:1060-1078`, GHS Thm 2.3, Cor. 2.7): the convex functions
  are proper l.s.c. `ψ : H → (-∞, ∞]`; "the gradient of a convex function pushing `P` forward to `Q` is `P`-a.e.
  unique" (bounded `supp Q`).
* The frozen wave-L7 claims (`OTFD/WaveL7/Statements.lean`): `ghs_grad_unique` (uniqueness only among finite convex
  LIPSCHITZ potentials, declared there as the remaining gap) and `brenier_uniq_H_bdd`; the frozen wave-23d
  `GHSGradUnique`, `GatDiff`, `cm_graph_gradient`.
Imports the frozen `OTFD/WaveL7` statements (through them `OTFD/WaveL1` `CycMon`, `CMConc`, `IsCMMapAE`, `Graph`,
`BrenierUniq`, `LipNull` and `Wave23d` `GatDiff`, `GHSGradUnique`), not copied. Mathlib otherwise.

Covered:
* `cm_grad_unique_convex`: GHS Cor. 2.7's uniqueness clause for ALL finite convex potentials (no Lipschitz bound),
  bounded target, no moment: two `A`-a.e. Gâteaux gradients of finite convex functions pushing `A` to `B` agree
  `A`-a.e. It is `GHSGradUnique` with the two Lipschitz hypotheses deleted, `Measurable` weakened to `AEMeasurable`,
  and the target bound `B (B̄(0, M))ᶜ = 0` added (which the Lipschitz hypotheses made automatic in `ghs_grad_unique`);
  so it implies `ghs_grad_unique` (route theorem `ghs_grad_unique_of_convex`).
* `cm_grad_unique_proper`: the same among proper extended-valued convex potentials `φ : H → (-∞, ∞]`.
* `cm_subgrad_unique_proper`: the same among `A`-a.e. SUBGRADIENT selections of proper convex potentials, so every
  reading of "gradient" that yields a subgradient is covered (see Encodings).
* `cm_grad_eq_map`: on the objects of the frozen `brenier_uniq_H_bdd`: if `F` is a Borel `P`-a.e. cyclically monotone
  map with `F#P = μ` bounded, every gradient of a proper convex potential pushing `P` to `μ` equals `F` `P`-a.e.
* `cm_plans_iv_grad`: (iv)'s middle clause as printed: the map `T` of a cyclically monotone `γ` with bounded `γ²`
  is the `A`-a.e. gradient of a finite convex `M`-Lipschitz `f` AND every gradient of any proper convex potential
  pushing `A` to `γ²` equals `T` `A`-a.e.

Encodings (to be checked by the critic):
* A proper convex `φ : H → (-∞, ∞]` is the pair `(C, f)`: `C = dom φ` (convex, possibly any convex set) and
  `f : H → ℝ` with `ConvexOn ℝ C f`; `φ = f` on `C`, `φ = +∞` off `C` (every proper convex `φ` arises so, with
  `f = φ.toReal`; the values of `f` off `C` are never read, see below). Lower semicontinuity is NOT assumed
  (generalisation; it is not needed). Finite convex potentials are `C = univ`.
* Gâteaux gradient of `φ` at `x` (`GatDiffDom C f x g`): for every direction `h`, the line `t ↦ x + t h` stays in `C`
  for `t` near `0` (`x` is in the core of `dom φ`, which for a l.s.c. `φ` is `int dom φ`) and `t ↦ f(x + t h)` has
  derivative `⟨g, h⟩` at `0`. Because the line stays in `C` near `0`, `HasDerivAt` only reads `f` on `C`: no junk
  value of `f` off `dom φ` can manufacture or mask a gradient. With `C = univ` it is the frozen `GatDiff`. This is
  the literal Gâteaux limit `(φ(x + th) − φ(x))/t → ⟨g, h⟩` for an extended-valued `φ` (a finite limit forces
  `φ(x + th) < ∞` for small `|t|`), A's convention (`D_f` = Gâteaux points, `:1423-1424`); for a l.s.c. `φ` on the
  Banach space `H`, core = interior of `dom φ`, so it is exactly GHS's `dom ∇ψ ⊆ int dom ψ`; without l.s.c. the class
  is larger (stronger claims). A reading of `∇ψ(x)` as "the unique element of `∂ψ(x)`" could, in infinite dimension
  only, also include non-core points (e.g. `ψ(x) = Σ n xₙ²` on `ℓ²`, whose domain is a dense subspace with empty
  core, yet `∂ψ(x) = {(2n xₙ)}` where that is in `ℓ²`); `cm_subgrad_unique_proper` covers that reading too.
* "Pushing `A` to `B`": `A.map G = B` with `G` only `AEMeasurable` (a generalisation of the paper's Borel versions;
  `Measure.map` of an a.e.-measurable map is the genuine pushforward, no junk). "`∇φ` is defined `A`-a.e." is
  `∀ᵐ x ∂A, GatDiffDom C f x (G x)`; nothing is assumed about `G` off that set. Bounded `μ` is `μ (B̄(0, M))ᶜ = 0`.
  No moments. `A` is a probability null on Lipschitz hypersurfaces (frozen `LipNull`), as in (iv).

Critic notes:
* Route (`OTFD/WaveL9/Route{Grad,Claims}.lean`, untrusted): a Gâteaux gradient of a convex `(C, f)` at a core point
  `x` is a subgradient of `φ` (`f x + ⟨g, z − x⟩ ≤ f z` for `z ∈ C`; slope of the convex line function), so the graph of
  `G` over an `A`-conull Borel set lies in the subdifferential graph of `φ`, which is cyclically monotone; hence
  `IsCMMapAE`. The certified wave-L7 `brenier_uniq_H_bdd` (McCann, moment-free) makes every cyclically monotone coupling
  of `(A, B)` equal to `(Id × G₀)#A` (`G₀` a Borel version), in particular `(Id × G₀')#A`; equal graph plans give
  `G = G'` `A`-a.e. `cm_plans_iv_grad` adds the certified wave-23d `cm_graph_gradient_thm`.
* No tautology: the conclusions (a.e. equality of maps) are not hypotheses; nothing about Lipschitz constants or
  cyclical monotonicity of `G` is assumed. No junk: see Encodings.
* Nonvacuity, and strictly beyond `ghs_grad_unique`: `H = ℝ` (Lipschitz hypersurfaces are points, `LipNull` =
  atomless), `A` uniform on `[0, 1]`, `f(x) = x²` (convex, differentiable, NOT Lipschitz on `ℝ`), `G = 2·id`,
  `B` uniform on `[0, 2]`, `M = 2`: all hypotheses of `cm_grad_unique_convex` hold with `f = f'`, `G = G'`, while
  `ghs_grad_unique` does not apply to the potential `x²`; proper case (`cm_grad_unique_proper`, `cm_grad_eq_map` with
  `F = G = 2·id`): the same `A`, `B`, `G` with `C = (−1, 2)`, `f(x) = x²` (`φ = +∞` off `C`, so not finite);
  `cm_subgrad_unique_proper`: the same (a Gâteaux gradient at a core point is a subgradient). The finite and proper
  hypotheses on this witness, and the non-Lipschitz property of `x²`, were typechecked by the critic (scratch file).
* Critic (2026-10-16): `cm_subgrad_unique_proper` added (route `isCMMapAE_of_subgrad`); in it `ConvexOn` is kept
  for fidelity although the route does not use it (any subgradient graph is cyclically monotone).
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/
set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.OTFD.WaveL9

open StatFormal.OTFD.WaveL1 (CMConc IsCMMapAE Graph BrenierUniq LipNull)
open StatFormal.Wave23d (GatDiff)

/-- Gâteaux gradient of the proper convex `φ = f` on `C`, `φ = +∞` off `C`, at `x`: for every direction `h`, the line
`t ↦ x + t h` stays in `C = dom φ` near `t = 0` and `t ↦ f(x + t h)` has derivative `⟨g, h⟩` at `0`. -/
def GatDiffDom {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (C : Set H) (f : H → ℝ) (x g : H) :
    Prop :=
  ∀ h, (∀ᶠ t : ℝ in 𝓝 0, x + t • h ∈ C) ∧ HasDerivAt (fun t : ℝ => f (x + t • h)) ⟪g, h⟫ 0

namespace Claims

/-- GHS Cor. 2.7 (uniqueness clause) for ALL finite convex potentials, bounded target, no moment: for a probability
`A` null on Lipschitz hypersurfaces and `B` carried by `B̄(0, M)`, two a.e.-measurable maps that are `A`-a.e. Gâteaux
gradients of finite convex functions and push `A` to `B` agree `A`-a.e. (`GHSGradUnique` without Lipschitz.) -/
def cm_grad_unique_convex : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (A B : Measure H) (M : ℝ), IsProbabilityMeasure A → LipNull A →
    B (Metric.closedBall 0 M)ᶜ = 0 →
    ∀ (f f' : H → ℝ) (T T' : H → H), ConvexOn ℝ univ f → ConvexOn ℝ univ f' → AEMeasurable T A →
      AEMeasurable T' A → (∀ᵐ x ∂A, GatDiff f x (T x)) → (∀ᵐ x ∂A, GatDiff f' x (T' x)) → A.map T = B →
      A.map T' = B → T =ᵐ[A] T'

/-- The same among proper extended-valued convex potentials `φ = f` on `C`, `+∞` off `C` (and `φ' = f'` on `C'`). -/
def cm_grad_unique_proper : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (A B : Measure H) (M : ℝ), IsProbabilityMeasure A → LipNull A →
    B (Metric.closedBall 0 M)ᶜ = 0 →
    ∀ (C C' : Set H) (f f' : H → ℝ) (T T' : H → H), ConvexOn ℝ C f → ConvexOn ℝ C' f' → AEMeasurable T A →
      AEMeasurable T' A → (∀ᵐ x ∂A, GatDiffDom C f x (T x)) → (∀ᵐ x ∂A, GatDiffDom C' f' x (T' x)) →
      A.map T = B → A.map T' = B → T =ᵐ[A] T'

/-- The same with "gradient" read as broadly as possible: two a.e.-measurable `A`-a.e. selections of the
subdifferentials of proper convex potentials (`T x ∈ ∂φ(x)`: `x ∈ C` and `f x + ⟪T x, z − x⟫ ≤ f z` for all `z ∈ C`)
pushing `A` to `B` agree `A`-a.e. Every gradient that is a subgradient (Gâteaux at core points, Fréchet, a singleton
subdifferential at a non-core point of a domain with empty interior) is covered. -/
def cm_subgrad_unique_proper : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (A B : Measure H) (M : ℝ), IsProbabilityMeasure A → LipNull A →
    B (Metric.closedBall 0 M)ᶜ = 0 →
    ∀ (C C' : Set H) (f f' : H → ℝ) (T T' : H → H), ConvexOn ℝ C f → ConvexOn ℝ C' f' → AEMeasurable T A →
      AEMeasurable T' A → (∀ᵐ x ∂A, x ∈ C ∧ ∀ z ∈ C, f x + ⟪T x, z - x⟫ ≤ f z) →
      (∀ᵐ x ∂A, x ∈ C' ∧ ∀ z ∈ C', f' x + ⟪T' x, z - x⟫ ≤ f' z) → A.map T = B → A.map T' = B → T =ᵐ[A] T'

/-- On the objects of the frozen `brenier_uniq_H_bdd`: a Borel `P`-a.e. cyclically monotone `F` with `F#P = μ`,
`μ` carried by `B̄(0, M)`, `P` null on Lipschitz hypersurfaces, is `P`-a.e. equal to every gradient of a proper
convex potential pushing `P` to `μ`. -/
def cm_grad_eq_map : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (P μ : ProbabilityMeasure H) (F : H → H) (M : ℝ),
    LipNull (P : Measure H) → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
    Measurable F → (P : Measure H).map F = μ → IsCMMapAE (P : Measure H) F →
    ∀ (C : Set H) (f : H → ℝ) (G : H → H), ConvexOn ℝ C f → AEMeasurable G (P : Measure H) →
      (∀ᵐ x ∂(P : Measure H), GatDiffDom C f x (G x)) → (P : Measure H).map G = μ → G =ᵐ[(P : Measure H)] F

/-- A `lem:app-cm-plans`(iv), middle clause as printed: for `γ` concentrated on a cyclically monotone set, with
`γ¹ = A` null on Lipschitz hypersurfaces and `γ²` carried by `B̄(0, M)`, there are a Borel `T` and a finite convex
`M`-Lipschitz `f` with `γ = (Id × T)#A`, `T#A = γ²` and `T = ∇f` `A`-a.e., and `T` is the `A`-a.e. unique gradient of
a convex function pushing `A` to `γ²`: every gradient of a proper convex potential with that pushforward equals `T`
`A`-a.e. -/
def cm_plans_iv_grad : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (γ : Measure (H × H)) (M : ℝ), IsProbabilityMeasure γ → LipNull γ.fst →
    CMConc γ → γ.snd (Metric.closedBall 0 M)ᶜ = 0 →
      ∃ (T : H → H) (f : H → ℝ), Measurable T ∧ γ = Graph γ.fst T ∧ γ.fst.map T = γ.snd ∧ ConvexOn ℝ univ f ∧
        (∀ x z, |f x - f z| ≤ M * ‖x - z‖) ∧ (∀ᵐ x ∂γ.fst, GatDiff f x (T x)) ∧
        ∀ (C : Set H) (g : H → ℝ) (G : H → H), ConvexOn ℝ C g → AEMeasurable G γ.fst →
          (∀ᵐ x ∂γ.fst, GatDiffDom C g x (G x)) → γ.fst.map G = γ.snd → G =ᵐ[γ.fst] T

end Claims

end StatFormal.OTFD.WaveL9
