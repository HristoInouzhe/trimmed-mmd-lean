import StatFormal.Archive.OTFD.Wave22a.Statements
import StatFormal.Archive.OTFD.WaveL3.Statements
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.MeasureTheory.Measure.Support

/-!
# FROZEN STATEMENTS — otfd wave L6 (discharges): the limit clauses of A `thm:sieve-convergence` (local-uniform weak
# convergence of the embedded sieve subgradients to GHS's `𝔽_P`, the cubic norm upgrade, the ball-law quantile
# clause and its norm form)

Sources (verbatim in `lean-formalisation/inventory/extracted/otfd-A_sieves.md`; current text of
`otfd/papers/A_sieves/`):
* `thm:sieve-convergence` (`main.tex:741-797`), with `def:ghs-rank` (`main.tex:721-739`) and its proof
  (`supplement.tex:1793-1850`: Steps 1-4 apply `thm:app-ghs-stability` with `P_ν = P`, `Q_ν = ι_K#μ_K`).
* `thm:app-ghs-stability` (`supplement.tex:1074-1107`: GHS Thm 3.1(i), the uniform subgradient bound
  `eq:app-uniform-subgradient` and the common compact range `eq:common-compact-range` (⋆) for the norm clause).
* The frozen wave-22a cores (`OTFD/Wave22a/Statements.lean`) `sieve_subdiff_nonempty`, `sieve_subgrad_cube`,
  `cube_interior_empty`, `ghs_lip`, `ghs_lip_subgrad` and the frozen wave-L3 `sieve_strong_limit_uncond`,
  `integrated_quantile_uncond` (the mean-square limits these claims localise).
Imports the frozen `OTFD/Wave22a` (`IsSubgrad`, `supAff`, `cubeH`) and `OTFD/WaveL3` (`Mom1`; through it `OTFD/WaveL1`
`LipNull`, `Euc`, `OTFD/Wave1` `PellClass`, `truncK`) statements, not copied. Mathlib otherwise (`HasLineDerivAt`,
`Measure.support`). No new definitions.

Covered:
* `sieve_conv_weak`: for every `h ∈ H` and strongly compact `𝒦₀ ⊆ int (supp P)` of Gâteaux points of `ψ̃`,
  `sup {|⟪y − 𝔽_P(x), h⟫| : x ∈ 𝒦₀, y ∈ ∂ψ_K(x)} → 0`, `ψ_K = φ_K ∘ Π_K`, for any boundedly supported `μ` (both named
  references).
* `sieve_conv_norm`: the norm form `sup ‖y − 𝔽_P(x)‖ → 0` under the common compact range (⋆) (`thm:app-ghs-stability`
  (ii) in the sieve setting).
* `sieve_conv_norm_cube`: the cubic-law norm clause with (⋆) discharged: `φ_K`, `ψ̃` suprema of affine maps with slopes
  in the box `∏_{k<K}[−λ_k, λ_k]`, resp. in the Hilbert cube `C_λ`, `(λ_k) ∈ ℓ²` (strong compactness of `C_λ` is
  proved, not assumed).
* `sieve_quant_weak`: the exchanged (quantile) clause: `sup {|⟪y − 𝕼_P(u), h⟫| : u ∈ 𝒦₀', y ∈ ∂χ_K(u)} → 0` for strongly
  compact `𝒦₀' ⊆ int (supp μ)` of Gâteaux points of `χ̃` (for the ball law `int (supp μ) = B_H(0,1)`; for the cubic
  law `int (supp μ) = ∅`, `cube_interior_empty`, and the claim is vacuous, as the paper says).
* `sieve_quant_norm`: its norm form under (⋆) for the reverse maps.
* `sieve_quant_norm_cpt`: the norm form with (⋆) discharged when the target slopes lie in a strongly compact `T`
  (the paper's `supp P` strongly compact): `χ̃`, `χ'_K` suprema of affine maps with slopes in `T`, resp. `Π_K(T)`;
  `𝒞 = cl conv (T ∪ ⋃_N ι_N Π_N(T))` is compact (Mazur), and every `y ∈ ∂(χ'_K ∘ Π_K)(u)` is `ι_K Π_K y` with
  `Π_K y ∈ ∂χ'_K(Π_K u)` (the range half of `lem:app-chain-rule`).

Not covered (declared):
* `sieve_conv_norm`, `sieve_quant_norm` keep (⋆) as a hypothesis (the general form of `thm:app-ghs-stability`(ii));
  their instances `sieve_conv_norm_cube` and `sieve_quant_norm_cpt` discharge it. In `sieve_quant_norm_cpt` the compact
  `T` is any compact set containing the slopes. The paper's objects (`cor:app-ghs-lipschitz`: slopes in the closed convex
  hull) fit with `T = ch(supp P)` (strongly compact by Mazur when `supp P` is), `S = ch(supp P) ∩ dom χ̃^*`,
  `S_K = ch(supp P_K) ∩ dom (χ'_K)^* ⊆ ch Π_K(supp P) = Π_K(ch supp P)`; `T = supp P` itself would not do, since the
  Lipschitz representatives take slopes in `ch(supp P)`, `ch(supp P_K)`. No relation `P(Tᶜ) = 0` is needed.
* Existence of the potentials (`thm:app-ghs-existence`, `lem:app-pullback`, `cor:app-ghs-lipschitz` in `ℝ^K`): the
  Brenier potentials `φ_K`, the Lipschitz potential `ψ̃` and the maps are premises (nonvacuity in finite dimension:
  frozen `brenier_exists_H`, `sieve_subdiff_nonempty`).
* Moments and regularity (no restriction vs A): A's `𝒫^ℓ` carries a finite second moment (`main.tex:396-398`,
  `def:app-lipschitz-hypersurface`; the moment clause is declared unused only in `lem:app-cm-plans`,
  `lem:plan-stability-H`, `prop:integrated-sieve-strong`, not in `thm:sieve-convergence`). The forward claims assume only
  `LipNull P` and `m₁(P) < ∞` (inherited from `sieve_strong_limit_uncond`): GENERALISATION. The quantile claims assume
  `P ∈ 𝒫^ℓ` (`PellClass`, as `integrated_quantile_uncond`) but neither A's bounded support of `P` (implied by the uniform
  Lipschitz premise: `‖Q_{+,K}‖ ≤ L_φ`, so every `P_K` lies in `B̄(0, L_φ)`) nor `μ ∈ 𝒫^ℓ`: GENERALISATION.

Encodings (to be checked by the critic):
* As in waves 22a and L1/L3: `H : Type` a separable real Hilbert space with its Borel σ-algebra; `Π_K = truncK e K`,
  `ℝ^K = Euc K`; `y ∈ ∂f(x)` is the frozen `IsSubgrad f x y` (global subgradient inequality); `ψ_K(x) = φ_K(Π_K x)`.
* `𝔽_P = ∇ψ̃` (`def:ghs-rank`): a Borel `F` with `F#P = μ` and `F(x) ∈ ∂ψ̃(x)` for `P`-a.e. `x`, `ψ̃` convex and
  `L`-Lipschitz (`cor:app-ghs-lipschitz`); "`x ∈ dom ∇ψ̃` with `𝔽_P(x) = ∇ψ̃(x)`" is Gâteaux differentiability with
  gradient `F x`: `∀ v, HasLineDerivAt ℝ ψ̃ ⟪F x, v⟫ x v` (implied by Fréchet `HasGradientAt`). The paper's
  `𝒦₀ ⊆ int (dom ∇ψ̃) ∩ int (supp P)` is weakened to `𝒦₀ ⊆ int (supp P)` plus Gâteaux differentiability at the points
  of `𝒦₀` (no interior of the differentiability domain needed).
* The Brenier potentials `φ_K` (`∇φ_K#P_K = μ_K`, "taken everywhere finite and globally Lipschitz"): any `φ_K : ℝ^K → ℝ`
  that is `L_φ`-Lipschitz with one constant for all `K` (`eq:app-uniform-subgradient`; the Lipschitz representative has
  `L_φ ≤ M`) and a Borel `F_{+,K}` with `F_{+,K}#P_K = μ_K` and `F_{+,K}(z) ∈ ∂φ_K(z)` for `P_K`-a.e. `z` (convexity of
  `φ_K` is not needed). Quantile side: `χ̃`, `χ'_K`, `Q`, `Q_{+,K}` with the roles of `P` and `μ` exchanged.
* "`sup S_K → 0`" over the subgradient pairs is written without `sSup`: `∀ ε > 0, ∀ᶠ K, ∀ x ∈ 𝒦₀, ∀ y ∈ ∂ψ_K(x), |…| ≤ ε`.
* "Either of GHS's two named references" is generalised to any Borel probability `μ` carried by a closed ball; the cubic
  claim takes slope sets in the box / cube instead of `supp μ_K`, `supp μ` (`ch supp μ_K ⊆ ∏[−λ_k/2, λ_k/2]` for the
  paper's cube; any `λ ∈ ℓ²` here).

Critic notes:
* Proof route (untrusted, `OTFD/WaveL6/Route*.lean`, library `Foundations/ConvexH`): not GHS's potential-convergence
  argument and no infinite-dimensional Rockafellar 24.5 for pointwise limits. The mean-square limit
  `sieve_strong_limit_uncond` (resp. `integrated_quantile_uncond`) gives convergence in `P`-measure of the selections
  `ι_K F_{+,K} ∘ Π_K ∈ ∂ψ_K` to `𝔽_P`; for `x ∈ int (supp P)` every ball `B(x − t h, r)` has positive mass, so for large
  `K` it contains a point `x'` where both selections are subgradients and close; monotonicity of `∂ψ_K`, the
  subgradient inequality of `ψ̃` at `x'` and the Gâteaux quotient `(ψ̃(x − t h) − ψ̃(x − 2t h))/t → ⟪𝔽_P(x), h⟫` bound
  `⟪y, h⟫` from below (and, with `−h`, from above); compactness of `𝒦₀` makes it uniform; under (⋆) weak + compact
  range gives norm convergence.
* No tautology: no hypothesis mentions a limit in `K` except through the frozen mean-square theorems used in the route;
  the conclusions are local-uniform limits.
* Nonvacuity (critic): `H = ℓ²`, `P` a nondegenerate Gaussian (full support, so `int (supp P) = H`, `LipNull`), the
  convex `C¹` potential `ψ̃(x) = ∑_j 2^{-j}(√(1 + x_j²) − 1)` of `prop:ghs-iii-counterexample` (`ψ̃ = supAff S ψ̃^*` with
  `S = range ∇ψ̃ ⊆ cubeH e (2^{-j})`), `μ = ∇ψ̃#P`, `φ_K` the Lipschitz Brenier representatives of `P_K → μ_K` (slopes in
  `ch supp μ_K`, inside the box), any compact `𝒦₀`: every premise of `sieve_conv_norm_cube` holds and the conclusion
  (`∂ψ_K → ∇ψ̃` in norm, uniformly on `𝒦₀`) is not trivial. The `supAff` premises (nonempty slopes, `BddAbove` at one
  point, bounded slopes) make every `iSup` a genuine, everywhere finite supremum.
* No junk: every `Measure.map` is of an assumed-measurable or continuous (`truncK`) map; no `sSup`, division or `toReal`;
  the `iSup` of `supAff` is guarded as just said.
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/
set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.OTFD.WaveL6

open StatFormal.OTFD.WaveL1 (LipNull Euc)
open StatFormal.OTFD.WaveL3 (Mom1)
open StatFormal.OTFD.Wave1 (PellClass truncK)
open StatFormal.OTFD.Wave22a (IsSubgrad supAff cubeH)

namespace Claims

/-! #### A `thm:sieve-convergence`: forward (distribution-function) limits -/

/-- Local-uniform weak convergence: for every `h ∈ H` and strongly compact `𝒦₀ ⊆ int (supp P)` at whose points `ψ̃` is
Gâteaux differentiable with gradient `𝔽_P`, `sup {|⟪y − 𝔽_P(x), h⟫| : x ∈ 𝒦₀, y ∈ ∂ψ_K(x)} → 0`, `ψ_K = φ_K ∘ Π_K`. -/
def sieve_conv_weak : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (P μ : ProbabilityMeasure H) (ψ : H → ℝ) (F : H → H) (M Lψ Lφ : ℝ)
    (φ : (K : ℕ) → Euc K → ℝ) (FK : (K : ℕ) → Euc K → Euc K) (K₀ : Set H) (h : H),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    LipNull (P : Measure H) → Mom1 (P : Measure H) ≠ ∞ → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
    ConvexOn ℝ univ ψ → (∀ x x', |ψ x - ψ x'| ≤ Lψ * ‖x - x'‖) →
    Measurable F → (P : Measure H).map F = μ → (∀ᵐ x ∂(P : Measure H), IsSubgrad ψ x (F x)) →
    (∀ K z z', |φ K z - φ K z'| ≤ Lφ * ‖z - z'‖) → (∀ K, Measurable (FK K)) →
    (∀ K, ((P : Measure H).map (truncK e K)).map (FK K) = (μ : Measure H).map (truncK e K)) →
    (∀ K, ∀ᵐ z ∂((P : Measure H).map (truncK e K)), IsSubgrad (φ K) z (FK K z)) →
    IsCompact K₀ → K₀ ⊆ interior (P : Measure H).support →
    (∀ x ∈ K₀, ∀ v, HasLineDerivAt ℝ ψ ⟪F x, v⟫ x v) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ K in atTop, ∀ x ∈ K₀, ∀ y,
        IsSubgrad (fun x' => φ K (truncK e K x')) x y → |⟪y - F x, h⟫| ≤ ε

/-- Norm form under the common strongly compact range (⋆): all subgradients of `ψ_K` at points of `𝒦₀` and all
`𝔽_P(x)`, `x ∈ 𝒦₀`, lie in one strongly compact `𝒞` ⇒ `sup {‖y − 𝔽_P(x)‖ : x ∈ 𝒦₀, y ∈ ∂ψ_K(x)} → 0`. -/
def sieve_conv_norm : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (P μ : ProbabilityMeasure H) (ψ : H → ℝ) (F : H → H) (M Lψ Lφ : ℝ)
    (φ : (K : ℕ) → Euc K → ℝ) (FK : (K : ℕ) → Euc K → Euc K) (K₀ C : Set H),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    LipNull (P : Measure H) → Mom1 (P : Measure H) ≠ ∞ → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
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

/-- Cubic law, norm clause: `φ_K = sup_{z ∈ S_K}{⟪·, z⟫ − b_K(z)}` with slopes in the box `∏_{k<K}[−λ_k, λ_k]`,
`ψ̃ = sup_{y ∈ S}{⟪·, y⟫ − b(y)}` with slopes in the Hilbert cube `C_λ`, `(λ_k) ∈ ℓ²` ⇒
`sup {‖y − 𝔽_P(x)‖ : x ∈ 𝒦₀, y ∈ ∂ψ_K(x)} → 0`. -/
def sieve_conv_norm_cube : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (lam : ℕ → ℝ) (P μ : ProbabilityMeasure H) (S : Set H) (b : H → ℝ) (x₀ : H) (F : H → H) (M : ℝ)
    (SK : (K : ℕ) → Set (Euc K)) (bK : (K : ℕ) → Euc K → ℝ) (zK : (K : ℕ) → Euc K)
    (FK : (K : ℕ) → Euc K → Euc K) (K₀ : Set H),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    (∀ k, 0 ≤ lam k) → Summable (fun k => lam k ^ 2) →
    LipNull (P : Measure H) → Mom1 (P : Measure H) ≠ ∞ → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
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

/-! #### A `thm:sieve-convergence`: exchanged (quantile) limits -/

/-- Quantile clause: roles of `P` and `μ` exchanged. `χ̃` convex Lipschitz with `𝕼_P(u) ∈ ∂χ̃(u)` `μ`-a.e.,
`𝕼_P#μ = P`; reverse sieve potentials `χ'_K` with `Q_{+,K}#μ_K = P_K`; for every `h` and strongly compact
`𝒦₀' ⊆ int (supp μ)` of Gâteaux points of `χ̃`: `sup {|⟪y − 𝕼_P(u), h⟫| : u ∈ 𝒦₀', y ∈ ∂χ_K(u)} → 0`. -/
def sieve_quant_weak : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (P μ : ProbabilityMeasure H) (χ : H → ℝ) (Q : H → H) (M Lχ Lφ : ℝ)
    (φ : (K : ℕ) → Euc K → ℝ) (QK : (K : ℕ) → Euc K → Euc K) (K₀ : Set H) (h : H),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    PellClass (P : Measure H) → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
    ConvexOn ℝ univ χ → (∀ u u', |χ u - χ u'| ≤ Lχ * ‖u - u'‖) →
    Measurable Q → (μ : Measure H).map Q = P → (∀ᵐ u ∂(μ : Measure H), IsSubgrad χ u (Q u)) →
    (∀ K z z', |φ K z - φ K z'| ≤ Lφ * ‖z - z'‖) → (∀ K, Measurable (QK K)) →
    (∀ K, ((μ : Measure H).map (truncK e K)).map (QK K) = (P : Measure H).map (truncK e K)) →
    (∀ K, ∀ᵐ z ∂((μ : Measure H).map (truncK e K)), IsSubgrad (φ K) z (QK K z)) →
    IsCompact K₀ → K₀ ⊆ interior (μ : Measure H).support →
    (∀ u ∈ K₀, ∀ v, HasLineDerivAt ℝ χ ⟪Q u, v⟫ u v) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ K in atTop, ∀ u ∈ K₀, ∀ y,
        IsSubgrad (fun u' => φ K (truncK e K u')) u y → |⟪y - Q u, h⟫| ≤ ε

/-- Quantile clause in norm, under the common strongly compact range (⋆) of the reverse maps. -/
def sieve_quant_norm : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (P μ : ProbabilityMeasure H) (χ : H → ℝ) (Q : H → H) (M Lχ Lφ : ℝ)
    (φ : (K : ℕ) → Euc K → ℝ) (QK : (K : ℕ) → Euc K → Euc K) (K₀ C : Set H),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    PellClass (P : Measure H) → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
    ConvexOn ℝ univ χ → (∀ u u', |χ u - χ u'| ≤ Lχ * ‖u - u'‖) →
    Measurable Q → (μ : Measure H).map Q = P → (∀ᵐ u ∂(μ : Measure H), IsSubgrad χ u (Q u)) →
    (∀ K z z', |φ K z - φ K z'| ≤ Lφ * ‖z - z'‖) → (∀ K, Measurable (QK K)) →
    (∀ K, ((μ : Measure H).map (truncK e K)).map (QK K) = (P : Measure H).map (truncK e K)) →
    (∀ K, ∀ᵐ z ∂((μ : Measure H).map (truncK e K)), IsSubgrad (φ K) z (QK K z)) →
    IsCompact K₀ → K₀ ⊆ interior (μ : Measure H).support →
    (∀ u ∈ K₀, ∀ v, HasLineDerivAt ℝ χ ⟪Q u, v⟫ u v) →
    IsCompact C → (∀ K, ∀ u ∈ K₀, ∀ y, IsSubgrad (fun u' => φ K (truncK e K u')) u y → y ∈ C) →
    (∀ u ∈ K₀, Q u ∈ C) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ K in atTop, ∀ u ∈ K₀, ∀ y,
        IsSubgrad (fun u' => φ K (truncK e K u')) u y → ‖y - Q u‖ ≤ ε

/-- Quantile clause in norm when the target slopes lie in a strongly compact set (`supp P` strongly compact), with (⋆)
discharged: `χ̃ = sup_{y ∈ S}{⟪·, y⟫ − b(y)}` with `S ⊆ T`, reverse potentials `χ'_K = sup_{z ∈ S_K}{⟪·, z⟫ − b_K(z)}`
with `S_K ⊆ Π_K(T)`, `T` strongly compact ⇒ `sup {‖y − 𝕼_P(u)‖ : u ∈ 𝒦₀', y ∈ ∂χ_K(u)} → 0`. -/
def sieve_quant_norm_cpt : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : ℕ → H) (P μ : ProbabilityMeasure H) (T S : Set H) (b : H → ℝ) (x₀ : H) (Q : H → H) (M : ℝ)
    (SK : (K : ℕ) → Set (Euc K)) (bK : (K : ℕ) → Euc K → ℝ) (zK : (K : ℕ) → Euc K)
    (QK : (K : ℕ) → Euc K → Euc K) (K₀ : Set H),
    Orthonormal ℝ e → ⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure →
    PellClass (P : Measure H) → (μ : Measure H) (Metric.closedBall 0 M)ᶜ = 0 →
    IsCompact T → S.Nonempty → S ⊆ T → BddAbove (range fun y : S => ⟪x₀, (y : H)⟫ - b y) →
    Measurable Q → (μ : Measure H).map Q = P → (∀ᵐ u ∂(μ : Measure H), IsSubgrad (supAff S b) u (Q u)) →
    (∀ K, (SK K).Nonempty) → (∀ K, SK K ⊆ truncK e K '' T) →
    (∀ K, BddAbove (range fun z : SK K => ⟪zK K, (z : Euc K)⟫ - bK K z)) → (∀ K, Measurable (QK K)) →
    (∀ K, ((μ : Measure H).map (truncK e K)).map (QK K) = (P : Measure H).map (truncK e K)) →
    (∀ K, ∀ᵐ z ∂((μ : Measure H).map (truncK e K)), IsSubgrad (supAff (SK K) (bK K)) z (QK K z)) →
    IsCompact K₀ → K₀ ⊆ interior (μ : Measure H).support →
    (∀ u ∈ K₀, ∀ v, HasLineDerivAt ℝ (supAff S b) ⟪Q u, v⟫ u v) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ K in atTop, ∀ u ∈ K₀, ∀ y,
        IsSubgrad (fun u' => supAff (SK K) (bK K) (truncK e K u')) u y → ‖y - Q u‖ ≤ ε

end Claims

end StatFormal.OTFD.WaveL6
