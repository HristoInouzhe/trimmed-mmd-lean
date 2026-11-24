import StatFormal.Wave31td.Statements
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.MetricSpace.Thickening

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 31tg: trimmed-mmd (jmlr) **v3**, the function `f` of Example `ex:separated` exists (finite supports, Matérn kernels), the three-point instance, and "the margin does not imply (Q)"

Printed source: `trimmed-mmd/jmlr/v3/NEW_STATEMENTS.md`, section "Wave 31tg" (G1a, G1b, G1c, G3b: the binding specification; trimmed-mmd
commit `d356058`, file sha256 `311b3b79b12704db129665550b6137172bf8d6d3552e071d0123422157c37cad`; read-only, read 2026-11-12). The printed
text is at trimmed-mmd `78c4665` (`jmlr/v3/`; the working tree may be edited elsewhere): `sections/03_analytic.tex:167-178` (Example 1,
`ex:separated`, certified in wave 31tb) and `:180-183` (the paragraph after it; file sha256 `b4b2301d…5b8e`); `appendix/B_analytic.tex:295-314`
(the proof of Example 1) and `:316-321` (the closing paragraph; sha256 `ec1eaeab…9eeb`); `sections/02_regions.tex:40-42` (the three-point
example after `eq:contam`; sha256 `d5dba9d8…07b7`); `sections/05_trimming.tex:77-78` (the sentence on finite support; sha256
`f787aecc…00db`). The printed text:

> **Example 1 (Separated contamination)** (`03_analytic.tex:167-178`). Let (A1) and (A2) of Assumption 1 hold. Let `R`, `P₀` and `Q₀` be
> probability measures concentrated on pairwise disjoint measurable sets `S_R`, `S_P` and `S_Q`, let `α⋆ ∈ (0,1)`, and put
> `P = (1−α⋆)R + α⋆P₀` and `Q = (1−α⋆)R + α⋆Q₀`. Then `TV(P,Q) = α⋆`. If moreover some `f ∈ ℋ` takes the value `0` on `S_R`, `1` on `S_P`
> and `−1` on `S_Q`, then for every `α ∈ [0,α⋆]`, `D_α(P,Q) ≥ 2(α⋆−α)/((1−α)‖f‖_ℋ) ≥ 2(α⋆−α)/‖f‖_ℋ`, so Assumption 2 holds with
> `ω(ε) = c₀ε` and `c₀ = 2/‖f‖_ℋ`.
>
> Such an `f` exists when the three sets are finite and `k` is strictly positive definite, by interpolation, as for the example of Section 2,
> with `R`, `P₀` and `Q₀` the point masses at `x₂`, `x₁` and `x₃`. It also exists when `S_P` and `S_Q` are bounded, the three sets are at
> positive distance from each other and `k` is a Matérn kernel on `ℝ^d`, whose RKHS is a Sobolev space (Wendland 2005, Chapter 10).
> (`03_analytic.tex:180-183`)
>
> For finite sets and a strictly positive definite kernel the Gram matrix of their points is invertible, so a combination `Σ_i c_i k(·,z_i)`
> takes any prescribed values on them. For a Matérn kernel on `ℝ^d` the RKHS is a Sobolev space with an equivalent norm (Wendland 2005,
> Chapter 10), which contains a smooth compactly supported function equal to `1` on the `ε/3`-neighbourhood of `S_P`, to `−1` on that of
> `S_Q` and to `0` outside their `2ε/3`-neighbourhoods, when `S_P` and `S_Q` are bounded and `ε > 0` is the smallest distance between two
> of the three sets. (`B_analytic.tex:316-321`)
>
> For instance, if `P` puts mass `½` on each of two points `x₁, x₂` and `Q` on each of `x₂, x₃`, then `α⋆ = ½`, and removing `x₁` from
> `P` and `x₃` from `Q` leaves the point mass at `x₂` in both. (`02_regions.tex:40-42`)
>
> Laws with finite support, such as those of Example 1, violate (Q), so the margin does not imply the density conditions.
> (`05_trimming.tex:77-78`)

and the frozen formal targets of "Wave 31tg" (G1a) a feature map into a real Hilbert space that is strictly positive definite on a finite set
`Z` of distinct points takes any prescribed values on `Z` (and so for pairwise disjoint finite `S_R, S_P, S_Q` there is `f` equal to `0`, `1`,
`−1` on them); (G1b) for distinct `x₁,x₂,x₃` with measurable singletons, `P = ½δ_{x₁} + ½δ_{x₂}`, `Q = ½δ_{x₂} + ½δ_{x₃}` have `TV(P,Q) = ½`
and the separated form of Example 1 (`α⋆ = ½`, `R = δ_{x₂}`, `P₀ = δ_{x₁}`, `Q₀ = δ_{x₃}`, on `{x₂}, {x₁}, {x₃}`), and for a feature map
strictly positive definite on `{x₁,x₂,x₃}` satisfying (A1)–(A2) the conclusion of Example 1 holds for this pair, stated as a composed
theorem; (G1c) with the Sobolev identification as a declared textbook bridge (Wendland 2005, Cor. 10.13: every `C^∞` function with compact
support is represented by an element of `ℋ`): `S_R, S_P, S_Q ⊂ ℝ^d` with pairwise distances at least `ε > 0` and `S_P, S_Q` bounded admit an
`f ∈ ℋ` equal to `0`, `1`, `−1` on them, in the printed form (`C^∞`, compact support, `1` on the `ε/3`-neighbourhood of `S_P`, `−1` on that
of `S_Q`, `0` outside their `2ε/3`-neighbourhoods); (G3b) there is a pair of finitely supported laws (the three-point pair with the Gaussian
kernel on three distinct reals) satisfying (A1)–(A3) such that Assumption 2 holds while (Q) fails at every level `α ∈ (0,α⋆)`, where
`D_α(P,Q) > 0` and `d⋆`, `t_α` are defined. (The proof routes named there are not part of the statements.)

Covered here (7 claims; labels `prose:ex-separated-finite (v3)`, `prose:ex-separated-three-points (v3)`, `prose:ex-separated-matern (v3)`,
`prose:margin-not-Q (v3)`, pseudo-labels of the unlabelled prose after Example 1 and after the linear-kernel instance):
* `interpolation` (G1a, `B_analytic.tex:316-317`) — for a feature map strictly positive definite on a finite set `Z`: the Gram matrix of `Z` is
  invertible, and every `v : Z → ℝ` is the trace on `Z` of some `f = Σ_z c_z φ(z) ∈ ℋ` (`⟪f, φ z⟫ = v z`).
* `interpolation_example` (G1a, `03_analytic.tex:180-181`) — for pairwise disjoint finite `S_R, S_P, S_Q` with `φ` strictly positive definite on
  their union, some `f ∈ ℋ` is `0` on `S_R`, `1` on `S_P`, `−1` on `S_Q`.
* `three_point_form` (G1b, `02_regions.tex:40-42`, `03_analytic.tex:181-182`) — the three-point pair: `TV = ½` and every hypothesis of
  Example 1 on `(R, P₀, Q₀, S_R, S_P, S_Q, α⋆)` with `R = δ_{x₂}`, `P₀ = δ_{x₁}`, `Q₀ = δ_{x₃}`, `α⋆ = ½`.
* `three_point_margin` (G1b, the composed theorem) — for a feature map `φ` with (A1) and strictly positive definite on `{x₁,x₂,x₃}`: an `f`
  with the values `0, 1, −1` at `x₂, x₁, x₃` exists, and for every such `f` the conclusion of Example 1 holds for the pair (`‖f‖ > 0`,
  `D_α ≥ 2(½−α)/((1−α)‖f‖) ≥ 2(½−α)/‖f‖` on `[0,½]`, Assumption 2 with `ω(ε) = (2/‖f‖)ε`).
* `matern_bump` (G1c, `B_analytic.tex:318-321`) — the printed smooth function: `S_P, S_Q ⊂ ℝ^d` bounded at distance `≥ ε > 0` carry a `C^∞`
  function with compact support, equal to `1` on the closed `ε/3`-neighbourhood of `S_P`, to `−1` on that of `S_Q`, and to `0` outside the
  open `2ε/3`-neighbourhoods of both. No bridge is used.
* `matern_interpolation` (G1c, `03_analytic.tex:182-183`) — under the declared bridge `ContainsSmoothCompact φ`, for `S_R, S_P, S_Q ⊂ ℝ^d`
  with pairwise distances `≥ ε > 0` and `S_P, S_Q` bounded, some `f ∈ ℋ` is `0` on `S_R`, `1` on `S_P`, `−1` on `S_Q`.
* `margin_not_Q` (G3b, `05_trimming.tex:77-78`) — for every three distinct reals and every `σ > 0` there is a feature map of the Gaussian
  kernel on them (a real separable Hilbert space, `𝒳 = Fin 3`) with (A1)–(A3), for which the three-point pair has `TV = ½`, the linear margin
  (Assumption 2 with `ω(ε) = c₀ε`, `c₀ > 0`), finite support, and for every level `α ∈ (0,½)`: `D_α > 0`, the population witness `d⋆` and a
  `(1−α)`-quantile `t_α` of `d⋆(X)` exist, and at every such `(d⋆, t_α)` the density condition (Q) fails (for every `r_Q > 0`, `c_f > 0`,
  `C_f`); also (Q) fails for every function and level, and the lower-density condition (Q′) fails for `Q` (the form of the certified
  `Wave31td.finite_support_not_Q`).

Reuses (imported, not copied; certified earlier): `Distances.tvDist` (`TV(P,Q) = sup_A |P(A) − Q(A)|`), `Wave30tu.Margin` (Assumption 2,
`α⋆ = tvDist P Q`, stated with `Dpop`), `Wave8a.dTrim` (the printed `D_α`, the infimum of `MMD` over `R_α(P) × R_α(Q)`),
`TrimmedMMD.Unconditional.Dpop` (the regions' distance, `eq:setdist`; the `D_α` of every certified claim), `TrimmedMMD.Concentration.region`
(`𝒞_α`), `TrimmedMMD.Projection.IsMinNorm` (the witness `d⋆`), `Wave12c.witFn` (`d⋆(x) = ⟪d⋆, φ x⟫`), `Wave12c.QDensity`/`QDensityLower`
((Q), (Q′)), `Wave30tx.IsQuantile` (`R(f < t) ≤ p ≤ R(f ≤ t)`), `TrimmedMMD.ZeroSet.Characteristic` ((A3)). The routes use the certified
`Wave31tb.separated` (Example 1) and `Wave31td.finite_support_not_Q`.

Encodings (see the card `certify/cards/wave31tg.md`):
* The feature-map encoding of every earlier trimmed-mmd wave: `ℋ` a real Hilbert space (`NormedAddCommGroup`, `InnerProductSpace ℝ`,
  `CompleteSpace`; the purely algebraic claims `interpolation`, `interpolation_example` and the analytic `matern_*` claims need no
  completeness and drop it: a generalisation), `φ : 𝒳 → ℋ` with `k(x,y) = ⟪φ x, φ y⟫`; an element `f ∈ ℋ` acts as `x ↦ ⟪f, φ x⟫`
  (reproducing property), `‖f‖_ℋ = ‖f‖`; for the canonical feature map of an RKHS this is literal. (A1) is `StronglyMeasurable φ` with
  `‖φ x‖ ≤ κ` (the repository's encoding of (A1)–(A2); separability (A2) is dropped in `three_point_margin`, whose proof does not use it
  (generalisation, as in `Wave31tb.separated`) and kept in `margin_not_Q`); (A3) is `Characteristic φ`.
* "`k` is strictly positive definite on `S`": `StrictlyPDOn φ S` (below): the Gram matrix of every finite set of distinct points of `S` is
  positive definite. `S = univ` is the usual "`k` is strictly positive definite" of the printed text; the claims assume it only on the finite
  set they use (a weaker hypothesis: a generalisation, the printed hypothesis implies it). "The Gram matrix is invertible":
  `Function.Bijective (Matrix.gram ℝ (fun z : Z => φ z)).mulVec`. "Any prescribed values": `v : Z → ℝ` arbitrary (equivalently `v : 𝒳 → ℝ`).
* Universes: `𝒳 H : Type` (universe 0), the repository convention of every earlier trimmed-mmd wave (the analytic claims on `ℝ^d` take `H : Type`).
* The three-point pair: `P = ofReal(½)•δ_{x₁} + ofReal(½)•δ_{x₂}`, `Q = ofReal(½)•δ_{x₂} + ofReal(½)•δ_{x₃}` (Mathlib `Measure.dirac`, `ℝ≥0∞`
  scalars); "measurable singletons": `MeasurableSet {xᵢ}` for the three points (weaker than a `MeasurableSingletonClass`). "`R, P₀, Q₀` concentrated
  on `S_R, S_P, S_Q`": `μ Sᶜ = 0`. The decomposition is stated with `ofReal(1−½)` and `ofReal(½)` exactly as the hypotheses of `Wave31tb.separated`.
* `ε`-neighbourhoods: `Metric.cthickening (ε/3)` (closed, `{x : infEDist x S ≤ ε/3}`) for the sets where the function is `±1` and
  `Metric.thickening (2ε/3)` (open, `{x : infEDist x S < 2ε/3}`) for the "outside their `2ε/3`-neighbourhoods", which is the stronger reading of each
  printed clause (both are empty for `S = ∅`: no `infDist ∅ = 0` junk). "`ε` the smallest distance between two of the three sets, `> 0`": `ε > 0` with
  `ε ≤ ‖x − y‖` for `x, y` in two different sets (equivalent: such an `ε` exists iff the smallest distance is positive; the claim for the
  smallest distance is the instance). "`C^∞`": `ContDiff ℝ ∞` (`∞ = (⊤ : ℕ∞)`, smooth, not analytic).
* BRIDGE (the only way "Matérn" enters, declared; Wendland 2005, Cor. 10.13): `ContainsSmoothCompact φ`, "every `C^∞` function `g` on `ℝ^d` with
  compact support is represented by some `f ∈ ℋ`, `⟪f, φ x⟫ = g x` for all `x`": for the canonical feature map of a Matérn kernel `k` on `ℝ^d`
  it says that every such `g` lies in the RKHS, which is the Sobolev space `H^{ν+d/2}(ℝ^d)` (equivalent norms) and contains `C_c^∞`. The
  Matérn kernel and its RKHS are not defined here and the inclusion is not proved. `ℝ^d` is `EuclideanSpace ℝ (Fin d)`.
* `margin_not_Q`: `𝒳 = Fin 3` (a three-point space, the points `0, 1, 2` playing `x₁, x₂, x₃`), the kernel is the Gaussian kernel
  `exp(−(rᵢ−rⱼ)²/(2σ²))` of three distinct reals `r` (the Gram identity of `φ`, the paper's `κ = 1`), `H` is existentially quantified (its
  existence is part of the claim). "(Q) fails at level `α`": for every minimal-norm element `d⋆` of `𝒞_α(P) − 𝒞_α(Q)` and every
  `(1−α)`-quantile `t_α` of `d⋆(X)` under `P`, `¬ QDensity P d⋆ t_α r c C` for all `r > 0`, `c > 0`, `C` ((Q) asks `0 < c_f ≤ C_f < ∞`);
  "where `D_α > 0` and `d⋆, t_α` are defined": `0 < Dpop`, and both exist. "Assumption 2 holds": the linear margin `Margin φ P Q (c₀ε)`, `c₀ > 0`.
* Junk values: `Dpop`/`dTrim` are `sInf` of nonempty sets bounded below by `0` for `α ∈ [0,1)` (the claims evaluate them there); the
  divisions `/((1−α)‖f‖)`, `/‖f‖`, `2/‖f‖` are by `1 − α ≥ ½ > 0` and `‖f‖ > 0` (a conclusion); `tvDist` is the `⨆` of a set bounded by `1`;
  `IsQuantile` uses `Measure.real` of measurable sets of finite measure; no `deriv`, no `log`, no `Measure.map`, no `toReal ∞`.
* Not covered: the Matérn kernel and the Sobolev identification (bridge); the equivalence "strictly positive definite ⇔ the `φ(z)` are linearly
  independent" (a parenthetical of the target; used by the proof); Example 1 itself (wave 31tb) and its use in the claims beyond the
  composition stated; the margin of a Matérn pair as a separate claim.
FROZEN 2026-11-12 before any proof, after an independent critic's pre-freeze review (7 claims: 6 ACCEPT and 1 ACCEPT-WITH-NOTE
(`matern_interpolation`: the declared Matérn/Sobolev bridge, as specified), none false, verdict READY TO FREEZE; it back-translated the
claims blind from the comment-free file, checked the printed lines and file hashes at `78c4665`, typechecked a witness of the hypotheses of
every claim in scratch Lean (`Fin 3` with the standard basis of `ℝ³`; `d = 0`, `H = ℝ` for the bridge), checked numerically on 399 random
triples of reals and bandwidths that the Gaussian Gram matrix is positive definite, that `D_α > 0` below `α⋆` and that the Example-1 bound is
never violated (attained exactly for the symmetric placement), and machine-proved all seven claims verbatim in scratch Lean; applied: the
`infEDist` wording for empty sets and the universe convention). Hashed in `certify/statements.lock` (with its imports); AI agents must not
edit this file.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace RealInnerProductSpace ContDiff Pointwise

namespace StatFormal.Wave31tg

open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional StatFormal.TrimmedMMD.Projection
  StatFormal.TrimmedMMD.ZeroSet StatFormal.Wave8a StatFormal.Wave12c StatFormal.Wave30tx StatFormal.Wave30tu

/-- `k(x,y) = ⟪φ x, φ y⟫` is strictly positive definite on the set `S ⊆ 𝒳`: for every finite set `Z ⊆ S` of points (a `Finset`, so the
points are distinct) and every coefficient vector `c` that is not zero on `Z`, `Σ_{z,w ∈ Z} c_z c_w k(z,w) > 0`; that is, the Gram matrix of
every finite set of distinct points of `S` is positive definite. For `S = univ` this is the usual "`k` is strictly positive definite". -/
def StrictlyPDOn {𝒳 H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (φ : 𝒳 → H) (S : Set 𝒳) : Prop :=
  ∀ Z : Finset 𝒳, (Z : Set 𝒳) ⊆ S → ∀ c : 𝒳 → ℝ, (∃ z ∈ Z, c z ≠ 0) →
    0 < ∑ z ∈ Z, ∑ w ∈ Z, c z * c w * ⟪φ z, φ w⟫_ℝ

/-- BRIDGE (declared textbook input, used only in `matern_interpolation`; Wendland 2005, Cor. 10.13): every `C^∞` function `g : ℝ^d → ℝ`
with compact support is represented by an element of `ℋ`: `⟪f, φ x⟫ = g x` for all `x`. For the canonical feature map `φ(x) = k(x,·)` of
a Matérn kernel `k` on `ℝ^d` it says that every such `g` belongs to the RKHS, which is the Sobolev space `H^{ν+d/2}(ℝ^d)` with an
equivalent norm and contains every `C^∞` function with compact support. (`∞` is `(⊤ : ℕ∞)`: smooth, not analytic. `ℝ^d` is
`EuclideanSpace ℝ (Fin d)`.) -/
def ContainsSmoothCompact {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (φ : EuclideanSpace ℝ (Fin d) → H) : Prop :=
  ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → ∃ f : H, ∀ x, ⟪f, φ x⟫_ℝ = g x

namespace Claims

/-- `prose:ex-separated-finite (v3)`, G1a, the printed reason (`B_analytic.tex:316-317`): "For finite sets and a strictly positive definite
kernel the Gram matrix of their points is invertible, so a combination `Σ_i c_i k(·, z_i)` takes any prescribed values on them." For a
feature map `φ : 𝒳 → ℋ` into a real inner product space that is strictly positive definite on a finite set `Z` of points: the Gram matrix
`(⟪φ z, φ w⟫)_{z,w ∈ Z}` is invertible (the linear map `ℝ^Z → ℝ^Z` it defines is bijective), and for every `v : Z → ℝ` there is `f ∈ ℋ`,
a combination `Σ_{z ∈ Z} c_z φ(z)` (in the RKHS, `Σ c_z k(·, z)`), with `⟪f, φ z⟫ = v z` (`f(z) = v(z)`) for all `z ∈ Z`. (Completeness of
`ℋ` is not needed: a generalisation.) -/
def interpolation : Prop :=
  ∀ (𝒳 H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (φ : 𝒳 → H) (Z : Finset 𝒳),
    StrictlyPDOn φ (Z : Set 𝒳) →
      Function.Bijective (Matrix.gram ℝ (fun z : Z => φ z)).mulVec ∧
      ∀ v : Z → ℝ, ∃ f : H, (∃ c : 𝒳 → ℝ, f = ∑ w ∈ Z, c w • φ w) ∧ ∀ z : Z, ⟪f, φ z⟫_ℝ = v z

/-- `prose:ex-separated-finite (v3)`, G1a, the printed sentence (`03_analytic.tex:180-181`): "Such an `f` exists when the three sets are
finite and `k` is strictly positive definite, by interpolation." For pairwise disjoint finite sets `S_R, S_P, S_Q ⊆ 𝒳` such that `φ` (i.e.
`k(x,y) = ⟪φ x, φ y⟫`) is strictly positive definite on `S_R ∪ S_P ∪ S_Q`, there is `f ∈ ℋ` with `f(x) = ⟪f, φ x⟫` equal to `0` on `S_R`,
`1` on `S_P` and `−1` on `S_Q`. (The hypothesis is the one on the union only: weaker than "`k` strictly positive definite", a
generalisation.) -/
def interpolation_example : Prop :=
  ∀ (𝒳 H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (φ : 𝒳 → H) (SR SP SQ : Set 𝒳),
    SR.Finite → SP.Finite → SQ.Finite → Disjoint SR SP → Disjoint SR SQ → Disjoint SP SQ →
    StrictlyPDOn φ (SR ∪ SP ∪ SQ) →
      ∃ f : H, (∀ x ∈ SR, ⟪f, φ x⟫_ℝ = 0) ∧ (∀ x ∈ SP, ⟪f, φ x⟫_ℝ = 1) ∧ (∀ x ∈ SQ, ⟪f, φ x⟫_ℝ = -1)

/-- `prose:ex-separated-three-points (v3)`, G1b, the form (`02_regions.tex:40-42`, `03_analytic.tex:181-182`): "if `P` puts mass `½` on
each of two points `x₁, x₂` and `Q` on each of `x₂, x₃`, then `α⋆ = ½`, and removing `x₁` from `P` and `x₃` from `Q` leaves the point mass at
`x₂` in both" and "as for the example of Section 2, with `R`, `P₀` and `Q₀` the point masses at `x₂`, `x₁` and `x₃`". For distinct points
`x₁, x₂, x₃` of a measurable space with measurable singletons and `P = ½δ_{x₁} + ½δ_{x₂}`, `Q = ½δ_{x₂} + ½δ_{x₃}`: `P`, `Q` are probability
measures, `TV(P,Q) = ½`, and `(P, Q)` is of the separated form of Example 1 with `α⋆ = ½`, `R = δ_{x₂}`, `P₀ = δ_{x₁}`, `Q₀ = δ_{x₃}`
concentrated on the pairwise disjoint measurable sets `{x₂}, {x₁}, {x₃}`: `P = (1−½)R + ½P₀`, `Q = (1−½)R + ½Q₀`. -/
def three_point_form : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (x₁ x₂ x₃ : 𝒳), x₁ ≠ x₂ → x₁ ≠ x₃ → x₂ ≠ x₃ →
    MeasurableSet ({x₁} : Set 𝒳) → MeasurableSet ({x₂} : Set 𝒳) → MeasurableSet ({x₃} : Set 𝒳) →
    ∀ P Q : Measure 𝒳,
      P = ENNReal.ofReal (1 / 2) • Measure.dirac x₁ + ENNReal.ofReal (1 / 2) • Measure.dirac x₂ →
      Q = ENNReal.ofReal (1 / 2) • Measure.dirac x₂ + ENNReal.ofReal (1 / 2) • Measure.dirac x₃ →
        IsProbabilityMeasure P ∧ IsProbabilityMeasure Q ∧
        StatFormal.Distances.tvDist P Q = 1 / 2 ∧
        Disjoint ({x₂} : Set 𝒳) {x₁} ∧ Disjoint ({x₂} : Set 𝒳) {x₃} ∧ Disjoint ({x₁} : Set 𝒳) {x₃} ∧
        Measure.dirac x₂ ({x₂} : Set 𝒳)ᶜ = 0 ∧ Measure.dirac x₁ ({x₁} : Set 𝒳)ᶜ = 0 ∧
        Measure.dirac x₃ ({x₃} : Set 𝒳)ᶜ = 0 ∧
        P = ENNReal.ofReal (1 - 1 / 2) • Measure.dirac x₂ + ENNReal.ofReal (1 / 2) • Measure.dirac x₁ ∧
        Q = ENNReal.ofReal (1 - 1 / 2) • Measure.dirac x₂ + ENNReal.ofReal (1 / 2) • Measure.dirac x₃

/-- `prose:ex-separated-three-points (v3)`, G1b, the composed theorem: the conclusion of Example 1 holds for the three-point pair when the
feature map is strictly positive definite on `{x₁,x₂,x₃}`. Let `φ : 𝒳 → ℋ` satisfy (A1) (`StronglyMeasurable φ`, `‖φ x‖ ≤ κ`; `ℋ` a real
Hilbert space, separability (A2) dropped: generalisation, as in `Wave31tb.separated`), `x₁, x₂, x₃` distinct with measurable singletons,
`φ` strictly positive definite on `{x₁,x₂,x₃}`, `P = ½δ_{x₁} + ½δ_{x₂}`, `Q = ½δ_{x₂} + ½δ_{x₃}`. Then `TV(P,Q) = ½ = α⋆`; some
`f ∈ ℋ` takes the values `0` at `x₂`, `1` at `x₁`, `−1` at `x₃` (interpolation); and for every such `f`: `‖f‖ > 0`, for every `α ∈ [0,½]`
`D_α(P,Q) ≥ 2(½−α)/((1−α)‖f‖) ≥ 2(½−α)/‖f‖` (for `D_α` the infimum of MMD over `R_α(P) × R_α(Q)`, `dTrim`, and for the regions' distance
`Dpop`), and Assumption 2 (`Wave30tu.Margin`) holds with `ω(ε) = c₀ε`, `c₀ = 2/‖f‖`. -/
def three_point_margin : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : 𝒳 → H) (κ : ℝ) (x₁ x₂ x₃ : 𝒳) (P Q : Measure 𝒳),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) →
    x₁ ≠ x₂ → x₁ ≠ x₃ → x₂ ≠ x₃ →
    MeasurableSet ({x₁} : Set 𝒳) → MeasurableSet ({x₂} : Set 𝒳) → MeasurableSet ({x₃} : Set 𝒳) →
    StrictlyPDOn φ {x₁, x₂, x₃} →
    P = ENNReal.ofReal (1 / 2) • Measure.dirac x₁ + ENNReal.ofReal (1 / 2) • Measure.dirac x₂ →
    Q = ENNReal.ofReal (1 / 2) • Measure.dirac x₂ + ENNReal.ofReal (1 / 2) • Measure.dirac x₃ →
      StatFormal.Distances.tvDist P Q = 1 / 2 ∧
      (∃ f : H, ⟪f, φ x₂⟫_ℝ = 0 ∧ ⟪f, φ x₁⟫_ℝ = 1 ∧ ⟪f, φ x₃⟫_ℝ = -1) ∧
      ∀ f : H, ⟪f, φ x₂⟫_ℝ = 0 → ⟪f, φ x₁⟫_ℝ = 1 → ⟪f, φ x₃⟫_ℝ = -1 →
        0 < ‖f‖ ∧
        (∀ α ∈ Icc (0 : ℝ) (1 / 2),
          2 * (1 / 2 - α) / ((1 - α) * ‖f‖) ≤ dTrim φ P Q α ∧
          2 * (1 / 2 - α) / ((1 - α) * ‖f‖) ≤ Dpop φ P Q α ∧
          2 * (1 / 2 - α) / ‖f‖ ≤ 2 * (1 / 2 - α) / ((1 - α) * ‖f‖)) ∧
        Margin φ P Q (fun ε => 2 / ‖f‖ * ε)

/-- `prose:ex-separated-matern (v3)`, G1c, the printed function (`B_analytic.tex:318-321`): "a smooth compactly supported function equal to
`1` on the `ε/3`-neighbourhood of `S_P`, to `−1` on that of `S_Q` and to `0` outside their `2ε/3`-neighbourhoods, when `S_P` and `S_Q` are
bounded and `ε > 0`". For bounded `S_P, S_Q ⊆ ℝ^d` with `‖x − y‖ ≥ ε > 0` for `x ∈ S_P`, `y ∈ S_Q`, there is a `C^∞` function `g : ℝ^d → ℝ`
with compact support, equal to `1` on the closed `ε/3`-neighbourhood `{x : infEDist x S_P ≤ ε/3}` (`Metric.cthickening`) of `S_P`, to `−1` on that of `S_Q`, and to `0`
at every point outside both open `2ε/3`-neighbourhoods `{x : infEDist x S_P < 2ε/3}`, `{x : infEDist x S_Q < 2ε/3}` (`Metric.thickening`; the
stronger readings of each clause; empty for an empty set; the two `2ε/3`-neighbourhoods may overlap, `g` is then free there). No bridge is
used. -/
def matern_bump : Prop :=
  ∀ (d : ℕ) (SP SQ : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ),
    Bornology.IsBounded SP → Bornology.IsBounded SQ → 0 < ε → (∀ x ∈ SP, ∀ y ∈ SQ, ε ≤ dist x y) →
      ∃ g : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
        (∀ x ∈ Metric.cthickening (ε / 3) SP, g x = 1) ∧ (∀ x ∈ Metric.cthickening (ε / 3) SQ, g x = -1) ∧
        ∀ x, x ∉ Metric.thickening (2 * ε / 3) SP → x ∉ Metric.thickening (2 * ε / 3) SQ → g x = 0

/-- `prose:ex-separated-matern (v3)`, G1c, the printed sentence (`03_analytic.tex:182-183`): "[Such an `f` exists] when `S_P` and `S_Q` are
bounded, the three sets are at positive distance from each other and `k` is a Matérn kernel on `ℝ^d`, whose RKHS is a Sobolev space", with the
Sobolev identification as the declared bridge `ContainsSmoothCompact φ` (Wendland 2005, Cor. 10.13; the Matérn kernel is not defined here).
Let `d ∈ ℕ`, `φ : ℝ^d → ℋ` a feature map into a real inner product space such that every `C^∞` function with compact support is
represented by an element of `ℋ` (the bridge). If `S_R, S_P, S_Q ⊆ ℝ^d` have pairwise distances at least `ε > 0` and `S_P`, `S_Q` are bounded
(`S_R` arbitrary), then some `f ∈ ℋ` takes the value `0` on `S_R`, `1` on `S_P` and `−1` on `S_Q` (`f(x) = ⟪f, φ x⟫`). -/
def matern_interpolation : Prop :=
  ∀ (d : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (φ : EuclideanSpace ℝ (Fin d) → H),
    ContainsSmoothCompact φ →
    ∀ (SR SP SQ : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ),
      Bornology.IsBounded SP → Bornology.IsBounded SQ → 0 < ε →
      (∀ x ∈ SR, ∀ y ∈ SP, ε ≤ dist x y) → (∀ x ∈ SR, ∀ y ∈ SQ, ε ≤ dist x y) → (∀ x ∈ SP, ∀ y ∈ SQ, ε ≤ dist x y) →
        ∃ f : H, (∀ x ∈ SR, ⟪f, φ x⟫_ℝ = 0) ∧ (∀ x ∈ SP, ⟪f, φ x⟫_ℝ = 1) ∧ (∀ x ∈ SQ, ⟪f, φ x⟫_ℝ = -1)

/-- `prose:margin-not-Q (v3)`, G3b (`05_trimming.tex:77-78`): "Laws with finite support, such as those of Example 1, violate (Q), so the margin
does not imply the density conditions." For every three distinct reals `r₀, r₁, r₂` and every `σ > 0` there are a real separable Hilbert space
`ℋ` and a feature map `φ : Fin 3 → ℋ` of the Gaussian kernel `k(i,j) = exp(−(rᵢ − rⱼ)²/(2σ²))` on the three-point space `𝒳 = Fin 3`
((A1): strongly measurable, `‖φ i‖ ≤ 1` (`κ = 1`); (A2): `ℋ` separable; (A3): `Characteristic φ`), such that for the three-point pair
`P = ½δ₀ + ½δ₁`, `Q = ½δ₁ + ½δ₂` (`x₁, x₂, x₃ = 0, 1, 2`): `P`, `Q` are probability measures with `TV(P,Q) = ½ = α⋆`, Assumption 2 holds
(with the linear `ω(ε) = c₀ε`, `c₀ > 0`: the margin of Example 1), `P` and `Q` have finite support (`{0,1}`, `{1,2}`), and for every level
`α ∈ (0,α⋆)`: `D_α(P,Q) > 0`, a population witness `d⋆` (an element of minimal norm of `𝒞_α(P) − 𝒞_α(Q)`) exists, and for every such `d⋆` a
`(1−α)`-quantile `t_α` of `d⋆(X)` under `P` exists, and (Q) fails: for every `r_Q > 0`, `c_f > 0` and `C_f` the law of `d⋆(X)` has no density
with values in `[c_f, C_f]` on `[t_α − r_Q, t_α + r_Q]` (`¬ QDensity`). Also, for every function `f`, level `t`, `r > 0`, `c > 0`, `C`:
`¬ QDensity P f t r c C`, and the lower-density condition (Q′) fails for `Q`: `¬ QDensityLower Q f u r c` (the form of
`Wave31td.finite_support_not_Q`). So Assumption 2, even with `γ = 1`, does not imply (Q). -/
def margin_not_Q : Prop :=
  ∀ (r : Fin 3 → ℝ) (σ : ℝ), Function.Injective r → 0 < σ →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H)
      (_ : TopologicalSpace.SeparableSpace H) (φ : Fin 3 → H),
      (∀ i j, ⟪φ i, φ j⟫_ℝ = Real.exp (-((r i - r j) ^ 2) / (2 * σ ^ 2))) ∧
      StronglyMeasurable φ ∧ (∀ i, ‖φ i‖ ≤ 1) ∧ Characteristic φ ∧
      ∀ P Q : Measure (Fin 3),
        P = ENNReal.ofReal (1 / 2) • Measure.dirac 0 + ENNReal.ofReal (1 / 2) • Measure.dirac 1 →
        Q = ENNReal.ofReal (1 / 2) • Measure.dirac 1 + ENNReal.ofReal (1 / 2) • Measure.dirac 2 →
          IsProbabilityMeasure P ∧ IsProbabilityMeasure Q ∧
          StatFormal.Distances.tvDist P Q = 1 / 2 ∧
          (∃ c₀ : ℝ, 0 < c₀ ∧ Margin φ P Q (fun ε => c₀ * ε)) ∧
          P ({0, 1} : Set (Fin 3))ᶜ = 0 ∧ Q ({1, 2} : Set (Fin 3))ᶜ = 0 ∧
          (∀ α ∈ Ioo (0 : ℝ) (1 / 2),
            0 < Dpop φ P Q α ∧
            (∃ dstar : H, IsMinNorm (region φ α P - region φ α Q) dstar) ∧
            ∀ dstar : H, IsMinNorm (region φ α P - region φ α Q) dstar →
              (∃ t : ℝ, IsQuantile P (witFn dstar φ) (1 - α) t) ∧
              ∀ t : ℝ, IsQuantile P (witFn dstar φ) (1 - α) t →
                ∀ ρ c C : ℝ, 0 < ρ → 0 < c → ¬ QDensity P (witFn dstar φ) t ρ c C) ∧
          (∀ (f : Fin 3 → ℝ) (t ρ c C : ℝ), 0 < ρ → 0 < c → ¬ QDensity P f t ρ c C) ∧
          (∀ (f : Fin 3 → ℝ) (u ρ c : ℝ), 0 < ρ → 0 < c → ¬ QDensityLower Q f u ρ c)

end Claims

end StatFormal.Wave31tg
