import StatFormal.Wave30tx.Statements
import StatFormal.Archive.TrimmedMMD.Projection.Statements
import StatFormal.Lib.Distances.TV
import Mathlib.Probability.ConditionalProbability

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 31td: trimmed-mmd (jmlr) **v3**, the linear-kernel instance of (Q) (prose after `rem:qdens`)

Printed source: `trimmed-mmd/jmlr/v3/NEW_STATEMENTS.md`, last section "linear-kernel (Q) instance (prose after rem:qdens in §5.2; added
after the cold read, frozen 2026-11-12)" (read-only, read 2026-11-12, sha256
`cc72897583ce85135f52e95eb19ff3b2125c427cc33d7a25857bf6f4aff80dbb`; trimmed-mmd master `ad9511a`, where `jmlr/v3/` is committed). The
paragraph is printed, unlabelled, right after `rem:qdens` at `jmlr/v3/sections/05_trimming.tex:74-79` (sha256
`12560de0458469ceb6108d88c31d11c91028d2d00fe89ae803129fd89710ccff`); (Q), (Q′) at `:55-61`; `R_α`, `D_α`, `𝒞_α`, `prop:georep`, the
witness `d⋆` (the element of minimal norm of `𝒞_α(P) − 𝒞_α(Q)`) at `jmlr/v3/sections/02_regions.tex:15, 70, 77, 84-90, 165-166`. The printed
text:

> For a fully explicit instance, take the linear kernel `k(x,y) = xy` on `𝒳 = [−1,1]`, which satisfies (A1) and (A2), with `P` uniform on
> `[−½,1]` and `Q` uniform on `[−1,½]`, so that `α⋆ = ⅓`. The regions are intervals of trimmed means, `D_α(P,Q) = (3/2)(⅓ − α)` for
> `α < ⅓`, `d⋆(x) = D_α(P,Q) x`, and (Q) and (Q′) hold with the constant density `2/(3D_α(P,Q))`. Laws with finite support, which satisfy
> the margin by Example `ex:separated`, violate (Q), so the two kinds of condition describe different pairs.

and the frozen formal targets (for every `α ∈ (0, ⅓)`): (a) `TV(P,Q) = ⅓`; (b) with `ℋ = ℝ`, `φ(x) = x`,
`C_α(P) = [−½ + ¾(1−α), 1 − ¾(1−α)]`, `C_α(Q) = [−1 + ¾(1−α), ½ − ¾(1−α)]`; (c) `D_α(P,Q) = (3/2)(⅓ − α) > 0`; (d) the minimal-norm
element of `C_α(P) − C_α(Q)` is `d⋆ = D_α(P,Q)`, so `d⋆(x) = D_α(P,Q)·x`; (e) the law of `d⋆(X)` under `P` is uniform on `[−D/2, D]` and
that of `d⋆(Y)` under `Q` uniform on `[−D, D/2]` (`D = D_α(P,Q)`), each with density `2/(3D)`, the `(1−α)`-quantile `t_α` of `d⋆(X)` and the
`α`-quantile `u_α` of `d⋆(Y)` are interior points, so (Q) and (Q′) hold for some `r_Q > 0` with `c_f = C_f = c′_f = 2/(3D)`; also "at
`α = ⅓` the path is `0`".

Covered here (10 claims, label `prose:linear-kernel (v3)`, the unlabelled paragraph after `rem:qdens`):
* `linear_setting` — the objects: `P`, `Q` are probability measures on `𝒳 = [−1,1]` with densities `2/3` on `[−½,1]`, `[−1,½]`; (A1)
  (`φ` strongly measurable, `‖φ(x)‖ ≤ 1`, `⟪φ(x), φ(y)⟫ = xy`); (A2) is the instance `ℋ = ℝ`.
* `linear_tv` — (a), `TV(P,Q) = ⅓` (`= α⋆`).
* `linear_regions` — (b), for every `α ∈ [0,1)` (generalisation of `(0,⅓)`).
* `linear_trimmed_means` — "intervals of trimmed means": each endpoint is the mean of `P` (or `Q`) over its lower or upper part of mass
  `1−α`, for every `α ∈ [0,1)`.
* `linear_D` — (c), as `D_α(P,Q) = max((3/2)(⅓ − α), 0)` for every `α ∈ [0,1)` (so `0` at `α = ⅓` and beyond: the "also note"), for both
  the regions' distance `Dpop` and the printed infimum over trimmings `dTrim`; and `= (3/2)(⅓ − α) > 0` on `(0,⅓)`.
* `linear_witness` — (d), for every `α ∈ [0,1)`: `D_α(P,Q)` is the unique element of minimal norm of `𝒞_α(P) − 𝒞_α(Q)`, and
  `d⋆(x) = ⟪d⋆, φ(x)⟫ = D_α(P,Q)·x`.
* `linear_laws` — (e), the laws of `d⋆(X)` and `d⋆(Y)`: densities `2/(3D)` on `[−D/2, D]` and `[−D, D/2]`, i.e. Mathlib's uniform laws.
* `linear_quantiles` — (e), the quantiles are unique, `t_α = D(−½ + (3/2)(1−α))`, `u_α = D(−1 + (3/2)α)`, interior points.
* `linear_Q_Qprime` — (e), (Q) and (Q′) with one `r_Q > 0` and `c_f = C_f = c′_f = 2/(3D) > 0`, at every `(1−α)`-quantile `t_α` and every
  `α`-quantile `u_α`, for the population witness `d⋆` (any element of minimal norm), in the form of `Wave31tc.qdens_Q_Qprime` and of the
  hypotheses of `Wave31ta.cor_trimrate_v2` (there `ρ` is fixed before the quantiles; here `r_Q` comes after them, as printed, and the two
  agree because the quantiles are unique, `linear_quantiles`).
* `finite_support_not_Q` — the printed sentence "laws with finite support … violate (Q)": for a law concentrated on a finite set, no
  function `f`, level `t` and `r > 0` give (Q) or even (Q′) with a positive lower density bound.

Reuses (imported, not copied): `TrimmedMMD.Concentration.region` (`𝒞_α`, `eq:region`), `TrimmedMMD.Unconditional.Dpop` (the regions'
distance, `eq:setdist`; the `D_α` of every certified estimator claim), `Wave8a.dTrim` (the printed `D_α`, `eq:trimMMDpop`: the infimum of
`‖μ_{P′} − μ_{Q′}‖` over `R_α(P) × R_α(Q)`, `Wave8a.trimSet` literal), `TrimmedMMD.Projection.IsMinNorm` (the witness `d⋆`),
`Wave12c.witFn` (`d⋆(x) = ⟨d⋆, φ(x)⟩`), `Wave12c.QDensity`/`QDensityLower` ((Q), (Q′)), `Wave30tx.IsQuantile` (`t` is a `p`-quantile:
`R(f < t) ≤ p ≤ R(f ≤ t)`), `Distances.tvDist` (`TV(P,Q) = sup_A |P(A) − Q(A)|`), Mathlib's `ProbabilityTheory.cond` (`volume[|Icc a b]` is
Mathlib's uniform law on `[a,b]`, the law in `MeasureTheory.pdf.IsUniform`).

Encodings (see the card `certify/cards/wave31td.md`):
* `𝒳 = [−1,1]` is the subtype `Icc (-1 : ℝ) 1` (its subtype σ-algebra); `ℋ = ℝ` with `⟪a, b⟫ = ab`; `φ(x) = x` (`phiLin`), so
  `k(x,y) = ⟪φ(x), φ(y)⟫ = xy` and `‖φ(x)‖ = |x| ≤ 1 = κ` ((A1); the RKHS of `k` is `{x ↦ cx} ≅ ℝ`, isometric to this `ℋ`; separable, (A2)).
* "`P` uniform on `[−½,1]`": `Plin = comap Subtype.val (volume[|Icc (−½) 1])`, the uniform law on `ℝ` seen on `[−1,1]` (no mass is lost:
  `[−½,1] ⊆ [−1,1]`; `linear_setting` certifies that `Plin` is a probability measure with `Plin(X ∈ B) = (2/3) λ(B ∩ [−½,1])`). Same for `Q`.
* "the law of `d⋆(X)` under `P` is uniform on `[a,b]`": `Plin.map d⋆ = volume[|Icc a b]` (`d⋆` is continuous, so `Measure.map` is genuine),
  together with the explicit density form `Plin(d⋆ ∈ B) = (2/(3D)) λ(B ∩ [a,b])` for every Borel `B`.
* "trimmed mean": the mean of the law over its lowest (highest) fraction `1−α`, the set `{x ≤ q}` (`{x ≥ q}`) of mass exactly `1−α`,
  `(1−α)⁻¹ ∫_{x ≤ q} x dP` — the one-sided `α`-trimmed mean (mass `α` removed from the top, respectively the bottom); the claim certifies
  the mass and the mean.
* (c) is stated for `α ∈ [0,1)` with a `max(·, 0)`, which contains the printed formula for `α < ⅓` (the frozen target states it on
  `(0,⅓)`), its positivity and the note at `α = ⅓`.
* (e): the witness is any `dstar ∈ ℝ` with `IsMinNorm (𝒞_α(P) − 𝒞_α(Q)) dstar` (the paper's definition of `d⋆`; it is `D` by
  `linear_witness`); quantiles are `IsQuantile` (any `p`-quantile; both are unique here); "for some `r_Q > 0`" is `∃ rQ, 0 < rQ ∧ …` after
  the quantiles, one `r_Q` for (Q) and (Q′) as printed. (`r_Q = (3/2)Dα` works; not part of the claim.)
* "finite support": `P(Sᶜ) = 0` for a finite set `S` (any measurable space `𝒳`, any measure, any `f`); stated as
  `¬ QDensity P f t r c C` and `¬ QDensityLower P f t r c` for every `t`, `r > 0`, `c > 0`, `C` (generalisation: `P` need not be finite).
* Junk values: `2/(3D)` only for `α ∈ (0,⅓)`, where `D > 0` is certified (`linear_D`); `1/(1−α)` inside `region`, `trimSet` only for
  `α < 1`; `(1−α)⁻¹` in the trimmed means only for `α < 1`; `region`'s Bochner integrals are of bounded measurable functions on a
  probability space (genuine); `Dpop` is the `sInf` of a nonempty set bounded below by `0`; `dTrim` likewise; `tvDist` is the `⨆` of a set
  bounded by `1`; `Measure.map` of a continuous (measurable) map.
* Not covered: "which satisfy the margin by Example `ex:separated`" (`ex:separated`, certified in wave 31tb on another branch, gives the
  margin for separated pairs only — core and contaminations on pairwise disjoint sets with an interpolating `f ∈ ℋ`; the clause for all
  finite-support laws is not formalised); the clause "so the two kinds of condition describe different pairs" (a reading of the two facts);
  the parenthetical of the frozen note "the linear kernel is not characteristic, but the computation does not need (A3)" (a remark in
  `NEW_STATEMENTS.md`, not printed in the paragraph; no claim here assumes (A3)).
FROZEN 2026-11-12 before any proof, after an independent critic's pre-freeze review (10 claims: 7 ACCEPT, 3 ACCEPT-WITH-NOTE, none false,
verdict READY TO FREEZE; it back-translated the claims blind, typechecked a scratch file proving `Plin univ = Qlin univ = 1` and the parses
of `(1−α)⁻¹ * ∫ …` and of the Minkowski difference, and checked the region endpoints and `D_α` by linear programs on a 6000-cell grid, the
masses and means exactly, and the laws, quantiles and windows by 2·10⁶-draw Monte Carlo; applied: the trimmed-mean wording (one-sided
`α`-trimmed means), the (c) wording, the `r_Q`-after-quantiles note, the margin and (A3) items under Not covered). Hashed in
`certify/statements.lock` (with its imports); AI agents must not edit this file.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace RealInnerProductSpace Pointwise

namespace StatFormal.Wave31td

open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional StatFormal.TrimmedMMD.Projection
  StatFormal.Wave8a StatFormal.Wave12c StatFormal.Wave30tx

/-- The feature map of the linear kernel `k(x,y) = xy` on `𝒳 = [−1,1]`: `φ(x) = x ∈ ℋ = ℝ`, so `k(x,y) = ⟪φ(x), φ(y)⟫ = xy`. -/
def phiLin (x : Icc (-1 : ℝ) 1) : ℝ := x

/-- The uniform law on `[a,b]` as a law on `𝒳 = [−1,1]`: Mathlib's uniform law `volume[|Icc a b]` on `ℝ` (the law of
`MeasureTheory.pdf.IsUniform`), pulled back to the subtype `[−1,1]` (for `[a,b] ⊆ [−1,1]` no mass is lost). -/
def unifLin (a b : ℝ) : Measure (Icc (-1 : ℝ) 1) :=
  Measure.comap Subtype.val (ProbabilityTheory.cond volume (Icc a b))

/-- `P`, uniform on `[−½, 1]`. -/
def Plin : Measure (Icc (-1 : ℝ) 1) := unifLin (-1 / 2) 1

/-- `Q`, uniform on `[−1, ½]`. -/
def Qlin : Measure (Icc (-1 : ℝ) 1) := unifLin (-1) (1 / 2)

namespace Claims

/-- The setting of the instance: `P` and `Q` are probability measures on `𝒳 = [−1,1]` with `P(X ∈ B) = (2/3) λ(B ∩ [−½,1])` and
`Q(Y ∈ B) = (2/3) λ(B ∩ [−1,½])` for every Borel `B ⊆ ℝ` (uniform laws); (A1): `φ` is strongly measurable with `‖φ(x)‖ ≤ 1`, and
`k(x,y) = ⟪φ(x), φ(y)⟫ = xy`. -/
def linear_setting : Prop :=
  IsProbabilityMeasure Plin ∧ IsProbabilityMeasure Qlin ∧
    (∀ B : Set ℝ, MeasurableSet B →
      Plin (Subtype.val ⁻¹' B) = ENNReal.ofReal (2 / 3) * volume (B ∩ Icc (-1 / 2) 1)) ∧
    (∀ B : Set ℝ, MeasurableSet B →
      Qlin (Subtype.val ⁻¹' B) = ENNReal.ofReal (2 / 3) * volume (B ∩ Icc (-1) (1 / 2))) ∧
    StronglyMeasurable phiLin ∧ (∀ x, ‖phiLin x‖ ≤ 1) ∧
    ∀ x y : Icc (-1 : ℝ) 1, ⟪phiLin x, phiLin y⟫_ℝ = (x : ℝ) * y

/-- (a) `TV(P,Q) = ⅓`, so `α⋆ = TV(P,Q) = ⅓`. -/
def linear_tv : Prop :=
  StatFormal.Distances.tvDist Plin Qlin = 1 / 3

/-- (b) The regions of the linear kernel are intervals: for every `α ∈ [0,1)`,
`𝒞_α(P) = [−½ + ¾(1−α), 1 − ¾(1−α)]` and `𝒞_α(Q) = [−1 + ¾(1−α), ½ − ¾(1−α)]`. -/
def linear_regions : Prop :=
  ∀ α : ℝ, 0 ≤ α → α < 1 →
    region phiLin α Plin = Icc (-1 / 2 + 3 / 4 * (1 - α)) (1 - 3 / 4 * (1 - α)) ∧
    region phiLin α Qlin = Icc (-1 + 3 / 4 * (1 - α)) (1 / 2 - 3 / 4 * (1 - α))

/-- (b) "intervals of trimmed means": for every `α ∈ [0,1)`, the endpoints of `𝒞_α(P)` are the means of `P` over its lower part
`{x ≤ −½ + (3/2)(1−α)}` and its upper part `{x ≥ 1 − (3/2)(1−α)}`, each of mass `1−α` (the one-sided `α`-trimmed means: the means of `P`
after removing mass `α` from the top, respectively the bottom), and
likewise for `Q` with `{x ≤ −1 + (3/2)(1−α)}` and `{x ≥ ½ − (3/2)(1−α)}`. -/
def linear_trimmed_means : Prop :=
  ∀ α : ℝ, 0 ≤ α → α < 1 →
    (Plin.real {x | (x : ℝ) ≤ -1 / 2 + 3 / 2 * (1 - α)} = 1 - α ∧
      (1 - α)⁻¹ * ∫ x in {x | (x : ℝ) ≤ -1 / 2 + 3 / 2 * (1 - α)}, phiLin x ∂Plin = -1 / 2 + 3 / 4 * (1 - α)) ∧
    (Plin.real {x | 1 - 3 / 2 * (1 - α) ≤ (x : ℝ)} = 1 - α ∧
      (1 - α)⁻¹ * ∫ x in {x | 1 - 3 / 2 * (1 - α) ≤ (x : ℝ)}, phiLin x ∂Plin = 1 - 3 / 4 * (1 - α)) ∧
    (Qlin.real {x | (x : ℝ) ≤ -1 + 3 / 2 * (1 - α)} = 1 - α ∧
      (1 - α)⁻¹ * ∫ x in {x | (x : ℝ) ≤ -1 + 3 / 2 * (1 - α)}, phiLin x ∂Qlin = -1 + 3 / 4 * (1 - α)) ∧
    (Qlin.real {x | 1 / 2 - 3 / 2 * (1 - α) ≤ (x : ℝ)} = 1 - α ∧
      (1 - α)⁻¹ * ∫ x in {x | 1 / 2 - 3 / 2 * (1 - α) ≤ (x : ℝ)}, phiLin x ∂Qlin = 1 / 2 - 3 / 4 * (1 - α))

/-- (c) For every `α ∈ [0,1)`, `D_α(P,Q) = max((3/2)(⅓ − α), 0)`, both as the distance between the regions (`Dpop`) and as the printed
infimum of `MMD(P′,Q′)` over `R_α(P) × R_α(Q)` (`dTrim`); in particular `D_α(P,Q) = (3/2)(⅓ − α) > 0` for `α ∈ (0,⅓)`, and the path is `0`
from `α = ⅓` on. -/
def linear_D : Prop :=
  (∀ α : ℝ, 0 ≤ α → α < 1 →
    Dpop phiLin Plin Qlin α = max (3 / 2 * (1 / 3 - α)) 0 ∧
    dTrim phiLin Plin Qlin α = max (3 / 2 * (1 / 3 - α)) 0) ∧
  ∀ α : ℝ, 0 < α → α < 1 / 3 →
    Dpop phiLin Plin Qlin α = 3 / 2 * (1 / 3 - α) ∧ 0 < Dpop phiLin Plin Qlin α

/-- (d) For every `α ∈ [0,1)`, the element of minimal norm of `𝒞_α(P) − 𝒞_α(Q)` is `d⋆ = D_α(P,Q)` (it is one, and every one equals it),
so the witness function is `d⋆(x) = ⟪d⋆, φ(x)⟫ = D_α(P,Q)·x`. -/
def linear_witness : Prop :=
  ∀ α : ℝ, 0 ≤ α → α < 1 →
    IsMinNorm (region phiLin α Plin - region phiLin α Qlin) (Dpop phiLin Plin Qlin α) ∧
    (∀ d : ℝ, IsMinNorm (region phiLin α Plin - region phiLin α Qlin) d → d = Dpop phiLin Plin Qlin α) ∧
    ∀ x : Icc (-1 : ℝ) 1, witFn (Dpop phiLin Plin Qlin α) phiLin x = Dpop phiLin Plin Qlin α * x

/-- (e) The laws of the witness: for `α ∈ (0,⅓)`, `D = D_α(P,Q)` and the population witness `d⋆` (an element of minimal norm of
`𝒞_α(P) − 𝒞_α(Q)`), the law of `d⋆(X)` under `P` has density `2/(3D)` on `[−D/2, D]` and none elsewhere, and that of `d⋆(Y)` under `Q`
density `2/(3D)` on `[−D, D/2]`: they are the uniform laws `volume[|Icc (−D/2) D]` and `volume[|Icc (−D) (D/2)]`. -/
def linear_laws : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 / 3 → ∀ dstar : ℝ, IsMinNorm (region phiLin α Plin - region phiLin α Qlin) dstar →
    let D := Dpop phiLin Plin Qlin α
    (∀ B : Set ℝ, MeasurableSet B →
      Plin (witFn dstar phiLin ⁻¹' B) = ENNReal.ofReal (2 / (3 * D)) * volume (B ∩ Icc (-D / 2) D)) ∧
    (∀ B : Set ℝ, MeasurableSet B →
      Qlin (witFn dstar phiLin ⁻¹' B) = ENNReal.ofReal (2 / (3 * D)) * volume (B ∩ Icc (-D) (D / 2))) ∧
    Plin.map (witFn dstar phiLin) = ProbabilityTheory.cond volume (Icc (-D / 2) D) ∧
    Qlin.map (witFn dstar phiLin) = ProbabilityTheory.cond volume (Icc (-D) (D / 2))

/-- (e) The quantiles: for `α ∈ (0,⅓)`, `D = D_α(P,Q)` and the population witness `d⋆`, the `(1−α)`-quantile of `d⋆(X)` under `P` is unique,
`t_α = D(−½ + (3/2)(1−α))`, the `α`-quantile of `d⋆(Y)` under `Q` is unique, `u_α = D(−1 + (3/2)α)`, and they are interior points of
`[−D/2, D]` and `[−D, D/2]`. -/
def linear_quantiles : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 / 3 → ∀ dstar : ℝ, IsMinNorm (region phiLin α Plin - region phiLin α Qlin) dstar →
    let D := Dpop phiLin Plin Qlin α
    (∀ t : ℝ, IsQuantile Plin (witFn dstar phiLin) (1 - α) t ↔ t = D * (-1 / 2 + 3 / 2 * (1 - α))) ∧
    (∀ u : ℝ, IsQuantile Qlin (witFn dstar phiLin) α u ↔ u = D * (-1 + 3 / 2 * α)) ∧
    D * (-1 / 2 + 3 / 2 * (1 - α)) ∈ Ioo (-D / 2) D ∧ D * (-1 + 3 / 2 * α) ∈ Ioo (-D) (D / 2)

/-- (e) (Q) and (Q′) with the constant density: for `α ∈ (0,⅓)`, `D = D_α(P,Q)` and the population witness `d⋆`, `2/(3D) > 0`, and for
every `(1−α)`-quantile `t_α` of `d⋆(X)` under `P` and every `α`-quantile `u_α` of `d⋆(Y)` under `Q` there is `r_Q > 0` such that the law
of `d⋆(X)` has on `[t_α − r_Q, t_α + r_Q]` a density with values in `[2/(3D), 2/(3D)]` ((Q) with `c_f = C_f = 2/(3D)`) and the law of
`d⋆(Y)` has on `[u_α − r_Q, u_α + r_Q]` a density at least `2/(3D)` ((Q′) with `c′_f = 2/(3D)`). -/
def linear_Q_Qprime : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 / 3 → ∀ dstar : ℝ, IsMinNorm (region phiLin α Plin - region phiLin α Qlin) dstar →
    let D := Dpop phiLin Plin Qlin α
    0 < 2 / (3 * D) ∧
    ∀ tα uα : ℝ, IsQuantile Plin (witFn dstar phiLin) (1 - α) tα → IsQuantile Qlin (witFn dstar phiLin) α uα →
      ∃ rQ : ℝ, 0 < rQ ∧
        QDensity Plin (witFn dstar phiLin) tα rQ (2 / (3 * D)) (2 / (3 * D)) ∧
        QDensityLower Qlin (witFn dstar phiLin) uα rQ (2 / (3 * D))

/-- "Laws with finite support … violate (Q)": if a measure `P` on any measurable space is concentrated on a finite set `S`, then
for every `f : 𝒳 → ℝ`, level `t`, half-width `r > 0` and bounds `c > 0`, `C`, the law of `f(X)` has on `[t − r, t + r]` no density with
values in `[c, C]` (`¬ (Q)`), nor even a density at least `c` (`¬ (Q′)`). -/
def finite_support_not_Q : Prop :=
  ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (P : Measure 𝒳) (S : Set 𝒳), S.Finite → P Sᶜ = 0 →
    ∀ (f : 𝒳 → ℝ) (t r c C : ℝ), 0 < r → 0 < c →
      ¬ QDensity P f t r c C ∧ ¬ QDensityLower P f t r c

end Claims

end StatFormal.Wave31td
