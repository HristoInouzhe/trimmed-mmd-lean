import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Homeomorph.Defs

/-!
# FROZEN STATEMENTS — otfd A: the probability scale `Υ` and `lem:T-risk`

**Draft for critic review; not frozen, not hashed.**

Sources (verbatim in `lean-formalisation/inventory/extracted/otfd-A_sieves.md`):
* `otfd/papers/A_sieves/main.tex:1202-1217` (paragraph "The probability scale"): `g_K` a norm on
  `ℝ^K`, `c_K(s) := μ_K{g_K ≤ s}`, `ρ_K := inf{s : c_K(s) = 1} ∈ (0, ∞]`; assume `c_K` continuous and
  strictly increasing on `[0, ρ_K)` with `c_K(0) = 0`, and `μ_K{g_K = ρ_K} = 0` (the hypothesis added
  2026-10-13); `Υ(r) := c_K(g_K r) · r / g_K r`, `Υ(0) = 0`. "It is continuous, takes values in the
  closed unit ball `{g_K ≤ 1}`, maps `{g_K < ρ_K}` homeomorphically onto the open ball `{g_K < 1}`,
  and sends everything beyond `ρ_K` to the sphere."
* `otfd/papers/A_sieves/supplement.tex:4873-4880` (the two facts): `S := (Υ|_{g_K<ρ_K})⁻¹` is
  continuous on `𝔹`, `S(w) = c_K⁻¹(g_K w) · w / g_K w`; `λ(∂𝔹) = 0` for `λ := Υ#μ_K`.
* `otfd/papers/A_sieves/supplement.tex:4930-4951` (`lem:T-risk` and proof): "For Borel maps
  `G_j : ℝ^K → ℝ^K` and `Z ∼ P_K`, `E‖Υ G_j(Z) − Υ F_K(Z)‖² → 0` if and only if `G_j → F_K` in
  `P_K`-probability. If `F̂_θ` is random, the same holds in probability."

Covered:
* `ups_ball`: `Υ` is continuous, `g(Υ r) ≤ 1`, `g(Υ r) = 1` beyond `ρ` (i.e. when `c(g r) = 1`), and
  `μ{r | g(Υ r) < 1} = 1` (`λ(∂𝔹) = 0`, the second fact; uses the added hypothesis);
* `ups_homeo`: `Υ` restricts to a homeomorphism `{g < ρ} ≃ₜ {g < 1}` whose inverse is the explicit
  `S(w) = c⁻¹(g w) · w / g w` (the first fact);
* `t_risk`: `lem:T-risk`, deterministic maps, both directions;
* `atom_needed`: without the added hypothesis `μ{g = ρ} = 0` (all other assumptions kept) the "only
  if" half of `lem:T-risk` is false (a fortiori the equivalence is false). Witness (proof route):
  `ℝ`, `g = |·|`, `μ = ¼ Leb|[−1,1] + ¼ δ₋₁ + ¼ δ₁`, `P = μ`, `F = id`, `G_j = G` with `G = 2·id` on
  `{|x| = 1}` and `id` elsewhere.
Not covered (declared): the random version of `lem:T-risk` ("if `F̂_θ` is random, the same holds in
probability", i.e. conditionally on the training fold, with `θ_n` data-dependent); the claim that the
added hypothesis holds whenever `μ_K` is absolutely continuous and its equivalence with
`c_K(ρ_K⁻) = 1`; `R_Υ`, the energy distance, `lem:T-stability` and everything after; the identity-scale
and whitening remarks; the fact that `F_K` is the gradient of a convex function (not used: any Borel
`F` with `F#P = μ` is allowed, a generalisation).

Encodings (to be checked by the critic):
* `ℝ^K` is generalised to any finite-dimensional real normed space `E` with its Borel σ-algebra; the
  norm `‖·‖` in the risk and in the probability event is `E`'s norm (Euclidean for
  `E = EuclideanSpace ℝ (Fin K)`); `g_K` is any function satisfying `IsGauge` (a norm on `E`, possibly
  different from `‖·‖`).
* `[0, ρ_K)` is written `{s | 0 ≤ s ∧ c s < 1}` and `{g_K < ρ_K}` as `{r | c(g r) < 1}`; these agree
  because `c` is monotone and right-continuous (`c(ρ) = 1` when `ρ < ∞`); `ρ_K = ∞` is the case
  `c < 1` everywhere and needs no separate treatment.
* "continuous on `[0, ρ_K)`" is `ContinuousAt c s` for each `s` in that set; equivalent, since
  `c = 0` on `(−∞, 0)` and `c(0) = 0`.
* `μ_K{g_K = ρ_K} = 0` is `ScaleHyp.atom`: `μ{g = s} = 0` whenever `c s = 1` (for `s > ρ_K` this is
  automatic, so it is equivalent; for `ρ_K = ∞` it is void).
* `Υ(0) = 0` and `S(0) = 0` come from Lean's `x / 0 = 0` and agree with the paper's convention.
  `c⁻¹` is `cinv y = sInf {s | 0 ≤ s ∧ y ≤ c s}`; `S` is only claimed on `{g < 1}`, where the set is
  nonempty (no `sInf ∅ = 0` junk is reached).
* `Z ∼ P_K` is a probability measure `P` on `E`; `F_K` is any measurable `F` with `P.map F = μ`
  (`F_K#P_K = μ_K`); `G_j` are measurable (Borel). Expectation is the Bochner integral: the integrand
  is measurable and bounded (`Υ` takes values in `{g ≤ 1}`), so the integral is not a junk `0`.
  Convergence in probability is `∀ η > 0, P.real {z | η < ‖G j z − F z‖} → 0`, an event that is
  measurable because `G j`, `F` are.
* `atom_needed` is the negation of the universally quantified "only if" half of `t_risk` with
  `ScaleHyp` replaced by its first three fields (`zero`, `cont`, `mono`), stated inline.

Hash-lock: when frozen, this file is renamed `Statements.lean` and hashed in
`certify/statements.lock` (with its imports); AI agents must not edit it after that.
(The untrusted `Route*.lean` files define the same names in `StatFormal.OTFD.Scale`; they must be
switched to import the frozen file and drop their copies.)
Critic note: in `t_risk`, `P` and `F` (any measurable map with `F#P = μ`) are intentionally more general than the paper's
`F_K` — the proof uses only `F(Z) ∼ μ_K`; the random (in-probability, conditional on the training fold) version is deferred.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace StatFormal.OTFD.Scale

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A norm on `E` given as a function (the gauge `g_K` of the paper). -/
structure IsGauge (g : E → ℝ) : Prop where
  smul : ∀ (t : ℝ) (x : E), g (t • x) = |t| * g x
  add_le : ∀ x y, g (x + y) ≤ g x + g y
  eq_zero : ∀ x, g x = 0 → x = 0

variable [MeasurableSpace E]

/-- `c_K(s) = μ{g ≤ s}`. -/
def cK (μ : Measure E) (g : E → ℝ) (s : ℝ) : ℝ := μ.real {x | g x ≤ s}

/-- The paper's assumption on `c_K` (with the 2026-10-13 correction as `atom`). -/
structure ScaleHyp (μ : Measure E) (g : E → ℝ) : Prop where
  zero : cK μ g 0 = 0
  cont : ∀ s, 0 ≤ s → cK μ g s < 1 → ContinuousAt (cK μ g) s
  mono : StrictMonoOn (cK μ g) {s | 0 ≤ s ∧ cK μ g s < 1}
  atom : ∀ s, cK μ g s = 1 → μ {x | g x = s} = 0

/-- `Υ(r) = c_K(g r) · r / g r` (and `Υ(0) = 0`, automatically since `x / 0 = 0`). -/
def ups (μ : Measure E) (g : E → ℝ) (r : E) : E := (cK μ g (g r) / g r) • r

/-- Generalised inverse of `c` on `[0,1)`. -/
def cinv (μ : Measure E) (g : E → ℝ) (y : ℝ) : ℝ := sInf {s | 0 ≤ s ∧ y ≤ cK μ g s}

/-- `S(w) = c⁻¹(g w) · w / g w`. -/
def Sinv (μ : Measure E) (g : E → ℝ) (w : E) : E := (cinv μ g (g w) / g w) • w

namespace Claims

/-- `Υ` is continuous, takes values in `{g ≤ 1}`, sends `{g ≥ ρ}` (`= {c ∘ g = 1}`) to the sphere,
and maps the reference into the open ball: `(Υ#μ){g < 1} = 1`. -/
def ups_ball : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsProbabilityMeasure μ] (g : E → ℝ),
    IsGauge g → ScaleHyp μ g →
      Continuous (ups μ g) ∧ (∀ r, g (ups μ g r) ≤ 1) ∧
      (∀ r, cK μ g (g r) = 1 → g (ups μ g r) = 1) ∧
      μ {r | g (ups μ g r) < 1} = 1

/-- `Υ` maps `{g < ρ}` (`= {c ∘ g < 1}`) homeomorphically onto `{g < 1}`, with inverse `S`. -/
def ups_homeo : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsProbabilityMeasure μ] (g : E → ℝ),
    IsGauge g → ScaleHyp μ g →
      ∃ h : {r : E // cK μ g (g r) < 1} ≃ₜ {w : E // g w < 1},
        (∀ r, (h r : E) = ups μ g r) ∧ ∀ w, (h.symm w : E) = Sinv μ g w

/-- **`lem:T-risk`** (deterministic maps): the probability-scale risk tends to `0` iff
`G_j → F` in `P`-probability. -/
def t_risk : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsProbabilityMeasure μ] (g : E → ℝ),
    IsGauge g → ScaleHyp μ g →
    ∀ (P : Measure E) [IsProbabilityMeasure P] (F : E → E) (G : ℕ → E → E),
      Measurable F → P.map F = μ → (∀ j, Measurable (G j)) →
      (Tendsto (fun j => ∫ z, ‖ups μ g (G j z) - ups μ g (F z)‖ ^ 2 ∂P) atTop (𝓝 0) ↔
        ∀ η > 0, Tendsto (fun j => P.real {z | η < ‖G j z - F z‖}) atTop (𝓝 0))

/-- **The added hypothesis `μ{g = ρ} = 0` is needed**: with only `c(0) = 0` and continuity and strict
monotonicity of `c` on `[0, ρ)`, the "only if" half of `lem:T-risk` is false. -/
def atom_needed : Prop :=
  ¬ ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsProbabilityMeasure μ] (g : E → ℝ),
    IsGauge g → cK μ g 0 = 0 →
    (∀ s, 0 ≤ s → cK μ g s < 1 → ContinuousAt (cK μ g) s) →
    StrictMonoOn (cK μ g) {s | 0 ≤ s ∧ cK μ g s < 1} →
    ∀ (P : Measure E) [IsProbabilityMeasure P] (F : E → E) (G : ℕ → E → E),
      Measurable F → P.map F = μ → (∀ j, Measurable (G j)) →
      Tendsto (fun j => ∫ z, ‖ups μ g (G j z) - ups μ g (F z)‖ ^ 2 ∂P) atTop (𝓝 0) →
        ∀ η > 0, Tendsto (fun j => P.real {z | η < ‖G j z - F z‖}) atTop (𝓝 0)

end Claims
end StatFormal.OTFD.Scale
