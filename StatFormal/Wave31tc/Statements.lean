import StatFormal.Archive.Wave12c.Statements
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 31tc: trimmed-mmd (jmlr) **v3**, `rem:qdens` (when the quantile-density condition (Q) holds)

Printed source: `trimmed-mmd/jmlr/v3/NEW_STATEMENTS.md`, section `rem:qdens` (frozen by the author 2026-11-12; read-only, read
2026-11-12, sha256 `6b4825f20f0253ee1dfff276ed801cfcbb906e5bafca87a16106b2ce3557c238`; trimmed-mmd master `d5cdddb`, `jmlr/v3/`
untracked). The remark is also printed in the v3 tex, `jmlr/v3/sections/05_trimming.tex:66-78` (sha256
`3fa3cba15999bc2ce1e115c182c1d56c4d1d26dcd6db97f657fd432490460040`; same content, worded "continuous near the level set", with the
`d = 1` sentence "the finite sum of `p(x)/|d⋆′(x)|` over the solutions of `d⋆(x) = t`"), proof at
`jmlr/v3/appendix/D_trimming.tex:312-333` (sha256 `291e0ac890c01ebf921e8c617fc97b7357375f90b9f9b3a8482803a547b6ea7c`). The remark as
frozen in NEW_STATEMENTS.md (main text §5 after (Q), (Q′), derivation in Appendix D):

> Let `𝒳 = ℝ^d` with the Gaussian kernel, fix `α ∈ (0,1)` with `D_α(P,Q) > 0`, and let `d⋆, t_α` be as in (Q). The function
> `d⋆ ∈ ℋ` is infinitely differentiable and vanishes at infinity. Suppose `t_α ≠ 0`, the level set `L = {x : d⋆(x) = t_α}` is
> nonempty, `∇d⋆` does not vanish on `L`, and `P` has a Lebesgue density `p` that is continuous on a neighbourhood of `L` and
> positive on `L`. Then (Q) holds: `L` is compact, and near `t_α` the law of `d⋆(X)` has the continuous positive density
> `t ↦ ∫_{d⋆=t} p/|∇d⋆| dℋ^{d−1}` (coarea formula). The same conditions at the `α`-quantile `u_α` of `d⋆(Y)` under `Q` give (Q′).

with the frozen formal target (univariate core, `d = 1`):

> let `h : ℝ → ℝ` be continuously differentiable with `h(x) → 0` as `|x| → ∞`, let `t ≠ 0` with `L = {h = t}` nonempty and `h′ ≠ 0`
> on `L`, and let `X` have a Lebesgue density `p` continuous on a neighbourhood of `L` and positive on `L`. Then there are `r > 0` and
> `0 < c ≤ C < ∞` such that the law of `h(X)`, restricted to `[t−r, t+r]`, has a density with respect to Lebesgue measure with values
> in `[c, C]`. (`L` is finite; the density there is `s ↦ Σ_{x : h(x) = s} p(x)/|h′(x)|`.)

Covered here (4 claims, label `rem:qdens (v3)`):
* `level_compact` — "`L` is compact", in every dimension `d`: a continuous `h : ℝ^d → ℝ` with `h(x) → 0` as `‖x‖ → ∞` has compact
  level sets `{h = t}` for every `t ≠ 0`.
* `qdens_univariate` — the frozen univariate target, with its conclusion in the paper's form (Q) (`Wave12c.QDensity`, the encoding of
  (Q) used by the frozen `Wave30tx`/`Wave31ta` claims).
* `qdens_formula` — the same with the parenthetical made explicit and the printed "continuous positive density": `L` is finite, `h′ ≠ 0`
  on `h⁻¹[t−r,t+r]`, every level `s ∈ [t−r,t+r]` has finitely many preimages, and the law of `h(X)` on `[t−r,t+r]` has the density
  `levelDens h p s = Σ_{x : h(x) = s} p(x)/|h′(x)|`, continuous on `[t−r,t+r]` with values in `[c, C]`, `c > 0`.
* `qdens_Q_Qprime` — the remark's conclusion "(Q) holds … the same conditions at `u_α` give (Q′)" for `𝒳 = ℝ`, the witness written
  `d⋆(x) = ⟨d⋆, φ(x)⟩_𝓗` (`Wave12c.witFn`) as in the frozen (Q), (Q′) hypotheses of `Wave31ta.cor_trimrate_v2`, with one common
  half-width `r_Q` for both conditions.

Encodings (see the card `certify/cards/wave31tc.md`):
* "`X` has a Lebesgue density `p`": the law of `X` is `P = volume.withDensity (fun x => ENNReal.ofReal (p x))` on `ℝ`, `p : ℝ → ℝ`;
  "the law of `h(X)` on `[t−r,t+r]` has a density `g` with values in `[c,C]`" is `QDensity P h t r c C` (`P(h⁻¹A) = ∫⁻_A g` for every
  Borel `A ⊆ [t−r,t+r]`, `g` measurable, `c ≤ g ≤ C` there). Generalisations: `P` need not be a probability (or finite) measure; `p`
  need not be integrable, measurable outside `U`, or nonnegative off `L` (only `ENNReal.ofReal ∘ p` enters, so negative values count
  as `0`).
* "continuous on a neighbourhood of `L`": an open `U ⊇ L` with `ContinuousOn p U` (the claims quantify over `U`).
* "continuously differentiable": `ContDiff ℝ 1 h`; `h′ = deriv h` (no junk: `h` is differentiable everywhere).
* "`h(x) → 0` as `|x| → ∞`": `Tendsto h atTop (𝓝 0)` and `Tendsto h atBot (𝓝 0)` (`d = 1`); for `ℝ^d` (`EuclideanSpace ℝ (Fin d)`),
  `Tendsto h (comap (‖·‖) atTop) (𝓝 0)` (this filter is `cobounded` = `cocompact`; for `d = 0` it is `⊥` and the claim is trivial).
* Conditionalisation (declared): the Gaussian-kernel facts "`d⋆` is infinitely differentiable and vanishes at infinity" are hypotheses
  (`C¹` and decay of `x ↦ ⟨d⋆, φ(x)⟩` are all the argument uses), not proved; the quantile property of `t_α`, `u_α` is not used (any
  levels `t_α, u_α ≠ 0` at which the level-set conditions hold), nor is `D_α(P,Q) > 0`, nor that `dstar` is the population witness or
  `H` an RKHS (any `dstar ∈ H`, `φ : ℝ → H`). Specialisation (declared): the density statements are for `d = 1` (the author's frozen
  formal target; a `d`-dimensional (Q) statement could be written, but its proof needs the coarea formula, which Mathlib lacks); only
  "`L` is compact" is stated in every dimension.
* Junk values: `p x / |deriv h x|` is used only at points of `h⁻¹[t−r,t+r]`, where `qdens_formula` asserts `deriv h ≠ 0`; the `finsum`
  in `levelDens` is used only at levels whose preimage is asserted finite (`∑ᶠ` over an infinite set would be `0`);
  `ENNReal.ofReal (levelDens h p s)` is used only for `s ∈ [t−r,t+r]`, where `levelDens ≥ c > 0` is asserted.

FROZEN 2026-11-12 before any proof, after an independent critic's pre-freeze review (4 claims: 3 ACCEPT, 1 ACCEPT-WITH-NOTE, none false,
verdict READY TO FREEZE; Monte Carlo on `levelDens` in four designs; applied: the printed-source paragraph (the remark is now in the v3
tex), the generalisation and junk-value wording, the `comap` filter note, the completeness of the declared conditionalisations, and the
`qdens_Q_Qprime` docstring). Hashed in `certify/statements.lock` (with its imports); AI agents must not edit this file.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave31tc

open StatFormal.Wave12c

/-- The density formula of `rem:qdens` for `d = 1`: `levelDens h p s = Σ_{x : h(x) = s} p(x)/|h′(x)|` (a `finsum`; the claims use it
only at levels `s` whose preimage `{x | h x = s}` is finite and on which `h′ ≠ 0`, both asserted where it is used). -/
def levelDens (h p : ℝ → ℝ) (s : ℝ) : ℝ := ∑ᶠ x ∈ {x | h x = s}, p x / |deriv h x|

namespace Claims

/-- `rem:qdens (v3)`, "`L` is compact", in every dimension: if `h : ℝ^d → ℝ` is continuous and `h(x) → 0` as `‖x‖ → ∞`, then for every
`t ≠ 0` the level set `{x : h(x) = t}` is compact. -/
def level_compact : Prop :=
  ∀ (d : ℕ) (h : EuclideanSpace ℝ (Fin d) → ℝ) (t : ℝ),
    Continuous h → Tendsto h (comap (fun x => ‖x‖) atTop) (𝓝 0) → t ≠ 0 → IsCompact {x | h x = t}

/-- `rem:qdens (v3)`, the frozen univariate target (`d = 1`), in the form (Q): let `h : ℝ → ℝ` be continuously differentiable with
`h(x) → 0` as `x → ±∞`, `t ≠ 0`, `L = {h = t}` nonempty, `h′ ≠ 0` on `L`, and let `X` have law `P = p·λ` with `p` continuous on an
open `U ⊇ L` and positive on `L`. Then there are `r > 0` and `0 < c ≤ C` such that the law of `h(X)` has, on `[t−r, t+r]`, a density
with values in `[c, C]` (`QDensity P h t r c C`). -/
def qdens_univariate : Prop :=
  ∀ (h p : ℝ → ℝ) (U : Set ℝ) (t : ℝ),
    ContDiff ℝ 1 h → Tendsto h atTop (𝓝 0) → Tendsto h atBot (𝓝 0) →
    t ≠ 0 → (∃ x, h x = t) → (∀ x, h x = t → deriv h x ≠ 0) →
    IsOpen U → {x | h x = t} ⊆ U → ContinuousOn p U → (∀ x, h x = t → 0 < p x) →
      ∃ r c C : ℝ, 0 < r ∧ 0 < c ∧ c ≤ C ∧
        QDensity (volume.withDensity fun x => ENNReal.ofReal (p x)) h t r c C

/-- `rem:qdens (v3)`, the univariate target with the explicit density: under the hypotheses of `qdens_univariate`, `L` is finite, and
there are `r > 0` and `0 < c ≤ C` such that `h′ ≠ 0` on `h⁻¹[t−r, t+r]`, every `s ∈ [t−r, t+r]` has finitely many preimages, the
function `s ↦ Σ_{x : h(x) = s} p(x)/|h′(x)|` (`levelDens h p`) is continuous on `[t−r, t+r]` with values in `[c, C]`, and it is the
density of the law of `h(X)` there: `P(h(X) ∈ A) = ∫_A levelDens h p` for every Borel `A ⊆ [t−r, t+r]`. -/
def qdens_formula : Prop :=
  ∀ (h p : ℝ → ℝ) (U : Set ℝ) (t : ℝ),
    ContDiff ℝ 1 h → Tendsto h atTop (𝓝 0) → Tendsto h atBot (𝓝 0) →
    t ≠ 0 → (∃ x, h x = t) → (∀ x, h x = t → deriv h x ≠ 0) →
    IsOpen U → {x | h x = t} ⊆ U → ContinuousOn p U → (∀ x, h x = t → 0 < p x) →
      {x | h x = t}.Finite ∧
      ∃ r c C : ℝ, 0 < r ∧ 0 < c ∧ c ≤ C ∧
        (∀ x, h x ∈ Icc (t - r) (t + r) → deriv h x ≠ 0) ∧
        (∀ s ∈ Icc (t - r) (t + r), {x | h x = s}.Finite ∧ c ≤ levelDens h p s ∧ levelDens h p s ≤ C) ∧
        ContinuousOn (levelDens h p) (Icc (t - r) (t + r)) ∧
        ∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc (t - r) (t + r) →
          (volume.withDensity fun x => ENNReal.ofReal (p x)) (h ⁻¹' A) = ∫⁻ s in A, ENNReal.ofReal (levelDens h p s)

/-- `rem:qdens (v3)`, the conclusion in the paper's notation, `𝒳 = ℝ`: for a witness `d⋆(x) = ⟨d⋆, φ(x)⟩_𝓗` that is continuously
differentiable and tends to `0` at `±∞`, if `P = p·λ` satisfies the level-set conditions at `t_α ≠ 0` and `Q = q·λ` satisfies them at
`u_α ≠ 0`, then (Q) and (Q′) hold with one common half-width: there are `r_Q > 0`, `0 < c_f ≤ C_f` and `c'_f > 0` with
`QDensity P d⋆ t_α r_Q c_f C_f` and `QDensityLower Q d⋆ u_α r_Q c'_f` (the forms in which (Q), (Q′) enter the frozen
`Wave31ta.cor_trimrate_v2`; its other hypotheses — probability measures, the quantile property, `ρ` before `N` — are not part of this
claim). -/
def qdens_Q_Qprime : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (φ : ℝ → H) (dstar : H) (p q : ℝ → ℝ) (U V : Set ℝ) (tα uα : ℝ),
    ContDiff ℝ 1 (witFn dstar φ) → Tendsto (witFn dstar φ) atTop (𝓝 0) → Tendsto (witFn dstar φ) atBot (𝓝 0) →
    tα ≠ 0 → (∃ x, witFn dstar φ x = tα) → (∀ x, witFn dstar φ x = tα → deriv (witFn dstar φ) x ≠ 0) →
    IsOpen U → {x | witFn dstar φ x = tα} ⊆ U → ContinuousOn p U → (∀ x, witFn dstar φ x = tα → 0 < p x) →
    uα ≠ 0 → (∃ y, witFn dstar φ y = uα) → (∀ y, witFn dstar φ y = uα → deriv (witFn dstar φ) y ≠ 0) →
    IsOpen V → {y | witFn dstar φ y = uα} ⊆ V → ContinuousOn q V → (∀ y, witFn dstar φ y = uα → 0 < q y) →
      ∃ rQ cf Cf cf' : ℝ, 0 < rQ ∧ 0 < cf ∧ cf ≤ Cf ∧ 0 < cf' ∧
        QDensity (volume.withDensity fun x => ENNReal.ofReal (p x)) (witFn dstar φ) tα rQ cf Cf ∧
        QDensityLower (volume.withDensity fun y => ENNReal.ofReal (q y)) (witFn dstar φ) uα rQ cf'

end Claims
end StatFormal.Wave31tc
