import StatFormal.Wave30tx.Statements
import StatFormal.Archive.Wave12c.Statements
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

set_option linter.style.longLine false

/-!
# FROZEN STATEMENTS — wave 31th: trimmed-mmd (jmlr) **v3**, `rem:qdens` in every dimension `d` (the Gaussian kernel on `ℝ^d`)

Printed source: `trimmed-mmd/jmlr/v3/NEW_STATEMENTS.md` at trimmed-mmd commit `d356058` (file section "v3 gap closure (2026-11-12)", subsection
"Wave 31th", G2 `rem:qdens` in dimension `d ≥ 2`, lines 184–210; the binding specification: lines 1–210 of the file, sha256
`311b3b79b12704db129665550b6137172bf8d6d3552e071d0123422157c37cad`; read-only, read 2026-11-12). The working-tree file carries, after line 210
(commit `6fe8200`), an independent second write-up of the same claim (G2, "`rem:qdens` for every `d`"); it agrees with lines 184–210 and
is not used as a specification. The remark is printed in `trimmed-mmd/jmlr/v3/sections/05_trimming.tex:65-71` at trimmed-mmd `78c4665`
(sha256 `f787aecc1a51fe078b1b7ebaa354c518c63c46ccda1e0fb4b2ae21a434e800db`; (Q), (Q′) at `:54-61`), its proof in
`jmlr/v3/appendix/D_trimming.tex:312-335` (sha256 `9962dc6bc571298bbcf410b3f9adf604f1c6f8ac61f17478d5d9efe5cdd6000f`):

> Let `𝒳 = ℝ^d` with the Gaussian kernel, so that `d⋆` is infinitely differentiable and vanishes at infinity. If `t_α ≠ 0`, the level set
> `{d⋆ = t_α}` is nonempty, the gradient of `d⋆` does not vanish on it, and `P` has a Lebesgue density `p` that is continuous near the
> level set and positive on it, then (Q) holds, by the coarea formula (Evans–Gariepy 2015). The same conditions at `u_α` under `Q` give (Q′).

with (Q): "the law of `d⋆(X)` under `P` has, on `[t_α − r_Q, t_α + r_Q]` for some `r_Q > 0`, a density with values in `[c_f, C_f]`, where
`0 < c_f ≤ C_f < ∞`" and (Q′): "the law of `d⋆(Y)` under `Q` has a density at least `c′_f > 0` on `[u_α − r_Q, u_α + r_Q]`, where `u_α` is an
`α`-quantile of `d⋆(Y)`". The printed proof: smoothness and decay of the Gaussian RKHS functions (Steinwart–Christmann 2008, Cor. 4.36,
Thm 4.21, Lemma 4.23), compactness of the band `{|d⋆ − t_α| ≤ |t_α|/2}`, a band `B_η` inside the open set where `∇d⋆ ≠ 0` and `p` is
continuous and positive, the coarea formula for the density `h(t) = ∫_{d⋆=t} p/|∇d⋆| dℋ^{d−1}`, and the flow of `∇d⋆/|∇d⋆|²` for its
continuity and positivity. Wave 31tc (`StatFormal.Wave31tc`) certified `d = 1` (`qdens_univariate`, `qdens_formula`, `qdens_Q_Qprime`) and
`level_compact` in every dimension, with the smoothness and decay of `d⋆` as hypotheses.

The binding target (`NEW_STATEMENTS.md:194-201`): `d ≥ 1`, `𝒳 = ℝ^d` (`EuclideanSpace ℝ (Fin d)`, Borel σ-algebra, Lebesgue measure), `k` the
Gaussian kernel `exp(−‖x−y‖²/(2σ²))`, `σ > 0`, and `ℋ` its RKHS with the frozen encoding of (A1)–(A3) of the earlier waves; `P`, `Q` probability
measures, `α ∈ (0,1)` with `D_α(P,Q) > 0`, `d⋆ ∈ ℋ` the element of minimal norm of `𝒞_α(P) − 𝒞_α(Q)`, `d⋆(x) = ⟨d⋆, φ x⟩`, `t_α` a
`(1−α)`-quantile of `d⋆(X)` under `P`, `u_α` an `α`-quantile of `d⋆(Y)` under `Q`. (Q): if `t_α ≠ 0`, `L = {d⋆ = t_α} ≠ ∅`, `∇d⋆ ≠ 0` on `L`, and
`P` has a Lebesgue density `p` continuous on an open neighbourhood of `L` and positive on `L`, then there are `r_Q > 0` and `0 < c_f ≤ C_f < ∞`
such that the law of `d⋆(X)` restricted to `[t_α − r_Q, t_α + r_Q]` has a Lebesgue density with values in `[c_f, C_f]`. (Q′): the same
hypotheses at `u_α` under `Q` give a density of the law of `d⋆(Y)` bounded below by some `c′_f > 0` on `[u_α − r_Q, u_α + r_Q]`, and `r_Q` can
be taken common to (Q) and (Q′). "The formal statement must specialise to the certified `d = 1` statements of Wave 31tc." Admissible
inputs there: the Gaussian-RKHS facts (smoothness at least `C¹`, vanishing at infinity) proved or declared as bridge hypotheses; the coarea
formula as a declared bridge, unless avoided by local straightening; NOT admissible as a bridge: the continuity or positivity of the
level-set density `h`, or anything that restates (Q).

Covered here (5 claims, label `rem:qdens (v3, every d)`):
* `qdens_euclid` — the geometric core, in every dimension `d`, with no kernel: a continuously differentiable `f : ℝ^d → ℝ` tending to `0` at
  infinity, `t ≠ 0`, `L = {f = t} ≠ ∅`, `∇f ≠ 0` on `L`, `p` continuous on an open `U ⊇ L` and positive on `L`: for some `r > 0`, `0 < c ≤ C`,
  the law of `f(X)`, `X ~ p·λ`, has on `[t − r, t + r]` a density with values in `[c, C]` (`QDensity`). For `d = 1` it is equivalent to the frozen
  `Wave31tc.Claims.qdens_univariate` through `x ↦ x 0 : ℝ^1 ≃ ℝ` (an isometry carrying `volume` to `volume`, the filter `comap ‖·‖ atTop` to
  `atBot ⊔ atTop`, and `fderiv ℝ f x ≠ 0` to `deriv h (x 0) ≠ 0`).
* `gaussian_regular` — the Gaussian-RKHS facts of the printed proof, at the level the argument uses: if `φ : ℝ^d → ℋ` has the Gaussian Gram
  function `⟨φ x, φ y⟩ = exp(−‖x−y‖²/(2σ²))` into a real Hilbert space, every `f ∈ ℋ` gives `x ↦ ⟨f, φ x⟩` continuously differentiable (`C¹`) and
  vanishing at infinity. Declared deviation: `C¹` instead of `C^∞` ("infinitely differentiable", Steinwart–Christmann Cor. 4.36); only `C¹`
  is used by the argument and certified here.
* `qdens_gauss_Q` — "(Q) holds": the remark for `P`, in the Gaussian setting with the standing hypotheses of §5.
* `qdens_gauss_Qprime` — "the same conditions at `u_α` under `Q` give (Q′)".
* `qdens_gauss_Q_Qprime` — (Q) and (Q′) together with one common half-width `r_Q`, as (Q′) is printed with the `r_Q` of (Q).

Encodings (see the card `certify/cards/wave31th.md`):
* `𝒳 = ℝ^d` is `EuclideanSpace ℝ (Fin d)` with its Borel σ-algebra and `volume` (Lebesgue measure). `d` is arbitrary (`d = 0` is vacuous: the
  derivative of a function on a point is `0`, so `∇f ≠ 0` on a nonempty level set fails).
* The Gaussian kernel: `φ : ℝ^d → ℋ` into a complete separable real Hilbert space with `⟨φ x, φ y⟩ = exp(−‖x−y‖²/(2σ²))`, `σ > 0` (the encoding of
  `Wave30tx.nearcontact_b`; the RKHS is the closed span of `φ(ℝ^d)`, isometric to the printed one; generalisation: any such `ℋ`). (A1)–(A2): `φ`
  strongly measurable with `‖φ x‖ ≤ κ` (some `κ`), `ℋ` complete and separable. (A3) (`Characteristic φ`) is NOT assumed: the remark does not use it
  (generalisation; the Gaussian kernel is characteristic anyway). `gaussian_regular` needs only completeness of `ℋ` (no separability, measurability or
  bound on `φ`: they follow from the Gram identity); the `qdens_gauss_*` claims take the printed (A1)–(A2), and `‖φ x‖ = 1`, so `κ ≥ 1` is automatic.
* `D_α(P,Q)` is `Dpop φ P Q α`; `d⋆` is any `dstar` with `IsMinNorm (region φ α P − region φ α Q) dstar` (the printed definition: the element of
  minimal norm of `𝒞_α(P) − 𝒞_α(Q)`); `d⋆(x) = witFn dstar φ x = ⟨d⋆, φ x⟩`. "`t_α` is a `(1−α)`-quantile of `d⋆(X)` under `P`" is
  `IsQuantile P (witFn dstar φ) (1−α) tα` (`R(f < t) ≤ p ≤ R(f ≤ t)`); likewise `u_α` for `Q` at level `α`. (Q), (Q′) are `Wave12c.QDensity` and
  `Wave12c.QDensityLower` (the forms consumed by the frozen `Wave30tx` and `Wave31ta.cor_trimrate_v2` claims).
* "`P` has a Lebesgue density `p`": `P = volume.withDensity (fun x => ENNReal.ofReal (p x))` with `p : ℝ^d → ℝ` (negative values count as `0`; only
  `ofReal ∘ p` enters). "continuous on a neighbourhood of `L`": an open `U ⊇ L` with `ContinuousOn p U` (the claims quantify over `U`).
* "the gradient of `d⋆` does not vanish": `fderiv ℝ d⋆ x ≠ 0` (a nonzero continuous linear functional, i.e. `∇d⋆(x) ≠ 0`); `d⋆` is `C¹`
  (`gaussian_regular`), so `fderiv` is the genuine derivative. "vanishes at infinity": `Tendsto f (comap (‖·‖) atTop) (𝓝 0)` (the filter of `‖x‖ → ∞`).
* "the law of `d⋆(X)` has on `[t_α − r_Q, t_α + r_Q]` a density with values in `[c_f, C_f]`" is `QDensity P d⋆ t_α r_Q c_f C_f` (a measurable `g`
  with `c_f ≤ g ≤ C_f` on the window and `P(d⋆⁻¹A) = ∫⁻_A g` for every Borel `A` in the window).
* The coarea formula is NOT used and not declared as a bridge: (Q) is stated as the existence of a density with values in `[c_f, C_f]`, without
  identifying it with `h(t) = ∫_{d⋆=t} p/|∇d⋆| dℋ^{d−1}` (intended route, not part of the statement: local straightening, implicit function theorem
  plus change of variables on finitely many charts covering the compact `L`). The Hausdorff-measure formula for `h` and the continuity of `h` (the
  printed flow argument) are not claimed.
* `ContDiff ℝ 1` is `C¹` (in this Mathlib `ContDiff ℝ ⊤` would be analyticity; `C^∞` is `ContDiff ℝ ∞`, which is not claimed).
* Junk values: at a point where `f` is not differentiable `fderiv ℝ f x = 0`, so `fderiv ℝ f x ≠ 0` can only exclude such `f` (and the witnesses of
  the claims are `C¹`); `volume.withDensity (ofReal ∘ p)` is read only on measurable subsets of `U` (`f⁻¹[t−r,t+r] ⊆ U` for small `r`), where `p` is
  continuous, off `U` `p` may be arbitrary; `QDensity` is the frozen predicate; `IsQuantile` uses `Measure.real` of probability measures (no
  `toReal ⊤`); `Dpop` is a `sInf` of a nonempty set bounded below by `0` for `α ∈ (0,1)`.
* Non-vacuity (pre-freeze critic): `qdens_euclid` at `d = 2`, `f = exp(−‖x‖²)`, `t = 1/2`, `p` the standard normal density, `U = ℝ²` satisfies every
  hypothesis (proved in Lean by the critic in scratch). The hypotheses of the `qdens_gauss_*` claims are met, by a numerical quadratic-program solve, for
  `d = 1`, `σ = 1`, `P = N(−2,1)`, `Q = N(2,1)`, `α = 0.2`: `D_α ≈ 0.968`, `t_α = −u_α ≈ 0.613`, level set `{−2.32, −1.81}` with `d⋆′ ≈ +0.061, −0.066`.
* Generalisations (declared): `t_α`, `u_α` need not be quantiles for the conclusions (the hypotheses `IsQuantile`, `0 < D_α`, `IsMinNorm` are
  assumed as printed, though the proofs do not use them); (A3) not assumed; `κ` and the separability are inessential.

FROZEN 2026-11-12 before any proof, after an independent critic's pre-freeze review (5 claims: 4 ACCEPT, 1 ACCEPT-WITH-NOTE (`gaussian_regular`: `C¹`
not `C^∞`, to be said on the card), none false, verdict READY TO FREEZE; applied: the source wording, the `d = 1` equivalence wording, the
encoding notes, the non-vacuity bullet; recorded on the card). Hashed in `certify/statements.lock` (with its imports); AI agents must not edit
this file.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace Pointwise

namespace StatFormal.Wave31th

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional
  StatFormal.TrimmedMMD.Projection StatFormal.Wave12c StatFormal.Wave30tx

namespace Claims

/-- `rem:qdens (v3, every d)`, the geometric core with no kernel, in every dimension `d`: let `f : ℝ^d → ℝ` be continuously differentiable with
`f(x) → 0` as `‖x‖ → ∞`, `t ≠ 0`, `L = {f = t}` nonempty, `∇f ≠ 0` on `L`, and let `X` have law `P = p·λ` with `p` continuous on an open `U ⊇ L`
and positive on `L`. Then there are `r > 0` and `0 < c ≤ C` such that the law of `f(X)` has, on `[t − r, t + r]`, a density with values in
`[c, C]` (`QDensity P f t r c C`). For `d = 1` this is equivalent to `Wave31tc.Claims.qdens_univariate` (through `x ↦ x 0 : ℝ^1 ≃ ℝ`). -/
def qdens_euclid : Prop :=
  ∀ (d : ℕ) (f p : EuclideanSpace ℝ (Fin d) → ℝ) (U : Set (EuclideanSpace ℝ (Fin d))) (t : ℝ),
    ContDiff ℝ 1 f → Tendsto f (comap (fun x => ‖x‖) atTop) (𝓝 0) →
    t ≠ 0 → (∃ x, f x = t) → (∀ x, f x = t → fderiv ℝ f x ≠ 0) →
    IsOpen U → {x | f x = t} ⊆ U → ContinuousOn p U → (∀ x, f x = t → 0 < p x) →
      ∃ r c C : ℝ, 0 < r ∧ 0 < c ∧ c ≤ C ∧
        QDensity (volume.withDensity fun x => ENNReal.ofReal (p x)) f t r c C

/-- The Gaussian-RKHS facts of the printed proof (Steinwart–Christmann 2008, Cor. 4.36, Thm 4.21, Lemma 4.23), at the level the argument uses: if
`φ : ℝ^d → ℋ` into a real Hilbert space has the Gaussian Gram function `⟨φ x, φ y⟩ = exp(−‖x−y‖²/(2σ²))`, `σ > 0`, then for every `f ∈ ℋ` the
function `x ↦ ⟨f, φ x⟩` is continuously differentiable and tends to `0` as `‖x‖ → ∞`. (Deviation from the printed "infinitely differentiable":
`C¹` is certified, which is all the argument uses.) -/
def gaussian_regular : Prop :=
  ∀ (d : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : EuclideanSpace ℝ (Fin d) → H) (σ : ℝ),
    0 < σ → (∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-‖x - y‖ ^ 2 / (2 * σ ^ 2))) →
    ∀ f : H, ContDiff ℝ 1 (witFn f φ) ∧ Tendsto (witFn f φ) (comap (fun x => ‖x‖) atTop) (𝓝 0)

/-- `rem:qdens (v3, every d)`, "(Q) holds": `𝒳 = ℝ^d` with the Gaussian kernel (feature map `φ` into `ℋ`, `⟨φ x, φ y⟩ = exp(−‖x−y‖²/(2σ²))`), (A1)–(A2),
`P`, `Q` probability measures, `α ∈ (0,1)` with `D_α(P,Q) > 0`, `d⋆` the element of minimal norm of `𝒞_α(P) − 𝒞_α(Q)`, `t_α` a `(1−α)`-quantile of
`d⋆(X)` under `P`. If `t_α ≠ 0`, `L = {d⋆ = t_α} ≠ ∅`, `∇d⋆ ≠ 0` on `L`, and `P = p·λ` with `p` continuous on an open `U ⊇ L` and positive on `L`,
then there are `r_Q > 0` and `0 < c_f ≤ C_f` with `QDensity P d⋆ t_α r_Q c_f C_f` (the law of `d⋆(X)` has on `[t_α − r_Q, t_α + r_Q]` a density with
values in `[c_f, C_f]`). -/
def qdens_gauss_Q : Prop :=
  ∀ (d : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (φ : EuclideanSpace ℝ (Fin d) → H) (σ κ α : ℝ) (P Q : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (dstar : H) (p : EuclideanSpace ℝ (Fin d) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin d))) (tα : ℝ),
    0 < σ → (∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-‖x - y‖ ^ 2 / (2 * σ ^ 2))) →
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) →
    0 < α → α < 1 → 0 < Dpop φ P Q α → IsMinNorm (region φ α P - region φ α Q) dstar →
    IsQuantile P (witFn dstar φ) (1 - α) tα →
    P = volume.withDensity (fun x => ENNReal.ofReal (p x)) →
    tα ≠ 0 → (∃ x, witFn dstar φ x = tα) → (∀ x, witFn dstar φ x = tα → fderiv ℝ (witFn dstar φ) x ≠ 0) →
    IsOpen U → {x | witFn dstar φ x = tα} ⊆ U → ContinuousOn p U → (∀ x, witFn dstar φ x = tα → 0 < p x) →
      ∃ rQ cf Cf : ℝ, 0 < rQ ∧ 0 < cf ∧ cf ≤ Cf ∧ QDensity P (witFn dstar φ) tα rQ cf Cf

/-- `rem:qdens (v3, every d)`, "the same conditions at `u_α` under `Q` give (Q′)": in the same setting, with `u_α` an `α`-quantile of `d⋆(Y)` under
`Q`: if `u_α ≠ 0`, `{d⋆ = u_α} ≠ ∅`, `∇d⋆ ≠ 0` there, and `Q = q·λ` with `q` continuous on an open `V ⊇ {d⋆ = u_α}` and positive on it, then there
are `r_Q > 0` and `c′_f > 0` with `QDensityLower Q d⋆ u_α r_Q c′_f` (the law of `d⋆(Y)` has on `[u_α − r_Q, u_α + r_Q]` a density at least `c′_f`). -/
def qdens_gauss_Qprime : Prop :=
  ∀ (d : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (φ : EuclideanSpace ℝ (Fin d) → H) (σ κ α : ℝ) (P Q : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (dstar : H) (q : EuclideanSpace ℝ (Fin d) → ℝ)
    (V : Set (EuclideanSpace ℝ (Fin d))) (uα : ℝ),
    0 < σ → (∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-‖x - y‖ ^ 2 / (2 * σ ^ 2))) →
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) →
    0 < α → α < 1 → 0 < Dpop φ P Q α → IsMinNorm (region φ α P - region φ α Q) dstar →
    IsQuantile Q (witFn dstar φ) α uα →
    Q = volume.withDensity (fun y => ENNReal.ofReal (q y)) →
    uα ≠ 0 → (∃ y, witFn dstar φ y = uα) → (∀ y, witFn dstar φ y = uα → fderiv ℝ (witFn dstar φ) y ≠ 0) →
    IsOpen V → {y | witFn dstar φ y = uα} ⊆ V → ContinuousOn q V → (∀ y, witFn dstar φ y = uα → 0 < q y) →
      ∃ rQ cf' : ℝ, 0 < rQ ∧ 0 < cf' ∧ QDensityLower Q (witFn dstar φ) uα rQ cf'

/-- `rem:qdens (v3, every d)`, the remark's conclusion with one common half-width: in the setting of `qdens_gauss_Q`, if the conditions hold at `t_α`
under `P` and at `u_α` under `Q`, then there are `r_Q > 0`, `0 < c_f ≤ C_f` and `c′_f > 0` with `QDensity P d⋆ t_α r_Q c_f C_f` and
`QDensityLower Q d⋆ u_α r_Q c′_f` — one `r_Q` for (Q) and (Q′), as (Q′) is printed with the `r_Q` of (Q). -/
def qdens_gauss_Q_Qprime : Prop :=
  ∀ (d : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (φ : EuclideanSpace ℝ (Fin d) → H) (σ κ α : ℝ) (P Q : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (dstar : H) (p q : EuclideanSpace ℝ (Fin d) → ℝ)
    (U V : Set (EuclideanSpace ℝ (Fin d))) (tα uα : ℝ),
    0 < σ → (∀ x y, ⟪φ x, φ y⟫_ℝ = Real.exp (-‖x - y‖ ^ 2 / (2 * σ ^ 2))) →
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) →
    0 < α → α < 1 → 0 < Dpop φ P Q α → IsMinNorm (region φ α P - region φ α Q) dstar →
    IsQuantile P (witFn dstar φ) (1 - α) tα → IsQuantile Q (witFn dstar φ) α uα →
    P = volume.withDensity (fun x => ENNReal.ofReal (p x)) →
    Q = volume.withDensity (fun y => ENNReal.ofReal (q y)) →
    tα ≠ 0 → (∃ x, witFn dstar φ x = tα) → (∀ x, witFn dstar φ x = tα → fderiv ℝ (witFn dstar φ) x ≠ 0) →
    IsOpen U → {x | witFn dstar φ x = tα} ⊆ U → ContinuousOn p U → (∀ x, witFn dstar φ x = tα → 0 < p x) →
    uα ≠ 0 → (∃ y, witFn dstar φ y = uα) → (∀ y, witFn dstar φ y = uα → fderiv ℝ (witFn dstar φ) y ≠ 0) →
    IsOpen V → {y | witFn dstar φ y = uα} ⊆ V → ContinuousOn q V → (∀ y, witFn dstar φ y = uα → 0 < q y) →
      ∃ rQ cf Cf cf' : ℝ, 0 < rQ ∧ 0 < cf ∧ cf ≤ Cf ∧ 0 < cf' ∧
        QDensity P (witFn dstar φ) tα rQ cf Cf ∧ QDensityLower Q (witFn dstar φ) uα rQ cf'

end Claims
end StatFormal.Wave31th
