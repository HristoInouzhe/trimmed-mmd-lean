import StatFormal.Archive.OTFD.Wave6b.Statements
import StatFormal.Archive.OTFD.Wave5a.Statements
import Mathlib.Probability.ConditionalProbability
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# FROZEN STATEMENTS — otfd wave 12a (QUEUE rows 101–102): R `thm:entropic` (with the unconditional
# `thm:region-breakdown`), R `thm:peaked-cube` (with `lem:spike`)

Sources (verbatim in `lean-formalisation/inventory/extracted/otfd-R_robustness.md`; current text after the
2026-10-14 corrections; paths below are under `otfd/papers/R_robustness/sections/`):
* `thm:entropic` (`s4_regions.tex:42-63`), proof `appendix_b.tex:3-49` (`eq:ratio2`; (a) mass argument and the
  `φ(x) = x min{1, Ce^{−tx/ε}}` bound; (b) co-located far points, the repaired version using `ε₋`), with the
  setting `s4_regions.tex:25-40` (`eq:mass`, `eq:ratio`), `eq:oos` (`s2_setting.tex:25-28`), `def:bp`
  (`s2_setting.tex:53-58`), `H_{t,D}`, `d^±` (`s2_setting.tex:62-71`).
* `thm:region-breakdown` (`s4_regions.tex:75-83`, proof `:85-93`), only to make the frozen Wave 6b claims
  unconditional.
* `thm:peaked-cube` (`s6_references.tex:121-136`), proof `appendix_b.tex:97-126`, with `lem:spike`
  (`s6_references.tex:104-109`, proof `:111-119`), `def:beta` (`s3_infinite.tex:112-117`) and
  `prop:depth-regions` (`s5_families.tex:47-56`).
Reuses the frozen `OTFDR/Statements.lean` (`piCond`, `Qhat`), `OTFDR/Lift/Statements.lean` (`Contam`, `BP`),
`OTFD/Wave1/Statements.lean` (`HtD`, `tukeyDepth`, `regionDepth`), `OTFD/Wave5a/Statements.lean` (`betaStar`) and
`OTFD/Wave6b/Statements.lean` (`dMinus`, `halfMass`, `IsEntPot`, `entBound`, `EntropicA`, `EntropicB`,
`EntSetting`, `regionSup`, `betaPlus`), imported, not copied.

Covered:
* `thm:entropic` (a): `entropic_weight` (`π(k|u₀) ≤ min{1, (n/κ)e^{−(t‖z_k‖−DB)/ε}}` for every replaced `k`),
  `entropic_displacement` (`EntSetting ⇒` the frozen `EntropicA`, i.e. `‖Q̂(u₀)‖ ≤ B + ℓ(DB+ε log(n/κ)+ε)/t`),
  `entropic_bp_lower` (`BP(Q̂(u₀)) ≥ d⁺(u₀;ν)`).
* `thm:entropic` (b): `entropic_unbounded` (`EntSetting ⇒` the frozen `EntropicB`, `n ≥ 1`),
  `entropic_bp_upper` (`BP(Q̂(u₀)) ≤ d⁻(u₀;ν) + 1/n`).
* `thm:entropic`, closing sentences: `dplus_eq_dminus` (`d⁺ = d⁻` for **every** measure: the optional sharpening of
  review m4), `entropic_ac` (`ν ≪ Leb ⇒ d⁺ = d⁻ = TD`); the data-driven temperature: `entropic_displacement_data`
  ((a) with `ε(Z̃) ≤ ε₊` on `𝔠_ℓ`, bound at `ε₊`), `entropic_unbounded_data` ((b) with `ε(Z̃) ≥ ε₋ > 0` on `𝔠_ℓ`),
  `entropic_bp_data` (`d⁺ ≤ BP ≤ d⁻ + 1/n` when `ε(Z̃) ∈ [ε₋, ε₊]` for every sample).
* `thm:region-breakdown` without the `EntropicA`/`EntropicB` hypotheses: `region_bounded_unconditional`,
  `region_unbounded_unconditional` (`n ≥ 1` added), `region_bp_general_unconditional`, `region_bp_unconditional`.
* `lem:spike`: `spike` (`TD(re_k) ≥ ½P(X_k ≥ r)`, `r ≥ 0`), `spike_cross` (`β(CP(r)) ≥ α/2`).
* `thm:peaked-cube`, finite-dimensional part (the truncations `μ_K`): `peaked_prob`, `peaked_support`
  (`μ_K(∏[−1/k,1/k]) = 1`), `peaked_symmetric`, `peaked_atomless` (`K ≥ 1`), `peaked_coherent` (`μ_K` is the
  image of `μ_{K'}`, `K ≤ K'`, under the first-`K` coordinates); `peaked_S_summable` (`S(L₀,a) < ∞`),
  `peaked_Lambda_le` (`Λ_K ≤ K log(1+L₀²K^{2a})`), `peaked_quantile` (the vertices are the coordinate
  `(1−α)`-quantiles), `peaked_cube` (content `≥ p`, robustness `≥ α_K/2`), `peaked_betaStar` (the displayed lower
  bound on `β*_K(p)`), `peaked_rate` (that bound is `≍ 1/(K log K)`), `peaked_betaStar_rate` (one law gives
  `β*_K(p) ≥ c/(K log K)` for all large `K`), `peaked_S_tendsto` (`S → 0` as `L₀ → ∞`), `peaked_cover` (any
  `p₀ < 1` is covered by one `L₀`).

Not covered (declared):
* `thm:entropic`: nothing of the displayed statements. The standing hypothesis `∫‖u‖²dν < ∞` is kept but unused.
  Existence of the entropic potentials (`EntSetting` assumes `fsel Z̃` satisfies `eq:mass` for every sample;
  semi-discrete entropic duality is not formalised).
* `thm:region-breakdown`: the **band** half (as in Wave 6b).
* `thm:peaked-cube`: the law `μ` on the Hilbert space `𝓗` itself (support in the Hilbert cube, atomless, symmetric,
  product, coherent as a law on `𝓗`) and `μ ∈ 𝒫^ℓ(𝓗)` (needs `lem:app-block-Pl`); covered through the family of
  truncations `μ_K` (product of the coordinate laws), which is what every displayed bound uses. The comparison
  sentences after the theorem (numerical exchange rates; "within a factor `log K` of any product").
* `lem:spike`: the convexity of depth regions is not re-proved (frozen, certified Wave 5a
  `depth_regions_closed_convex`).

Encodings (see card):
* `thm:entropic`: as in Wave 6b (`ℝ^K = EuclideanSpace ℝ (Fin K)`; `ℝ≥0∞`-valued depths; `Q̂ = Qhat Z̃ (fsel Z̃) ε`
  with potentials selected by `fsel` and recomputed on every contaminated sample; "replaced" is `Z̃_k ≠ Z_k`;
  `B` is any bound on the unreplaced points, equivalent to the maximum since every bound is increasing in `B`).
  `d⁺(u₀;ν) = sup_{t>0,D} inf_{‖e‖=1} ν(H_{t,D}(e))` is `dPlus` (`D < 0` gives empty sets, harmless in a sup).
  `κ = 1 − ℓ/(nδ)` is `kappa` (positive under `ℓ < nδ`: no junk). The estimator of `BP(Q̂(u₀))` is
  `Z̃ ↦ Qhat Z̃ (fsel Z̃) ε u₀` fed to the frozen `BP`. The data-driven temperature is a selector `εsel` with
  `EntSettingData` (`εsel Z̃ > 0` and `eq:mass` at `εsel Z̃` for every sample); "stays in a compact subset of
  `(0,∞)` over `𝔠_ℓ`" is `ε₋ ≤ εsel ≤ ε₊` on `𝔠_ℓ(𝒵)` (only the side the proof uses is assumed in (a), (b)); in
  `entropic_bp_data` it is assumed on every sample (`𝔠_n(𝒵)` is every sample, and the breakdown point involves
  every `ℓ ≤ n`). `n ≥ 1` in (b): for `n = 0`, `0 · d⁻ = 0 < ℓ` but `Q̂ = 0`, so the frozen `EntropicB` is false
  (the paper has `n ≥ 1` data points); `region_unbounded_unconditional` adds `1 ≤ n` for the same reason.
* `lem:spike`: "independent coordinates, each symmetric" is the law `(⊗_k μ_k)` pushed to `EuclideanSpace`
  (`Measure.pi`, the joint law of independent coordinates), each `μ_k` a probability with `μ_k ∘ (−·)⁻¹ = μ_k`;
  `re_k = EuclideanSpace.single k r`; `½P(X_k ≥ r) = 2⁻¹ μ_k[r,∞)` in `ℝ≥0∞`. `CP(r) = {u : Σ_k |u_k|/r_k ≤ 1}`
  (`crossPoly`) with `r_k > 0`.
* `thm:peaked-cube`: the standard Cauchy law is `Leb.withDensity (1/(π(1+x²)))`; `C^{(L)}` is its conditional
  law given `[−L, L]` (`ProbabilityTheory.cond`); `L_k = L₀k^a` (`Real.rpow`, `k ≥ 1`); the coordinate law of
  `X_k = C_k/(kL_k)` is the image `peakedCoord`; `μ_K = peakedLaw L₀ a K` is the product of the first `K`
  coordinate laws (index `i : Fin K` is `k = i + 1`). `S(L₀,a)` is a `tsum` (`peaked_S_summable` shows it is not
  the junk value of a divergent series); `Λ_K` a finite sum; `α_K = (π/16)(1−p−S)/Λ_K` (`Λ_K > 0` for `K ≥ 1`,
  `L₀ ≥ 1`, so no `x/0`). The upper `α`-quantile of `C^{(L)}` is written in closed form,
  `y = tan((1−2α) arctan L)` (`tcQuantile`), and `peaked_quantile` proves it is the quantile; the vertices are
  `r_k = y_k/(kL_k)` (`peakedVertex`). Contents and robustness are `ℝ≥0∞` (`ENNReal.ofReal` of the real bounds);
  `β*_K(p)` is the frozen `betaStar` at `ofReal p`. `≍` is Mathlib's `=Θ[atTop]` along `K ∈ ℕ`.
  "Coherent" for the truncations: `μ_K` is the image of `μ_{K'}` under the first `K` coordinates.

Critic notes:
* `thm:entropic` holds as printed, at every `n ≥ 1`, `K`, `ε > 0` and every Borel probability `ν` (the second
  moment is never used). The frozen Wave 6b hypotheses `EntropicA`/`EntropicB` are now theorems
  (`entropic_displacement`, `entropic_unbounded`), so `thm:region-breakdown` is unconditional
  (`region_*_unconditional`), except for `n = 0` in the unbounded clause (degenerate, see encodings).
* (a): two facts the printed proof uses tacitly are derived: `ℓ < nδ` forces `δ > 0`, hence `D ≥ t > 0` and an
  unreplaced point (so `B ≥ 0`); the case `z_k = 0` is trivial (`(n/κ)e^{DB/ε} ≥ 1`).
* (b): the printed proof writes `A(u) = ℓπ_k(u)` "for any `k ∈ 𝒪`", i.e. equal weights for co-located points
  (true, but only via `eq:mass`, and not argued); the route avoids it and the division by `C(u)`:
  `C(u₀)A(u) ≤ e^{DB/ε}A(u₀)C(u) ≤ e^{DB/ε}A(u₀)` summed over all pairs, which also covers `ℓ ≥ n` (`C ≡ 0`).
  The repaired `ε₋` version is correct: only a lower bound on the temperature is needed for (b), only an upper
  bound for (a).
* `lem:spike` holds as printed; the route proves the stronger `TD(ce_k) ≥ ½ min{P(X_k ≤ c), P(X_k ≥ c)}` for every
  real `c` without symmetry of `X_k` itself (symmetry of the other coordinates suffices), which handles the
  vertices `−r_ke_k` directly.
* `thm:peaked-cube` holds as printed. The quantile step uses `tan θ = sin/cos` with `sin θ ≤ θ`,
  `cos θ ≥ 1 − θ²/2` for `θ ≤ πα ≤ π/8` instead of the convexity of `tan`; same constant `4α`. `α_K ≤ 1/8`
  holds for all large `K` (`Λ_K ≥ K log 2`), so the bound is not vacuous (`peaked_betaStar_rate`).
* Scope of "`≍ 1/(K log K)`": what is proved (and what the paper claims) is that the **lower bound** is
  `≍ 1/(K log K)`; `β*_K(p)` itself is only bounded below (`peaked_betaStar_rate`). The queue note's
  "coherent law with `β* ≍ 1/(K log K)`" overstates it: the matching upper bound is not claimed (the paper only
  compares with `log(1/p)/(2K)` for products, `thm:rates`(a), a factor `log K` away).
* Critic (2026-10-14): ACCEPT-WITH-NOTE. `EntSetting` is exactly the paper's setting (`eq:mass` = optimality of the
  concave semi-dual; satisfiable). The frozen Wave6b `EntropicB` is false at `n = 0` (checked in Lean), hence `1 ≤ n`
  in `region_unbounded_unconditional`; the paper has `n ≥ 1` implicitly. `dplus_eq_dminus` (every measure) goes
  beyond the paper's `d⁺ ≤ d⁻`. `entropic_bp_data` assumes `[εlo, εhi]` on every sample (stronger than "over `𝔠_ℓ`";
  the paper's `ℓ` is ambiguous). Proof of (b): co-located points get equal weights because `π_k/π_{k'}` is constant in
  `u` and `eq:mass` forces it to be 1 — at most a missing one-line justification (S4). `peaked_rate` (Θ) concerns the
  bound only, as printed; the law on 𝓗 and `𝒫^ℓ(𝓗)` are declared (`peaked_coherent` is the Kolmogorov consistency).
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Asymptotics
open scoped InnerProductSpace ENNReal Topology

namespace StatFormal.OTFD.Wave12a

open StatFormal.OTFDR (piCond Qhat)
open StatFormal.OTFDR.Lift (Contam BP)
open StatFormal.OTFD.Wave1 (HtD tukeyDepth regionDepth)
open StatFormal.OTFD.Wave5a (betaStar)
open StatFormal.OTFD.Wave6b (dMinus halfMass IsEntPot entBound EntropicA EntropicB EntSetting regionSup)

/-! ### R `thm:entropic` -/

section Entropic
variable {K : ℕ}

/-- `d⁺(u₀;ν) = sup_{t>0, D<∞} inf_{‖e‖=1} ν(H_{t,D}(e))`. -/
def dPlus (ν : Measure (EuclideanSpace ℝ (Fin K))) (u₀ : EuclideanSpace ℝ (Fin K)) : ℝ≥0∞ :=
  ⨆ (t : ℝ) (_ : 0 < t) (D : ℝ), halfMass ν u₀ t D

/-- `κ = 1 − ℓ/(nδ)`. -/
def kappa (n ℓ : ℕ) (δ : ℝ) : ℝ := 1 - ℓ / (n * δ)

/-- Standing hypotheses with a data-driven temperature `ε(Z̃) = εsel Z̃`. -/
def EntSettingData (ν : Measure (EuclideanSpace ℝ (Fin K))) {n : ℕ}
    (εsel : (Fin n → EuclideanSpace ℝ (Fin K)) → ℝ)
    (fsel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ) : Prop :=
  ∫⁻ u, ‖u‖ₑ ^ 2 ∂ν < ⊤ ∧ ∀ Z', 0 < εsel Z' ∧ IsEntPot ν (εsel Z') Z' (fsel Z')

end Entropic

/-! ### R `lem:spike`, `thm:peaked-cube` -/

section Peaked

/-- The standard Cauchy law, density `1/(π(1+x²))`. -/
def cauchyStd : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (1 / (Real.pi * (1 + x ^ 2)))

/-- `C^{(L)}`: the standard Cauchy law conditioned on `|C| ≤ L`. -/
def truncCauchy (L : ℝ) : Measure ℝ := ProbabilityTheory.cond cauchyStd (Icc (-L) L)

/-- `L_k = L₀ k^a`. -/
def Lk (L₀ a : ℝ) (k : ℕ) : ℝ := L₀ * (k : ℝ) ^ a

/-- The law of `X_k = C_k/(k L_k)`. -/
def peakedCoord (L₀ a : ℝ) (k : ℕ) : Measure ℝ :=
  (truncCauchy (Lk L₀ a k)).map fun x => x / (k * Lk L₀ a k)

/-- `μ_K`: the law of `(X_1, …, X_K)` (independent coordinates), on `ℝ^K`. -/
def peakedLaw (L₀ a : ℝ) (K : ℕ) : Measure (EuclideanSpace ℝ (Fin K)) :=
  (Measure.pi fun i : Fin K => peakedCoord L₀ a (i.val + 1)).map (WithLp.toLp 2)

/-- The summand `log(1+L_k²)/L_k` of `S(L₀,a)`, at `k = j + 1`. -/
def peakedTerm (L₀ a : ℝ) (j : ℕ) : ℝ := Real.log (1 + Lk L₀ a (j + 1) ^ 2) / Lk L₀ a (j + 1)

/-- `S(L₀,a) = (4/π) Σ_{k≥1} log(1+L_k²)/L_k`. -/
def peakedS (L₀ a : ℝ) : ℝ := 4 / Real.pi * ∑' j : ℕ, peakedTerm L₀ a j

/-- `Λ_K = Σ_{k≤K} log(1+L_k²)`. -/
def peakedLambda (L₀ a : ℝ) (K : ℕ) : ℝ := ∑ i : Fin K, Real.log (1 + Lk L₀ a (i.val + 1) ^ 2)

/-- `α_K = (π/16)(1 − p − S)/Λ_K`. -/
def peakedAlpha (L₀ a p : ℝ) (K : ℕ) : ℝ := Real.pi / 16 * (1 - p - peakedS L₀ a) / peakedLambda L₀ a K

/-- The upper `α`-quantile of `C^{(L)}` in closed form, `tan((1 − 2α) arctan L)`. -/
def tcQuantile (L α : ℝ) : ℝ := Real.tan ((1 - 2 * α) * Real.arctan L)

/-- The vertex radii `r_k = y_k/(k L_k)`, `y_k` the upper `α`-quantile of `C^{(L_k)}`. -/
def peakedVertex (L₀ a α : ℝ) (K : ℕ) (i : Fin K) : ℝ :=
  tcQuantile (Lk L₀ a (i.val + 1)) α / ((i.val + 1 : ℝ) * Lk L₀ a (i.val + 1))

/-- The cross-polytope `CP(r) = {u : Σ_k |u_k|/r_k ≤ 1}`. -/
def crossPoly {K : ℕ} (r : Fin K → ℝ) : Set (EuclideanSpace ℝ (Fin K)) := {u | ∑ i, |u i| / r i ≤ 1}

/-- The displayed lower bound `π(1 − p − S)/(32 K log(1 + L₀² K^{2a}))`. -/
def peakedBound (L₀ a p : ℝ) (K : ℕ) : ℝ :=
  Real.pi * (1 - p - peakedS L₀ a) / (32 * K * Real.log (1 + L₀ ^ 2 * (K : ℝ) ^ (2 * a)))

end Peaked

namespace Claims

/-! ### `thm:entropic` (a) -/

/-- (a), first display: for every replaced `k`, `π(k|u₀) ≤ min{1, (n/κ) exp(−(t‖z_k‖ − DB)/ε)}`. -/
def entropic_weight : Prop :=
  ∀ (K n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν] (ε : ℝ)
    (fsel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ) (Z : Fin n → EuclideanSpace ℝ (Fin K))
    (ℓ : ℕ) (u₀ : EuclideanSpace ℝ (Fin K)) (t D : ℝ),
    EntSetting ν ε fsel → 0 < t → (ℓ : ℝ) < n * (halfMass ν u₀ t D).toReal →
      ∀ Z' ∈ Contam Z ℓ, ∀ B : ℝ, (∀ j, Z' j = Z j → ‖Z' j‖ ≤ B) → ∀ k, Z' k ≠ Z k →
        piCond Z' (fsel Z') ε u₀ k ≤
          min 1 (n / kappa n ℓ (halfMass ν u₀ t D).toReal * Real.exp (-(t * ‖Z' k‖ - D * B) / ε))

/-- (a), second display: the standing hypotheses imply the frozen `EntropicA` (displacement bound). -/
def entropic_displacement : Prop :=
  ∀ (K n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν] (ε : ℝ)
    (fsel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ) (Z : Fin n → EuclideanSpace ℝ (Fin K)),
    EntSetting ν ε fsel → EntropicA ν ε fsel Z

/-- (a), "in particular": `BP(Q̂(u₀)) ≥ d⁺(u₀;ν)`. -/
def entropic_bp_lower : Prop :=
  ∀ (K n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν] (ε : ℝ)
    (fsel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ) (Z : Fin n → EuclideanSpace ℝ (Fin K))
    (u₀ : EuclideanSpace ℝ (Fin K)),
    0 < K → 1 ≤ n → EntSetting ν ε fsel →
      (dPlus ν u₀).toReal ≤ BP (fun Z' => Qhat Z' (fsel Z') ε u₀) Z

/-! ### `thm:entropic` (b) -/

/-- (b): for `n ≥ 1` the standing hypotheses imply the frozen `EntropicB` (unboundedness for `ℓ > n d⁻`). -/
def entropic_unbounded : Prop :=
  ∀ (K n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν] (ε : ℝ)
    (fsel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ) (Z : Fin n → EuclideanSpace ℝ (Fin K)),
    1 ≤ n → EntSetting ν ε fsel → EntropicB ν ε fsel Z

/-- (b), "hence": `BP(Q̂(u₀)) ≤ d⁻(u₀;ν) + 1/n`. -/
def entropic_bp_upper : Prop :=
  ∀ (K n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν] (ε : ℝ)
    (fsel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ) (Z : Fin n → EuclideanSpace ℝ (Fin K))
    (u₀ : EuclideanSpace ℝ (Fin K)),
    0 < K → 1 ≤ n → EntSetting ν ε fsel →
      BP (fun Z' => Qhat Z' (fsel Z') ε u₀) Z ≤ (dMinus ν u₀).toReal + 1 / n

/-! ### `thm:entropic`, closing sentences -/

/-- Sharpening (review m4): `d⁺(u₀;ν) = d⁻(u₀;ν)` for every measure `ν`. -/
def dplus_eq_dminus : Prop :=
  ∀ (K : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) (u₀ : EuclideanSpace ℝ (Fin K)),
    dPlus ν u₀ = dMinus ν u₀

/-- If `ν` is absolutely continuous, `d⁺ = d⁻ = TD(u₀;ν)`. -/
def entropic_ac : Prop :=
  ∀ (K : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) (u₀ : EuclideanSpace ℝ (Fin K)),
    ν ≪ volume → dPlus ν u₀ = dMinus ν u₀ ∧ dMinus ν u₀ = tukeyDepth ν u₀

/-- (a) with a data-driven temperature bounded above by `εhi` on `𝔠_ℓ(𝒵)`: the bound holds at `εhi`. -/
def entropic_displacement_data : Prop :=
  ∀ (K n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν]
    (εsel : (Fin n → EuclideanSpace ℝ (Fin K)) → ℝ)
    (fsel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ) (Z : Fin n → EuclideanSpace ℝ (Fin K))
    (ℓ : ℕ) (u₀ : EuclideanSpace ℝ (Fin K)) (t D εhi : ℝ),
    EntSettingData ν εsel fsel → 0 < t → (ℓ : ℝ) < n * (halfMass ν u₀ t D).toReal →
      ∀ Z' ∈ Contam Z ℓ, εsel Z' ≤ εhi → ∀ B : ℝ, (∀ j, Z' j = Z j → ‖Z' j‖ ≤ B) →
        ‖Qhat Z' (fsel Z') (εsel Z') u₀‖ ≤ entBound n ℓ t D B εhi (halfMass ν u₀ t D).toReal

/-- (b) with a data-driven temperature bounded below by `εlo > 0` on `𝔠_ℓ(𝒵)`. -/
def entropic_unbounded_data : Prop :=
  ∀ (K n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν]
    (εsel : (Fin n → EuclideanSpace ℝ (Fin K)) → ℝ)
    (fsel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ) (Z : Fin n → EuclideanSpace ℝ (Fin K))
    (ℓ : ℕ) (u₀ : EuclideanSpace ℝ (Fin K)) (εlo : ℝ),
    1 ≤ n → EntSettingData ν εsel fsel → 0 < εlo → (∀ Z' ∈ Contam Z ℓ, εlo ≤ εsel Z') →
      (n : ℝ≥0∞) * dMinus ν u₀ < ℓ →
        ∀ M : ℝ, ∃ Z' ∈ Contam Z ℓ, M < ‖Qhat Z' (fsel Z') (εsel Z') u₀‖

/-- The breakdown bracket with a data-driven temperature in `[εlo, εhi] ⊂ (0,∞)`. -/
def entropic_bp_data : Prop :=
  ∀ (K n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν]
    (εsel : (Fin n → EuclideanSpace ℝ (Fin K)) → ℝ)
    (fsel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ) (Z : Fin n → EuclideanSpace ℝ (Fin K))
    (u₀ : EuclideanSpace ℝ (Fin K)) (εlo εhi : ℝ),
    0 < K → 1 ≤ n → EntSettingData ν εsel fsel → 0 < εlo → (∀ Z', εlo ≤ εsel Z' ∧ εsel Z' ≤ εhi) →
      (dPlus ν u₀).toReal ≤ BP (fun Z' => Qhat Z' (fsel Z') (εsel Z') u₀) Z ∧
        BP (fun Z' => Qhat Z' (fsel Z') (εsel Z') u₀) Z ≤ (dMinus ν u₀).toReal + 1 / n

/-! ### `thm:region-breakdown`, unconditional -/

/-- Frozen `region_bounded` without the hypothesis `EntropicA`. -/
def region_bounded_unconditional : Prop :=
  ∀ (K n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν] (ε : ℝ)
    (fsel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ) (Z : Fin n → EuclideanSpace ℝ (Fin K))
    (A : Set (EuclideanSpace ℝ (Fin K))) (ℓ : ℕ),
    0 < K → EntSetting ν ε fsel → IsCompact A → (ℓ : ℝ≥0∞) < n * Wave6b.betaPlus ν A →
      ∃ M : ℝ, ∀ Z' ∈ Contam Z ℓ, ∀ u ∈ A, ‖Qhat Z' (fsel Z') ε u‖ ≤ M

/-- Frozen `region_unbounded` without the hypothesis `EntropicB` (`n ≥ 1` added). -/
def region_unbounded_unconditional : Prop :=
  ∀ (K n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν] (ε : ℝ)
    (fsel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ) (Z : Fin n → EuclideanSpace ℝ (Fin K))
    (A : Set (EuclideanSpace ℝ (Fin K))) (ℓ : ℕ),
    0 < K → 1 ≤ n → EntSetting ν ε fsel → IsCompact A → A.Nonempty →
      (n : ℝ≥0∞) * (⨅ u ∈ A, dMinus ν u) < ℓ →
      ∀ M : ℝ, ∃ Z' ∈ Contam Z ℓ, ∃ u ∈ A, M < ‖Qhat Z' (fsel Z') ε u‖

/-- Frozen `region_bp_general` without `EntropicA`, `EntropicB`. -/
def region_bp_general_unconditional : Prop :=
  ∀ (K n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν] (ε : ℝ)
    (fsel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ) (Z : Fin n → EuclideanSpace ℝ (Fin K))
    (A : Set (EuclideanSpace ℝ (Fin K))),
    0 < K → 1 ≤ n → EntSetting ν ε fsel → IsCompact A → A.Nonempty →
      (⨅ u ∈ A, dMinus ν u).toReal ≤ BP (regionSup ε fsel A) Z ∧
        BP (regionSup ε fsel A) Z ≤ (⨅ u ∈ A, dMinus ν u).toReal + 1 / n

/-- Frozen `region_bp` without `EntropicA`, `EntropicB`. -/
def region_bp_unconditional : Prop :=
  ∀ (K n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure ν] (ε : ℝ)
    (fsel : (Fin n → EuclideanSpace ℝ (Fin K)) → Fin n → ℝ) (Z : Fin n → EuclideanSpace ℝ (Fin K))
    (A : Set (EuclideanSpace ℝ (Fin K))),
    0 < K → 1 ≤ n → ν ≪ volume → EntSetting ν ε fsel → IsCompact A → A.Nonempty →
      (regionDepth ν A).toReal ≤ BP (regionSup ε fsel A) Z ∧
        BP (regionSup ε fsel A) Z ≤ (regionDepth ν A).toReal + 1 / n

/-! ### `lem:spike` -/

/-- `TD(r e_k; ⊗μ_j) ≥ ½ μ_k[r, ∞)` for independent symmetric coordinates and `r ≥ 0`. -/
def spike : Prop :=
  ∀ (K : ℕ) (μ : Fin K → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)],
    (∀ i, (μ i).map (fun x => -x) = μ i) → ∀ (k : Fin K) (r : ℝ), 0 ≤ r →
      2⁻¹ * μ k (Ici r) ≤
        tukeyDepth ((Measure.pi μ).map (WithLp.toLp 2)) (EuclideanSpace.single k r)

/-- `lem:spike`, consequence: if `μ_k[r_k, ∞) ≥ α` for every `k`, then `β(CP(r)) ≥ α/2`. -/
def spike_cross : Prop :=
  ∀ (K : ℕ) (μ : Fin K → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)],
    (∀ i, (μ i).map (fun x => -x) = μ i) → ∀ (r : Fin K → ℝ) (α : ℝ≥0∞),
      (∀ i, 0 < r i) → (∀ i, α ≤ μ i (Ici (r i))) →
        α / 2 ≤ regionDepth ((Measure.pi μ).map (WithLp.toLp 2)) (crossPoly r)

/-! ### `thm:peaked-cube` -/

/-- `μ_K` is a probability measure. -/
def peaked_prob : Prop :=
  ∀ (L₀ a : ℝ) (K : ℕ), 1 ≤ L₀ → IsProbabilityMeasure (peakedLaw L₀ a K)

/-- `μ_K` is carried by the cube `∏_{k≤K} [−1/k, 1/k]`. -/
def peaked_support : Prop :=
  ∀ (L₀ a : ℝ) (K : ℕ), 1 ≤ L₀ →
    peakedLaw L₀ a K {u | ∀ i : Fin K, |u i| ≤ 1 / ((i.val : ℝ) + 1)} = 1

/-- `μ_K` is symmetric. -/
def peaked_symmetric : Prop :=
  ∀ (L₀ a : ℝ) (K : ℕ), 1 ≤ L₀ → (peakedLaw L₀ a K).map (fun u => -u) = peakedLaw L₀ a K

/-- `μ_K` is atomless (`K ≥ 1`). -/
def peaked_atomless : Prop :=
  ∀ (L₀ a : ℝ) (K : ℕ), 1 ≤ L₀ → 1 ≤ K → NullSingletonClass (peakedLaw L₀ a K)

/-- Coherence of the truncations: `μ_K` is the image of `μ_{K'}` (`K ≤ K'`) under the first `K` coordinates. -/
def peaked_coherent : Prop :=
  ∀ (L₀ a : ℝ) (K K' : ℕ) (h : K ≤ K'), 1 ≤ L₀ →
    (peakedLaw L₀ a K').map (fun u => WithLp.toLp 2 fun i : Fin K => u (Fin.castLE h i)) = peakedLaw L₀ a K

/-- `S(L₀,a) < ∞`: the series `Σ_k log(1+L_k²)/L_k` converges for `a > 1`. -/
def peaked_S_summable : Prop :=
  ∀ (L₀ a : ℝ), 1 ≤ L₀ → 1 < a → Summable (peakedTerm L₀ a)

/-- `Λ_K ≤ K log(1 + L₀² K^{2a})`. -/
def peaked_Lambda_le : Prop :=
  ∀ (L₀ a : ℝ) (K : ℕ), 1 ≤ L₀ → 0 < a →
    peakedLambda L₀ a K ≤ K * Real.log (1 + L₀ ^ 2 * (K : ℝ) ^ (2 * a))

/-- The vertices are the coordinate `(1 − α)`-quantiles: `μ_K{u_k ≥ r_k} = α` (`0 ≤ α ≤ 1/8`). -/
def peaked_quantile : Prop :=
  ∀ (L₀ a α : ℝ) (K : ℕ) (i : Fin K), 1 ≤ L₀ → 0 < a → 0 ≤ α → α ≤ 1 / 8 →
    peakedLaw L₀ a K {u | peakedVertex L₀ a α K i ≤ u i} = ENNReal.ofReal α

/-- Main clause: for `p < 1 − S` and `α_K ≤ 1/8`, `CP(r)` has content `≥ p` and robustness `≥ α_K/2`. -/
def peaked_cube : Prop :=
  ∀ (L₀ a p : ℝ) (K : ℕ), 1 ≤ L₀ → 1 < a → 1 ≤ K → p < 1 - peakedS L₀ a → peakedAlpha L₀ a p K ≤ 1 / 8 →
    ENNReal.ofReal p ≤ peakedLaw L₀ a K (crossPoly (peakedVertex L₀ a (peakedAlpha L₀ a p K) K)) ∧
      ENNReal.ofReal (peakedAlpha L₀ a p K / 2) ≤
        regionDepth (peakedLaw L₀ a K) (crossPoly (peakedVertex L₀ a (peakedAlpha L₀ a p K) K))

/-- The displayed bound: `β*_K(p) ≥ π(1 − p − S)/(32 K log(1 + L₀²K^{2a}))`. -/
def peaked_betaStar : Prop :=
  ∀ (L₀ a p : ℝ) (K : ℕ), 1 ≤ L₀ → 1 < a → 1 ≤ K → p < 1 - peakedS L₀ a → peakedAlpha L₀ a p K ≤ 1 / 8 →
    ENNReal.ofReal (peakedBound L₀ a p K) ≤ betaStar (peakedLaw L₀ a K) (ENNReal.ofReal p)

/-- The bound is `≍ 1/(K log K)`. -/
def peaked_rate : Prop :=
  ∀ (L₀ a p : ℝ), 1 ≤ L₀ → 1 < a → p < 1 - peakedS L₀ a →
    (fun K : ℕ => peakedBound L₀ a p K) =Θ[atTop] (fun K : ℕ => 1 / ((K : ℝ) * Real.log K))

/-- One law gives `β*_K(p) ≥ c/(K log K)` for every large `K`. -/
def peaked_betaStar_rate : Prop :=
  ∀ (L₀ a p : ℝ), 1 ≤ L₀ → 1 < a → p < 1 - peakedS L₀ a →
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ K : ℕ in atTop,
      ENNReal.ofReal (c / ((K : ℝ) * Real.log K)) ≤ betaStar (peakedLaw L₀ a K) (ENNReal.ofReal p)

/-- `S(L₀,a) → 0` as `L₀ → ∞`. -/
def peaked_S_tendsto : Prop :=
  ∀ a : ℝ, 1 < a → Tendsto (fun L₀ => peakedS L₀ a) atTop (𝓝 0)

/-- Any range of contents `p ≤ p₀ < 1` is covered by one law: some `L₀ ≥ 1` has `p₀ < 1 − S(L₀,a)`. -/
def peaked_cover : Prop :=
  ∀ a p₀ : ℝ, 1 < a → p₀ < 1 → ∃ L₀ : ℝ, 1 ≤ L₀ ∧ p₀ < 1 - peakedS L₀ a

end Claims
end StatFormal.OTFD.Wave12a
