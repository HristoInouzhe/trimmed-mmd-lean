import StatFormal.Archive.Wave30cq.Statements
import StatFormal.Archive.Wave29i.Statements
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# FROZEN STATEMENTS — wave 30da: trimmed-mmd `cor:boundary-linear` ("`G_P` a function of `𝔾_P`, so independent";
# the isotropic chi-bar-square sentence) and `thm:split` in the general regime `n₂, m₂ → ∞`

Source (pCloud = GitHub master `31e6ee2`, copied 2026-10-27): `trimmed-mmd/supplement.tex`, setting
`supp:boundarystate` (`:2756-2813`; `𝔾_P`, `𝔾_Q` independent Brownian bridges with continuous paths on
`𝔹_r × [−κ,κ]`, `H_P`, `H_Q` (`eq:Hdef`)), `thm:boundary` (`:2814-2839`), `cor:boundary-linear` (`:2846-2891`).
Printed text covered here:
* "The hypothesis holds, with `G_P` a function of `𝔾_P` and `G_Q` of `𝔾_Q` (so independent), in each of the
  following cases. (a) A unique separating direction: `K° = {λν : λ ≥ 0}` for a unit vector `ν`. … (b) A
  nondegenerate vertex contact of discrete laws: … Then `G_P = β 𝔾_P ψ_P` … and `G_Q` likewise." (`:2856-2883`)
* "When `c_P G_P − c_Q G_Q` is a centred Gaussian vector with covariance a multiple of the identity, the squared
  limit is a scaled chi-bar-square variable." (`:2884-2886`)
* `paper.tex` `thm:split` (`:1063-1076`): "Hold the first fold fixed … and let only the second fold grow. Then `T̂`
  in `eq:splitstat` is asymptotically normal as `n₂, m₂ → ∞`, with a variance consistently estimated by the
  nonparametric bootstrap … Then the rule reject `H_{0,α}` if `T̂_δ > 0` has asymptotic level `δ`, and rejection
  certifies `TV(P,Q) > α`"; `ass:split` (`:1051-1061`); proof `supplement.tex:747-790` ("the asymptotic variance of
  `T̂`, `(1−α)^{-2}[Var_P(q − f̂(X))_+/n₂ + Var_Q(f̂(Y) − q')_+/m₂]` … its plug-in estimate with a normal quantile is
  equally valid"). The print states NO ratio condition on `n₂, m₂`, and the printed variance is written with `n₂` and
  `m₂` separately, so the intended reading is the general regime; the frozen waves 22c/29i/29l/29w/30d cover it
  under `m(n)/n → κ ∈ (0, ∞)` only.
Imports the frozen statement files of wave 29i (`splitTrimLo`, `splitTrimUp`, `splitSE`, `splitUQ`, `splitAss`;
through it `Wave17a` `sepVal`, `Distances` `tvDist`), of wave 30cq and, through it, wave 30z (`hinge`, `Idx1`, `Idx2`, `IsLimitGP`,
`Hfun`, `SampleModel`, `Scaling`, `metricProj`, `discVar`, `vertexVec`), wave 30v (`Ball`, `ballNeg`, `polarSet`,
`coneHull`) and `TrimmedMMD` (`region`, `Demp`). New definitions: `leftPath`, `rightPath` (the two copies `𝔾_P ℓ`,
`𝔾_Q ℓ` of a path of the joint limit process), `splitSdAny` (the printed asymptotic standard deviation at sizes
`n, m`).

Covered (6 claims). `thm:split`, general regime (sizes `n_k, m_k ≥ 1` with `n_k → ∞`, `m_k → ∞`, NO ratio condition;
the setting of the frozen wave-29i claims otherwise verbatim: `T̂_k = splitTrimLo (n_k) α (h(X)) − splitTrimUp (m_k) α
(h(Y))`, `h = ⟨f, φ⟩`, i.i.d. samples, the two families independent):
* `split_normal_any` — "asymptotically normal as `n₂, m₂ → ∞`": `(T̂_k − T₀)/se_k ⇒ N(0,1)`, `T₀ = sep(f; 𝒞_α(P),
  𝒞_α(Q))`, `se_k = √(Var_P(q − h)_+/n_k + Var_Q(h − q')_+/m_k)/(1 − α)` (`splitSdAny`, the printed variance), under
  quantile uniqueness on both sides (the frozen `split_asymp_normal` premise, a generalisation of `ass:split`) and
  `Var_P(q − h)_+ > 0`, `Var_Q(h − q')_+ > 0` (declared extra premises: without them `se_k` may vanish or the
  standardisation fail; both follow from `ass:split` at `α > 0`, proved in the route of `split_level_any`).
* `split_level_any` — the frozen `split_level_discharged` (printed `ass:regularity` + `ass:split`, `0 < α < 1`, the
  plug-in standard error `splitSE`, `Φ̄(z) = δ`) with `m(n)/n → κ > 0` replaced by arbitrary `n_k, m_k → ∞`:
  asymptotic coverage `≥ 1 − δ − η` of `T̂_δ = T̂ − z ŝe`, asymptotic level `δ` under `TV ≤ α`, certification.
`cor:boundary-linear` (4 claims; `K = cl cone(B − A)`, `K°` its polar, all in the setting of `thm:boundary` (ii) exactly as in the
frozen wave-30z claims):
* `boundary_linear_factor` — `cor:boundary-linear`, the factorisation, GENERAL form: whenever the corollary's
  hypothesis holds with SOME random vectors `G_P, G_Q` (the hypotheses of the frozen `boundary_linear`, verbatim), it
  holds with `G_P' = F_P(𝔾_P)`, `G_Q' = F_Q(𝔾_Q)` for CONTINUOUS deterministic maps `F_P, F_Q : C(𝔹_r × [−κ,κ]) → ℝ^r`
  (`𝔾_P = leftPath 𝔾`, `𝔾_Q = rightPath 𝔾`); `G_P'`, `G_Q'` agree a.s. with `G_P`, `G_Q` on every direction of `K°`
  (`⟨g, G_P'⟩ = ⟨g, G_P⟩`, `g ∈ K°`), are INDEPENDENT (for the Borel σ-algebra of `ℝ^r`), and
  `r_k D̂ ⇒ ‖Π_{K°}(c_P G_P' − c_Q G_Q')‖`.
* `boundary_ray_factor` — (a): under the hypotheses of the frozen wave-30cq `boundary_ray_G` (`K° = ℝ₊ν`, `‖ν‖ = 1`):
  continuous `F_P, F_Q` with, for EVERY `ω'`, `F_P(𝔾_P) = −H_P(−ν) ν` and `F_Q(𝔾_Q) = H_Q(ν) ν`; the corollary's
  hypothesis holds a.s. for them, they are independent, and the projected-norm limit holds.
* `boundary_vertex_factor` — (b): under the hypotheses of the frozen wave-30z `boundary_vertex`, verbatim: continuous
  `F_P, F_Q` such that `G_P = F_P(𝔾_P)`, `G_Q = F_Q(𝔾_Q)` satisfy the corollary's hypothesis a.s., have the printed
  joint centred Gaussian law on the directions of `K°` (the conjunct of the frozen `boundary_vertex`, verbatim: the
  covariance `β² Cov_P(ψ_P) ⊕ β² Cov_Q(ψ_Q)` written through the atoms), are independent, and give the limit.
* `boundary_chibar` — the isotropic sentence: in the setting of the corollary (the hypotheses of the frozen
  `boundary_linear`, verbatim), if moreover `c_P G_P − c_Q G_Q ∼ N(0, σ² I)` (`σ ≥ 0`), then
  `(r_k D̂)² ⇒ σ² ‖Π_{K°} Z‖²`, `Z ∼ N(0, I_r)`: the squared limit is `σ²` times the chi-bar-square variable of the
  cone `K°`.

Encodings (to be checked by the critic):
* "`G_P` a function of `𝔾_P`": `G_P ω' = F_P (leftPath (𝔾 ω'))` for EVERY `ω'`, with `F_P` a fixed continuous (hence
  Borel) map `C(Idx1 E κ, ℝ) → E` that may depend on the data `φ, α, P, Q, κ, ν, …` but not on `ω'`;
  `leftPath v = v ∘ inl` is the `P`-copy `(f, t) ↦ 𝔾_P ℓ_{f,t}` of the joint path (the frozen `IsLimitGP` carries
  `(𝔾_P ℓ, 𝔾_Q ℓ)` as one element of `C(Idx1 ⊕ Idx1, ℝ)`), `rightPath v = v ∘ inr` the `Q`-copy.
* "(so independent)": `IndepFun G_P G_Q μ'` for every Borel measurable-space structure on `E` (stated as
  `∀ [MeasurableSpace E] [BorelSpace E], …`; `E` carries no σ-algebra in the frozen setting). It is PROVED from the
  frozen `IsLimitGP` (the joint finite-dimensional laws of the two copies have the additive variance `gpVar`, so
  the law of `𝔾` is the product of the laws of its copies), not assumed.
* `boundary_linear_factor` is a generalisation (declared): the printed sentence names the cases (a), (b); the general
  form gives both (and is how (b) is proved). The new vectors need not equal the given ones off `span K°`; the limit
  only reads them on `K°`.
* In (a) the vectors are the explicit `−H_P(−ν)ν`, `H_Q(ν)ν` of the frozen wave-30cq construction, now written as
  continuous functions of the respective copies.
* In (b) the printed identity `G_P = β 𝔾_P ψ_P` is (as in the frozen `boundary_vertex`, declared there) represented by
  the law of `G_P` on the directions of `K°`: the limit process is indexed by the hinge class only.
* Chi-bar-square: for a closed convex cone `C ⊆ ℝ^r`, the chi-bar-square variable of `C` is `‖Π_C Z‖²`,
  `Z ∼ N(0, I_r)` (Shapiro's definition; its representation as a mixture `Σ_k w_k(C) χ²_k` is not stated). `N(0, I_r)`
  is Mathlib's `stdGaussian E` (finite-dimensional inner product space `E` with its Borel σ-algebra), and
  "`c_P G_P − c_Q G_Q` centred Gaussian with covariance `σ² I`" is `HasLaw (c_P G_P − c_Q G_Q) ((stdGaussian E).map
  (σ • ·)) μ'` (Mathlib `HasLaw`: a.e.-measurable with that law; a bare `μ'.map … = …` would not exclude a
  non-measurable vector, whose `map` is a junk Dirac mass), `σ ≥ 0` (every multiple `σ² ≥ 0` of the identity). The limit is stated as convergence in distribution
  of `(r_k D̂)²` to `σ² ‖Π_{K°} Z‖²` on `(E, N(0, I))`, `Π_{K°} = metricProj (polarSet K)` (frozen).
* Everything else as in the frozen wave-30z claims (`Hfun`, `metricProj`, `TendstoInDistribution` with
  a.e.-measurability built in, sampling model, generalised scaling `r_k`).

Encodings for `thm:split`: those of the frozen wave-29i claims (`splitTrimLo/Up` through the capped simplex,
`splitUQ`, `splitAss`, `splitSE`, `sepVal` in `EReal`, `TendstoInDistribution` to `id` under `N(0,1)`); a "sequence
`n₂, m₂ → ∞`" is a pair `n, m : ℕ → ℕ` tending to `atTop`; the premise `n_k, m_k ≥ 1` (declared; sample sizes)
excludes the junk `/0` of `splitSdAny`, `splitSE` at empty samples and loses nothing asymptotically.

Not covered (declared): `thm:split` in the general regime — the bootstrap clause ("a variance consistently
estimated by the nonparametric bootstrap", and the bootstrap/percentile versions of the level) and the `α = 0` case
(sample means; the uniqueness / density premises are unsatisfiable there, as for the frozen wave-29i claims); both
remain certified in the ratio regime (waves 29l, 29w, 30d). `cor:boundary-linear`: the chi-bar-square mixture weights; the printed vector identity `G_P = β 𝔾_P ψ_P` in (b)
beyond the directions of `K°` (as in the frozen `boundary_vertex`); the sentence "In general it is the squared norm
of the projection … it need not be chi-bar-square (`rem:boundary-examples`)" (an example).

Non-vacuity: the hypotheses of `boundary_linear_factor`, `boundary_ray_factor`, `boundary_vertex_factor` are those of
the frozen `boundary_linear`, `boundary_ray_G`, `boundary_vertex` (critic-checked; wave-30z `NonVac`), and for
`boundary_linear_factor` the vectors of the frozen `boundary_ray_G` meet the extra premise. The extra premise of
`boundary_chibar` is met in the ray case with `E = ℝ` and unique quantiles: there `c_P G_P − c_Q G_Q =
(−c_P H_P(−ν) − c_Q H_Q(ν)) ν ∼ N(0, σ²)` (frozen `boundary_ray`, `boundary_Hprops` (d) and the independence
proved here), and every centred Gaussian on `ℝ` is isotropic.

Non-vacuity (`thm:split`): the premises of `split_level_any` are those of the frozen `split_level_discharged`
minus the ratio, plus `n_k, m_k ≥ 1`; they are met by the frozen witness (`Wave29i.RouteSplit.splitAss_uniform`:
uniform law on `[0,1]`, `P = Q`, with the clamped bounded `φ`) with `n_k = m_k = k + 1` (or any `n_k = k+1`, `m_k = 2^k`, outside every ratio
regime). Those of `split_normal_any` then hold too (`AssDens.uq`, `AssDens.var_pos` and its upper-side mirror).

Junk audit: `splitSdAny` and `splitSE` divide by `n_k, m_k ≥ 1` only, and the standardisation divides by
`se_k > 0` (positive variances); otherwise no division, no `toReal`; `Hfun` is the frozen `β · sInf` over the nonempty compact argmin set;
`metricProj` onto the closed convex nonempty `K°` is a genuine nearest point (frozen); `stdGaussian E` is a
probability measure; `IndepFun` is stated for Borel σ-algebras.

FROZEN 2026-10-27 — hashed in `certify/statements.lock` (with its imports) after the critic's review; AI agents must not edit it.
Critic (2026-10-27): ACCEPT (defs, boundary_ray_factor, boundary_vertex_factor, boundary_chibar, split_level_any), ACCEPT-WITH-NOTE
(boundary_linear_factor, split_normal_any); see certify/cards/wave30da.md.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped InnerProductSpace RealInnerProductSpace Pointwise

namespace StatFormal.Wave30da

open StatFormal.TrimmedMMD.Concentration (region)
open StatFormal.TrimmedMMD.Unconditional (Demp)
open StatFormal.Wave30v (Ball ballNeg polarSet coneHull)
open StatFormal.Wave30z

section Defs
variable {E : Type*} [NormedAddCommGroup E] {κ : ℝ}

/-- The `P`-copy `(f, t) ↦ 𝔾_P ℓ_{f,t}` of a path `v` of the joint limit process (`v` on the left copy). -/
def leftPath (v : C(Idx2 E κ, ℝ)) : C(Idx1 E κ, ℝ) := v.comp ⟨Sum.inl, continuous_inl⟩

/-- The `Q`-copy `(f, s) ↦ 𝔾_Q ℓ_{f,s}` of a path `v` of the joint limit process (`v` on the right copy). -/
def rightPath (v : C(Idx2 E κ, ℝ)) : C(Idx1 E κ, ℝ) := v.comp ⟨Sum.inr, continuous_inr⟩

end Defs

namespace Claims

/-- `cor:boundary-linear`, "with `G_P` a function of `𝔾_P` and `G_Q` of `𝔾_Q` (so independent)", general form:
under the hypotheses of the frozen `boundary_linear` (the corollary's hypothesis with some random vectors `G_P, G_Q`),
there are continuous maps `F_P, F_Q` such that `G_P' = F_P(𝔾_P)`, `G_Q' = F_Q(𝔾_Q)` satisfy the corollary's
hypothesis almost surely, agree a.s. with `G_P, G_Q` on every direction of `K°`, are independent, and
`r_k D̂ ⇒ ‖Π_{K°}(c_P G_P' − c_Q G_Q')‖`. -/
def boundary_linear_factor : Prop :=
  ∀ (𝒳 E : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (φ : 𝒳 → E) (κ α : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ η : ℕ → Ω → 𝒳)
    (n m : ℕ → ℕ) (r : ℕ → ℝ) (cP cQ : ℝ)
    (Ω' : Type) [MeasurableSpace Ω'] (μ' : Measure Ω') [IsProbabilityMeasure μ'] (𝔾 : Ω' → C(Idx2 E κ, ℝ))
    (GP GQ : Ω' → E),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → SampleModel P Q μ ξ η → Scaling n m r cP cQ →
    IsLimitGP φ P Q 1 1 κ μ' 𝔾 → (region φ α P ∩ region φ α Q).Nonempty →
    (∀ᵐ ω' ∂μ', ∀ g : Ball E, (g : E) ∈ polarSet (closure (coneHull (region φ α Q - region φ α P))) →
      Hfun φ α P κ Sum.inl (𝔾 ω') (ballNeg g) = ⟪-(g : E), GP ω'⟫ ∧ Hfun φ α Q κ Sum.inr (𝔾 ω') g = ⟪(g : E), GQ ω'⟫) →
      ∃ FP FQ : C(Idx1 E κ, ℝ) → E, Continuous FP ∧ Continuous FQ ∧
        (∀ᵐ ω' ∂μ', ∀ g : Ball E, (g : E) ∈ polarSet (closure (coneHull (region φ α Q - region φ α P))) →
          Hfun φ α P κ Sum.inl (𝔾 ω') (ballNeg g) = ⟪-(g : E), FP (leftPath (𝔾 ω'))⟫ ∧
            Hfun φ α Q κ Sum.inr (𝔾 ω') g = ⟪(g : E), FQ (rightPath (𝔾 ω'))⟫) ∧
        (∀ᵐ ω' ∂μ', ∀ g ∈ polarSet (closure (coneHull (region φ α Q - region φ α P))),
          ⟪g, FP (leftPath (𝔾 ω'))⟫ = ⟪g, GP ω'⟫ ∧ ⟪g, FQ (rightPath (𝔾 ω'))⟫ = ⟪g, GQ ω'⟫) ∧
        (∀ [MeasurableSpace E] [BorelSpace E],
          IndepFun (fun ω' => FP (leftPath (𝔾 ω'))) (fun ω' => FQ (rightPath (𝔾 ω'))) μ') ∧
        TendstoInDistribution
          (fun k ω => r k * Demp φ (fun i : Fin (n k) => ξ i ω) (fun j : Fin (m k) => η j ω) α)
          atTop (fun ω' => ‖metricProj (polarSet (closure (coneHull (region φ α Q - region φ α P))))
            (cP • FP (leftPath (𝔾 ω')) - cQ • FQ (rightPath (𝔾 ω')))‖) (fun _ => μ) μ'

/-- `cor:boundary-linear` (a), "the hypothesis holds, with `G_P` a function of `𝔾_P` and `G_Q` of `𝔾_Q` (so
independent)": under the hypotheses of the frozen wave-30cq `boundary_ray_G` (`K° = {cν : c ≥ 0}`, `‖ν‖ = 1`),
there are continuous maps `F_P, F_Q` with `F_P(𝔾_P) = −H_P(−ν) ν` and `F_Q(𝔾_Q) = H_Q(ν) ν` for every `ω'`, which
satisfy the corollary's hypothesis almost surely, are independent, and give `r_k D̂ ⇒ ‖Π_{K°}(c_P G_P − c_Q G_Q)‖`. -/
def boundary_ray_factor : Prop :=
  ∀ (𝒳 E : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (φ : 𝒳 → E) (κ α : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ η : ℕ → Ω → 𝒳)
    (n m : ℕ → ℕ) (r : ℕ → ℝ) (cP cQ : ℝ)
    (Ω' : Type) [MeasurableSpace Ω'] (μ' : Measure Ω') [IsProbabilityMeasure μ'] (𝔾 : Ω' → C(Idx2 E κ, ℝ))
    (ν : Ball E),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → SampleModel P Q μ ξ η → Scaling n m r cP cQ →
    IsLimitGP φ P Q 1 1 κ μ' 𝔾 → (region φ α P ∩ region φ α Q).Nonempty → ‖(ν : E)‖ = 1 →
    polarSet (closure (coneHull (region φ α Q - region φ α P))) = {x | ∃ c : ℝ, 0 ≤ c ∧ x = c • (ν : E)} →
      ∃ FP FQ : C(Idx1 E κ, ℝ) → E, Continuous FP ∧ Continuous FQ ∧
        (∀ ω', FP (leftPath (𝔾 ω')) = (-Hfun φ α P κ Sum.inl (𝔾 ω') (ballNeg ν)) • (ν : E) ∧
          FQ (rightPath (𝔾 ω')) = Hfun φ α Q κ Sum.inr (𝔾 ω') ν • (ν : E)) ∧
        (∀ᵐ ω' ∂μ', ∀ g : Ball E, (g : E) ∈ polarSet (closure (coneHull (region φ α Q - region φ α P))) →
          Hfun φ α P κ Sum.inl (𝔾 ω') (ballNeg g) = ⟪-(g : E), FP (leftPath (𝔾 ω'))⟫ ∧
            Hfun φ α Q κ Sum.inr (𝔾 ω') g = ⟪(g : E), FQ (rightPath (𝔾 ω'))⟫) ∧
        (∀ [MeasurableSpace E] [BorelSpace E],
          IndepFun (fun ω' => FP (leftPath (𝔾 ω'))) (fun ω' => FQ (rightPath (𝔾 ω'))) μ') ∧
        TendstoInDistribution
          (fun k ω => r k * Demp φ (fun i : Fin (n k) => ξ i ω) (fun j : Fin (m k) => η j ω) α)
          atTop (fun ω' => ‖metricProj (polarSet (closure (coneHull (region φ α Q - region φ α P))))
            (cP • FP (leftPath (𝔾 ω')) - cQ • FQ (rightPath (𝔾 ω')))‖) (fun _ => μ) μ'

/-- `cor:boundary-linear` (b), "the hypothesis holds, with `G_P` a function of `𝔾_P` and `G_Q` of `𝔾_Q` (so
independent)": under the hypotheses of the frozen wave-30z `boundary_vertex` (verbatim), there are continuous maps
`F_P, F_Q` such that `G_P = F_P(𝔾_P)`, `G_Q = F_Q(𝔾_Q)` satisfy the corollary's hypothesis almost surely, have the
printed joint centred Gaussian law on the directions of `K°` (`β² Cov_P(ψ_P) ⊕ β² Cov_Q(ψ_Q)`, through the atoms),
are independent, and give `r_k D̂ ⇒ ‖Π_{K°}(c_P G_P − c_Q G_Q)‖`. -/
def boundary_vertex_factor : Prop :=
  ∀ (𝒳 E : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (φ : 𝒳 → E) (κ α : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ η : ℕ → Ω → 𝒳)
    (n m : ℕ → ℕ) (r : ℕ → ℝ) (cP cQ : ℝ)
    (Ω' : Type) [MeasurableSpace Ω'] (μ' : Measure Ω') [IsProbabilityMeasure μ'] (𝔾 : Ω' → C(Idx2 E κ, ℝ))
    (J : ℕ) (xs : Fin J → 𝒳) (ps : Fin J → ℝ) (j0 : Fin J) (U : Finset (Fin J))
    (J' : ℕ) (ys : Fin J' → 𝒳) (qs : Fin J' → ℝ) (j0' : Fin J') (U' : Finset (Fin J')),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → SampleModel P Q μ ξ η → Scaling n m r cP cQ →
    IsLimitGP φ P Q 1 1 κ μ' 𝔾 → (region φ α P ∩ region φ α Q).Nonempty →
    (∀ j, 0 ≤ ps j) → P = ∑ j, ENNReal.ofReal (ps j) • Measure.dirac (xs j) → j0 ∉ U →
    ∑ j ∈ U, ps j < 1 - α → 1 - α < ∑ j ∈ U, ps j + ps j0 →
    (∀ g ∈ polarSet (closure (coneHull (region φ α Q - region φ α P))), g ≠ 0 →
      (∀ j ∈ U, ⟪-g, φ (xs j0)⟫ < ⟪-g, φ (xs j)⟫) ∧ (∀ j, j ∉ U → j ≠ j0 → ⟪-g, φ (xs j)⟫ < ⟪-g, φ (xs j0)⟫)) →
    (∀ j, 0 ≤ qs j) → Q = ∑ j, ENNReal.ofReal (qs j) • Measure.dirac (ys j) → j0' ∉ U' →
    ∑ j ∈ U', qs j < 1 - α → 1 - α < ∑ j ∈ U', qs j + qs j0' →
    (∀ g ∈ polarSet (closure (coneHull (region φ α Q - region φ α P))), g ≠ 0 →
      (∀ j ∈ U', ⟪g, φ (ys j0')⟫ < ⟪g, φ (ys j)⟫) ∧ (∀ j, j ∉ U' → j ≠ j0' → ⟪g, φ (ys j)⟫ < ⟪g, φ (ys j0')⟫)) →
      ∃ FP FQ : C(Idx1 E κ, ℝ) → E, Continuous FP ∧ Continuous FQ ∧
        (∀ᵐ ω' ∂μ', ∀ g : Ball E, (g : E) ∈ polarSet (closure (coneHull (region φ α Q - region φ α P))) →
          Hfun φ α P κ Sum.inl (𝔾 ω') (ballNeg g) = ⟪-(g : E), FP (leftPath (𝔾 ω'))⟫ ∧
            Hfun φ α Q κ Sum.inr (𝔾 ω') g = ⟪(g : E), FQ (rightPath (𝔾 ω'))⟫) ∧
        (∀ (p : ℕ) (f g : Fin p → E) (u w : Fin p → ℝ),
          (∀ i, f i ∈ polarSet (closure (coneHull (region φ α Q - region φ α P)))) →
          (∀ i, g i ∈ polarSet (closure (coneHull (region φ α Q - region φ α P)))) →
          μ'.map (fun ω' => ∑ i, u i * ⟪-f i, FP (leftPath (𝔾 ω'))⟫ + ∑ i, w i * ⟪g i, FQ (rightPath (𝔾 ω'))⟫) =
            gaussianReal 0 ((1 / (1 - α)) ^ 2 * (discVar ps (fun j => ∑ i, u i * ⟪-f i, vertexVec φ xs j0 U j⟫) +
              discVar qs (fun j => ∑ i, w i * ⟪g i, vertexVec φ ys j0' U' j⟫))).toNNReal) ∧
        (∀ [MeasurableSpace E] [BorelSpace E],
          IndepFun (fun ω' => FP (leftPath (𝔾 ω'))) (fun ω' => FQ (rightPath (𝔾 ω'))) μ') ∧
        TendstoInDistribution
          (fun k ω => r k * Demp φ (fun i : Fin (n k) => ξ i ω) (fun j : Fin (m k) => η j ω) α)
          atTop (fun ω' => ‖metricProj (polarSet (closure (coneHull (region φ α Q - region φ α P))))
            (cP • FP (leftPath (𝔾 ω')) - cQ • FQ (rightPath (𝔾 ω')))‖) (fun _ => μ) μ'

/-- `cor:boundary-linear`, "When `c_P G_P − c_Q G_Q` is a centred Gaussian vector with covariance a multiple of the
identity, the squared limit is a scaled chi-bar-square variable": under the hypotheses of the frozen
`boundary_linear`, if `c_P G_P − c_Q G_Q ∼ N(0, σ² I)` with `σ ≥ 0`, then `(r_k D̂)² ⇒ σ² ‖Π_{K°} Z‖²`,
`Z ∼ N(0, I)` (`σ²` times the chi-bar-square variable `‖Π_{K°} Z‖²` of the cone `K°`). -/
def boundary_chibar : Prop :=
  ∀ (𝒳 E : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (φ : 𝒳 → E) (κ α : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ η : ℕ → Ω → 𝒳)
    (n m : ℕ → ℕ) (r : ℕ → ℝ) (cP cQ : ℝ)
    (Ω' : Type) [MeasurableSpace Ω'] (μ' : Measure Ω') [IsProbabilityMeasure μ'] (𝔾 : Ω' → C(Idx2 E κ, ℝ))
    (GP GQ : Ω' → E) (σ : ℝ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → SampleModel P Q μ ξ η → Scaling n m r cP cQ →
    IsLimitGP φ P Q 1 1 κ μ' 𝔾 → (region φ α P ∩ region φ α Q).Nonempty →
    (∀ᵐ ω' ∂μ', ∀ g : Ball E, (g : E) ∈ polarSet (closure (coneHull (region φ α Q - region φ α P))) →
      Hfun φ α P κ Sum.inl (𝔾 ω') (ballNeg g) = ⟪-(g : E), GP ω'⟫ ∧ Hfun φ α Q κ Sum.inr (𝔾 ω') g = ⟪(g : E), GQ ω'⟫) →
    0 ≤ σ → HasLaw (fun ω' => cP • GP ω' - cQ • GQ ω') ((stdGaussian E).map (fun x => σ • x)) μ' →
      TendstoInDistribution
        (fun k ω => (r k * Demp φ (fun i : Fin (n k) => ξ i ω) (fun j : Fin (m k) => η j ω) α) ^ 2)
        atTop (fun x => σ ^ 2 * ‖metricProj (polarSet (closure (coneHull (region φ α Q - region φ α P)))) x‖ ^ 2)
        (fun _ => μ) (stdGaussian E)

end Claims

section SplitDefs

/-- The asymptotic standard deviation of `T̂` at sizes `n₂ = n`, `m₂ = m` (`supplement.tex:763-765`):
`se_{n,m} = √(Var_P (q − h)_+ / n + Var_Q (h − q')_+ / m) / (1 − α)`. -/
def splitSdAny {𝒳 : Type*} [MeasurableSpace 𝒳] (P Q : Measure 𝒳) (h : 𝒳 → ℝ) (α q q' : ℝ) (n m : ℕ) : ℝ :=
  √(Var[fun x => max (q - h x) 0; P] / n + Var[fun x => max (h x - q') 0; Q] / m) / (1 - α)

end SplitDefs

namespace Claims

open StatFormal.Wave17a (sepVal)
open StatFormal.Wave29i (splitTrimLo splitTrimUp splitSE splitUQ splitAss)

/-- `thm:split`, "asymptotically normal as `n₂, m₂ → ∞`", in the GENERAL regime (no ratio condition): for any
sizes `n_k, m_k ≥ 1` with `n_k → ∞`, `m_k → ∞`, the standardised statistic
`(T̂_k − T₀)/se_{n_k,m_k} ⇒ N(0, 1)`, `T₀ = sep(f; 𝒞_α(P), 𝒞_α(Q))`, under quantile uniqueness on both sides (the
frozen `split_asymp_normal` premise) and positive influence variances (both implied by `ass:split` at `α > 0`,
`split_level_any`). -/
def split_normal_any : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ' α q q' : ℝ) (f : H)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → 𝒳) (n m : ℕ → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ') → 0 ≤ α → α < 1 →
    splitUQ P (fun x => ⟪f, φ x⟫) (1 - α) q → splitUQ Q (fun x => ⟪f, φ x⟫) α q' →
    0 < Var[fun x => max (q - ⟪f, φ x⟫) 0; P] → 0 < Var[fun x => max (⟪f, φ x⟫ - q') 0; Q] →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X μ → iIndepFun Y μ →
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ → (∀ i, μ.map (X i) = P) → (∀ i, μ.map (Y i) = Q) →
    (∀ k, 1 ≤ n k) → (∀ k, 1 ≤ m k) → Tendsto n atTop atTop → Tendsto m atTop atTop →
      ∃ T₀ : ℝ, sepVal f (region φ α P) (region φ α Q) = (T₀ : EReal) ∧
        TendstoInDistribution (fun k ω =>
            (splitTrimLo (n k) α (fun i => ⟪f, φ (X i ω)⟫) - splitTrimUp (m k) α (fun j => ⟪f, φ (Y j ω)⟫) - T₀) /
              splitSdAny P Q (fun x => ⟪f, φ x⟫) α q q' (n k) (m k))
          atTop id (fun _ => μ) (gaussianReal 0 1)

/-- `thm:split` in the GENERAL regime `n₂, m₂ → ∞` (no ratio condition), UNCONDITIONAL, with the plug-in standard
error `ŝe = splitSE` and the normal quantile `z` (`Φ̄(z) = δ`), under `ass:regularity` and `ass:split` (density form,
both sides, `0 < α < 1`): asymptotic coverage of the lower limit `T̂_δ = T̂ − z ŝe`, asymptotic level `δ` under
`H_{0,α}`, and certification on the coverage event — the frozen `split_level_discharged` with the premise
`m(n)/n → κ ∈ (0, ∞)` replaced by arbitrary sizes `n_k, m_k ≥ 1`, `n_k, m_k → ∞`. -/
def split_level_any : Prop :=
  ∀ (𝒳 H : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : 𝒳 → H) (κ' α q q' δ z : ℝ) (f : H)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → 𝒳) (n m : ℕ → ℕ),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ') → 0 < α → α < 1 →
    splitAss P (fun x => ⟪f, φ x⟫) (1 - α) q → splitAss Q (fun x => ⟪f, φ x⟫) α q' →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X μ → iIndepFun Y μ →
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ → (∀ i, μ.map (X i) = P) → (∀ i, μ.map (Y i) = Q) →
    (∀ k, 1 ≤ n k) → (∀ k, 1 ≤ m k) → Tendsto n atTop atTop → Tendsto m atTop atTop →
    (gaussianReal 0 1).real (Ioi z) = δ →
      (∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, 1 - δ - η ≤ μ.real {ω |
          ((splitTrimLo (n k) α (fun i => ⟪f, φ (X i ω)⟫) - splitTrimUp (m k) α (fun j => ⟪f, φ (Y j ω)⟫) -
            z * splitSE (n k) (m k) α (fun i => ⟪f, φ (X i ω)⟫) (fun j => ⟪f, φ (Y j ω)⟫) : ℝ) : EReal) ≤
            sepVal f (region φ α P) (region φ α Q)}) ∧
      (StatFormal.Distances.tvDist P Q ≤ α →
          ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, μ {ω | 0 < splitTrimLo (n k) α (fun i => ⟪f, φ (X i ω)⟫) -
            splitTrimUp (m k) α (fun j => ⟪f, φ (Y j ω)⟫) -
            z * splitSE (n k) (m k) α (fun i => ⟪f, φ (X i ω)⟫) (fun j => ⟪f, φ (Y j ω)⟫)} ≤ ENNReal.ofReal (δ + η)) ∧
      (∀ k, ∀ ω, ((splitTrimLo (n k) α (fun i => ⟪f, φ (X i ω)⟫) - splitTrimUp (m k) α (fun j => ⟪f, φ (Y j ω)⟫) -
            z * splitSE (n k) (m k) α (fun i => ⟪f, φ (X i ω)⟫) (fun j => ⟪f, φ (Y j ω)⟫) : ℝ) : EReal) ≤
            sepVal f (region φ α P) (region φ α Q) →
          0 < splitTrimLo (n k) α (fun i => ⟪f, φ (X i ω)⟫) - splitTrimUp (m k) α (fun j => ⟪f, φ (Y j ω)⟫) -
            z * splitSE (n k) (m k) α (fun i => ⟪f, φ (X i ω)⟫) (fun j => ⟪f, φ (Y j ω)⟫) →
          α < StatFormal.Distances.tvDist P Q)

end Claims

end StatFormal.Wave30da
