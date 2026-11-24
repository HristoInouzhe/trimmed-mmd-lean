import StatFormal.Archive.ICL.Statements
import StatFormal.Archive.ICL.JointFull.Statements
import StatFormal.Archive.Wave11b.Statements
import StatFormal.Archive.Wave23a.Statements
import StatFormal.Archive.OTFD.Bands.Statements
import StatFormal.Archive.OTFD.Bands2.Statements
import StatFormal.Archive.OTFD.Wave14c.Statements
import StatFormal.Archive.TrimmedMMD.BangBang.Statements
import StatFormal.Archive.RobustEquality.Paper2.Seminorm.Statements
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# FROZEN STATEMENTS — wave P1d (PARTIAL_AUDIT wave 1d, finite gaps): ICL `prop:cps-gradient`, `thm:joint`,
# `prop:swor-score`; otfd B `prop:rk-paths`, `prop:band-certificate`; trimmed MMD `prop:bangbang`; robust equality
# paper 2 `prop:direction`, `lem:delta-inf`

Sources (verbatim in `lean-formalisation/inventory/extracted/{context-distribution-icl,otfd-B_bands,trimmed-mmd,
robust-equality-paper2}.md`; current manuscript text of 2026-10-16):
* ICL `prop:cps-gradient` (`context-distribution-ICL/paper/v3/sections/06_estimation.tex:13-27`), the paragraph after it
  (`:53-63`: logit gradient, continuous extension to faces, rest points, Frank–Wolfe gap at a fixed prompt), proofs
  `supp/proofs_main.tex:62-80` and the paragraph "The Frank–Wolfe gap at a fixed prompt" (`:82-88`).
* ICL `thm:joint` (`sections/06_estimation.tex:76-89`, the `M`-subset sentence), proof `supp/proofs_main.tex:90-118`
  (`:100-101`: laws on `M`-subsets presented in random order).
* ICL `prop:swor-score` (`supp/proofs_score.tex:346-353`), `as:smooth` (`:34-40`), proof "Derivatives" and "Application"
  (`:356-392`).
* otfd B `prop:rk-paths` (i), last sentence (`otfd/papers/B_bands/supplement.tex:6586-6595`), proof `:5186-5192`.
* otfd B `prop:band-certificate` (iv) (`otfd/papers/B_bands/main.tex:720-753`).
* trimmed MMD `prop:bangbang` (ii) residual-mass sentence and (iii) (`trimmed-mmd/paper.tex:1394-1424`), proof
  `supplement.tex:537-583`.
* robust equality paper 2 `prop:direction`, shrinkage sentence and the `ρ` paragraph
  (`robust-equality-outcomes-under-distribution-shift/paper2/main.tex:424-443`), `G = Δ + N₀ + N₁` (`:337`).
* robust equality paper 2 `lem:delta-inf`, first sentence for general laws (`paper2/main.tex:296-302`), proof
  `paper2/app_proofs.tex:34-45`.
Reuses, imported and not copied: `esym`, `InDeltaM`, `cps`, `incl`, `Grisk`, `Vrisk` (frozen `ICL`); `ProbVec`, `devJ`
(`ICL/Joint`); `jSwor`, `jIid`, `wScore` (Wave 11b); `cdfK`, `cdfKInv` (Wave 23a); `softmax`, `Qent`,
`gap`, `IsSimplexProj` (`OTFD/Bands`); `edgeUp`, `edgeLo`, `band` (`OTFD/Bands2`); `certUp`, `certLo`, `entCaps`,
`quadCaps` (OTFD Wave 14c); `oosA`, `oosB`, `rawScore`, `baryMap` (OTFD Wave 7a); `capped`, `qp`, `ord`, `cap`, `kfloor`
(`TrimmedMMD/BangBang`); `Deltafin` (`Paper2/Seminorm`); Tau Ceti's `wassersteinEDist`,
`IsCoupling`. New definitions: `oneSlotSub`, `coverSub`, `devFullSub` (the `M`-subset analogues of the frozen
`ICL/JointFull` `oneSlot`, `cover`, `devFull`).

Covered:
* `prop:cps-gradient`: `cps_logit` (softmax weights lie in `Δ^(M)` and `∂G/∂η_ℓ = π_ℓ(V_ℓ − G)`), `cps_logit_extension`
  (`w ↦ π_ℓ(V_ℓ − G)` is continuous on all of `Δ^(M)`, faces `w_ℓ = 0` included: the continuous extension of the logit
  gradient), `cps_fixed_prompt` (at `w` uniform on a prompt `P`, `|P| = M`: `w ∈ Δ^(M)`, `G = L(P)`, the logit gradient
  vanishes in every coordinate, `∂G/∂w_ℓ = 0` on `P`, `e_{M−1}(w_{−ℓ})/e_M(w) = M²` and `V_ℓ` = the risk after `ℓ`
  replaces a uniformly chosen member of `P` off `P`, and the Frank–Wolfe gap `⟨w,g⟩ − min_ℓ g_ℓ` equals
  `M² max_{ℓ∉P}(G − V_ℓ)_+`).
* `thm:joint`: `joint_full_subsets` (laws on `M`-subsets with the coverage term: the first term of the frozen
  `joint_full` replaced by `2B_L√(2 log(2C(n,M))/m)`).
* `prop:swor-score`: `swor_derivs` (first and second derivatives of `J_{n,m} − J^iid_{n,m}` bounded by `C₁/n`, `C₂/n`).
* `prop:rk-paths` (i): `rk_paths_strict` (entropic map, affinely spanning `Z_j`: strictly increasing).
* `prop:band-certificate` (iv): `band_outer_ent`, `band_outer_quad` (`x̄↓ ≤ x̂↓`, `x̂↑ ≤ x̄↑` for every `t`, hence
  `B̂ ⊆ B̄`, with caps from any lower bound of the reachability gaps).
* `prop:bangbang`: `bangbang_residual` ((ii): the tied residual mass equals `1 − k_n c` when the values below the
  threshold are distinct from it, and exceeds it when ties reach below rank `k_n`), `bangbang_residual_v` (the same for
  `v`, "symmetrically"), `bangbang_iii` ((iii): if `D̂ = 0`, `𝒯_α` is the set of feasible pairs with
  `Σ w_i φ(X_i) = Σ v_j φ(Y_j)`), `bangbang_iii_not_face` (refutation: for any `φ(a) ≠ φ(b)` — every characteristic
  kernel at two distinct points — `X = Y = (a, b)`, `α = β = ½` give `D̂ = 0` and a `𝒯_α` that is not a face).
* `prop:direction`: `direction_cert_homog` (the certified disparity `G(w)² = (Δ + N₀ + N₁)²` is `≥ 0`, even and
  2-homogeneous — the parenthesis "every disparity, certified …, is"; the realised disparity `Δ²` of a shifted pair is the
  instance `N₀ = N₁ = 0`), `direction_rho` (`inf G² > 0` and the `ρ` bound),
  `direction_rho_iso` (isotropic penalties: `N̄ = N̲ = c₀ + c₁` and `ρ ≤ (1 + Δ(u₀)/(c₀ + c₁))²`).
* `lem:delta-inf`: `delta_inf_general` (for any probability laws on a standard Borel `K` and measurable `h`:
  `W₂²(h#μ₀, h#μ₁) ≤ E_γ{h(X) − h(Y)}²` for every coupling, with equality at some coupling — the minimum).

Not covered (declared):
* `prop:cps-gradient`: the version of the fixed-prompt gap "with coverage" (`λ_cov M(c̄_P − c_ℓ)` inside the maximum)
  and "with `λ_KL > 0` the gap is infinite"; "fixed prompts are rest points of softmax and exponentiated-gradient
  updates" (a reading of `cps_fixed_prompt`); the sampling and algorithm paragraphs.
* `thm:joint`: nothing further (the `[n]^M` form is the frozen `ICL/JointFull` `joint_full`, the risk-only subset form
  and `log C(n,M) ≤ M log(en/M)` the frozen `ICL/Joint` claims).
* `prop:swor-score`: the multivariate form (gradient norm and Hessian operator norm on `U ⊆ ℝ^p`) — stated along a
  one-dimensional parameter, i.e. along every line `θ + t u` (the proof's own reduction; the operator-norm bound is its
  polarisation remark). This is not weaker: applied to `t ↦ s_{θ+tu}` (`U' = {t : θ + tu ∈ U}` open, `b₁ = sup‖∇s‖`,
  `b₂ = sup‖∇²s‖_op`) it bounds `|∂_u F| ≤ C₁/n` and `|uᵀ∇²F u| ≤ C₂/n` for every unit `u`, hence the gradient norm and the
  (symmetric) Hessian operator norm; only the existence of the multivariate derivatives (chain rule) is left implicit.
  The transfer to `thm:score`, `cor:inference` (empirical-process work, EMPPROC).
* `prop:rk-paths`: the curve-space form, the shell variant of (iii), general `M_K` in (iii) (unchanged).
* `prop:band-certificate` (iv): "the maximum is a fractional knapsack" (certified: OTFD Wave 15b `greedyFill`, Wave 2
  `tangent_knapsack`) and "the reference-space work is done once" (commentary).
* `prop:bangbang` (iii): "generically of positive dimension" and "no element is distinguished" (commentary).
* `prop:direction`: "when it dominates `Δ`, `ρ` is close to one" beyond the explicit bound of `direction_rho_iso`;
  "shrinking to `t b⋆` multiplies every such disparity by `t²`" is the 2-homogeneity hypothesis itself (`GoodPen`, `t > 0`;
  the cost `(1 − t)²` is the frozen `Paper2` `direction_shrink`), and "`G(u)² ≥ G(u₀)²/ρ`" is the definition of `ρ` —
  both restatements, not stated.
* `lem:delta-inf`: the linear-rule sentence `Δ(w)² = min_γ wᵀM_γw` for general laws (the instance `h = ⟨w,·⟩`,
  `E_γ⟨w, X − Y⟩² = wᵀM_γw`); the vertex part is for empirical centres (frozen `Paper2/Alternating`).

Encodings (see card):
* `cps_logit`: softmax logits `η ∈ ℝⁿ`, `w = softmax η` (frozen `Bands.softmax`); the partial derivative in `η_ℓ` is
  `HasDerivAt` of `t ↦ G(softmax(update η ℓ t))`; `1 ≤ M ≤ n` (otherwise `Δ^(M)` is empty). `cps_fixed_prompt`: the
  gradient `g_ℓ = e_{M−1}(w_{−ℓ})/e_M(w)(V_ℓ − G)` is the frozen `cps_gradient` formula; the gap is
  `Σ_ℓ w_ℓ g_ℓ − ⨅_ℓ g_ℓ` (a finite minimum, `n ≥ M ≥ 1`); `M² max_{ℓ∉P}(G − V_ℓ)_+` is the greatest element of
  `{0} ∪ {M²(G − V_ℓ) : ℓ ∉ P}` (for `P` the whole pool the gap is `0`). The mean risk over the validation queries is the
  case `L = m⁻¹Σ_i L(z̃_i; ·)` (`G`, `V_ℓ`, `∂G` are linear in `L`).
* `joint_full_subsets`: as in the frozen `ICL/JointFull`, with the index set `{S : Finset (Fin n) // |S| = M}`; the
  one-slot marginal of a law on `M`-subsets presented in random order is `Π̄_j = M⁻¹ Σ_S Π(S) 1{j ∈ S}`; `M ≤ n`.
* `swor_derivs`: a real parameter `t` (any line in `Θ`), score family `s : ℝ → 𝒵 → ℝ` with `s_- ≤ s ≤ s_+` and, at
  every `t ∈ U`, derivatives `s1`, `s2` in `t` bounded by `b₁`, `b₂` (`as:smooth`; the Lipschitz conditions in `z` are
  unused); the constants `C₁`, `C₂` are chosen before everything else except `M, s_±, b₁, b₂, B_L, κ ≥ K_max/K_min,
  Λ ≥ λ_cov` (so they depend on exactly the listed quantities); derivatives as functions `D₁`, `D₂` with `HasDerivAt`
  (no `deriv` junk). Otherwise the frozen Wave 11b encoding (`jSwor`, `jIid`, `n ≥ M(M−1)s₊/s₋`, `1 ≤ M ≤ n`).
* `rk_paths_strict`: `Q̂ = Qent ε M Z f` (frozen; any fitted potentials `f`), `⟨v, ·⟩_M = (Mv) ⬝ᵥ ·`,
  `τ_{K,p} = cdfKInv` with a continuous calibration (`c_K(0) = 0`, `c_K(1) = 1`); strictly increasing on `[0,1] ⊇ 𝒫_v`;
  `v ≠ 0` (`v ∈ 𝕊_K`).
* `band_outer_*`: the frozen Wave 14c `certUp`, `certLo` (knapsack values in `EReal`) and Bands2 `edgeUp`, `edgeLo`, at
  `mo = 𝔪(t)`, `v = e(t)`; caps `entCaps ε δ`, `quadCaps m γ δ` for any `δ ≤ δ_j(p)` (the gap of the affine scores
  `oosA`, `oosB` of `lem:oos-potential` over the region `A = A_{K,p}`), which covers "replacing `δ_j(p)` by any lower
  bound". The upper edge at `δ = δ_j(p)` is the frozen Wave 14c `rk_linear_ent`/`rk_linear_quad` at the evaluation
  functional; new here: any lower bound `δ`, the lower edge and the band inclusion.
* `bangbang_*`: the frozen `TrimmedMMD/BangBang` encoding; `D̂ = 0` is a minimiser with `qp = 0`; "face" is Mathlib's
  `IsExtreme` (extreme subset; every face in any sense is one); the refutation is universal over `E` and `a ≠ b`, so it
  meets the standing `ass:regularity` (bounded characteristic kernel: `φ` injective on points), tied samples allowed.
* `direction_*`: `ρ`-paragraph on any real inner-product space (generalises `ℝ^d`), unit sphere `‖u‖ = 1`, `Δ = Deltafin`
  of two finite centres, `N₀, N₁` arbitrary seminorms; `max`/`min` over the sphere as `IsLUB`/`IsGLB` (attained in
  finite dimension); `0 < Δ_min + N̲` (the denominator of the displayed bound), which makes `ρ` non-junk.
* `delta_inf_general`: `K` standard Borel (covers compact `K ⊆ ℝ^d`); `μ₀, μ₁` probability measures; `E_γ{…}²` is the
  lower integral of `ofReal((h x − h y)²)`; `W₂` is Tau Ceti's `wassersteinEDist 2` in `ℝ≥0∞`.

Manuscript notes:
* trimmed MMD `prop:bangbang`(iii) (`paper.tex:1421`): "a face of the product polytope that is generically of positive
  dimension" is false in general (`bangbang_iii_not_face`: `X = Y = (a, b)`, `α = β = ½`; `𝒯_α` is the diagonal `{w = v}` of
  the square, not a face). The proof shows exactly the slice of the product polytope by the linear constraint
  `Σ w_i φ(X_i) = Σ v_j φ(Y_j)` (a polytope, of positive dimension here); suggested wording "a polytope (the slice of
  the product polytope by the linear constraint …)". Minor: wording only, nothing downstream uses the face property
  (`rem:overfit` "discrete face" is figurative). The contribution list (`paper.tex:377-379`) speaks of the (ii) tie set
  as "a face of the feasible polytope" — a separate sentence, not checked here.

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open Finset MeasureTheory ProbabilityTheory TauCeti Set Matrix
open scoped ENNReal

namespace StatFormal.WaveP1d

open StatFormal.ICL.Joint (ProbVec devJ)

/-- One-slot marginal of a law on `M`-subsets presented in random order: `Π̄_j = M⁻¹ Σ_S Π(S) 1{j ∈ S}`. -/
def oneSlotSub {n M : ℕ} (law : {S : Finset (Fin n) // S.card = M} → ℝ) (j : Fin n) : ℝ :=
  (1 / (M : ℝ)) * ∑ S, law S * (if j ∈ S.1 then 1 else 0)

/-- Coverage `ρ(z) = Σ_j Π̄_j K(z, z_j)` of a law on `M`-subsets. -/
def coverSub {Z : Type*} {n M : ℕ} (k : Fin n → Z → ℝ) (law : {S : Finset (Fin n) // S.card = M} → ℝ)
    (z : Z) : ℝ :=
  ∑ j, oneSlotSub law j * k j z

/-- `J_m(Π) − J_pool(Π)` with the coverage term, for a law on `M`-subsets. -/
def devFullSub {Z : Type*} [MeasurableSpace Z] {n M m : ℕ} (μ : Measure Z)
    (L : {S : Finset (Fin n) // S.card = M} → Z → ℝ) (k : Fin n → Z → ℝ) (lcov : ℝ)
    (law : {S : Finset (Fin n) // S.card = M} → ℝ) (zs : Fin m → Z) : ℝ :=
  devJ μ m L law zs +
    lcov * (-(1 / (m : ℝ)) * ∑ i, Real.log (coverSub k law (zs i)) + ∫ z, Real.log (coverSub k law z) ∂μ)

namespace Claims

open StatFormal.ICL (esym InDeltaM incl Grisk Vrisk)
open StatFormal.OTFD.Bands (softmax Qent gap IsSimplexProj)
open StatFormal.OTFD.Bands2 (edgeUp edgeLo band)
open StatFormal.OTFD.Wave14c (certUp certLo entCaps quadCaps)
open StatFormal.OTFD.Wave7a (oosA oosB rawScore baryMap)
open StatFormal.TrimmedMMD.BangBang (capped qp ord cap kfloor)
open StatFormal.RobustEquality.Paper2.Seminorm (Deltafin)
open StatFormal.Wave11b (jSwor jIid wScore)

/-! ### ICL `prop:cps-gradient` -/

/-- Logit derivative: for softmax logits `η` (`1 ≤ M ≤ n`), `w = softmax η ∈ Δ^(M)` and
`∂G/∂η_ℓ = π_ℓ (V_ℓ − G)`. -/
def cps_logit : Prop :=
  ∀ (n M : ℕ) (η : Fin n → ℝ) (L : Finset (Fin n) → ℝ), 1 ≤ M → M ≤ n →
    InDeltaM (softmax η) M ∧
    ∀ ℓ, HasDerivAt (fun t => Grisk (softmax (Function.update η ℓ t)) M L)
      (incl (softmax η) M ℓ * (Vrisk (softmax η) M L ℓ - Grisk (softmax η) M L)) (η ℓ)

/-- The logit gradient `π_ℓ(V_ℓ − G)` extends continuously to the faces `w_ℓ = 0`: it is continuous on all of `Δ^(M)`. -/
def cps_logit_extension : Prop :=
  ∀ (n M : ℕ) (L : Finset (Fin n) → ℝ) (ℓ : Fin n), 1 ≤ M →
    ContinuousOn (fun w => incl w M ℓ * (Vrisk w M L ℓ - Grisk w M L)) {w | InDeltaM w M}

/-- Fixed prompts: at `w` uniform on `P` (`|P| = M`), `w ∈ Δ^(M)`, `G = L(P)`, the logit gradient vanishes, the
gradient `g_ℓ = ∂G/∂w_ℓ` vanishes on `P`, off `P` it is `M²(V_ℓ − G)` with `V_ℓ` the risk after `ℓ` replaces a uniformly
chosen member of `P`, and the Frank–Wolfe gap `⟨w, g⟩ − min_ℓ g_ℓ` is `M² max_{ℓ∉P}(G − V_ℓ)_+`. -/
def cps_fixed_prompt : Prop :=
  ∀ (n M : ℕ) (P : Finset (Fin n)) (L : Finset (Fin n) → ℝ), 1 ≤ M → P.card = M →
    let w : Fin n → ℝ := fun j => if j ∈ P then 1 / (M : ℝ) else 0
    let g : Fin n → ℝ := fun ℓ =>
      esym w (univ.erase ℓ) (M - 1) / esym w univ M * (Vrisk w M L ℓ - Grisk w M L)
    InDeltaM w M ∧ Grisk w M L = L P ∧
    (∀ ℓ, incl w M ℓ * (Vrisk w M L ℓ - Grisk w M L) = 0) ∧
    (∀ ℓ ∈ P, g ℓ = 0) ∧
    (∀ ℓ ∉ P, esym w (univ.erase ℓ) (M - 1) / esym w univ M = (M : ℝ) ^ 2 ∧
       Vrisk w M L ℓ = (1 / (M : ℝ)) * ∑ k ∈ P, L (insert ℓ (P.erase k))) ∧
    IsGreatest (insert 0 ((fun ℓ => (M : ℝ) ^ 2 * (Grisk w M L - Vrisk w M L ℓ)) '' {ℓ | ℓ ∉ P}))
      ((∑ ℓ, w ℓ * g ℓ) - ⨅ ℓ, g ℓ)

/-! ### ICL `thm:joint`, laws on `M`-subsets with the coverage term -/

/-- `thm:joint` for laws on `M`-subsets (presented in random order), risk and coverage terms. -/
def joint_full_subsets : Prop :=
  ∀ (Z Ω : Type) [MeasurableSpace Z] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure Z) [IsProbabilityMeasure μ] (n M m : ℕ) (L : {S : Finset (Fin n) // S.card = M} → Z → ℝ)
    (k : Fin n → Z → ℝ) (BL Kmin Kmax lcov δ : ℝ) (X : Fin m → Ω → Z),
    2 ≤ n → 1 ≤ M → M ≤ n → 0 < m → 0 < δ → δ < 1 → 0 ≤ lcov → 0 < Kmin →
    (∀ j, Measurable (L j)) → (∀ j z, 0 ≤ L j z ∧ L j z ≤ BL) →
    (∀ j, Measurable (k j)) → (∀ j z, Kmin ≤ k j z ∧ k j z ≤ Kmax) →
    (∀ i, Measurable (X i)) → iIndepFun X P → (∀ i, P.map (X i) = μ) →
      ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - δ) ≤ P E ∧
        E ⊆ {ω | ∀ law : {S : Finset (Fin n) // S.card = M} → ℝ, ProbVec law →
          |devFullSub μ L k lcov law (fun i => X i ω)| ≤
            2 * BL * √(2 * Real.log (2 * (n.choose M : ℝ)) / m) +
            4 * lcov * (Kmax / Kmin) * √(2 * Real.log (2 * n) / m) +
            (BL + lcov * Real.log (Kmax / Kmin)) * √(Real.log (1 / δ) / (2 * m))}

/-! ### ICL `prop:swor-score`, derivative bounds -/

/-- Under `as:smooth` along a real parameter `t ∈ U` (`s_t` with `t`-derivatives `s1`, `s2` bounded by `b₁`, `b₂`),
the first and second derivatives of `J_{n,m} − J^iid_{n,m}` are bounded by `C₁/n` and `C₂/n`, with `C₁`, `C₂` depending
only on `M`, `s_±`, `b₁`, `b₂`, `B_L`, `κ ≥ K_max/K_min` and `Λ ≥ λ_cov`. -/
def swor_derivs : Prop :=
  ∀ (M : ℕ) (sm sp b1 b2 BL κ Λ : ℝ), ∃ C1 C2 : ℝ,
  ∀ (Z : Type) (n m : ℕ) (z : Fin n → Z) (zt : Fin m → Z) (s s1 s2 : ℝ → Z → ℝ)
    (L : Z → (Fin M → Z) → ℝ) (K : Z → Z → ℝ) (Kmin Kmax lcov lKL : ℝ) (U : Set ℝ),
    1 ≤ M → M ≤ n → 0 < m → 0 < sm → (∀ t x, sm ≤ s t x ∧ s t x ≤ sp) →
    (∀ x, ∀ t ∈ U, HasDerivAt (fun t => s t x) (s1 t x) t ∧ HasDerivAt (fun t => s1 t x) (s2 t x) t) →
    (∀ x, ∀ t ∈ U, |s1 t x| ≤ b1 ∧ |s2 t x| ≤ b2) →
    (∀ x t, 0 ≤ L x t ∧ L x t ≤ BL) → (∀ x t (σ : Equiv.Perm (Fin M)), L x (t ∘ σ) = L x t) →
    0 < Kmin → (∀ x y, Kmin ≤ K x y ∧ K x y ≤ Kmax) → Kmax / Kmin ≤ κ → 0 ≤ lcov → lcov ≤ Λ →
    M * ((M : ℝ) - 1) * sp / sm ≤ n →
      ∃ D1 D2 : ℝ → ℝ, ∀ t ∈ U,
        HasDerivAt (fun t => jSwor L K z zt lcov lKL (wScore s z t) - jIid L K z zt lcov lKL (wScore s z t))
          (D1 t) t ∧
        HasDerivAt D1 (D2 t) t ∧ |D1 t| ≤ C1 / n ∧ |D2 t| ≤ C2 / n

/-! ### otfd B `prop:rk-paths` (i), strictness -/

/-- For the entropic map with affinely spanning `Z_j`, `p ↦ ⟨v, Q̂(τ_{K,p} v)⟩_M` is strictly increasing. -/
def rk_paths_strict : Prop :=
  ∀ (K n : ℕ) (ε : ℝ) (M : Matrix (Fin K) (Fin K) ℝ) (Z : Fin n → Fin K → ℝ) (f : Fin n → ℝ)
    (μ : Measure (EuclideanSpace ℝ (Fin K))) (ρ : EuclideanSpace ℝ (Fin K) → ℝ) (v : Fin K → ℝ),
    0 < ε → M.PosDef → affineSpan ℝ (Set.range Z) = ⊤ → v ≠ 0 →
    ContinuousOn (StatFormal.Wave23a.cdfK μ ρ) (Icc 0 1) → StatFormal.Wave23a.cdfK μ ρ 0 = 0 →
    StatFormal.Wave23a.cdfK μ ρ 1 = 1 →
      StrictMonoOn (fun p => (M *ᵥ v) ⬝ᵥ Qent ε M Z f (StatFormal.Wave23a.cdfKInv μ ρ p • v)) (Icc 0 1)

/-! ### otfd B `prop:band-certificate` (iv), the certified outer band -/

/-- Entropic map: with caps `κ_j = e^{−δ_j/ε}` from any `δ_j ≤ δ_j(p)`, `x̄↓(t) ≤ x̂↓(t)` and `x̂↑(t) ≤ x̄↑(t)` for every
`t`, so the exact band is contained in the certified outer band. -/
def band_outer_ent : Prop :=
  ∀ (n K : ℕ) (ε : ℝ) (M : Matrix (Fin K) (Fin K) ℝ) (Z : Fin n → Fin K → ℝ) (f : Fin n → ℝ)
    (A : Set (Fin K → ℝ)) (δ : Fin n → ℝ) (T : Type) (mo : T → ℝ) (e : T → Fin K → ℝ),
    0 < n → 0 < ε → M.PosDef → A.Nonempty → (∀ j, δ j ≤ gap (oosA M f Z) (oosB M Z) A j) →
      (∀ t, certLo (entCaps ε δ) Z (mo t) (e t) ≤ edgeLo (Qent ε M Z f) A (mo t) (e t) ∧
        edgeUp (Qent ε M Z f) A (mo t) (e t) ≤ certUp (entCaps ε δ) Z (mo t) (e t)) ∧
      band (fun t => edgeLo (Qent ε M Z f) A (mo t) (e t)) (fun t => edgeUp (Qent ε M Z f) A (mo t) (e t)) ⊆
        band (fun t => certLo (entCaps ε δ) Z (mo t) (e t)) (fun t => certUp (entCaps ε δ) Z (mo t) (e t))

/-- Quadratic map (`λ = γ/m`): the same with the caps `κ_j = (1 − mδ_j/γ)_+`. -/
def band_outer_quad : Prop :=
  ∀ (n K m : ℕ) (γ : ℝ) (M : Matrix (Fin K) (Fin K) ℝ) (Z : Fin n → Fin K → ℝ) (f : Fin n → ℝ)
    (q : (Fin K → ℝ) → Fin n → ℝ) (A : Set (Fin K → ℝ)) (δ : Fin n → ℝ) (T : Type) (mo : T → ℝ)
    (e : T → Fin K → ℝ),
    0 < γ → 0 < m → M.PosDef → A.Nonempty → (∀ u, IsSimplexProj (rawScore (γ / m) M f Z u) (q u)) →
    (∀ j, δ j ≤ gap (oosA M f Z) (oosB M Z) A j) →
      (∀ t, certLo (quadCaps m γ δ) Z (mo t) (e t) ≤ edgeLo (fun u => baryMap (q u) Z) A (mo t) (e t) ∧
        edgeUp (fun u => baryMap (q u) Z) A (mo t) (e t) ≤ certUp (quadCaps m γ δ) Z (mo t) (e t)) ∧
      band (fun t => edgeLo (fun u => baryMap (q u) Z) A (mo t) (e t))
          (fun t => edgeUp (fun u => baryMap (q u) Z) A (mo t) (e t)) ⊆
        band (fun t => certLo (quadCaps m γ δ) Z (mo t) (e t)) (fun t => certUp (quadCaps m γ δ) Z (mo t) (e t))

/-! ### trimmed MMD `prop:bangbang` -/

/-- (ii), residual mass: if `D̂ > 0`, the indices tied at the threshold `d̂_{(k_n+1)}` carry at least `1 − k_n c`, exactly
`1 − k_n c` when the values below the threshold are distinct from it (or `k_n = 0`), and strictly more when ties reach
below rank `k_n` (`d̂_{(k_n)} = d̂_{(k_n+1)}`). -/
def bangbang_residual : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n m : ℕ) (x : Fin n → E)
    (y : Fin m → E) (α β : ℝ) (p : (Fin n → ℝ) × (Fin m → ℝ)),
    0 < n → 0 < m → 0 ≤ α → α < 1 → 0 ≤ β → β < 1 → kfloor n α < n → kfloor m β < m →
    p ∈ capped n α ×ˢ capped m β → IsMinOn (qp x y) (capped n α ×ˢ capped m β) p → 0 < qp x y p →
      let d := ∑ i, p.1 i • x i - ∑ j, p.2 j • y j
      let dx : Fin n → ℝ := fun i => inner ℝ d (x i)
      let θx := ord dx (kfloor n α)
      1 - kfloor n α * cap n α ≤ ∑ i ∈ univ.filter (fun i => dx i = θx), p.1 i ∧
      ((kfloor n α = 0 ∨ ord dx (kfloor n α - 1) < θx) →
        ∑ i ∈ univ.filter (fun i => dx i = θx), p.1 i = 1 - kfloor n α * cap n α) ∧
      (0 < kfloor n α → ord dx (kfloor n α - 1) = θx →
        1 - kfloor n α * cap n α < ∑ i ∈ univ.filter (fun i => dx i = θx), p.1 i)

/-- (ii), residual mass of `v` ("symmetrically"): if `D̂ > 0`, the indices tied at the threshold `d̂_{(m−k_m)}` of the
`Y` values carry at least `1 − k_m c_m`, exactly `1 − k_m c_m` when the values above the threshold are distinct from it
(or `k_m = 0`), and strictly more when ties reach above rank `m − k_m` (`d̂_{(m−k_m+1)} = d̂_{(m−k_m)}`). -/
def bangbang_residual_v : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n m : ℕ) (x : Fin n → E)
    (y : Fin m → E) (α β : ℝ) (p : (Fin n → ℝ) × (Fin m → ℝ)),
    0 < n → 0 < m → 0 ≤ α → α < 1 → 0 ≤ β → β < 1 → kfloor n α < n → kfloor m β < m →
    p ∈ capped n α ×ˢ capped m β → IsMinOn (qp x y) (capped n α ×ˢ capped m β) p → 0 < qp x y p →
      let d := ∑ i, p.1 i • x i - ∑ j, p.2 j • y j
      let dy : Fin m → ℝ := fun j => inner ℝ d (y j)
      let θy := ord dy (m - kfloor m β - 1)
      1 - kfloor m β * cap m β ≤ ∑ j ∈ univ.filter (fun j => dy j = θy), p.2 j ∧
      ((kfloor m β = 0 ∨ θy < ord dy (m - kfloor m β)) →
        ∑ j ∈ univ.filter (fun j => dy j = θy), p.2 j = 1 - kfloor m β * cap m β) ∧
      (0 < kfloor m β → ord dy (m - kfloor m β) = θy →
        1 - kfloor m β * cap m β < ∑ j ∈ univ.filter (fun j => dy j = θy), p.2 j)

/-- (iii): if `D̂ = 0` (a minimiser with value `0`), the minimisers are exactly the feasible pairs with
`Σ w_i φ(X_i) = Σ v_j φ(Y_j)`. -/
def bangbang_iii : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n m : ℕ) (x : Fin n → E)
    (y : Fin m → E) (α β : ℝ) (p₀ : (Fin n → ℝ) × (Fin m → ℝ)),
    0 < n → 0 < m → 0 ≤ α → α < 1 → 0 ≤ β → β < 1 →
    p₀ ∈ capped n α ×ˢ capped m β → IsMinOn (qp x y) (capped n α ×ˢ capped m β) p₀ → qp x y p₀ = 0 →
      {p | p ∈ capped n α ×ˢ capped m β ∧ IsMinOn (qp x y) (capped n α ×ˢ capped m β) p} =
        {p | p ∈ capped n α ×ˢ capped m β ∧ ∑ i, p.1 i • x i = ∑ j, p.2 j • y j}

/-- (iii), refutation of "a face of the product polytope": for any two distinct feature vectors `a ≠ b` (any
characteristic kernel at two distinct points), the samples `X = Y = (a, b)` at `α = β = ½` have `D̂ = 0`, and `𝒯_α`
(the diagonal `{w = v}` of the square `Δ_½(2) × Δ_½(2)`) is not an extreme subset of the product polytope. -/
def bangbang_iii_not_face : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a b : E), a ≠ b →
    (∃ p₀ ∈ capped 2 (1 / 2) ×ˢ capped 2 (1 / 2),
      IsMinOn (qp ![a, b] ![a, b]) (capped 2 (1 / 2) ×ˢ capped 2 (1 / 2)) p₀ ∧ qp ![a, b] ![a, b] p₀ = 0) ∧
    ¬ IsExtreme ℝ (capped 2 (1 / 2) ×ˢ capped 2 (1 / 2))
      {p | p ∈ capped 2 (1 / 2) ×ˢ capped 2 (1 / 2) ∧
        IsMinOn (qp ![a, b] ![a, b]) (capped 2 (1 / 2) ×ˢ capped 2 (1 / 2)) p}

/-! ### robust equality paper 2 `prop:direction` -/

/-- The certified disparity `G(w)² = (Δ(w) + N₀(w) + N₁(w))²` of a linear rule is such a penalty: `G ≥ 0` and
`G(t w)² = t² G(w)²` for every real `t` (so it is even). -/
def direction_cert_homog : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n₀ n₁ : ℕ)
    (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (N₀ N₁ : Seminorm ℝ E),
    (∀ w, 0 ≤ Deltafin a₀ x₀ a₁ x₁ w + N₀ w + N₁ w) ∧
    ∀ (t : ℝ) (w : E), (Deltafin a₀ x₀ a₁ x₁ (t • w) + N₀ (t • w) + N₁ (t • w)) ^ 2 =
      t ^ 2 * (Deltafin a₀ x₀ a₁ x₁ w + N₀ w + N₁ w) ^ 2

/-- The `ρ` paragraph: with `N̄ = sup (N₀+N₁)`, `N̲ = inf (N₀+N₁)`, `Δ_min = inf Δ` and `inf G²` over the unit sphere,
and `Δ_min + N̲ > 0`: `inf G² > 0` and `ρ = G(u₀)²/inf G² ≤ ((Δ(u₀) + N̄)/(Δ_min + N̲))²`. -/
def direction_rho : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n₀ n₁ : ℕ)
    (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (N₀ N₁ : Seminorm ℝ E)
    (u₀ : E) (Nbar Nund Dmin Gsqmin : ℝ),
    ‖u₀‖ = 1 →
    IsLUB {r | ∃ u : E, ‖u‖ = 1 ∧ r = N₀ u + N₁ u} Nbar →
    IsGLB {r | ∃ u : E, ‖u‖ = 1 ∧ r = N₀ u + N₁ u} Nund →
    IsGLB {r | ∃ u : E, ‖u‖ = 1 ∧ r = Deltafin a₀ x₀ a₁ x₁ u} Dmin →
    IsGLB {r | ∃ u : E, ‖u‖ = 1 ∧ r = (Deltafin a₀ x₀ a₁ x₁ u + N₀ u + N₁ u) ^ 2} Gsqmin →
    0 < Dmin + Nund →
      0 < Gsqmin ∧
      (Deltafin a₀ x₀ a₁ x₁ u₀ + N₀ u₀ + N₁ u₀) ^ 2 / Gsqmin ≤
        ((Deltafin a₀ x₀ a₁ x₁ u₀ + Nbar) / (Dmin + Nund)) ^ 2

/-- Isotropic penalties `N_s = c_s‖·‖`: `N̄ = N̲ = c₀ + c₁` (attained), the bound reads
`ρ ≤ ((Δ(u₀) + c)/(Δ_min + c))² ≤ (1 + Δ(u₀)/c)²`, `c = c₀ + c₁ > 0`: close to one when `c` dominates `Δ`. -/
def direction_rho_iso : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n₀ n₁ : ℕ)
    (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E) (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (N₀ N₁ : Seminorm ℝ E)
    (u₀ : E) (c₀ c₁ Dmin Gsqmin : ℝ),
    ‖u₀‖ = 1 → (∀ u, N₀ u = c₀ * ‖u‖) → (∀ u, N₁ u = c₁ * ‖u‖) → 0 < c₀ + c₁ →
    IsGLB {r | ∃ u : E, ‖u‖ = 1 ∧ r = Deltafin a₀ x₀ a₁ x₁ u} Dmin →
    IsGLB {r | ∃ u : E, ‖u‖ = 1 ∧ r = (Deltafin a₀ x₀ a₁ x₁ u + N₀ u + N₁ u) ^ 2} Gsqmin →
      IsGreatest {r | ∃ u : E, ‖u‖ = 1 ∧ r = N₀ u + N₁ u} (c₀ + c₁) ∧
      IsLeast {r | ∃ u : E, ‖u‖ = 1 ∧ r = N₀ u + N₁ u} (c₀ + c₁) ∧
      (Deltafin a₀ x₀ a₁ x₁ u₀ + N₀ u₀ + N₁ u₀) ^ 2 / Gsqmin ≤
        ((Deltafin a₀ x₀ a₁ x₁ u₀ + (c₀ + c₁)) / (Dmin + (c₀ + c₁))) ^ 2 ∧
      (Deltafin a₀ x₀ a₁ x₁ u₀ + N₀ u₀ + N₁ u₀) ^ 2 / Gsqmin ≤
        (1 + Deltafin a₀ x₀ a₁ x₁ u₀ / (c₀ + c₁)) ^ 2

/-! ### robust equality paper 2 `lem:delta-inf`, general laws -/

/-- For probability laws `μ₀, μ₁` on a standard Borel space and a measurable rule `h`,
`W₂²(h#μ₀, h#μ₁) = min_{γ ∈ Π(μ₀, μ₁)} E_γ{h(X) − h(Y)}²`: every coupling costs at least `W₂²`, and some coupling costs
exactly `W₂²`. -/
def delta_inf_general : Prop :=
  ∀ (K : Type) [MeasurableSpace K] [StandardBorelSpace K] (μ₀ μ₁ : Measure K)
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] (h : K → ℝ), Measurable h →
    (∀ γ : Measure (K × K), IsCoupling γ μ₀ μ₁ →
      wassersteinEDist 2 (μ₀.map h) (μ₁.map h) ^ 2 ≤ ∫⁻ z, ENNReal.ofReal ((h z.1 - h z.2) ^ 2) ∂γ) ∧
    ∃ γ : Measure (K × K), IsCoupling γ μ₀ μ₁ ∧
      wassersteinEDist 2 (μ₀.map h) (μ₁.map h) ^ 2 = ∫⁻ z, ENNReal.ofReal ((h z.1 - h z.2) ^ 2) ∂γ

end Claims

end StatFormal.WaveP1d
