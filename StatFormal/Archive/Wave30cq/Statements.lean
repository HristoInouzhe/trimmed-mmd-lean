import StatFormal.Archive.SBFairness.Statements
import StatFormal.Archive.OTFD.Wave13a.Statements
import StatFormal.Archive.Wave28e.Statements
import StatFormal.Archive.Wave30z.Statements
import StatFormal.Archive.Wave29y.Statements

/-!
# FROZEN STATEMENTS — wave 30cq: five gaps of the 2026-10-27 fidelity audit (SB `thm:gaussian` (b) identity; otfd A
# `thm:sieve-breakdown` coherent limits without the atomless premise; paper 2 `prop:jointmin` structured equality;
# trimmed-mmd `cor:boundary-linear` (a) existence of `G_P, G_Q`; ICL `thm:score` normality with `s_{gθ} ∝ s_θ`)

Sources (read 2026-10-27; paths under `~/pCloudDrive/research-lines/`):
* SB `thm:gaussian` (b): `data-fairness-repair/schrodinger_bridge_fairness_repair.tex:2401-2441`, (b) `:2424-2428`:
  "(No crossing.) `v_0(t) − v_1(t) = (1−t)[(1−t)(σ_0² − σ_1²) + t(κ_{ε,0} − κ_{ε,1})]`, and since `σ ↦ κ_{ε,·}` is
  increasing, `sign(v_0(t) − v_1(t)) = sign(σ_0 − σ_1)` for all `t ∈ [0,1)`", with `eq:gaussmarg`
  `v_s(t) = (1−t)²σ_s² + t²τ² + t(1−t)κ_{ε,s}`, `κ_{ε,s} = √(ε² + 4σ_s²τ²)` (`:2405-2415`). The journal
  (`data-fairness-repair-journal/journal/supp/s_univariate.tex:368-395`, (b) `:391-395`; also the server branch
  `reframe/journal`, same file and lines) prints the identical text.
* otfd A `thm:sieve-breakdown` (`otfd/papers/A_sieves/supplement.tex:680-735`): "Let `μ` be a fixed law on `H`, put
  `μ_K = Π_K#μ` … Suppose `K_n → ∞`, `u ∈ H`, and … `eq:coherent-depth-approximation`. Then, if `K_n/n → 0`,
  `BP(q^H_{j_n,n}) → TD_H(u; μ)` (`eq:coherent-breakdown-limit`)"; proof Step 4 (`:784-809`) proves
  `TD(Π_K u; Π_K#μ) ↓ TD_H(u; μ)` (`eq:app-coherent-tukey-limit`) by dominated convergence, with NO hypothesis on
  `μ{⟨v, z − u⟩ = 0}` (Lean comment `:803`: "no atomless premise; DEFECTS #162").
* paper 2 `prop:jointmin` (`robust-equality-outcomes-under-distribution-shift/paper2/main.tex:305-316`, branch master):
  "For structured sets with a finite cell cover the same holds with the objective of `(P_η)` replaced by its cell bound
  (`prop:structured`), the infimum being over the multipliers and one coupling `γ_j` per cell; the cell bound dominates
  the objective of `(P_η)`, and for Wasserstein and anisotropic differential sets equals it when every `L_j(w)`
  vanishes."
* trimmed-mmd `cor:boundary-linear` (`trimmed-mmd/supplement.tex:2846-2890`): "suppose there are random vectors
  `G_P, G_Q ∈ ℝ^r` such that, almost surely, `H_P(f) = ⟨f, G_P⟩` for every `f ∈ −K°` with `‖f‖ ≤ 1` and
  `H_Q(g) = ⟨g, G_Q⟩` for every `g ∈ K°` with `‖g‖ ≤ 1`. Then `√N D̂ ⇒ ‖Π_{K°}(c_P G_P − c_Q G_Q)‖` … The hypothesis
  holds, with `G_P` a function of `𝔾_P` and `G_Q` of `𝔾_Q` (so independent), in each of the following cases. (a) A
  unique separating direction: `K° = {λν : λ ≥ 0}` for a unit vector `ν`" (`:2856-2861`).
* ICL `thm:score` (`context-distribution-ICL/paper/v4/sections/06_estimation.tex:179-196`) with `as:interior`
  (`supp/proofs_score.tex:105-111`): "every minimizer of `J` is obtained from `θ⋆` by a relabeling symmetry of the
  parametrization: an element `g` of a finite group `G` of continuous maps of `Θ` onto itself with `s_{gθ} ∝ s_θ` for
  every `θ ∈ Θ` … so that `J` and `J_{n,m}` … are `G`-invariant".
Imports the frozen statement files `SBFairness` (`v`, `kappa`), `OTFD/Wave13a` (`SieveSetting`, `liftQNorm`,
`tukeyDepthH`; through it `OTFD.Wave1` `tukeyDepth`, `truncK`, `OTFD.Wave6b` `empMeasure`, `OTFDR.Lift` `BP`),
`Wave28e` (`jointObjStruct`; through it `Wave20a` `ProbW`, `Polytope`, `Lcell`, `certStruct`), `Wave30z` (`Hfun`,
`IsLimitGP`, `SampleModel`, `Scaling`, `metricProj`; through it `Wave30v` `Ball`, `ballNeg`, `polarSet`, `coneHull`,
`TrimmedMMD` `region`, `Demp`) and `Wave29y` (`IsClosestRelabel`; through it `Wave28b` `jScore`, `jPop`, `Wave29h`
`hessMat`, `covMat`). No new definitions.

Covered (6 claims):
* `thm_gaussian_b_identity` — SB `thm:gaussian` (b), the identity
  `v_0(t) − v_1(t) = (1−t)[(1−t)(σ_0² − σ_1²) + t(κ_{ε,0} − κ_{ε,1})]` on the frozen `v`, `kappa` (the sign clause is
  the frozen `SBFairness` `thm_gaussian_b`).
* `coherent_tukey_limit_noatom` — otfd A `thm:sieve-breakdown`, `eq:app-coherent-tukey-limit`: the frozen Wave 13a
  `coherent_tukey_limit` with the premise `∀ v ≠ 0, μ{⟨v, z − u⟩ = 0} = 0` REMOVED.
* `sieve_bp_coherent_noatom` — otfd A `thm:sieve-breakdown`, `eq:coherent-breakdown-limit`: the frozen Wave 13a
  `sieve_bp_coherent` with the same premise REMOVED.
* `jointmin_struct_eq_zero` — paper 2 `prop:jointmin`, "equals it when every `L_j(w)` vanishes": under the hypotheses
  of the frozen Wave 28e `jointmin_struct_inf`, if `L_j(w) = 0` for every cell `j`, the infimum of the cell objective
  over `(λ₀, λ₁, (γ_j)_j)` EQUALS `R + η F̄(w)`, `F̄ = certStruct` the certified worst case of the structured model
  with anisotropic (Wasserstein: `G_s = I`) differential balls (the objective of `(P_η)` in the reading of the frozen
  `jointmin_struct_inf`, second conjunct).
* `boundary_ray_G` — trimmed-mmd `cor:boundary-linear` (a), "the hypothesis holds": under the hypotheses of the
  frozen Wave 30z `boundary_ray` (setting of `thm:boundary` (ii), `K° = {cν : c ≥ 0}`, `‖ν‖ = 1`) there are random
  vectors `G_P, G_Q : Ω' → E` with, almost surely, `H_P(−g) = ⟨−g, G_P⟩` and `H_Q(g) = ⟨g, G_Q⟩` for every
  `g ∈ K°` with `‖g‖ ≤ 1` (the corollary hypothesis in the form of the frozen `boundary_linear`, `f = −g` ranging over
  `−K° ∩ B`), and hence `r_k D̂ ⇒ ‖Π_{K°}(c_P G_P − c_Q G_Q)‖` (explicitly `G_P = −H_P(−ν) ν`, `G_Q = H_Q(ν) ν`).
* `score_relabel_normal_prop` — ICL `thm:score`, asymptotic normality modulo relabelling: the frozen Wave 29y
  `score_relabel_normal` with its premise `∀ g, ∀ θ ∈ T, s_{gθ} = s_θ` REPLACED by the printed
  `s_{gθ} ∝ s_θ`: `∀ g, ∀ θ ∈ T, ∃ c > 0, ∀ z, s_{gθ}(z) = c s_θ(z)` (`c` may depend on `g` and `θ`; the scores are
  positive, `s ≥ s_− > 0`, so `∝` with any real factor forces `c > 0`). All other premises and the conclusion are
  verbatim (including the frozen premise that the stabiliser of `θ⋆` acts by isometries).

Encodings (to be checked by the critic): exactly those of the frozen claims extended (`v`, `kappa` real-valued
closed forms; `TD`, `TD_H`, `Π_K = truncK`, `μ_K = μ.map (truncK b K)`, `BP`, `SieveSetting`; `jointObjStruct`,
`Lcell` in `ℝ≥0∞`, `certStruct`; `Hfun`, `ballNeg`, `polarSet (closure (coneHull (B − A)))` for `K°`, `metricProj`;
`jScore`, `jPop`, `IsClosestRelabel`, `hessMat`, `covMat`, `TendstoInDistribution`). In `boundary_ray_G` the existential
random vectors are arbitrary functions `Ω' → E` as in the frozen `boundary_vertex` (the corollary says "random
vectors"; their measurability is not part of the hypothesis of the frozen `boundary_linear`).

Generalisations (declared): `thm_gaussian_b_identity` holds for ALL real `ε, σ₀, σ₁, τ, t` (a ring identity; the
paper's setting is `ε > 0`, `τ > 0`, `σ_s > 0`, `t ∈ [0,1]`). `jointmin_struct_eq_zero` keeps the hypotheses of the
frozen `jointmin_struct_inf` (`β_s ≥ 0`, any `Θ`, any `p`) and adds only `∀ j, L_j(w) = 0`; no nonemptiness of `Θ`
is assumed (for `Θ = ∅` the cover forces `J = 0` and both sides equal `R`).

Not covered (declared): `cor:boundary-linear`: that `G_P` is a function of `𝔾_P` and `G_Q` of `𝔾_Q` (so
independent) in (a) and (b) (the `G_P` built here is `ω' ↦ −H_P(−ν)(𝔾 ω') ν`, which reads only the `P`-copy of
`𝔾 ω'`, but no measurable factorisation is stated); the isotropic chi-bar-square sentence beyond the ray.
ICL `thm:score`: normality when the stabiliser of `θ⋆` acts non-isometrically (frozen premise kept).

Junk audit: no division, `toReal` only as in the frozen `sieve_bp_coherent` (`TD_H(u; μ) ≤ 1 < ∞` for a probability
`μ` and `H ≠ 0`, as `b 0 ≠ 0`); `ℝ≥0∞` infima and suprema as in the frozen Wave 28e/20a definitions; `Hfun` is a real
`sInf` over the image of the nonempty compact argmin set (frozen Wave 30z, genuine); no new `Measure.map`.

Paper notes: none; all five printed clauses are true as printed (in the encodings above).

FROZEN 2026-10-27 — hashed in `certify/statements.lock` (with its imports) after the critic's review; AI agents must not edit it.
Critic (2026-10-27): ACCEPT (2), ACCEPT-WITH-NOTE (4); see certify/cards/wave30cq.md.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace Pointwise

namespace StatFormal.Wave30cq

namespace Claims

/-! ### SB `thm:gaussian` (b), the identity -/

open StatFormal.SBFairness (v kappa) in
/-- SB `thm:gaussian` (b), the identity: `v₀(t) − v₁(t) = (1−t)[(1−t)(σ₀² − σ₁²) + t(κ_{ε,0} − κ_{ε,1})]`, with
`v_s(t) = (1−t)²σ_s² + t²τ² + t(1−t)κ_{ε,s}` and `κ_{ε,s} = √(ε² + 4σ_s²τ²)` (frozen `SBFairness` `v`, `kappa`), for
all real `ε, σ₀, σ₁, τ, t` (generalisation of the printed setting `ε > 0`, `τ > 0`, `σ_s > 0`, `t ∈ [0,1]`). -/
def thm_gaussian_b_identity : Prop :=
  ∀ ε σ₀ σ₁ τ t : ℝ,
    v ε σ₀ τ t - v ε σ₁ τ t = (1 - t) * ((1 - t) * (σ₀ ^ 2 - σ₁ ^ 2) + t * (kappa ε σ₀ τ - kappa ε σ₁ τ))

/-! ### otfd A `thm:sieve-breakdown`, coherent limits without the atomless premise -/

open StatFormal.OTFD.Wave1 (tukeyDepth truncK) in
open StatFormal.OTFD.Wave13a (tukeyDepthH) in
/-- otfd A `thm:sieve-breakdown`, proof, eq. `app-coherent-tukey-limit`: `TD(Π_K u; Π_K#μ) ↓ TD_H(u; μ)` for EVERY
probability `μ` on `H` (the frozen Wave 13a `coherent_tukey_limit` without its premise
`∀ v ≠ 0, μ{⟨v, z − u⟩ = 0} = 0`). -/
def coherent_tukey_limit_noatom : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    [BorelSpace H] (b : HilbertBasis ℕ ℝ H) (μ : Measure H) [IsProbabilityMeasure μ] (u : H),
      Antitone (fun K => tukeyDepth (μ.map (truncK b (K + 1))) (truncK b (K + 1) u)) ∧
      Tendsto (fun K => tukeyDepth (μ.map (truncK b K)) (truncK b K u)) atTop (𝓝 (tukeyDepthH μ u))

open StatFormal.OTFD.Wave1 (tukeyDepth truncK) in
open StatFormal.OTFD.Wave6b (empMeasure) in
open StatFormal.OTFDR.Lift (BP) in
open StatFormal.OTFD.Wave13a (tukeyDepthH SieveSetting liftQNorm) in
/-- otfd A `thm:sieve-breakdown`, eq. `coherent-breakdown-limit`: under coherent depth approximation
(`eq:coherent-depth-approximation`), `K_n → ∞` and `K_n/n → 0`, `BP(q^H_{j_n,n}) → TD_H(u; μ)` for EVERY probability
`μ` on `H` (the frozen Wave 13a `sieve_bp_coherent` without its premise `∀ v ≠ 0, μ{⟨v, z − u⟩ = 0} = 0`). -/
def sieve_bp_coherent_noatom : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    [BorelSpace H] (b : HilbertBasis ℕ ℝ H) (μ : Measure H) [IsProbabilityMeasure μ] (u : H)
    (Kn : ℕ → ℕ) (uu : ∀ n, Fin (n + 1) → EuclideanSpace ℝ (Fin (Kn n))) (X : ∀ n, Fin (n + 1) → H)
    (j : ∀ n, Fin (n + 1)),
    (∀ n, SieveSetting (⇑b) (Kn n) (n + 1) (uu n) (X n)) → Tendsto Kn atTop atTop →
    Tendsto (fun n => |(tukeyDepth (empMeasure (uu n)) (uu n (j n))).toReal -
        (tukeyDepth (μ.map (truncK b (Kn n))) (truncK b (Kn n) u)).toReal|) atTop (𝓝 0) →
    Tendsto (fun n => (Kn n : ℝ) / (n + 1)) atTop (𝓝 0) →
      Tendsto (fun n => BP (liftQNorm (⇑b) (Kn n) (uu n) (j n)) (X n)) atTop
        (𝓝 (tukeyDepthH μ u).toReal)

/-! ### paper 2 `prop:jointmin`, the structured equality when every `L_j(w)` vanishes -/

open StatFormal.RobustEquality.Paper2.Seminorm StatFormal.Wave20a StatFormal.Wave28e in
/-- paper 2 `prop:jointmin`, structured sets with a finite cell cover, "for Wasserstein and anisotropic differential
sets equals it when every `L_j(w)` vanishes": under the hypotheses of the frozen Wave 28e `jointmin_struct_inf`, if
`L_j(w) = 0` for every cell `j`, the infimum of the cell objective over `(λ₀, λ₁, (γ_j)_j)` equals the objective of
`(P_η)` for the structured model, `R + η sup_θ inf_λ F̄_θ(w; λ)` (`certStruct`). -/
def jointmin_struct_eq_zero : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
    (Θ : Type) (n₀ n₁ J : ℕ) (G₀ G₁ : E ≃L[ℝ] E) (β₀ β₁ : ℝ) (a₀ : Fin n₀ → ℝ) (x₀ : Fin n₀ → E)
    (a₁ : Fin n₁ → ℝ) (x₁ : Fin n₁ → E) (A : Θ → E →L[ℝ] E) (b : Θ → E) (cell : Fin J → Set Θ) (θc : Fin J → Θ)
    (p w : E) (Rh η : ℝ),
    ProbW a₀ → ProbW a₁ → 0 ≤ β₀ → 0 ≤ β₁ → 0 < η → (∀ θ, ∃ j, θ ∈ cell j) → (∀ j, θc j ∈ cell j) →
    (∀ j, Lcell a₀ x₀ a₁ x₁ p A (cell j) (θc j) w = 0) →
      (⨅ (lam₀ : Set.Ioi (0 : ℝ)) (lam₁ : Set.Ioi (0 : ℝ)) (γ : Fin J → Polytope a₀ a₁),
          jointObjStruct G₀ G₁ β₀ β₁ a₀ x₀ a₁ x₁ A cell θc p w Rh η lam₀ lam₁ (fun j => γ j)) =
        ENNReal.ofReal Rh + ENNReal.ofReal η * certStruct G₀ G₁ β₀ β₁ a₀ x₀ a₁ x₁ A b w

/-! ### trimmed-mmd `cor:boundary-linear` (a), existence of `G_P`, `G_Q` -/

open StatFormal.TrimmedMMD.Concentration (region) in
open StatFormal.TrimmedMMD.Unconditional (Demp) in
open StatFormal.Wave30v (Ball ballNeg polarSet coneHull) in
open StatFormal.Wave30z in
/-- trimmed-mmd `cor:boundary-linear` (a), "The hypothesis holds … (a) A unique separating direction": under the
hypotheses of the frozen Wave 30z `boundary_ray` (setting of `thm:boundary` (ii), `K° = {cν : c ≥ 0}` for a unit
vector `ν`), there are random vectors `G_P, G_Q` such that almost surely `H_P(f) = ⟨f, G_P⟩` for every `f ∈ −K°`,
`‖f‖ ≤ 1` (written `f = −g`, `g ∈ K°`) and `H_Q(g) = ⟨g, G_Q⟩` for every `g ∈ K°`, `‖g‖ ≤ 1`; hence (main statement)
`r_k D̂ ⇒ ‖Π_{K°}(c_P G_P − c_Q G_Q)‖`. -/
def boundary_ray_G : Prop :=
  ∀ (𝒳 E : Type) [MeasurableSpace 𝒳] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (φ : 𝒳 → E) (κ α : ℝ) (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ η : ℕ → Ω → 𝒳)
    (n m : ℕ → ℕ) (r : ℕ → ℝ) (cP cQ : ℝ)
    (Ω' : Type) [MeasurableSpace Ω'] (μ' : Measure Ω') [IsProbabilityMeasure μ'] (𝔾 : Ω' → C(Idx2 E κ, ℝ))
    (ν : Ball E),
    StronglyMeasurable φ → (∀ x, ‖φ x‖ ≤ κ) → 0 ≤ α → α < 1 → SampleModel P Q μ ξ η → Scaling n m r cP cQ →
    IsLimitGP φ P Q 1 1 κ μ' 𝔾 → (region φ α P ∩ region φ α Q).Nonempty → ‖(ν : E)‖ = 1 →
    polarSet (closure (coneHull (region φ α Q - region φ α P))) = {x | ∃ c : ℝ, 0 ≤ c ∧ x = c • (ν : E)} →
      ∃ GP GQ : Ω' → E,
        (∀ᵐ ω' ∂μ', ∀ g : Ball E, (g : E) ∈ polarSet (closure (coneHull (region φ α Q - region φ α P))) →
          Hfun φ α P κ Sum.inl (𝔾 ω') (ballNeg g) = ⟪-(g : E), GP ω'⟫ ∧ Hfun φ α Q κ Sum.inr (𝔾 ω') g = ⟪(g : E), GQ ω'⟫) ∧
        TendstoInDistribution
          (fun k ω => r k * Demp φ (fun i : Fin (n k) => ξ i ω) (fun j : Fin (m k) => η j ω) α)
          atTop (fun ω' => ‖metricProj (polarSet (closure (coneHull (region φ α Q - region φ α P))))
            (cP • GP ω' - cQ • GQ ω')‖) (fun _ => μ) μ'

/-! ### ICL `thm:score`, normality modulo relabelling with `s_{gθ} ∝ s_θ` -/

open StatFormal.Wave28b (jScore jPop) in
open StatFormal.Wave29h (hessMat covMat) in
open StatFormal.Wave29y (IsClosestRelabel) in
/-- ICL `thm:score`, asymptotic normality modulo a finite relabelling group, with the printed `as:interior`
condition `s_{gθ} ∝ s_θ`: the frozen Wave 29y `score_relabel_normal` with its premise `∀ g, ∀ θ ∈ T, s_{gθ} = s_θ`
replaced by `∀ g, ∀ θ ∈ T, ∃ c > 0, ∀ z, s_{gθ}(z) = c s_θ(z)`; every other premise (including isometric action of the
stabiliser of `θ⋆`) and the conclusion are verbatim: the closest relabellings `θ̃_n` of the exact minimisers `θ̂_n`
are exact minimisers of `J_{n,m}` over `T`, and `√n(θ̃_n − θ⋆) ⇝ N(0, V⁻¹(Σ_pool + κ⁻¹Σ_val)V⁻¹)`. -/
def score_relabel_normal_prop : Prop :=
  ∀ (p M : ℕ) (sm sp BL Kmin Kmax κ lc lK δ : ℝ) (θs : EuclideanSpace ℝ (Fin p))
    (T : Set (EuclideanSpace ℝ (Fin p))) (Z Ω G : Type) [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] [MeasurableSpace Ω] [Group G] [Fintype G] [MulAction G (EuclideanSpace ℝ (Fin p))]
    (P : Measure Ω) [IsProbabilityMeasure P] (P0 : Measure Z) (X Y : ℕ → Ω → Z)
    (m : ℕ → ℕ) (s : EuclideanSpace ℝ (Fin p) → Z → ℝ)
    (s1 : EuclideanSpace ℝ (Fin p) → Z → EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ)
    (s2 : EuclideanSpace ℝ (Fin p) → Z → EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ)
    (L : Z → (Fin M → Z) → ℝ) (K : Z → Z → ℝ) (lcn lKn : ℕ → ℝ) (θh θr : ℕ → Ω → EuclideanSpace ℝ (Fin p)),
    (∀ g : G, Continuous (fun θ : EuclideanSpace ℝ (Fin p) => g • θ)) →
    (∀ g : G, g • θs = θs → Isometry (fun θ : EuclideanSpace ℝ (Fin p) => g • θ)) → (∀ g : G, ∀ θ ∈ T, g • θ ∈ T) →
    (∀ g : G, ∀ θ ∈ T, ∃ c : ℝ, 0 < c ∧ ∀ z, s (g • θ) z = c * s θ z) →
    1 ≤ M → 0 < sm → (∀ t x, sm ≤ s t x ∧ s t x ≤ sp) → IsCompact T →
    ContinuousOn (Function.uncurry s) (T ×ˢ univ) → 0 < δ → Metric.ball θs δ ⊆ T →
    ContinuousOn (Function.uncurry s1) (Metric.ball θs δ ×ˢ univ) →
    ContinuousOn (Function.uncurry s2) (Metric.ball θs δ ×ˢ univ) →
    (∀ x, ∀ t ∈ Metric.ball θs δ, HasFDerivAt (fun t => s t x) (s1 t x) t ∧
      HasFDerivAt (fun t => s1 t x) (s2 t x) t) →
    Continuous (Function.uncurry L) → (∀ x t, 0 ≤ L x t ∧ L x t ≤ BL) →
    (∀ x t (σ : Equiv.Perm (Fin M)), L x (t ∘ σ) = L x t) →
    Continuous (Function.uncurry K) → 0 < Kmin → (∀ x y, Kmin ≤ K x y ∧ K x y ≤ Kmax) →
    (∀ n, 0 ≤ lcn n) → Tendsto lcn atTop (𝓝 lc) → Tendsto lKn atTop (𝓝 lK) →
    Tendsto (fun n : ℕ => √(n : ℝ) * (lcn n - lc)) atTop (𝓝 0) →
    Tendsto (fun n : ℕ => √(n : ℝ) * (lKn n - lK)) atTop (𝓝 0) →
    0 < κ → Tendsto (fun n => (m n : ℝ) / n) atTop (𝓝 κ) →
    (∀ θ ∈ T, (∀ θ' ∈ T, jPop P0 s L K lc lK θ ≤ jPop P0 s L K lc lK θ') → ∃ g : G, θ = g • θs) →
    (hessMat (jPop P0 s L K lc lK) θs).PosDef →
    (∀ n, Measurable (θh n)) →
    (∀ n ω, θh n ω ∈ T ∧ ∀ t ∈ T, jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n)
      (lKn n) (θh n ω) ≤ jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n) t) →
    (∀ n, Measurable (θr n)) → (∀ n ω, IsClosestRelabel G θs (θh n ω) (θr n ω)) →
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) → iIndepFun X P → iIndepFun Y P →
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) P → (∀ i, P.map (X i) = P0) → (∀ i, P.map (Y i) = P0) →
      (∀ n ω, θr n ω ∈ T ∧ ∀ t ∈ T, jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n)
        (lKn n) (θr n ω) ≤ jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n) t) ∧
      (∀ᶠ n in atTop, ∀ ω, DifferentiableAt ℝ
        (jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n)) θs) ∧
      ∃ ψp ψv : Z → EuclideanSpace ℝ (Fin p), Measurable ψp ∧ Measurable ψv ∧
        (∃ C, ∀ z, ‖ψp z‖ ≤ C ∧ ‖ψv z‖ ≤ C) ∧ ∫ z, ψp z ∂P0 = 0 ∧ ∫ z, ψv z ∂P0 = 0 ∧
        TendstoInMeasure P (fun (n : ℕ) ω =>
          √(n : ℝ) • gradient (jScore s L K (fun i => X i ω) (fun i => Y i ω) n (m n) (lcn n) (lKn n)) θs -
            ((√(n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, ψp (X i ω) +
              (√(n : ℝ) / m n) • ∑ i ∈ Finset.range (m n), ψv (Y i ω))) atTop 0 ∧
        ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
          (G' : Ω' → EuclideanSpace ℝ (Fin p)),
          HasLaw G' (multivariateGaussian 0 ((hessMat (jPop P0 s L K lc lK) θs)⁻¹ *
            (covMat P0 ψp + κ⁻¹ • covMat P0 ψv) * (hessMat (jPop P0 s L K lc lK) θs)⁻¹)) P' →
          TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) • (θr n ω - θs)) atTop G' (fun _ => P) P'

end Claims

end StatFormal.Wave30cq
