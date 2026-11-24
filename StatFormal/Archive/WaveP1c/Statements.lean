import StatFormal.Archive.Wave22c.Statements
import StatFormal.Archive.SBFairness.Decay.Statements
import StatFormal.Archive.Wave23c.Statements
import Mathlib.Probability.Distributions.Gamma
import StatFormal.Archive.OTFD.Wave12a.Statements
import Mathlib.Probability.ProductMeasure

/-!
# FROZEN STATEMENTS — wave P1c (`PARTIAL_AUDIT.md`, Wave 1c: small analytic gaps): SB `thm:gaussian` (eq:gaussF,
# (a), (d)), `prop:eps2` (the `W₂` equality), `cor:tdelta` (attainment); robust equality JASA `prop:ep-gauss` (the
# Gaussian integral); otfd R `cor:gaussian-t` (the depth identities), `thm:peaked-cube` (the law on `H`)

Sources (verbatim in `lean-formalisation/inventory/extracted/{data-fairness-repair,robust-equality-jasa,otfd-R_robustness}.md`;
current text read 2026-10-16, SB revised 2026-10-16):
* SB `thm:gaussian` (`data-fairness-repair/schrodinger_bridge_fairness_repair.tex:2497-2540`), `eq:gaussmarg`, `eq:gaussF`,
  with `F_ε(t) = W₂(μ^ε_{0,t}, μ^ε_{1,t})` and the costs `C^flow`, `C^sto` (`:2349-2376`, `prop:excess`). Frozen partial
  claims: `SBFairness.thm_gaussian_b`, `thm_gaussian_c` (closed forms only); certified inputs: Wave 22c `gaussmarg_endpoint`,
  `gaussPlan_marginals`, `gaussPlan_cov`, Wave 18b `excess_sto_cost`, `w2_gauss_same_mean` (route lemma).
* SB `prop:eps2` (`:2589-2600`). Frozen partial claim: `SBFairness.prop_eps2_bounds` (the two inequalities on the closed
  form); `μ^0_{s,t}` as in the frozen Wave 22c `noisefree_bridge_exact_plan` (comonotone plan, `c_0 = σ_sτ`).
* SB `cor:tdelta` (`:2455-2463`), with `thm:decay`, `def:glued` and `prop:mixture` (`:457`). Frozen partial claim:
  `SBFairness.Decay.tdelta_bound` (the bound only); same frozen `bridge`.
* JASA `prop:ep-gauss` (`robust-equality-outcomes-under-distribution-shift/jasa/supp_eps.tex:331-342`, proof `:344-349`),
  with the notation header (`:6-17`: `c = |x−y|²`, `R_ε`, `K^ε_{x₀}`, `f_h`, `T_ε(λ; r)`) and `𝖡_ε` (`prop:ep-blur`).
  Frozen partial claims: Wave 11a `gauss_xstar`, `gauss_inf`, `gauss_bounds`, `gauss_root` (from the formula `Tgauss`).
* otfd R `cor:gaussian-t` (`otfd/papers/R_robustness/sections/s3_infinite.tex:74-85`), with `thm:elliptical` (`:56-72`).
  Frozen partial claims: Wave 24e `gaussian_t_moment`, `gaussian_t_tail` (there `F_{t_ν}` is defined as `F₁`); certified
  input: Wave 23c `elliptical_depth`.
* otfd R `thm:peaked-cube` (`otfd/papers/R_robustness/sections/s6_references.tex:127-145`, proof `appendix_b.tex:156-`).
  Frozen partial claims: OTFD Wave 12a `peaked_*` (the truncations `μ_K`); certified inputs: Wave 12a coordinate lemmas,
  Wave 20a `app_block_Pl_class`, the proof pattern of Wave 24d `refs_Pl_cubic`.
Imports the frozen `Wave22c` (`gaussPlan`; through it Wave 18b, `SBFairness` `cEps`, `kappa`, `v`, `geo`, Wave 4b
`endpointMixture1`, Wave 9b `stoPlan`, `qcost`, Wave 11a `Tgauss`), `SBFairness/Decay` (`bridge`), `Wave23c` (`ellF1`,
`cmNorm`, `ellLaw`, `EllSetting`; OTFD Wave 13a `tukeyDepthH`) and `OTFD/Wave12a` (`peakedCoord`, `peakedLaw`; OTFD Wave 1
`truncK`, `PellClass`) statements, not copied; Mathlib otherwise.

Covered (all NEW claims for missing clauses; no frozen claim is restated):
* `thm:gaussian`: `gaussian_F` (eq:gaussF, `ε ≥ 0`, `t ∈ [0,1]`), `gaussian_a` ((a): the means differ by exactly
  `(1−t)(a₀−a₁)`), `gaussian_d_flow` ((d), `C^flow_s = W₂²(R_s, μ^ε_{s,t})`), `gaussian_d_sto` ((d), `C^sto_s = t²M_s +
  εt(1−t)` with `M_s ≥ 0`).
* `prop:eps2`: `eps2_W2` (`W₂(μ^ε_{s,t}, μ^0_{s,t}) = √v_s(t) − ((1−t)σ_s + tτ)` for every `t ∈ [0,1]`, and
  `sup_t W₂ ≤ ε²/(32σ_sτ min(σ_s,τ))`).
* `cor:tdelta`: `tdelta_attained` (`{t ∈ [0,1] : F(t) ≤ δ}` is nonempty and contains its infimum, every `δ ≥ 0`).
* `prop:ep-gauss`: `ep_gauss_kernel` (`K^ε_{x₀} = N(x₀, (ε/2)I)`, `𝖡_ε = |w|²ε/2`), `ep_gauss_T` (the `T_ε` formula
  from the header definitions, with positive finite integrals, for every centre `n⁻¹Σδ_{x_i}`).
* `cor:gaussian-t`: `gaussian_t_gauss_TD` (`TD_H = Φ(−‖x‖_CM)`), `gaussian_t_student_F` (`√W ξ ∼ t_ν`: `F₁ = F_{t_ν}`, the
  Student distribution function), `gaussian_t_student_TD` (`TD_H = F_{t_ν}(−‖x‖_CM)`).
* `thm:peaked-cube`: `peakedH_basic` (probability, Hilbert-cube support, symmetric, atomless), `peakedH_coherent`
  (`Π_K#μ = μ_K`, the product of the coordinate laws), `peakedH_Pl` (`μ ∈ 𝒫^ℓ(H)`).

Not covered (declared):
* `thm:gaussian`/`prop:eps2`: `eq:gaussmarg` as an OT identity — that the entropic plan `π*_ε(N(a,σ²), N(a⋆,τ²))` is the
  Gaussian plan with cross-covariance `c_ε` and that the Schrödinger-bridge marginal is the mixture (`prop:mixture`
  path space); and that the comonotone plan is `π*_0` (GAUSS-EOT). Everything here is for the endpoint mixtures of the
  Gaussian plans, as in the frozen Wave 22c `noisefree_*_plan`.
* SB `prop:twopoint`: the minimax lower bound (UNPROVED in the manuscript: the only proof is "Proof of eq:modulus",
  frozen `modulus_corrected`). For `d = 1` it holds as printed, for every estimator: `lem:excess` pointwise; on
  `W₂(R_0,ω) ≥ √d` the excess is `≥ d/2 − J⋆ ≥ d/4 > Δ_n²/32`, otherwise `M = max_s W₂(R_s,ω) < 2√d`, which is the
  printed `4M` with `M = √d` (no cube-valued estimators needed); then Le Cam (overlap `≥ 1 − TV ≥ ½`) with `lem:qgrowth`
  (i) (`c = 1`) and `W₂(ν⋆_μ, ν⋆_μ') = ½W₂(μ, μ')` (quantile averages) gives `Δ_n²/32`. For `d ≥ 2` the step
  `inf_ω [F_μ(ω) − F_μ(ν⋆_μ) + F_μ'(ω) − F_μ'(ν⋆_μ')] ≥ W₂²(μ, μ')/8` for near-extremal pairs of `Δ_n` is unproved; via
  quadratic growth it needs `c = 1`, which `rem:qgrowth-fails` refutes in general (and which fails even with an
  isotropic known group: Gaussian `A_0 = I`, `A_1` of condition number `100`, `c ≈ 0.89`, critic numerics). Not
  encoded here (measurable estimators and the experiment are not built).
* `cor:gaussian-t`: `E‖X‖² = E W · tr Σ` (stays as in Wave 24e).
* `thm:peaked-cube`: nothing further (the content and robustness clauses are the frozen Wave 12a claims on `μ_K`).

Encodings (to be checked by the critic):
* SB: `μ^ε_{s,t} = endpointMixture1 ε t (gaussPlan a_s σ_s a⋆ τ (cEps ε σ_s τ))`, `μ^0_{s,t}` the same at `ε = 0`
  (`c_0 = σ_sτ`: the law of `(1−t)(a_s + σ_sU) + t(a⋆ + τU)`, the monotone displacement interpolant), `R_s =
  gaussianReal a_s σ_s²`; `W₂` = Tau Ceti `wassersteinEDist 2`; squared identities in `ℝ≥0∞` with `ofReal` of a
  nonnegative right side; `σ_s, τ > 0`. `C^sto_s` = frozen `qcost (stoPlan ε t π_s)` (Wave 9b; `prop:excess`).
* `cor:tdelta`: the frozen `bridge` (mixture form of `prop:mixture`) of arbitrary probability plans on `ℝᵈ × ℝᵈ` with a
  common second marginal (generalisation of the entropic plans), `δ ≥ 0` (paper: any level), `inf` = `sInf` on `ℝ`.
* `prop:ep-gauss`: `ν` = Lebesgue measure on `EuclideanSpace ℝ (Fin d)` (as the paper: not normalised; only `r − R_ε`
  matters), `K^ε_{x₀}` = Mathlib `volume.tilted (−c(x₀,·)/ε)`, `N(x₀, (ε/2)I)` = law of `x₀ + √(ε/2) Z`, `Z ∼
  stdGaussian`; `h(x) = ⟨w,x⟩ + b`; `E_ν` = Bochner `∫ dν`, `E_{P̂}` the average over the anchors `x_i`, `n ≥ 1`;
  `λ > |w|²` as in the frozen `gauss_inf`.
* `cor:gaussian-t`: `t_ν` density written out (`studentPDF`), `F_{t_ν} = studentCDF` (Bochner integral over `(−∞,s]`);
  `W ∼ InvGamma(ν/2,ν/2)` as `1/W ∼ gammaMeasure (ν/2) (ν/2)` (as in Wave 24e); Gaussian case: the hypotheses of
  `EllSetting` on `G` alone (`W ≡ 1`), law `𝓛(G)`.
* `thm:peaked-cube`: `H` any separable real Hilbert space with Hilbert basis `e` (paper `𝓗 = ℓ²`); the coordinate `k ≥ 1`
  is index `j = k − 1`; `μ = (⊗_j peakedCoord L₀ a (j+1)).map seriesPt` with `seriesPt v = Σ' v_j e_j` (Mathlib
  `infinitePi`, `tsum`); "product, coherent" as `Π_K#μ = peakedLaw L₀ a K` for all `K` (the frozen finite-dimensional
  product law); `𝒫^ℓ(H)` = frozen `PellClass`; atomless as `μ{x} = 0`.

Critic notes:
* All 14 claims are proved in `WaveP1c/Route{SBGauss,Tdelta,Student,EpGauss,PeakedH}.lean` (library lemma file
  `RouteGaussW2.lean`: `W₂²(N(m₁,v), N(m₂,w)) = (m₁ − m₂)² + (√v − √w)²`); dependencies: propext, Classical.choice, Quot.sound only.
  No frozen statement is restated; no premise is removed from a frozen claim.
* Junk values: `v_s(t) > 0` on `[0,1]` for every `ε`, `√v ≥ (1−t)σ + tτ`, so every `ofReal` has a nonnegative argument;
  `ep_gauss_T` asserts positivity of every integral, so neither `∫` nor `log` is a junk `0`; `peakedLawH` is shown to be
  a probability measure (`infinitePi` and `Measure.map` are not junk); `studentPDF` is integrable on `(−∞, s]` (route);
  the `sInf` of `tdelta_attained` is of a nonempty set bounded below.
* Observations: (1) eq:gaussF, (a), (d) hold for every `ε ≥ 0` (paper `ε > 0`). (2) `peakedH_*` use `L₀ > 0` only
  (`a > 1` is not needed for the law on `H`). (3) `tdelta_attained` needs neither second moments nor `G_ε < ∞`
  (weak lower semicontinuity of `W₂`). (4) No statement was found false.

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TauCeti
open scoped ENNReal NNReal

namespace StatFormal.WaveP1c

/-! ### otfd R: the Student law -/

/-- The Student `t_ν` density `Γ((ν+1)/2)/(√(νπ) Γ(ν/2)) · (1 + x²/ν)^{−(ν+1)/2}`. -/
def studentPDF (ν x : ℝ) : ℝ :=
  Real.Gamma ((ν + 1) / 2) / (√(ν * Real.pi) * Real.Gamma (ν / 2)) * (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2))

/-- The Student distribution function `F_{t_ν}(s) = ∫_{−∞}^s t_ν`. -/
def studentCDF (ν s : ℝ) : ℝ := ∫ x in Iic s, studentPDF ν x

/-! ### otfd R `thm:peaked-cube`: the law on `H` -/

section PeakedH
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]

/-- The point `Σ_k v_k e_k` of `H` (`∑'`; a genuine sum whenever `Σ_k v_k² < ∞`, in particular on the Hilbert cube). -/
def seriesPt (e : HilbertBasis ℕ ℝ H) (v : ℕ → ℝ) : H := ∑' k, v k • e k

/-- The peaked-cube law on `H`: `μ = 𝓛(Σ_{k≥1} (C_k/(kL_k)) e_k)`, the coordinates `C_k/(kL_k)` independent with the frozen
laws `peakedCoord L₀ a k` (index `j = k − 1`; `Measure.infinitePi` is the product law). -/
def peakedLawH (e : HilbertBasis ℕ ℝ H) (L₀ a : ℝ) : Measure H :=
  (Measure.infinitePi fun j : ℕ => StatFormal.OTFD.Wave12a.peakedCoord L₀ a (j + 1)).map (seriesPt e)

end PeakedH

namespace Claims

open StatFormal.SBFairness (cEps kappa v geo)
open StatFormal.Wave22c (gaussPlan)
open StatFormal.Wave4b (endpointMixture1)
open StatFormal.Wave9b (stoPlan qcost)

/-! ### SB `thm:gaussian`, `prop:eps2` -/

/-- `eq:gaussF`: with `μ^ε_{s,t}` the endpoint mixture of the Gaussian plan with cross-covariance `c_ε(σ_s,τ)`
between `R_s = N(a_s,σ_s²)` and `ν = N(a⋆,τ²)`,
`F_ε(t)² = W₂²(μ^ε_{0,t}, μ^ε_{1,t}) = (1−t)²(a₀−a₁)² + (√v₀(t) − √v₁(t))²`, every `ε ≥ 0`, `t ∈ [0,1]`. -/
def gaussian_F : Prop :=
  ∀ ε σ₀ σ₁ τ a₀ a₁ astar t : ℝ, 0 ≤ ε → 0 < σ₀ → 0 < σ₁ → 0 < τ → t ∈ Icc (0 : ℝ) 1 →
    wassersteinEDist 2 (endpointMixture1 ε t (gaussPlan a₀ σ₀ astar τ (cEps ε σ₀ τ)))
        (endpointMixture1 ε t (gaussPlan a₁ σ₁ astar τ (cEps ε σ₁ τ))) ^ 2 =
      ENNReal.ofReal ((1 - t) ^ 2 * (a₀ - a₁) ^ 2 + (√(v ε σ₀ τ t) - √(v ε σ₁ τ t)) ^ 2)

/-- `thm:gaussian` (a): the mean component of `eq:gaussF`. The means of `μ^ε_{0,t}` and `μ^ε_{1,t}` differ by exactly
`(1−t)(a₀−a₁)`, for every `ε ≥ 0`: the mean gap decays exactly linearly. -/
def gaussian_a : Prop :=
  ∀ ε σ₀ σ₁ τ a₀ a₁ astar t : ℝ, 0 ≤ ε → 0 < σ₀ → 0 < σ₁ → 0 < τ → t ∈ Icc (0 : ℝ) 1 →
    ∫ x, x ∂(endpointMixture1 ε t (gaussPlan a₀ σ₀ astar τ (cEps ε σ₀ τ))) -
        ∫ x, x ∂(endpointMixture1 ε t (gaussPlan a₁ σ₁ astar τ (cEps ε σ₁ τ))) = (1 - t) * (a₀ - a₁)

/-- `thm:gaussian` (d), flow cost: `C^flow_s(t) = W₂²(R_s, μ^ε_{s,t}) = t²(a⋆ − a_s)² + (√v_s(t) − σ_s)²`. -/
def gaussian_d_flow : Prop :=
  ∀ ε σ τ a astar t : ℝ, 0 ≤ ε → 0 < σ → 0 < τ → t ∈ Icc (0 : ℝ) 1 →
    wassersteinEDist 2 (gaussianReal a (σ ^ 2).toNNReal) (endpointMixture1 ε t (gaussPlan a σ astar τ (cEps ε σ τ))) ^ 2 =
      ENNReal.ofReal (t ^ 2 * (astar - a) ^ 2 + (√(v ε σ τ t) - σ) ^ 2)

/-- `thm:gaussian` (d), stochastic cost: for the stochastic realisation over the Gaussian plan,
`C^sto_s(t) = E(X_t − X_0)² = t² M_s + εt(1−t)`, `M_s = (a_s − a⋆)² + σ_s² + τ² − 2c_ε(σ_s,τ) ≥ 0`. -/
def gaussian_d_sto : Prop :=
  ∀ ε σ τ a astar t : ℝ, 0 ≤ ε → 0 < σ → 0 < τ → t ∈ Icc (0 : ℝ) 1 →
    0 ≤ (a - astar) ^ 2 + σ ^ 2 + τ ^ 2 - 2 * cEps ε σ τ ∧
      qcost (stoPlan ε t (gaussPlan a σ astar τ (cEps ε σ τ))) =
        ENNReal.ofReal (t ^ 2 * ((a - astar) ^ 2 + σ ^ 2 + τ ^ 2 - 2 * cEps ε σ τ) + ε * t * (1 - t))

/-- `prop:eps2`, the `W₂` statement: with `μ^0_{s,t}` the endpoint mixture of the comonotone plan (`c_0 = σ_sτ`, the
displacement interpolant), for all `t ∈ [0,1]`, `W₂(μ^ε_{s,t}, μ^0_{s,t}) = √v_s(t) − ((1−t)σ_s + tτ)`, and
`sup_{t∈[0,1]} W₂(μ^ε_{s,t}, μ^0_{s,t}) ≤ ε²/(32σ_sτ min(σ_s,τ)) = O(ε²)`. -/
def eps2_W2 : Prop :=
  ∀ ε σ τ a astar : ℝ, 0 < ε → 0 < σ → 0 < τ →
    (∀ t ∈ Icc (0 : ℝ) 1,
      wassersteinEDist 2 (endpointMixture1 ε t (gaussPlan a σ astar τ (cEps ε σ τ)))
          (endpointMixture1 0 t (gaussPlan a σ astar τ (cEps 0 σ τ))) =
        ENNReal.ofReal (√(v ε σ τ t) - geo σ τ t)) ∧
    ⨆ t ∈ Icc (0 : ℝ) 1, wassersteinEDist 2 (endpointMixture1 ε t (gaussPlan a σ astar τ (cEps ε σ τ)))
          (endpointMixture1 0 t (gaussPlan a σ astar τ (cEps 0 σ τ))) ≤
      ENNReal.ofReal (ε ^ 2 / (32 * σ * τ * min σ τ))

/-! ### SB `cor:tdelta` -/

open StatFormal.SBFairness.Decay (bridge Gsq)

/-- `cor:tdelta`, well-definedness and attainment: with `F(t) = W₂(μ_{0,t}, μ_{1,t})`, the set
`{t ∈ [0,1] : F(t) ≤ δ}` is nonempty and contains its infimum `t_δ`, for every `δ ≥ 0`. -/
def tdelta_attained : Prop :=
  ∀ (d : ℕ) (π₀ π₁ : Measure ((EuclideanSpace ℝ (Fin d)) × (EuclideanSpace ℝ (Fin d))))
    [IsProbabilityMeasure π₀] [IsProbabilityMeasure π₁] (ε δ : ℝ), π₀.snd = π₁.snd → 0 ≤ ε → 0 ≤ δ →
      {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ wassersteinEDist 2 (bridge π₀ ε t) (bridge π₁ ε t) ≤ ENNReal.ofReal δ}.Nonempty ∧
      sInf {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ wassersteinEDist 2 (bridge π₀ ε t) (bridge π₁ ε t) ≤ ENNReal.ofReal δ} ∈
        {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ wassersteinEDist 2 (bridge π₀ ε t) (bridge π₁ ε t) ≤ ENNReal.ofReal δ}

/-! ### otfd R `cor:gaussian-t` -/

open StatFormal.Wave23c (ellF1 cmNorm ellLaw EllSetting)
open StatFormal.OTFD.Wave13a (tukeyDepthH)
open scoped RealInnerProductSpace

/-- `cor:gaussian-t`, Gaussian reference (`W ≡ 1`): for a centred Gaussian `G` on `H` with injective covariance,
`TD_H(x; 𝓛(G)) = Φ(−‖x‖_CM)` (and `0` off the Cameron–Martin space). -/
def gaussian_t_gauss_TD : Prop :=
  ∀ (Ω H : Type) [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
    [BorelSpace H] [Nontrivial H] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (G : Ω → H),
    Measurable G → IsGaussian (Pr.map G) → (∀ v, ∫ ω, ⟪v, G ω⟫ ∂Pr = 0) →
    (∀ v, v ≠ 0 → 0 < Var[fun ω => ⟪v, G ω⟫; Pr]) → ∀ x : H,
      (cmNorm Pr G x = ⊤ → tukeyDepthH (Pr.map G) x = 0) ∧
        ∀ r : ℝ, cmNorm Pr G x = r → tukeyDepthH (Pr.map G) x = ENNReal.ofReal (cdf (gaussianReal 0 1) (-r))

/-- `cor:gaussian-t`, "`√W ξ ∼ t_ν`": for `W ∼ InvGamma(ν/2, ν/2)` (`W > 0`, `1/W ∼ Gamma(ν/2, rate ν/2)`), the
distribution function `F₁(s) = E Φ(s/√W)` of `√W ξ` is the Student distribution function `F_{t_ν}`. -/
def gaussian_t_student_F : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (W : Ω → ℝ) (ν : ℝ),
    0 < ν → Measurable W → (∀ᵐ ω ∂Pr, 0 < W ω) → Pr.map (fun ω => (W ω)⁻¹) = gammaMeasure (ν / 2) (ν / 2) →
      ∀ s : ℝ, ellF1 Pr W s = studentCDF ν s

/-- `cor:gaussian-t`, Student reference: for `μ = 𝓛(√W G)` with `W ∼ InvGamma(ν/2, ν/2)`,
`TD_H(x; μ) = F_{t_ν}(−‖x‖_CM)` with the Student distribution function (and `0` off the Cameron–Martin space). -/
def gaussian_t_student_TD : Prop :=
  ∀ (Ω H : Type) [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
    [BorelSpace H] [Nontrivial H] (Pr : Measure Ω) (G : Ω → H) (W : Ω → ℝ) (ν : ℝ),
    EllSetting Pr G W → 0 < ν → Pr.map (fun ω => (W ω)⁻¹) = gammaMeasure (ν / 2) (ν / 2) → ∀ x : H,
      (cmNorm Pr G x = ⊤ → tukeyDepthH (ellLaw Pr G W) x = 0) ∧
        ∀ r : ℝ, cmNorm Pr G x = r → tukeyDepthH (ellLaw Pr G W) x = ENNReal.ofReal (studentCDF ν (-r))

/-! ### Robust equality (JASA) `prop:ep-gauss` -/

open StatFormal.Wave11a (Tgauss)

/-- `prop:ep-gauss`, the floor kernel and the blur: for `ν` Lebesgue measure on `ℝ^d` and `c(x,y) = |x − y|²`, the floor
kernel `K^ε_{x₀}(dy) ∝ e^{−c(x₀,y)/ε} ν(dy)` is `N(x₀, (ε/2) I)` (the law of `x₀ + √(ε/2) Z`, `Z ∼ N(0, I)`), and for
`h(x) = ⟨w, x⟩ + b` the blur `𝖡_ε = E_{K^ε_{x₀}} f_h(x₀, ·)`, `f_h(x₀,y) = (h(y) − h(x₀))²`, is `|w|²ε/2` at every
anchor `x₀`. -/
def ep_gauss_kernel : Prop :=
  ∀ (d : ℕ) (x₀ w : EuclideanSpace ℝ (Fin d)) (b ε : ℝ), 0 < ε →
    (volume : Measure (EuclideanSpace ℝ (Fin d))).tilted (fun y => -‖x₀ - y‖ ^ 2 / ε) =
        (stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun z => x₀ + √(ε / 2) • z) ∧
      ∫ y, ((⟪w, y⟫ + b) - (⟪w, x₀⟫ + b)) ^ 2
          ∂((volume : Measure (EuclideanSpace ℝ (Fin d))).tilted (fun y => -‖x₀ - y‖ ^ 2 / ε)) = ‖w‖ ^ 2 * ε / 2

/-- `prop:ep-gauss`, the `T_ε` formula (the Gaussian integral): for `ν` Lebesgue on `ℝ^d`, `c(x,y) = |x − y|²`, a centre
`P̂ = n⁻¹ Σ_i δ_{x_i}`, `h(x) = ⟨w, x⟩ + b`, the floor `R_ε = −ε E_{P̂} log ∫ e^{−c(x₀,y)/ε} dy` and the paper's
`T_ε(λ; r) = λr + λε E_{P̂} log ∫ exp((f_h(x₀,y) − λc(x₀,y))/(λε)) dy`: for every `λ > |w|²` both integrals are finite and
positive at every anchor and `T_ε(λ; R_ε + β) = λβ − (λε/2) log(1 − |w|²/λ)` (the frozen `Tgauss`). -/
def ep_gauss_T : Prop :=
  ∀ (d n : ℕ) (x : Fin n → EuclideanSpace ℝ (Fin d)) (w : EuclideanSpace ℝ (Fin d)) (b β ε lam : ℝ),
    0 < n → 0 < ε → ‖w‖ ^ 2 < lam →
      (∀ i, 0 < ∫ y, Real.exp (-‖x i - y‖ ^ 2 / ε)) ∧
      (∀ i, 0 < ∫ y, Real.exp ((((⟪w, y⟫ + b) - (⟪w, x i⟫ + b)) ^ 2 - lam * ‖x i - y‖ ^ 2) / (lam * ε))) ∧
      lam * (-ε * ((1 / (n : ℝ)) * ∑ i, Real.log (∫ y, Real.exp (-‖x i - y‖ ^ 2 / ε))) + β) +
          lam * ε * ((1 / (n : ℝ)) * ∑ i, Real.log (∫ y,
            Real.exp ((((⟪w, y⟫ + b) - (⟪w, x i⟫ + b)) ^ 2 - lam * ‖x i - y‖ ^ 2) / (lam * ε)))) =
        Tgauss (‖w‖ ^ 2) β ε lam

/-! ### otfd R `thm:peaked-cube`: the law on `H` -/

open StatFormal.OTFD.Wave12a (peakedLaw)
open StatFormal.OTFD.Wave1 (truncK PellClass)

/-- `thm:peaked-cube`, first sentence: the law `μ` of `X = Σ_k (C_k/(kL_k)) e_k` on `H` is a probability measure, is
supported in the Hilbert cube `∏_k [−1/k, 1/k]` (coordinates in the basis `e`), is symmetric and atomless. -/
def peakedH_basic : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (e : HilbertBasis ℕ ℝ H) (L₀ a : ℝ), 1 ≤ L₀ → 1 < a →
      IsProbabilityMeasure (peakedLawH e L₀ a) ∧
      peakedLawH e L₀ a {x | ∀ j : ℕ, |⟪e j, x⟫| ≤ 1 / ((j : ℝ) + 1)} = 1 ∧
      (peakedLawH e L₀ a).map (fun x => -x) = peakedLawH e L₀ a ∧
      ∀ x : H, peakedLawH e L₀ a {x} = 0

/-- `thm:peaked-cube`, "a product, coherent": for every `K`, the image of `μ` under the first `K` coordinates is the frozen
`μ_K = peakedLaw L₀ a K`, the product of the first `K` coordinate laws (so the finite-dimensional laws of the
theorem are the projections of the one law `μ` on `H`). -/
def peakedH_coherent : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (e : HilbertBasis ℕ ℝ H) (L₀ a : ℝ), 1 ≤ L₀ → 1 < a →
      ∀ K : ℕ, (peakedLawH e L₀ a).map (truncK e K) = peakedLaw L₀ a K

/-- `thm:peaked-cube`, "belongs to `𝒫^ℓ(H)`" (frozen `PellClass`: probability, finite second moment, null on Lipschitz
hypersurfaces). -/
def peakedH_Pl : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (e : HilbertBasis ℕ ℝ H) (L₀ a : ℝ), 1 ≤ L₀ → 1 < a →
      PellClass (peakedLawH e L₀ a)

end Claims

end StatFormal.WaveP1c
