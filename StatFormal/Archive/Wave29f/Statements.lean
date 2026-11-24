import StatFormal.Archive.Wave24c.Statements
import StatFormal.Archive.Wave23b.Statements
import StatFormal.Archive.Wave23c.Statements
import StatFormal.Archive.Wave23d.Statements
import StatFormal.Archive.OTFD.Wave12a.Statements
import StatFormal.Archive.OTFD.Wave8b.Statements
import StatFormal.Archive.WaveP3a.Statements
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Distributions.Gaussian.Basic

/-!
# FROZEN STATEMENTS — wave 29f: the remaining partial coverage of otfd R and otfd T — R `thm:student` (i), (iii) and
# the outlyingness clause of (ii); T `thm:coverage-error` with the representation `X = E_m Q(U)` DISCHARGED

The other targets assigned to this wave (`eq:smooth` consistency, `thm:peaked-cube` on `𝓗`, `lem:plan-w2` in `ℝ^d`)
are already certified; see "Already certified" below.

Sources (current text, `otfd/papers`, T_tangent at commit 57944952 of 2026-10-17):
* otfd R `thm:student` (`R_robustness/sections/s6_references.tex:71-88`, proof `:90-98`), with `𝒫^ℓ(𝓗)` and `m₂`
  (`:11-22`), `thm:moment-sieve` (`:39-48`), `thm:region-breakdown` (frozen OTFD Wave 6b / 12a) and the band
  enclosures of InouzheB (compact regions).
* otfd T `thm:coverage-error` (`T_tangent/supp_moved.tex:955-978`, proof `:970-977`), with `lem:exp` (`:829-845`),
  `ass:model` (`T_tangent/sec_tangent_theory.tex:89-95`), `eq:Hembed` (`:62-66`), the chart `eq:chart` (`:75-79`) and
  `thm:population` (`:137-175`).
Imports the frozen `Wave24c` (`coverage_error`; through it `OTFD/Wave22b` `LengthBound`, `Lb`), `Wave23b` (through it
`OTFD/Wave8c` `IsRankPair`, `IsGradMap`; `OTFD/WaveL1` `LipNull`, `Mom2`, `Euc`), `Wave23c` (`EllSetting`, `ellLaw`),
`Wave23d` (`studentLaw`, `tCDF`, `fCDF`, `fQuant`), `WaveP3a` (`bandSup`), `OTFD/Wave12a` (through it `OTFD/Wave6b` `IsEntPot`, `regionSup`;
`OTFDR/Lift` `BP`; `OTFD/Wave1` `IsLipHyp`, `PellClass`, `truncK`) and `OTFD/Wave8b` (`embed`) statements, not copied;
Mathlib (`covarianceBilin`, `variance`, `gammaMeasure`, `stdGaussian`) otherwise.

Covered:
* R `thm:student` (i): `student_lipnull` (`μ = 𝓛(√W G)` gives mass `0` to every Lipschitz hypersurface; no moment and
  no law of `W` needed beyond `W > 0` a.s. and independence), `student_moment` (`ν > 2`, `W ∼ InvGamma(ν/2, ν/2)`:
  `m₂(μ) = ν/(ν−2) tr Σ`, `tr Σ < ∞`, hence `μ ∈ 𝒫^ℓ(𝓗)`; "`thm:moment-sieve` applies to ranks and quantiles" is
  exactly `PellClass μ` and `Mom2 μ < ∞`, the hypotheses of the frozen OTFD WaveL3 `moment_sieve_a_uncond`,
  `moment_sieve_b_uncond`, so no instance is restated), `student_coherent` (`Π_K#μ` is the frozen `studentLaw K ν A`
  for EVERY `A` with `AAᵀ = Σ_K = Π_K Σ ι_K`, and such an `A` exists).
* R `thm:student` (ii), the clause left open by Wave 23d: `student_outlyingness` (for `U ∼ μ_K`,
  `F_{K,ν}(‖Σ_K^{-1/2}U‖²/K)` is exactly `Unif[0,1]`).
* R `thm:student` (iii): `student_breakdown` (the content-`p` ellipsoid is compact and nonempty, and for the fitted
  entropic region over it and every band over it (bounded spanning evaluation functionals),
  `BP ∈ [β*_K(p), β*_K(p) + 1/n]` with `β*_K(p) = F_{t_ν}(−√(K F_{K,ν}^{-1}(p)))`; the finite-second-moment and
  absolute-continuity premises of the frozen `region_bp_unconditional` / WaveP3a `band_bp_unconditional` are
  DISCHARGED for the Student law, `ν > 2`).
* T `thm:coverage-error`: `coverr_rank` (the representation `X = E_m Q(U)` of the frozen Wave 24c `coverage_error`
  DISCHARGED: `X` any random element of the curve space with a rank pair `(F, Q)` between `μ` and `ν = L_m#P` — the
  output of `thm:population` — and the chart conditions of `eq:chart`/`ass:model`; `U := F(L_m X)` is built, not
  assumed), `coverr_model` (fully under `ass:model`: the rank pair is the McCann pair of the certified Wave 23b
  `pop_hilbert`, and the theorem holds for it). The bound on `Q_ν` is required `μ`-a.e. only.

Not covered (declared):
* R `thm:student`: the depth formula and `β*`/region optimality ((ii), frozen Wave 23d), the rate `≍ K^{−ν/2}`
  (frozen Wave 25d `rates_student`), `cor:gaussian-t` (frozen Wave 24e/WaveP1c) are not restated; "the band enclosures
  of InouzheB apply" is covered only as the compactness of the regions (the B enclosure theorems are generic in a
  compact region and are not instantiated); "the K-variate Student law" is the frozen `studentLaw` (law of
  `√W A Z`), not a density formula.
* T `thm:coverage-error`: `LengthBound`, `L_b < ∞` (`lem:exp`'s Riemannian inputs, hypotheses as in Wave 22b/24c) and
  `eq:Hembed` (hypothesis, as printed); the "consequently" clause on asymptotic content (a consistency hypothesis plus
  the bound); the chart `E_m` is an abstract measurable map into a measurable curve space `C` with an evaluation
  `curve : C → T → M` (not `C(T, M)` with its Borel structure).

Encodings (to be checked by the critic):
* Student: `G` and `W` as in the frozen `EllSetting` (centred Gaussian on `𝓗`, `Var⟨v, G⟩ > 0` for `v ≠ 0`, i.e.
  injective covariance; `W > 0` a.s., `W ⫫ G`); `μ = ellLaw Pr G W = 𝓛(√W G)`; `W ∼ InvGamma(ν/2, ν/2)` as
  `𝓛(1/W) = gammaMeasure (ν/2) (ν/2)` (as in the frozen Wave 24e `gaussian_t_moment`); `tr Σ = Σ_k Var⟨e_k, G⟩` over a
  Hilbert basis `(e_k)` (`= Σ_k ⟨Σe_k, e_k⟩`; basis-independent), in `[0, ∞]`; `m₂ = Mom2` in `[0, ∞]`;
  `Σ_K(x, y) = covarianceBilin 𝓛(G) (ι_K x) (ι_K y)` (`ι_K = embed e K`), "`AAᵀ = Σ_K`" as
  `⟪A* x, A* y⟫ = Σ_K(x, y)` (`IsScaleRoot`); `𝒫^ℓ` = frozen `PellClass`; hypersurfaces = frozen `IsLipHyp`.
* Outlyingness: the law of `F_{K,ν}(‖A⁻¹U‖²/K)` under `U ∼ studentLaw K ν A` equals `Leb|_{[0,1]}` (the uniform law).
* Breakdown: `regionSup`, `BP`, `IsEntPot` frozen (OTFD Wave 6b, OTFDR Lift), `bandSup` frozen (WaveP3a; evaluation
  functionals `e : 𝒯 → ℝ^K` bounded and spanning, as in `band_bp_unconditional`); the content-`p` ellipsoid is
  `{u : ‖A⁻¹u‖ ≤ √(K F_{K,ν}^{-1}(p))}` as in the frozen `student_region`; `0 < ε`, entropic potentials for every
  sample (the paper's fitted band), `K, n ≥ 1`.
* Coverage: as in the frozen `coverage_error` (fields `H` separable, curves `t ↦ Ex t ((ι v)(t))`, `L = (Lb D b).toReal Λ`
  under `Lb D b ≠ ⊤`, expanded tube = within `δ` of a point of `𝒯(t)`, measurable event, truncated subtraction in
  `[0, ∞]`); the data trajectory `X : Ω → C`, `P_X = P.map X`; `E_m = Em : H → C` with `curve (Em v) t = Ex t ((ι v) t)`,
  `L_m = Lm` Borel with `L_m E_m = id` on `𝒟_r` and `X ∈ E_m(𝒟_r)` a.s. (the hypotheses of the frozen Wave 23b
  `pop_manifold`); `ν = (P.map X).map Lm`; `coverr_model`'s `ass:model`: `ν`, `μ` probability, `LipNull`, supported in
  balls `B`, `B_μ` (a.e. bounds, as in the frozen `pop_hilbert`).

Junk audit: every `Measure.map` is of a measurable map (`√W • G`, `truncK`, `X`, `Lm`, the outlyingness map is
monotone∘continuous); `variance` is of `⟨e_k, G⟩ ∈ L²` (Gaussian; no junk `0`); `ν/(ν − 2)` with `ν > 2`; `1/n`
with `n ≥ 1`; `toReal` of `Lb D b ≠ ⊤`; `fQuant` is an `sInf` of a nonempty set bounded below for `0 < p < 1` (frozen,
Wave 23d); `tCDF`, `fCDF` are `cdf`s of probability measures; `BP` takes the value `1` when nothing explodes (genuine
definition `def:bp`); `regionSup` is a `⨆` over a compact region of a continuous map (bounded, frozen
`region_bp_unconditional` handles it). No `sInf`/`sSup`/division by a possibly-zero quantity in the new definitions.

Already certified (no new claim): T `eq:smooth` consistency — the frozen Wave 25b `smooth_consistency_discharged`
removes the `thm:empirical` premise of Wave 24c `smooth_consistency` (and Wave 25b `empirical_quantile` certifies
`thm:empirical` itself); R `thm:peaked-cube`, the law on `𝓗` and `μ ∈ 𝒫^ℓ(𝓗)` — frozen WaveP1c `peakedH_basic`,
`peakedH_coherent`, `peakedH_Pl`; R `lem:plan-w2` in `ℝ^d` with `P ≪ Leb` — frozen OTFD WaveL1 `plan_w2_fd_a`,
`plan_w2_fd_b`, `plan_w2_fd_b_map`. `certify.py check` (2026-10-20): CERTIFIED, 2046 targets.

Proof notes (author of the draft, 2026-10-20): all 7 claims are proved in `Wave29f/Route{Coverage,StudentPl,
StudentCoherent,StudentBreak}.lean` (`#print axioms`: propext, Classical.choice, Quot.sound), on the new library
`Foundations/StudentRef/Basic` (inverse-gamma mean `E[1/V] = r/(a−1)`, Parseval `E‖X‖² = Σ_k E⟨e_k, X⟩²`,
`E⟨v, X⟩² = Var` when centred), `Foundations/ChiSquare/Whitening`, the WaveP2b routes (`gaussian_null`,
`isLipHyp_smul_preimage`, `gaussian_ac`, `colourEquiv_whiten`) and the certified Wave 23b `pop_manifold`,
`pop_hilbert`, Wave 24c `coverage_error`, Wave 23d `student_region`, `student_beta`, OTFD Wave 12a
`region_bp_unconditional`.
* `student_lipnull`: `𝓛(W, G) = 𝓛(W) ⊗ 𝓛(G)`; Tonelli; for `w > 0`, `{g : √w g ∈ S}` is a Lipschitz hypersurface,
  null for the Gaussian law (injective covariance from `EllSetting.inj`).
* `student_moment`: `‖√W G‖² = W ‖G‖²` a.s., independence of `W` and `‖G‖²`, `E W = (ν/2)/(ν/2 − 1)` by the Gamma
  integral `∫ v^{a−2} e^{−av} = a^{1−a} Γ(a−1)` and `Γ(a) = (a−1)Γ(a−1)`; Parseval and centring for `E‖G‖²`; Fernique
  for finiteness.
* `student_coherent`: `Π_K = ι_K*`; `𝓛(Π_K G)` is a centred Gaussian with covariance `Σ_K`; `IsGaussian.ext` against
  `A#N(0, I)` (covariance `⟪A*x, A*y⟫`); the law of `(W, Π_K G)` is a product; `𝓛(W) = inv#Gamma`;
  `√(1/v) = (√v)⁻¹`; a swap of the product. Existence: `A = W_K⁻¹ ∘ R`, `W_K` the whitening map (bijective: injective
  by `colourEquiv_whiten`, equal dimensions), `R` the reindexing isometry `ℝ^K ≅ ℝ^{dim ℝ^K}` (`N(0, I)` is invariant).
* `student_outlyingness`: `‖A⁻¹((√v)⁻¹Az)‖²/K = ‖z‖²/(Kv)` for `v ≥ 0` (Gamma-a.s.); `fLaw` atomless; PIT.
* `student_breakdown`: `studentLaw ≪ Leb` (Tonelli in `v`, `N(0, I) ≪ Leb`, `Leb(L⁻¹N) = |det L⁻¹| Leb N`), second
  moment `≤ E[1/V] ‖A‖² E‖Z‖² < ∞`; compact ellipsoid as a homeomorphic preimage of a closed ball; region half by
  OTFD Wave 12a `region_bp_unconditional`, band half by WaveP3a `band_bp_unconditional` (added by the critic).
* `coverr_rank`: `U = F(L_m X)`, `𝓛(U) = μ` and `E_m Q(U) = X` a.s. (`pop_manifold`); `Q' = Q̂` on a measurable
  `μ`-null set carrying the failures of the bound, `Q` elsewhere; `coverage_error` for `(U, Q')`; remove a measurable
  `P`-null set. `coverr_model`: `pop_hilbert` supplies `(F, Q)`, then `coverr_rank`. Fidelity check (critic):
  `RouteCoverage.coverr_rank_gives_frozen` derives from `Claims.coverr_rank` the frozen `coverage_error` conclusion on
  its own objects (`U ∼ μ`, curve `Ex t (ι (Q U) t)`) for the represented trajectory `X := E_m Q(U)`, given a rank pair
  between `μ` and `Q#μ` and the chart conditions.
* Still open after this wave (critic): R `thm:student` (ii) "the region of content `p`" with content EXACTLY `p`
  (frozen `student_region` gives `≥ p`; the atomlessness `fLaw_noAtoms` proved in `RouteStudentBreak` is the missing
  input, but no claim states it).

Observations on the papers (no claim found false): (1) R `thm:student` (i): the hypersurface clause needs neither
`ν > 2` nor the inverse-gamma law (only `W > 0` a.s. and `W ⫫ G`), and coherence holds for every `ν > 0`; `ν > 2`
enters only through `m₂` (and, in (iii), through the finite-second-moment standing assumption of `thm:entropic`).
(2) T `thm:coverage-error`: the proof's "represent a fresh trajectory by `X = Q^m(U)`" is justified by
`thm:population` with `U := F^m(X)` (an a.s. identity, not only in law); the tangent bound on `Q_ν` is needed only
`μ`-a.e. (under `ass:model` it holds with `b = ΛB`), which is the only meaningful reading for an a.e.-defined map.

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace StatFormal.Wave29f

open StatFormal.OTFD.WaveL1 (Euc LipNull Mom2)
open StatFormal.OTFD.Wave1 (IsLipHyp PellClass truncK)

/-- `A` is a square root of the truncated covariance: `AAᵀ = Σ_K`, i.e. `⟪A* x, A* y⟫ = ⟪Σ ι_K x, ι_K y⟫` for all
`x, y ∈ ℝ^K` (`Σ_K = Π_K Σ ι_K`, the covariance of `Π_K G`). -/
def IsScaleRoot {Ω H : Type*} [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
    [BorelSpace H] (Pr : Measure Ω) (G : Ω → H) (e : ℕ → H) (K : ℕ) (A : Euc K ≃L[ℝ] Euc K) : Prop :=
  ∀ x y : Euc K, ⟪(A : Euc K →L[ℝ] Euc K).adjoint x, (A : Euc K →L[ℝ] Euc K).adjoint y⟫_ℝ =
    covarianceBilin (Pr.map G) (StatFormal.OTFD.Wave8b.embed e K x) (StatFormal.OTFD.Wave8b.embed e K y)

namespace Claims

open StatFormal.Wave23c (EllSetting ellLaw)
open StatFormal.Wave23d (studentLaw tCDF fCDF fQuant)

/-! ### R `thm:student` (i) -/

/-- R `thm:student` (i), "`μ ∈ 𝒫^ℓ(𝓗)`", the hypersurface clause: for `μ = 𝓛(√W G)`, `G` a centred Gaussian element
of `𝓗` with injective covariance and `W > 0` independent of `G`, every Lipschitz hypersurface has `μ`-mass `0`. -/
def student_lipnull : Prop :=
  ∀ (H Ω : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] [MeasurableSpace Ω] (Pr : Measure Ω) (G : Ω → H) (W : Ω → ℝ),
    EllSetting Pr G W → ∀ S : Set H, IsLipHyp S → ellLaw Pr G W S = 0

/-- R `thm:student` (i), the moment clause: for `W ∼ InvGamma(ν/2, ν/2)`, `ν > 2`,
`m₂(μ) = ν/(ν−2) · tr Σ` with `tr Σ = Σ_k Var⟨e_k, G⟩ < ∞`; hence `μ ∈ 𝒫^ℓ(𝓗)` (with its second moment), the
hypothesis under which `thm:moment-sieve` applies to ranks and quantiles. -/
def student_moment : Prop :=
  ∀ (H Ω : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] [MeasurableSpace Ω] (Pr : Measure Ω) (G : Ω → H) (W : Ω → ℝ)
    (e : HilbertBasis ℕ ℝ H) (ν : ℝ),
    EllSetting Pr G W → 2 < ν → Pr.map (fun ω => (W ω)⁻¹) = gammaMeasure (ν / 2) (ν / 2) →
      Mom2 (ellLaw Pr G W) =
          ENNReal.ofReal (ν / (ν - 2)) * ∑' k, ENNReal.ofReal (Var[fun ω => ⟪e k, G ω⟫_ℝ; Pr]) ∧
        ∑' k, ENNReal.ofReal (Var[fun ω => ⟪e k, G ω⟫_ℝ; Pr]) < ⊤ ∧ PellClass (ellLaw Pr G W)

/-- R `thm:student` (i), "it is coherent: `μ_K` is the `K`-variate Student law with scale `Σ_K`": for every `K`, a
square root `A` of `Σ_K` exists, and for every such `A`, `Π_K#μ` is the frozen `studentLaw K ν A` (the law of
`√W' A Z`, `Z` standard Gaussian on `ℝ^K`, `1/W' ∼ Gamma(ν/2, ν/2)` independent). -/
def student_coherent : Prop :=
  ∀ (H Ω : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] [MeasurableSpace Ω] (Pr : Measure Ω) (G : Ω → H) (W : Ω → ℝ)
    (e : HilbertBasis ℕ ℝ H) (ν : ℝ) (K : ℕ),
    EllSetting Pr G W → 0 < ν → Pr.map (fun ω => (W ω)⁻¹) = gammaMeasure (ν / 2) (ν / 2) →
      (∃ A : Euc K ≃L[ℝ] Euc K, IsScaleRoot Pr G (fun k => e k) K A) ∧
        ∀ A : Euc K ≃L[ℝ] Euc K, IsScaleRoot Pr G (fun k => e k) K A →
          (ellLaw Pr G W).map (truncK (fun k => e k) K) = studentLaw K ν A

/-! ### R `thm:student` (ii), the outlyingness -/

/-- R `thm:student` (ii), last clause: the outlyingness `F_{K,ν}(‖Σ_K^{-1/2}u‖²/K)` of a rank `u` distributed as
`μ_K` is exactly uniform on `[0, 1]`. -/
def student_outlyingness : Prop :=
  ∀ (K : ℕ) (ν : ℝ) (A : Euc K ≃L[ℝ] Euc K), 0 < K → 0 < ν →
    (studentLaw K ν A).map (fun u => fCDF K ν (‖A.symm u‖ ^ 2 / K)) = volume.restrict (Icc (0 : ℝ) 1)

/-! ### R `thm:student` (iii) -/

open StatFormal.OTFD.Wave6b (IsEntPot regionSup) in
open StatFormal.OTFDR.Lift (BP) in
/-- R `thm:student` (iii): the content-`p` ellipsoid `E_p = {‖Σ_K^{-1/2}u‖ ≤ √(K F_{K,ν}^{-1}(p))}` is compact and
nonempty (so the band enclosures apply), and `thm:region-breakdown` gives the breakdown point of the fitted entropic
region `Q̂(E_p)` (`sup_{u∈E_p} ‖Q̂(u)‖`) and of every band over it (sup-norm of the band edges for bounded evaluation
functionals spanning `ℝ^K`, frozen WaveP3a `bandSup`): `β*_K(p) ≤ BP ≤ β*_K(p) + 1/n`,
`β*_K(p) = F_{t_ν}(−√(K F_{K,ν}^{-1}(p)))` (`ν > 2`: finite second moment of the reference). -/
def student_breakdown : Prop :=
  ∀ (K n : ℕ) (ν ε p : ℝ) (A : Euc K ≃L[ℝ] Euc K) (fsel : (Fin n → Euc K) → Fin n → ℝ) (Z : Fin n → Euc K),
    0 < K → 1 ≤ n → 2 < ν → 0 < ε → (∀ Z', IsEntPot (studentLaw K ν A) ε Z' (fsel Z')) → 0 < p → p < 1 →
      IsCompact {u : Euc K | ‖A.symm u‖ ≤ √(K * fQuant K ν p)} ∧
        {u : Euc K | ‖A.symm u‖ ≤ √(K * fQuant K ν p)}.Nonempty ∧
        tCDF ν (-√(K * fQuant K ν p)) ≤ BP (regionSup ε fsel {u : Euc K | ‖A.symm u‖ ≤ √(K * fQuant K ν p)}) Z ∧
        BP (regionSup ε fsel {u : Euc K | ‖A.symm u‖ ≤ √(K * fQuant K ν p)}) Z ≤
          tCDF ν (-√(K * fQuant K ν p)) + 1 / n ∧
        ∀ (𝒯 : Type) (e : 𝒯 → Euc K), (∃ C : ℝ, ∀ t, ‖e t‖ ≤ C) → Submodule.span ℝ (Set.range e) = ⊤ →
          tCDF ν (-√(K * fQuant K ν p)) ≤
              BP (StatFormal.WaveP3a.bandSup ε fsel {u : Euc K | ‖A.symm u‖ ≤ √(K * fQuant K ν p)} e) Z ∧
            BP (StatFormal.WaveP3a.bandSup ε fsel {u : Euc K | ‖A.symm u‖ ≤ √(K * fQuant K ν p)} e) Z ≤
              tCDF ν (-√(K * fQuant K ν p)) + 1 / n

/-! ### T `thm:coverage-error`, representation discharged -/

open StatFormal.OTFD.Wave8c (IsRankPair) in
open StatFormal.OTFD.Wave22b (LengthBound Lb) in
/-- T `thm:coverage-error` with the representation `X = Q^m(U)` DISCHARGED: `X` is any random element of a curve
space `C` (evaluation `curve`), in the chart image `E_m(𝒟_r)` a.s., with `L_m E_m = id` on `𝒟_r`, and `(F, Q)` is a
rank pair between `μ` and `ν = L_m#P_X` (the output of `thm:population`); `Q` has pointwise tangent norms at most `b`
`μ`-a.e., the fitted `Q̂` everywhere. If a fitted tube contains `E_m Q̂(u)` for `u ∈ A`, `μ(A) ≥ p̲`, then for `δ > 0`
there is a measurable event of probability `≥ p̲ − L_b²Λ²δ^{-2} ∫ ‖Q̂ − Q‖² dμ` on which `X(t)` is within `δ` of
`𝒯(t)` for every `t`. -/
def coverr_rank : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [SecondCountableTopology H] [MeasurableSpace H]
    [BorelSpace H] (Tm V W M C Ω : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
    [NormedSpace ℝ W] [PseudoEMetricSpace M] [MeasurableSpace C] [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → C)
    (curve : C → Tm → M) (μ : Measure H) (Ex : Tm → V → M) (D : Tm → V → V →L[ℝ] W) (ι : H →ₗ[ℝ] (Tm → V))
    (Em : H → C) (Lm : C → H) (Dr : Set H) (F Q Qhat : H → H) (tube : Tm → Set M) (A : Set H) (b Λ pbar δ : ℝ),
    IsProbabilityMeasure P → IsProbabilityMeasure μ → Measurable X → (∀ v t, curve (Em v) t = Ex t (ι v t)) →
    Measurable Em → Measurable Lm → MeasurableSet Dr → (∀ v ∈ Dr, Lm (Em v) = v) →
    (∀ᵐ x ∂(P.map X), Lm x ∈ Dr ∧ Em (Lm x) = x) → IsRankPair μ ((P.map X).map Lm) F Q →
    Measurable Qhat → MeasurableSet A → 0 < δ → 0 ≤ Λ → LengthBound Ex D → Lb D b ≠ ⊤ →
    (∀ x t, ‖ι x t‖ ≤ Λ * ‖x‖) → (∀ᵐ u ∂μ, ∀ t, ‖ι (Q u) t‖ ≤ b) → (∀ u t, ‖ι (Qhat u) t‖ ≤ b) →
    (∀ u ∈ A, ∀ t, Ex t (ι (Qhat u) t) ∈ tube t) → ENNReal.ofReal pbar ≤ μ A →
      ∃ Ev : Set Ω, MeasurableSet Ev ∧
        (∀ ω ∈ Ev, ∀ t, ∃ y ∈ tube t, edist (curve (X ω) t) y ≤ ENNReal.ofReal δ) ∧
        ENNReal.ofReal pbar - ENNReal.ofReal (((Lb D b).toReal * Λ) ^ 2 / δ ^ 2) *
            ∫⁻ u, ‖Qhat u - Q u‖ₑ ^ 2 ∂μ ≤ P Ev

open StatFormal.OTFD.Wave8c (IsRankPair IsGradMap) in
open StatFormal.OTFD.Wave22b (LengthBound Lb) in
/-- T `thm:coverage-error` under `ass:model` (the population chart model): `ν = L_m#P_X` and `μ` are boundedly
supported and null on Lipschitz hypersurfaces, `X ∈ E_m(𝒟_r)` a.s.; then the McCann rank and quantile maps
`F_ν`, `Q_ν` (a.e. convex gradients, mutual inverses, `thm:population`) exist, and for them, with `eq:Hembed`, `lem:exp`
(`LengthBound`, `L_b < ∞`) and tangent norms `≤ b` (for `Q_ν` `μ`-a.e.), every fitted tube containing `E_m Q̂(A)`,
`μ(A) ≥ p̲`, has `P{X(t) ∈ 𝒯^δ(t) ∀t} ≥ p̲ − L_b²Λ²δ^{-2} ∫ ‖Q̂ − Q_ν‖² dμ` (on a measurable event). -/
def coverr_model : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (Tm V W M C Ω : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [PseudoEMetricSpace M] [MeasurableSpace C] [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → C) (curve : C → Tm → M) (μ : Measure H) (Ex : Tm → V → M) (D : Tm → V → V →L[ℝ] W)
    (ι : H →ₗ[ℝ] (Tm → V)) (Em : H → C) (Lm : C → H) (Dr : Set H) (B Bμ Λ : ℝ),
    IsProbabilityMeasure P → IsProbabilityMeasure μ → Measurable X → (∀ v t, curve (Em v) t = Ex t (ι v t)) →
    Measurable Em → Measurable Lm → MeasurableSet Dr → (∀ v ∈ Dr, Lm (Em v) = v) →
    (∀ᵐ x ∂(P.map X), Lm x ∈ Dr ∧ Em (Lm x) = x) →
    LipNull ((P.map X).map Lm) → LipNull μ → (∀ᵐ v ∂((P.map X).map Lm), ‖v‖ ≤ B) → (∀ᵐ u ∂μ, ‖u‖ ≤ Bμ) →
    0 ≤ Λ → (∀ x t, ‖ι x t‖ ≤ Λ * ‖x‖) → LengthBound Ex D →
      ∃ F Q : H → H, IsRankPair μ ((P.map X).map Lm) F Q ∧ IsGradMap ((P.map X).map Lm) μ F ∧
        IsGradMap μ ((P.map X).map Lm) Q ∧
        ∀ (Qhat : H → H) (tube : Tm → Set M) (A : Set H) (b pbar δ : ℝ),
          Measurable Qhat → MeasurableSet A → 0 < δ → Lb D b ≠ ⊤ → (∀ᵐ u ∂μ, ∀ t, ‖ι (Q u) t‖ ≤ b) →
          (∀ u t, ‖ι (Qhat u) t‖ ≤ b) → (∀ u ∈ A, ∀ t, Ex t (ι (Qhat u) t) ∈ tube t) →
          ENNReal.ofReal pbar ≤ μ A →
            ∃ Ev : Set Ω, MeasurableSet Ev ∧
              (∀ ω ∈ Ev, ∀ t, ∃ y ∈ tube t, edist (curve (X ω) t) y ≤ ENNReal.ofReal δ) ∧
              ENNReal.ofReal pbar - ENNReal.ofReal (((Lb D b).toReal * Λ) ^ 2 / δ ^ 2) *
                  ∫⁻ u, ‖Qhat u - Q u‖ₑ ^ 2 ∂μ ≤ P Ev

end Claims

end StatFormal.Wave29f
