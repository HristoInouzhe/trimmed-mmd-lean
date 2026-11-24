import StatFormal.Archive.OTFD.Wave16b.Statements
import StatFormal.Archive.Wave15b.Statements
import StatFormal.Archive.RobustEquality.Paper2.Seminorm.Statements
import StatFormal.Archive.Wave12b.Statements
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# FROZEN STATEMENTS — gaps 1: paper2 `prop:band` at `ε = 0` (Wasserstein, restricted and anisotropic sets) and
# `cor:oracle` unconditional (`ε = 0` and `ε > 0`); otfd C `lem:full-support-region`(i) and
# `thm:neural-band-consistency` / `cor:net-inner-band-neural` without the support hypothesis `hsupp`;
# otfd C `prop:fixed-sieve-collapse` "`f₀` is a hard-OT dual potential"

Sources (verbatim in `lean-formalisation/inventory/extracted/robust-equality-paper2.md`, `otfd-C_conditional.md`;
paths under `research-lines/`):
* paper2 `prop:band` (`robust-equality-outcomes-under-distribution-shift/paper2/main.tex:557-563`, proof
  `paper2/app_proofs.tex:201-207`), with `eq:BN`, the `ε = 0` reading of `eq:T` (`T⁰_s(h,λ) = λr_s +
  E_{x₀∼P̂_s} sup_{x∈supp ν}{f_h(x₀,x) − λc(x₀,x)}`) and the anisotropic sets (`main.tex:222-250`).
* paper2 `cor:oracle` (`paper2/main.tex:565-578`, proof `app_proofs.tex:209-215`), with `thm:seminorm`(iv)(a),(c)
  (`main.tex:336-344`; frozen `Paper2/Seminorm` `seminorm_wass`).
* otfd C `lem:full-support-region`(i) (`otfd/papers/C_conditional/supplement.tex:1034-1049`, proof `:1051-1060`), the
  standing assumption of `eq:conditional-pop-band` (`C_conditional/main.tex:630-640`: `μ_K` absolutely continuous),
  `thm:neural-band-consistency` (`main.tex:738-756`, frozen Wave 7a) and `cor:net-inner-band-neural`
  (`supplement.tex:1605-1621`, frozen Wave 16b).
* otfd C `prop:fixed-sieve-collapse`(a), the sentence "Then `f_0` is a hard-OT dual potential"
  (`otfd/papers/C_conditional/supplement.tex:2395-2405`; the frozen Wave 12b claims cover the rest of (a)).
Reuses, imported, not copied: frozen `RobustEquality/Certificate/Statements.lean` (`centre`),
`Wave4b/Statements.lean` (`InBall`, `sqrtT`, `nominal`, `RefClass`), `Wave15b/Statements.lean` (`deltaPop`,
`BandHolds`, `certSetN`, `certSet2`: the objects of the conditional `cor:oracle`), `Paper2/Seminorm/Statements.lean`
(`Deltafin`, `T0`), `Wave12b/Statements.lean` (`coup`, `cost`, `optFace`, `Marg`), `OTFD/Wave7a/Statements.lean` (`NeuralSetting`, `risk`, `MonoOn`, `BandsClose`),
`OTFD/Wave16b/Statements.lean` (`NetCovers`, `NetClose`); Mathlib's `Measure.support`; Tau Ceti's `wassersteinEDist`.

Covered:
* `prop:band`, `ε = 0`: `band0` (the two-sided band on `E = {P_s ∈ 𝓑_s}` for Wasserstein balls restricted to the
  support of a reference in a class `𝒩_s`, every measurable rule, bounded or not, every cost `c ≥ 0`, all
  multipliers), `band0_selected` ("hence": a rule and multipliers selected on the same data, measurable-event
  convention), `band0_aniso` (anisotropic sets `{Q : inf_γ E_γ‖A(X′ − X)‖² ≤ β}` on `K = E`, linear rules, with the
  frozen `T0` and `Deltafin`).
* `cor:oracle` without the `prop:band` hypothesis: `oracle_band0`, `oracle0` (class of references, `ε = 0`, any
  `N_s ≥ inf_λ √T⁰_s`), `oracle_band_aniso`, `oracle_aniso` (anisotropic and Wasserstein sets on `E`, with the closed
  form `N_s(w) = √(β_s‖(A_s⁻¹)*w‖²)` of `thm:seminorm`(iv)), `oracle_band_ent`, `oracle_ent` (`ε > 0`, the frozen
  kernel balls, covariates in `K` through a bounded feature map). Each `oracle_band_*` proves the hypothesis
  `BandHolds` of the frozen Wave 15b claims; each `oracle_*` is the conjunction of the conclusions of the frozen
  `oracle_sets` and `oracle_ineq`, now on the event `E` itself.
* `lem:full-support-region`(i): `full_support_region` (`A = cl(int A)`, `μ(A ∩ N) > 0` for open `N` meeting `A`,
  `supp(μ|_A) = A`, and `ess sup_A g = sup_A g` for continuous `g`), `region_interior` (`μ ≪ Leb` and `μ(A) > 0` give a
  convex `A` nonempty interior, the step used for the level regions).
* `thm:neural-band-consistency` without `hsupp`: `neural_band_uniform_convex`, `neural_band_ae_convex`,
  `neural_band_prob_convex`, `neural_band_rate_convex` (Wave 7a claims with `hsupp` replaced by `μ_K ≪ Leb`, convex
  level regions of positive mass); `cor:net-inner-band-neural` two-sided parts without `hsupp`:
  `net_inner_two_sided_convex`, `net_band_neural_two_sided_ae_convex`, `net_band_neural_two_sided_prob_convex`,
  `net_band_neural_rate_convex` (Wave 16b claims, same replacement).
* `prop:fixed-sieve-collapse` "`f₀` is a hard-OT dual potential": `fs_hard_dual_ent` (entropic, counting-measure
  potentials), `fs_hard_dual_quad` (quadratic, semi-dual potentials): along `θ_k ↓ 0` with `f_{θ_k} → f₀`, the column
  potentials converge to the `c`-transform `g₀ = min_i(C_{i·} − f₀ i)`, and `(f₀, g₀)` is dual feasible, dual optimal
  against every feasible pair, has zero gap with every hard-optimal plan, and satisfies complementary slackness on its
  support (`IsHardDual`).

Not covered (declared):
* `prop:band`, `ε = 0`: the deployment clause at the free end (paper2 composes a free-end radius with a declared
  budget via the companion `prop:cs-compose`, an `ε > 0` statement; at `ε = 0` the ball is witnessed by couplings
  in kernel form and the gluing is not formalised); structured sets.
* `cor:oracle`: the last two sentences (independent certification sample; Rademacher control), as in Wave 15b;
  `oracle_ball` needs no band and is already unconditional (frozen Wave 15b).
* `lem:full-support-region`(ii), (iii) (the GHS laws), and "`𝒰_K` compact convex" (not needed for (i)).
* `prop:fixed-sieve-collapse`: "if the normalised hard row potential is unique, no subsequence extraction is needed"
  (still declared, as in Wave 12b); existence of the regularised potentials (entered as hypotheses: the plans are
  given in potential form). `lem:conditional-weights` a.s. version: NOT attempted here (needs conditional
  Borel–Cantelli on `Measure.infinitePi`; still declared).

Encodings:
* `ε = 0` balls (`InBall0`): `Q` a probability measure carried by `supp ν` (Mathlib `Measure.support`; `Q(supp νᶜ) = 0`)
  for some `ν ∈ 𝒩`, and `inf_γ E_γ c ≤ r` over couplings `γ` of `P̂` and `Q` in kernel form `γ = n⁻¹Σ_i δ_{x_i} ⊗ Γ_i`
  (`KernelWitness0`, cost a lower integral, so no integrability junk), written `∀ t > 0, ∃` a coupling of cost
  `≤ r + t` (the infimum need not be attained). `0 ≤ r`. Couplings of a finitely supported `P̂` with labelled atoms are
  exactly the kernel forms (disintegration over the atoms; not formalised, as for the frozen `ε > 0` witness).
  Anisotropic sets (`InAniso`): full support (no support condition) and cost `‖A(z − x)‖²`, `A : E ≃L[ℝ] E` (the paper's
  `M^{-1/2}`; `A = id` gives Wasserstein balls on `K = E = ℝ^d`).
* `T⁰` (`T0ref`) at a support set `S` is `λr + Σ_i n⁻¹ sup_{z∈S}{(h z − h x_i)² − λc(x_i,z)}` in `EReal` (`+∞` allowed,
  e.g. for linear rules and small `λ`); `√T⁰` is `T⁰.toENNReal ^ (1/2)` (`+∞ ↦ ∞`, negative `↦ 0`; on the event
  `T⁰ ≥ W₂² ≥ 0`); `√T⁰_s` over the class is `⨆_{ν∈𝒩} √T⁰(supp ν)` (`sqrtT0`, as the frozen `sqrtT`). With
  `S = univ`, cost `‖A(z − x)‖²`, `h = ⟪w,·⟫` and uniform weights this is the frozen `Seminorm.T0` (used literally in
  `band0_aniso`). The rule `h` is any measurable map (no boundedness: `W₂ = ∞` cases are covered by `ℝ≥0∞`).
* `cor:oracle`: the frozen Wave 15b objects with uniform weights `unifW n = (1/n, …, 1/n)` (the centre `P̂_s` with `n_s`
  labelled atoms). "`N_s` computed at the calibrated radii" (`N_s = inf_λ √T_s`) is the hypothesis
  `⨅_{λ>0} √T_s(⟪w,·⟫, λ) ≤ N_s(w)` in `ℝ≥0∞` for nonnegative real `N_s` (equality is the paper's choice; any
  certified upper bound is allowed, a generalisation); in the anisotropic claims `N_s` is the closed form. At
  `ε > 0` (frozen kernel balls on a measurable space `K`, bounded measurable cost) linear rules are
  `z ↦ ⟪w, φ z⟫` for a measurable bounded feature map `φ : K → E` (paper: `K ⊆ ℝ^d` compact, `φ` the inclusion), and
  the Wave 15b objects are evaluated at `P_s.map φ` and `φ ∘ x_s`. Deterministic "on `E`" form, as in Wave 15b.
* `lem:full-support-region`(i): `ℝ^K = EuclideanSpace ℝ (Fin K)`, `μ` any measure (paper: Borel probability with
  compact convex support), "`A ⊆ 𝒰_K`" is `A ⊆ μ.support`; `ess sup` in `EReal` w.r.t. `μ|_A` (as the frozen `popSup`).
* Neural claims: the frozen Wave 7a / 16b claims with `hsupp` replaced by `μ ≪ volume` (the standing absolute
  continuity of `eq:conditional-pop-band`) and `Convex ℝ (A p) ∧ 0 < μ (A p)` for `0 < p ≤ 1 − δ` (the regions are
  convex, `lem:full-support-region`(ii), and carry mass `≥ p > 0`); the support of `μ_K` enters through the frozen
  `NeuralSetting` (every ball centred in `O ⊇ S` has positive mass). Closedness of `A p` is not needed.
* `prop:fixed-sieve-collapse`, hard dual: the frozen Wave 12b arrays (`coup`, `cost`, `optFace`, `Marg`: `r_i > 0`,
  `b_j > 0`, both summing to one); `θ_k → 0⁺` is `Tendsto θ atTop (𝓝[>] 0)` (as in the frozen `fs_offgrid_*`); the
  regularised plans are in potential form, `π_{k,ij} = exp((f_{k,i} + g_{k,j} − C_ij)/θ_k)` (entropic, counting
  reference, the paper's `f_θ`) resp. `π_{k,ij} = (f_{k,i} + g_{k,j} − C_ij)_+/θ_k` (quadratic), with
  `π_k ∈ Π(r,b)`; "along a convergent subsequence" is a sequence with `f_k → f₀`. "Hard-OT dual potential" is
  `IsHardDual` (feasibility, optimality against all feasible pairs, zero gap and slackness on `Opt(r,b)`), with
  the explicit partner `g₀ j = ⨅_i (C_ij − f₀ i)` (a finite `iInf`, `n ≥ 1` from `Σ r = 1`: no junk). The additive
  normalisation `Σ f = 0` is not needed.
* All claims quantify types in `Type` (universe 0), as elsewhere in the repo.

Critic notes:
* All 21 claims are proved by the routes (`Gaps1/Route{Band0,Oracle,Support,HardDual}.lean`), axioms
  `propext, Classical.choice, Quot.sound` only. Not yet reviewed by a critic.
* At `ε = 0` the band needs `r_s ≥ 0` and `λ_s ≥ 0` (`λ > 0` as printed), but neither boundedness of `h` or `c` nor
  compactness of `K`: on the event the per-anchor sup bounds the integrand pointwise on `supp ν`, which carries every
  kernel `Γ_i` (because it carries `Q = n⁻¹ΣΓ_i`); `W₂²(h#P̂, h#Q) ≤ λ(r + t) + Σ_i n⁻¹ s_i` for every `t > 0`.
* For anisotropic sets on `E = ℝ^d` the band combined with the certified `seminorm_wass` gives the closed-form
  `N_s(w) = √β_s‖(A_s⁻¹)*w‖` (`= √β_s|M_s^{1/2}w|`, `= √r_s|w|` for Wasserstein balls), so `cor:oracle` is
  unconditional there (needs `CompleteSpace E` for the adjoint).
* `lem:full-support-region`(i) holds for any measure with `A ⊆ supp μ`; for the neural theorem the needed inclusion
  `A_{K,p} ⊆ supp μ_K` already follows from the frozen `NeuralSetting`, and nonempty interior from `μ_K ≪ Leb`,
  `μ_K(A_{K,p}) > 0` and convexity (the frontier of a convex set is Lebesgue-null), as the Wave 7a critic note said.
* Hard dual: no LP duality is needed. Entropic: `log π = (f + g − C)/θ` and `x log x ≥ x − 1` give
  `⟨C,π_k⟩ ≤ Σ r f_k + Σ b g_k + θ_k nm`; the column marginals give
  `g₀ + θ(log b_j − log n) ≤ g_{k,j} ≤ g₀ + θ log b_j` (with `f_k` in place of `f₀`). Quadratic: `⟨C,π_k⟩ ≤ Σ r f_k +
  Σ b g_k` and `g₀ ≤ g_{k,j} ≤ g₀ + θ b_j`. Weak duality against `π_k` and the limits give optimality and zero gap.
* Critic (2026-10-15): ACCEPT-WITH-NOTE, all 21 TRUE. Discharges (verified by a scripted diff against the frozen
  statements): Wave15b `oracle_sets`/`oracle_ineq` (`BandHolds` derived, ε = 0 and ε > 0); Wave7a `neural_band_*` and
  Wave16b `net_inner_two_sided`/`net_band_neural_*` (`hsupp` replaced by `μ ≪ Leb` + convex `A p` with `μ(A p) > 0`,
  exactly C main:270–277, :630). Fills gaps: paper2 `prop:band` at ε = 0 (`InBall0` = the paper's prose "Wasserstein
  balls restricted to the support of the reference" — a weaker hypothesis than the literal `Q ≪ ν`, so a stronger
  claim); "`f₀` is a hard-dual potential" (Wave12b). `√T⁰` junk check: `√⊤ = ⊤` is uninformative-true as in the paper,
  clipping negatives tightens. `unifW` is a local copy of `n⁻¹` (= frozen `Wave15b.unifW`). Paper S4: paper2 eq:BN at
  ε = 0 contains `0·KL` (ambiguous); the support restriction is only in prose (DEFECTS #61).
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped InnerProductSpace ENNReal

namespace StatFormal.Gaps1

open StatFormal.OTFD.Wave7a (NeuralSetting risk MonoOn BandsClose)
open StatFormal.OTFD.Wave16b (NetCovers NetClose)
open StatFormal.RobustEquality.Certificate (centre)
open StatFormal.Wave4b (InBall sqrtT nominal RefClass)
open StatFormal.Wave15b (deltaPop BandHolds certSetN certSet2)
open StatFormal.RobustEquality.Paper2.Seminorm (Deltafin T0)
open TauCeti (wassersteinEDist)

/-! ### paper2 `prop:band` at `ε = 0` -/

section Band0
variable {K : Type} [MeasurableSpace K]

/-- `Q = n⁻¹ Σ_i Γ_i` with transport cost `n⁻¹ Σ_i E_{Γ_i} c(x_i, ·) ≤ r`: a coupling of `P̂` and `Q` in kernel form
with cost at most `r` (lower integrals). -/
def KernelWitness0 {n : ℕ} (x : Fin n → K) (c : K → K → ℝ) (r : ℝ) (Q : Measure K) : Prop :=
  ∃ Γ : Fin n → Measure K, (∀ i, IsProbabilityMeasure (Γ i)) ∧ Q = (n : ℝ≥0∞)⁻¹ • ∑ i, Γ i ∧
    (n : ℝ≥0∞)⁻¹ * ∑ i, ∫⁻ z, ENNReal.ofReal (c (x i) z) ∂(Γ i) ≤ ENNReal.ofReal r

/-- `T⁰(h,λ) = λr + Σ_i n⁻¹ sup_{z∈S} {(h z − h x_i)² − λ c(x_i,z)}` at a support set `S`, in `EReal`. -/
def T0ref {n : ℕ} (x : Fin n → K) (c : K → K → ℝ) (h : K → ℝ) (r lam : ℝ) (S : Set K) : EReal :=
  ((lam * r : ℝ) : EReal) + ∑ i, (((n : ℝ)⁻¹ : ℝ) : EReal) *
    ⨆ z ∈ S, ((((h z - h (x i)) ^ 2 - lam * c (x i) z : ℝ)) : EReal)

variable [TopologicalSpace K]

/-- `Q ∈ B^𝒩(P̂; r)` at `ε = 0`: a probability measure carried by the support of some `ν ∈ 𝒩` with
`inf_γ E_γ c ≤ r` over couplings in kernel form. -/
def InBall0 {n : ℕ} (x : Fin n → K) (c : K → K → ℝ) (r : ℝ) (N : Set (Measure K)) (Q : Measure K) : Prop :=
  IsProbabilityMeasure Q ∧ (∃ ν ∈ N, Q ν.supportᶜ = 0) ∧ ∀ t : ℝ, 0 < t → KernelWitness0 x c (r + t) Q

/-- `√T⁰_s(h,λ) = ⨆_{ν∈𝒩} √T⁰(h,λ; supp ν)` in `ℝ≥0∞`. -/
def sqrtT0 {n : ℕ} (x : Fin n → K) (c : K → K → ℝ) (h : K → ℝ) (r lam : ℝ) (N : Set (Measure K)) : ℝ≥0∞ :=
  ⨆ ν ∈ N, (T0ref x c h r lam ν.support).toENNReal ^ (1 / 2 : ℝ)

end Band0

/-- Uniform weights `(1/n, …, 1/n)` of a centre with `n` labelled atoms. -/
def unifW (n : ℕ) : Fin n → ℝ := fun _ => (n : ℝ)⁻¹

section Aniso
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

/-- The anisotropic set `{Q : inf_γ E_γ ‖A(X′ − X)‖² ≤ β}` around `P̂` (full-support reference, couplings in kernel
form). -/
def InAniso {n : ℕ} (x : Fin n → E) (A : E ≃L[ℝ] E) (β : ℝ) (Q : Measure E) : Prop :=
  IsProbabilityMeasure Q ∧ ∀ t : ℝ, 0 < t → KernelWitness0 x (fun a z => ‖A (z - a)‖ ^ 2) (β + t) Q

/-- The closed form `N(w) = (β ‖(A⁻¹)* w‖²)^{1/2}` of `thm:seminorm`(iv) (frozen `seminorm_wass`). -/
def NAniso [CompleteSpace E] (A : E ≃L[ℝ] E) (β : ℝ) (w : E) : ℝ :=
  √(β * ‖(ContinuousLinearMap.adjoint (A.symm : E →L[ℝ] E)) w‖ ^ 2)

end Aniso

section HardDual
open StatFormal.Wave12b (coup cost optFace)
variable {n m : ℕ}

/-- `(f, g)` is a hard-OT dual potential pair for `C` and the marginals `r, b`: dual feasible, optimal against every
feasible pair, with zero gap and complementary slackness for every hard-optimal plan. -/
def IsHardDual (C : Fin n → Fin m → ℝ) (r : Fin n → ℝ) (b : Fin m → ℝ) (f : Fin n → ℝ) (g : Fin m → ℝ) : Prop :=
  (∀ i j, f i + g j ≤ C i j) ∧
  (∀ (f' : Fin n → ℝ) (g' : Fin m → ℝ), (∀ i j, f' i + g' j ≤ C i j) →
    ∑ i, r i * f' i + ∑ j, b j * g' j ≤ ∑ i, r i * f i + ∑ j, b j * g j) ∧
  ∀ π ∈ optFace C r b, ∑ i, r i * f i + ∑ j, b j * g j = cost C π ∧ ∀ i j, 0 < π i j → f i + g j = C i j

end HardDual

namespace Claims

/-! ### paper2 `prop:band`, `ε = 0` -/

/-- `prop:band` at `ε = 0`: on `E = {P_s ∈ 𝓑_s}` (Wasserstein balls restricted to the support of a reference in `𝒩_s`),
for every measurable rule `h` and all multipliers, `|W₂(h#P₀, h#P₁) − Δ(h)| ≤ √T⁰₀(h,λ₀) + √T⁰₁(h,λ₁)`. -/
def band0 : Prop :=
  ∀ (K : Type) [TopologicalSpace K] [MeasurableSpace K] (n₀ n₁ : ℕ) (x₀ : Fin n₀ → K) (x₁ : Fin n₁ → K)
    (c : K → K → ℝ) (r₀ r₁ : ℝ) (𝒩₀ 𝒩₁ : Set (Measure K)) (P₀ P₁ : Measure K),
    0 < n₀ → 0 < n₁ → (∀ a, Measurable (c a)) → (∀ a b, 0 ≤ c a b) → 0 ≤ r₀ → 0 ≤ r₁ →
    InBall0 x₀ c r₀ 𝒩₀ P₀ → InBall0 x₁ c r₁ 𝒩₁ P₁ →
      ∀ (h : K → ℝ) (lam₀ lam₁ : ℝ), Measurable h → 0 < lam₀ → 0 < lam₁ →
        wassersteinEDist 2 (P₀.map h) (P₁.map h) ≤
            nominal x₀ x₁ h + sqrtT0 x₀ c h r₀ lam₀ 𝒩₀ + sqrtT0 x₁ c h r₁ lam₁ 𝒩₁ ∧
          nominal x₀ x₁ h ≤
            wassersteinEDist 2 (P₀.map h) (P₁.map h) + sqrtT0 x₀ c h r₀ lam₀ 𝒩₀ + sqrtT0 x₁ c h r₁ lam₁ 𝒩₁

/-- `prop:band` at `ε = 0`, "hence": a rule and multipliers selected on the same data; with `P(E) ≥ 1 − α`
(measurable-event convention) the bound holds on a measurable event of probability `≥ 1 − α`. -/
def band0_selected : Prop :=
  ∀ (K Ω : Type) [TopologicalSpace K] [MeasurableSpace K] [MeasurableSpace Ω] (P : Measure Ω) (n₀ n₁ : ℕ)
    (x₀ : Ω → Fin n₀ → K) (x₁ : Ω → Fin n₁ → K) (c : K → K → ℝ) (α : ℝ) (r₀ r₁ : Ω → ℝ)
    (𝒩₀ 𝒩₁ : Set (Measure K)) (P₀ P₁ : Measure K) (hsel : Ω → K → ℝ) (lam₀ lam₁ : Ω → ℝ) (G : Set Ω),
    0 < n₀ → 0 < n₁ → (∀ a, Measurable (c a)) → (∀ a b, 0 ≤ c a b) → (∀ ω, 0 ≤ r₀ ω ∧ 0 ≤ r₁ ω) →
    (∀ ω, Measurable (hsel ω) ∧ 0 < lam₀ ω ∧ 0 < lam₁ ω) →
    MeasurableSet G → ENNReal.ofReal (1 - α) ≤ P G →
    (∀ ω ∈ G, InBall0 (x₀ ω) c (r₀ ω) 𝒩₀ P₀ ∧ InBall0 (x₁ ω) c (r₁ ω) 𝒩₁ P₁) →
      ∃ G' : Set Ω, MeasurableSet G' ∧ ENNReal.ofReal (1 - α) ≤ P G' ∧
        G' ⊆ {ω | wassersteinEDist 2 (P₀.map (hsel ω)) (P₁.map (hsel ω)) ≤
          nominal (x₀ ω) (x₁ ω) (hsel ω) + sqrtT0 (x₀ ω) c (hsel ω) (r₀ ω) (lam₀ ω) 𝒩₀ +
            sqrtT0 (x₁ ω) c (hsel ω) (r₁ ω) (lam₁ ω) 𝒩₁}

/-- `prop:band` for anisotropic sets on `K = E`, linear rules `⟪w,·⟫`: with the frozen `Δ = Deltafin` and
`T⁰ = Seminorm.T0`, `|Δ_P(w) − Δ(w)| ≤ √T⁰₀(w,λ₀) + √T⁰₁(w,λ₁)` for all `λ_s > 0`. -/
def band0_aniso : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (n₀ n₁ : ℕ) (x₀ : Fin n₀ → E) (x₁ : Fin n₁ → E) (A₀ A₁ : E ≃L[ℝ] E) (β₀ β₁ : ℝ) (P₀ P₁ : Measure E),
    0 < n₀ → 0 < n₁ → 0 ≤ β₀ → 0 ≤ β₁ → InAniso x₀ A₀ β₀ P₀ → InAniso x₁ A₁ β₁ P₁ →
      ∀ (w : E) (lam₀ lam₁ : ℝ), 0 < lam₀ → 0 < lam₁ →
        deltaPop P₀ P₁ w ≤ ENNReal.ofReal (Deltafin (unifW n₀) x₀ (unifW n₁) x₁ w) +
            (T0 A₀ β₀ (unifW n₀) x₀ w lam₀).toENNReal ^ (1 / 2 : ℝ) +
            (T0 A₁ β₁ (unifW n₁) x₁ w lam₁).toENNReal ^ (1 / 2 : ℝ) ∧
          ENNReal.ofReal (Deltafin (unifW n₀) x₀ (unifW n₁) x₁ w) ≤ deltaPop P₀ P₁ w +
            (T0 A₀ β₀ (unifW n₀) x₀ w lam₀).toENNReal ^ (1 / 2 : ℝ) +
            (T0 A₁ β₁ (unifW n₁) x₁ w lam₁).toENNReal ^ (1 / 2 : ℝ)

/-! ### paper2 `cor:oracle`, unconditional -/

/-- `ε = 0`, references in classes `𝒩_s`: on `E`, the band of `cor:oracle` (`BandHolds`, the hypothesis of the frozen
Wave 15b claims) holds for linear rules with any `N_s ≥ inf_{λ>0} √T⁰_s`. -/
def oracle_band0 : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (n₀ n₁ : ℕ) (x₀ : Fin n₀ → E) (x₁ : Fin n₁ → E) (c : E → E → ℝ) (r₀ r₁ : ℝ) (𝒩₀ 𝒩₁ : Set (Measure E))
    (P₀ P₁ : Measure E) (N₀ N₁ : E → ℝ),
    0 < n₀ → 0 < n₁ → (∀ a, Measurable (c a)) → (∀ a b, 0 ≤ c a b) → 0 ≤ r₀ → 0 ≤ r₁ →
    InBall0 x₀ c r₀ 𝒩₀ P₀ → InBall0 x₁ c r₁ 𝒩₁ P₁ → (∀ w, 0 ≤ N₀ w) → (∀ w, 0 ≤ N₁ w) →
    (∀ w, ⨅ l : Set.Ioi (0 : ℝ), sqrtT0 x₀ c (fun z => ⟪w, z⟫_ℝ) r₀ l 𝒩₀ ≤ ENNReal.ofReal (N₀ w)) →
    (∀ w, ⨅ l : Set.Ioi (0 : ℝ), sqrtT0 x₁ c (fun z => ⟪w, z⟫_ℝ) r₁ l 𝒩₁ ≤ ENNReal.ofReal (N₁ w)) →
      BandHolds P₀ P₁ (unifW n₀) x₀ (unifW n₁) x₁ N₀ N₁

/-- `cor:oracle` at `ε = 0` on `E` (classes of references): `𝒞^{(2)}(δ) ⊆ 𝒞_n(δ) ⊆ {Δ_P ≤ √δ}`, a minimiser `ŵ` of
`𝓡_n` over `𝒞_n(δ)` is certified and `𝓡(ŵ) ≤ 𝓡(w′) + 2B` for `w′ ∈ 𝒞^{(2)}(δ)`, `B ≥ sup_{𝒞_n(δ)}|𝓡_n − 𝓡|`. -/
def oracle0 : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (n₀ n₁ : ℕ) (x₀ : Fin n₀ → E) (x₁ : Fin n₁ → E) (c : E → E → ℝ) (r₀ r₁ : ℝ) (𝒩₀ 𝒩₁ : Set (Measure E))
    (P₀ P₁ : Measure E) (N₀ N₁ : E → ℝ) (δ : ℝ),
    0 < n₀ → 0 < n₁ → (∀ a, Measurable (c a)) → (∀ a b, 0 ≤ c a b) → 0 ≤ r₀ → 0 ≤ r₁ →
    InBall0 x₀ c r₀ 𝒩₀ P₀ → InBall0 x₁ c r₁ 𝒩₁ P₁ → (∀ w, 0 ≤ N₀ w) → (∀ w, 0 ≤ N₁ w) →
    (∀ w, ⨅ l : Set.Ioi (0 : ℝ), sqrtT0 x₀ c (fun z => ⟪w, z⟫_ℝ) r₀ l 𝒩₀ ≤ ENNReal.ofReal (N₀ w)) →
    (∀ w, ⨅ l : Set.Ioi (0 : ℝ), sqrtT0 x₁ c (fun z => ⟪w, z⟫_ℝ) r₁ l 𝒩₁ ≤ ENNReal.ofReal (N₁ w)) → 0 ≤ δ →
      (certSet2 P₀ P₁ N₀ N₁ δ ⊆ certSetN (unifW n₀) x₀ (unifW n₁) x₁ N₀ N₁ δ ∧
        certSetN (unifW n₀) x₀ (unifW n₁) x₁ N₀ N₁ δ ⊆ {w | deltaPop P₀ P₁ w ≤ ENNReal.ofReal √δ}) ∧
      ∀ (R Rn : E → ℝ) (wh : E), wh ∈ certSetN (unifW n₀) x₀ (unifW n₁) x₁ N₀ N₁ δ →
        IsMinOn Rn (certSetN (unifW n₀) x₀ (unifW n₁) x₁ N₀ N₁ δ) wh →
          deltaPop P₀ P₁ wh ≤ ENNReal.ofReal √δ ∧
          ∀ w' ∈ certSet2 P₀ P₁ N₀ N₁ δ, ∀ B : ℝ,
            (∀ w ∈ certSetN (unifW n₀) x₀ (unifW n₁) x₁ N₀ N₁ δ, |Rn w - R w| ≤ B) → R wh ≤ R w' + 2 * B

/-- Anisotropic (and, `A = id`, Wasserstein) sets on `E`: on `E` the band of `cor:oracle` holds with the closed-form
seminorms `N_s(w) = √(β_s‖(A_s⁻¹)*w‖²)`. -/
def oracle_band_aniso : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    (n₀ n₁ : ℕ) (x₀ : Fin n₀ → E) (x₁ : Fin n₁ → E) (A₀ A₁ : E ≃L[ℝ] E) (β₀ β₁ : ℝ) (P₀ P₁ : Measure E),
    0 < n₀ → 0 < n₁ → 0 ≤ β₀ → 0 ≤ β₁ → InAniso x₀ A₀ β₀ P₀ → InAniso x₁ A₁ β₁ P₁ →
      BandHolds P₀ P₁ (unifW n₀) x₀ (unifW n₁) x₁ (NAniso A₀ β₀) (NAniso A₁ β₁)

/-- `cor:oracle` for anisotropic / Wasserstein sets on `E`, with `N_s = NAniso A_s β_s`. -/
def oracle_aniso : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    (n₀ n₁ : ℕ) (x₀ : Fin n₀ → E) (x₁ : Fin n₁ → E) (A₀ A₁ : E ≃L[ℝ] E) (β₀ β₁ : ℝ) (P₀ P₁ : Measure E) (δ : ℝ),
    0 < n₀ → 0 < n₁ → 0 ≤ β₀ → 0 ≤ β₁ → InAniso x₀ A₀ β₀ P₀ → InAniso x₁ A₁ β₁ P₁ → 0 ≤ δ →
      (certSet2 P₀ P₁ (NAniso A₀ β₀) (NAniso A₁ β₁) δ ⊆
          certSetN (unifW n₀) x₀ (unifW n₁) x₁ (NAniso A₀ β₀) (NAniso A₁ β₁) δ ∧
        certSetN (unifW n₀) x₀ (unifW n₁) x₁ (NAniso A₀ β₀) (NAniso A₁ β₁) δ ⊆
          {w | deltaPop P₀ P₁ w ≤ ENNReal.ofReal √δ}) ∧
      ∀ (R Rn : E → ℝ) (wh : E), wh ∈ certSetN (unifW n₀) x₀ (unifW n₁) x₁ (NAniso A₀ β₀) (NAniso A₁ β₁) δ →
        IsMinOn Rn (certSetN (unifW n₀) x₀ (unifW n₁) x₁ (NAniso A₀ β₀) (NAniso A₁ β₁) δ) wh →
          deltaPop P₀ P₁ wh ≤ ENNReal.ofReal √δ ∧
          ∀ w' ∈ certSet2 P₀ P₁ (NAniso A₀ β₀) (NAniso A₁ β₁) δ, ∀ B : ℝ,
            (∀ w ∈ certSetN (unifW n₀) x₀ (unifW n₁) x₁ (NAniso A₀ β₀) (NAniso A₁ β₁) δ, |Rn w - R w| ≤ B) →
              R wh ≤ R w' + 2 * B

/-- `ε > 0` (frozen kernel balls on a measurable space `K`), linear rules through a bounded measurable feature map
`φ : K → E`: on `E` the band of `cor:oracle` holds for `w ↦ ⟪w, φ ·⟫` with any `N_s ≥ inf_{λ>0} √T_s`. -/
def oracle_band_ent : Prop :=
  ∀ (K E : Type) [MeasurableSpace K] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (φ : K → E) (n₀ n₁ : ℕ) (x₀ : Fin n₀ → K) (x₁ : Fin n₁ → K) (c : K → K → ℝ) (ε r₀ r₁ : ℝ)
    (𝒩₀ 𝒩₁ : Set (Measure K)) (P₀ P₁ : Measure K) (N₀ N₁ : E → ℝ),
    Measurable φ → (∃ M, ∀ z, ‖φ z‖ ≤ M) → 0 < n₀ → 0 < n₁ → 0 < ε →
    Measurable (Function.uncurry c) → (∀ a b, 0 ≤ c a b) → (∃ B, ∀ a b, c a b ≤ B) →
    RefClass 𝒩₀ → RefClass 𝒩₁ → InBall x₀ c ε r₀ 𝒩₀ P₀ → InBall x₁ c ε r₁ 𝒩₁ P₁ →
    (∀ w, 0 ≤ N₀ w) → (∀ w, 0 ≤ N₁ w) →
    (∀ w, ⨅ l : Set.Ioi (0 : ℝ), sqrtT x₀ c (fun z => ⟪w, φ z⟫_ℝ) ε r₀ l 𝒩₀ ≤ ENNReal.ofReal (N₀ w)) →
    (∀ w, ⨅ l : Set.Ioi (0 : ℝ), sqrtT x₁ c (fun z => ⟪w, φ z⟫_ℝ) ε r₁ l 𝒩₁ ≤ ENNReal.ofReal (N₁ w)) →
      BandHolds (P₀.map φ) (P₁.map φ) (unifW n₀) (fun i => φ (x₀ i)) (unifW n₁) (fun i => φ (x₁ i)) N₀ N₁

/-- `cor:oracle` at `ε > 0` on `E` (the conclusions of the frozen `oracle_sets` and `oracle_ineq`). -/
def oracle_ent : Prop :=
  ∀ (K E : Type) [MeasurableSpace K] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (φ : K → E) (n₀ n₁ : ℕ) (x₀ : Fin n₀ → K) (x₁ : Fin n₁ → K) (c : K → K → ℝ) (ε r₀ r₁ : ℝ)
    (𝒩₀ 𝒩₁ : Set (Measure K)) (P₀ P₁ : Measure K) (N₀ N₁ : E → ℝ) (δ : ℝ),
    Measurable φ → (∃ M, ∀ z, ‖φ z‖ ≤ M) → 0 < n₀ → 0 < n₁ → 0 < ε →
    Measurable (Function.uncurry c) → (∀ a b, 0 ≤ c a b) → (∃ B, ∀ a b, c a b ≤ B) →
    RefClass 𝒩₀ → RefClass 𝒩₁ → InBall x₀ c ε r₀ 𝒩₀ P₀ → InBall x₁ c ε r₁ 𝒩₁ P₁ →
    (∀ w, 0 ≤ N₀ w) → (∀ w, 0 ≤ N₁ w) →
    (∀ w, ⨅ l : Set.Ioi (0 : ℝ), sqrtT x₀ c (fun z => ⟪w, φ z⟫_ℝ) ε r₀ l 𝒩₀ ≤ ENNReal.ofReal (N₀ w)) →
    (∀ w, ⨅ l : Set.Ioi (0 : ℝ), sqrtT x₁ c (fun z => ⟪w, φ z⟫_ℝ) ε r₁ l 𝒩₁ ≤ ENNReal.ofReal (N₁ w)) → 0 ≤ δ →
      (certSet2 (P₀.map φ) (P₁.map φ) N₀ N₁ δ ⊆
          certSetN (unifW n₀) (fun i => φ (x₀ i)) (unifW n₁) (fun i => φ (x₁ i)) N₀ N₁ δ ∧
        certSetN (unifW n₀) (fun i => φ (x₀ i)) (unifW n₁) (fun i => φ (x₁ i)) N₀ N₁ δ ⊆
          {w | deltaPop (P₀.map φ) (P₁.map φ) w ≤ ENNReal.ofReal √δ}) ∧
      ∀ (R Rn : E → ℝ) (wh : E),
        wh ∈ certSetN (unifW n₀) (fun i => φ (x₀ i)) (unifW n₁) (fun i => φ (x₁ i)) N₀ N₁ δ →
        IsMinOn Rn (certSetN (unifW n₀) (fun i => φ (x₀ i)) (unifW n₁) (fun i => φ (x₁ i)) N₀ N₁ δ) wh →
          deltaPop (P₀.map φ) (P₁.map φ) wh ≤ ENNReal.ofReal √δ ∧
          ∀ w' ∈ certSet2 (P₀.map φ) (P₁.map φ) N₀ N₁ δ, ∀ B : ℝ,
            (∀ w ∈ certSetN (unifW n₀) (fun i => φ (x₀ i)) (unifW n₁) (fun i => φ (x₁ i)) N₀ N₁ δ,
              |Rn w - R w| ≤ B) → R wh ≤ R w' + 2 * B

/-! ### otfd C `lem:full-support-region`(i) -/

/-- `lem:full-support-region`(i): a closed convex `A ⊆ supp μ` with nonempty interior satisfies `A = cl(int A)`,
`μ(A ∩ N) > 0` for every open `N` meeting `A`, `supp(μ|_A) = A`, and `μ|_A-ess sup g = sup_A g` for continuous `g`. -/
def full_support_region : Prop :=
  ∀ (K : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin K))) (A : Set (EuclideanSpace ℝ (Fin K))),
    IsClosed A → Convex ℝ A → (interior A).Nonempty → A ⊆ μ.support →
      A = closure (interior A) ∧ (∀ N, IsOpen N → (N ∩ A).Nonempty → 0 < μ (A ∩ N)) ∧
      (μ.restrict A).support = A ∧
      ∀ g : EuclideanSpace ℝ (Fin K) → ℝ, ContinuousOn g A →
        essSup (fun u => ((g u : ℝ) : EReal)) (μ.restrict A) = ⨆ u ∈ A, ((g u : ℝ) : EReal)

/-- Absolute continuity and positive mass give a convex region nonempty interior. -/
def region_interior : Prop :=
  ∀ (K : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin K))) (A : Set (EuclideanSpace ℝ (Fin K))),
    μ ≪ volume → Convex ℝ A → 0 < μ A → (interior A).Nonempty

/-! ### otfd C `thm:neural-band-consistency` without `hsupp` (frozen Wave 7a claims) -/

/-- Wave 7a `neural_band_uniform` with `hsupp` discharged: `μ_K ≪ Leb`, convex level regions of positive mass. -/
def neural_band_uniform_convex : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ : Measure (EuclideanSpace ℝ (Fin K))) (O : Set (EuclideanSpace ℝ (Fin K)))
    (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (A : ℝ → Set (EuclideanSpace ℝ (Fin K)))
    (δ : ℝ) (mo : 𝒯 → ℝ) (e : 𝒯 → EuclideanSpace ℝ (Fin K)) (E : ℝ),
    NeuralSetting μ O Q A δ e E → μ ≪ volume →
    (∀ p, 0 < p → p ≤ 1 - δ → Convex ℝ (A p) ∧ 0 < μ (A p)) →
      ∀ ε, 0 < ε → ∃ η, 0 < η ∧ ∀ T : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K),
        MonoOn T O → risk μ O T Q ≤ ENNReal.ofReal η → BandsClose μ T Q A δ mo e ε

/-- Wave 7a `neural_band_ae` with `hsupp` discharged. -/
def neural_band_ae_convex : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ : Measure (EuclideanSpace ℝ (Fin K))) (O : Set (EuclideanSpace ℝ (Fin K)))
    (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (A : ℝ → Set (EuclideanSpace ℝ (Fin K)))
    (δ : ℝ) (mo : 𝒯 → ℝ) (e : 𝒯 → EuclideanSpace ℝ (Fin K)) (E : ℝ)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (T : ℕ → Ω → EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)),
    NeuralSetting μ O Q A δ e E → μ ≪ volume →
    (∀ p, 0 < p → p ≤ 1 - δ → Convex ℝ (A p) ∧ 0 < μ (A p)) →
    (∀ n ω, MonoOn (T n ω) O) →
    (∀ᵐ ω ∂P, Tendsto (fun n => risk μ O (T n ω) Q) atTop (𝓝 0)) →
      ∀ᵐ ω ∂P, ∀ ε, 0 < ε → ∀ᶠ n in atTop, BandsClose μ (T n ω) Q A δ mo e ε

/-- Wave 7a `neural_band_prob` with `hsupp` discharged (measurable-event convention on both sides). -/
def neural_band_prob_convex : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ : Measure (EuclideanSpace ℝ (Fin K))) (O : Set (EuclideanSpace ℝ (Fin K)))
    (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (A : ℝ → Set (EuclideanSpace ℝ (Fin K)))
    (δ : ℝ) (mo : 𝒯 → ℝ) (e : 𝒯 → EuclideanSpace ℝ (Fin K)) (E : ℝ)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (T : ℕ → Ω → EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)),
    NeuralSetting μ O Q A δ e E → μ ≪ volume →
    (∀ p, 0 < p → p ≤ 1 - δ → Convex ℝ (A p) ∧ 0 < μ (A p)) →
    (∀ n ω, MonoOn (T n ω) O) →
    (∀ η, 0 < η → ∀ δ', 0 < δ' → ∀ᶠ n in atTop, ∃ G : Set Ω, MeasurableSet G ∧
        G ⊆ {ω | risk μ O (T n ω) Q ≤ ENNReal.ofReal η} ∧ ENNReal.ofReal (1 - δ') ≤ P G) →
      ∀ ε, 0 < ε → ∀ δ', 0 < δ' → ∀ᶠ n in atTop, ∃ G : Set Ω, MeasurableSet G ∧
        G ⊆ {ω | BandsClose μ (T n ω) Q A δ mo e ε} ∧ ENNReal.ofReal (1 - δ') ≤ P G

/-- Wave 7a `neural_band_rate` (`eq:neural-band-rate`) with `hsupp` discharged. -/
def neural_band_rate_convex : Prop :=
  ∀ (K : ℕ) (ρ : ℝ), 0 < K → 0 < ρ → ∃ Cst : ℝ, 0 < Cst ∧
    ∀ (𝒯 : Type) (μ : Measure (EuclideanSpace ℝ (Fin K))) (O O' : Set (EuclideanSpace ℝ (Fin K)))
      (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (A : ℝ → Set (EuclideanSpace ℝ (Fin K)))
      (δ : ℝ) (mo : 𝒯 → ℝ) (e : 𝒯 → EuclideanSpace ℝ (Fin K)) (E L : ℝ),
      NeuralSetting μ O Q A δ e E → μ ≪ volume →
      (∀ p, 0 < p → p ≤ 1 - δ → Convex ℝ (A p) ∧ 0 < μ (A p)) →
      IsOpen O' → A (1 - δ) ⊆ O' → O' ⊆ O →
      (∀ B, MeasurableSet B → B ⊆ O' → ENNReal.ofReal ρ * volume B ≤ μ B) →
      0 < L → (∀ x ∈ O', ∀ y ∈ O', ‖Q x - Q y‖ ≤ L * ‖x - y‖) →
        ∃ R₀, 0 < R₀ ∧ ∀ R, 0 < R → R ≤ R₀ →
          ∀ T : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K),
            MonoOn T O → risk μ O T Q ≤ ENNReal.ofReal R →
              BandsClose μ T Q A δ mo e
                (E * Cst * L ^ ((K : ℝ) / (K + 2)) * R ^ ((1 : ℝ) / (K + 2)))

/-! ### otfd C `cor:net-inner-band-neural`, two-sided parts without `hsupp` (frozen Wave 16b claims) -/

/-- Wave 16b `net_inner_two_sided` with the support condition discharged. -/
def net_inner_two_sided_convex : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ : Measure (EuclideanSpace ℝ (Fin K))) (O : Set (EuclideanSpace ℝ (Fin K)))
    (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (A : ℝ → Set (EuclideanSpace ℝ (Fin K)))
    (δ : ℝ) (mo : 𝒯 → ℝ) (e : 𝒯 → EuclideanSpace ℝ (Fin K)) (E : ℝ)
    (T : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (N : ℝ → Finset (EuclideanSpace ℝ (Fin K)))
    (h η w : ℝ),
    0 < K → NeuralSetting μ O Q A δ e E → MonoOn Q O → μ ≪ volume →
    (∀ p, 0 < p → p ≤ 1 - δ → Convex ℝ (A p) ∧ 0 < μ (A p)) →
    0 ≤ η → (∀ u ∈ A (1 - δ), ‖T u - Q u‖ ≤ η) →
    (∀ x ∈ A (1 - δ), ∀ y ∈ A (1 - δ), ‖x - y‖ ≤ h → ‖Q x - Q y‖ ≤ w) →
    (∀ p, 0 < p → p ≤ 1 - δ → NetCovers (A p) (N p) h) →
      NetClose μ T Q A δ mo e N (E * (w + η))

/-- Wave 16b `net_band_neural_two_sided_ae` with the support condition discharged. -/
def net_band_neural_two_sided_ae_convex : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ : Measure (EuclideanSpace ℝ (Fin K))) (O : Set (EuclideanSpace ℝ (Fin K)))
    (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (A : ℝ → Set (EuclideanSpace ℝ (Fin K)))
    (δ : ℝ) (mo : 𝒯 → ℝ) (e : 𝒯 → EuclideanSpace ℝ (Fin K)) (E : ℝ)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (T : ℕ → Ω → EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (N : ℕ → ℝ → Finset (EuclideanSpace ℝ (Fin K))) (h : ℕ → ℝ),
    0 < K → NeuralSetting μ O Q A δ e E → MonoOn Q O → (∀ n ω, MonoOn (T n ω) O) → μ ≪ volume →
    (∀ p, 0 < p → p ≤ 1 - δ → Convex ℝ (A p) ∧ 0 < μ (A p)) →
    Tendsto h atTop (𝓝 0) → (∀ n p, 0 < p → p ≤ 1 - δ → NetCovers (A p) (N n p) (h n)) →
    (∀ᵐ ω ∂P, Tendsto (fun n => risk μ O (T n ω) Q) atTop (𝓝 0)) →
      ∀ᵐ ω ∂P, ∀ ε, 0 < ε → ∀ᶠ n in atTop, NetClose μ (T n ω) Q A δ mo e (N n) ε

/-- Wave 16b `net_band_neural_two_sided_prob` with the support condition discharged. -/
def net_band_neural_two_sided_prob_convex : Prop :=
  ∀ (K : ℕ) (𝒯 : Type) (μ : Measure (EuclideanSpace ℝ (Fin K))) (O : Set (EuclideanSpace ℝ (Fin K)))
    (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (A : ℝ → Set (EuclideanSpace ℝ (Fin K)))
    (δ : ℝ) (mo : 𝒯 → ℝ) (e : 𝒯 → EuclideanSpace ℝ (Fin K)) (E : ℝ)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (T : ℕ → Ω → EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K))
    (N : ℕ → ℝ → Finset (EuclideanSpace ℝ (Fin K))) (h : ℕ → ℝ),
    0 < K → NeuralSetting μ O Q A δ e E → MonoOn Q O → (∀ n ω, MonoOn (T n ω) O) → μ ≪ volume →
    (∀ p, 0 < p → p ≤ 1 - δ → Convex ℝ (A p) ∧ 0 < μ (A p)) →
    Tendsto h atTop (𝓝 0) → (∀ n p, 0 < p → p ≤ 1 - δ → NetCovers (A p) (N n p) (h n)) →
    (∀ η, 0 < η → ∀ δ', 0 < δ' → ∀ᶠ n in atTop, ∃ G : Set Ω, MeasurableSet G ∧
        G ⊆ {ω | risk μ O (T n ω) Q ≤ ENNReal.ofReal η} ∧ ENNReal.ofReal (1 - δ') ≤ P G) →
      ∀ ε, 0 < ε → ∀ δ', 0 < δ' → ∀ᶠ n in atTop, ∃ G : Set Ω, MeasurableSet G ∧
        G ⊆ {ω | NetClose μ (T n ω) Q A δ mo e (N n) ε} ∧ ENNReal.ofReal (1 - δ') ≤ P G

/-- Wave 16b `net_band_neural_rate` with the support condition discharged. -/
def net_band_neural_rate_convex : Prop :=
  ∀ (K : ℕ) (ρ : ℝ), 0 < K → 0 < ρ → ∃ Cst : ℝ, 0 < Cst ∧
    ∀ (𝒯 : Type) (μ : Measure (EuclideanSpace ℝ (Fin K))) (O O' : Set (EuclideanSpace ℝ (Fin K)))
      (Q : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K)) (A : ℝ → Set (EuclideanSpace ℝ (Fin K)))
      (δ : ℝ) (mo : 𝒯 → ℝ) (e : 𝒯 → EuclideanSpace ℝ (Fin K)) (E L : ℝ),
      NeuralSetting μ O Q A δ e E → MonoOn Q O → μ ≪ volume →
      (∀ p, 0 < p → p ≤ 1 - δ → Convex ℝ (A p) ∧ 0 < μ (A p)) →
      IsOpen O' → A (1 - δ) ⊆ O' → O' ⊆ O →
      (∀ B, MeasurableSet B → B ⊆ O' → ENNReal.ofReal ρ * volume B ≤ μ B) →
      0 < L → (∀ x ∈ O', ∀ y ∈ O', ‖Q x - Q y‖ ≤ L * ‖x - y‖) →
        ∃ R₀, 0 < R₀ ∧ ∀ R, 0 < R → R ≤ R₀ →
          ∀ T : EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin K),
            MonoOn T O → risk μ O T Q ≤ ENNReal.ofReal R →
              ∀ (N : ℝ → Finset (EuclideanSpace ℝ (Fin K))) (h : ℝ), 0 ≤ h →
                (∀ p, 0 < p → p ≤ 1 - δ → NetCovers (A p) (N p) h) →
                  NetClose μ T Q A δ mo e N
                    (E * (L * h + Cst * L ^ ((K : ℝ) / (K + 2)) * R ^ ((1 : ℝ) / (K + 2))))

/-! ### otfd C `prop:fixed-sieve-collapse`: `f₀` is a hard-OT dual potential -/

open StatFormal.Wave12b (coup Marg) in
/-- Entropic: plans `π_k = exp((f_k ⊕ g_k − C)/θ_k)` in `Π(r,b)`, `θ_k → 0⁺`, `f_k → f₀`; then `g_k → g₀ = min_i(C_{i·} −
f₀ i)` and `(f₀, g₀)` is a hard-OT dual potential pair. -/
def fs_hard_dual_ent : Prop :=
  ∀ (n m : ℕ) (C : Fin n → Fin m → ℝ) (r : Fin n → ℝ) (b : Fin m → ℝ) (θ : ℕ → ℝ) (f : ℕ → Fin n → ℝ)
    (g : ℕ → Fin m → ℝ) (π : ℕ → Fin n → Fin m → ℝ) (f₀ : Fin n → ℝ),
    Marg r b → Tendsto θ atTop (𝓝[>] 0) → (∀ k, π k ∈ coup r b) →
    (∀ k i j, π k i j = Real.exp ((f k i + g k j - C i j) / θ k)) → Tendsto f atTop (𝓝 f₀) →
      Tendsto g atTop (𝓝 (fun j => ⨅ i, (C i j - f₀ i))) ∧ IsHardDual C r b f₀ (fun j => ⨅ i, (C i j - f₀ i))

open StatFormal.Wave12b (coup Marg) in
/-- Quadratic: plans `π_k = (f_k ⊕ g_k − C)_+/θ_k` in `Π(r,b)`, `θ_k → 0⁺`, `f_k → f₀`; same conclusion. -/
def fs_hard_dual_quad : Prop :=
  ∀ (n m : ℕ) (C : Fin n → Fin m → ℝ) (r : Fin n → ℝ) (b : Fin m → ℝ) (θ : ℕ → ℝ) (f : ℕ → Fin n → ℝ)
    (g : ℕ → Fin m → ℝ) (π : ℕ → Fin n → Fin m → ℝ) (f₀ : Fin n → ℝ),
    Marg r b → Tendsto θ atTop (𝓝[>] 0) → (∀ k, π k ∈ coup r b) →
    (∀ k i j, π k i j = max 0 (f k i + g k j - C i j) / θ k) → Tendsto f atTop (𝓝 f₀) →
      Tendsto g atTop (𝓝 (fun j => ⨅ i, (C i j - f₀ i))) ∧ IsHardDual C r b f₀ (fun j => ⨅ i, (C i j - f₀ i))

end Claims

end StatFormal.Gaps1
