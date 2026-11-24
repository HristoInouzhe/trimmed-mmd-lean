import StatFormal.Archive.RobustEquality.Tax.Statements
import StatFormal.Archive.RobustEquality.Strong.Statements
import StatFormal.Archive.Wave4b.Statements
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# FROZEN STATEMENTS — wave 11a (QUEUE rows 93–96): robust equality JASA `cor:dominated`, `lem:kernel`,
# `prop:cs-compose`, `prop:ep-gauss`

Sources (verbatim in `lean-formalisation/inventory/extracted/robust-equality-jasa.md`; current text after the
2026-10-13/14 corrections; paths relative to `robust-equality-outcomes-under-distribution-shift/jasa/`):
* `cor:dominated` (`supp_proofs.tex:495-510`, proof `:512-521`), with `thm:ghost` (`main.tex:465-472`, proof
  `supp_proofs.tex:454-472`), `lem:tax` (`main.tex:243-253`), `def:family` (`main.tex:236-241`), `eq:T`
  (`main.tex:348-352`) and the reference convention (`supp_proofs.tex:15-23`: `0 < ν(K) ≤ 1`,
  `KL(Q‖ν) = ∫ log(dQ/dν) dQ`).
* `lem:kernel` (`main.tex:265-272`, proof `supp_proofs.tex:186-201`, `eq:floorid`), with the notation block
  (`supp_proofs.tex:25-33`: labelled atoms, `G_ν(Γ)`, `ρ_ν`, `R^𝒩_min = inf_ν ρ_ν`) and `lem:gibbs`
  (`supp_proofs.tex:52-60`).
* `prop:cs-compose` (`supp_common_shift.tex:393-402`, proof `:404-411`), with the notation header
  (`supp_common_shift.tex:6-13`).
* `prop:ep-gauss` (`supp_eps.tex:330-341`, proof `:343-348`), with the notation header (`supp_eps.tex:5-15`) and
  `Ψ_ε`, `T_ε(λ; R_ε + β) = λβ + Ψ_ε(λ)` (`supp_eps.tex:296-298`).
Reuses the frozen `RobustEquality/Statements.lean` (`klRef`, `lem_gibbs`'s `tilted`), `SemidualStrong` (`OTdisc`,
`Setting`, `muDisc`), `Tax` (`Wdisc`, `tax`, `ballN`), `Certificate` (`centre`, `KernelWitness`, `Tref1`),
`Strong` (`budget` = `G_ν`, `floorRef` = `ρ_ν`) and `Wave4b` (`RefClass`, `InBall`, `sqrtT`) statements, and Tau Ceti's `wassersteinEDist`, imported, not copied.

Covered:
* `cor:dominated`: `dom_tax_finite` (`τ_{𝒩_κ}(Q) = log(1/κ)` for finitely supported `Q`), `dom_tax_le`
  (`KL(Q‖(1−κ)ν₀ + κQ) ≤ log(1/κ)`, hence `τ_{𝒩_κ} ≤ log(1/κ)` everywhere), `dom_aN` (`a_{𝒩_κ} = log(1/κ)`),
  `dom_valid` ((i), **conditional on the general clause of `thm:ghost`**, the hypothesis `GhostAt` at `𝒩 = 𝒩_κ`),
  `dom_ball` ((ii), the inclusion), `dom_worst` ((ii), the worst cases), `dom_cert` ((iii), member by member and
  for the supremum `√T`).
* `lem:kernel`: `kernel_value` (`W^ν_ε(P̂,Q)` is the **minimum** over labelled kernels with `P̂Γ = Q` of
  `G_ν(Γ)`), `kernel_iff` (the membership "if and only if"), `kernel_floor_min` (`eq:floorid` consequence:
  `min_Γ G_ν(Γ) = ρ_ν`, attained only at the Gibbs kernel), `kernel_floor_ref` (one reference: non-empty iff
  `r ≥ ρ_ν`), `kernel_floor` (a class: non-empty only if `r ≥ R_min`, if `r > R_min`, and iff `r ≥ R_min` when the
  infimum is attained), `kernel_floor_compact` (weakly compact classes: non-empty iff `r ≥ R_min`).
* `prop:cs-compose`: `cs_compose` (`OT_ε(μ,Q) ≤ (√OT_ε(μ,P) + W₂(P,Q))²`, all quantities finite),
  `cs_compose_ball` (the free-end membership of the consequence, given the transport bound at the transported
  centre).
* `prop:ep-gauss`: `gauss_xstar` (`x − log x = 1 + 2β/ε` has a unique root `x* > 1`), `gauss_inf`
  (`inf_{λ>|w|²} T_ε = |w|²(β + ε/2 (1 + log x*)) = |w|² ε x*/2`, a minimum when `w ≠ 0`), `gauss_bounds` (the
  two-sided bound), `gauss_root` (the two root-unit bounds on the excess).

Not covered (declared):
* `cor:dominated`: the general (finite-`a_𝒩`) clause of `thm:ghost` itself (BACKLOG; entered as the explicit
  hypothesis `GhostAt … 𝒩_κ …` of `dom_valid`; `GhostGeneral` implies it); weak compactness of `𝒩_κ` (the proof's attainment remark — not
  needed: (ii) uses the explicit member `(1−κ)ν₀ + κQ`); the closing sentence ("valid exactly when … never
  smaller", a reading of (i)–(iii)); the mortgage-data numbers.
* `lem:kernel`: lower semicontinuity of the objective on `Π(P̂,Q)` (replaced by the certified strong duality, which
  gives attainment); weak continuity of `ν ↦ ρ_ν` beyond what `kernel_floor_compact` uses.
* `prop:cs-compose`: a general (non-discrete) first marginal `μ` (specialised to labelled atoms, the case the
  consequence uses: `μ = (T_θ)_#P̂_s`); the carry step `OT_ε((T_θ)_#P̂_s,(T_θ)_#P_s) ≤ max(1,‖A_θ‖²) r̂_s`
  (`prop:cs-carry`, a different proposition; `cs_compose_ball` takes the transported bound `ρ` as input, and
  `(max(1,‖A‖)√r̂ + √β)² = (√(max(1,‖A‖²) r̂) + √β)²`); "the free-class certificate of `thm:cs-certificate` at these
  radii bounds the deployment disparity on the calibrated event" (a pointer to frozen `cs_certificate`).
* `prop:ep-gauss`: the Gaussian identities `K^ε_{x₀} = N(x₀, ε/2 I)`, `B_ε = |w|²ε/2` and
  `T_ε(λ; R_ε + β) = λβ − (λε/2) log(1 − |w|²/λ)` (the Gaussian integral; the claims start from this formula,
  `Tgauss`); "against `|w|²β` for the `ε = 0` member" (a comparison with `thm:ep-cert0`).

Encodings (see card):
* Centres: labelled atoms. `cor:dominated` (i)–(ii) and `prop:cs-compose` use the `Tax`/`SemidualStrong`
  encoding (`μ = muDisc a`, `a_i > 0`, `Σ a = 1`, costs `c_i = c(x_i,·)` bounded measurable, `Setting`);
  `lem:kernel` links it with the `Certificate` kernel encoding (`P̂ = n⁻¹Σδ_{x_i}`, `a = 1/n`,
  `c_i = c(x_i,·)`, kernels `Γ : Fin n → Measure K` of probabilities, `P̂Γ = n⁻¹ Σ Γ_i`, the frozen
  `KernelWitness`); (iii) uses `Tref1`/`sqrtT`. `K` is any measurable space (paper: compact `K ⊂ ℝ^d`); for
  `prop:cs-compose` a compact metric space with `c = dist²` (paper: `K_Θ` compact, `c = ‖·‖²`).
* References: finite measures (`RefClass`: `0 < ν(K) ≤ 1` where the paper needs it); `KL` = frozen `klRef`.
  `𝒩_κ = {(1−κ)ν₀ + κm : m ∈ 𝒫(K)}` is `defMix ν₀ κ` (weights `ENNReal.ofReal`); `𝒫(K)` is `freeClass`;
  "no atom in `K`" is `ν₀{y} = 0` for every `y` (measurable singletons); "finitely supported" is `FinSupp`
  (`Q(sᶜ) = 0` for a finite set `s`, as in the frozen `ghost_atomless`); `a_𝒩` is `aN`, an `EReal` infimum (`⊤`
  for atomless classes, no junk).
* Radii are `EReal` in the `Tax` encoding (`r − ε log(1/κ)` is `EReal` subtraction of a real), real in the
  kernel encoding (as in the frozen `KernelWitness`).
* `cor:dominated` (i): a radius is a measurable `r̂ : (Fin n → K) → EReal` of an i.i.d. sample
  (`Measure.pi`), validity over finitely supported laws bounds the (outer) measure of the membership set, as in
  the frozen `ghost_atomless` (a weaker hypothesis); the conclusion uses the measurable-event convention (∃
  measurable `E ⊆ {P ∈ 𝓑^{𝒫(K)}(r̂ − ε log(1/κ))}` with `P^{⊗n}(E) ≥ 1 − α`). `GhostAt` is `thm:ghost`'s
  general clause in exactly this encoding (cost jointly measurable and bounded; conclusion
  `Pr_P[r̂ ≥ OT_ε(P̂,P) + ε a_𝒩] ≥ 1 − α`, measurable-event convention).
* `cor:dominated` (ii), worst cases: `worstPair` is `sup_{(Q₀,Q₁) ∈ 𝓑₀×𝓑₁} W₂²(h#Q₀, h#Q₁)` in `ℝ≥0∞` (Tau
  Ceti `W₂`; `⨆` over the empty set is `0`, the right value for a supremum of nonnegative quantities).
* `cor:dominated` (iii): `T^{𝒩}_s(h,λ; r)` is the frozen `sqrtT` (`⨆_ν ofReal √T^{{ν}}`, monotone in
  `T^{𝒩}`); the member-wise inequality is stated for `Tref1` in `ℝ` (bounded `c`, `h`: every integral is of a
  bounded measurable function against a finite measure, no junk).
* `lem:kernel`: `G_ν(Γ)` is the frozen `Strong.budget` (the `KernelWitness` expression, in `EReal`); `ρ_ν` is the
  frozen `Strong.floorRef` (real:
  `∫ e^{−c(x_i,·)/ε} dν > 0` for bounded `c` and `ν(K) > 0`, so the logarithm is not junk); `R^𝒩_min` is
  `floorN = ⨅_{ν∈𝒩} ρ_ν` in `EReal` (no junk for empty or unbounded classes; the paper's
  `−ε sup_ν E log E e^{−c/ε}`); "the set is non-empty" is `∃ Q, InBall …` (frozen kernel form; `kernel_iff` makes
  it the coupling form). "Weakly compact `𝒩`" is a compact set of Mathlib's `FiniteMeasure K` (weak topology) on
  a compact metric `K` with continuous `c`; the Gibbs kernel is Mathlib's `ν.tilted (−c(x_i,·)/ε)`.
* `prop:cs-compose`: `OT_ε` is the frozen `OTdisc` (`EReal`); the claim also asserts `0 ≤ OT_ε(μ,P) < ⊤` and
  `W₂(P,Q) < ⊤`, so the `toReal`s are not junk. `cs_compose_ball` takes `ρ ≥ 0` with `OT_ε(μ,P) ≤ ρ` and `β ≥ 0`
  with `W₂²(P,Q) ≤ β` (here `μ` = the transported centre, `P` = the transported population, `Q` = the deployment).
* `prop:ep-gauss`: `|w|² = ‖w‖²` for `w ∈ ℝ^d` (`EuclideanSpace`); `T_ε(λ; R_ε + β) = Tgauss ‖w‖² β ε λ` on
  `λ > ‖w‖²` (for `λ ≤ ‖w‖²` the Gaussian integral diverges and `T_ε = +∞`, so the infimum is over
  `Ioi ‖w‖²`); `inf` is `IsGLB` of the image (for `w = 0` the infimum `0` is not attained), and `IsLeast` when
  `w ≠ 0`; `x*` enters as any `x > 1` with `x − log x = 1 + 2β/ε` (unique by `gauss_xstar`).
Critic notes:
* `cor:dominated` holds as printed; the atomless hypothesis on `ν₀` is used only for `τ = log(1/κ)` on finitely
  supported laws (and hence (i)); (ii) and (iii) hold for every finite `ν₀`. (i) is only as strong as
  `GhostAt K n ε α cost 𝒩_κ r̂` (the general clause of `thm:ghost` at the one setting used). `GhostGeneral` (all
  settings: any measurable space, any bounded jointly measurable cost, any finite references, outer-measure
  hypothesis, inner-measure conclusion) is strictly stronger than the paper's theorem and is kept only as a
  sufficient condition; we believe it true (the weak-continuity step needs only lower semicontinuity of
  `OT_ε(P̂,·)` along the ghost empirical laws, from the semidual and the strong law of large numbers).
* `lem:kernel` holds as printed. "For weakly compact `𝒩`" needs continuity of `c` (true for `‖·‖²`).
* `prop:cs-compose` holds as printed. The route is dual (no gluing or data processing needed):
  `|x_i − z|² ≤ (1+t)|x_i − y|² + (1+1/t)|y − z|²` shifts the soft-min potential along an optimal `W₂` coupling,
  weak duality for the cost `(1+t)c` gives `OT_ε(μ,Q) ≤ (1+t)OT_ε(μ,P) + (1+1/t)W₂²`, and then minimise over `t`.
* `prop:ep-gauss`: the printed formulas hold, including the root bounds (the printed
  `√(a+b) − √a ≥ b/(2√(a+b))` with `b = (ε/2)(1 + log x*) ≥ ε/2` suffices, since `b ↦ b/√(β+b)` is increasing).
* "Weakly compact `𝒩`" read as a compact set of `FiniteMeasure K` covers the paper's case; compactness of
  restrictions to `K` of laws on `ℝ^d` (as for `𝒩_b`) is a different notion, not covered by `kernel_floor_compact`.
* `prop:cs-compose`: restricting `μ` to labelled atoms loses no content the paper uses (`μ = (T_θ)_#P̂_s`), and
  taking the transported bound `ρ` as an input is faithful (the carry step is `prop:cs-carry`).
* Paper nits (S4): `cor:dominated` writes the level `1−a` where `thm:ghost` uses `α`; the `prop:ep-gauss` proof's
  substitution `λ = |w|²/(1−s)` tacitly assumes `w ≠ 0`; the weak-compactness remark in the `cor:dominated` proof
  is unnecessary (`m = Q` attains the tax).
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory TauCeti Set
open scoped ENNReal NNReal

namespace StatFormal.Wave11a

open StatFormal.RobustEquality StatFormal.RobustEquality.Tax StatFormal.RobustEquality.SemidualStrong
  StatFormal.RobustEquality.Certificate

section Classes

variable {K : Type} [MeasurableSpace K]

/-- The defensive-mixture class `𝒩_κ = {(1−κ)ν₀ + κm : m ∈ 𝒫(K)}`. -/
def defMix (ν₀ : Measure K) (κ : ℝ) : Set (Measure K) :=
  {ν | ∃ m : Measure K, IsProbabilityMeasure m ∧
    ν = ENNReal.ofReal (1 - κ) • ν₀ + ENNReal.ofReal κ • m}

/-- The free class `𝒫(K)`. -/
def freeClass : Set (Measure K) := {ν | IsProbabilityMeasure ν}

/-- `Q` is finitely supported: `Q(sᶜ) = 0` for a finite set `s`. -/
def FinSupp (Q : Measure K) : Prop := ∃ s : Finset K, Q (↑s : Set K)ᶜ = 0

/-- `a_𝒩 = inf {τ_𝒩(Q) : Q finitely supported}` (`thm:ghost`), in `EReal`. -/
def aN (𝒩 : Set (Measure K)) : EReal :=
  ⨅ (Q : Measure K) (_ : IsProbabilityMeasure Q ∧ FinSupp Q), tax 𝒩 Q

/-- The worst-case disparity `sup_{(Q₀,Q₁) ∈ 𝓑^{𝒩₀}(r₀) × 𝓑^{𝒩₁}(r₁)} W₂²(h#Q₀, h#Q₁)` over coupling-form balls. -/
def worstPair {k₀ k₁ : ℕ} (𝒩₀ 𝒩₁ : Set (Measure K)) (ε : ℝ) (a₀ : Fin k₀ → ℝ) (c₀ : Fin k₀ → K → ℝ)
    (r₀ : EReal) (a₁ : Fin k₁ → ℝ) (c₁ : Fin k₁ → K → ℝ) (r₁ : EReal) (h : K → ℝ) : ℝ≥0∞ :=
  ⨆ (Q₀ : Measure K) (_ : Q₀ ∈ ballN 𝒩₀ ε a₀ c₀ r₀) (Q₁ : Measure K) (_ : Q₁ ∈ ballN 𝒩₁ ε a₁ c₁ r₁),
    wassersteinEDist 2 (Q₀.map h) (Q₁.map h) ^ 2

/-- The floor `R^𝒩_min = inf_{ν ∈ 𝒩} ρ_ν`, in `EReal`. -/
def floorN {n : ℕ} (x : Fin n → K) (c : K → K → ℝ) (ε : ℝ) (𝒩 : Set (Measure K)) : EReal :=
  ⨅ ν ∈ 𝒩, ((StatFormal.RobustEquality.Strong.floorRef x c ε ν : ℝ) : EReal)

end Classes

/-- `T_ε(λ; R_ε + β) = λβ − (λε/2) log(1 − |w|²/λ)` (`prop:ep-gauss`, `A = |w|²`). -/
def Tgauss (A β ε lam : ℝ) : ℝ := lam * β - lam * ε / 2 * Real.log (1 - A / lam)

/-- The general clause of `thm:ghost` for one fixed setting `(K, n, ε, α, cost, 𝒩, r̂)`, in the frozen `Tax`
encoding: if `r̂` covers every finitely supported population at level `1 − α`, then for every population
`Pr_P[r̂ ≥ OT_ε(P̂,P) + ε a_𝒩] ≥ 1 − α` (measurable-event convention). Uncertified (BACKLOG); used only as a
hypothesis, at the single instance `dom_valid` needs. -/
def GhostAt (K : Type) [MeasurableSpace K] (n : ℕ) (ε α : ℝ) (cost : K → K → ℝ) (𝒩 : Set (Measure K))
    (r : (Fin n → K) → EReal) : Prop :=
  0 < n → 0 < ε → Measurable (Function.uncurry cost) → (∃ B, ∀ x0 y, |cost x0 y| ≤ B) →
    (∀ ν ∈ 𝒩, IsFiniteMeasure ν) → Measurable r →
    (∀ Q : Measure K, IsProbabilityMeasure Q → FinSupp Q →
      ENNReal.ofReal (1 - α) ≤ (Measure.pi fun _ : Fin n => Q)
        {x | Q ∈ ballN 𝒩 ε (fun _ => (1 : ℝ) / n) (fun i => cost (x i)) (r x)}) →
    ∀ P : Measure K, IsProbabilityMeasure P →
      ∃ E : Set (Fin n → K), MeasurableSet E ∧
        E ⊆ {x | OTdisc ε (fun _ => (1 : ℝ) / n) (fun i => cost (x i)) P + (ε : EReal) * aN 𝒩 ≤ r x} ∧
        ENNReal.ofReal (1 - α) ≤ (Measure.pi fun _ : Fin n => P) E

/-- The general clause of `thm:ghost` in every setting (stronger than the paper's; implies every `GhostAt`). -/
def GhostGeneral : Prop :=
  ∀ (K : Type) [MeasurableSpace K] [MeasurableSingletonClass K] (n : ℕ) (ε α : ℝ) (cost : K → K → ℝ)
    (𝒩 : Set (Measure K)) (r : (Fin n → K) → EReal), GhostAt K n ε α cost 𝒩 r

namespace Claims

/-! ### `cor:dominated` -/

/-- `τ_{𝒩_κ}(Q) = log(1/κ)` for every finitely supported `Q`, when `ν₀` has no atom. -/
def dom_tax_finite : Prop :=
  ∀ (K : Type) [MeasurableSpace K] [MeasurableSingletonClass K] (ν₀ : Measure K) [IsFiniteMeasure ν₀]
    (κ : ℝ) (Q : Measure K) [IsProbabilityMeasure Q],
    0 < κ → κ ≤ 1 → ν₀ Set.univ ≤ 1 → (∀ y, ν₀ {y} = 0) → FinSupp Q →
      tax (defMix ν₀ κ) Q = ((Real.log (1 / κ) : ℝ) : EReal)

/-- `KL(Q‖(1−κ)ν₀ + κQ) ≤ log(1/κ)`, so `τ_{𝒩_κ}(Q) ≤ log(1/κ)` for every `Q`. -/
def dom_tax_le : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (ν₀ : Measure K) [IsFiniteMeasure ν₀] (κ : ℝ) (Q : Measure K)
    [IsProbabilityMeasure Q],
    0 < κ → κ ≤ 1 →
      ENNReal.ofReal (1 - κ) • ν₀ + ENNReal.ofReal κ • Q ∈ defMix ν₀ κ ∧
      klRef Q (ENNReal.ofReal (1 - κ) • ν₀ + ENNReal.ofReal κ • Q) ≤ ((Real.log (1 / κ) : ℝ) : EReal) ∧
      tax (defMix ν₀ κ) Q ≤ ((Real.log (1 / κ) : ℝ) : EReal)

/-- `a_{𝒩_κ} = log(1/κ)`. -/
def dom_aN : Prop :=
  ∀ (K : Type) [MeasurableSpace K] [MeasurableSingletonClass K] [Nonempty K] (ν₀ : Measure K)
    [IsFiniteMeasure ν₀] (κ : ℝ),
    0 < κ → κ ≤ 1 → ν₀ Set.univ ≤ 1 → (∀ y, ν₀ {y} = 0) →
      aN (defMix ν₀ κ) = ((Real.log (1 / κ) : ℝ) : EReal)

/-- (i), given the general clause of `thm:ghost`: a radius valid for `𝒩_κ` over the finitely supported laws,
minus `ε log(1/κ)`, is a valid radius for the free class at every population. -/
def dom_valid : Prop :=
  ∀ (K : Type) [MeasurableSpace K] [MeasurableSingletonClass K] (n : ℕ) (ε α κ : ℝ) (cost : K → K → ℝ)
    (ν₀ : Measure K) [IsFiniteMeasure ν₀] (r : (Fin n → K) → EReal),
    GhostAt K n ε α cost (defMix ν₀ κ) r →
    0 < n → 0 < ε → 0 < κ → κ ≤ 1 → ν₀ Set.univ ≤ 1 → (∀ y, ν₀ {y} = 0) →
    Measurable (Function.uncurry cost) → (∃ B, ∀ x0 y, |cost x0 y| ≤ B) → Measurable r →
    (∀ Q : Measure K, IsProbabilityMeasure Q → FinSupp Q →
      ENNReal.ofReal (1 - α) ≤ (Measure.pi fun _ : Fin n => Q)
        {x | Q ∈ ballN (defMix ν₀ κ) ε (fun _ => (1 : ℝ) / n) (fun i => cost (x i)) (r x)}) →
    ∀ P : Measure K, IsProbabilityMeasure P →
      ∃ E : Set (Fin n → K), MeasurableSet E ∧
        E ⊆ {x | P ∈ ballN freeClass ε (fun _ => (1 : ℝ) / n) (fun i => cost (x i))
          (r x - ((ε * Real.log (1 / κ) : ℝ) : EReal))} ∧
        ENNReal.ofReal (1 - α) ≤ (Measure.pi fun _ : Fin n => P) E

/-- (ii) `𝓑^{𝒫(K)}(r − ε log(1/κ)) ⊆ 𝓑^{𝒩_κ}(r)`. -/
def dom_ball : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k : ℕ) (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (ν₀ : Measure K) [IsFiniteMeasure ν₀] (κ : ℝ) (r : EReal),
    Setting ε a c → 0 < κ → κ ≤ 1 →
      ballN freeClass ε a c (r - ((ε * Real.log (1 / κ) : ℝ) : EReal)) ⊆ ballN (defMix ν₀ κ) ε a c r

/-- (ii) the worst-case disparity over `𝒩_κ`-sets at radii `r_s` is at least that over free sets at radii
`r_s − ε log(1/κ)`. -/
def dom_worst : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k₀ k₁ : ℕ) (ε : ℝ) (a₀ : Fin k₀ → ℝ) (c₀ : Fin k₀ → K → ℝ)
    (a₁ : Fin k₁ → ℝ) (c₁ : Fin k₁ → K → ℝ) (ν₀ : Measure K) [IsFiniteMeasure ν₀] (κ : ℝ)
    (r₀ r₁ : EReal) (h : K → ℝ),
    Setting ε a₀ c₀ → Setting ε a₁ c₁ → 0 < κ → κ ≤ 1 → Measurable h →
      worstPair freeClass freeClass ε a₀ c₀ (r₀ - ((ε * Real.log (1 / κ) : ℝ) : EReal)) a₁ c₁
          (r₁ - ((ε * Real.log (1 / κ) : ℝ) : EReal)) h ≤
        worstPair (defMix ν₀ κ) (defMix ν₀ κ) ε a₀ c₀ r₀ a₁ c₁ r₁ h

/-- (iii) `T^{𝒩_κ}_s(h,λ; r) ≥ T^{𝒫(K)}_s(h,λ; r − ε log(1/κ))`: member by member, and for the supremum. -/
def dom_cert : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n : ℕ) (x : Fin n → K) (c : K → K → ℝ) (h : K → ℝ) (ε r lam : ℝ)
    (ν₀ : Measure K) [IsFiniteMeasure ν₀] (κ : ℝ),
    0 < n → 0 < ε → 0 < lam → 0 < κ → κ ≤ 1 →
    Measurable (Function.uncurry c) → (∃ B, ∀ a b, |c a b| ≤ B) → Measurable h → (∃ H, ∀ z, |h z| ≤ H) →
      (∀ m : Measure K, IsProbabilityMeasure m →
        Tref1 x c h ε (r - ε * Real.log (1 / κ)) lam m ≤
          Tref1 x c h ε r lam (ENNReal.ofReal (1 - κ) • ν₀ + ENNReal.ofReal κ • m)) ∧
      StatFormal.Wave4b.sqrtT x c h ε (r - ε * Real.log (1 / κ)) lam freeClass ≤
        StatFormal.Wave4b.sqrtT x c h ε r lam (defMix ν₀ κ)

/-! ### `lem:kernel` -/

/-- `W^ν_ε(P̂,Q)` is the minimum, over labelled kernels with `P̂Γ = Q`, of `G_ν(Γ)`. -/
def kernel_value : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n : ℕ) (x : Fin n → K) (c : K → K → ℝ) (ε : ℝ) (ν Q : Measure K)
    [IsFiniteMeasure ν] [IsProbabilityMeasure Q],
    0 < n → 0 < ε → (∀ y, Measurable (c y)) → (∃ B, ∀ a b, |c a b| ≤ B) →
      IsLeast {v | ∃ Γ : Fin n → Measure K, (∀ i, IsProbabilityMeasure (Γ i)) ∧
          Q = (n : ℝ≥0∞)⁻¹ • ∑ i, Γ i ∧ v = StatFormal.RobustEquality.Strong.budget x c ε ν Γ}
        (Wdisc ε (fun _ => (1 : ℝ) / n) (fun i => c (x i)) ν Q)

/-- `Q ∈ 𝓑^𝒩(r)` iff some `ν ∈ 𝒩` and kernel `Γ` have `P̂Γ = Q` and `G_ν(Γ) ≤ r`. -/
def kernel_iff : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n : ℕ) (x : Fin n → K) (c : K → K → ℝ) (ε r : ℝ)
    (𝒩 : Set (Measure K)) (Q : Measure K) [IsProbabilityMeasure Q],
    0 < n → 0 < ε → (∀ y, Measurable (c y)) → (∃ B, ∀ a b, |c a b| ≤ B) →
    (∀ ν ∈ 𝒩, IsFiniteMeasure ν) →
      (Q ∈ ballN 𝒩 ε (fun _ => (1 : ℝ) / n) (fun i => c (x i)) (r : EReal) ↔
        ∃ ν ∈ 𝒩, KernelWitness x c ε r ν Q)

/-- `min_Γ G_ν(Γ) = ρ_ν`, attained only at the Gibbs kernel `K^ν_{x_i} ∝ e^{−c(x_i,·)/ε} ν`. -/
def kernel_floor_min : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n : ℕ) (x : Fin n → K) (c : K → K → ℝ) (ε : ℝ) (ν : Measure K)
    [IsFiniteMeasure ν],
    0 < n → 0 < ε → (∀ y, Measurable (c y)) → (∃ B, ∀ a b, |c a b| ≤ B) → ν Set.univ ≠ 0 →
      IsLeast {v | ∃ Γ : Fin n → Measure K, (∀ i, IsProbabilityMeasure (Γ i)) ∧ v = StatFormal.RobustEquality.Strong.budget x c ε ν Γ}
          ((StatFormal.RobustEquality.Strong.floorRef x c ε ν : ℝ) : EReal) ∧
        ∀ Γ : Fin n → Measure K, (∀ i, IsProbabilityMeasure (Γ i)) →
          StatFormal.RobustEquality.Strong.budget x c ε ν Γ = ((StatFormal.RobustEquality.Strong.floorRef x c ε ν : ℝ) : EReal) →
            ∀ i, Γ i = ν.tilted (fun z => -c (x i) z / ε)

/-- One reference: `{Q : W^ν_ε(P̂,Q) ≤ r} ≠ ∅` iff `r ≥ ρ_ν`. -/
def kernel_floor_ref : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n : ℕ) (x : Fin n → K) (c : K → K → ℝ) (ε r : ℝ) (ν : Measure K)
    [IsFiniteMeasure ν],
    0 < n → 0 < ε → (∀ y, Measurable (c y)) → (∃ B, ∀ a b, |c a b| ≤ B) → ν Set.univ ≠ 0 →
      ((∃ Q : Measure K, IsProbabilityMeasure Q ∧ KernelWitness x c ε r ν Q) ↔ StatFormal.RobustEquality.Strong.floorRef x c ε ν ≤ r)

/-- A class: `𝓑^𝒩(r) ≠ ∅` only if `r ≥ R^𝒩_min`, if `r > R^𝒩_min`, and iff `r ≥ R^𝒩_min` when the infimum
defining the floor is attained. -/
def kernel_floor : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (n : ℕ) (x : Fin n → K) (c : K → K → ℝ) (ε r : ℝ)
    (𝒩 : Set (Measure K)),
    0 < n → 0 < ε → (∀ y, Measurable (c y)) → (∃ B, ∀ a b, |c a b| ≤ B) →
    StatFormal.Wave4b.RefClass 𝒩 →
      ((∃ Q, StatFormal.Wave4b.InBall x c ε r 𝒩 Q) → floorN x c ε 𝒩 ≤ (r : EReal)) ∧
      (floorN x c ε 𝒩 < (r : EReal) → ∃ Q, StatFormal.Wave4b.InBall x c ε r 𝒩 Q) ∧
      ((∃ ν ∈ 𝒩, ((StatFormal.RobustEquality.Strong.floorRef x c ε ν : ℝ) : EReal) = floorN x c ε 𝒩) →
        ((∃ Q, StatFormal.Wave4b.InBall x c ε r 𝒩 Q) ↔ floorN x c ε 𝒩 ≤ (r : EReal)))

/-- Weakly compact classes (compact metric `K`, continuous `c`): `𝓑^𝒩(r) ≠ ∅` iff `r ≥ R^𝒩_min`. -/
def kernel_floor_compact : Prop :=
  ∀ (K : Type) [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (n : ℕ)
    (x : Fin n → K) (c : K → K → ℝ) (ε r : ℝ) (𝒩 : Set (FiniteMeasure K)),
    0 < n → 0 < ε → Continuous (Function.uncurry c) → IsCompact 𝒩 →
    (∀ ν ∈ 𝒩, (ν : Measure K) Set.univ ≠ 0 ∧ (ν : Measure K) Set.univ ≤ 1) →
      ((∃ Q, StatFormal.Wave4b.InBall x c ε r (((↑) : FiniteMeasure K → Measure K) '' 𝒩) Q) ↔
        floorN x c ε (((↑) : FiniteMeasure K → Measure K) '' 𝒩) ≤ (r : EReal))

/-! ### `prop:cs-compose` -/

/-- `OT_ε(μ,Q) ≤ (√OT_ε(μ,P) + W₂(P,Q))²` for `μ = Σ_i a_i δ_{x_i}` on a compact metric `K`, `c = dist²`. -/
def cs_compose : Prop :=
  ∀ (K : Type) [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (k : ℕ) (ε : ℝ)
    (a : Fin k → ℝ) (x : Fin k → K) (P Q : Measure K) [IsProbabilityMeasure P] [IsProbabilityMeasure Q],
    0 < ε → (∀ i, 0 < a i) → ∑ i, a i = 1 →
      0 ≤ OTdisc ε a (fun i y => dist (x i) y ^ 2) P ∧ OTdisc ε a (fun i y => dist (x i) y ^ 2) P ≠ ⊤ ∧
      wassersteinEDist 2 P Q ≠ ⊤ ∧
      OTdisc ε a (fun i y => dist (x i) y ^ 2) Q ≤
        (((√((OTdisc ε a (fun i y => dist (x i) y ^ 2) P).toReal) + (wassersteinEDist 2 P Q).toReal) ^ 2 : ℝ) :
          EReal)

/-- The consequence at the free end: `OT_ε(μ,P) ≤ ρ` and `W₂²(P,Q) ≤ β` give `Q ∈ 𝓑^{𝒫(K)}(μ; (√ρ + √β)²)`. -/
def cs_compose_ball : Prop :=
  ∀ (K : Type) [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (k : ℕ) (ε : ℝ)
    (a : Fin k → ℝ) (x : Fin k → K) (P Q : Measure K) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (ρ β : ℝ),
    0 < ε → (∀ i, 0 < a i) → ∑ i, a i = 1 → 0 ≤ ρ → 0 ≤ β →
    OTdisc ε a (fun i y => dist (x i) y ^ 2) P ≤ (ρ : EReal) →
    wassersteinEDist 2 P Q ^ 2 ≤ ENNReal.ofReal β →
      Q ∈ ballN freeClass ε a (fun i y => dist (x i) y ^ 2) (((√ρ + √β) ^ 2 : ℝ) : EReal)

/-! ### `prop:ep-gauss` -/

/-- `x − log x = 1 + 2β/ε` has exactly one root `x* > 1`. -/
def gauss_xstar : Prop :=
  ∀ β ε : ℝ, 0 < β → 0 < ε → ∃! x : ℝ, 1 < x ∧ x - Real.log x = 1 + 2 * β / ε

/-- `inf_{λ > |w|²} T_ε(λ; R_ε + β) = |w|²(β + ε/2 (1 + log x*)) = |w|² ε x*/2`, attained when `w ≠ 0`. -/
def gauss_inf : Prop :=
  ∀ (d : ℕ) (w : EuclideanSpace ℝ (Fin d)) (β ε xs : ℝ),
    0 < β → 0 < ε → 1 < xs → xs - Real.log xs = 1 + 2 * β / ε →
      IsGLB (Tgauss (‖w‖ ^ 2) β ε '' Set.Ioi (‖w‖ ^ 2)) (‖w‖ ^ 2 * (β + ε / 2 * (1 + Real.log xs))) ∧
      ‖w‖ ^ 2 * (β + ε / 2 * (1 + Real.log xs)) = ‖w‖ ^ 2 * ε * xs / 2 ∧
      (w ≠ 0 → IsLeast (Tgauss (‖w‖ ^ 2) β ε '' Set.Ioi (‖w‖ ^ 2))
        (‖w‖ ^ 2 * (β + ε / 2 * (1 + Real.log xs))))

/-- `|w|²(β + ε/2) ≤ inf T_ε ≤ |w|²(β + ε/2 (1 + log(2 + 4β/ε)))`. -/
def gauss_bounds : Prop :=
  ∀ (d : ℕ) (w : EuclideanSpace ℝ (Fin d)) (β ε xs : ℝ),
    0 < β → 0 < ε → 1 < xs → xs - Real.log xs = 1 + 2 * β / ε →
      ‖w‖ ^ 2 * (β + ε / 2) ≤ ‖w‖ ^ 2 * (β + ε / 2 * (1 + Real.log xs)) ∧
      ‖w‖ ^ 2 * (β + ε / 2 * (1 + Real.log xs)) ≤
        ‖w‖ ^ 2 * (β + ε / 2 * (1 + Real.log (2 + 4 * β / ε)))

/-- The root-unit excess `√(inf T_ε) − |w|√β` lies in
`[|w|ε/(4√(β+ε)), |w| min{√(ε(1+L)/2), ε(1+L)/(4√β)}]`, `L = log(2 + 4β/ε)`. -/
def gauss_root : Prop :=
  ∀ (d : ℕ) (w : EuclideanSpace ℝ (Fin d)) (β ε xs : ℝ),
    0 < β → 0 < ε → 1 < xs → xs - Real.log xs = 1 + 2 * β / ε →
      ‖w‖ * ε / (4 * √(β + ε)) ≤ √(‖w‖ ^ 2 * (β + ε / 2 * (1 + Real.log xs))) - ‖w‖ * √β ∧
      √(‖w‖ ^ 2 * (β + ε / 2 * (1 + Real.log xs))) - ‖w‖ * √β ≤
        ‖w‖ * min (√(ε * (1 + Real.log (2 + 4 * β / ε)) / 2))
          (ε * (1 + Real.log (2 + 4 * β / ε)) / (4 * √β))

end Claims
end StatFormal.Wave11a
