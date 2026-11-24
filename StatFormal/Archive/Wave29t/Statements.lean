import StatFormal.Archive.Wave29q.Statements
import StatFormal.Archive.Wave29g.Statements

/-!
# FROZEN STATEMENTS — wave 29t: SB `lem:equiv` in general (static existence and uniqueness for arbitrary `μ`, `ν`; the
# dynamic problem has the same value; `mixture_bridge` made unconditional); `prop:mixture` on path space in `ℝ^d`

Sources (`data-fairness-repair/schrodinger_bridge_fairness_repair.tex`, current text read 2026-10-20):
* `sec:schrodinger` (`:374-393`): `Ω = C([0,1]; ℝ^d)`, `𝕎^ε_μ` the law of `dX_t = √ε dB_t`, `X₀ ∼ μ`; `eq:dynamic`
  (`P*_ε(μ,ν) = argmin {KL(P ‖ 𝕎^ε_μ) : P₀ = μ, P₁ = ν}`); `eq:static` (`C_ε`, "with minimiser `π*_ε(μ,ν)`, unique when
  finite by strict convexity"); `ass:ac` (`:396-400`).
* `lem:equiv` (`:415-425`, proof `:2721-2738`: "Existence and uniqueness follow from lower semicontinuity and strict
  convexity of `−Ent`"; `R₀₁(dx,dy) = μ(dx) p_ε(y − x) dy`, `p_ε` the `N(0, εI_d)` density; `eq:calib` with
  `(εd/2) log(2πε)`).
* `prop:mixture` (`:458-473`, proof `:2740-2746`): `eq:mixture` with `Z ∼ N(0, I_d)`, `eq:convolution`, in `ℝ^d`.
Imports the frozen wave 29q statements (`IsBrownianRef`, `IsPathCoupling`, `IsSchrodingerBridge`, `refPlan`,
`IsStaticBridge`, `bridgeLaw`; through them Wave P3b `sqCost`, `IsEntPlan`, Wave 4b `endpointMixture1`, Wave 9b
`stoPlan`) and the frozen wave 29g statements (`sqCostD`, `IsEntPlanD`), not copied; Tau Ceti (`IsCoupling`,
`schroedingerValue`, `entropicTransportCost`) and Mathlib (`klDiv`, `multivariateGaussian`, `stdGaussian`,
`Measure.conv`) otherwise. Libraries: `Foundations/SchrodingerPath/Exists.lean` (new file), `Foundations/SchrodingerPathD`
(new: `Gauss`, `Static`); the frozen wave 29q library `Foundations/SchrodingerPath` is reused unchanged.

Covered:
* `lem:equiv`, `d = 1`, GENERAL marginals (the gap declared by wave 29q):
  `equiv_static` (for every `ε > 0`, every probability `μ` and every `ν`: a static minimiser of `KL(· ‖ R₀₁)` over
  `Π(μ,ν)` exists iff the static value `inf_{Π(μ,ν)} KL(· ‖ R₀₁)` is finite, and it is unique);
  `equiv_bridge` (relative to every `ε`-Brownian reference: the dynamic value `inf {KL(P ‖ R) : P₀ = μ, P₁ = ν}` EQUALS
  the static value, a Schrödinger bridge exists iff it is finite, it is unique, and `KL(P* ‖ R)` is that value);
  `equiv_static_ac` (under `ass:ac` for the target and `𝒫₂`: the static value and the entropic cost are finite, and
  `π*_ε` exists and is unique, both as the static minimiser and as the Wave P3b `IsEntPlan`).
* `prop:mixture` + `lem:equiv`, `d = 1`, UNCONDITIONAL: `mixture_bridge_uncond` (the frozen `mixture_bridge` was
  conditional on a bridge existing; under `ass:ac` for `ν` and `𝒫₂` the bridge exists and is unique, its endpoint law
  is `IsEntPlan`, `dP*/dR = g(X₀,X₁)`, `eq:calib` holds in Tau Ceti's normalisation, and all time-`t` conclusions of
  `mixture_bridge` hold).
* `ℝ^d` (every `d : ℕ`, in particular `d ≥ 2`), path space: `mixtureD_bridge` (the `ℝ^d` `mixture_bridge`:
  `h`-transform form, static minimality with equal value, three-time law `bridgeLawD`, `eq:mixture` with
  `Z ∼ N(0, I_d)` and `eq:convolution` with `N(0, εt(1−t) I_d)`), `mixtureD_exists` (transfer static → dynamic,
  uniqueness given the endpoint law), `equiv_static_d`, `equiv_bridge_d` (the `ℝ^d` `equiv_static`/`equiv_bridge`).
* `ℝ^d`, static half and unconditional form: `equiv_static_calib_d` (`eq:calib` at the level of plans with
  `(d/2) log(2πε)`), `equiv_static_ac_d` (static minimisers = Wave 29g `IsEntPlanD`; existence and uniqueness of
  both; finiteness), `mixtureD_uncond` (the `ℝ^d` `mixture_bridge_uncond`).

Not covered (declared):
* `eq:calib` and `eq:static` in the paper's differential-entropy normalisation (`C_ε = ½∫|x−y|² dπ − ε Ent(π)`,
  `Ent(μ)`): Mathlib has no differential entropy. The claims use Tau Ceti's `entropicTransportCost`
  `C^TC_ε = inf_π ∫ ½|x−y|² dπ + ε KL(π ‖ μ ⊗ ν)`; back-translation: when `μ` and `ν` have finite differential entropy,
  `KL(π ‖ μ ⊗ ν) = −Ent(π) + Ent(μ) + Ent(ν)`, so `C^TC_ε = C_ε + ε Ent(μ) + ε Ent(ν)` and, with `Ent(ν) = −∫ log q dν`,
  the claimed `ε KL(P* ‖ R) = C^TC_ε + ε(∫ log q dν + (d/2) log(2πε))` is exactly `eq:calib`
  `= C_ε + ε Ent(μ) + (εd/2) log(2πε)` (informal step: the entropy identity).
* Hypothesis of `lem:equiv` "`C_ε(μ,ν) < ∞`": encoded as finiteness of the static value
  `schroedingerValue (refPlan ε μ) μ ν` (`equiv_static`, `equiv_bridge`), and as `ass:ac` for `ν` + `𝒫₂` (no condition
  on `μ`) in the `*_ac`/`*_uncond` claims, under which it is PROVED finite. The encoding is a GENERALISATION (informal
  step): for `μ, ν ∈ 𝒫₂`, `C_ε < ∞` forces a coupling with `Ent(π) > −∞`, hence (subadditivity, Gaussian bound) `μ`, `ν`
  absolutely continuous with finite entropy, and then the identity of the proof of `lem:equiv` gives
  `KL(π ‖ R₀₁) < ∞`; so the paper's hypothesis implies the Lean one. The converse fails: for atomic `μ` and `ν = N(0,1)`,
  `C_ε = ∞` (differential entropy) while the static value is finite and `P*_ε` exists (`equiv_bridge`). The static
  value is `∞` exactly when no coupling is `≪ R₀₁` with integrable log-likelihood ratio (Mathlib `klDiv = ∞`, the
  genuine value of `KL` for probability measures; no junk), e.g. atomic `ν`.
* Existence of Wiener measure on `C([0,1]; ℝ^d)` (as in wave 29q): the claims quantify over every `(Ω, X, R)` with the
  three-time laws of `X₀ + √ε B`. Non-vacuity is a ROUTE lemma, not a target: `RouteMixtureD.isBrownianRefD_witness`
  (one process `X_t(x,z₁,z₂) = x + t z₁ + √(t(1−t)) z₂` on `(ℝ^d)³` under `μ ⊗ N(0,εI) ⊗ N(0,εI)`, every `ε ≥ 0`, every
  probability `μ`), `RouteStaticD.acHyps_isoG` / `RouteEquiv.acHyps_gauss` (`ν = N(0, I_d)` / `N(0,1)` satisfies the
  `ass:ac` and `𝒫₂` premises), `RouteStaticD.bridgeD_exists_witness` / `RouteEquiv.bridge_exists_witness` (on those
  witnesses a Schrödinger bridge exists at every `ε > 0`), so every premise of every claim is satisfiable.
* `ℝ^d` Gaussian case (`mixture_gauss` with general covariances: endpoint law = the Wave 29g Gaussian plan) and `ℝ^d`
  versions of the wave 29q path discharges: not attempted (they need the Lebesgue density of `N(m, B)` for general
  `B ≻ 0`; only the isotropic `N(0, εI)` density is proved here).

Encodings (to be checked by the critic):
* `d = 1` objects: the frozen wave 29q encodings, unchanged. `ℝ^d = EuclideanSpace ℝ (Fin d)`; `N(0, s I_d) = isoGauss d s
  = multivariateGaussian 0 (s₊ • 1)` (every use has `s ≥ 0`: `ε > 0`, `t ∈ [0,1]`; no `toNNReal` junk);
  `IsBrownianRefD`, `IsPathCouplingD`, `IsSchrodingerBridgeD`, `refPlanD`, `IsStaticBridgeD`, `bridgeLawD` are the wave
  29q definitions with `ℝ` replaced by `ℝ^d`, `*` by `•`, `gaussianReal 0 s` by `isoGauss d s` (wave 29q's are
  `ℝ`-specific and cannot be reused).
* `eq:mixture`: `Z ∼ stdGaussian (ℝ^d)` (Mathlib; `= multivariateGaussian 0 1` by `multivariateGaussian_zero_one`), law of
  `(1−t)X₀ + tX₁ + √(εt(1−t)) Z` as `(π ⊗ N(0,I)).map …`; `eq:convolution`: Mathlib `Measure.conv` (`∗`) of the
  entropic displacement interpolant `ρ^ε_t = π.map ((1−t)x + ty)` with `N(0, εt(1−t) I_d)`.
* "`π*_ε` exists and is unique": `∃!` over measures; for general `ν` as "exists iff value finite" plus "any two
  coincide" (the value can be `∞`, e.g. atomic `ν`, when no coupling has finite entropy).
* The dynamic value `⨅ Q (_ : IsPathCoupling X μ ν Q), KL(Q ‖ R)` is an infimum in `[0,∞]` (no junk; `∞` on an empty
  constraint set).
* `ass:ac` for `ν` and `𝒫₂`: as in the frozen `mixture_static` (`ν = Leb.withDensity q`, `q ≥ 0` measurable,
  `log q ∈ L¹(ν)`, `|x|² ∈ L¹(μ)`, `|y|² ∈ L¹(ν)`; in `ℝ^d` with `‖·‖²`); `ass:ac` for `μ` not needed.
* `eq:calib` with `toReal`: `KL(P* ‖ R) ≠ ∞` is part of `IsSchrodingerBridge(D)`; `entropicTransportCost ≠ ∞` is a stated
  conjunct; `log q = 0` on `{q = 0}` is junk only on a `ν`-null set.

Proof notes: existence is Tau Ceti `exists_isCoupling_klDiv_eq_schroedingerValue` (Csiszár: densities of a minimising
sequence are Cauchy in `L¹(R₀₁)` by quantitative strict convexity, the limit is a coupling, Fatou), NOT lower
semicontinuity + Prokhorov; uniqueness is `IsCoupling.eq_of_klDiv_eq_schroedingerValue` (strict convexity of `KL`).
`ℝ^d` Brownian-bridge decomposition: characteristic functionals on `ℝ^d × ℝ^d` (`charFunDual_prod`, `charFunDual_map`,
dual norms through the Riesz isometry). `ℝ^d` Gaussian density: `N(0,εI) = (⊗ᵢ N(0,ε)).map toLp` (characteristic
functions), product density by `integral_fintype_prod_eq_prod`. The `h`-transform library is dimension-free.

Critic notes (wave 29t, 2026-10-20):
* `mixture_bridge_uncond`/`mixtureD_uncond` strengthened to also carry `R ∘ (X₀,X₁)⁻¹ = R₀₁`, `IsStaticBridge(D)` of the
  endpoint law and `KL(P ‖ R) = KL(π ‖ R₀₁)`, so that under their hypotheses they imply every conclusion of the frozen
  `mixture_bridge` (resp. `mixtureD_bridge`) for the bridge they prove to exist (new ⇒ old literally).
* Existence (Tau Ceti, Csiszár 1975 Thm 2.1) is unconditional on topology: an `L¹(R₀₁)`-Cauchy minimising sequence of
  densities, limit a coupling, Fatou; the finiteness hypothesis is used (the excess bound needs a finite value), not
  absorbed by a `⊤` convention. The `⇒` half of each "exists iff finite" is immediate from `IsStaticBridge`'s
  finiteness conjunct; the content is `⇐` and uniqueness.
* `d = 1` claims are on the frozen wave 29q objects (they extend the frozen chain); the `ℝᵈ` claims are on new
  `ℝᵈ` objects (at `d = 1` they are the `d = 1` claims transported along `ℝ ≃ EuclideanSpace ℝ (Fin 1)`; for `d ≥ 2`
  new). Not restatements of each other in Lean (different types), deliberate duplication at `d = 1`.

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TauCeti InformationTheory
open scoped ENNReal NNReal

namespace StatFormal.Wave29t

open StatFormal.WaveP3b (sqCost IsEntPlan)
open StatFormal.Wave29q (IsBrownianRef IsPathCoupling IsSchrodingerBridge refPlan IsStaticBridge bridgeLaw)


/-! ### `ℝᵈ` objects (`prop:mixture`, `lem:equiv` on `C([0,1]; ℝᵈ)`) -/

local notation "E" d => EuclideanSpace ℝ (Fin d)

/-- `N(0, s I_d)` (Mathlib `multivariateGaussian`, covariance `s₊ I_d`, `s₊ = max s 0`). -/
def isoGauss (d : ℕ) (s : ℝ) : Measure (E d) :=
  multivariateGaussian 0 ((s.toNNReal : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ))

section DefsD

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- `R` is an `ε`-Brownian reference on `ℝᵈ` started from `μ` (`𝕎^ε_μ`), through its three-time laws: each `X t`,
`t ∈ [0,1]`, is measurable and `(X₀, X_t − X₀, X₁ − X_t) ∼ μ ⊗ N(0, εt I_d) ⊗ N(0, ε(1−t) I_d)` under `R`. -/
def IsBrownianRefD (ε : ℝ) (μ : Measure (E d)) (X : ℝ → Ω → E d) (R : Measure Ω) : Prop :=
  (∀ t ∈ Icc (0 : ℝ) 1, Measurable (X t)) ∧
    ∀ t ∈ Icc (0 : ℝ) 1, R.map (fun ω => (X 0 ω, X t ω - X 0 ω, X 1 ω - X t ω)) =
      μ.prod ((isoGauss d (ε * t)).prod (isoGauss d (ε * (1 - t))))

/-- The constraint set of `eq:dynamic` in `ℝᵈ`. -/
def IsPathCouplingD (X : ℝ → Ω → E d) (μ ν : Measure (E d)) (P : Measure Ω) : Prop :=
  IsProbabilityMeasure P ∧ P.map (X 0) = μ ∧ P.map (X 1) = ν

/-- `P = P*_ε(μ, ν)` (`eq:dynamic`) in `ℝᵈ`: a minimiser of `KL(· ‖ R)` over the constraint set, with finite minimum. -/
def IsSchrodingerBridgeD (X : ℝ → Ω → E d) (R : Measure Ω) (μ ν : Measure (E d)) (P : Measure Ω) : Prop :=
  IsPathCouplingD X μ ν P ∧ klDiv P R ≠ ∞ ∧ ∀ Q : Measure Ω, IsPathCouplingD X μ ν Q → klDiv P R ≤ klDiv Q R

end DefsD

variable {d : ℕ}

/-- `R₀₁(dx, dy) = μ(dx) N(x, ε I_d)(dy)`: the law of `(x, x + √ε G)`. -/
def refPlanD (ε : ℝ) (μ : Measure (E d)) : Measure ((E d) × (E d)) :=
  (μ.prod (isoGauss d ε)).map (fun p => (p.1, p.1 + p.2))

/-- The static Schrödinger problem in `ℝᵈ`: `π ∈ Π(μ, ν)` minimises `KL(· ‖ R₀₁)` over `Π(μ, ν)`, with finite minimum. -/
def IsStaticBridgeD (ε : ℝ) (μ ν : Measure (E d)) (π : Measure ((E d) × (E d))) : Prop :=
  IsCoupling π μ ν ∧ klDiv π (refPlanD ε μ) ≠ ∞ ∧
    ∀ π' : Measure ((E d) × (E d)), IsCoupling π' μ ν → klDiv π (refPlanD ε μ) ≤ klDiv π' (refPlanD ε μ)

/-- `π` mixed with the `ε`-Brownian bridge at time `t`: the law of `((X₀, X₁), (1−t)X₀ + tX₁ + Z)`,
`(X₀, X₁) ∼ π`, `Z ∼ N(0, εt(1−t) I_d)` independent. -/
def bridgeLawD (ε t : ℝ) (π : Measure ((E d) × (E d))) : Measure (((E d) × (E d)) × (E d)) :=
  (π.prod (isoGauss d (ε * t * (1 - t)))).map (fun q => (q.1, (1 - t) • q.1.1 + t • q.1.2 + q.2))

namespace Claims

open StatFormal.Wave4b (endpointMixture1)
open StatFormal.Wave9b (stoPlan)

/-! ### SB `lem:equiv`, `d = 1`, general marginals -/

/-- `lem:equiv`, static problem, ARBITRARY `ν`: a minimiser of `KL(· ‖ R₀₁)` over `Π(μ, ν)` with finite value exists iff
the static value `inf_{π ∈ Π(μ,ν)} KL(π ‖ R₀₁)` is finite, and there is at most one. -/
def equiv_static : Prop :=
  ∀ (ε : ℝ) (μ ν : Measure ℝ), 0 < ε → IsProbabilityMeasure μ →
    ((∃ π : Measure (ℝ × ℝ), IsStaticBridge ε μ ν π) ↔ schroedingerValue (refPlan ε μ) μ ν ≠ ∞) ∧
    ∀ π π' : Measure (ℝ × ℝ), IsStaticBridge ε μ ν π → IsStaticBridge ε μ ν π' → π = π'

/-- `lem:equiv`, dynamic problem, ARBITRARY `ν`: relative to an `ε`-Brownian reference the dynamic value
`inf {KL(P ‖ R) : P₀ = μ, P₁ = ν}` equals the static value; a Schrödinger bridge exists iff this value is finite;
there is at most one; and its relative entropy is the common value. -/
def equiv_bridge : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (ε : ℝ) (μ ν : Measure ℝ) (X : ℝ → Ω → ℝ) (R : Measure Ω),
    0 < ε → IsProbabilityMeasure μ → IsBrownianRef ε μ X R →
      (⨅ (Q : Measure Ω) (_ : IsPathCoupling X μ ν Q), klDiv Q R) = schroedingerValue (refPlan ε μ) μ ν ∧
      ((∃ P : Measure Ω, IsSchrodingerBridge X R μ ν P) ↔ schroedingerValue (refPlan ε μ) μ ν ≠ ∞) ∧
      (∀ P P' : Measure Ω, IsSchrodingerBridge X R μ ν P → IsSchrodingerBridge X R μ ν P' → P = P') ∧
      ∀ P : Measure Ω, IsSchrodingerBridge X R μ ν P → klDiv P R = schroedingerValue (refPlan ε μ) μ ν

/-- `lem:equiv` under `ass:ac` for the target and `𝒫₂`: for `ν` with a Lebesgue density `q` of finite entropy and
`μ, ν ∈ 𝒫₂`, the static value and the entropic cost are finite, the static minimiser `π*_ε` exists and is unique, and
the entropic optimal plan (frozen Wave P3b `IsEntPlan`) exists and is unique. -/
def equiv_static_ac : Prop :=
  ∀ (ε : ℝ) (μ ν : Measure ℝ) (q : ℝ → ℝ), 0 < ε → IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    Measurable q → (∀ y, 0 ≤ q y) → ν = volume.withDensity (fun y => ENNReal.ofReal (q y)) →
    Integrable (fun y => Real.log (q y)) ν → Integrable (fun x : ℝ => x ^ 2) μ → Integrable (fun y : ℝ => y ^ 2) ν →
      schroedingerValue (refPlan ε μ) μ ν ≠ ∞ ∧ entropicTransportCost sqCost ε.toNNReal μ ν ≠ ∞ ∧
      (∃! π : Measure (ℝ × ℝ), IsStaticBridge ε μ ν π) ∧ ∃! π : Measure (ℝ × ℝ), IsEntPlan ε μ ν π

/-- `prop:mixture` with `lem:equiv`, UNCONDITIONAL (`ε > 0`, `ν` with a Lebesgue density of finite entropy,
`μ, ν ∈ 𝒫₂`, every `ε`-Brownian reference `R`): `R ∘ (X₀,X₁)⁻¹ = R₀₁`; the Schrödinger bridge `P*_ε` exists and is
unique; its endpoint law is the static minimiser, with `KL(P* ‖ R) = KL(π* ‖ R₀₁)`, and the entropic optimal plan;
`dP*/dR = g(X₀, X₁)`; `eq:calib` in Tau Ceti's normalisation
`ε KL(P* ‖ R) = C_ε(μ,ν) + ε(∫ log q dν + ½ log(2πε))`, `C_ε = inf_π ∫ ½(x−y)² dπ + ε KL(π ‖ μ ⊗ ν)`; and for every
`t ∈ [0,1]` the conclusions of `prop:mixture` (`eq:mixture`, `eq:convolution`) hold. Under its hypotheses it implies
every conclusion of the frozen `mixture_bridge`, for the bridge it proves to exist. -/
def mixture_bridge_uncond : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (ε : ℝ) (μ ν : Measure ℝ) (q : ℝ → ℝ) (X : ℝ → Ω → ℝ) (R : Measure Ω),
    0 < ε → IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    Measurable q → (∀ y, 0 ≤ q y) → ν = volume.withDensity (fun y => ENNReal.ofReal (q y)) →
    Integrable (fun y => Real.log (q y)) ν → Integrable (fun x : ℝ => x ^ 2) μ → Integrable (fun y : ℝ => y ^ 2) ν →
    IsBrownianRef ε μ X R →
      R.map (fun ω => (X 0 ω, X 1 ω)) = refPlan ε μ ∧
      (∃! P : Measure Ω, IsSchrodingerBridge X R μ ν P) ∧
      ∀ P : Measure Ω, IsSchrodingerBridge X R μ ν P →
        IsStaticBridge ε μ ν (P.map (fun ω => (X 0 ω, X 1 ω))) ∧
        klDiv P R = klDiv (P.map (fun ω => (X 0 ω, X 1 ω))) (refPlan ε μ) ∧
        IsEntPlan ε μ ν (P.map (fun ω => (X 0 ω, X 1 ω))) ∧
        (∃ g : ℝ × ℝ → ℝ≥0∞, Measurable g ∧ P.map (fun ω => (X 0 ω, X 1 ω)) = (refPlan ε μ).withDensity g ∧
          P = R.withDensity (fun ω => g (X 0 ω, X 1 ω))) ∧
        entropicTransportCost sqCost ε.toNNReal μ ν ≠ ∞ ∧
        ε * (klDiv P R).toReal = (entropicTransportCost sqCost ε.toNNReal μ ν).toReal +
          ε * (∫ y, Real.log (q y) ∂ν + Real.log (2 * Real.pi * ε) / 2) ∧
        ∀ t ∈ Icc (0 : ℝ) 1,
          P.map (fun ω => ((X 0 ω, X 1 ω), X t ω)) = bridgeLaw ε t (P.map (fun ω => (X 0 ω, X 1 ω))) ∧
          P.map (X t) = endpointMixture1 ε t (P.map (fun ω => (X 0 ω, X 1 ω))) ∧
          P.map (fun ω => (X 0 ω, X t ω)) = stoPlan ε t (P.map (fun ω => (X 0 ω, X 1 ω)))

/-! ### SB `prop:mixture` and `lem:equiv` in `ℝᵈ` (every `d`) -/

/-- `prop:mixture` with the path-space half of `lem:equiv` in `ℝᵈ`: a Schrödinger bridge relative to an `ε`-Brownian
reference has `dP/dR = g(X₀, X₁)`, its endpoint law is the static minimiser with the same value, and for every
`t ∈ [0,1]` the law of `((X₀,X₁), X_t)` is `bridgeLawD ε t π*`, so `μ^ε_t = Law((1−t)X₀ + tX₁ + √(εt(1−t)) Z)`,
`Z ∼ N(0, I_d)` (`eq:mixture`) `= ρ^ε_t ∗ N(0, εt(1−t) I_d)` (`eq:convolution`). -/
def mixtureD_bridge : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (d : ℕ) (ε : ℝ) (μ ν : Measure (E d)) (X : ℝ → Ω → E d) (R P : Measure Ω),
    0 < ε → IsProbabilityMeasure μ → IsBrownianRefD ε μ X R → IsSchrodingerBridgeD X R μ ν P →
      R.map (fun ω => (X 0 ω, X 1 ω)) = refPlanD ε μ ∧
      IsStaticBridgeD ε μ ν (P.map (fun ω => (X 0 ω, X 1 ω))) ∧
      klDiv P R = klDiv (P.map (fun ω => (X 0 ω, X 1 ω))) (refPlanD ε μ) ∧
      (∃ g : (E d) × (E d) → ℝ≥0∞, Measurable g ∧ P.map (fun ω => (X 0 ω, X 1 ω)) = (refPlanD ε μ).withDensity g ∧
        P = R.withDensity (fun ω => g (X 0 ω, X 1 ω))) ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        P.map (fun ω => ((X 0 ω, X 1 ω), X t ω)) = bridgeLawD ε t (P.map (fun ω => (X 0 ω, X 1 ω))) ∧
        P.map (X t) = ((P.map (fun ω => (X 0 ω, X 1 ω))).prod (stdGaussian (E d))).map
          (fun q => (1 - t) • q.1.1 + t • q.1.2 + √(ε * t * (1 - t)) • q.2) ∧
        P.map (X t) = ((P.map (fun ω => (X 0 ω, X 1 ω))).map (fun z => (1 - t) • z.1 + t • z.2)) ∗
          isoGauss d (ε * t * (1 - t))

/-- `lem:equiv` in `ℝᵈ`, transfer: every static minimiser is the endpoint law of a Schrödinger bridge, and two
Schrödinger bridges with the same endpoint law coincide. -/
def mixtureD_exists : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (d : ℕ) (ε : ℝ) (μ ν : Measure (E d)) (X : ℝ → Ω → E d) (R : Measure Ω),
    0 < ε → IsProbabilityMeasure μ → IsBrownianRefD ε μ X R →
      (∀ π : Measure ((E d) × (E d)), IsStaticBridgeD ε μ ν π →
        ∃ P : Measure Ω, IsSchrodingerBridgeD X R μ ν P ∧ P.map (fun ω => (X 0 ω, X 1 ω)) = π) ∧
      ∀ P P' : Measure Ω, IsSchrodingerBridgeD X R μ ν P → IsSchrodingerBridgeD X R μ ν P' →
        P.map (fun ω => (X 0 ω, X 1 ω)) = P'.map (fun ω => (X 0 ω, X 1 ω)) → P = P'

/-- `lem:equiv` in `ℝᵈ`, static problem, ARBITRARY `ν`: a static minimiser exists iff the static value is finite, and
there is at most one. -/
def equiv_static_d : Prop :=
  ∀ (d : ℕ) (ε : ℝ) (μ ν : Measure (E d)), 0 < ε → IsProbabilityMeasure μ →
    ((∃ π : Measure ((E d) × (E d)), IsStaticBridgeD ε μ ν π) ↔ schroedingerValue (refPlanD ε μ) μ ν ≠ ∞) ∧
    ∀ π π' : Measure ((E d) × (E d)), IsStaticBridgeD ε μ ν π → IsStaticBridgeD ε μ ν π' → π = π'

/-- `lem:equiv` in `ℝᵈ`, dynamic problem, ARBITRARY `ν`: the dynamic value equals the static value; a Schrödinger
bridge exists iff it is finite; there is at most one; its relative entropy is the common value. -/
def equiv_bridge_d : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (d : ℕ) (ε : ℝ) (μ ν : Measure (E d)) (X : ℝ → Ω → E d) (R : Measure Ω),
    0 < ε → IsProbabilityMeasure μ → IsBrownianRefD ε μ X R →
      (⨅ (Q : Measure Ω) (_ : IsPathCouplingD X μ ν Q), klDiv Q R) = schroedingerValue (refPlanD ε μ) μ ν ∧
      ((∃ P : Measure Ω, IsSchrodingerBridgeD X R μ ν P) ↔ schroedingerValue (refPlanD ε μ) μ ν ≠ ∞) ∧
      (∀ P P' : Measure Ω, IsSchrodingerBridgeD X R μ ν P → IsSchrodingerBridgeD X R μ ν P' → P = P') ∧
      ∀ P : Measure Ω, IsSchrodingerBridgeD X R μ ν P → klDiv P R = schroedingerValue (refPlanD ε μ) μ ν

/-- `lem:equiv` in `ℝᵈ`, static half (`eq:calib` at the level of plans): for `ν` with a Lebesgue density `q` of finite
entropy and `μ, ν ∈ 𝒫₂(ℝᵈ)`, a coupling has `KL(π ‖ R₀₁) < ∞ ⟺ KL(π ‖ μ ⊗ ν) < ∞`, and then
`ε KL(π ‖ R₀₁) = ∫ ½‖x−y‖² dπ + ε KL(π ‖ μ ⊗ ν) + ε(∫ log q dν + (d/2) log(2πε))`. -/
def equiv_static_calib_d : Prop :=
  ∀ (d : ℕ) (ε : ℝ) (μ ν : Measure (E d)) (q : (E d) → ℝ), 0 < ε → IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    Measurable q → (∀ y, 0 ≤ q y) → ν = volume.withDensity (fun y => ENNReal.ofReal (q y)) →
    Integrable (fun y => Real.log (q y)) ν → Integrable (fun x : E d => ‖x‖ ^ 2) μ →
    Integrable (fun y : E d => ‖y‖ ^ 2) ν →
    ∀ π : Measure ((E d) × (E d)), IsCoupling π μ ν →
      (klDiv π (refPlanD ε μ) ≠ ∞ ↔ klDiv π (μ.prod ν) ≠ ∞) ∧
      (klDiv π (μ.prod ν) ≠ ∞ →
        ε * (klDiv π (refPlanD ε μ)).toReal =
          ∫ z, ‖z.1 - z.2‖ ^ 2 / 2 ∂π + ε * (klDiv π (μ.prod ν)).toReal +
            ε * (∫ y, Real.log (q y) ∂ν + (d : ℝ) * Real.log (2 * Real.pi * ε) / 2))

/-- `lem:equiv` in `ℝᵈ` under `ass:ac` for the target and `𝒫₂`: the static value and the entropic cost are finite, the
static minimisers are exactly the entropic optimal plans of the frozen Wave 29g (`IsEntPlanD`), and both exist and are
unique. -/
def equiv_static_ac_d : Prop :=
  ∀ (d : ℕ) (ε : ℝ) (μ ν : Measure (E d)) (q : (E d) → ℝ), 0 < ε → IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    Measurable q → (∀ y, 0 ≤ q y) → ν = volume.withDensity (fun y => ENNReal.ofReal (q y)) →
    Integrable (fun y => Real.log (q y)) ν → Integrable (fun x : E d => ‖x‖ ^ 2) μ →
    Integrable (fun y : E d => ‖y‖ ^ 2) ν →
      schroedingerValue (refPlanD ε μ) μ ν ≠ ∞ ∧
      entropicTransportCost StatFormal.Wave29g.sqCostD ε.toNNReal μ ν ≠ ∞ ∧
      (∀ π : Measure ((E d) × (E d)), IsStaticBridgeD ε μ ν π ↔ StatFormal.Wave29g.IsEntPlanD ε μ ν π) ∧
      (∃! π : Measure ((E d) × (E d)), IsStaticBridgeD ε μ ν π) ∧
      ∃! π : Measure ((E d) × (E d)), StatFormal.Wave29g.IsEntPlanD ε μ ν π

/-- `prop:mixture` with `lem:equiv` in `ℝᵈ`, UNCONDITIONAL (`ε > 0`, `ν` with a Lebesgue density of finite entropy,
`μ, ν ∈ 𝒫₂(ℝᵈ)`, every `ε`-Brownian reference): `R ∘ (X₀,X₁)⁻¹ = R₀₁`; `P*_ε` exists and is unique; its endpoint law
is the static minimiser, with `KL(P* ‖ R) = KL(π* ‖ R₀₁)`, and the entropic optimal plan; `dP*/dR = g(X₀, X₁)`; `eq:calib` in Tau Ceti's normalisation
`ε KL(P* ‖ R) = C_ε(μ,ν) + ε(∫ log q dν + (d/2) log(2πε))`; and for every `t ∈ [0,1]` the conclusions of
`prop:mixture` (`eq:mixture`, `eq:convolution`) hold. -/
def mixtureD_uncond : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (d : ℕ) (ε : ℝ) (μ ν : Measure (E d)) (q : (E d) → ℝ) (X : ℝ → Ω → E d)
    (R : Measure Ω), 0 < ε → IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    Measurable q → (∀ y, 0 ≤ q y) → ν = volume.withDensity (fun y => ENNReal.ofReal (q y)) →
    Integrable (fun y => Real.log (q y)) ν → Integrable (fun x : E d => ‖x‖ ^ 2) μ →
    Integrable (fun y : E d => ‖y‖ ^ 2) ν → IsBrownianRefD ε μ X R →
      R.map (fun ω => (X 0 ω, X 1 ω)) = refPlanD ε μ ∧
      (∃! P : Measure Ω, IsSchrodingerBridgeD X R μ ν P) ∧
      ∀ P : Measure Ω, IsSchrodingerBridgeD X R μ ν P →
        IsStaticBridgeD ε μ ν (P.map (fun ω => (X 0 ω, X 1 ω))) ∧
        klDiv P R = klDiv (P.map (fun ω => (X 0 ω, X 1 ω))) (refPlanD ε μ) ∧
        StatFormal.Wave29g.IsEntPlanD ε μ ν (P.map (fun ω => (X 0 ω, X 1 ω))) ∧
        (∃ g : (E d) × (E d) → ℝ≥0∞, Measurable g ∧
          P.map (fun ω => (X 0 ω, X 1 ω)) = (refPlanD ε μ).withDensity g ∧
          P = R.withDensity (fun ω => g (X 0 ω, X 1 ω))) ∧
        entropicTransportCost StatFormal.Wave29g.sqCostD ε.toNNReal μ ν ≠ ∞ ∧
        ε * (klDiv P R).toReal = (entropicTransportCost StatFormal.Wave29g.sqCostD ε.toNNReal μ ν).toReal +
          ε * (∫ y, Real.log (q y) ∂ν + (d : ℝ) * Real.log (2 * Real.pi * ε) / 2) ∧
        ∀ t ∈ Icc (0 : ℝ) 1,
          P.map (fun ω => ((X 0 ω, X 1 ω), X t ω)) = bridgeLawD ε t (P.map (fun ω => (X 0 ω, X 1 ω))) ∧
          P.map (X t) = ((P.map (fun ω => (X 0 ω, X 1 ω))).prod (stdGaussian (E d))).map
            (fun q => (1 - t) • q.1.1 + t • q.1.2 + √(ε * t * (1 - t)) • q.2) ∧
          P.map (X t) = ((P.map (fun ω => (X 0 ω, X 1 ω))).map (fun z => (1 - t) • z.1 + t • z.2)) ∗
            isoGauss d (ε * t * (1 - t))

end Claims

end StatFormal.Wave29t
