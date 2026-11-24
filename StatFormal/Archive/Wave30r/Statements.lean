import StatFormal.Archive.Wave8a.Statements

/-!
# FROZEN STATEMENTS — wave 30r: SB `lem:sharp` for the entropic plan on NON-COMPACT supports (journal version) and
# the FAccT form (without `ass:ac`), with the moment hypothesis the FAccT text omits

Sources (current text read 2026-10-20):
* SB journal version `data-fairness-repair-journal/journal/` (branch `reframe/journal`): `main/m_defect.tex:66-81`
  (`lem:sharp`, "Under Assumption `ass:ac`, let `ε>0` and let `π^⋆_ε(R_s,ν)` have barycentric projection
  `T^ε_s(x)=E[X₁|X₀=x]`. Then `(T^ε_s)#R_s=ν` iff `E[Var(X₁|X₀)]=0`, i.e. iff the entropic plan is induced by a map.
  For `ε>0` the plan has a positive density with respect to `R_s⊗ν`, so this fails whenever `ν` is not a Dirac
  measure."), `supp/s_setting.tex:63-89` (`μ,ν ∈ 𝒫₂(ℝ^d)`, `eq:static` `C_ε = min ½∫|x−y|² dπ − ε Ent(π)` "with
  minimiser `π^⋆_ε(μ,ν)`, unique when finite", `ass:ac`: `R₀, R₁, ν` absolutely continuous with finite differential
  entropy), `main/02_setting.tex:7` (`μ_s ∈ 𝒫₂(ℝ^d)`).
* FAccT draft `data-fairness-repair-journal/facct/facct_repair.tex` (byte-identical to
  `data-fairness-repair/facct/facct_repair.tex` at `d0d9392`): `:244-246` (`μ_s` "with continuous marginal
  distribution functions"), `:388-395` (`π^ε_s = argmin_{π∈Π(μ_s,ν)} ∫½‖x−y‖² dπ + ε KL(π‖μ_s⊗ν)`, `T^ε_s(x) =
  E_{π^ε_s}[Z|X=x]`), `:953-957` (`lem:sharp`: "For any `ε>0` and any target `ν` that is not a point mass, the entropic
  map `T^ε_s(x)=E[Z|X=x]` satisfies `(T^ε_s)#μ_s≠ν`."), proof `:959-965` ("The entropic plan has a strictly positive
  density with respect to `μ_s⊗ν`").
Imports the frozen `Wave8a` statements (`IsBaryProj`, `quadCost`, `IsEntropicPlan`), and through them Tau Ceti
(`IsCoupling`, `HasFiniteMoment`, `entropicTransportCost`), not copied. New definitions: `halfQuadCost`,
`IsEntropicPlanHalf` (the FAccT objective, literally).

Covered:
* journal `lem:sharp`: `sharp_P2` (`R, ν ∈ 𝒫₂(ℝ^d)`, NO compactness, NO `ass:ac`: the entropic plan exists and is
  unique, and for every version `T` of its barycentric projection `T_#R = ν` iff `ν` is Dirac), `sharp_P2_density`
  (third sentence: every entropic plan has a density against `R ⊗ ν` that is positive `R ⊗ ν`-a.e.).
* FAccT `lem:sharp`: `sharp_facct` (the FAccT objective `½∫‖x−y‖² + ε KL`, at the SAME `ε`; `μ, ν ∈ 𝒫₂(ℝ^d)`, no
  continuity or absolute continuity: plan exists, is unique, `T_#μ ≠ ν` unless `ν` is a point mass),
  `sharp_facct_moments` (REFUTATION of the FAccT text as printed, which assumes no moments, under the literal
  reading of `argmin` as the set of couplings attaining the infimum even when it is `+∞`: for `μ` with continuous
  marginal CDF and infinite second moment (Pareto(1,1) on `ℝ¹`) and a two-point target `ν ∈ 𝒫₂`, the FAccT objective
  is `+∞` on every coupling, so every coupling is an `argmin`; the graph coupling of a threshold map `S` is one, and
  every version of its conditional-mean map pushes `μ` exactly to `ν`).

Encodings:
* As in `Wave8a`: `ℝ^d = EuclideanSpace ℝ (Fin d)`; `T` is a version of `x ↦ E_π[X₁|X₀ = x]` (`IsBaryProj`); "not a
  Dirac measure" is `¬ ∃ y, ν = dirac y`, stated as the iff; positive density: `π = (R ⊗ ν).withDensity f`, `f`
  measurable, `0 < f` `(R⊗ν)`-a.e.; `𝒫₂` is Tau Ceti `HasFiniteMoment 2`.
* The journal plan (`eq:static`, `½∫|x−y|² − ε Ent`) is `IsEntropicPlan` at `2ε` (Sinkhorn normalisation `∫‖x−y‖² +
  2ε KL(π‖R⊗ν)`), exact under `ass:ac` (`−Ent(π) = KL(π‖R⊗ν) − Ent(R) − Ent(ν)` on couplings), and `ε` ranges over all
  of `(0,∞)` — the encoding certified in Wave 8a. `ass:ac` is therefore NOT a hypothesis of `sharp_P2`: in the
  Sinkhorn normalisation the result holds for all `R, ν ∈ 𝒫₂`, empirical laws included. On `ass:ac` instances this
  is exactly the printed lemma; off them it is a GENERALISATION to the Sinkhorn-normalised plan (the journal's
  `rem:convention`, `supp/s_univariate.tex:126-131`), not a statement about the printed object, since there the
  differential-entropy problem `eq:static` need not be finite and is `+∞` on every coupling as soon as a marginal
  has an atom (`supp/s_setting.tex:91-95`). `ν ∈ 𝒫₂` is implicit in the journal (`eq:static` is posed for
  `μ, ν ∈ 𝒫₂(ℝ^d)`, `s_setting.tex:67`; `ass:main` `:45`). "The" plan: existence and
  uniqueness are part of the claim (`∃!`).
* The FAccT plan is `IsEntropicPlanHalf ε`: a coupling attaining `inf_π ∫ ½‖x−y‖² dπ + ε KL(π‖μ⊗ν)`
  (`entropicTransportCost halfQuadCost ε`), literally. "Continuous marginal distribution functions" is
  `μ.map (· i) {s} = 0` for every coordinate `i` and point `s`.
Critic notes (drafter):
* `lem:sharp` (journal) holds as printed (under `ass:ac` and the standing `𝒫₂`), and its Sinkhorn-normalised
  analogue holds without `ass:ac`, for all `R, ν ∈ 𝒫₂`. Positivity of the density is proved WITHOUT Schrödinger
  potentials, by Csiszár's perturbation argument (mixing `π` with `R ⊗ ν`); the product form `e^{(f⊕g−c)/ε}` cited
  in the journal proof is not proved here for the unbounded cost (not needed). It is nonetheless true for
  `c ∈ L¹(R⊗ν)` (I-projection product form: Csiszár 1975, Rüschendorf–Thomsen 1993; Nutz's EOT notes), so the
  journal's step is uncited, not wrong.
* FAccT `lem:sharp` is FALSE as printed, for a degenerate reason: the FAccT setting never assumes finite second
  moments, and without them the entropic problem is `+∞` on every coupling (`sharp_facct_moments`). With
  `μ_s, ν ∈ 𝒫₂` (to be added) it is TRUE, and dropping `ass:ac` is harmless in the FAccT (KL) normalisation
  (`sharp_facct`).
Critic (2026-10-20): ACCEPT-WITH-NOTE. Encoding and `ε ↔ 2ε` as in Wave 8a (exact under `ass:ac`; `ε : ℝ≥0`,
  `ε ≠ 0` is `ε > 0`). `sharp_facct_moments` refutes the FAccT lemma only under the literal `argmin` reading (every
  coupling minimises an objective that is `+∞` everywhere, so "the" plan is not unique and the graph coupling is
  one); under the convex-analysis convention `argmin f = ∅` when `inf f = +∞` (Rockafellar–Wets, §1.A) the printed
  lemma is vacuous instead. Either way a hypothesis is missing: S3 (as DEFECTS #39 for the journal's `ass:ac`), not
  S1. The FAccT text never states `𝒫₂`, but uses it tacitly throughout (`W₂` at `:353`, `Cov(Z)` at `:961`, `V_ν` at
  `:436`). Manuscript notes: FAccT `:955` add finite second moments; journal `m_defect.tex:79-80`, long paper
  `:929-930` and FAccT `:963` cite or replace the positivity step (S4); journal `THEOREM_MAP.md` stale for
  `lem:sharp` (now Lemma 5.4 in `main/m_defect.tex`).
DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a
`Statements.lean`, is hashed there (with its imports), and AI agents must not edit it.
-/

noncomputable section
open MeasureTheory ProbabilityTheory TauCeti Set InformationTheory
open scoped ENNReal NNReal

namespace StatFormal.Wave30r

open StatFormal.Wave8a

/-- The FAccT cost `½‖x − y‖²` on `ℝ^d × ℝ^d`, in `ℝ≥0∞`. -/
def halfQuadCost {d : ℕ} (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  quadCost z / 2

/-- `π` is the FAccT entropic plan `π^ε = argmin_{π ∈ Π(μ,ν)} ∫ ½‖x − y‖² dπ + ε KL(π ‖ μ ⊗ ν)`: a coupling attaining
the infimum (Tau Ceti `entropicTransportCost`). -/
def IsEntropicPlanHalf {d : ℕ} (ε : ℝ≥0) (μ ν : Measure (EuclideanSpace ℝ (Fin d)))
    (π : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) : Prop :=
  IsCoupling π μ ν ∧
    ∫⁻ z, halfQuadCost z ∂π + ε * klDiv π (μ.prod ν) = entropicTransportCost halfQuadCost ε μ ν

namespace Claims

/-- journal `lem:sharp`, general `𝒫₂` marginals (no compactness, no `ass:ac`): for `ε > 0` the entropic plan
`π^⋆_ε(R,ν)` (Sinkhorn normalisation `∫‖x−y‖² + ε KL(π‖R⊗ν)`, i.e. the journal's plan at `ε/2` under `ass:ac`)
exists and is unique, and for every version `T` of its barycentric projection, `T_#R = ν` iff `ν` is a
Dirac measure. -/
def sharp_P2 : Prop :=
  ∀ (d : ℕ) (R ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure R] [IsProbabilityMeasure ν]
    (ε : ℝ≥0), HasFiniteMoment 2 R → HasFiniteMoment 2 ν → ε ≠ 0 →
      (∃! π, IsEntropicPlan ε R ν π) ∧
        ∀ (π : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)))
          (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
          IsEntropicPlan ε R ν π → IsBaryProj π T → (R.map T = ν ↔ ∃ y, ν = Measure.dirac y)

/-- journal `lem:sharp`, third sentence: "for `ε > 0` the plan has a positive density with respect to `R_s ⊗ ν`",
for general `𝒫₂` marginals. -/
def sharp_P2_density : Prop :=
  ∀ (d : ℕ) (R ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure R] [IsProbabilityMeasure ν]
    (ε : ℝ≥0), HasFiniteMoment 2 R → HasFiniteMoment 2 ν → ε ≠ 0 →
      ∀ π : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)), IsEntropicPlan ε R ν π →
        ∃ f : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞, Measurable f ∧
          (∀ᵐ z ∂(R.prod ν), 0 < f z) ∧ π = (R.prod ν).withDensity f

/-- FAccT `lem:sharp`, with the moment hypothesis added (no continuity, no absolute continuity): for the FAccT
objective `½∫‖x − y‖² + ε KL(π‖μ⊗ν)`, `ε > 0` and `μ, ν ∈ 𝒫₂`, the plan exists and is unique, and every version `T`
of its conditional-mean map satisfies `T_#μ = ν` iff `ν` is a point mass. -/
def sharp_facct : Prop :=
  ∀ (d : ℕ) (μ ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ε : ℝ≥0), HasFiniteMoment 2 μ → HasFiniteMoment 2 ν → ε ≠ 0 →
      (∃! π, IsEntropicPlanHalf ε μ ν π) ∧
        ∀ (π : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)))
          (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
          IsEntropicPlanHalf ε μ ν π → IsBaryProj π T → (μ.map T = ν ↔ ∃ y, ν = Measure.dirac y)

/-- FAccT `lem:sharp` as printed (no moment hypothesis) is FALSE under the literal reading of `argmin` (all
couplings attaining the infimum, even when it is `+∞`; under the convention `argmin ≡ ∅` when `inf = +∞` the printed
lemma is vacuous instead — either way the moment hypothesis is missing): on `ℝ¹` there are a law `μ` with continuous
distribution function and infinite second moment and a target `ν ∈ 𝒫₂` that is not a point mass such that, for every
`ε`, some FAccT entropic plan (an `argmin` of an objective that is `+∞` on every coupling) has a conditional-mean map,
and every version `T` of it satisfies `T_#μ = ν`. -/
def sharp_facct_moments : Prop :=
  ∃ μ ν : Measure (EuclideanSpace ℝ (Fin 1)), IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧
    (∀ (i : Fin 1) (s : ℝ), μ.map (fun x => x i) {s} = 0) ∧ ¬ HasFiniteMoment 2 μ ∧ HasFiniteMoment 2 ν ∧
    (¬ ∃ y, ν = Measure.dirac y) ∧
    ∀ ε : ℝ≥0, ∃ π, IsEntropicPlanHalf ε μ ν π ∧ (∃ T, IsBaryProj π T) ∧
      ∀ T, IsBaryProj π T → μ.map T = ν

end Claims

end StatFormal.Wave30r
