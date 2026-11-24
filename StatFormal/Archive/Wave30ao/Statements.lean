import StatFormal.Archive.Wave29t.Statements
import StatFormal.Archive.Wave30r.Statements

/-!
# FROZEN STATEMENTS — wave 30ao: SB in the printed DIFFERENTIAL-ENTROPY normalisation (`lem:equiv` / `eq:calib`,
# `eq:static`, `def:repair` premise, `prop:mixture` hypothesis, `rem:convention`, the `ass:ac` atom remark)

Sources (both papers carry IDENTICAL texts for every item below; one claim each, second-paper label recorded):
* SB long paper `data-fairness-repair/schrodinger_bridge_fairness_repair.tex` (read 2026-10-21):
  `eq:static` with "Write `Ent(π) = −∫ π log π` for differential entropy … with minimiser `π*_ε(μ,ν)`, unique when
  finite" (`:401-410`); `ass:ac` (`:412-416`) and the paragraph after it (`:418-431`: "`Ent(π) = −∞` for any `π`
  without a Lebesgue density; a coupling one of whose marginals has an atom has none …, so `C_ε(μ,ν) = +∞` as soon as
  one marginal has an atom"); `lem:equiv` with `eq:calib` (`:433-443`); `def:repair` (`:455-465`); `prop:mixture`
  (`:476-491`); proof of `lem:equiv` (`:2610-2633`: the display `KL(π‖R₀₁) = −Ent(π) + Ent(μ) + (d/2) log(2πε)
  + (1/2ε)∫|x−y|² dπ` at `:2619-2623`, "for `μ, ν ∈ 𝒫₂`, `C_ε < ∞` forces `Ent(μ)` finite" at `:2628-2629`);
  `rem:convention` (`:2189-2196`); `lem:sharp` (`:916-923`).
* SB journal `data-fairness-repair-journal/journal/` (branch `reframe/journal`, `2ae7a22`, read 2026-10-21):
  `supp/s_setting.tex` `eq:static` (`:74-82`), `ass:ac` (`:85-89`, paragraph `:91-100`), `lem:equiv` (`:113-123`),
  `def:repair` (`:148-158`), `prop:mixture` (`:171-186`); `supp/s_proofs.tex` proof of `lem:equiv` (`:147-178`, display
  `:165-168`, "forces" `:173-174`); `supp/s_univariate.tex` `rem:convention` (`:125-132`); `main/m_defect.tex` `lem:sharp` (`:66-73`); `main/02_setting.tex`
  `eq:plan` (`:37-45`, `π^ε_s = argmin_{Π(R_s,ν)} ½∫‖x−z‖² dπ − ε Ent(π)`, the journal's literal objective).
Imports the frozen Wave 30r statements (through them Wave 8a `IsBaryProj`) and the frozen Wave 29t statements (`IsBrownianRefD`, `IsSchrodingerBridgeD`, `refPlanD`, `IsStaticBridgeD`,
`bridgeLawD`, `isoGauss`; through them Wave 29g `sqCostD`, `IsEntPlanD`), Tau Ceti (`IsCoupling`,
`schroedingerValue`, `entropicTransportCost`) and Mathlib (`klDiv`, `Measure.rnDeriv`, `stdGaussian`, `EReal`).
New library (imports Mathlib only): `Foundations/DiffEntropy/{Basic,Gauss}` (chain rule `KL(π‖μ⊗ν) = −Ent π + Ent μ + Ent ν`, Gibbs'
inequality, Gaussian maximum-entropy bound `Ent ρ ≤ (d/2) log(2πe tr Cov/d)`, finiteness of marginal entropies).

Covered (the gap of sweep row #39 / audit g1: Wave 29q/29t certified `eq:calib` only at plan level in Tau Ceti's
`KL(π‖μ⊗ν)` normalisation):
* `lem:equiv` IN THE PRINTED NORMALISATION, every clause, with the printed hypothesis `C_ε(μ,ν) < ∞` (`entCost < ⊤`)
  and `ass:main` (`𝒫₂`): `equiv_printed` (the printed minimiser `π*_ε` exists and is unique, `P*_ε` exists and is
  unique, its endpoint law is `π*_ε`, `dP*/dR = g(X₀,X₁)` and the three-time law is the `ε`-Brownian bridge mixture,
  and `eq:calib` `ε KL(P*‖𝕎^ε_μ) = C_ε(μ,ν) + ε Ent(μ) + (εd/2) log(2πε)` with the printed constants).
* the proof display: `equiv_display_printed`; "`C_ε < ∞` forces `Ent(μ)` finite": `cost_finite_iff` (for
  `μ, ν ∈ 𝒫₂`: `C_ε < ∞ ⟺ μ, ν` absolutely continuous with finite differential entropy; and, independent of the
  encoding, any coupling with a Lebesgue density and `Ent(π) > −∞` has `Ent π`, `Ent μ`, `Ent ν` finite).
* `def:repair` premise: `repair_premise` (`C_ε(R_s,ν) < ∞` for `s ∈ {0,1}` ⟺ `ass:ac` for `R₀`, `R₁`, `ν`; it
  implies the ass:ac-for-`ν` encoding of every certified Wave 29t claim, with `∫ log q dν = −Ent(ν)`, finite static
  value and Sinkhorn cost, and existence and uniqueness of both repair bridges).
* `prop:mixture` with its printed hypothesis: `mixture_printed` (`eq:mixture`, `eq:convolution` for `(X₀,X₁) ∼` the
  PRINTED `π*_ε`).
* `rem:convention` (both marginals with finite entropy): `convention_printed` (the two objectives differ by
  `ε(Ent μ + Ent ν)` on every coupling with finite entropy; finite `Ent π ⟺ KL(π‖μ⊗ν) < ∞`; the printed plan IS the
  Wave 29g Sinkhorn plan `IsEntPlanD`, and it exists uniquely).
* `rem:convention` AS PRINTED (absolute continuity only): `convention_counter` (Lean refutation: an absolutely
  continuous `μ ∈ 𝒫₂(ℝ)` with `Ent(μ) = −∞` against `ν = N(0,1)`: no printed plan, `C_ε = +∞`, unique Sinkhorn plan).
* `eq:static` / journal `eq:plan` "with minimiser, unique when finite" and the literal objective OFF `ass:ac`:
  `plan_literal` (`𝒫₂`: if `C_ε < ∞` the printed plan exists and is unique; if `μ` or `ν` lacks finite entropy, the
  literal objective is `+∞` on EVERY coupling, so the printed argmin is all of `Π(μ,ν)`).
* `ass:ac` paragraph: `cost_atom` (`d ≥ 1`, `ε > 0`; an atom in either marginal: no coupling has a Lebesgue density and
  `C_ε(μ,ν) = +∞`).
* `lem:sharp` for the PRINTED plan (the Wave 30r gap "the journal's literal `−ε·Ent` objective"): `sharp_printed`
  (under `ass:ac` + `𝒫₂`: the printed plan exists uniquely, has an a.e.-positive density against `R ⊗ ν`, and no
  version of its barycentric projection is parity-exact unless `ν` is Dirac — never, for `d ≥ 1`).

Not covered (declared): Wiener measure (as in Waves 29q/29t, the claims quantify over every `ε`-Brownian reference
`IsBrownianRefD`; non-vacuity is certified there); the Gaussian value of `C_ε` in this normalisation (Wave 30c
`dplan_value` stays in Tau Ceti's normalisation: it needs the differential entropy of `N(m, Σ)` for general `Σ`);
the closed form `Ent(π*_ε) = log(2πe) + ½ log det Σ` (SB `:2766`); `rem:convention`'s weaker hypothesis "both
marginals absolutely continuous" in the positive claim (false as printed: `convention_counter`; `convention_printed`
adds finite entropy).

Encodings (to be checked by the critic):
* `ℝᵈ = EuclideanSpace ℝ (Fin d)`, Lebesgue `volume`; on `ℝᵈ × ℝᵈ` Mathlib's product `volume = volume.prod volume`.
  `logDensity ρ x = log (dρ/dLeb)(x)` (`Measure.rnDeriv`, `toReal`): `0` on the `ρ`-null set where the derivative is
  `0` or `∞` (junk confined to a null set). `diffEnt ρ = −∫ logDensity ρ dρ` is used ONLY together with
  `HasFiniteEnt ρ` (`ρ ≪ Leb` and `logDensity ρ ∈ L¹(ρ)`), so the Bochner integral is never the junk `0`.
* `entObj ε π : EReal` is the printed objective `½∫|x−y|² dπ − ε Ent(π)`; it is the real value when `Ent π` is finite
  and the cost integrable, and `⊤` otherwise. JUNK AUDIT: for couplings of `𝒫₂` marginals (`ass:main`, in force in
  every claim) `cost_finite_iff` proves `entObj = ⊤ ⟺ ¬(π ≪ Leb ∧ (log p)⁺ ∈ L¹(π))`, i.e. exactly when the printed
  `−ε Ent(π)` is `+∞` (`π` without density: `Ent = −∞` by the printed convention; `(log p)⁺ ∉ L¹`: `Ent = −∞`); the
  remaining case `Ent π = +∞` cannot occur in `𝒫₂` (library `negPart_integrable_P2_prod`: `(log p)⁻ ∈ L¹`), and the
  cost is finite on `Π(μ,ν)`. So on every instance used `entObj` is the literal extended-real value (`ε > 0`).
* `entCost ε μ ν = ⨅_{π ∈ Π(μ,ν)} entObj ε π` (`EReal`; the printed `min`; attainment is a conclusion).
  "`C_ε(μ,ν) < ∞`" is `entCost ε μ ν < ⊤`; values are read with `EReal.toReal` only after `≠ ⊥`, `≠ ⊤` are proved.
* `IsPrintedPlan ε μ ν π` (`π = π*_ε(μ,ν)`): a coupling with `entObj ε π ≠ ⊤` minimising `entObj ε` over `Π(μ,ν)`.
* `𝒫₂` as in Wave 29t: `‖x‖² ∈ L¹`. `KL(P*‖𝕎^ε_μ)` is `klDiv P R` for an `ε`-Brownian reference `R`
  (`IsBrownianRefD`, Wave 29t); `(εd/2) log(2πε)` is written `ε * d * log(2πε) / 2`.
* `repair_premise`: groups `s ∈ Fin 2`; the Wave 29t ass:ac-for-`ν` encoding is `ν = Leb.withDensity (ofReal ∘ q)`,
  `q ≥ 0` measurable, `log q ∈ L¹(ν)`.

Paper notes (checked clause by clause; every printed constant is CORRECT): `eq:calib`'s `ε Ent(μ) + (εd/2) log(2πε)`
(`equiv_printed`), the proof display's `−Ent(π) + Ent(μ) + (d/2) log(2πε) + (1/2ε)∫|x−y|²` (`equiv_display_printed`)
and `rem:convention`'s `ε(Ent(μ) + Ent(ν))` (`convention_printed`) are proved as printed. One S4 imprecision, Lean-refuted
(`convention_counter`): `rem:convention` "leaves the optimal plan unchanged when both marginals are absolutely
continuous" needs FINITE differential entropy (`ass:ac`): for the absolutely continuous `μ ∈ 𝒫₂(ℝ)` with density
`1/(x log² x)` on `(0, e⁻¹)` (`Ent(μ) = −∞`) and `ν = N(0,1)` the printed objective is `+∞` on every coupling
(`plan_literal`), so there is no printed optimal plan while the Sinkhorn plan exists uniquely. OLD "when both marginals are absolutely continuous" → NEW "when both marginals are absolutely continuous
with finite differential entropy (Assumption~\ref{ass:ac})".

DRAFT — not yet in `certify/statements.lock`; on the author's approval it becomes a `Statements.lean`, is hashed there
(with its imports), and AI agents must not edit it.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TauCeti InformationTheory
open scoped ENNReal NNReal

namespace StatFormal.Wave30ao

open StatFormal.Wave29t (isoGauss IsBrownianRefD IsSchrodingerBridgeD refPlanD IsStaticBridgeD bridgeLawD)
open StatFormal.Wave29g (sqCostD IsEntPlanD)

local notation "E" d => EuclideanSpace ℝ (Fin d)

section Defs

variable {α : Type*} [MeasureSpace α]

/-- `log (dρ/dLeb)`. -/
def logDensity (ρ : Measure α) (x : α) : ℝ := Real.log (ρ.rnDeriv volume x).toReal

/-- Differential entropy `Ent(ρ) = −∫ log (dρ/dLeb) dρ` (used only under `HasFiniteEnt ρ`). -/
def diffEnt (ρ : Measure α) : ℝ := -∫ x, logDensity ρ x ∂ρ

/-- `ρ` is absolutely continuous with finite differential entropy (`ass:ac`). -/
def HasFiniteEnt (ρ : Measure α) : Prop := ρ ≪ volume ∧ Integrable (logDensity ρ) ρ

end Defs

variable {d : ℕ}

open Classical in
/-- The printed objective of `eq:static` / `eq:plan`, `½∫|x−y|² dπ − ε Ent(π)`, in `EReal` (`⊤` when `Ent(π)` is not
finite or the cost is not integrable; see the junk audit). -/
def entObj (ε : ℝ) (π : Measure ((E d) × (E d))) : EReal :=
  if HasFiniteEnt π ∧ Integrable (fun z : (E d) × (E d) => ‖z.1 - z.2‖ ^ 2) π then
    (((∫ z, ‖z.1 - z.2‖ ^ 2 / 2 ∂π) - ε * diffEnt π : ℝ) : EReal)
  else ⊤

/-- `C_ε(μ, ν) = inf_{π ∈ Π(μ,ν)} {½∫|x−y|² dπ − ε Ent(π)}` (`eq:static`). -/
def entCost (ε : ℝ) (μ ν : Measure (E d)) : EReal :=
  ⨅ (π : Measure ((E d) × (E d))) (_ : IsCoupling π μ ν), entObj ε π

/-- `π = π*_ε(μ, ν)`: a minimiser of the printed objective over `Π(μ, ν)` with finite value. -/
def IsPrintedPlan (ε : ℝ) (μ ν : Measure (E d)) (π : Measure ((E d) × (E d))) : Prop :=
  IsCoupling π μ ν ∧ entObj ε π ≠ ⊤ ∧ ∀ π' : Measure ((E d) × (E d)), IsCoupling π' μ ν → entObj ε π ≤ entObj ε π'

namespace Claims

/-- SB `lem:equiv` (long `:433-443`; journal `supp/s_setting.tex:113-123`) in the PRINTED normalisation: for `ε > 0`,
`μ, ν ∈ 𝒫₂(ℝᵈ)` with `C_ε(μ,ν) < ∞` and every `ε`-Brownian reference `R` started at `μ`: `C_ε` is finite and `Ent(μ)`
is finite; the printed minimiser `π*_ε(μ,ν)` exists and is unique; `P*_ε(μ,ν)` exists and is unique; for it, the
endpoint law is `π*_ε`, `dP*/dR = g(X₀,X₁)` (an `h`-transform: conditionally on the endpoints the `ε`-Brownian bridge),
the law of `((X₀,X₁),X_t)` is the bridge mixture `bridgeLawD`, `C_ε` is attained at `π*_ε`, and
`eq:calib`: `ε KL(P*‖𝕎^ε_μ) = C_ε(μ,ν) + ε Ent(μ) + (εd/2) log(2πε)`. -/
def equiv_printed : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (d : ℕ) (ε : ℝ) (μ ν : Measure (E d)) (X : ℝ → Ω → E d) (R : Measure Ω),
    0 < ε → IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    Integrable (fun x : E d => ‖x‖ ^ 2) μ → Integrable (fun y : E d => ‖y‖ ^ 2) ν →
    entCost ε μ ν < ⊤ → IsBrownianRefD ε μ X R →
      entCost ε μ ν ≠ ⊥ ∧ HasFiniteEnt μ ∧
      (∃! π : Measure ((E d) × (E d)), IsPrintedPlan ε μ ν π) ∧
      (∃! P : Measure Ω, IsSchrodingerBridgeD X R μ ν P) ∧
      ∀ P : Measure Ω, IsSchrodingerBridgeD X R μ ν P →
        IsPrintedPlan ε μ ν (P.map (fun ω => (X 0 ω, X 1 ω))) ∧
        entCost ε μ ν = entObj ε (P.map (fun ω => (X 0 ω, X 1 ω))) ∧
        (∃ g : (E d) × (E d) → ℝ≥0∞, Measurable g ∧ P = R.withDensity (fun ω => g (X 0 ω, X 1 ω))) ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          P.map (fun ω => ((X 0 ω, X 1 ω), X t ω)) = bridgeLawD ε t (P.map (fun ω => (X 0 ω, X 1 ω)))) ∧
        ε * (klDiv P R).toReal = (entCost ε μ ν).toReal + ε * diffEnt μ + ε * d * Real.log (2 * Real.pi * ε) / 2

/-- SB proof of `lem:equiv`, display (long `:2619-2623`; journal `supp/s_proofs.tex:165-168`): under `C_ε(μ,ν) < ∞`
and `𝒫₂`, every coupling `π` with finite differential entropy has `KL(π‖R₀₁) < ∞` and
`KL(π‖R₀₁) = −Ent(π) + Ent(μ) + (d/2) log(2πε) + (1/2ε) ∫|x−y|² dπ`; every other coupling (for which the right side
is `+∞`) has `KL(π‖R₀₁) = ∞`. -/
def equiv_display_printed : Prop :=
  ∀ (d : ℕ) (ε : ℝ) (μ ν : Measure (E d)), 0 < ε → IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    Integrable (fun x : E d => ‖x‖ ^ 2) μ → Integrable (fun y : E d => ‖y‖ ^ 2) ν → entCost ε μ ν < ⊤ →
    ∀ π : Measure ((E d) × (E d)), IsCoupling π μ ν →
      (HasFiniteEnt π → klDiv π (refPlanD ε μ) ≠ ∞ ∧
        (klDiv π (refPlanD ε μ)).toReal = -diffEnt π + diffEnt μ + d / 2 * Real.log (2 * Real.pi * ε) +
          1 / (2 * ε) * ∫ z, ‖z.1 - z.2‖ ^ 2 ∂π) ∧
      (¬ HasFiniteEnt π → klDiv π (refPlanD ε μ) = ∞)

/-- SB proof of `lem:equiv`, "for `μ, ν ∈ 𝒫₂`, `C_ε < ∞` forces `Ent(μ)` finite" (long `:2628-2629`; journal
`supp/s_proofs.tex:173-174`), in full: for `μ, ν ∈ 𝒫₂(ℝᵈ)`, `ε > 0`: (i) `C_ε(μ,ν) < ∞` iff `μ` and `ν` are
absolutely continuous with finite differential entropy; (ii) encoding-free: a coupling with a Lebesgue density
and `Ent(π) > −∞` (`(log p)⁺ ∈ L¹(π)`) has `Ent(π)`, `Ent(μ)`, `Ent(ν)` all finite; (iii) junk audit of `entObj`:
on `Π(μ,ν)`, `entObj ε π = ⊤` exactly when the printed `−ε Ent(π)` is `+∞`. -/
def cost_finite_iff : Prop :=
  ∀ (d : ℕ) (ε : ℝ) (μ ν : Measure (E d)), 0 < ε → IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    Integrable (fun x : E d => ‖x‖ ^ 2) μ → Integrable (fun y : E d => ‖y‖ ^ 2) ν →
      (entCost ε μ ν < ⊤ ↔ HasFiniteEnt μ ∧ HasFiniteEnt ν) ∧
      (∀ π : Measure ((E d) × (E d)), IsCoupling π μ ν → π ≪ volume →
        Integrable (fun z => max (logDensity π z) 0) π → HasFiniteEnt π ∧ HasFiniteEnt μ ∧ HasFiniteEnt ν) ∧
      ∀ π : Measure ((E d) × (E d)), IsCoupling π μ ν →
        (entObj ε π = ⊤ ↔ ¬ (π ≪ volume ∧ Integrable (fun z => max (logDensity π z) 0) π))

/-- SB `def:repair` premise (long `:455-465`; journal `supp/s_setting.tex:148-158`), "`ν ∈ 𝒫₂` with
`C_ε(R_s,ν) < ∞` for `s ∈ {0,1}`", under `ass:main`: it is EQUIVALENT to `ass:ac` (`R₀`, `R₁`, `ν` absolutely
continuous with finite differential entropy); it yields the ass:ac-for-`ν` hypotheses of the certified Wave 29t
claims (`ν = q · Leb`, `log q ∈ L¹(ν)`, `∫ log q dν = −Ent(ν)`), finite static value and Sinkhorn cost, and for every
`ε`-Brownian reference from `R_s` a unique Schrödinger bridge `P*_ε(R_s,ν)` (so the repair path is well defined). -/
def repair_premise : Prop :=
  ∀ (d : ℕ) (ε : ℝ) (Rs : Fin 2 → Measure (E d)) (ν : Measure (E d)), 0 < ε → (∀ s, IsProbabilityMeasure (Rs s)) →
    IsProbabilityMeasure ν → (∀ s, Integrable (fun x : E d => ‖x‖ ^ 2) (Rs s)) →
    Integrable (fun y : E d => ‖y‖ ^ 2) ν →
      ((∀ s, entCost ε (Rs s) ν < ⊤) ↔ (∀ s, HasFiniteEnt (Rs s)) ∧ HasFiniteEnt ν) ∧
      ((∀ s, entCost ε (Rs s) ν < ⊤) →
        (∃ q : (E d) → ℝ, Measurable q ∧ (∀ y, 0 ≤ q y) ∧ ν = volume.withDensity (fun y => ENNReal.ofReal (q y)) ∧
          Integrable (fun y => Real.log (q y)) ν ∧ ∫ y, Real.log (q y) ∂ν = -diffEnt ν) ∧
        ∀ s, schroedingerValue (refPlanD ε (Rs s)) (Rs s) ν ≠ ∞ ∧
          entropicTransportCost sqCostD ε.toNNReal (Rs s) ν ≠ ∞ ∧
          ∀ (Ω : Type) [MeasurableSpace Ω] (X : ℝ → Ω → E d) (R : Measure Ω), IsBrownianRefD ε (Rs s) X R →
            ∃! P : Measure Ω, IsSchrodingerBridgeD X R (Rs s) ν P)

/-- SB `prop:mixture` (long `:476-491`; journal `supp/s_setting.tex:171-186`) with its printed hypothesis
(`μ, ν ∈ 𝒫₂`, `C_ε(μ,ν) < ∞`) and `(X₀, X₁) ∼ π*_ε(μ,ν)` the PRINTED minimiser: for every `ε`-Brownian reference,
the Schrödinger bridge exists and is unique, and for every `t ∈ [0,1]`
`μ^ε_t = Law((1−t)X₀ + tX₁ + √(εt(1−t)) Z)`, `Z ∼ N(0, I_d)` independent (`eq:mixture`)
`= ρ^ε_t ∗ N(0, εt(1−t) I_d)` (`eq:convolution`). -/
def mixture_printed : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (d : ℕ) (ε : ℝ) (μ ν : Measure (E d)) (X : ℝ → Ω → E d) (R : Measure Ω),
    0 < ε → IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    Integrable (fun x : E d => ‖x‖ ^ 2) μ → Integrable (fun y : E d => ‖y‖ ^ 2) ν →
    entCost ε μ ν < ⊤ → IsBrownianRefD ε μ X R →
      (∃! P : Measure Ω, IsSchrodingerBridgeD X R μ ν P) ∧
      ∀ (π : Measure ((E d) × (E d))) (P : Measure Ω), IsPrintedPlan ε μ ν π → IsSchrodingerBridgeD X R μ ν P →
        ∀ t ∈ Icc (0 : ℝ) 1,
          P.map (X t) = (π.prod (stdGaussian (E d))).map
            (fun q => (1 - t) • q.1.1 + t • q.1.2 + √(ε * t * (1 - t)) • q.2) ∧
          P.map (X t) = (π.map (fun z => (1 - t) • z.1 + t • z.2)) ∗ isoGauss d (ε * t * (1 - t))

/-- SB `rem:convention` (long `:2189-2196`; journal `supp/s_univariate.tex:125-132`), for marginals in `𝒫₂` with
finite differential entropy: a coupling has finite entropy iff `KL(π‖μ⊗ν) < ∞`; on such couplings the chain rule
`KL(π‖μ⊗ν) = −Ent(π) + Ent(μ) + Ent(ν)` holds, hence `[½∫|x−y|² + ε KL(π‖μ⊗ν)] − [½∫|x−y|² − ε Ent(π)] = ε(Ent(μ) + Ent(ν))`; and the optimal plans coincide: the printed
minimiser is exactly the Sinkhorn-normalisation plan (Wave 29g `IsEntPlanD`), which exists and is unique. -/
def convention_printed : Prop :=
  ∀ (d : ℕ) (ε : ℝ) (μ ν : Measure (E d)), 0 < ε → IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    Integrable (fun x : E d => ‖x‖ ^ 2) μ → Integrable (fun y : E d => ‖y‖ ^ 2) ν →
    HasFiniteEnt μ → HasFiniteEnt ν →
      (∀ π : Measure ((E d) × (E d)), IsCoupling π μ ν → (HasFiniteEnt π ↔ klDiv π (μ.prod ν) ≠ ∞)) ∧
      (∀ π : Measure ((E d) × (E d)), IsCoupling π μ ν → HasFiniteEnt π →
        (klDiv π (μ.prod ν)).toReal = -diffEnt π + diffEnt μ + diffEnt ν) ∧
      (∀ π : Measure ((E d) × (E d)), IsCoupling π μ ν → HasFiniteEnt π →
        (∫ z, ‖z.1 - z.2‖ ^ 2 / 2 ∂π + ε * (klDiv π (μ.prod ν)).toReal) -
          (∫ z, ‖z.1 - z.2‖ ^ 2 / 2 ∂π - ε * diffEnt π) = ε * (diffEnt μ + diffEnt ν)) ∧
      (∀ π : Measure ((E d) × (E d)), IsPrintedPlan ε μ ν π ↔ IsEntPlanD ε μ ν π) ∧
      ∃! π : Measure ((E d) × (E d)), IsPrintedPlan ε μ ν π

/-- SB `eq:static` "with minimiser `π*_ε(μ,ν)`, unique when finite" (long `:401-410`; journal
`supp/s_setting.tex:74-82`) and journal `eq:plan` (`main/02_setting.tex:37-45`, the literal `−ε·Ent` objective),
for `μ, ν ∈ 𝒫₂`: if `C_ε(μ,ν) < ∞` the printed minimiser exists and is unique; if `μ` or `ν` is not absolutely
continuous with finite differential entropy (off `ass:ac`), the printed objective is `+∞` on every coupling. -/
def plan_literal : Prop :=
  ∀ (d : ℕ) (ε : ℝ) (μ ν : Measure (E d)), 0 < ε → IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    Integrable (fun x : E d => ‖x‖ ^ 2) μ → Integrable (fun y : E d => ‖y‖ ^ 2) ν →
      (entCost ε μ ν < ⊤ → ∃! π : Measure ((E d) × (E d)), IsPrintedPlan ε μ ν π) ∧
      (¬ (HasFiniteEnt μ ∧ HasFiniteEnt ν) →
        ∀ π : Measure ((E d) × (E d)), IsCoupling π μ ν → entObj ε π = ⊤)

/-- SB paragraph after `ass:ac` (long `:418-424`; journal `supp/s_setting.tex:91-96`): in `ℝᵈ`, `d ≥ 1`, if one
marginal has an atom then no coupling has a Lebesgue density and `C_ε(μ,ν) = +∞` (`ε > 0`: at `ε ≤ 0` the printed
objective of a density-free coupling is not `+∞`, so the encoding `entObj = ⊤` would be junk there). -/
def cost_atom : Prop :=
  ∀ (d : ℕ) (ε : ℝ) (μ ν : Measure (E d)), 0 < d → 0 < ε → IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    ((∃ a, μ {a} ≠ 0) ∨ (∃ b, ν {b} ≠ 0)) →
      (∀ π : Measure ((E d) × (E d)), IsCoupling π μ ν → ¬ π ≪ volume) ∧ entCost ε μ ν = ⊤

/-- SB `lem:sharp` (long `:916-923`; journal `main/m_defect.tex:66-73`) for the PRINTED plan
`π*_ε(R_s,ν) = argmin ½∫|x−y|² − ε Ent` (under `ass:ac` and `𝒫₂`; the frozen Wave 30r `sharp_P2` is stated for the
Sinkhorn-normalised plan at `2ε`): the printed plan exists and is unique; it has a density against `R ⊗ ν` that is
positive `R ⊗ ν`-a.e.; every version `T` of its barycentric projection has `T_#R = ν` iff `ν` is a Dirac measure; and
in `ℝᵈ`, `d ≥ 1`, `T_#R ≠ ν` always (an absolutely continuous `ν` is not Dirac). -/
def sharp_printed : Prop :=
  ∀ (d : ℕ) (ε : ℝ) (R ν : Measure (E d)), 0 < ε → IsProbabilityMeasure R → IsProbabilityMeasure ν →
    Integrable (fun x : E d => ‖x‖ ^ 2) R → Integrable (fun y : E d => ‖y‖ ^ 2) ν → HasFiniteEnt R → HasFiniteEnt ν →
      (∃! π : Measure ((E d) × (E d)), IsPrintedPlan ε R ν π) ∧
      (∀ π : Measure ((E d) × (E d)), IsPrintedPlan ε R ν π →
        ∃ f : (E d) × (E d) → ℝ≥0∞, Measurable f ∧ (∀ᵐ z ∂(R.prod ν), 0 < f z) ∧ π = (R.prod ν).withDensity f) ∧
      (∀ (π : Measure ((E d) × (E d))) (T : (E d) → E d), IsPrintedPlan ε R ν π →
        StatFormal.Wave8a.IsBaryProj π T → (R.map T = ν ↔ ∃ y, ν = Measure.dirac y)) ∧
      (0 < d → ∀ (π : Measure ((E d) × (E d))) (T : (E d) → E d), IsPrintedPlan ε R ν π →
        StatFormal.Wave8a.IsBaryProj π T → R.map T ≠ ν)

/-- SB `rem:convention` (long `:2189-2196`; journal `supp/s_univariate.tex:125-132`) AS PRINTED ("leaves the optimal
plan unchanged when both marginals are absolutely continuous") is false: there are absolutely continuous `μ, ν ∈ 𝒫₂(ℝ)`
(`ν` with finite differential entropy, `μ` with `Ent(μ) = −∞`: `(log p)⁻ ∈ L¹(μ)`, `(log p)⁺ ∉ L¹(μ)`) such that for
every `ε > 0` the printed objective is `+∞` on every coupling, `C_ε(μ,ν) = +∞` and there is no printed optimal plan, while
the Sinkhorn-normalised plan (Wave 29g `IsEntPlanD`) exists and is unique. -/
def convention_counter : Prop :=
  ∃ μ ν : Measure (E 1), IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧
    Integrable (fun x : E 1 => ‖x‖ ^ 2) μ ∧ Integrable (fun y : E 1 => ‖y‖ ^ 2) ν ∧ μ ≪ volume ∧ ν ≪ volume ∧
    HasFiniteEnt ν ∧ ¬ HasFiniteEnt μ ∧ Integrable (fun x => max (-logDensity μ x) 0) μ ∧
    ¬ Integrable (fun x => max (logDensity μ x) 0) μ ∧
    ∀ ε : ℝ, 0 < ε → (∀ π : Measure ((E 1) × (E 1)), IsCoupling π μ ν → entObj ε π = ⊤) ∧ entCost ε μ ν = ⊤ ∧
      (¬ ∃ π : Measure ((E 1) × (E 1)), IsPrintedPlan ε μ ν π) ∧ ∃! π : Measure ((E 1) × (E 1)), IsEntPlanD ε μ ν π

end Claims

end StatFormal.Wave30ao
