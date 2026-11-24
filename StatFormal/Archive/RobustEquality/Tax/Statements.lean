import StatFormal.Archive.RobustEquality.SemidualStrong.Statements

/-!
# FROZEN STATEMENTS — robust equality (JASA): the misspecification tax and ghost samples

Sources (verbatim in `inventory/extracted/robust-equality-jasa.md`): definition of `W^ν_ε` and of the balls
`𝓑^𝒩(r) = ⋃_{ν∈𝒩} {Q ∈ 𝒫(K) : W^ν_ε(P̂,Q) ≤ r}` (`jasa/main.tex:225-241`), `lem:tax` (`main.tex:243-253`),
`thm:ghost` (`main.tex:465-472`); conventions `jasa/supp_proofs.tex:15-45`.

Covered:
* `tax_identity` (`lem:tax`): `W^ν_ε(P̂,Q) = OT_ε(P̂,Q) + ε KL(Q‖ν)`, both sides `⊤` when `Q ⋘̸ ν` (EReal);
* `tax_ball` (`lem:tax`): `Q ∈ 𝓑^𝒩(r) ⇒ OT_ε(P̂,Q) + ε τ_𝒩(Q) ≤ r`, and the converse when the infimum defining the
  tax `τ_𝒩(Q) = inf_{ν∈𝒩} KL(Q‖ν)` is attained;
* `ghost_atomless` (`thm:ghost`, "in particular"): if no member of `𝒩` has an atom, every radius that covers every
  finitely supported population is `+∞` with probability `≥ 1 − α` at every population.
Not covered (declared): the general clause `Pr_P[r̂ ≥ OT_ε(P̂,P) + ε a_𝒩] ≥ 1 − α` for finite `a_𝒩` (its event
depends on the population; needs the paper's exchangeable coupling of ghost samples, or weak continuity of `OT_ε`).

Encodings (see card): `P̂ = Σ_i a_i δ_{x_i}` as labelled atoms (`OTdisc`, `Setting` of the frozen `SemidualStrong`
statements); `W^ν_ε` is the infimum over couplings `γ ∈ Π(P̂,Q)` of `E_γ c + ε KL(γ‖P̂⊗ν)` (`Wdisc`); references
`ν ∈ 𝒩` are finite measures (the paper: `0 < ν(K) ≤ 1` — a generalisation); `KL` is the paper's `klRef`. In
`ghost_atomless` the sample is `x : Fin n → K` with `P̂ = n⁻¹Σ δ_{x_i}` (costs `cost(x_i, ·)`), `r̂` is a measurable
`EReal`-valued function of the sample (the paper: independent randomisation changes nothing), "finitely supported"
is `Q(sᶜ) = 0` for a finite set `s`, and the validity hypothesis bounds an outer measure (a weaker hypothesis, hence
a stronger claim); the conclusion's event `{r̂ = ⊤}` is measurable.
Hashed in `certify/statements.lock` (with its imports); AI agents must not edit this file.
-/

noncomputable section
open MeasureTheory

namespace StatFormal.RobustEquality.Tax

open StatFormal.RobustEquality.Semidual StatFormal.RobustEquality.SemidualStrong

variable {K : Type*} [MeasurableSpace K] {k : ℕ}

/-- `W^ν_ε(P̂, Q)`: infimum over couplings of `(P̂, Q)` of `E_γ c + ε KL(γ ‖ P̂ ⊗ ν)`. -/
def Wdisc (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ) (ν Q : Measure K) : EReal :=
  sInf {v | ∃ γ : Measure (Fin k × K), IsProbabilityMeasure γ ∧ γ.map Prod.fst = muDisc a ∧
    γ.map Prod.snd = Q ∧
    v = ((∫ z, c z.1 z.2 ∂γ : ℝ) : EReal) + (ε : EReal) * StatFormal.RobustEquality.klRef γ ((muDisc a).prod ν)}

/-- The tax `τ_𝒩(Q) = inf_{ν ∈ 𝒩} KL(Q ‖ ν)`. -/
def tax (𝒩 : Set (Measure K)) (Q : Measure K) : EReal := ⨅ ν ∈ 𝒩, StatFormal.RobustEquality.klRef Q ν

/-- The ball `𝓑^𝒩(r) = ⋃_{ν ∈ 𝒩} {Q ∈ 𝒫(K) : W^ν_ε(P̂, Q) ≤ r}`. -/
def ballN (𝒩 : Set (Measure K)) (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ) (r : EReal) : Set (Measure K) :=
  {Q | IsProbabilityMeasure Q ∧ ∃ ν ∈ 𝒩, Wdisc ε a c ν Q ≤ r}

namespace Claims

/-- `lem:tax`: `W^ν_ε(P̂,Q) = OT_ε(P̂,Q) + ε KL(Q‖ν)`. -/
def tax_identity : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k : ℕ) (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (ν Q : Measure K) [IsFiniteMeasure ν] [IsProbabilityMeasure Q],
    Setting ε a c → Wdisc ε a c ν Q = OTdisc ε a c Q + (ε : EReal) * StatFormal.RobustEquality.klRef Q ν

/-- `lem:tax`, balls: membership implies `OT + ε τ ≤ r`; the converse holds when the tax is attained. -/
def tax_ball : Prop :=
  ∀ (K : Type) [MeasurableSpace K] (k : ℕ) (ε : ℝ) (a : Fin k → ℝ) (c : Fin k → K → ℝ)
    (𝒩 : Set (Measure K)) (r : EReal) (Q : Measure K) [IsProbabilityMeasure Q],
    Setting ε a c → (∀ ν ∈ 𝒩, IsFiniteMeasure ν) →
      (Q ∈ ballN 𝒩 ε a c r → OTdisc ε a c Q + (ε : EReal) * tax 𝒩 Q ≤ r) ∧
      ((∃ ν ∈ 𝒩, StatFormal.RobustEquality.klRef Q ν = tax 𝒩 Q) →
        OTdisc ε a c Q + (ε : EReal) * tax 𝒩 Q ≤ r → Q ∈ ballN 𝒩 ε a c r)

/-- `thm:ghost`, atomless classes: a radius valid at every finitely supported population is `+∞` with probability
`≥ 1 − α` at every population. -/
def ghost_atomless : Prop :=
  ∀ (K : Type) [MeasurableSpace K] [MeasurableSingletonClass K] (n : ℕ) (ε α : ℝ) (cost : K → K → ℝ)
    (𝒩 : Set (Measure K)) (r : (Fin n → K) → EReal),
    0 < n → 0 < ε → (∀ x0, Measurable (cost x0)) → (∃ B, ∀ x0 y, |cost x0 y| ≤ B) →
    (∀ ν ∈ 𝒩, IsFiniteMeasure ν) → (∀ ν ∈ 𝒩, ∀ y, ν {y} = 0) → Measurable r →
    (∀ Q : Measure K, IsProbabilityMeasure Q → (∃ s : Finset K, Q (↑s)ᶜ = 0) →
      ENNReal.ofReal (1 - α) ≤ (Measure.pi fun _ : Fin n => Q)
        {x | Q ∈ ballN 𝒩 ε (fun _ => (1 : ℝ) / n) (fun i => cost (x i)) (r x)}) →
    ∀ P : Measure K, IsProbabilityMeasure P →
      ENNReal.ofReal (1 - α) ≤ (Measure.pi fun _ : Fin n => P) {x | r x = ⊤}

end Claims
end StatFormal.RobustEquality.Tax
